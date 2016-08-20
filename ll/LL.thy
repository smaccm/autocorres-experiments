theory LL imports
 "/home/dacosta/development/rockwellcollins/l4v/tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin

new_C_include_dir "/home/dacosta/development/rockwellcollins/verification/musllibc/include"

install_C_file "./ll.c"
autocorres [ heap_abs_syntax, ts_rules = nondet, unsigned_word_abs =] "./ll.c"

context ll begin

fun ll :: "lifted_globals \<Rightarrow> llnode_C ptr \<Rightarrow> llnode_C ptr list \<Rightarrow> bool" where
  "ll s i [] = (i = NULL)"
| "ll s i (x # xs) = (i = x \<and> i \<noteq> NULL \<and> is_valid_llnode_C s i \<and> ll s s[i]\<rightarrow>next xs)"

lemma ll_null_empty:"ll h NULL ptrs \<Longrightarrow> ptrs = []"
apply(cases rule:ll.cases) by auto

lemma ll_single:"\<lbrakk>n \<noteq> NULL; is_valid_llnode_C s' n; s'[n]\<rightarrow>next = NULL\<rbrakk> \<Longrightarrow> ll s' n [n]"
by simp

lemma ll_nonempty_nonnull:"ll h i (x # xs) \<Longrightarrow> i \<noteq> NULL \<and> x = i"
apply(cases rule:ll.cases) by auto

lemma ll_nonnull_nonempty:"\<lbrakk>ll h i xs; i \<noteq> NULL\<rbrakk> \<Longrightarrow> \<exists> xs'. xs = i # xs'"
apply(cases xs) using ll.ll.elims(2) by auto

lemma ll_path_unique:"\<lbrakk>ll s i xs; ll s i ys\<rbrakk>\<Longrightarrow> xs = ys"
apply(induction xs arbitrary: i ys) by (metis ll.elims(2) ll.simps)+

lemma ll_non_null_form:"\<lbrakk>ll s a xs; a \<noteq> NULL\<rbrakk> \<Longrightarrow> \<exists> xs'. xs = a # xs'"
  by (induction rule: ll.induct) auto

lemma ll_list_no_nulls:"ll s i xs \<Longrightarrow> \<forall> x \<in> set xs. x \<noteq> NULL" by(induction xs arbitrary: i) auto

lemma ll_suffix:"\<lbrakk>ll s i xs; j \<in> set xs\<rbrakk> \<Longrightarrow> \<exists> ys zs. ll s j zs \<and> xs = ys @ zs" 
proof(induction xs arbitrary: i)
  case Nil
  thus ?case by auto
next
  case (Cons x xs')
  then have y1:"ll s s[i]\<rightarrow>next xs'" by auto
  have y2:"j \<noteq> NULL" using ll_list_no_nulls[OF Cons(2)] Cons.prems(2) by blast 
  have "j = x \<or> j \<noteq> x" by auto
  thus ?case
  proof 
    assume "j = x"
    then have "i = j" using Cons.prems(1) by auto
    then have "ll s j (x # xs')" using Cons(2) by auto
    thus ?case by blast 
  next
    assume "j \<noteq> x"
    then have y3:"j \<in> set xs'" using Cons by auto
    thus ?case using Cons(1)[OF y1 y3] Cons by fastforce
  qed
qed

lemma ll_suffix_ex:"\<lbrakk>ll s i xs; j \<in> set xs\<rbrakk> \<Longrightarrow> Ex(ll s j)" using ll_suffix by blast

lemma ll_all_valid:"\<lbrakk>ll s f ptrs; j \<in> set ptrs\<rbrakk> \<Longrightarrow> is_valid_llnode_C s j"
apply(induction ptrs arbitrary: f) by auto
 
definition to_list :: "lifted_globals \<Rightarrow>  llnode_C ptr \<Rightarrow>  llnode_C ptr list" where
"to_list s i \<equiv> The (ll s i)"

lemma to_list_val:"ll s i xs \<Longrightarrow> to_list s i = xs"
  using ll_path_unique by (unfold to_list_def, induction xs arbitrary: i) blast+

lemma to_list_null:"to_list s NULL = []" using to_list_def to_list_val by auto

lemma to_list_non_null:"\<lbrakk> ll s i xs; i \<noteq> NULL\<rbrakk> \<Longrightarrow> to_list s i \<noteq> []" 
  using to_list_def to_list_val by auto

lemma to_list_non_null_recursive:"\<lbrakk>ll s i xs; i \<noteq> NULL\<rbrakk> \<Longrightarrow> to_list s i = i # to_list s s[i]\<rightarrow>next"
  using to_list_def to_list_val by(unfold to_list_def,induction xs) auto

lemma to_list_length_ineq_1:"\<lbrakk>ll s i xs; i \<noteq> NULL\<rbrakk> \<Longrightarrow> length (to_list s NULL) < length (to_list s i)" 
  using to_list_null to_list_non_null by auto

lemma to_list_length_ineq_2:
  "\<lbrakk>ll s i xs; i \<noteq> NULL\<rbrakk> \<Longrightarrow> length (to_list s s[i]\<rightarrow>next) < length (to_list s i)" 
  using to_list_non_null_recursive by simp

lemma loop_support_1: 
"\<lbrakk>ll s j xs; i \<in> set xs; s[i]\<rightarrow>next \<noteq> NULL\<rbrakk> \<Longrightarrow> s[i]\<rightarrow>next \<in> set xs"
proof -
  assume a1:"ll s j xs"
  assume a3:"i \<in> set xs"
  assume a4:"s[i]\<rightarrow>next \<noteq> NULL"
  obtain ys zs where y1:"ll s i zs" and y2:"xs = ys @ zs" using ll_suffix[OF a1 a3]  by auto
  then obtain zs' where y3:"ll s s[i]\<rightarrow>next zs'" and y4:"zs = i # zs'" 
    by (metis (no_types, hide_lams) a1 a3 ll.ll.elims(2) ll.ll_list_no_nulls)
  then obtain zs'' where y5:"zs' = s[i]\<rightarrow>next # zs''" using a4 ll_non_null_form by blast
  thus ?thesis using y2 y4 y5  by auto
qed

lemma loop_support_2:
"\<lbrakk>ll s i xs; j \<in> set xs\<rbrakk> \<Longrightarrow> length (to_list s s[j]\<rightarrow>next) < length (to_list s j)"
proof -
  assume a1:"ll s i xs"
  assume a2:"j \<in> set xs"
  obtain ys zs where "ll s j zs" and "xs = ys @ zs" using ll_suffix[OF a1 a2] by auto
  thus ?thesis using a1 a2 ll.ll_list_no_nulls ll.to_list_length_ineq_2 by auto
qed

lemma find_insertion:"
\<lbrace> \<lambda> (s::lifted_globals). ll s front xs \<and> s = s'\<rbrace>
  find_insertion' val front
\<lbrace> \<lambda> r s. (r = NULL \<or> r \<in> set xs) \<and> s = s'\<rbrace>!"
apply (rule validNF_assume_pre)
apply (unfold find_insertion'_def)
apply (subst whileLoop_add_inv [where 
  I = " \<lambda> (it,last,cond) s. 
       s = s'
       \<and> (cond = 0 \<or> cond = 1)
       \<and> (cond = 1 \<longrightarrow> last = NULL \<longrightarrow> (it \<noteq> NULL \<and> s[it]\<rightarrow>val \<le> val \<and> it \<in> set xs \<and> front = it))
       \<and> (cond = 1 \<longrightarrow> last \<noteq> NULL \<longrightarrow> 
           (it \<noteq> NULL \<and> s[it]\<rightarrow>val \<le> val \<and> s[last]\<rightarrow>next = it \<and> it \<in> set xs))
       \<and> (cond = 0 \<longrightarrow> last = NULL \<longrightarrow> it = NULL \<longrightarrow> front = NULL)
       \<and> (cond = 0 \<longrightarrow> last = NULL \<longrightarrow> it \<noteq> NULL \<longrightarrow> front = it \<and> val < s[it]\<rightarrow>val)
       \<and> (cond = 0 \<longrightarrow> last \<noteq> NULL \<longrightarrow> s[last]\<rightarrow>val \<le> val \<and> last \<in> set xs)"
  and M = "\<lambda>((it,r),s). length (to_list s it)"])
apply wp+
apply clarsimp
using  loop_support_1 loop_support_2 ll.ll_suffix_ex ll.to_list_length_ineq_1
apply (meson ll.ll.elims(2) ll.ll_suffix | blast)
apply clarsimp+
apply wp
by (metis if_P_1_0_eq_0 list.set_intros(1) ll.ll.elims(2) not_less)

lemma state_eq_mod_next_upd:"(ptr :: llnode_C ptr) \<noteq> n \<Longrightarrow> (s::lifted_globals)[ptr] = (s[n\<rightarrow>next := x])[ptr]"
by (simp add: fun_upd_def ll.update_llnode_next_def)

lemma next_upd_preserves_validity:"\<lbrakk>is_valid_llnode_C s f\<rbrakk> \<Longrightarrow> is_valid_llnode_C (s[n\<rightarrow>next := x]) f" 
by simp

lemma ll_preserved_by_non_aliased_upd:"\<lbrakk>ll s front ptrs;n \<notin> set ptrs\<rbrakk> \<Longrightarrow> ll s[n\<rightarrow>next := x] front ptrs"
apply(induction ptrs arbitrary: front, simp)
by (metis state_eq_mod_next_upd next_upd_preserves_validity insert_iff list.simps(15) ll.get_llnode_next_def ll.ll.simps(2))

lemma ll_insert_front:"\<lbrakk>ll s front ptrs; n \<noteq> NULL; is_valid_llnode_C s n; n \<notin> set ptrs\<rbrakk> \<Longrightarrow> ll s[n\<rightarrow>next := front] n (n # ptrs) \<and> n \<in> set  (n # ptrs)"
apply(drule ll_preserved_by_non_aliased_upd)
apply assumption
apply (drule next_upd_preserves_validity[of _ _ "front"])
apply (rule conjI)
apply (simp add: fun_upd_apply)+
done

lemma ll_front_acyclic:"ll s ptr (ptr # ptrs) \<Longrightarrow> ptr \<noteq> s[ptr]\<rightarrow>next"
proof(induction ptrs arbitrary: ptr)
  case Nil
  thus ?case by auto
next
  case (Cons ptr' ptrs)
  then have "ll s s[ptr]\<rightarrow>next (s[ptr]\<rightarrow>next # ptrs)" by auto
  then have "s[ptr]\<rightarrow>next \<noteq> s[s[ptr]\<rightarrow>next]\<rightarrow>next" using Cons by auto
  thus ?case by auto
qed

lemma ll_acyclic:"ll s ptr (ptr # ptrs) \<Longrightarrow> ptr \<notin> set ptrs"
apply(induction rule:ll.induct)
apply auto[1]
using ll_front_acyclic ll.ll.simps(2) ll.loop_support_1 set_ConsD by fastforce

lemma ll_insert_not_front:"\<lbrakk>ll s' front ptrs; n \<noteq> NULL; is_valid_llnode_C s' n; s'[n]\<rightarrow>next = NULL; n \<notin> set ptrs; r \<in> set ptrs; r \<noteq> NULL\<rbrakk>
         \<Longrightarrow> \<exists>xs_new. ll s'[n\<rightarrow>next := s'[r]\<rightarrow>next][r\<rightarrow>next := n] front xs_new \<and> n \<in> set xs_new"
proof (induction ptrs arbitrary: front)
  case Nil
  thus ?case by auto
next
  case (Cons ptr ptrs)
  then have "r \<noteq> ptr \<or> r = ptr" by auto
  thus ?case
  proof
    assume a:"r \<noteq> ptr"
    have h1:"ll s' s'[front]\<rightarrow>next ptrs" using Cons by auto
    have h2:"n \<notin> set ptrs" using Cons by auto
    have h3:"r \<in> set ptrs" using Cons a by auto
    obtain xs'_new where h4:"ll s'[n\<rightarrow>next := s'[r]\<rightarrow>next][r\<rightarrow>next := n]  s'[front]\<rightarrow>next xs'_new \<and> n \<in> set xs'_new" using h1 h2 h3 Cons by auto
    have h5:"r \<noteq> front" using a Cons by auto
    have h6:"n \<noteq> front" using Cons by auto
    have h7:"s'[front]\<rightarrow>next = (s'[n\<rightarrow>next := s'[r]\<rightarrow>next][r\<rightarrow>next := n])[front]\<rightarrow>next" by (metis h5 h6 fun_upd_def ll.heap_abs_simps(16))
    have h8:"ll s'[n\<rightarrow>next := s'[r]\<rightarrow>next][r\<rightarrow>next := n]  (s'[n\<rightarrow>next := s'[r]\<rightarrow>next][r\<rightarrow>next := n])[front]\<rightarrow>next xs'_new \<and> n \<in> set xs'_new" using h4 h7 by auto
    have h9:"front \<noteq> NULL" using Cons by auto
    have h10:"is_valid_llnode_C (s'[n\<rightarrow>next := s'[r]\<rightarrow>next][r\<rightarrow>next := n]) front" using next_upd_preserves_validity Cons by auto
    have h11:"ll s'[n\<rightarrow>next := s'[r]\<rightarrow>next][r\<rightarrow>next := n] front (front # xs'_new) \<and> n \<in> set (front # xs'_new)" using h8 h9 h10 by auto
    thus ?case by metis
  next
    assume a:"r = ptr"
    have h1:"r = front" using Cons a by auto
    have h2:"n \<noteq> front" using Cons by auto
    have h3:"front \<notin> set ptrs" using Cons ll_acyclic by auto
    have h4:"ll s' s'[front]\<rightarrow>next ptrs" using Cons by auto
    have h5:"ll  s'[n\<rightarrow>next := s'[front]\<rightarrow>next] (s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n])[n]\<rightarrow>next ptrs" 
    using Cons h2  insert_iff list.set(2) ll.ll.simps(2) ll.ll_insert_front by (metis fun_upd_def ll.heap_abs_simps(16))
    have h6:"ll  s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n] (s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n])[n]\<rightarrow>next ptrs" 
    using ll_preserved_by_non_aliased_upd[OF h5 h3] by auto
    have h7:"is_valid_llnode_C s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n] n" using Cons next_upd_preserves_validity by auto
    have h8:"ll  s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n] n (n # ptrs)" using Cons(3) h7 h6 by auto
    have h9:"ll  s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n] (s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n])[front]\<rightarrow>next (n # ptrs)" using h8 by (simp add: fun_upd_same)
    have h10:"ll  s'[n\<rightarrow>next := s'[front]\<rightarrow>next][front\<rightarrow>next := n] front (front # n # ptrs)" using Cons h1 a
    by (metis h3 insert_iff list.set(2) ll.heap_abs_simps(31) ll.ll.simps(2) ll.ll_insert_front)
    have h11:"n \<in> set (front # n # ptrs)" by auto
    thus ?case using h10 h11 h1 by metis
  qed
qed

lemma insert:"
\<lbrace> \<lambda> (s::lifted_globals).
  ll s front ptrs
  \<and> s' = s
  \<and> n \<noteq> NULL
  \<and> is_valid_llnode_C s n
  \<and> s[n]\<rightarrow>next = NULL
  \<and> n \<notin> set ptrs
\<rbrace>
  insert' n front
\<lbrace> \<lambda> r s. \<exists> xs_new. ll s r xs_new \<and> n \<in> set xs_new\<rbrace>!"
apply (rule validNF_assume_pre)
apply (unfold insert'_def)
apply wp
apply (rule validNF_chain[OF find_insertion,of " \<lambda> (s::lifted_globals).
  ll s front ptrs
  \<and> s' = s
  \<and> n \<noteq> NULL
  \<and> is_valid_llnode_C s n
  \<and> s[n]\<rightarrow>next = NULL
  \<and> n \<notin> set ptrs" _ ptrs s'])
apply auto
apply (rule exI, rule ll_insert_front, simp+)+
apply (auto intro: ll_insert_not_front ll_all_valid)
apply wp
apply simp
done

end