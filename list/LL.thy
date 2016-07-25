theory LL imports
 "/home/dacosta/development/rockwellcollins/l4v/tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin

new_C_include_dir "/home/dacosta/development/rockwellcollins/verification/musllibc/include"

install_C_file "./ll.c"
autocorres [ heap_abs_syntax, ts_rules = nondet] "./ll.c"

context ll begin


fun ll :: "lifted_globals \<Rightarrow> llnode_C ptr \<Rightarrow> llnode_C ptr list \<Rightarrow> bool" where
  "ll s i [] = (i = NULL)"
| "ll s i (x # xs) = (i = x \<and> i \<noteq> NULL \<and> is_valid_llnode_C s i \<and> ll s s[i]\<rightarrow>next xs)"

lemma ll_path_unique:"\<lbrakk>ll s i xs; ll s i ys\<rbrakk>\<Longrightarrow> xs = ys"
proof(induction xs arbitrary: i ys)
  case Nil
  thus ?case using ll.elims(2) ll.simps(1) by auto
next
  case (Cons x xs)
  then have y1:"i \<noteq> NULL" by auto
  then have y2:"ll s s[i]\<rightarrow>next xs" using Cons by auto
  then obtain ys' where y3:"ys = i # ys'" using Cons.prems(2) ll.ll.elims(2) y1 by blast
  then have y4:"ll s s[i]\<rightarrow>next ys'" using Cons by auto
  then have y5:"xs = ys'" using Cons(1)[OF y2 y4] by auto
  then have y6:"x = i" using Cons by auto
  thus ?case using y6 y3 y5 by auto
qed

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


lemma find_insertion_weak:"
\<lbrace> \<lambda> (s::lifted_globals). s' = s \<and> ll s' front xs \<rbrace>
  find_insertion' val front
\<lbrace> \<lambda> r s. 
  s = s' 
  \<and> (r \<noteq> NULL \<longrightarrow> (s[r]\<rightarrow>val \<le> val \<and> r \<in> set xs))
  \<and> (r = NULL \<longrightarrow> front \<noteq> NULL \<longrightarrow> val < s[front]\<rightarrow>val)
\<rbrace>!"
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
apply wp
apply clarsimp
apply auto
using  loop_support_1 loop_support_2 ll.ll_suffix_ex ll.to_list_length_ineq_1
apply (meson ll.ll.elims(2) ll.ll_suffix | blast )+
apply wp
by (metis if_P_1_0_eq_0 list.set_intros(1) ll.ll.elims(2) not_less)

lemma less_than_prefix:"\<lbrakk>xs = ys @[ x ]@ zs; sorted xs;distinct xs\<rbrakk> \<Longrightarrow> \<forall> y \<in> set ys . y < x"
apply(induction ys arbitrary: xs,simp)
using sorted_Cons by fastforce

lemma greater_than_suffix:"\<lbrakk>xs = ys @[ x ]@ zs; sorted xs;distinct xs\<rbrakk> \<Longrightarrow>  \<forall> z \<in> set zs. x < z"
apply(induction ys arbitrary: xs,simp)
using antisym_conv1 sorted_Cons apply fastforce
by (simp add: sorted_Cons)

lemma llnode_val_less_than_prefix:
"\<lbrakk>xs = ys @[ x ]@ zs; sorted (map (\<lambda>x. s[x]\<rightarrow>val ) xs); distinct (map (\<lambda>x. s[x]\<rightarrow>val ) xs)\<rbrakk> 
 \<Longrightarrow>  \<forall> y \<in> set ys. s[y]\<rightarrow>val < s[x]\<rightarrow>val"
proof -
  assume a1:"xs = ys @[ x ]@ zs"
  assume a2:"sorted (map (\<lambda>x. s[x]\<rightarrow>val ) xs)"
  assume a3:"distinct (map (\<lambda>x. s[x]\<rightarrow>val ) xs)"
  then obtain bs where y1:"bs = map (\<lambda>x. s[x]\<rightarrow>val ) ys" by auto
  then obtain cs where y2:"cs = map(\<lambda>x. s[x]\<rightarrow>val ) zs" by auto
  then obtain a where y3:"a = s[x]\<rightarrow>val" by auto
  then have y4:"sorted (bs @ [ a ] @ cs)" 
    using a1 a2 append_Cons append_Nil list.simps(9) map_append y1 y2 by auto
  then have y5:"distinct (bs @ [ a ] @ cs)" using a1 a3 y1 y2 y3 by auto
  thus ?thesis using  less_than_prefix[OF _ y4 y5] y3 y1 by auto
qed

lemma llnode_val_greater_than_suffix:
"\<lbrakk>xs = ys @[ x ]@ zs; sorted (map (\<lambda>x. s[x]\<rightarrow>val ) xs); distinct (map (\<lambda>x. s[x]\<rightarrow>val ) xs)\<rbrakk> 
  \<Longrightarrow>  \<forall> z \<in> set zs. s[x]\<rightarrow>val < s[z]\<rightarrow>val"
proof -
  assume a1:"xs = ys @[ x ]@ zs"
  assume a2:"sorted (map (\<lambda>x. s[x]\<rightarrow>val ) xs)"
  assume a3:"distinct (map (\<lambda>x. s[x]\<rightarrow>val ) xs)"
  then obtain bs where y1:"bs = map (\<lambda>x. s[x]\<rightarrow>val ) ys" by auto
  then obtain cs where y2:"cs = map(\<lambda>x. s[x]\<rightarrow>val ) zs" by auto
  then obtain a where y3:"a = s[x]\<rightarrow>val" by auto
  then have y4:"sorted (bs @ [ a ] @ cs)" using a1 a2 append_Cons append_Nil list.simps(9) map_append y1 y2 by auto
  then have y5:"distinct (bs @ [ a ] @ cs)" using a1 a3 y1 y2 y3 by auto
  then have y6:"\<forall> c \<in> set cs. a < c" using greater_than_suffix[OF _ y4 y5] by auto
  thus ?thesis using y3 y2 by auto
qed

lemma insertion_found:
"\<lbrakk>ll s front xs; sorted (map (\<lambda> x. s[x]\<rightarrow>val) xs); 
  distinct (map (\<lambda> x. s[x]\<rightarrow>val) xs); 
  s[r]\<rightarrow>val \<le> val; 
  r \<in> set xs; r \<noteq> NULL \<rbrakk>
  \<Longrightarrow> (\<exists> ys zs. 
      xs = ys @ [r] @ zs 
      \<and> (\<forall> y \<in> set ys. s[y]\<rightarrow>val < s[r]\<rightarrow>val)
      \<and> s[r]\<rightarrow>val \<le> val 
      \<and> (\<forall> z \<in> set zs. s[r]\<rightarrow>val < s[z]\<rightarrow>val))"
proof -
    assume a1:"ll s front xs"
    assume a2:"sorted (map (\<lambda> x. s[x]\<rightarrow>val) xs)"
    assume a3:"distinct (map (\<lambda> x. s[x]\<rightarrow>val) xs)"
    assume a4:"s[r]\<rightarrow>val \<le> val"
    assume a5:"r \<in> set xs"
    obtain ys zs where y1:"xs = ys @ [ r ] @ zs" 
      using a5 by (metis append_Cons append_Nil in_set_conv_decomp)
    have y2:"(\<forall> y \<in> set ys. s[y]\<rightarrow>val < s[r]\<rightarrow>val)" 
      using llnode_val_less_than_prefix[OF y1 a2 a3] by auto
    have y3:"(\<forall> z \<in> set zs. s[r]\<rightarrow>val < s[z]\<rightarrow>val)" 
      using llnode_val_greater_than_suffix[OF y1 a2 a3] by auto
    thus ?thesis using y1 y2 y3 a4 by auto 
qed

lemma lt_first_lt_all:
"\<lbrakk>ll s front xs; sorted (map (\<lambda> x. s[x]\<rightarrow>val) xs); front \<noteq> NULL; val < s[front]\<rightarrow>val\<rbrakk> 
  \<Longrightarrow> \<forall> x \<in> set xs. val < s[x]\<rightarrow>val"
proof -
  assume a1:"ll s front xs"
  assume a2:"sorted (map (\<lambda> x. s[x]\<rightarrow>val) xs)"
  assume a3:"front \<noteq> NULL"
  assume a4:"val < s[front]\<rightarrow>val"
  obtain xs' where y1:"xs = front # xs'" using ll_non_null_form[OF a1 a3] by auto
  then obtain ys where y2:"ys = (map (\<lambda> x. s[x]\<rightarrow>val) xs)" by auto
  then have "\<forall> y \<in> set (tl ys). val < y" 
    using y1 a2 a4 by (simp add: less_le_trans list.sel(1) list.simps(3) list.simps(9) sorted_Cons)
  thus ?thesis using y1 y2 
    using a4 image_eqI list.map(2) list.sel(3) set_ConsD set_map by auto
qed

definition R where
"R s val front xs r d \<equiv> 
(r \<noteq> NULL \<longrightarrow> 
    (\<exists> ys zs. xs = 
      ys @ [r] @ zs 
      \<and> (\<forall> y \<in> set ys. s[y]\<rightarrow>val < s[r]\<rightarrow>val)
      \<and> s[r]\<rightarrow>val \<le> val 
      \<and> (\<forall> z \<in> set zs. s[r]\<rightarrow>val < s[z]\<rightarrow>val)))
\<and> (r = NULL \<longrightarrow> front \<noteq> NULL \<longrightarrow> (\<forall> x \<in> set xs. val < s[x]\<rightarrow>val))"

lemma find_insertion[wp]:"
\<lbrace> \<lambda> (s::lifted_globals). 
s' = s
\<and> ll s' front xs
\<and> sorted (map (\<lambda> x. s'[x]\<rightarrow>val) xs)
\<and> distinct (map (\<lambda> x. s'[x]\<rightarrow>val) xs)
\<rbrace>
  find_insertion' val front
\<lbrace> \<lambda> r s. 
R s' val front xs r s
 \<rbrace>!"
apply (rule validNF_assume_pre)
apply (rule validNF_chain)
apply (rule find_insertion_weak[of s' front xs]) 
apply(unfold R_def)
using insertion_found lt_first_lt_all apply (unfold R_def | clarsimp | simp)+
done



lemma "
\<lbrace> \<lambda> (s::lifted_globals). 
ll s front xs
\<and> is_valid_llnode_C s i
\<and> sorted (map (\<lambda> x. s[x]\<rightarrow>val) xs)
\<and> distinct (map (\<lambda> x. s[x]\<rightarrow>val) xs)
\<rbrace>
  insert' i  front
\<lbrace> \<lambda> r s. 
\<exists> xs. ll s front xs
\<and> sorted (map (\<lambda> x. s[x]\<rightarrow>val) xs)
\<and> distinct (map (\<lambda> x. s[x]\<rightarrow>val) xs)
 \<rbrace>!"
apply (unfold insert'_def)
apply (rule condition_wp)

end

end