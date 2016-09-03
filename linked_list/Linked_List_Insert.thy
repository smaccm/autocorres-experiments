theory Linked_List_Insert imports
 "/home/dacosta/development/rockwellcollins/l4v/tools/autocorres/AutoCorres"
 "/home/dacosta/development/rockwellcollins/l4v/tools/autocorres/DataStructures"
begin

text{* 

Author: Dan DaCosta
Description: Work towards a correctness proof of an order preserving linked list insert. Insertion
relies on a function, find_insertion, to find the correct placement for the new node. Currently,
there is a proof that find_insertion finds the insertion point according to the following 
statements:

  - find_insertion does not alter the heap

  - if find_insertion returns a non-null node n, then all ancestors of n and n have values less than
  or equal to value find_insertion was called with.

  - if find_insertion returns a non-null node n and n's direct descendant is not null than n's 
  direct descendant has a value greater than that of what find_insertion was called with.

  - if find_insertion returns null then either the list find_insertion was called with was null or
  the first element of the list is greater than the value find_insertion was called with.

TODO:
 
 - Requires significant cleanup.

 - A proof that insert uses find_insertion to insert a new element into a linked list preserving
 ascending order must be given.

*}

install_C_file linked_list.c
autocorres [ heap_abs_syntax, ts_rules = nondet] linked_list.c
context linked_list begin

interpretation DataStructures.linked_list next_C NULL
done

declare list_split [simp del]
declare path_split [simp del]

fun lkup :: "lifted_globals \<Rightarrow> ll_C ptr \<Rightarrow> ll_C option" where 
"lkup s a = (if is_valid_ll_C s a then Some (s[a]) else None)"

declare lkup.simps [simp del]

lemma list_no_null:"list (lkup s') xs i \<Longrightarrow> NULL \<notin> set xs"
 apply (induction xs arbitrary: i) by auto

lemma list_next:"\<lbrakk>list (lkup s) xs i; j \<in> set xs; s[j]\<rightarrow>next \<noteq> NULL\<rbrakk> \<Longrightarrow> s[j]\<rightarrow>next \<in> set xs"
 apply (induction xs arbitrary: i j)
 apply auto
 by (metis linked_list.get_ll_next_def linked_list.lkup.simps list_mem option.distinct(1) option.sel)

lemma list_all_valid:"\<lbrakk>list (lkup s) xs i; j \<in> set xs\<rbrakk> \<Longrightarrow> is_valid_ll_C s j"
 apply (induction xs arbitrary: i j)
 apply auto
 by (metis linked_list.lkup.simps option.distinct(1))

lemma the_list_next_is_smaller:"\<lbrakk>list (lkup s) xs i; j \<in> set xs\<rbrakk>
       \<Longrightarrow> length (the_list (lkup s) s[j]\<rightarrow>next) < length (the_list (lkup s) j)"
 apply (induction xs arbitrary: i j)
 apply auto
 by (metis (no_types, hide_lams) add.right_neutral add_Suc_right is_list_non_NULL lessI 
    linked_list.get_ll_next_def linked_list.list_is_list list.size(4) lkup.simps option.distinct(1) 
    option.sel the_list_non_NULL)


lemma the_list_absurd:
  "\<lbrakk>is_valid_ll_C s x; x \<noteq> NULL; s[x]\<rightarrow>next = NULL; the_list (lkup s) x = []\<rbrakk> \<Longrightarrow> False"
 by (metis lkup.simps is_list_non_NULL linked_list.is_list_empty linked_list.get_ll_next_def 
    the_list_empty')

lemma path_null_list_imp: "list s xs i \<Longrightarrow> path s i xs NULL"
 using path_null_list by auto

lemma list_singleton:"\<lbrakk>list (lkup s) xs a; a \<noteq> NULL; s[a]\<rightarrow>next = NULL\<rbrakk> \<Longrightarrow> xs = [a]"
 apply (cases xs, auto) 
 by (metis linked_list.list_empty linked_list.get_ll_next_def linked_list.lkup.simps 
    option.distinct(1) option.sel)

lemma list_non_empty:"list (lkup s) (x # xs) i \<Longrightarrow> i \<noteq> NULL \<and> x = i \<and> is_valid_ll_C s i \<and> list (lkup s) xs s[i]\<rightarrow>next"
 by (metis linked_list.get_ll_next_def linked_list.list_all_valid linked_list.lkup.simps 
    list.set_intros(1) local.list.simps(2) option.sel)

lemma list_path_no_cycles:"\<lbrakk>list (lkup s) xs i; a \<in> set xs; path (lkup s) a ys a\<rbrakk> \<Longrightarrow> ys = []"
proof (induction xs arbitrary: i)
  case Nil
  thus ?case by auto
next
  case (Cons x xs)
  have "a = i \<or> a \<noteq> i" using Cons by auto
  thus ?case
  proof
    assume "a = i"
    thus ?case using Cons by (meson append_self_conv2 list_split list_unique)
  next
    assume a:"a \<noteq> i"
    then have "x = i \<and> list (lkup s) xs (s[i]\<rightarrow>next)" using Cons list_non_empty by blast
    then have h1:"x = i" and h2:"list (lkup s) xs (s[i]\<rightarrow>next)" by auto
    thus ?case using Cons Cons(1)[OF h2 _ Cons(4)] a by auto
  qed
qed

lemma paths_preserve_list:
"\<lbrakk>list (lkup s) xs i; a \<in> set xs; path (lkup s) i xs1 a; path (lkup s) a xs2 NULL\<rbrakk> 
 \<Longrightarrow> xs = xs1 @ xs2"
proof (induction xs arbitrary: i)
  case Nil
  thus ?case by auto
next
  case (Cons x xs)
  have "a = i \<or> a \<noteq> i" using Cons by auto
  thus ?case
  proof
    assume "a = i"
    thus ?case using Cons list_path_no_cycles 
      by (metis append_self_conv2 list_unique path_null_list)
  next
    assume a:"a \<noteq> i"
    then have "x = i \<and> list (lkup s) xs (s[i]\<rightarrow>next)" using list_non_empty Cons by blast
    then have h1:"x = i" and h2:"list (lkup s) xs (s[i]\<rightarrow>next)" by auto
    thus ?case 
      using Cons(1)[OF h2 _ _ Cons(5)] Cons a by (meson list_split list_unique path_null_list) 
  qed
qed

lemma path_extend:
"\<lbrakk>path (lkup s) i xs a; a \<noteq> NULL; is_valid_ll_C s a\<rbrakk> \<Longrightarrow> path (lkup s) i (xs@[a]) s[a]\<rightarrow>next"
proof(induction xs arbitrary:i)
  case Nil
  thus ?case by (simp add: linked_list.get_ll_next_def linked_list.lkup.simps)
next
  case (Cons x xs)
  then have "i \<noteq> NULL \<and> is_valid_ll_C s a \<and> i = x \<and> path (lkup s) s[i]\<rightarrow>next xs a" 
    using lkup.simps 
    by (metis linked_list.get_ll_next_def option.distinct(1) option.sel path.simps(2))
  then have h1:"i = x" and h2:"path (lkup s) s[i]\<rightarrow>next xs a" and h3:"i \<noteq> NULL" and h4:"is_valid_ll_C s a" by auto
  then have "path (lkup s) s[i]\<rightarrow>next (xs @ [a]) s[a]\<rightarrow>next" using Cons(1)[OF h2 Cons(3) Cons(4)] by auto
  thus ?case 
    using h3 h4 h1 Cons.prems(1) append_Cons linked_list.get_ll_next_def 
    by (metis lkup.simps option.simps(3) path.simps(2))
qed

lemma path_shorten:"\<lbrakk>path (lkup s) i xs NULL; i \<noteq> NULL\<rbrakk> \<Longrightarrow> path (lkup s) s[i]\<rightarrow>next (tl xs) NULL"
proof -
  assume a1:"path (lkup s) i xs NULL"
  and a2:"i \<noteq> NULL"
  have "s[i]\<rightarrow>next = NULL \<or> s[i]\<rightarrow>next \<noteq> NULL" by simp
  thus ?thesis
  proof 
    assume "s[i]\<rightarrow>next = NULL"
    thus ?thesis 
      using a1 a2 linked_list.path.simps(1) linked_list.path_null_list 
            linked_list.list_singleton list.sel(3) 
      by fastforce
  next
    assume "s[i]\<rightarrow>next \<noteq> NULL"
    thus ?thesis by (metis a1 a2 linked_list.path_null_list list.sel(3) list_non_empty path_next)
  qed
qed

lemma find_insertion_1_loop_step:
assumes a1:"list (lkup s) xs i"
and a2:"path (lkup s) i xs1 a"
and a3:"\<forall>x\<in>set xs1. sint s[x]\<rightarrow>val \<le> v"
and a4:"path (lkup s) a xs2 NULL"
and a5:"a \<noteq> NULL"
and a6:"sint s[a]\<rightarrow>val \<le> v"
and a7:"a \<in> set xs"
shows "\<exists>xs1. path (lkup s) i xs1 s[a]\<rightarrow>next 
       \<and> (\<exists>xs2. path (lkup s) s[a]\<rightarrow>next xs2 NULL) 
       \<and> (\<forall>x\<in>set xs1. sint s[x]\<rightarrow>val \<le> v)"
proof - 
  have h1:"path (lkup s) i (xs1 @ [a]) s[a]\<rightarrow>next" using path_extend[OF a2 a5 list_all_valid[OF a1 a7]] by simp
  then have h2:"path (lkup s) s[a]\<rightarrow>next (tl xs2) NULL" using path_shorten[OF a4 a5] by simp
  then have h3:"\<forall>x\<in>set (xs1@[a]). sint s[x]\<rightarrow>val \<le> v" using a3 a6 by simp
  thus ?thesis using h1 h2 h3 by metis
qed

lemma find_insertion_1:
"\<lbrace> \<lambda> (s::lifted_globals). 
  s' = s
  \<and> i \<noteq> NULL
  \<and> sint s'[i]\<rightarrow>val \<le> v
  \<and> list (lkup s) xs i \<rbrace>
  find_insertion' v i
\<lbrace> \<lambda> r s.
  s' = s
  \<and> r \<noteq> NULL
  \<and> (s[r]\<rightarrow>next = NULL \<or> (s[r]\<rightarrow>next \<noteq> NULL \<and>  v < sint s[s[r]\<rightarrow>next]\<rightarrow>val))
  \<and> (\<exists> xs1 xs2.
       path (lkup s) i xs1 s[r]\<rightarrow>next 
       \<and> path (lkup s) s[r]\<rightarrow>next xs2 NULL
       \<and> (\<forall> x \<in> set xs1. sint s[x]\<rightarrow>val \<le> v))
\<rbrace>!"
 apply (rule validNF_assume_pre)
 apply (unfold find_insertion'_def)
 apply (subst whileLoop_add_inv [where 
  I = " \<lambda> (it,last,cond) s. 
       s = s'
       \<and> (cond \<noteq> 0 \<longrightarrow> it \<noteq> NULL \<and> sint s[it]\<rightarrow>val \<le> v \<and> it \<in> set xs)
       \<and> (cond = 0 \<longrightarrow> last \<noteq> NULL \<and> (it = NULL \<or> v < sint s[it]\<rightarrow>val))
       \<and> (last \<noteq> NULL \<longrightarrow> s[last]\<rightarrow>next = it \<and> last \<in> set xs)
       \<and> (\<exists> xs1 xs2. path (lkup s) i xs1 it \<and> path (lkup s) it xs2 NULL \<and> (\<forall> x \<in> set xs1. sint s[x]\<rightarrow>val \<le> v))
" 
  and M = "\<lambda>((it,r,_),s). length (the_list (lkup s) it)"])
 apply wp
    apply (clarsimp,auto intro: list_all_valid list_next list_mem the_list_next_is_smaller path_null_list_imp the_list_absurd find_insertion_1_loop_step)[1]
   apply (clarsimp, auto)
  apply wp
 apply (auto intro: list_mem list_all_valid) 
 apply (metis empty_iff linked_list.path.simps(1) linked_list.path_null_list list.set(1))
done

lemma find_insertion_2:
"\<lbrace> \<lambda> (s::lifted_globals). 
  s' = s
  \<and> i = NULL
  \<and> list (lkup s) xs i \<rbrace>
  find_insertion' v i
\<lbrace> \<lambda> r s.
  s' = s
  \<and> r = NULL
\<rbrace>!"
 apply (unfold find_insertion'_def)
 apply (subst whileLoop_unroll)
 apply wp
    apply (rule validNF_false_pre)
   apply (rule validNF_false_pre)
  apply wp
 apply auto
done

lemma find_insertion_3:
"\<lbrace> \<lambda> (s::lifted_globals). 
  s' = s
  \<and> i \<noteq> NULL
  \<and> v < sint s'[i]\<rightarrow>val
  \<and> list (lkup s) xs i \<rbrace>
  find_insertion' v i
\<lbrace> \<lambda> r s.
  s' = s
  \<and> r = NULL
  \<and> v < sint s'[i]\<rightarrow>val
\<rbrace>!"
 apply (unfold find_insertion'_def)
 apply (subst whileLoop_unroll)
 apply wp
    apply (rule validNF_false_pre)
   apply (rule validNF_false_pre)
  apply wp
 apply (auto intro: list_all_valid list_mem) 
done


lemma separate_cases:"(\<And>s. s' = s \<and> list (lkup s) xs i \<Longrightarrow>
        (s' = s \<and> i \<noteq> NULL \<and> sint s'[i]\<rightarrow>val \<le> v \<and> list (lkup s) xs i 
        \<or> s' = s \<and> i = NULL \<and> list (lkup s) xs i) 
        \<or> s' = s \<and> i \<noteq> NULL \<and> v < sint s'[i]\<rightarrow>val \<and> list (lkup s) xs i) "
by auto

lemma find_insertion:
"
\<lbrace> \<lambda> (s::lifted_globals). 
  s' = s
  \<and> list (lkup s) xs i \<rbrace>
  find_insertion' v i
\<lbrace> \<lambda> r s.
  (s' = s \<and> r \<noteq> NULL \<and>
                     (s[r]\<rightarrow>next = NULL \<or> s[r]\<rightarrow>next \<noteq> NULL \<and> v < sint s[s[r]\<rightarrow>next]\<rightarrow>val) \<and>
                     (\<exists>xs1 xs2. path (lkup s) i xs1 s[r]\<rightarrow>next \<and> path (lkup s) s[r]\<rightarrow>next xs2 NULL \<and> (\<forall>x\<in>set xs1. sint s[x]\<rightarrow>val \<le> v)) \<or>
            s' = s \<and> r = NULL) \<or>
           s' = s \<and> r = NULL \<and> v < sint s'[i]\<rightarrow>val
\<rbrace>!"
using validNF_weaken_pre[OF 
        validNF_vcg_disj_lift[OF 
          validNF_vcg_disj_lift[OF find_insertion_1 find_insertion_2]  
          find_insertion_3, 
          of s' i v xs s' xs s' xs],
        of "\<lambda> s . s' = s \<and> list (lkup s) xs i", 
      OF separate_cases] by simp

lemma "\<lbrace> \<lambda> (s::lifted_globals). 
  s' = s
  \<and> n \<noteq> NULL
  \<and> is_valid_ll_C s n
  \<and> s[n]\<rightarrow>next = NULL
  \<and> list (lkup s) xs' i 
  \<and> sorted xs
  \<and> (\<forall> x \<in> set xs. n \<noteq> x)\<rbrace>
  insert' n i
\<lbrace> \<lambda> r s. (\<exists> xs. list (lkup s) xs' r \<and> n \<in> set xs' \<and> sorted xs')\<rbrace>!"
oops

end