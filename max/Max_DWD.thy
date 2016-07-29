theory Max_DWD imports
  "../../tools/autocorres/AutoCorres"
begin

install_C_file max_DWD.c
autocorres [ heap_abs_syntax, ts_rules = nondet, unsigned_word_abs = max ] max_DWD.c
context max_DWD begin

inductive array :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> bool"  where
  one:"is_valid_w32 h p \<Longrightarrow> array h p (Suc 0)"
| more:"\<lbrakk>is_valid_w32 h p; array h (p +\<^sub>p 1) n\<rbrakk> \<Longrightarrow> array h p (Suc n)"

lemma ptr_distrib[simp]:"p +\<^sub>p x +\<^sub>p y = p +\<^sub>p (x + y)" 
  by (simp add: CTypesDefs.ptr_add_def distrib_right)

lemma all_valid_raw:"array h p l \<Longrightarrow> \<forall> i<l. is_valid_w32 h (p +\<^sub>p int i)"
apply(induction rule:array.induct)
apply auto
using less_Suc_eq_0_disj by auto

lemma all_valid:"\<lbrakk>array h p l; i < l\<rbrakk> \<Longrightarrow> is_valid_w32 h (p +\<^sub>p int i)" 
  using all_valid_raw by auto

lemma "
\<lbrace> \<lambda> (h::lifted_globals). 
  array h p l
  \<and> l < UINT_MAX
  \<and> h' = h \<rbrace> 
 max' p l
\<lbrace> \<lambda> (m::nat) (h::lifted_globals). 
  h' = h 
  \<and> (\<forall> j<l. unat h'[p +\<^sub>p int j] \<le> m) 
  \<and> (\<exists> k<l. unat h'[p +\<^sub>p int k] = m)\<rbrace>!
"
apply (rule validNF_assume_pre)
apply (unfold max'_def)
apply (subst whileLoop_add_inv 
  [where 
    I = "\<lambda> (i,m) h. 
      h' = h 
      \<and> i \<le> l 
      \<and> (\<forall> j<i. unat h'[p +\<^sub>p int j] \<le> m) 
      \<and> (0 < i \<longrightarrow> (\<exists> k<i. unat h'[p +\<^sub>p int k] = m)) 
      \<and> (i = 0 \<longrightarrow> 0 = m)"
    and M = "\<lambda>((i,m),_).  l - i"])
apply wp
apply (insert all_valid less_Suc_eq)
apply (auto simp add: uint_nat unat_less_helper diff_less_mono2 word_1_0 not_less_iff_gr_or_eq)
by (meson Zero_not_Suc max_DWD.array.cases)
