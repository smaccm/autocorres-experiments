theory Max_DWD imports
  "../../tools/autocorres/AutoCorres"
begin

install_C_file max_DWD.c
autocorres [ heap_abs_syntax, ts_rules = nondet, unsigned_word_abs = max ] max_DWD.c
context max_DWD begin

definition array :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> bool"  where
 "array h p l \<equiv> (\<forall> i < l. is_valid_w32 h (p +\<^sub>p int i))"

lemma "
\<lbrace> \<lambda> (h::lifted_globals). 
  array h p l
  \<and> l < UINT_MAX
  \<and> h' = h \<rbrace> 
 max' p l
\<lbrace> \<lambda> (m::nat) (h::lifted_globals). 
  h' = h 
  \<and> (\<forall> j<l. unat h'[p +\<^sub>p int j] \<le> m) 
  \<and> 0 < l \<longrightarrow> (\<exists> k<l. unat h'[p +\<^sub>p int k] = m)\<rbrace>!
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
apply (auto simp add: array_def less_Suc_eq)
done
