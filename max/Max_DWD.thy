theory Max_DWD imports
  "../../tools/autocorres/AutoCorres"
begin

install_C_file max_DWD.c
autocorres [ heap_abs_syntax, ts_rules = nondet, unsigned_word_abs = max ] max_DWD.c
context max_DWD begin

inductive array :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"  where
  one:"is_valid_w32 h p \<Longrightarrow> array h p (Suc 0) [unat h[p]]"
| more:"\<lbrakk>is_valid_w32 h p; array h (p +\<^sub>p 1) n xs\<rbrakk> \<Longrightarrow> array h p (Suc n) (unat h[p] # xs)"

lemma ptr_distrib[simp]:"p +\<^sub>p x +\<^sub>p y = p +\<^sub>p (x + y)" 
  by (simp add: CTypesDefs.ptr_add_def distrib_right)

lemma all_valid_raw:"array h p l xs \<Longrightarrow> \<forall> i<l. is_valid_w32 h (p +\<^sub>p int i)"
apply(induction rule:array.induct)
apply auto
using less_Suc_eq_0_disj by auto

lemma all_valid:"\<lbrakk>array h p l xs; i < l\<rbrakk> \<Longrightarrow> is_valid_w32 h (p +\<^sub>p int i)" 
  using all_valid_raw by auto

lemma nth_to_offset_raw:"\<lbrakk>array h p l xs \<rbrakk> \<Longrightarrow> \<forall> l'<l. xs ! l' = unat h[p +\<^sub>p int l']"
proof(induction "l" arbitrary: xs p)
  case 0 
  thus ?case by auto
next
  case (Suc n) 
  then have "0 < n \<or> n = 0" by auto
  thus ?case
  proof
    assume "0 < n"
    then obtain xs' where y1:"array h (p +\<^sub>p 1) n xs'" and y2:"xs = unat h[p] # xs'" 
      using Suc 
      by (metis Suc_0_eq_1 diff_Suc_1 gr0_conv_Suc lessI less_nat_zero_code array.simps)
    then have y1:"\<forall>l'<Suc n. l' > 0 \<longrightarrow> xs' ! (l' - 1) = unat h[p +\<^sub>p 1 +\<^sub>p int (l' - 1)]" 
      using Suc(1)[OF y1] by auto
    then have "(unat h[p +\<^sub>p 0] # xs') ! 0 = unat h[p +\<^sub>p 0]" by auto
    thus ?case using y1 by (simp add: Suc_pred' nth_Cons'  y2)
  next
    assume "n = 0"
    thus ?case 
      using Suc by (metis Suc_0_eq_1 int_0 less_one array.simps nth_Cons_0 ptr_add_0_id)
  qed
qed

lemma nth_to_offset[simp]:"\<lbrakk>array h p l xs; l' < l \<rbrakk> \<Longrightarrow>  unat h[p +\<^sub>p int l'] = xs ! l'" 
  using nth_to_offset_raw by auto

lemma "
\<lbrace> \<lambda> (h::lifted_globals). 
  array h p l xs
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
      \<and> (\<forall> j<i. xs ! j \<le> m) 
      \<and> (1 < i \<longrightarrow> (\<exists> k<i. xs ! k = m)) 
      \<and> (i = 0 \<longrightarrow> m = 0) 
      \<and> (i = 1 \<longrightarrow> m = xs ! 0)"
    and M = "\<lambda>((i,m),_).  l - i"])
apply wp
apply (insert all_valid nth_to_offset less_Suc_eq)
apply (clarsimp simp add: uint_nat unat_less_helper diff_less_mono2 word_1_0 not_less_iff_gr_or_eq)
apply (auto simp add: uint_nat unat_less_helper diff_less_mono2 word_1_0 not_less_iff_gr_or_eq)
apply (auto simp add: nth_to_offset_raw)+
apply (meson Zero_not_Suc array.cases)+
done
