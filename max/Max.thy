theory Max imports
  "../../tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin

install_C_file "./max.c"
autocorres [ heap_abs_syntax, ts_rules = nondet ] "./max.c"
context max begin

definition
  ptr_valid_32 :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> bool"
where
  "ptr_valid_32 s p \<equiv> is_valid_w32 s (ptr_coerce p)"

definition
  valid_chunk_32 :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_chunk_32 s p l \<equiv> (\<forall> i. i < int l \<longrightarrow> ptr_valid_32 s (p +\<^sub>p i))"

lemma "
\<lbrace> \<lambda> (s::lifted_globals). 
len < (unat (max_word::32 word)) 
\<and> valid_chunk_32 s (a::32 word ptr) len 
\<and> s' = s \<rbrace> 
 max' a (of_nat len)
\<lbrace> \<lambda> r s. x < len \<longrightarrow> (heap_w32 s (a +\<^sub>p (int x))) \<le> r \<rbrace>!
"
apply (rule validNF_assume_pre)
apply (unfold max'_def)
apply (subst whileLoop_add_inv [where 
        I = " \<lambda> (i,m) s. (\<forall> x. x \<ge> 0 \<longrightarrow> x < uint i \<longrightarrow> (heap_w32 s (a +\<^sub>p x)) \<le> m) \<and> s = s'"
        and M = "\<lambda>((i,m),_). len - unat i"])
apply wp
apply clarsimp
apply 
  (auto 
    simp add: 
      diff_less_mono2 
      word_1_0 
      max.valid_chunk_32_def 
      ptr_valid_32_def 
      uint_nat 
      unat_less_helper)+
apply 
  (metis (no_types, hide_lams) 
    zless_add1_eq 
    less_le_trans
    uint_1
    uint_add_le
    less_imp_le
    less_le_trans
    not_less
    uint_nat)
apply 
  (metis (no_types) uint_nat zless_add1_eq  less_le_trans uint_1 uint_add_le less_le_trans not_less)
apply
  (metis (no_types) 
    le_less_trans 
    le_unat_uoi 
    less_imp_le
    not_less_iff_gr_or_eq
    of_nat_0_le_iff
    of_nat_less_iff word_less_nat_alt)
done

end
