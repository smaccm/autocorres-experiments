theory max imports
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

lemma nat_two_or_greater:"2 \<le> Suc l \<Longrightarrow> \<exists> l'. Suc l = Suc (Suc l')" using le_Suc_ex by fastforce

lemma unat_plus_assoc:" a \<le> a + b  \<Longrightarrow> unat a + unat b = unat (a + b)"
proof -
  assume a1: "a \<le> a + b"
  hence "unat (a + b) - unat a = unat b"
    by (metis add_diff_eq unat_sub zadd_diff_inverse)
  thus ?thesis
    using a1 by (metis (no_types) ordered_cancel_comm_monoid_diff_class.add_diff_inverse word_le_nat_alt)
qed

lemma int_unat_to_uint:"int (unat (x::32 word)) = uint x"
proof -
  have "int (unat x) = int (unat x)" by auto
  then have y1:"int (unat x) = int (nat (uint x))" using unat_def[of x] by auto
  have y2:"0 \<le> uint x" by auto
  thus "int (unat x) = uint x" using nat_0_le[OF y2] y1 by auto
qed

lemma "
  \<lbrace> \<lambda> (s::lifted_globals). len < (unat (max_word::32 word)) \<and> valid_chunk_32 s (a::32 word ptr) len \<and> s' = s \<rbrace> 
 max' a (of_nat len)
  \<lbrace> \<lambda> r s. (\<forall> x. x < len \<longrightarrow> (heap_w32 s (a +\<^sub>p (int x))) \<le> r) \<rbrace>!
"
apply (rule validNF_assume_pre)
apply (unfold max'_def)
apply (subst whileLoop_add_inv [where 
        I = " \<lambda> (i,m) s. (\<forall> x. x \<ge> 0 \<longrightarrow> x < uint i \<longrightarrow> (heap_w32 s (a +\<^sub>p x)) \<le> m) \<and> s = s'"
        and M = "\<lambda>((i,m),_). len - unat i"])
apply wp
apply clarsimp
apply auto
proof - 
  fix aa :: "32 word"
  and b :: "32 word"
  and sa ::"lifted_globals" 
  and x :: "int"
  assume a1:"\<forall>x\<ge>0. x < uint aa \<longrightarrow> sa[a +\<^sub>p x] \<le> b"
  assume a2:"b < (sa[(a +\<^sub>p(uint aa))])"
  assume a3:"x < uint (aa + 1)"
  assume a4:"0 \<le> x"
  then have y1:"x \<le> uint aa" using a3 
    by (metis leD le_less_linear less_le_trans uint_1 uint_add_le zless_imp_add1_zle)
  then have y2:"0 \<le> x \<longrightarrow> x < uint aa \<longrightarrow>  sa[a +\<^sub>p x] \<le> (sa[(a +\<^sub>p(uint aa))])" 
    using a1 a2 by auto
  thus "sa[a +\<^sub>p x] \<le> sa[a +\<^sub>p uint aa]" using y1 y2 a4 by auto
next
  fix aa :: "32 word"
  assume a1:"aa < of_nat len"
  assume a2:"len < unat (max_word::32 word)"
  then have "of_nat len < (max_word::32 word)" using word_of_nat_less[OF
    a2] by auto
  then have "aa < ((max_word::32 word) - 1)" using a1 by (meson
    minus_one_helper2 not_le order_trans)
  then have y1:"aa \<le> aa + 1" by (metis less_le less_x_plus_1 max_word_max
    not_less)
  then have y2:"unat aa < len" using a1 by (metis le_less not_le word_of_nat_less
    word_unat.Rep_inverse')
  then have y3:"0 < len - unat aa" by simp
  thus "len - unat (aa + 1) < len - unat aa" using
  unat_plus_assoc[OF y1] by auto
next
  fix aa :: "32 word"
  assume a1:"aa < of_nat len"
  assume a2:"len < unat (max_word::32 word)"
  then have "of_nat len < (max_word::32 word)" using word_of_nat_less[OF
    a2] by auto
  then have "aa < ((max_word::32 word) - 1)" using a1 by (meson
    minus_one_helper2 not_le order_trans)
  then have y1:"aa \<le> aa + 1" by (metis less_le less_x_plus_1 max_word_max
    not_less)
  then have y2:"unat aa < len" using a1 by (metis le_less not_le word_of_nat_less
    word_unat.Rep_inverse')
  then have y3:"0 < len - unat aa" by simp
  thus "len - unat (aa + 1) < len - unat aa" using
  unat_plus_assoc[OF y1] by auto
next 
  fix aa :: "32 word"
  and x :: "int"
  and b :: "32 word"
  assume a1:"x < uint (aa + 1)"
  assume a2:"\<forall>x\<ge>0. x < uint aa \<longrightarrow> s'[a +\<^sub>p x] \<le> b"
  assume a3:"0 \<le> x"
  assume a4:"\<not> b < s'[a +\<^sub>p uint aa]"
  then have y1:"s'[a +\<^sub>p uint aa] \<le> b" by auto
  then have y2:"x \<le> uint aa" using a1
    by (metis leD le_less_linear less_le_trans uint_1 uint_add_le
      zless_imp_add1_zle)
  thus "s'[a +\<^sub>p x] \<le> b" using a3 a2 y1 by auto
next
  fix aa :: "32 word"
  and b :: "32 word"
  assume a1:"aa < of_nat len"
  assume a2:"valid_chunk_32 s' a len"
  then have "unat aa < len" using a1 unat_less_helper by auto
  then have y1:"int (unat aa) < int len" by auto
  then have y2:"0 \<le> int (unat aa)" by auto
  then have "ptr_valid_32 s' (a +\<^sub>p int (unat aa))" using valid_chunk_32_def a2 y2 y1 by auto
  thus "is_valid_w32 s' (a +\<^sub>p uint aa)" using ptr_valid_32_def int_unat_to_uint by auto
next
  fix aa :: "32 word"
  and b :: "32 word"
  assume a1:"aa < of_nat len"
  assume a2:"valid_chunk_32 s' a len"
  then have "unat aa < len" using a1 unat_less_helper by auto
  then have y1:"int (unat aa) < int len" by auto
  then have y2:"0 \<le> int (unat aa)" by auto
  then have "ptr_valid_32 s' (a +\<^sub>p int (unat aa))" using valid_chunk_32_def a2 y2 y1 by auto
  thus "is_valid_w32 s' (a +\<^sub>p uint aa)" using ptr_valid_32_def int_unat_to_uint by auto
next
  fix aa :: "32 word"
  and b :: "32 word"
  and x :: "nat"
  assume a1:"\<not> aa < of_nat len"
  assume a2:"len < unat (max_word::32 word)"
  assume a3:"\<forall>x\<ge>0. x < uint aa \<longrightarrow> s'[a +\<^sub>p x] \<le> b"
  assume a4:"x < len"
  have y1:"of_nat len \<le> aa" using a1 by auto
  have y2:"len \<le> unat (max_word::32 word)" using a2 by auto
  then have "unat ((of_nat len)::32 word) \<le> unat aa" using y1 word_le_nat_alt by auto
  then have "len \<le> unat aa" using le_unat_uoi[OF y2] by auto
  then have y3:"x < unat aa" using a4 by auto
  then have y4:"int x < uint aa" using y3 by (simp add: uint_nat)
  thus "s'[a +\<^sub>p int x] \<le> b" using a3 y4 by auto
qed

end
