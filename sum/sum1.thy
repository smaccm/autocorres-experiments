theory sum1 imports
  "../../tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin

install_C_file "./sum1.c"
autocorres [ ts_rules = nondet ] "./sum1.c"
context sum1 begin

lemma invariant1:"\<lbrakk> 0 \<le> x; (x::int) \<le> 92681 \<rbrakk> \<Longrightarrow> x * (x + 1) < 2^33"
proof -
  assume "0 \<le> x" "x \<le> 92681"
  hence "x * (x + 1) \<le> 92681 * 92682"
    using mult_mono[where b=92681 and d=92682] by fastforce
  thus "x * (x  + 1) < 2^33" by simp
qed


lemma foo:"\<lbrakk>0 \<le> a; a \<le> uint max_word; 0 \<le> b; b \<le>
uint max_word; a \<le> b; c \<le> word_of_int a\<rbrakk> \<Longrightarrow> c \<le> word_of_int b"
sorry

lemma plus_one_mono_32word:"(b::32 word) \<le> (max_word - 1) \<Longrightarrow> b \<le> b + 1" by (metis
(no_types, hide_lams) add_diff_cancel_right add_uminus_conv_diff
dual_order.strict_iff_order eq_iff less_x_plus_1 max_word_max
zadd_diff_inverse)



lemma "
  \<lbrace> \<lambda> a. x \<ge> 0 \<and> x \<le> 92681 \<rbrace> 
 sum' ((word_of_int x)::32 word)
  \<lbrace> \<lambda> r a. 2 * (uint r) = x * (x + 1) \<rbrace>!
"
apply (rule validNF_assume_pre)
apply (unfold sum'_def)
apply clarsimp
apply (subst whileLoop_add_inv [where 
        I = " \<lambda> (r,i) a. (2 * (uint r) 
                            = x * (x + 1) - uint i * (uint i + 1))
                         \<and> i \<le> (word_of_int x)
                         \<and> r \<le> r + i"
        and M = "\<lambda>((_,i),a). unat (i+1)"])
apply wp 
apply clarsimp
apply (auto simp: measure_unat)
proof -
  fix a :: "32 word" and b :: "32 word"
  assume a1: "b \<le> word_of_int x"
  assume a2: "0 < b"
  then have y1: "0 \<le> b - 1" by auto
  then have y2: "b - 1 < b" using a2 y1 minus_one_helper5 by force
  thus "b - 1 \<le> word_of_int x" using a1 by auto
next
  fix a :: "32 word" and b :: "32 word"
  assume "\<not> 0 < b" 
  then have " 0 = b" using word_neq_0_conv by blast
  thus "uint b = 0" by auto
next
  fix a :: "32 word" and b :: "32 word"
  assume a1:"0 \<le> x"
  assume a2:"x \<le> 92681"
  then have y1:"x < 2 ^ len_of TYPE(32)" by auto
  then have y2:"word_of_int x = word_of_int x" by auto
  thus "x * (x + 1) = uint ((word_of_int x :: 32 word)) * (uint ((word_of_int x) :: 32 word) + 1)" using
  word_of_int_inverse[OF y2 a1 y1] by auto
next
  fix a :: "32 word" and b :: "32 word"
  assume a1:"x \<le> 92681"
  assume a2:"b \<le> word_of_int x"
  assume a3:"0 \<le> x"
  assume a4:"0 < b"
  then have y1:"2^32 - 1 = (max_word::32 word)" by (simp add:max_word_eq)
  then have y2:"2^32 - 1 = uint ((2^32 - 1)::32 word)" by eval 
  then have y3:"2^32 - 1 = uint (max_word::32 word)" using y1 y2 by auto
  then have y4:"x \<le> uint (max_word::32 word)" using a1 y3 by auto
  then have y5:"(0::int) \<le> 92681" by auto
  then have y6:"92681 \<le> uint (max_word::32 word)" using y3 by auto
  then have "b \<le> word_of_int 92681" using foo[OF a3 y4 y5 y6 a1 a2] by auto
  then have y7:"b \<le> 92681" by auto
  then have y8:"92681 \<le> (max_word::32 word) - 1" by eval
  then have y8:"b \<le> max_word - 1" using y7 by auto
  then have y8:"b \<le> b + 1" using plus_one_mono_32word[of b] by auto
  then have y9:"unat b \<le> unat (b + 1)" by (simp add:word_le_nat_alt)
  thus "unat b < unat (b + 1)" by (simp add: dual_order.strict_iff_order)
next
  fix a :: "32 word" and b :: "32 word"
  assume a1:"x \<le> 92681"
  assume a2:"b \<le> word_of_int x"
  assume a3:"0 \<le> x"
  assume a4:"0 < b"
  assume a5:"a \<le> a + b"
  assume a6:"2 * uint a = x * (x + 1) - uint b * (uint b + 1)"
  then have "a + b \<le> (max_word::32 word)" using a5 by blast

(*  then have y1:"2 * uint a \<le> x * (x + 1)" by auto
  then have y2:"x * (x + 1) < 2^33" using invariant1[OF a3 a1] by simp
  then have "2 * uint a < 2^33" using y1 y2 by linarith
  then have "uint a < 2^32" using y1 y2 by auto
  then have "a \<le> (max_word::32 word)" using y1 y2 max_word_eq by auto *)
  
(*  then have "(x * (x + 1)) div 2 < 2^32" by fastforce
  then have "uint a < 2^32" using a5 *)
(*
sledgehammer

apply (metis add.comm_neutral add.commute diff_add_cancel inc_le linorder_not_le
  uint_1 uint_minus_simple_alt zless_add1_eq)
using uint_eq_0 word_neq_0_conv apply blast
apply (auto simp: word_of_int_inverse)
*)

end

end