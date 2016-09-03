theory Sum imports
  "../../tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin
text{* 

Author: Dan DaCosta
Description: Correctness proof for a function that calculates the sum from zero to n naively.
TODO: loop_support lemma should be cleaned up.

*}

install_C_file "./sum.c"
autocorres [ ts_rules = nondet ] "./sum.c"
context sum begin

lemma loop_support:"
\<lbrakk> \<not> result_C a + b \<le> result_C a; 2 * uint (result_C a) = x * (x + 1) - uint b * (uint b + 1)\<rbrakk>
 \<Longrightarrow> 2 * uint (result_C a + b) = x * (x + 1) - uint (b - 1) * (uint (b - 1) + 1)"
proof -
  assume A:" 2 * uint (result_C a) = x * (x + 1) - uint b * (uint b + 1)"
  assume B:"\<not> result_C a + b \<le> result_C a"
  then have B:"result_C a + b > result_C a" by simp
  then have C:"b > 0" using word_neq_0_conv by fastforce
  then have 
    "2 * uint (result_C a + b) 
     = x * (x + 1) - uint b * (uint b + 1) + 2 * uint b" 
    using B by (simp add: A distrib_left less_imp_le uint_plus_simple)
  then have 
    "2 * uint (result_C a + b) 
     = x * (x + 1) - (uint b * uint b + uint b) + 2 * uint b" 
    by (metis (no_types, hide_lams) diff_diff_eq2 
        diff_zero mult.right_neutral mult_eq_0_iff right_diff_distrib)
  then have 
    "2 * uint (result_C a + b) = x * (x + 1) - ((uint b - 1) * uint b)" 
    by (simp add: mult.commute right_diff_distrib)
  then have 
    "2 * uint (result_C a + b) = x * (x + 1) - (uint (b - 1) * uint b)" 
    using C by (metis add.left_neutral linorder_not_less uint_1 uint_eq_0 
                uint_minus_simple_alt word_less_def zless_imp_add1_zle)
  then have 
    "2 * uint (result_C a + b) 
     = x * (x + 1) - uint (b - 1) * (uint (b - 1) + 1)" 
    using C by (metis dual_order.strict_iff_order eq_diff_eq gt0_iff_gem1 
                      uint_1 uint_plus_simple)
  thus ?thesis by simp
qed


lemma "
\<lbrace> \<lambda> a. x \<ge> 0 \<and> 2^32 > x \<rbrace> 
 sum' ((word_of_int x)::32 word)
\<lbrace> \<lambda> r a. 2 * uint (result_C r) = x * (x + 1) \<or> overflow_C r = 1\<rbrace>!
"
 apply (rule validNF_assume_pre)
 apply (unfold sum'_def)
 apply clarsimp
 apply (subst whileLoop_add_inv [where 
        I = " \<lambda> (r,i) a. (((2 * uint (result_C r) 
                            = (x * (x + 1)) - (uint i * ((uint i) + 1)))) 
                            \<or> overflow_C r = 1)" 
        and M = "\<lambda>((_,i),a). unat i"])
 apply wp 
   apply (clarsimp,auto intro: loop_support simp: measure_unat)
  using uint_eq_0 word_neq_0_conv apply blast
 using word_of_int_inverse[of x "(word_of_int x)::32 word"] apply auto
done

end

end