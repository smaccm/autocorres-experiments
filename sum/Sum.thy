theory Sum imports
  "../../tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin

text{*

The most difficult aspects of this proof was finding theorems applicable to
moving subtraction and addition in and out of the uint and word_of_int
functions. The uint function converts an unsigned word to an integer and the
word_of_int function converts an integer to a word. For example, it should be
clear that if "x <= x + y" then "uint x + y = uint x + uint y" where x and y are
32 bit words; from "x <= x + y" we know that adding "x" and "y" will not result
in overflow. In fact, these theorems were only uncovered after they were
essentially reconstructed in earlier revisions of this proof and this came after
some time was spent trying to isolate the areas of the proof that were
preventing better automated tactics (e.g., sledgehammer) from solving
obligations that seemed valid. 

There was also a point in the proof where completing the proof in "apply-style"
was elusive. The sticking point seemed to be the algebraic manipulation 
captured in the "invariant" theorem below. It would seem that the proof of this
theorem is overly detailed and, rather, should have relied on more sophisticated
tactics to combine multiple steps. However, certain steps seemed to result in
no intuitive way for the proof to go through and sledgehammer did not find any
solution.

*}

install_C_file "./sum.c"
autocorres [ ts_rules = nondet ] "./sum.c"
context sum begin

lemma invariant:"
\<lbrakk> 0 \<le> x
; 0 < (b::32 word)
; x < 2^32
; \<not> result_C a + b \<le> result_C a
; 2 * uint (result_C a) = x * (x + 1) - uint b * (uint b + 1)
; uint (word_of_int x) = x\<rbrakk>
 \<Longrightarrow> 2 * uint (result_C a + b) 
     = x * (x + 1) - uint (b - 1) * (uint (b - 1) + 1)"

proof -
  assume A:" 2 * uint (result_C a) = x * (x + 1) - uint b * (uint b + 1)"
  assume B:"\<not> result_C a + b \<le> result_C a"
  then have B:"result_C a + b > result_C a" by simp
  then have C:"b > 0" using word_neq_0_conv by fastforce
  then have 
    "2 * uint (result_C a + b) 
     = x * (x + 1) - uint b * (uint b + 1) + 2 * uint b" 
    using B by (simp add: A distrib_left less_imp_le one_add_one uint_plus_simple)
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
apply (unfold sum'_def)
apply clarsimp
apply (subst whileLoop_add_inv [where 
        I = " \<lambda> (r,i) a. x \<ge> 0 
                         \<and> 2^32 > x 
                         \<and> (((2 * uint (result_C r) 
                            = (x * (x + 1)) - (uint i * ((uint i) + 1)))) 
                            \<or> overflow_C r = 1)" 
        and M = "\<lambda>((_,i),a). unat i"])
apply wp 
apply clarsimp
apply (auto simp: measure_unat)
defer
using uint_eq_0 word_neq_0_conv apply blast
using word_of_int_inverse[of x "(word_of_int x)::32 word"] apply auto
using invariant apply auto
done

end

text{*

\section{Final Notes}

1) Attempt to minimize the need for natural number subtraction; it can
unnecessarily complicate reasoning. When not avoidable, additional properties
may have to be shown to handle cases where traditional integer subtraction is
truncated.

2) Code should explicitly check and handle possible occurrences of integer
overflow/underflow. There seems to be no simple way in AutoCorress to prove
properties under the assumption that the code does not exhibit such errors
without explicitly handling them within the code.

3) If a top-level proof requires algebraic manipulations involving conversion
between words and more primitive types (e.g., integers), identities may need to
be proved separately, in basic steps, using ISAR proofs.

The sum function defined in C is also less than satisfactory; it continues to
aggregate a value after overflow has been detected. A better implementation
might make use of the "break" statement. Dealing with break requires more
sophisticated use of the AutoCorress tool and will be explored in other
experiments.

*}
end