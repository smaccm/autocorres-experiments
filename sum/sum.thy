theory sum imports
  "../../tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin
text{*

\section{Summary}

What follows is an experiment in trying to prove the correctness of a c function
that calculates the sum of numbers from 0 to x in a naive fashion, i.e.,
iteratively. AutoCorress monadically encodes c programs with faithful hardware
representations of primitive types, e.g., words, bytes. Thus, when reasoning
over integers and their corresponding operations, overflow must be considered.

The first attempt to prove correctness over such a function failed. The function
did not explicitly handle occurrences of overflow resulting in certain proof
obligation that would have required tedious reasoning about 32 bit words.
Operating under the false assumption that there would be some way to weaken the
correctness property to sum evaluations where overflow did not occur, a focus
was made on trying to prove correctness on a conceptual implementation of this
naive sum directly in AutoCorress's monadic encoding of c where all 32 bit word
types were replaced with natural numbers.

That exercise along with quickstart document found in the AutoCorress repository
revealed, what may be, a high-level methodology for using AutoCorress that goes
as follows:

 1) specify the property to be proven

 2) apply the "clarsimp" tactic to simplify the property to be proved

 3) specify the loop invariant and inductive measure using the
 "whileLoop_add_inv"

 4) apply the weakest precondition tactic "wp"; this hopefully extracts proof
 obligations by percolating the loop invariant and inductive measure backwards
 through the loop under investigation

 5) prove the resulting proof obligations

Another outcome of this first attempt was a practical example of how reasoning
over natural numbers when subtraction is involved can be tedious. This exercise
is the content of the section titled "Correctness of Direct Monadic Sum Function".

After completing the exercise described above and looking through the seL4
code/proofs it seemed that weakening the correctness property to ignore overflow
occurrences was not the correct approach; throughout the seL4 code overflow is
explicitly handled. Therefore, I modified the naive sum c function to:

 1) return a structure with a field for the result and a field indicating
 whether an overflow occurred

 2) if the previous (the sum result from the last iteration) aggregate is
 greater than or equal to the current aggregate then set the overflow indicator
 field to one.

 3) the loop counts down from the desired x and terminates before 0 is reached;
 this ensures the overflow field will only be set when overflow actually
 occurs.

The c sum function modified to explictly handle overflow is proved in the
section titled "Correctness of C Sum Function."

\section{Correctness of Direct Monadic Sum Function}

As a way to get a handle on proof of the above program. I considered, what I 
thought would be, a simpler proof on a c-like program that operated on naturals 
numbers:

s = s'
i = i' // where i' <= x
while (x <= i) {
  s += s + i
  i += 1
}

Here we let s' and i' be arbitrary provided i' <= x. When s' and i' are zero, we have a 
naive sum implementation for the natural numbers. I would like to prove that for all s' and 
i', if i' <= x then after the loop completes s = s' + sum(0,x) - sum(0,i-1). The equation in the 
consequent can be simplified to 2*s = 2*s' + x*(x+1) - i*(i-1). In the process of reasoning about
this property it becomes necessary to do algebraic manipulation of natural number equations 
involving subtraction. This can be rather messy; algebraic manipulations valid under integers 
might no longer be valid under natural numbers. Overcoming this, involves showing that whenever the
expression "a - b" occurs that b < a or b = a. This is the strategy that is used in the following 
proof.

*}

lemma invariant1[simp]: "(i::nat) < a \<Longrightarrow> a + i * i < a * a \<or> a * a = a + i * i"
proof (induct a arbitrary: i)
  case 0
  thus ?case by auto
next
  case (Suc a)
  have "i = a \<or> i < a" using Suc by auto
  then show ?case
  proof
    assume "i = a"
    thus ?case by auto
  next  
    assume A:"i < a"
    hence B:"0 < a" by simp
    have "a + i * i < a * a \<or> a * a = a + i * i" using Suc(1)[OF A] by simp
    then show ?case 
    proof
      assume "a + i * i < a * a"
      hence "a + i * i + 1 \<le> a * a" by simp
      hence "Suc a + i * i \<le>  a * a" and "a * a < Suc a * Suc a" by simp+
      hence "Suc a + i * i < Suc a * Suc a" by simp
      thus ?case by simp
    next 
      assume C:"a * a = a + i * i"
      hence "a * a + 1 = Suc a + i * i" by simp
      have "a * a + 1 < Suc a * Suc a" using B by simp
      hence "Suc a * Suc a > Suc a + i * i" using C by simp
      hence "Suc a + i * i < Suc a * Suc a" by simp
      thus ?case by simp
    qed
  qed
qed

lemma invariant2[simp]: " (i::nat)<a \<Longrightarrow> a * 2 + (a * a - (a + i * i)) = a + a * a - i * i"
proof -
  assume "i < a"
  hence "a + i * i < a * a \<or> a * a = a + i * i" using invariant1 by simp
  then show ?thesis
  proof
    assume "a + i * i < a * a"
    thus ?thesis by simp
  next
    assume "a * a = a + i * i"
    thus ?thesis by simp
  qed
qed

lemma "\<lbrace> \<lambda> a. (i'::nat) \<le> x \<rbrace> 
   whileLoop (\<lambda>(i, _) a. i \<le> x)
     (\<lambda>(i, s). return (i + 1, s + i))
    (i', s')
 \<lbrace> \<lambda> (_,s) a.  s*2 = s'*2 + ((x*x - i'*i') + x + i') \<rbrace>!
"
apply (rule validNF_assume_pre)
apply clarsimp
apply (subst whileLoop_add_inv [where 
        I = " \<lambda> (i,s) a. (i' < i \<and> i \<le> x + 1 \<and> s*2 = s'*2 + (i*i - i - i'*i' + i')) 
            \<or> (i = i' \<and> s = s')" 
        and M = "\<lambda>((i',s'),a). (x + 1) - i'"])
apply wp
apply clarsimp
apply (auto simp: algebra_simps)
using less_Suc_eq_le mult_le_mono by fastforce

text{*

\section{Correctness of C Sum Function}

*}

install_C_file "./sum.c"
autocorres [ ts_rules = nondet ] "./sum.c"
context sum begin
thm sum'_def

(* uint_plus_simple, word_of_int_inverse*)
(* Talk about the difficulty in finding the lemma that should be used and the
   amount of time spent recreating the wheel in with respect to this lemma. *)


lemma foo:" \<lbrakk>0 \<le> x; 0 < (b::32 word); x < 4294967296; \<not> result_C a + b \<le> result_C a; overflow_C a \<noteq> 1; 2 * uint (result_C a) = x * (x + 1) - uint b * (uint b + 1);
            uint (word_of_int x) = x\<rbrakk>
           \<Longrightarrow> 2 * uint (result_C a + b) = x * (x + 1) - uint (b - 1) * (uint (b - 1) + 1)"
proof -
  assume A:" 2 * uint (result_C a) = x * (x + 1) - uint b * (uint b + 1)"
  assume "\<not> result_C a + b \<le> result_C a"
  then have B:"result_C a + b > result_C a" by simp
  then have C:"b > 0" using word_neq_0_conv by fastforce
  then have "2 * uint (result_C a) + 2 * uint b = x * (x + 1) - uint b * (uint b + 1) + 2 * uint b" using A by simp
  then have "2 * (uint (result_C a) + uint b) = x * (x + 1) - uint b * (uint b + 1) + 2 * uint b" by simp
  then have "2 * uint (result_C a + b) = x * (x + 1) - uint b * (uint b + 1) + 2 * uint b" using B by (simp add: uint_plus_simple)
  then have "2 * uint (result_C a + b) = x * (x + 1) - (uint b * uint b + uint b) + 2 * uint b" by (metis (no_types, hide_lams) diff_diff_eq2 diff_zero mult.right_neutral mult_eq_0_iff right_diff_distrib)
  then have "2 * uint (result_C a + b) = x * (x + 1) - uint b * uint b - uint b + 2 * uint b" by simp
  then have "2 * uint (result_C a + b) = x * (x + 1) - uint b * uint b + uint b" by simp
  then have "2 * uint (result_C a + b) = x * (x + 1) - (uint b * uint b - uint b)" by simp
  then have "2 * uint (result_C a + b) = x * (x + 1) - (uint b * (uint b - 1))" by (simp add: int_distrib(4))
  then have "2 * uint (result_C a + b) = x * (x + 1) - ((uint b - 1) * uint b)" by simp  
  then have "2 * uint (result_C a + b) = x * (x + 1) - (uint (b - 1) * uint b)" using C by (metis add.left_neutral linorder_not_less uint_1 uint_eq_0 uint_minus_simple_alt word_less_def zless_imp_add1_zle)
  then have "2 * uint (result_C a + b) = x * (x + 1) - (uint (b - 1) * (uint (b - 1 + 1)))" by simp
  then have "2 * uint (result_C a + b) = x * (x + 1) - uint (b - 1) * (uint (b - 1) + 1)" using C by (metis dual_order.strict_iff_order eq_diff_eq gt0_iff_gem1 uint_1 uint_plus_simple)
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
        I = " \<lambda> (r,i) a. x \<ge> 0 \<and> 2^32 > x \<and> (((2 * uint (result_C r) = (x * (x + 1)) - (uint i * ((uint i) + 1)))) \<or> overflow_C r = 1)" 
        and M = "\<lambda>((_,i),a). unat i"])
apply wp 
apply clarsimp
apply (auto simp: measure_unat)
defer
using uint_eq_0 word_neq_0_conv apply blast
using word_of_int_inverse[of x "(word_of_int x)::32 word"] apply auto
using foo apply auto
done

end
text{*
\section{Summary}

This exercise can be used to capture some guidelines when proving properties
about mathematical computations on integers:

1) Attempt to minimize the need for natural number subtraction; it can 
   unnecessarily complicate reason. When not done, additional properties may
   have to be shown to handle cases where traditional integer subtraction is 
   truncated.

2) Code should explicitly check and handle possible occurrences of integer
   overflow/underflow. There seems to be now way in autocorress to prove 
   properties under the assumption that the code does not exhibit such errors 
   without explicitly handling them within the code.


*}
end