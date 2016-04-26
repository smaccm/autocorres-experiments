theory sum imports
  "../../tools/autocorres/AutoCorres"
begin
text{*

I would like to prove the correctness of the following c function that calculates the result of 
summing integers from 0 to x. If an integer overflow occurs then as much is noted in the result
and the function immediately returns.

struct integer_result {
  unsigned char overflow;
  unsigned int result;
};

struct integer_result sum(const unsigned int x) {

  struct integer_result r;
  r.overflow = 0;
  r.result = 0;
  unsigned int i = 0;
  while (x >= i) {
    if( r.result+i < i || i+1 < i ) {
      r.overflow = 1;
      break;
    } 
    r.result += i;
    i += 1;
    
  }
  return r;
}

\section{The correctness of a naive sum program}

As a way to get a handle on proof of the above program. I considered, what I thought would be, a 
simpler proof on a c-like program that operated on naturals numbers:

s = s'
i = i' // where i' <= x
while (x <= i) {
  s += s + i
  i += 1
}

Here we let s' and i' be arbitrary provided i' <= x. When s' and i' are zero, we have a 
sum the naive sum implementation for the natural numbers. I would like to prove that for all s' and 
i', if i' <= x then after the loop completes s = s' + sum(0,x) - sum(0,i-1). The equation in the 
consequent can be simplified to 2*s = 2*s' + x*(x+1) - i*(i-1). In the process of reasoning about
this property it becomes necessary to do algebraic manipulation of natural number equations 
involving subtraction. This can be rather messy; algebraic manipulations valid under integers 
might longer be valid under natural numbers. Overcoming this, involves showing that whenever the
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

\section{Desired property}

*}

install_C_file "./sum.c"
autocorres [ ts_rules = nondet ] "./sum.c"
context sum begin
thm sum'_def

lemma "
  \<lbrace> \<lambda> a. x \<ge> 0 \<rbrace> 
 sum' (word_of_int x)
  \<lbrace> \<lambda> r a. 2*(result_C r) = (word_of_int x) * ((word_of_int x) + 1) \<or> overflow_C r = 1\<rbrace>!
"
apply (rule validNF_assume_pre)
apply (unfold sum'_def)
apply clarsimp
apply (subst whileLoop_add_inv [where 
        I = " \<lambda> (i,r) a. i \<le> (word_of_int x) + 1 \<and> (2*(result_C r) = i * (i - 1) \<or> overflow_C r = 1)" 
        and M = "\<lambda>((i,_),a). unat ((word_of_int x)+1-i)"])
apply wp
apply clarsimp
oops

end

end