theory sum imports
  "../../tools/autocorres/AutoCorres"
begin


text{*

Prove a property about a sum program manipulating natural numbers.

*}

lemma nat_algebra_1[simp]: "(i::nat) < a \<Longrightarrow> a + i * i < a * a \<or> a * a = a + i * i"
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

lemma nat_algebra_2[simp]: " (i::nat)<a \<Longrightarrow> a * 2 + (a * a - (a + i * i)) = a + a * a - i * i"  using nat_algebra_1
proof -
  assume "i < a"
  hence "a + i * i < a * a \<or> a * a = a + i * i" using nat_algebra_1 by simp
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

install_C_file "./sum.c"
autocorres [ ts_rules = nondet ] "./sum.c"
context sum begin
thm sum'_def

lemma "
  \<lbrace> \<lambda> a. True \<rbrace> 
 sum' f
  \<lbrace> \<lambda> s a.  2*s = x * (x + 1) \<rbrace>!
"
oops

end

end