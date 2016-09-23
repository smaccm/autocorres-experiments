theory ArrSum
imports "../l4v/tools/autocorres/AutoCorres"
begin

install_C_file arrsum.c
autocorres[ts_rules = nondet, heap_abs_syntax ] arrsum.c
(* We could think to use the "unsigned_word_abs". This will do some conversion from words to 
  natural numbers provided certain proof obligations regarding overflow during operations can be 
  discharged. However, this is not all that useful here; we would have to somehow guarantee that 
  the statement accumulating the sum will never overflow. There seems to be no straightforward way 
  to do bake this into the precondition. Instead we will allow overflow and write a functional 
  specification where it is clear that the sum over 32 bit words is being calculated. *)

context arrsum begin

lemma ptr_add_assoc [simp]:
  "p +\<^sub>p (i + j) = p +\<^sub>p i +\<^sub>p j"
by (simp add: CTypesDefs.ptr_add_def distrib_right)

fun the_array :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> 32 word list \<Rightarrow> bool" where
"the_array s a [] = True"
|"the_array s a (w # ws) = (w = s[a] \<and> is_valid_w32 s a \<and> the_array s (a +\<^sub>p 1) ws)" 

lemma the_array_all_valid:" \<lbrakk>the_array s a ws; (i::32 word) < of_nat (length ws)\<rbrakk> \<Longrightarrow> is_valid_w32 s (a +\<^sub>p uint i)"
proof(induction ws arbitrary: a i)
  case Nil
  thus ?case by auto
next
  case (Cons w ws)
  then have "0 = i \<or> 0 < i" using word_neq_0_conv by blast 
  thus ?case
  proof
    assume "0 = i"
    thus ?case using Cons by auto
  next 
    assume a:"0 < i"
    then have "i - 1 < of_nat (length ws)" 
      by (metis (no_types) Cons.prems(2) add.commute gt0_iff_gem1 le_less_trans length_Cons not_less plus_one_helper semiring_1_class.of_nat_simps(2))
    then have "is_valid_w32 s (a +\<^sub>p 1 +\<^sub>p uint (i - 1))" using Cons by auto
    thus ?case using Cons 
    by (metis (no_types) a add.commute arrsum.ptr_add_assoc diff_add_cancel diff_zero uint_1 uint_eq_0 uint_sub_lem word_less_def zless_imp_add1_zle)
  qed
qed

lemma the_array_list_corres:"\<lbrakk>the_array s a ws; (i::32 word) < of_nat (length ws)\<rbrakk> \<Longrightarrow> s[a +\<^sub>p uint i] = ws ! (unat i)"
proof(induction ws arbitrary: a i)
  case Nil
  thus ?case by auto
next
  case (Cons w ws)
  then have "0 = i \<or> 0 < i" using word_neq_0_conv by blast 
  thus ?case
  proof
    assume "0 = i"
    thus ?case using Cons by auto
  next 
    assume a:"0 < i"
    then have "i - 1 < of_nat (length ws)" 
      by (metis (no_types) Cons.prems(2) add.commute gt0_iff_gem1 le_less_trans length_Cons not_less plus_one_helper semiring_1_class.of_nat_simps(2))
    then have "s[a +\<^sub>p 1 +\<^sub>p uint (i - 1)] = ws ! (unat (i - 1))" using Cons by auto
    thus ?case using Cons 
    by (metis (mono_tags) Suc_pred' a arrsum.ptr_add_assoc nat.simps(3) nth_Cons' of_nat_Suc uint_nat unat_0 unat_minus_one word_less_nat_alt)
  qed
qed

lemma take_break_out_last:"\<lbrakk>(n::32 word) < of_nat (length xs)\<rbrakk> \<Longrightarrow> take (unat (n+1)) xs = take (unat n) xs @ [xs ! unat n]"
sorry

lemma listsum_take_break_out_last:"listsum (take (unat ((n::32 word)+1)) xs) = listsum (take (unat n) xs @ [xs ! unat n])"
sorry

lemma unat_of_nat:"x \<le> UINT_MAX \<Longrightarrow> unat ((of_nat x)::32 word) = x"
sorry

lemma arrsum_correct:
  "\<lbrace> \<lambda>s. the_array s a ws \<and> s = s' \<and> length ws \<le> UINT_MAX\<rbrace>
   arrsum' a (of_nat (length ws))
   \<lbrace> \<lambda>r s. r = listsum ws \<and> s = s' \<rbrace>!"
apply (rule validNF_assume_pre)
apply (unfold arrsum'_def)
apply (subst whileLoop_add_inv 
  [where 
    I = "\<lambda> (j,sum) s. 
      s = s'
      \<and> j \<le> of_nat (length ws)
      \<and> sum = listsum (take (unat j) ws)"
    and M = "\<lambda>((j,_),_).  length ws - unat j"])
apply wp
   apply clarsimp
   apply (simp add: inc_le diff_less_mono2 unat_less_helper word_1_0 the_array_all_valid listsum_take_break_out_last the_array_list_corres)
  using unat_of_nat apply auto[1]
 apply auto
done
  

end

end