theory ArrSum
imports "../l4v/tools/autocorres/AutoCorres"
begin
text{* 

Author: Dan DaCosta
Description: A proof of the correctness, with respect to a function specification, of a C function 
that sums all unsigned integers in an array. In other words, it is shown that a C function and 
Isabelle function, when applied to the same input modulo a mapping function, return the same value. 
Note that correctness in sense permits integer overflow.

*}
install_C_file arrsum.c
autocorres[ts_rules = nondet, heap_abs_syntax ] arrsum.c
text{*

We could use the "unsigned_word_abs" conversion on this function. When done, a proof obligation
that the while loop body statement associated with aggregating the sum never overflows must be 
discharged. Instead we have opted to prove correctness via equivalence with a functional 
specification that also permits overflow making the utility of such a conversion low.

*}

context arrsum begin

lemma ptr_add_assoc [simp]: "p +\<^sub>p (i + j) = p +\<^sub>p i +\<^sub>p j" 
 by (simp add: CTypesDefs.ptr_add_def distrib_right)

fun the_array :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> 32 word list \<Rightarrow> bool" where
"the_array s a [] = True"
|"the_array s a (w # ws) = (w = s[a] \<and> is_valid_w32 s a \<and> the_array s (a +\<^sub>p 1) ws)" 

lemma drop_extend_eq:"0 < n \<Longrightarrow> drop (n-1) xs = drop n (x # xs)"
 apply (induction n) by auto

lemma drop_unat_extend_eq:"0 < (n::32 word) \<Longrightarrow> drop (unat (n-1)) xs = drop (unat n) (x # xs)"
by (metis arrsum.drop_extend_eq unat_0 unat_minus_one unat_mono word_gt_0)

lemma the_array_offsets:
 "\<lbrakk>the_array s a ws; (i::32 word) < of_nat (length ws)\<rbrakk> \<Longrightarrow> the_array s (a +\<^sub>p uint i) (drop (unat i) ws)"
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
      by (metis (no_types) Cons.prems(2) add.commute gt0_iff_gem1 le_less_trans length_Cons 
          not_less plus_one_helper semiring_1_class.of_nat_simps(2))
    then have "the_array s (a +\<^sub>p 1 +\<^sub>p uint (i - 1)) (drop (unat (i - 1)) ws)" using Cons by auto
    then have "the_array s (a +\<^sub>p uint i) (drop (unat (i - 1)) ws)" 
    by (metis (no_types, hide_lams) Suc_unat_minus_one a arrsum.ptr_add_assoc of_nat_Suc uint_nat word_not_simps(1))
    thus ?case using drop_unat_extend_eq[OF a,of ws w] by auto
  qed
qed

lemma drop_not_empty:"i < length xs \<Longrightarrow> drop i xs \<noteq> []"
by auto

lemma the_array_all_valid:
 "\<lbrakk>the_array s a ws; (i::32 word) < of_nat (length ws)\<rbrakk> \<Longrightarrow> is_valid_w32 s (a +\<^sub>p uint i)"
using the_array_offsets drop_not_empty by (metis arrsum.the_array.elims(2) unat_less_helper)

lemma the_array_list_corres:
"\<lbrakk>the_array s a ws; (i::32 word) < of_nat (length ws)\<rbrakk> \<Longrightarrow> s[a +\<^sub>p uint i] = ws ! (unat i)"
using the_array_offsets drop_not_empty
  by (metis (no_types, hide_lams) arrsum.the_array.simps(2) drop_0 hd_drop_conv_nth
      length_greater_0_conv list.exhaust nth_Cons_0 unat_less_helper)

lemma word_ge_zero[simp]:"(x::32 word) = 0 \<or> 0 < x"
using word_neq_0_conv by blast

lemma growing_listsum:"\<lbrakk>length ws \<le> UINT_MAX; (iw::32 word) < of_nat (length ws)\<rbrakk>
          \<Longrightarrow> listsum (take (unat iw) ws) + (ws ! unat iw) = listsum (take (unat (iw + 1)) ws)"
proof -
  assume a1:"length ws \<le> UINT_MAX" and a2:"(iw::32 word) < of_nat (length ws)"
  then have h1:"unat iw < length ws" by (simp add: unat_less_helper)
  have "take (unat (iw + 1)) ws = take (unat (iw + 1)) ws" by auto
  then have "take (unat iw) ws @ [ws ! unat iw] = take (unat (iw + 1)) ws" 
    by (metis less_irrefl word_1_0  word_zero_le sym[OF take_Suc_conv_app_nth[OF h1]] a2 unatSuc2)
  then have "listsum (take (unat iw) ws @ [ws ! unat iw]) = listsum (take (unat (iw + 1)) ws)" 
    by auto
  thus ?thesis by auto
qed

(* I cannot seem to simplify this proof anything further ... very strange. *)
lemma unat_of_nat32_alt:"x \<le> UINT_MAX \<Longrightarrow> unat ((of_nat x)::32 word) = x"
proof -
  assume "x \<le> UINT_MAX"
  then have "x \<le> 2 ^ 32 - 1" using UINT_MAX_def by auto
  then have "x < 2 ^ 32" by auto
  thus ?thesis using unat_of_nat32 word_bits_conv by auto
qed

lemma arrsum_correct:
  "\<lbrace> \<lambda>s. the_array s a ws \<and> length ws \<le> UINT_MAX \<and> s = s'\<rbrace>
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
   (* Obligation from loop axiom plus obligation for measure decrease. *)
   apply (auto simp add: inc_le diff_less_mono2 unat_less_helper word_1_0 the_array_all_valid
          the_array_list_corres intro: growing_listsum)[1]
   (* Invariant implies postcondition. *)
  using unat_of_nat32_alt apply auto[1]
  (* Precondition implies invariant. *)
 apply auto
done
  
end

end