(* Author: Andrew Gacek [http://loonwerks.com/people/andrew-gacek.html] *)
theory Max_AJG
imports "../l4v/tools/autocorres/AutoCorres"
begin

(* Based on Quicksort.thy *)

install_C_file max_AJG.c
autocorres[ts_rules = nondet, unsigned_word_abs = max, heap_abs_syntax] max_AJG.c

context max_AJG begin

lemma ptr_add_assoc [simp]:
  "p +\<^sub>p (i + j) = p +\<^sub>p i +\<^sub>p j"
by (simp add: CTypesDefs.ptr_add_def distrib_right)

(*
 * Array validity definitions
 *)

definition array_loc_valid :: "32 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "array_loc_valid a n \<equiv> (unat (ptr_val a) + size_of TYPE(32 word) * n \<le> UINT_MAX)"

fun array_elems_valid :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "array_elems_valid s a 0 = True" |
  "array_elems_valid s a (Suc n) = (is_valid_w32 s a \<and> array_elems_valid s (a +\<^sub>p 1) n)"

definition is_array :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "is_array s a n \<equiv> (array_loc_valid a n \<and> array_elems_valid s a n)"

lemma array_elems_valid_Suc [simp]:
  "array_elems_valid s a (Suc n) = (array_elems_valid s a n \<and> is_valid_w32 s (a +\<^sub>p int n))"
by (induction n arbitrary: a, auto)

declare array_elems_valid.simps(2)[simp del]

lemma array_all_elems_valid [intro]:
  "\<lbrakk> array_elems_valid s a n; m < n \<rbrakk> \<Longrightarrow> is_valid_w32 s (a +\<^sub>p int m)"
by (induction n arbitrary: a, auto elim: less_SucE)

lemma array_all_loc_valid [intro]:
  "\<lbrakk> array_loc_valid p n; m < n \<rbrakk> \<Longrightarrow> Suc m \<le> UINT_MAX"
by (simp add: array_loc_valid_def)

(*
 * Array contents
 *)

fun the_array :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> nat list" where
  "the_array s a 0 = []" |
  "the_array s a (Suc n) = unat s[a] # the_array s (a +\<^sub>p 1) n"

lemma the_array_Suc[simp]:
  "the_array s a (Suc n) = the_array s a n @ [unat s[a +\<^sub>p int n]]"
by (induction n arbitrary: a, auto)

declare the_array.simps(2)[simp del]

fun maxL :: "nat list \<Rightarrow> nat" where
  "maxL [] = 0" |
  "maxL (x#xs) = max x (maxL xs)"

lemma maxL_append [simp]:
  "maxL (xs @ ys) = max (maxL xs) (maxL ys)"
by (induction xs, auto)

lemma "\<lbrace> \<lambda>s. is_array s a n \<and> P s \<rbrace>
       max' a n
       \<lbrace> \<lambda>r s. r = maxL (the_array s a n) \<and> P s \<rbrace>!"
apply (unfold max'_def)
apply (subst whileLoop_add_inv[where
       I = "\<lambda>(i, result) s. result = maxL (the_array s a i) \<and> 
                            i \<le> n \<and>
                            is_array s a n \<and>
                            P s" and
       M = "\<lambda>((i, result), s). n - i"])
apply wp
apply (auto simp add: is_array_def)
done

end
end