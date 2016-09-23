theory Linked_queue
imports "../l4v/tools/autocorres/AutoCorres"
        "../l4v/tools/autocorres/DataStructures"
begin

install_C_file linked_queue.c
autocorres[ts_rules = nondet, heap_abs_syntax] linked_queue.c

context linked_queue begin

sublocale linked_list next_C NULL
done

definition
  lkup :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C option"
where
  "lkup s p = (if is_valid_node_C s p then Some s[p] else None)"

(* Lifted version of DataStructures.linked_list.list_non_NULL *)
lemma list_lkup_non_NULL:
  "p \<noteq> NULL \<Longrightarrow>
    list (lkup s) xs p = (\<exists>ys. xs = p#ys \<and> is_valid_node_C s p \<and> list (lkup s) ys s[p]\<rightarrow>next)"
by (simp add: lkup_def list_non_NULL linked_queue.get_node_next_def)

definition
  queue :: "lifted_globals \<Rightarrow> node_C ptr list \<Rightarrow> bool"
where
  "queue s xs \<equiv> (front_'' s = NULL \<and> back_'' s = NULL \<and> xs = []) \<or>
                 (list (lkup s) xs (front_'' s) \<and> back_'' s = last xs \<and> xs \<noteq> [])"

lemma front_ign_w8[simp]:
  "front_'' s[x := (v::8 word)] = front_'' s"
by (simp add: linked_queue.update_w8_def)

lemma back_ign_w8[simp]:
  "back_'' s[x := (v::8 word)] = back_'' s"
by (simp add: linked_queue.update_w8_def)

lemma front_ign_next[simp]:
  "front_'' s[x\<rightarrow>next := v] = front_'' s"
by (simp add: linked_queue.update_node_next_def)

lemma element_ign_front[simp]:
  "(s\<lparr>front_'' := f\<rparr>)[p]\<rightarrow>element = s[p]\<rightarrow>element"
by (simp add: linked_queue.get_node_element_def)

lemma element_ign_back[simp]:
  "(s\<lparr>back_'' := b\<rparr>)[p]\<rightarrow>element = s[p]\<rightarrow>element"
by (simp add: linked_queue.get_node_element_def)

lemma lkup_ign_front[simp]:
  "lkup (s\<lparr>front_'' := f\<rparr>) = lkup s"
by (auto simp: lkup_def)

lemma lkup_ign_back[simp]:
  "lkup (s\<lparr>back_'' := b\<rparr>) = lkup s"
by (auto simp: lkup_def)

lemma lkup_ignore_w8[simp]:
  "lkup s[x := (v::8 word)] = lkup s"
by (auto simp: lkup_def)

lemma dequeue_correct:
  "(\<And>s f. P (s\<lparr>front_'' := f\<rparr>) = P s) \<Longrightarrow>
   (\<And>s b. P (s\<lparr>back_'' := b\<rparr>) = P s) \<Longrightarrow>
   (\<And>s v. P (s[x := v]) = P s) \<Longrightarrow>
   \<lbrace> \<lambda>s. queue s xs \<and> xs \<noteq> [] \<and> is_valid_w8 s x \<and> P s \<rbrace>
   dequeue' x
   \<lbrace> \<lambda>r s. r > 0 \<and> queue s (tl xs) \<and> s[x] = s[hd xs]\<rightarrow>element \<and> P s \<rbrace>!"
apply (unfold dequeue'_def)
apply wp
apply (fastforce simp: queue_def list_lkup_non_NULL)
done

lemma dequeue_correct':
  "\<lbrace> \<lambda>s. queue s [] \<and> P s \<rbrace>
   dequeue' x
   \<lbrace> \<lambda>r s. r = 0 \<and> P s \<rbrace>!"
apply (unfold dequeue'_def)
apply wp
apply (simp add: queue_def)
done

lemma list_no_null[simp]:
  "\<lbrakk> list s xs p \<rbrakk> \<Longrightarrow> NULL \<notin> set xs"
by (induct xs arbitrary: p, auto)

lemma list_lkup_in_valid:
  "\<lbrakk> list (lkup s) xs p; x \<in> set xs \<rbrakk> \<Longrightarrow> is_valid_node_C s x"
by (auto simp: lkup_def split: if_splits dest!: list_in_Some)

lemma path_lkup_ign_next[simp]:
  "x \<notin> set xs \<Longrightarrow> path (lkup s[x\<rightarrow>next := v]) p xs q = path (lkup s) p xs q"
by (induct xs arbitrary: p, auto simp: lkup_def linked_queue.update_node_next_def)

lemma path_lkup_update_last:
  "\<lbrakk> path (lkup s) p xs q; xs \<noteq> []; distinct xs \<rbrakk> \<Longrightarrow>
      path (lkup s[last xs\<rightarrow>next := q']) p xs q'"
apply (induct xs arbitrary: p)
apply (auto simp: lkup_def linked_queue.update_node_next_def split: if_splits)
done

lemma list_lkup_extend:
  "\<lbrakk> is_valid_node_C s x; x \<noteq> NULL; x \<notin> set xs; list (lkup s) xs p; xs \<noteq> [] \<rbrakk> \<Longrightarrow>
     list (lkup s[last xs\<rightarrow>next := x][x\<rightarrow>next := NULL]) (xs @ [x]) p"
apply (frule list_distinct)
apply (simp add: path_null_list[symmetric] path_lkup_update_last)
apply (simp add: lkup_def linked_queue.update_node_next_def)
done

declare list_split[simp del]

lemma enqueue_correct:
  "(\<And>s f. P (s\<lparr>front_'' := f\<rparr>) = P s) \<Longrightarrow>
   (\<And>s b. P (s\<lparr>back_'' := b\<rparr>) = P s) \<Longrightarrow>
   (\<And>s n. P (s[back_'' s\<rightarrow>next := n]) = P s) \<Longrightarrow>
   (\<And>s v. P (s[x\<rightarrow>next := v]) = P s) \<Longrightarrow>
   \<lbrace> \<lambda>s. queue s xs \<and> is_valid_node_C s x \<and> x \<noteq> NULL \<and> x \<notin> set xs \<and> P s \<rbrace>
   enqueue' x
   \<lbrace> \<lambda>r s. queue s (xs @ [x]) \<and> P s \<rbrace>!"
apply (unfold enqueue'_def)
apply wp
apply (clarsimp simp: queue_def)
apply safe
   apply (fastforce simp: lkup_def linked_queue.update_node_next_def)
  apply (drule list_no_null, simp)
 apply (simp add: list_lkup_extend)
apply (simp add: list_lkup_in_valid)
done

end
end