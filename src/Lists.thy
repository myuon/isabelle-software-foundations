theory Lists
imports Main
begin

section {* Lists *}
subsection {* Pairs of Numbers *}

datatype natprod = pair nat nat

value "pair 3 5"
  (* \<Longrightarrow> "pair (Suc (Suc (Suc 0))) (Suc (Suc (Suc (Suc (Suc 0)))))" :: "natprod" *)

fun fst :: "natprod \<Rightarrow> nat" where
  "fst (pair x _) = x"
fun snd :: "natprod \<Rightarrow> nat" where
  "snd (pair _ y) = y"
fun swap_pair :: "natprod \<Rightarrow> natprod" where
  "swap_pair (pair x y) = pair y x"

value "fst (pair 3 5)"
  (* \<Longrightarrow> "Suc (Suc (Suc 0))" :: "nat" *)

(* value "fst (3,5)" *)
  (* \<Longrightarrow> "Suc (Suc (Suc 0))" :: "nat" *)

theorem surjective_pairing': "\<forall>n m :: nat. pair n m = pair (fst (pair n m)) (snd (pair n m))" by simp
theorem surjective_pairing_stuck: "\<forall>(p :: natprod). p = pair (fst p) (snd p)"
apply auto by (case_tac p, simp)

(* Exercise: 1 star (snd_fst_is_swap) *)

theorem snd_fst_is_swap: "\<forall>(p :: natprod). pair (snd p) (fst p) = swap_pair p"
apply auto by (case_tac p, simp)

(* Exercise: 1 star, optional (fst_swap_is_snd) *)

theorem fst_swap_is_snd: "\<forall>(p :: natprod). fst (swap_pair p) = snd p"
apply auto by (case_tac p, simp)

subsection {* Lists of Numbers *}

datatype natlist = nil | cons nat natlist

definition "mylist \<equiv> cons 1 (cons 2 (cons 3 nil))"

no_notation
  List.Nil ("[]")

notation
  nil ("[]") and
  cons (infixr ";" 60)

no_syntax
  "_list" :: "args \<Rightarrow> 'a list" ("[(_)]")

syntax
  "_natlist" :: "args \<Rightarrow> natlist" ("[(_)]")

translations
  "[x; xs]" == "x;[xs]"
  "[x]" == "x;[]"

definition "mylist1 \<equiv> 1 ; (2 ; (3 ; nil))"
definition "mylist2 \<equiv> 1 ; 2 ; 3 ; nil"
definition "mylist3 \<equiv> [1;2;3]"

subsubsection {* Repeat *}

fun repeat :: "nat \<Rightarrow> nat \<Rightarrow> natlist" where
  "repeat n 0 = []"
  | "repeat n (Suc count) = n ; (repeat n count)"

subsubsection {* Length *}

fun length :: "natlist \<Rightarrow> nat" where
  "length nil = 0"
  | "length (h ; t) = Suc (length t)"

subsubsection {* Append *}

no_notation
  Map.map_add (infixl "++" 100)

fun app :: "natlist \<Rightarrow> natlist \<Rightarrow> natlist" (infixr "++" 80) where
  "app nil l2 = l2"
  | "app (h ; t) l2 = h ; (app t l2)"

lemma test_app1: "[1;2;3] ++ [4;5] = [1;2;3;4;5]" by simp
lemma test_app2: "nil ++ [4;5] = [4;5]" by simp
lemma test_app3: "[1;2;3] ++ nil = [1;2;3]" by simp

subsubsection {* Head (with default) and Tail *}

fun hd :: "nat \<Rightarrow> natlist \<Rightarrow> nat" where
  "hd d nil = d"
  | "hd _ (h ; t) = h"

fun tl :: "natlist \<Rightarrow> natlist" where
  "tl nil = nil"
  | "tl (h ; t) = t"

lemma test_hd1: "hd 0 [1;2;3] = 1" by simp
lemma test_hd2: "hd 0 [] = 0" by simp
lemma test_tl: "tl [1;2;3] = [2;3]" by simp

(* Exercise: 2 stars (list_funs) *)

fun nonzeros :: "natlist \<Rightarrow> natlist" where
  "nonzeros nil = nil"
  | "nonzeros (h ; t) = (if h = 0 then nonzeros t else h ; nonzeros t)"

lemma test_nonzeros: "nonzeros [0;1;0;2;3;0;0] = [1;2;3]" by simp

fun oddmembers :: "natlist \<Rightarrow> natlist" where
  "oddmembers nil = nil"
  | "oddmembers (h ; t) = (if h mod 2 = 0 then oddmembers t else h ; oddmembers t)"

lemma test_oddmembers: "oddmembers [0;1;0;2;3;0;0] = [1;3]" by simp

fun countoddmembers :: "natlist \<Rightarrow> nat" where
  "countoddmembers l = length (oddmembers l)"

lemma test_countoddmembers1: "countoddmembers [1;0;3;1;4;5] = 4" by simp
lemma test_countoddmembers2: "countoddmembers [0;2;4] = 0" by simp
lemma test_countoddmembers3: "countoddmembers nil = 0" by simp

(* Exercise: 3 stars, advanced (alternate) *)

fun alternate :: "natlist \<Rightarrow> natlist \<Rightarrow> natlist" where
  "alternate nil l2 = l2"
  | "alternate l1 nil = l1"
  | "alternate (h1;t1) (h2;t2) = h1 ; h2 ; alternate t1 t2"

lemma test_alternate1: "alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6]" by simp
lemma test_alternate2: "alternate [1] [4;5;6] = [1;4;5;6]" by simp
lemma test_alternate3: "alternate [1;2;3] [4] = [1;4;2;3]" by simp
lemma test_alternate4: "alternate [] [20;30] = [20;30]" by simp

subsubsection {* Bags via Lists *}

type_synonym bag = natlist

(* Exercise: 3 stars (bag_functions) *)

fun count :: "nat \<Rightarrow> bag \<Rightarrow> nat" where
  "count _ nil = 0"
  | "count a (h ; t) = (if a = h then 1 + count a t else count a t)"

lemma test_count1: "count 1 [1;2;3;1;4;1] = 3" by simp
lemma test_count2: "count 6 [1;2;3;1;4;1] = 0" by simp

fun sum :: "bag \<Rightarrow> bag \<Rightarrow> bag" where
  "sum l1 l2 = l1 ++ l2"

lemma test_sum1: "count 1 (sum [1;2;3] [1;4;1]) = 3" by simp

fun add :: "nat \<Rightarrow> bag \<Rightarrow> bag" where
  "add x xs = x ; xs"

lemma test_add1: "count 1 (add 1 [1;4;1]) = 3" by simp
lemma test_add2: "count 5 (add 1 [1;4;1]) = 0" by simp

fun member :: "nat \<Rightarrow> bag \<Rightarrow> bool" where
  "member x nil = False"
  | "member x (h; t) = (if x = h then True else member x t)"

lemma test_member1: "member 1 [1;4;1] = True" by simp
lemma test_member2: "member 2 [1;4;1] = False" by simp

(* Exercise: 3 stars, optional (bag_more_functions) *)

fun remove_one :: "nat \<Rightarrow> bag \<Rightarrow> bag" where
  "remove_one _ nil = nil"
  | "remove_one x (h;t) = (if x = h then t else h ; remove_one x t)"

lemma test_remove_one1: "count 5 (remove_one 5 [2;1;5;4;1]) = 0" by simp
lemma test_remove_one2: "count 5 (remove_one 5 [2;1;4;1]) = 0" by simp
lemma test_remove_one3: "count 4 (remove_one 5 [2;1;4;5;1;4]) = 2" by simp
lemma test_remove_one4: "count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1" by simp

fun remove_all :: "nat \<Rightarrow> bag \<Rightarrow> bag" where
  "remove_all _ nil = nil"
  | "remove_all x (h;t) = (if x = h then remove_all x t else h ; remove_all x t)"

lemma test_remove_all1: "count 5 (remove_all 5 [2;1;5;4;1]) = 0" by simp
lemma test_remove_all2: "count 5 (remove_all 5 [2;1;4;1]) = 0" by simp
lemma test_remove_all3: "count 4 (remove_all 5 [2;1;4;5;1;4]) = 2" by simp
lemma test_remove_all4: "count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0" by simp

fun subset :: "bag \<Rightarrow> bag \<Rightarrow> bool" where
  "subset nil _ = True"
  | "subset (x ; xs) ys = (if count x ys = 0 then False else subset xs (remove_one x ys))"

lemma test_subset1: "subset [1;2] [2;1;4;1] = True" by simp
lemma test_subset2: "subset [1;2;2] [2;1;4;1] = False" by simp

(* Exercise: 3 stars (bag_theorem) *)

subsection {* Reasoning About Lists *}

theorem nil_app: "\<forall>l::natlist. [] ++ l = l" by simp

fun pred :: "nat \<Rightarrow> nat" where
  "pred 0 = 0"
  | "pred (Suc n) = n"

theorem tl_length_pred: "\<forall>l::natlist. pred (length l) = length (tl l)"
apply auto by (case_tac l, auto)

subsubsection {* Micro-Sermon *}
subsubsection {* Induction on Lists *}

theorem app_assoc: "\<forall>l1 l2 l3 :: natlist. (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)"
apply auto by (induct_tac l1, auto)

subsubsection {* Informal version *}

(* Informal version of the proof *)
theorem app_assoc_Isar: "\<forall>l1 l2 l3 :: natlist. (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)"
proof (auto, induct_tac l1)
  (* case l1 = [] *)
  show "\<And>l1 l2 l3. ([] ++ l2) ++ l3 = [] ++ l2 ++ l3" by simp
next
  (* case l1 = nat ; natlist *)
  fix l1 l2 l3 nat natlist
  assume hyp: "(natlist ++ l2) ++ l3 = natlist ++ l2 ++ l3"
  show "((nat ; natlist) ++ l2) ++ l3 = (nat ; natlist) ++ l2 ++ l3"
    using hyp by simp
qed

subsubsection {* Another example *}

theorem app_length: "\<forall>l1 l2 :: natlist. length (l1 ++ l2) = (length l1) + (length l2)"
apply auto by (induct_tac l1, auto)

subsubsection {* Reversing a list *}

fun snoc :: "natlist \<Rightarrow> nat \<Rightarrow> natlist" where
  "snoc nil v = [v]"
  | "snoc (h;t) v = h ; (snoc t v)"

fun rev :: "natlist \<Rightarrow> natlist" where
  "rev nil = nil"
  | "rev (h ; t) = snoc (rev t) h"

lemma test_rev1: "rev [1;2;3] = [3;2;1]" by simp
lemma test_rev2: "rev nil = nil" by simp

subsubsection {* Proofs about reverse *}

theorem length_snoc: "\<forall>n :: nat. \<forall>l :: natlist. length (snoc l n) = Suc (length l)"
apply auto by (induct_tac l, auto)

theorem rev_length: "\<forall>l :: natlist. length (rev l) = length l"
apply auto by (induct_tac l, auto simp add: length_snoc)

theorem length_snoc_Isar: "\<forall>n :: nat. \<forall>l :: natlist. length (snoc l n) = Suc (length l)"
proof (auto, induct_tac l)
  (* case l = [] *)
  fix n l
  show "Lists.length (snoc [] n) = Suc (Lists.length [])" by simp
next
  (* case l = nat ; natlist *)
  fix n l nat natlist
  assume hyp: "Lists.length (snoc natlist n) = Suc (Lists.length natlist)"
  show "Lists.length (snoc (nat ; natlist) n) = Suc (Lists.length (nat ; natlist))"
    using hyp by simp
qed

(* theorem rev_length_Isar: "\<forall>l :: natlist. length (rev l) = length l" *)

subsubsection {* SearchAbout *}
subsubsection {* List Exercises, Part 1 *}

(* Exercise: 3 stars (list_exercises) *)

theorem app_nil_end: "\<forall>l :: natlist. l ++ [] = l"
apply auto by (induct_tac l, auto)

lemma rev_involutive_lem: "\<And>x :: nat. \<And>l :: natlist. rev (snoc l x) = x ; rev l"
by (induct_tac l, auto)

theorem rev_involutive: "\<forall>l :: natlist. rev (rev l) = l"
apply auto by (induct_tac l, auto simp add: rev_involutive_lem)

theorem app_assoc4: "\<forall>l1 l2 l3 l4 :: natlist. l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4"
apply auto by (induct_tac l1, auto simp add: app_assoc)

theorem snoc_append: "\<forall>(l::natlist) (n::nat). snoc l n = l ++ [n]"
apply auto by (induct_tac l, auto)

theorem distr_rev: "\<forall>l1 l2 :: natlist. rev (l1 ++ l2) = (rev l2) ++ (rev l1)"
apply auto by (induct_tac l1, auto simp add: app_nil_end snoc_append app_assoc)

lemma nonzeros_app: "\<forall>l1 l2 :: natlist. nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)"
apply auto by (induct_tac l1, auto)

(* Exercise: 2 stars (beq_natlist) *)

fun beq_natlist :: "natlist \<Rightarrow> natlist \<Rightarrow> bool" where
  "beq_natlist nil nil = True"
  | "beq_natlist nil _ = False"
  | "beq_natlist _ nil = False"
  | "beq_natlist (h1;t1) (h2;t2) = (if h1 = h2 then beq_natlist t1 t2 else False)"

lemma test_beq_natlist1: "beq_natlist nil nil = True" by simp
lemma test_beq_natlist2: "beq_natlist [1;2;3] [1;2;3] = True" by simp
lemma test_beq_natlist3: "beq_natlist [1;2;3] [1;2;4] = False" by simp

theorem beq_natlist_refl: "\<forall>l::natlist. True = beq_natlist l l"
apply auto by (induct_tac l, auto)

subsubsection {* List Exercises, Part 2 *}

(* Exercise: 2 stars (list_design) *)
(* Exercise: 3 stars, advanced (bag_proofs) *)

(* ble_nat = \<le> *)
theorem count_member_nonzero: "\<forall>(s :: bag). 1 \<le> (count 1 (1 ; s)) = True" by simp

theorem ble_n_Sn : "\<forall>n. n \<le> (Suc n) = True" by simp

theorem remove_decreases_count: "\<forall>(s :: bag). count 0 (remove_one 0 s) \<le> count 0 s = True"
apply auto by (induct_tac s, auto)

(* Exercise: 3 stars, optional (bag_count_sum) *)
(* Exercise: 4 stars, advanced (rev_injective) *)

lemma rev_injective_lem: "\<And>l1 l2. rev (rev l1) = rev (rev l2) \<Longrightarrow> l1 = l2"
by (auto simp add: rev_involutive)

theorem rev_injective: "\<forall>l1 l2 :: natlist. rev l1 = rev l2 \<longrightarrow> l1 = l2"
apply auto by (auto simp add: rev_injective_lem)

(* a hard way? *)

subsection {* Options *}

datatype natoption = Some nat | None

fun index :: "nat \<Rightarrow> natlist \<Rightarrow> natoption" where
  "index n nil = None"
  | "index n (a ; l) = (if n = 0 then Some a else index (pred n) l)"

lemma test_index1: "index 0 [4;5;6;7] = Some 4" by simp
lemma test_index2: "index 3 [4;5;6;7] = Some 7"
proof -
  have 3: "3 = Suc (Suc 1)" by simp
  show ?thesis by (simp add: 3)
qed
lemma test_index3: "index 10 [4;5;6;7] = None"
proof -
  have 10: "10 = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 1))))))))" by simp
  show ?thesis by (simp add: 10)
qed

fun option_elim :: "nat \<Rightarrow> natoption \<Rightarrow> nat" where
  "option_elim d (Some n) = n"
  | "option_elim d None = d"

(* Exercise: 2 stars (hd_opt) *)

fun hd_opt :: "natlist \<Rightarrow> natoption" where
  "hd_opt nil = None"
  | "hd_opt l = Some (hd 0 l)"

lemma test_hd_opt1: "hd_opt [] = None" by simp
lemma test_hd_opt2: "hd_opt [1] = Some 1" by simp
lemma test_hd_opt3: "hd_opt [5;6] = Some 5" by simp

(* Exercise: 1 star, optional (option_elim_hd) *)

theorem option_elim_hd: "\<forall>(l::natlist) (default::nat). hd default l = option_elim default (hd_opt l)"
apply auto by (induct_tac l, auto)

subsection {* Dictionaries *}

datatype dictionary = empty | record' nat nat dictionary

fun insert :: "nat \<Rightarrow> nat \<Rightarrow> dictionary \<Rightarrow> dictionary" where
  "insert key value d = record' key value d"

fun find :: "nat \<Rightarrow> dictionary \<Rightarrow> natoption" where
  "find key empty = None"
  | "find key (record' k v d) = (if key = k then Some v else find key d)"

(* Exercise: 1 star (dictionary_invariant1) *)

theorem dictionary_invariant1': "\<forall>(d :: dictionary) k (v :: nat). (find k (insert k v d)) = Some v"
by simp

(* Exercise: 1 star (dictionary_invariant2) *)

theorem dictionary_invariant2': "\<forall>(d :: dictionary) (m :: nat) n o'. m = n = False \<longrightarrow> find m d = find m (insert n o' d)"
by simp

end
