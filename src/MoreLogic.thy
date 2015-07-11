theory MoreLogic
imports Main Prop
begin

section {* MoreLogic *}
subsection {* Existential Quantification *}

inductive ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool" for P :: "'a \<Rightarrow> bool" where
  ex_intro: "P witness \<Longrightarrow> ex P"

(*
Notation "'exists' x , p" := (ex (fun x \<Rightarrow> p))
  (at level 200, x ident, right associativity) : type_scope.
*)

lemma exists_example_1: "ex (\<lambda>n :: nat. n + (n * n) = 6)"
apply (rule ex_intro [of _ 2]) by simp

theorem exists_example_2: "ex (\<lambda>m. n = 4 + m) \<Longrightarrow> ex (\<lambda>l. n = 2 + l)"
proof (erule ex.inducts)
  fix witness assume "n = 4 + witness"
  thus "ex (\<lambda>l. n = 2 + l)"
    apply (rule_tac ex_intro [of _ "2 + witness"]) by simp
qed

lemma exists_example_3: "ex (\<lambda>n :: nat. even n & beautiful n)"
apply (rule ex_intro [of _ 8]) by (simp add: eight_is_beautiful)

(* Exercise: 1 star, optional (english_exists) *)
(* Exercise: 1 star (dist_not_exists) *)
theorem dist_not_exists: "(\<forall>x. P x) \<Longrightarrow> \<not> (ex (\<lambda>x. \<not> P x))"
by (auto, simp add: ex.simps)

(* Exercise: 3 stars, optional (not_exists_dist) *)
abbreviation "excluded_middle P \<equiv> \<forall>x. P x \<or> \<not> P x"

theorem not_exists_dist: "excluded_middle P \<Longrightarrow> \<not> (ex (\<lambda>x. \<not> P x)) \<longrightarrow> (\<forall>x. P x)"
by (auto, simp add: ex.simps)

(* Exercise: 2 stars (dist_exists_or) *)
theorem dist_exists_or: "ex (\<lambda>x. P x \<or> Q x) \<longleftrightarrow> ex (\<lambda>x. P x) \<or> ex (\<lambda>x. Q x)"
by (auto simp add: ex.simps)

subsection {* Evidence-carrying booleans. *}

inductive sumbool where
  left: "A \<Longrightarrow> sumbool A _"
  | right: "B \<Longrightarrow> sumbool _ B"

notation
  sumbool ("{_} \<bar> {_}")

theorem eq_nat_dec: "\<And>n :: nat. {n = m} \<bar> {n \<noteq> m}"
apply (induct m)
  apply (case_tac n)
    apply (rule left, simp)
    apply (rule right, simp)
  apply (case_tac n)
    apply (rule right, simp)
    apply (simp)
done

(* In Isabelle, we only use the boolean type to decide whether a prop is true or not *)
fun eq_nat_dec where
  "eq_nat_dec n m = (n = m)"

fun override' where
  "override' f k x = (\<lambda>(k' :: nat). if eq_nat_dec k k' then x else f k')"

theorem override_same': "f k1 = x1 \<Longrightarrow> (override' f k1 x1) k2 = f k2"
by auto

(* Exercise: 1 star (override_shadow') *)
theorem override_shadow': "override' (override' f k1 x2) k1 x1 k2 = (override' f k1 x1 k2)"
by simp

subsection {* Additional Exercises *}

(* Exercise: 3 stars (all_forallb) *)
inductive all for P where
  all_nil: "all P []"
  | all_cons: "\<lbrakk> all P xs; P x \<rbrakk> \<Longrightarrow> all P (x # xs)"

fun forallb :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "forallb test [] = True"
  | "forallb test (x # xs) = (test x \<and> forallb test xs)"

theorem forallb_all: "forallb test xs \<longleftrightarrow> all test xs"
apply (auto)
  apply (induct xs, rule, simp, rule all_cons, simp, simp)
  apply (erule all.inducts, simp, simp)
done

(* Exercise: 4 stars, advanced (filter_challenge) *)
inductive in_order_merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  in_order_xs_nil: "in_order_merge [] [] []"
  | in_order_cons_r: "in_order_merge xs ys zs \<Longrightarrow> in_order_merge xs (x # ys) (x # zs)"
  | in_order_cons_l: "in_order_merge xs ys zs \<Longrightarrow> in_order_merge (x # xs) ys (x # zs)"

lemma in_order_merge_ex1: "in_order_merge [1,6,2] [4,3] [1,4,6,2,3]"
by (rule+)

theorem filter_challenge:
  "\<And>l1 l2. \<lbrakk> in_order_merge l1 l2 l; forallb test l1; forallb (\<lambda>x. \<not> test x) l2 \<rbrakk> \<Longrightarrow> filter test l = l1"
apply (induct l, simp)
  apply (erule in_order_merge.cases, simp, simp, simp)
  apply (erule in_order_merge.cases, simp, simp, simp)
done

(* Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
lemma forallt_filter: "forallb test m \<Longrightarrow> filter test m = m"
by (induct m, auto)

lemma subseq_length: "m {subseq of} l \<Longrightarrow> length m \<le> length l"
by (erule subseq.induct, simp, simp, simp)

lemma subseq_filter: "m {subseq of} l \<Longrightarrow> (filter test m) {subseq of} (filter test l)"
apply (erule subseq.induct, simp, rule subseq_nil)
apply (simp add: subseq_cons)
apply (simp add: subseq_cons_both)
done

theorem filter_challenge_2 : "m {subseq of} l \<Longrightarrow> forallb test m \<Longrightarrow> length m \<le> length (filter test l)"
proof -
  assume "m {subseq of} l" "forallb test m"
  have "(filter test m) {subseq of} (filter test l)" by (rule subseq_filter, simp add: `m {subseq of} l`)
  hence "m {subseq of} (filter test l)" by (simp add: `forallb test m` forallt_filter)
  thus "length m \<le> length (filter test l)" by (rule subseq_length)
qed

(* Exercise: 4 stars, advanced (no_repeats) *)
inductive appears_in where
  ai_here: "appears_in a (a # l)"
  | ai_later: "appears_in a l \<Longrightarrow> appears_in a (b # l)"

lemma appears_in_app: "\<And>ys. appears_in x (xs @ ys) \<Longrightarrow> appears_in x xs \<or> appears_in x ys"
apply (induct xs, simp, simp)
apply (erule appears_in.cases)
proof (simp add: ai_here, simp)
  fix a :: "'a" and xs :: "'a list" and ys aa l b
  assume hyp: "(\<And>ys. appears_in aa (xs @ ys) \<Longrightarrow> appears_in aa xs \<or> appears_in aa ys)"
  and assms: "a = b \<and> xs @ ys = l" "appears_in aa l"
  have "appears_in aa xs \<or> appears_in aa ys"
    by (rule hyp, simp add: assms)
  thus "appears_in aa (b # xs) \<or> appears_in aa ys"
    using ai_later [of aa xs b] by auto
qed

lemma ai_later_app: "appears_in x xs \<Longrightarrow> appears_in x (ys @ xs)"
by (induct ys, simp, simp, rule, simp)

lemma app_appears_in: "appears_in x xs \<or> appears_in x ys \<Longrightarrow> appears_in x (xs @ ys)"
apply auto
apply (erule appears_in.inducts, simp add: ai_here, simp add: ai_later)
apply (simp add: ai_later_app)
done

fun disjoint where
  "disjoint l1 l2 = (\<forall>x. appears_in x l1 \<longrightarrow> \<not> appears_in x l2)"

inductive no_repeat where
  no_repeat_nil: "no_repeat []"
  | no_repeat_cons: "\<lbrakk> no_repeat l; \<not> appears_in x l \<rbrakk> \<Longrightarrow> no_repeat (x # l)"

theorem no_repeat_disjoint_app: "\<lbrakk> no_repeat xs; no_repeat ys; disjoint xs ys \<rbrakk> \<Longrightarrow> no_repeat (xs @ ys)"
apply (induct xs, simp, simp)
by (metis ai_here ai_later appears_in_app list.distinct(1) list.sel(1) list.sel(3) no_repeat.simps)

(* Exercise: 3 stars (nostutter) *)
inductive nostutter where
  nostutter_nil: "nostutter []"
  | nostutter_singleton: "nostutter [x]"
  | nostutter_cons: "\<lbrakk> nostutter (x # xs); x \<noteq> y \<rbrakk> \<Longrightarrow> nostutter (y # x # xs)"

lemma test_nostutter_1: "nostutter [(3::nat),1,4,1,5,6]"
apply rule+ by auto

lemma test_nostutter_2: "nostutter []" by rule
lemma test_nostutter_3: "nostutter [5]" by rule

lemma test_nostutter_4: "\<not> (nostutter [3 :: nat,1,1,4])"
by (rule, erule nostutter.cases, auto, erule nostutter.cases, auto)

(* Exercise: 4 stars, advanced (pigeonhole principle) *)
lemma app_length: "length (l1 @ l2) = length l1 + length l2" by simp

lemma appears_in_app_split: "appears_in x l \<Longrightarrow> \<exists>l1. \<exists>l2. l = l1 @ (x # l2)"
apply (induct l)
  apply (erule appears_in.cases, simp, simp)
  apply (erule appears_in.cases, auto)
proof -
  fix b l1 l2
  show "\<exists>l1a l2a. b # l1 @ x # l2 = l1a @ x # l2a"
    using exI [of _ "b # l1"] exI [of _ l2] by simp
qed

inductive repeats where
  repeats_appear: "appears_in x xs \<Longrightarrow> repeats (x # xs)"
  | repeats_cons: "repeats xs \<Longrightarrow> repeats (x # xs)"

(*
theorem pigeonhole_principle: "\<And>l2. (\<And>x. appears_in x l1 \<Longrightarrow> appears_in x l2) \<Longrightarrow> length l2 < length l1 \<Longrightarrow> repeats l1"
sorry
*)

(*
using excluded_middle, induction by l1 ?
*)

end
