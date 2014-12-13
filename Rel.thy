theory Rel
imports Main
begin

section {* Rel *}

type_synonym 'a relation = "'a \<Rightarrow> 'a \<Rightarrow> bool"
term "less_eq"
  (* "op \<le>" :: "'a \<Rightarrow> 'a \<Rightarrow> bool" *)

subsection {* Basic Properties of Relations *}

definition partial_function' :: "'a relation \<Rightarrow> bool" where
  "partial_function' R \<equiv> \<forall>x y1 y2. R x y1 \<longrightarrow> R x y2 \<longrightarrow> y1 = y2"

fun next_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "next_nat n m = (Suc n = m)"
term "next_nat :: nat relation"
  (* "next_nat" :: "nat \<Rightarrow> nat \<Rightarrow> bool" *)

theorem next_nat_partial_function: "partial_function' next_nat"
unfolding partial_function'_def by simp

theorem le_not_a_partial_function: "\<not> (partial_function' (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool))"
unfolding partial_function'_def by auto

(* Exercise: 2 stars, optional *)
(* total_relation ? *)

(* Exercise: 2 stars, optional *)
(* empty_relation ? *)

definition reflexive :: "'a relation \<Rightarrow> bool" where
  "reflexive R \<equiv> \<forall>a. R a a"

theorem le_reflexive: "reflexive (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"
unfolding reflexive_def by simp

definition transitive :: "'a relation \<Rightarrow> bool" where
  "transitive R \<equiv> \<forall>a b c. R a b \<longrightarrow> R b c \<longrightarrow> R a c"

theorem le_trans: "transitive (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"
unfolding transitive_def by simp

theorem lt_trans: "transitive (op < :: nat \<Rightarrow> nat \<Rightarrow> bool)"
unfolding transitive_def by simp

(* Exercise: 2 stars, optional *)
(* lt_trans' *)

(* Exercise: 2 stars, optional *)
(* lt_trans'' *)

theorem le_Sn_le: "\<forall>n m. Suc n \<le> m \<longrightarrow> n \<le> m" by simp

(* Exercise: 1 star, optional *)
theorem le_S_n: "\<forall>n m. Suc n \<le> Suc m \<longrightarrow> n \<le> m" by simp

(* Exercise: 2 stars, optional (le_Sn_n_inf) *)
(* Exercise: 1 star, optional *)
theorem le_Sn_n_inf: "\<forall>n. \<not> (Suc n \<le> n)" by simp

definition symmetric :: "'a relation \<Rightarrow> bool" where
  "symmetric R \<equiv> \<forall>a b. R a b \<longrightarrow> R b a"

(* Exercise: 2 stars, optional *)
theorem le_not_symmetric: "\<not> (symmetric (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool))"
unfolding symmetric_def by auto

definition antisymmetric where
  "antisymmetric R \<equiv> \<forall>a b. R a b \<longrightarrow> R b a \<longrightarrow> a = b"

(* Exercise: 2 stars, optional *)

theorem le_antisymmetric: "antisymmetric (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"
unfolding antisymmetric_def by auto

(* Exercise: 2 stars, optional *)

theorem le_step: "\<forall>n m p. n < m \<longrightarrow> m \<le> Suc p \<longrightarrow> n \<le> p" by simp

definition equivalence where
  "equivalence R \<equiv> reflexive R \<and> symmetric R \<and> transitive R"

definition order where
  "order R \<equiv> reflexive R \<and> antisymmetric R \<and> transitive R"

definition preorder where
  "preorder R \<equiv> reflexive R \<and> transitive R"

theorem le_order: "order (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"
unfolding order_def reflexive_def antisymmetric_def transitive_def by auto

subsection {* Reflexive, Transitive Closure *}

inductive_set clos_refl_trans :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" for R :: "('a \<times> 'a) set" where
  rt_step: "(x,y) \<in> R \<Longrightarrow> (x,y) \<in> clos_refl_trans R"
  | rt_refl: "(x,x) \<in> clos_refl_trans R"
  | rt_trans: "\<lbrakk> (x,y) \<in> clos_refl_trans R; (y,z) \<in> clos_refl_trans R \<rbrakk> \<Longrightarrow> (x,z) \<in> clos_refl_trans R"

abbreviation clos_refl_trans_op :: "'a relation \<Rightarrow> 'a relation" ("rt[ _ ]") where
  "rt[R] x y \<equiv> ((x,y) \<in> clos_refl_trans {(x,y). R x y})"

lemma next_nat_closure_is_le_right: "rt[next_nat] n m \<Longrightarrow> rt[next_nat] n (Suc m)"
apply (erule clos_refl_trans.induct)
apply (auto simp add: rt_step)
apply (rule_tac rt_trans, rule_tac rt_step, auto simp add: rt_step)
apply (rule_tac rt_trans, auto)
done

theorem next_nat_closure_is_le: "\<forall>n m. (n \<le> m) \<longleftrightarrow> (rt[next_nat] n m)" (is "\<forall>n m. _ \<longleftrightarrow> (?R n m)")
proof auto
  fix n :: nat and m
  assume "n \<le> m"
  hence mn: "m = n + (m - n)" by auto
  have p: "\<And>a :: nat. ?R n (n + a)"
    apply (induct_tac a, auto simp add: rt_refl)
    using next_nat_closure_is_le_right [of n] by auto
  show "rt[ \<lambda>x. op = (Suc x) ] n m"
    using p [of "m - n"] mn by auto
next
  fix n :: nat and m
  assume "rt[ \<lambda>x. op = (Suc x) ] n m"
  thus "n \<le> m"
    by (rule_tac clos_refl_trans.induct [of n m], auto)
qed

inductive_set refl_step_closure :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" for R :: "('a \<times> 'a) set" where
  rsc_refl: "(x,x) \<in> refl_step_closure R"
  | rsc_step: "\<lbrakk> (x,y) \<in> R; (y,z) \<in> refl_step_closure R \<rbrakk> \<Longrightarrow> (x,z) \<in> refl_step_closure R"

abbreviation refl_step_closure_op :: "'a relation \<Rightarrow> 'a relation" ("rsc[ _ ]") where
  "rsc[R] x y \<equiv> ((x,y) \<in> refl_step_closure {(x,y). R x y})"

theorem rsc_R: "R x y \<Longrightarrow> rsc[R] x y"
by (simp add: rsc_refl rsc_step)

lemma rsc_trans_lem: "rsc[R] x y \<Longrightarrow> rsc[R] y z \<longrightarrow> rsc[R] x z"
apply (erule_tac refl_step_closure.induct)
by (auto simp add: rsc_step)

(* Exercise: 2 stars, optional (rsc_trans) *)
theorem rsc_trans: "\<forall>R x y z. rsc[R] x y \<longrightarrow> rsc[R] y z \<longrightarrow> rsc[R] x z"
using rsc_trans_lem by fastforce

(* Exercise: 3 stars, optional (rtc_rsc_coincide) *)
theorem rtc_rsc_coincide: "\<forall>R x y. rt[R] x y \<longleftrightarrow> rsc[R] x y"
apply auto
apply (erule_tac clos_refl_trans.induct, auto simp add: rsc_R rsc_refl rsc_step)
apply (metis rsc_trans)
apply (erule_tac refl_step_closure.induct, simp add: rt_refl)
apply (metis rt_trans rt_step)
done

end

