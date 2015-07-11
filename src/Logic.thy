theory Logic
imports Main
begin

(* In Isabelle, Prop in Coq is just a type 'bool', then things are much easier *)

section {* Logic *}
subsection {* Propositions *}

term "3 = 3"
  (* \<Longrightarrow> "3 = 3" :: "bool" *)
term "\<forall>(n :: nat). n = 2"
  (* \<Longrightarrow> "\<forall>n. n = 2" :: "bool" *)

subsection {* Proofs and Evidence *}

lemma silly: "0 * 3 = (0 :: nat)" by simp
thm silly
  (* \<Longrightarrow> 0 * 3 = 0 *)

subsubsection {* Implications are functions *}

lemma silly_implication: "(1 + 1) = 2 \<longrightarrow> 0 * 3 = (0 :: nat)" by simp
thm silly_implication
  (* \<Longrightarrow> 1 + 1 = 2 \<longrightarrow> 0 * 3 = 0 *)

subsubsection {* Defining Propositions *}

subsection {* Conjunction (Logical "and") *}

(*
Inductive and (P Q : Prop) : Prop :=
  conj : P \<rightarrow> Q \<rightarrow> (and P Q).
*)

value "\<lambda>x y. x \<and> y"
  (* \<Longrightarrow> "_" :: "bool \<Rightarrow> bool \<Rightarrow> bool" *)

subsubsection {* "Introducing" Conjuctions *}

theorem and_example: "((0 :: nat) = 0) \<and> ((4 :: nat) = 2 * 2)" by simp

subsubsection {* "Eliminating" conjunctions *}

theorem proj1: "\<forall>p q. p \<and> q \<longrightarrow> p" by simp

(* Exercise: 1 star, optional (proj2) *)

theorem proj2: "\<forall>p q. p \<and> q \<longrightarrow> q" by simp
theorem and_commut: "\<forall>p q. p \<and> q \<longrightarrow> q \<and> p" by simp

(* Exercise: 2 stars (and_assoc) *)

theorem and_assoc: "\<forall>p q r. p \<and> (q \<and> r) \<longrightarrow> (p \<and> q) \<and> r" by simp

subsection {* Iff *}

no_notation
  iff (infixr "\<longleftrightarrow>" 25)

abbreviation iff (infixr "\<longleftrightarrow>" 25) where
  "iff p q \<equiv> (p \<longrightarrow> q) \<and> (q \<longrightarrow> p)"

theorem iff_implies: "\<forall>p q. (p \<longleftrightarrow> q) \<longrightarrow> p \<longrightarrow> q" by simp
theorem iff_sym: "\<forall>p q. (p \<longleftrightarrow> q) \<longrightarrow> (q \<longleftrightarrow> p)" by simp

(* Exercise: 1 star, optional (iff_properties) *)

theorem iff_refl: "\<forall>p. p \<longleftrightarrow> p" by simp
theorem iff_trans: "\<forall>p q r. (p \<longleftrightarrow> q) \<longrightarrow> (q \<longleftrightarrow> r) \<longrightarrow> (p \<longleftrightarrow> r)" by fastforce

subsection {* Disjunction (Logical "or") *}
subsubsection {* Implementing Disjunction *}

(*
Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
*)

thm "disjI1"
  (* ?P \<Longrightarrow> ?P \<or> ?Q *)
thm "disjI2"
  (* ?Q \<Longrightarrow> ?P \<or> ?Q *)

theorem or_commut: "\<forall>p q. p \<or> q \<longrightarrow> q \<or> p" by simp
theorem or_distributes_over_and_1: "\<forall>p q r. p \<or> (q \<and> r) \<longrightarrow> (p \<or> q) \<and> (p \<or> r)" by simp

(* Exercise: 2 stars (or_distributes_over_and_2) *)
theorem or_distributes_over_and_2: "\<forall>p q r. (p \<or> q) \<and> (p \<or> r) \<longrightarrow> p \<or> (q \<and> r)" by auto

(* Exercise: 1 star, optional (or_distributes_over_and) *)
theorem or_distributes_over_and : "\<forall>P Q R. P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)" by auto

subsubsection {* Relating \<and> and \<or> with andb and orb (advanced) *}

theorem andb_prop: "\<forall>b c. b \<and> c = True \<longrightarrow> b = True \<and> c = True" by simp
theorem andb_true_intro: "\<forall>b c. b = True \<and> c = True \<longrightarrow> b \<and> c" by simp

(* Exercise: 2 stars, optional (bool_prop) *)
theorem andb_false: "\<forall>b c. b \<and> c = False \<longrightarrow> b = False \<or> c = False" by simp
theorem orb_prop: "\<forall>b c. b \<or> c = True \<longrightarrow> b = True \<or> c = True" by simp
theorem orb_false_elim: "\<forall>b c. (b \<or> c) = False \<longrightarrow> b = False \<and> c = False" by simp

subsection {* Falsehood *}

(* Inductive False : Prop := . *)

theorem False_implies_nonsense: "False \<longrightarrow> 2 + 2 = 5" by simp
theorem ex_falso_quodlibet: "\<forall>p. False \<longrightarrow> p" by simp

subsubsection {* Truth *}

(* Exercise: 2 stars, advanced (True) *)

subsection {* Negation *}

(* Definition not (P:Prop) := P \<rightarrow> False. *)

term "\<lambda>x. \<not> x"
  (* \<Longrightarrow> "Not" :: "bool \<Rightarrow> bool" *)

theorem not_False: "\<not> False" by simp
theorem contradiction_implies_anything: "\<forall>p q. (p \<and> \<not> p) \<longrightarrow> q" by simp
theorem double_neg: "\<forall>p. p \<longrightarrow> ~~ p" by simp

(* Exercise: 2 stars, advanced (double_neg_inf) *)
(* Exercise: 2 stars (contrapositive) *)

theorem contrapositive: "\<forall>p q. (p \<longrightarrow> q) \<longrightarrow> (\<not> q \<longrightarrow> \<not> p)" by auto

(* Exercise: 1 star (not_both_true_and_false) *)

theorem "\<not> (p \<and> \<not> p)" by simp

(* Exercise: 1 star, advanced (informal_not_PNP) *)

subsubsection {* Constructive logic *}

theorem classis_double_neg: "~~ p \<longrightarrow> p" by simp

(* Exercise: 5 stars, advanced, optional (classical_axioms) *)

abbreviation "peirce \<equiv> \<forall>p q. ((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
abbreviation "classic \<equiv> \<forall>p. ~~p \<longrightarrow> p"
abbreviation "excluded_middle \<equiv> \<forall>p. p \<or> \<not> p"
abbreviation "de_morgan_not_and_not \<equiv> \<forall>p q. \<not> (\<not> p \<and> \<not> q) \<longrightarrow> p \<or> q"
abbreviation "implies_to_or \<equiv> \<forall>p q. (p \<longrightarrow> q) \<longrightarrow> (\<not> p \<or> q)"

(* Exercise: 3 stars (excluded_middle_irrefutable) *)

theorem excluded_middle_irrefutable: "\<forall>p. \<not> \<not> (p \<or> \<not> p)" by simp

subsubsection {* Inequality *}

theorem not_false_then_true: "\<forall>b. b \<noteq> False \<longrightarrow> b = True" by simp

(* Exercise: 2 stars (false_beq_nat) *)

theorem false_beq_nat: "\<forall>n m. n \<noteq> m \<longrightarrow> n = m = False" by simp

(* Exercise: 2 stars, optional (beq_nat_false) *)

theorem beq_nat_false: "\<forall>n m. n = m = False \<longrightarrow> n \<noteq> m" by simp

end
