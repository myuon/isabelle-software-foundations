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
  conj : P -> Q -> (and P Q).
*)

value "\<lambda>x y. and' x y"
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

theorem andb_prop: "\<forall>b c. b & c = True \<longrightarrow> b = True \<and> c = True" by simp

(*
Theorem andb_prop : \<forall>b c,
  andb b c = true \<rightarrow> b = true \<and> c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H. Qed.

Theorem andb_true_intro : \<forall>b c,
  b = true \<and> c = true \<rightarrow> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

Exercise: 2 stars, optional (bool_prop)
Theorem andb_false : \<forall>b c,
  andb b c = false \<rightarrow> b = false \<or> c = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem orb_prop : \<forall>b c,
  orb b c = true \<rightarrow> b = true \<or> c = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem orb_false_elim : \<forall>b c,
  orb b c = false \<rightarrow> b = false \<and> c = false.
Proof.
  (* FILL IN HERE *) Admitted.
☐

Falsehood
Logical falsehood can be represented in Coq as an inductively defined proposition with no constructors.

Inductive False : Prop := .

Intuition: False is a proposition for which there is no way to give evidence.
Since False has no constructors, inverting an assumption of type False always yields zero subgoals, allowing us to immediately prove any goal.

Theorem False_implies_nonsense :
  False \<rightarrow> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra. Qed.

How does this work? The inversion tactic breaks contra into each of its possible cases, and yields a subgoal for each case. As contra is evidence for False, it has no possible cases, hence, there are no possible subgoals and the proof is done.
Conversely, the only way to prove False is if there is already something nonsensical or contradictory in the context:

Theorem nonsense_implies_False :
  2 + 2 = 5 \<rightarrow> False.
Proof.
  intros contra.
  inversion contra. Qed.

Actually, since the proof of False_implies_nonsense doesn't actually have anything to do with the specific nonsensical thing being proved; it can easily be generalized to work for an arbitrary P:

Theorem ex_falso_quodlibet : \<forall>(P:Prop),
  False \<rightarrow> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra. Qed.

The Latin ex falso quodlibet means, literally, "from falsehood follows whatever you please." This theorem is also known as the principle of explosion.



*)

end
