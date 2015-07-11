theory MoreInd
imports Main Prop
begin

section {* MoreInd *}
subsection {* Induction Principles *}

thm nat_induct
  (* \<Longrightarrow> ?P 0 \<Longrightarrow> (\<And>n. ?P n \<Longrightarrow> ?P (Suc n)) \<Longrightarrow> ?P ?n *)

theorem mult_0_r': "\<And>n::nat. n * 0 = 0"
apply (induct_tac n)
apply (simp, simp)
done

(* Exercise: 2 stars, optional (plus_one_r') *)
theorem plus_one_r': "\<And>n::nat. n + 1 = Suc n" by simp

datatype yesno = yes | no

thm yesno.induct
  (* \<Longrightarrow> ?P yes \<Longrightarrow> ?P no \<Longrightarrow> ?P ?yesno *)

(* Exercise: 1 star, optional (rgb) *)
datatype rgb = red | green | blue

thm rgb.induct
  (* \<Longrightarrow> ?P red \<Longrightarrow> ?P green \<Longrightarrow> ?P blue \<Longrightarrow> ?P ?rgb *)

datatype natlist = nnil | ncons nat natlist

thm natlist.inducts
  (* \<Longrightarrow> ?P nnil \<Longrightarrow> (\<And>nat natlist. ?P natlist \<Longrightarrow> ?P (ncons nat natlist)) \<Longrightarrow> ?P ?natlist *)

(* Exercise: 1 star, optional (natlist1) *)
datatype natlist1 = nnil1 | nsnoc1 natlist nat

thm natlist1.inducts
  (* \<Longrightarrow> ?P nnil1 \<Longrightarrow> (\<And>natlist nat. ?P (nsnoc1 natlist nat)) \<Longrightarrow> ?P ?natlist1.0 *)

(* Exercise: 1 star, optional (byntree_ind) *)
datatype byntree = bempty | bleaf yesno | nbranch yesno byntree byntree

thm byntree.inducts
  (* \<Longrightarrow> ?P bempty \<Longrightarrow> (\<And>yesno. ?P (bleaf yesno)) \<Longrightarrow> (\<And>yesno byntree1 byntree2. ?P byntree1 \<Longrightarrow>
         ?P byntree2 \<Longrightarrow> ?P (nbranch yesno byntree1 byntree2)) \<Longrightarrow> ?P ?byntree *)

(* Exercise: 1 star, optional (ex_set) *)
datatype ExSet = con1 bool | con2 nat ExSet

thm ExSet.inducts
  (* \<Longrightarrow> (\<And>bool. ?P (con1 bool)) \<Longrightarrow> (\<And>nat ExSet. ?P ExSet \<Longrightarrow> ?P (con2 nat ExSet)) \<Longrightarrow> ?P ?ExSet *)

datatype 'a list' = nil | cons 'a "'a list"

thm list'.inducts
  (* \<Longrightarrow> ?P nil \<Longrightarrow> (\<And>a list. ?P list \<Longrightarrow> ?P (cons a list)) \<Longrightarrow> ?P ?list *)

(* Exercise: 1 star, optional (tree) *)
datatype 'a tree = leaf 'a | node "'a tree" "'a tree"

thm tree.inducts
  (* \<Longrightarrow> (\<And>a. ?P (leaf a)) \<Longrightarrow> (\<And>tree1 tree2. ?P tree1 \<Longrightarrow> ?P tree2 \<Longrightarrow> ?P (node tree1 tree2)) \<Longrightarrow> ?P ?tree *)

(* Exercise: 1 star, optional (mytype) *)
datatype 'a mytype = constr1 'a | constr2 nat | constr3 "'a mytype" nat

thm mytype.inducts
  (* \<Longrightarrow> (\<And>a. ?P (constr1 a)) \<Longrightarrow> (\<And>nat. ?P (constr2 nat)) \<Longrightarrow> (\<And>mytype nat. ?P mytype \<Longrightarrow> ?P (constr3 mytype nat)) \<Longrightarrow> ?P ?mytype *)

(* Exercise: 1 star, optional (foo) *)
datatype ('a,'b) foo = bar 'a | baz 'b | quux "nat \<Rightarrow> ('a,'b) foo"

thm foo.inducts
  (* \<Longrightarrow> (\<And>a. ?P (bar a)) \<Longrightarrow> (\<And>b. ?P (baz b)) \<Longrightarrow> (\<And>fun. (\<And>x. ?P (fun x)) \<Longrightarrow> ?P (quux fun)) \<Longrightarrow> ?P ?foo *)

(* Exercise: 1 star, optional (foo') *)
datatype 'a foo' = C1 "'a list" "'a foo'" | C2

thm foo'.inducts
  (* \<Longrightarrow> (\<And>list foo'. ?P foo' \<Longrightarrow> ?P (C1 list foo')) \<Longrightarrow> ?P C2 \<Longrightarrow> ?P ?foo' *)

subsubsection {* Induction Hypotheses *}
subsubsection {* More on the induction Tactic *}

(* Exercise: 1 star, optional (plus_explicit_prop) *)

subsubsection {* Generalizing Inductions. *}

(*
lemma one_not_beautiful: "\<And>n :: nat. n = Suc 0 \<Longrightarrow> \<not> (beautiful n)"
apply (rule, erule beautiful.cases, auto)


lemma one_not_beautiful': "\<not> beautiful 1" sorry
*)

subsection {* Informal Proofs (Advanced) *}
subsubsection {* Informal Proofs by Induction *}
subsubsection {* Induction Over an Inductively Defined Set *}
subsubsection {* Induction Over an Inductively Defined Proposition *}

subsection {* Optional Material *}
subsubsection {* Induction Principles in Prop *}

subsection {* Additional Exercises *}

(* Exercise: 2 stars, optional (foo_ind_principle) *)
datatype ('a,'b) foo'' = foo1 'a | foo2 'b | foo3 "('a,'b) foo"

thm foo''.inducts
  (* \<Longrightarrow> (\<And>a. ?P (foo1 a)) \<Longrightarrow> (\<And>b. ?P (foo2 b)) \<Longrightarrow> (\<And>foo. ?P (foo3 foo)) \<Longrightarrow> ?P ?foo'' *)

(* Exercise: 2 stars, optional (bar_ind_principle) *)
datatype bar = bar1 nat | bar2 bar | bar3 bool bar

thm bar.inducts
  (* \<Longrightarrow> (\<And>nat. ?P (bar1 nat)) \<Longrightarrow> (\<And>bar. ?P bar \<Longrightarrow> ?P (bar2 bar)) \<Longrightarrow> (\<And>bool bar. ?P bar \<Longrightarrow> ?P (bar3 bool bar)) \<Longrightarrow> ?P ?bar *)

(* Exercise: 2 stars, optional (no_longer_than_ind) *)
inductive no_longer_than :: "'a set \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  nlt_nil: "no_longer_than X [] n"
  | nlt_cons: "no_longer_than X l n \<Longrightarrow> no_longer_than X (x # l) (Suc n)"
  | nlt_succ: "no_longer_than X l n \<Longrightarrow> no_longer_than X l (Suc n)"

thm no_longer_than.inducts
  (* \<Longrightarrow> no_longer_than ?x1.0 ?x2.0 ?x3.0 \<Longrightarrow>
    (\<And>X n. ?P X [] n) \<Longrightarrow>
    (\<And>X l n x. no_longer_than X l n \<Longrightarrow> ?P X l n \<Longrightarrow> ?P X (x # l) (Suc n)) \<Longrightarrow>
    (\<And>X l n. no_longer_than X l n \<Longrightarrow> ?P X l n \<Longrightarrow> ?P X l (Suc n)) \<Longrightarrow> ?P ?x1.0 ?x2.0 ?x3.0 *)

subsubsection {* Induction Principles for other Logical Propositions *}

(*
inductive eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq x x"
*)

thm eq.inducts
  (* \<Longrightarrow> Predicate.eq ?x1.0 ?x2.0 \<Longrightarrow> (\<And>x. ?P x x) \<Longrightarrow> ?P ?x1.0 ?x2.0 *)

(* Exercise: 1 star, optional (and_ind_principle) *)
thm induct_conj(1)
  (* \<Longrightarrow> ??.HOL.induct_forall (\<lambda>x. ??.HOL.induct_conj (?A x) (?B x)) = ??.HOL.induct_conj (??.HOL.induct_forall ?A) (??.HOL.induct_forall ?B) *)
thm induct_conj(2)
  (* \<Longrightarrow> ??.HOL.induct_implies ?C (??.HOL.induct_conj ?A ?B) = ??.HOL.induct_conj (??.HOL.induct_implies ?C ?A) (??.HOL.induct_implies ?C ?B) *)

(* Exercise: 1 star, optional (or_ind_principle) *)
(* Exercise: 1 star, optional (False_ind_principle) *)

subsubsection {* Explicit Proof Objects for Induction *}

thm nat.inducts
  (* \<Longrightarrow> ?P 0 \<Longrightarrow> (\<And>nat. ?P nat \<Longrightarrow> ?P (Suc nat)) \<Longrightarrow> ?P ?nat *)

lemma even_2x: "\<And>n :: nat. even n \<Longrightarrow> n = 2 * (n div 2)" by auto
lemma noteven_2x1: "\<And>n :: nat. \<not> (even n) \<Longrightarrow> n = 2 * (n div 2) + 1" by presburger

theorem nat_induct2: "P 0 \<Longrightarrow> P (Suc 0) \<Longrightarrow> (\<And>n :: nat. P n \<Longrightarrow> P (Suc (Suc n))) \<Longrightarrow> P n"
proof (cases "even n")
  assume "P 0" "P (Suc 0)" and hyp: "\<And>n. P n \<Longrightarrow> P (Suc (Suc n))"
  {
    assume "even n"
    then obtain k where k: "n = 2 * k" using even_2x [of n] by simp
    have "P (2 * k)"
      by (induct k, simp, rule `P 0`, simp, rule hyp, simp)
    thus "P n" by (simp add: k)
  }
  {
    assume "n mod 2 \<noteq> 0"
    then obtain k where k: "n = 2 * k + 1" using noteven_2x1 [of n] by auto
    have "P (2 * k + 1)"
      by (induct k, simp, rule `P (Suc 0)`, simp, rule hyp, simp)
    thus "P n" by (simp add: k)
  }
qed

lemma even_ev': "even n \<longrightarrow> ev n"
apply (rule nat_induct2, auto)
apply (rule ev_0, rule ev_SS, simp)
done

subsubsection {* The Coq Trusted Computing Base *}

end

