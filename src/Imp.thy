theory Imp
imports Main Prop MoreLogic
begin

section {* Imp *}
subsubsection {* Sflib *}

subsection {* Arithmetic and Boolean Expressions *}
subsubsection {* Syntax *}

datatype aexp = ANum nat | APlus aexp aexp | AMinus aexp aexp | AMult aexp aexp
datatype bexp = BTrue | BFalse | BEq aexp aexp | BLe aexp aexp | BNot bexp | BAnd bexp bexp

subsubsection {* Evaluation *}

fun aeval :: "aexp \<Rightarrow> nat" where
  "aeval (ANum n) = n"
  | "aeval (APlus a1 a2) = aeval a1 + aeval a2"
  | "aeval (AMinus a1 a2) = aeval a1 - aeval a2"
  | "aeval (AMult a1 a2) = aeval a1 * aeval a2"

lemma test_aeval1: "aeval (APlus (ANum 2) (ANum 2)) = 4" by simp

fun beval :: "bexp \<Rightarrow> bool" where
  "beval BTrue = True"
  | "beval BFalse = False"
  | "beval (BEq a1 a2) = (aeval a1 = aeval a2)"
  | "beval (BLe a1 a2) = (aeval a1 \<le> aeval a2)"
  | "beval (BNot b1) = (\<not> beval b1)"
  | "beval (BAnd b1 b2) = (beval b1 \<and> beval b2)"

subsubsection {* Optimization *}

fun optimize_0plus :: "aexp \<Rightarrow> aexp" where
  "optimize_0plus (ANum n) = ANum n"
  | "optimize_0plus (APlus (ANum 0) e2) = optimize_0plus e2"
  | "optimize_0plus (APlus e1 e2) = APlus (optimize_0plus e1) (optimize_0plus e2)"
  | "optimize_0plus (AMinus e1 e2) = AMinus (optimize_0plus e1) (optimize_0plus e2)"
  | "optimize_0plus (AMult e1 e2) = AMult (optimize_0plus e1) (optimize_0plus e2)"

lemma test_optimize_0plus:
  "optimize_0plus (APlus (ANum 2) (APlus (ANum 0) (APlus (ANum 0) (ANum 1)))) = APlus (ANum 2) (ANum 1)"
by (subst Suc_1 [symmetric], subst optimize_0plus.simps(3), simp)

theorem optimize_0plus_sound: "aeval (optimize_0plus a) = aeval a"
  apply (induct rule: optimize_0plus.induct, auto)
  done

subsection {* Coq Automation *}

subsubsection {* Tacticals *}
subsubsection {* The repeat Tactical *}

theorem ev100: "ev (100 :: nat)"
proof -
  have 1: "\<And>n::nat. ev (double n)" using double_even by simp
  show "ev 100" using 1 [of 50] by simp
qed

subsubsection {* The try Tactical *}

theorem silly1: "aeval ae = aeval ae" by simp
theorem silly2: "P \<Longrightarrow> P" by simp

subsubsection {* The ; Tactical (Simple Form) *}

lemma foo: "0 \<le> (n :: nat)" by simp

subsubsection {* The ; Tactical (General Form) *}
subsubsection {* Defining New Tactic Notations *}
subsubsection {* Bulletproofing Case Analyses *}

(* Exercise: 3 stars (optimize_0plus_b) *)
fun optimize_0plus_b :: "bexp \<Rightarrow> bexp" where
  "optimize_0plus_b BTrue = BTrue"
  | "optimize_0plus_b BFalse = BFalse"
  | "optimize_0plus_b (BEq a1 a2) = BEq a1 a2"
  | "optimize_0plus_b (BLe a1 a2) = BLe a1 a2"
  | "optimize_0plus_b (BNot b1) = BNot b1"
  | "optimize_0plus_b (BAnd BTrue b2) = b2"
  | "optimize_0plus_b (BAnd BFalse _) = BFalse"
  | "optimize_0plus_b (BAnd b1 b2) = BAnd b1 b2"

theorem optimize_0plus_b_sound: "beval (optimize_0plus_b b) = beval b"
  apply (induct rule: optimize_0plus_b.induct)
  apply auto
  done

(* Exercise: 4 stars, optional (optimizer) *)

subsubsection {* The omega Tactic *}

lemma silly_presburger_example: "(m :: nat) + n \<le> n + o' \<and> o' + 3 = p + 3 \<Longrightarrow> m \<le> p" by simp

subsubsection {* A Few More Handy Tactics *}

subsection {* Evaluation as a Relation *}

inductive aevalR :: "aexp \<Rightarrow> nat \<Rightarrow> bool" (infixl "\<Down>" 70) where
  E_ANum: "aevalR (ANum n) n"
  | E_APlus: "\<lbrakk> aevalR e1 n1; aevalR e2 n2 \<rbrakk> \<Longrightarrow> aevalR (APlus e1 e2) (n1 + n2)"
  | E_AMinus: "\<lbrakk> aevalR e1 n1; aevalR e2 n2 \<rbrakk> \<Longrightarrow> aevalR (AMinus e1 e2) (n1 - n2)"
  | E_AMult: "\<lbrakk> aevalR e1 n1; aevalR e2 n2 \<rbrakk> \<Longrightarrow> aevalR (AMult e1 e2) (n1 * n2)"

subsubsection {* Inference Rule Notation *}
subsubsection {* Equivalence of the Definitions *}

theorem aeval_iff_aevalR: "a \<Down> n \<longleftrightarrow> aeval a = n"
apply auto
apply (erule aevalR.inducts, auto)
apply (rule aeval.induct, auto, rule)
  apply (rule, auto)+
done

(* Exercise: 3 stars (bevalR) *)
inductive bevalR :: "bexp \<Rightarrow> bool \<Rightarrow> bool" where
  E_BTrue: "bevalR BTrue True"
  | E_BFalse: "bevalR BFalse False"
  | E_BEq: "\<lbrakk> aevalR a1 m1; aevalR a2 m2 \<rbrakk> \<Longrightarrow> bevalR (BEq a1 a2) (m1 = m2)"
  | E_BLe: "\<lbrakk> aevalR a1 m1; aevalR a2 m2 \<rbrakk> \<Longrightarrow> bevalR (BLe a1 a2) (m1 \<le> m2)"
  | E_BNot: "bevalR b1 m1 \<Longrightarrow> bevalR (BNot b1) (\<not> m1)"
  | E_BAnd: "\<lbrakk> bevalR b1 m1; bevalR b2 m2 \<rbrakk> \<Longrightarrow> bevalR (BAnd b1 b2) (m1 \<and> m2)"

lemma bevalR_beval: "bevalR b (beval b)"
apply (induct b)
apply (simp, rule)+
apply (fastforce simp add: aeval_iff_aevalR)
apply (fastforce simp add: aeval_iff_aevalR)
apply (simp, metis E_BLe aeval_iff_aevalR)
apply (simp, rule, simp)
apply (simp, rule, simp, simp)
done

theorem beval_iff_bevalR: "bevalR b m \<longleftrightarrow> beval b = m"
apply rule
apply (erule bevalR.inducts, simp, simp)
  apply (simp, fastforce simp add: aeval_iff_aevalR)+
proof -
  assume 1: "beval b = m"
  show "bevalR b m"
    apply (subst 1 [symmetric])
    by (rule bevalR_beval)
qed

subsubsection {* Computational vs. Relational Definitions *}

datatype aexp' = ANum nat | APlus aexp' aexp' | AMinus aexp' aexp' | AMult aexp' aexp'
  | ADiv aexp' aexp'

inductive aevalR' :: "aexp' \<Rightarrow> nat \<Rightarrow> bool" where
  E_ANum: "aevalR' (ANum n) n"
  | E_APlus: "\<lbrakk> aevalR' e1 n1; aevalR' e2 n2 \<rbrakk> \<Longrightarrow> aevalR' (APlus e1 e2) (n1 + n2)"
  | E_AMinus: "\<lbrakk> aevalR' e1 n1; aevalR' e2 n2 \<rbrakk> \<Longrightarrow> aevalR' (AMinus e1 e2) (n1 - n2)"
  | E_AMult: "\<lbrakk> aevalR' e1 n1; aevalR' e2 n2 \<rbrakk> \<Longrightarrow> aevalR' (AMult e1 e2) (n1 * n2)"
  | E_ADiv: "\<lbrakk> aevalR' e1 n1; aevalR' e2 n2; n2 * n3 = n1 \<rbrakk> \<Longrightarrow> aevalR' (ADiv a1 a2) n3"

subsubsection {* Adding nondeterminism *}

datatype aexp'' = AAny | ANum nat | APlus aexp'' aexp'' | AMinus aexp'' aexp'' | AMult aexp'' aexp''

inductive aevalR'' :: "aexp'' \<Rightarrow> nat \<Rightarrow> bool" where
  E_Any: "aevalR'' AAny n"
  | E_ANum: "aevalR'' (ANum n) n"
  | E_APlus: "\<lbrakk> aevalR'' e1 n1; aevalR'' e2 n2 \<rbrakk> \<Longrightarrow> aevalR'' (APlus e1 e2) (n1 + n2)"
  | E_AMinus: "\<lbrakk> aevalR'' e1 n1; aevalR'' e2 n2 \<rbrakk> \<Longrightarrow> aevalR'' (AMinus e1 e2) (n1 - n2)"
  | E_AMult: "\<lbrakk> aevalR'' e1 n1; aevalR'' e2 n2 \<rbrakk> \<Longrightarrow> aevalR'' (AMult e1 e2) (n1 * n2)"

subsection {* Expressions With Variables *}
subsubsection {* Identifiers *}

datatype id = Id nat

theorem eq_id_dec: "\<And>id1 id2 :: id. {id1 = id2} \<bar> {id1 \<noteq> id2}"
apply (case_tac id1, case_tac id2, auto)
by (rule eq_nat_dec)

fun eq_id_dec where
  "eq_id_dec id1 id2 = (id1 = id2)"

lemma eq_id: "(if eq_id_dec x x then p else q) = p" by simp

(* Exercise: 1 star, optional (neq_id) *)
lemma neq_id: "x \<noteq> y \<Longrightarrow> (if eq_id_dec x y then p else q) = q" by simp

subsubsection {* States *}

type_synonym state = "id \<Rightarrow> nat"

fun empty_state :: state where
  "empty_state _ = 0"
fun update :: "state \<Rightarrow> id \<Rightarrow> nat \<Rightarrow> state" where
  "update st x n x' = (if eq_id_dec x x' then n else st x')"

(* Exercise: 1 star (update_eq) *)
theorem update_eq: "update st x n x = n" by simp

(* Exercise: 1 star (update_neq) *)
theorem udpate_neq: "x2 \<noteq> x1 \<Longrightarrow> update st x2 n x1 = st x1" by simp

(* Exercise: 1 star (update_example) *)
theorem update_example: "update empty_state (Id 2) n (Id 3) = 0" by simp

(* Exercise: 1 star (update_shadow) *)
theorem update_shadow: "update (update st x2 n1) x2 n2 x1 = update st x2 n2 x1" by simp

(* Exercise: 2 stars (update_same) *)
theorem update_same: "st x1 = n1 \<Longrightarrow> update st x1 n1 x2 = st x2" by auto

(* Exercise: 3 stars (update_permute) *)
theorem update_permute: "x2 \<noteq> x1 \<Longrightarrow> update (update st x2 n1) x1 n2 x3 = update (update st x1 n2) x2 n1 x3"
by auto

subsubsection {* Syntax *}

datatype aexp3 = ANum nat | AId id | APlus aexp3 aexp3 | AMinus aexp3 aexp3 | AMult aexp3 aexp3
abbreviation X where "X \<equiv> Id 0"
abbreviation Y where "Y \<equiv> Id 1"
abbreviation Z where "Z \<equiv> Id 2"

datatype bexp3 = BTrue | BFalse | BEq aexp3 aexp3 | BLe aexp3 aexp3 | BNot bexp3 | BAnd bexp3 bexp3

subsubsection {* Evaluation *}

fun aeval3 where
  "aeval3 st (ANum n) = n"
  | "aeval3 st (AId x) = st x"
  | "aeval3 st (APlus a1 a2) = aeval3 st a1 + aeval3 st a2"
  | "aeval3 st (AMinus a1 a2) = aeval3 st a1 - aeval3 st a2"
  | "aeval3 st (AMult a1 a2) = aeval3 st a1 * aeval3 st a2"

fun beval3 where
  "beval3 st BTrue = True"
  | "beval3 st BFalse = False"
  | "beval3 st (BEq a1 a2) = (aeval3 st a1 = aeval3 st a2)"
  | "beval3 st (BLe a1 a2) = (aeval3 st a1 \<le> aeval3 st a2)"
  | "beval3 st (BNot b1) = (\<not> beval3 st b1)"
  | "beval3 st (BAnd b1 b2) = (beval3 st b1 \<and> beval3 st b2)"

lemma aexp1: "aeval3 (update empty_state x 5) (APlus (ANum 3) (AMult (AId x) (ANum 2))) = 13"
by (simp add: sumbool.left)

lemma bexp1: "beval3 (update empty_state x 5) (BAnd BTrue (BNot (BLe (AId x) (ANum 4)))) = True"
by (simp add: sumbool.left)

subsection {* Commands *}
subsubsection {* Syntax *}

datatype com = CSkip | CAss id aexp3 | CSeq com com | CIf bexp3 com com | CWhile bexp3 com

notation
  CSkip ("SKIP") and
  CAss ("_ ::= _" [50,50] 90) and
  CSeq (infixr ";;" 30) and
  CWhile ("WHILE _ DO _ END" 90) and
  CIf ("IF _ THEN _ ELSE _ FI" 80)

definition fact_in_Isabelle :: com where
  "fact_in_Isabelle \<equiv>
    Z ::= AId X ;;
    Y ::= ANum 1 ;;
    WHILE BNot (BEq (AId Z) (ANum 0)) DO
      Y ::= AMult (AId Y) (AId Z) ;;
      Z ::= AMinus (AId Z) (ANum 1)
    END"

subsubsection {* Examples *}

definition plus2 where
  "plus2 \<equiv> (X ::= APlus (AId X) (ANum 2))"
definition XtimesYinZ where
  "XtimesYinZ \<equiv> (Z ::= AMult (AId X) (AId Y))"
definition subtract_slowly_body where
  "subtract_slowly_body \<equiv> (
    Z ::= AMinus (AId Z) (ANum 1) ;;
    X ::= AMinus (AId X) (ANum 1)
  )"

subsubsection {* Loops *}

definition subtract_slowly where
  "subtract_slowly \<equiv> (
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      subtract_slowly_body
    END
  )"
definition subtract_3_from_5_slowly where
  "subtract_3_from_5_slowly \<equiv> (
    X ::= ANum 3 ;;
    Z ::= ANum 5 ;;
    subtract_slowly
  )"

subsubsection {* An infinite loop *}

definition loop where
  "loop \<equiv> WHILE BTrue DO SKIP END"

subsection {* Evaluation *}
subsubsection {* Evaluation as a Function (Failed Attempt) *}

fun ceval_fun_no_while where
  "ceval_fun_no_while st SKIP = st"
  | "ceval_fun_no_while st (x ::= a1) = update st x (aeval3 st a1)"
  | "ceval_fun_no_while st (c1 ;; c2) = ceval_fun_no_while (ceval_fun_no_while st c1) c2"
  | "ceval_fun_no_while st (IF b THEN c1 ELSE c2 FI) = (if (beval3 st b)
      then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2)"
  | "ceval_fun_no_while st (WHILE b DO c END) = st" (* bogus *)

subsubsection {* Evaluation as a Relation *}
subsubsection {* Operational Semantics *}

inductive ceval :: "com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" ("_ %: _ \<Down> _" [39] 40) where
  E_Skip: "SKIP %: st \<Down> st"
  | E_Ass: "aeval3 st a1 = n \<Longrightarrow> (x ::= a1) %: st \<Down> (update st x n)"
  | E_Seq: "\<lbrakk> c1 %: st \<Down> st'; c2 %: st' \<Down> st'' \<rbrakk> \<Longrightarrow> (c1 ;; c2) %: st \<Down> st''"
  | E_IfTrue: "\<lbrakk> beval3 st b = True; c1 %: st \<Down> st' \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2 FI) %: st \<Down> st'"
  | E_IfFalse: "\<lbrakk> beval3 st b = False; c2 %: st \<Down> st' \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2 FI) %: st \<Down> st'"
  | E_WhileEnd: "beval3 st b = False \<Longrightarrow> (WHILE b DO c END) %: st \<Down> st"
  | E_WhileLoop: "\<lbrakk> beval3 st b = True; c %: st \<Down> st'; (WHILE b DO c END) %: st' \<Down> st'' \<rbrakk> \<Longrightarrow> (WHILE b DO c END) %: st \<Down> st''"

lemma eval_example1: "(
  X ::= ANum 2 ;;
  IF BLe (AId X) (ANum 1)
    THEN Y ::= ANum 3
    ELSE Z ::= ANum 4
  FI) %: empty_state \<Down> (update (update empty_state X 2) Z 4)"
by (rule+, auto, rule, simp)

(* Exercise: 2 stars (ceval_example2) *)
lemma ceval_example2: "(X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2)
  %: empty_state \<Down> (update (update (update empty_state X 0) Y 1) Z 2)"
by (auto, rule+, auto, rule, simp)

(* Exercise: 3 stars, advanced (pup_to_n) *)
definition pup_to_n where
  "pup_to_n \<equiv> (
    Y ::= ANum 0;;
    WHILE BLe (ANum 1) (AId X) DO
      Y ::= APlus (AId Y) (AId X);;
      X ::= AMinus (AId X) (ANum 1)
    END
  )"

theorem pup_to_2_ceval:
  "pup_to_n %: (update empty_state X 2) \<Down>
    update (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0"
unfolding pup_to_n_def
apply (rule, simp, rule, simp)
apply (rule, simp, rule, rule, simp, rule, simp)
apply (rule, simp, rule, rule, simp, rule, rule, simp)
apply (subst Num.numeral_3_eq_3, subst Num.numeral_2_eq_2, rule E_WhileEnd, simp)
done

subsubsection {* Determinism of Evaluation *}

lemma ceval_deterministic_lemma: "c %: st \<Down> st' \<Longrightarrow> (\<And>u. c %: st \<Down> u \<Longrightarrow> st' = u)"
using ceval.induct [of c st st' "\<lambda>c0 st0 st'0. ((c0 %: st0 \<Down> st'0) \<longrightarrow> (\<forall>u. (c0 %: st0 \<Down> u) \<longrightarrow> (st'0 = u)))"]
apply rule
apply simp
proof-
  fix u sta
  assume "c %: st \<Down> st'" "c %: st \<Down> u"
  show "(SKIP %: sta \<Down> sta) \<longrightarrow> (\<forall>u. (SKIP %: sta \<Down> u) \<longrightarrow> sta = u)"
    by (auto, erule ceval.cases, auto, erule ceval.cases, auto)
next
  fix u sta a1 n x
  assume a: "c %: st \<Down> st'" "c %: st \<Down> u" "aeval3 sta a1 = n"
  show "(x ::= a1 %: sta \<Down> update sta x n) \<longrightarrow> (\<forall>u. (x ::= a1 %: sta \<Down> u) \<longrightarrow> update sta x n = u)"
    apply (auto, erule ceval.cases, auto)
    apply (erule ceval.cases, auto simp add: a)
    done
next
  fix u c1 sta st'a c2 st''
  assume a1: "c %: st \<Down> st'" "c %: st \<Down> u"
  and a2: "c1 %: sta \<Down> st'a" "(c1 %: sta \<Down> st'a) \<longrightarrow> (\<forall>u. (c1 %: sta \<Down> u) \<longrightarrow> st'a = u)"
  and a3: "c2 %: st'a \<Down> st''" "(c2 %: st'a \<Down> st'') \<longrightarrow> (\<forall>u. (c2 %: st'a \<Down> u) \<longrightarrow> st'' = u)"
  show "((c1 ;; c2) %: sta \<Down> st'') \<longrightarrow> (\<forall>u. ((c1 ;; c2) %: sta \<Down> u) \<longrightarrow> st'' = u)"
    proof auto
      fix u
      assume "(c1 ;; c2) %: sta \<Down> st''" "(c1 ;; c2) %: sta \<Down> u"
      from this(2) obtain u0 where
        u0: "c1 %: sta \<Down> u0" "c2 %: u0 \<Down> u" by (rule, auto)
      have 1: "st'a = u0" using u0(1) a2 by simp
      show "st'' = u" using a3(2) u0(2) by (simp add: a3(1), simp add: 1)
    qed
next
  fix u sta b c1 st'a c2
  assume a: "c %: st \<Down> st'" "c %: st \<Down> u" "beval3 sta b = True" "c1 %: sta \<Down> st'a" "(c1 %: sta \<Down> st'a) \<longrightarrow> (\<forall>u. (c1 %: sta \<Down> u) \<longrightarrow> st'a = u)"
  show "(IF b THEN c1 ELSE c2 FI %: sta \<Down> st'a) \<longrightarrow> (\<forall>u. (IF b THEN c1 ELSE c2 FI %: sta \<Down> u) \<longrightarrow> st'a = u)"
    proof auto
      fix u
      assume "IF b THEN c1 ELSE c2 FI %: sta \<Down> st'a" "IF b THEN c1 ELSE c2 FI %: sta \<Down> u"
      from this(2) have "c1 %: sta \<Down> u" by (rule, auto, auto simp add: a(3))
      thus "st'a = u" using a(5) a(4) by simp
    qed
next
  fix u sta b c2 st'a c1
  assume a: "c %: st \<Down> st'" "c %: st \<Down> u" "beval3 sta b = False" "c2 %: sta \<Down> st'a" "(c2 %: sta \<Down> st'a) \<longrightarrow> (\<forall>u. (c2 %: sta \<Down> u) \<longrightarrow> st'a = u)"
  show "(IF b THEN c1 ELSE c2 FI %: sta \<Down> st'a) \<longrightarrow> (\<forall>u. (IF b THEN c1 ELSE c2 FI %: sta \<Down> u) \<longrightarrow> st'a = u)"
    proof auto
      fix u
      assume "IF b THEN c1 ELSE c2 FI %: sta \<Down> st'a" "IF b THEN c1 ELSE c2 FI %: sta \<Down> u"
      from this(2) have "c2 %: sta \<Down> u" by (rule, auto, auto simp add: a(3))
      thus "st'a = u" using a(5) a(4) by simp
    qed
next
  fix u sta b ca
  assume a: "c %: st \<Down> st'" "c %: st \<Down> u" "beval3 sta b = False"
  show "(WHILE b DO ca END %: sta \<Down> sta) \<longrightarrow> (\<forall>u. (WHILE b DO ca END %: sta \<Down> u) \<longrightarrow> sta = u)"
    proof auto
      fix u
      assume "WHILE b DO ca END %: sta \<Down> sta" "WHILE b DO ca END %: sta \<Down> u"
      from this(2) show "sta = u"
        by (rule, auto, auto simp add: a(3))
    qed
next
  fix u sta b ca st'a st''
  assume "c %: st \<Down> st'" "c %: st \<Down> u"
  and a: "beval3 sta b = True" "ca %: sta \<Down> st'a" "(ca %: sta \<Down> st'a) \<longrightarrow> (\<forall>u. (ca %: sta \<Down> u) \<longrightarrow> st'a = u)"
  and a2: "WHILE b DO ca END %: st'a \<Down> st''" "(WHILE b DO ca END %: st'a \<Down> st'') \<longrightarrow> (\<forall>u. (WHILE b DO ca END %: st'a \<Down> u) \<longrightarrow> st'' = u)"

  have b1: "\<And>u. ca %: sta \<Down> u \<Longrightarrow> st'a = u" using a by simp
  have b2: "\<And>u. (WHILE b DO ca END) %: st'a \<Down> u \<Longrightarrow> st'' = u" using a2 by simp
  show "(WHILE b DO ca END %: sta \<Down> st'') \<longrightarrow> (\<forall>u. (WHILE b DO ca END %: sta \<Down> u) \<longrightarrow> st'' = u)"
    proof auto
      fix u
      assume a4: "WHILE b DO ca END %: sta \<Down> st''" "WHILE b DO ca END %: sta \<Down> u"
      from this(2) obtain u' where
        u': "ca %: sta \<Down> u'" "(WHILE b DO ca END) %: u' \<Down> u" by (rule, auto, auto simp add: a(1))
      have "st'a = u'" using b1 [OF u'(1)] by simp
      thus "st'' = u" using b2 u'(2) by auto
    qed
qed (auto)

theorem ceval_deterministic: "\<lbrakk> c %: st \<Down> st1; c %: st \<Down> st2 \<rbrakk> \<Longrightarrow> st1 = st2"
by (auto simp add: ceval_deterministic_lemma)

subsection {* Reasoning About Imp Programs *}

theorem plus2_spec: "\<lbrakk> st X = n; plus2 %: st \<Down> st' \<rbrakk> \<Longrightarrow> st' X = n + 2"
unfolding plus2_def
by (erule ceval.cases, auto)

(* Exercise: 3 stars (XtimesYinZ_spec) *)
theorem XtimesYinZ_spec: "XtimesYinZ %: st \<Down> st' \<Longrightarrow> st' Z = st X * st Y"
unfolding XtimesYinZ_def
by (erule ceval.cases, auto)

(* Exercise: 3 stars (loop_never_stops) *)
lemma while_induction:
  assumes red: "(WHILE b DO c END) %: st \<Down> st'"
  and base: "\<And>t t'. \<lbrakk> beval3 t b = False; t' = t \<rbrakk> \<Longrightarrow> P t t'"
  and step: "\<And>t t' t''. \<lbrakk> beval3 t b = True; c %: t \<Down> t'; (WHILE b DO c END) %: t' \<Down> t''; P t' t'' \<rbrakk> \<Longrightarrow> P t t''"
  shows "P st st'"
proof-
  have "(WHILE b DO c END) %: st \<Down> st' \<Longrightarrow> P st st'"
    using ceval.induct [of _ _ _ "\<lambda>c0 t t'. WHILE b DO c END = c0 \<longrightarrow> P t t'"] apply rule
    apply (simp, auto, simp add: base)
    apply (fastforce simp add: step)
    apply (fastforce simp add: step)
    done
  thus ?thesis by (simp add: red)
qed

theorem loop_never_stops: "\<not> (loop %: st \<Down> st')"
proof (unfold loop_def, auto)
  assume p: "WHILE BTrue DO SKIP END %: st \<Down> st'"
  show "False"
    using while_induction [of BTrue SKIP st st' "\<lambda>_. \<lambda>_. False"]
    by (rule, simp add: p, auto)
qed

(* Exercise: 3 stars (no_whilesR) *)
primrec no_whiles where
  "no_whiles SKIP = True"
  | "no_whiles (_ ::= _) = True"
  | "no_whiles (c1 ;; c2) = (no_whiles c1 \<and> no_whiles c2)"
  | "no_whiles (IF _ THEN ct ELSE cf FI) = (no_whiles ct \<and> no_whiles cf)"
  | "no_whiles (WHILE _ DO _ END) = False"

inductive no_whilesR where
  NW_Skip: "no_whilesR SKIP"
  | NW_Seq: "no_whilesR (x ::= aexp)"
  | NW_Ass: "\<lbrakk> no_whilesR e1; no_whilesR e2 \<rbrakk> \<Longrightarrow> no_whilesR (e1 ;; e2)"
  | NW_If: "\<lbrakk> no_whilesR e1; no_whilesR e2 \<rbrakk> \<Longrightarrow> no_whilesR (IF b THEN e1 ELSE e2 FI)"

theorem no_whiles_eqv: "no_whiles c \<longleftrightarrow> no_whilesR c"
apply rule
  apply (induct c, auto, rule+, auto, rule, auto)
  apply (erule no_whilesR.induct, auto)
done

(* Exercise: 4 stars (no_whiles_terminating) *)
theorem no_whiles_terminating: "no_whilesR c \<Longrightarrow> (\<And>st. c %: st \<Down> (ceval_fun_no_while st c))"
using no_whilesR.induct [of c "\<lambda>c0. \<forall>st. c0 %: st \<Down> (ceval_fun_no_while st c0)"] apply (rule, simp)
proof-
  fix st
  assume "no_whilesR c" show "\<forall>x. SKIP %: x \<Down> ceval_fun_no_while x SKIP" by (auto, rule)
next
  fix st x aexp
  assume "no_whilesR c" show "\<forall>xa. x ::= aexp %: xa \<Down> ceval_fun_no_while xa (x ::= aexp)" by (auto, rule, simp)
next
  fix st e1 e2
  assume a: "no_whilesR c" "no_whilesR e1" "\<forall>x. e1 %: x \<Down> ceval_fun_no_while x e1" "no_whilesR e2" "\<forall>x. e2 %: x \<Down> ceval_fun_no_while x e2"
  show "\<forall>x. (e1 ;; e2) %: x \<Down> ceval_fun_no_while x (e1 ;; e2)"
    proof (rule, rule)
      fix x
      {
        show "e1 %: x \<Down> ceval_fun_no_while x e1"
          using a(3) by simp
      }
      {
        show "e2 %: ceval_fun_no_while x e1 \<Down> ceval_fun_no_while x (e1 ;; e2)"
          using a(5) by simp
      }
    qed
next
  fix st e1 e2 b
  assume "no_whilesR c"
  and a1: "no_whilesR e1" "\<forall>x. e1 %: x \<Down> ceval_fun_no_while x e1"
  and a2: "no_whilesR e2" "\<forall>x. e2 %: x \<Down> ceval_fun_no_while x e2"
  show "\<forall>x. IF b THEN e1 ELSE e2 FI %: x \<Down> ceval_fun_no_while x (IF b THEN e1 ELSE e2 FI)"
    apply (auto)
    apply (rule E_IfTrue, simp, simp add: a1(2))
    apply (rule E_IfFalse, simp, simp add: a2(2))
    done
qed (auto)


subsection {* Additional Exercises *}

(* Exercise: 3 stars (stack_compiler) *)

datatype sinstr = SPush nat | SLoad id | SPlus | SMinus | SMult

fun s_execute :: "state \<Rightarrow> nat list \<Rightarrow> sinstr list \<Rightarrow> nat list" where
  "s_execute st l [] = l"
  | "s_execute st l ((SPush n) # xs) = s_execute st (n # l) xs"
  | "s_execute st l ((SLoad x) # xs) = s_execute st (st x # l) xs"
  | "s_execute st [] (SPlus # xs) = s_execute st [] xs"
  | "s_execute st [y] (SPlus # xs) = s_execute st [y] xs"
  | "s_execute st (y1 # y2 # ys) (SPlus # xs) = s_execute st ((y2 + y1) # ys) xs"
  | "s_execute st [] (SMinus # xs) = s_execute st [] xs"
  | "s_execute st [y] (SMinus # xs) = s_execute st [y] xs"
  | "s_execute st (y1 # y2 # ys) (SMinus # xs) = s_execute st ((y2 - y1) # ys) xs"
  | "s_execute st [] (SMult # xs) = s_execute st [] xs"
  | "s_execute st [y] (SMult # xs) = s_execute st [y] xs"
  | "s_execute st (y1 # y2 # ys) (SMult # xs) = s_execute st ((y2 * y1) # ys) xs"

lemma s_execute1: "s_execute empty_state [] [SPush 5, SPush 3, SPush 1, SMinus] = [2,5]"
by simp

lemma s_execute2: "s_execute (update empty_state X 3) [3,4] [SPush 4, SLoad X, SMult, SPlus] = [15, 4]"
by simp

fun s_compile :: "aexp3 \<Rightarrow> sinstr list" where
  "s_compile (ANum n) = [SPush n]"
  | "s_compile (AId x) = [SLoad x]"
  | "s_compile (APlus y1 y2) = s_compile y1 @ s_compile y2 @ [SPlus]"
  | "s_compile (AMinus y1 y2) = s_compile y1 @ s_compile y2 @ [SMinus]"
  | "s_compile (AMult y1 y2) = s_compile y1 @ s_compile y2 @ [SMult]"

lemma s_compile1: "s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y))) = [SLoad X, SPush 2, SLoad Y, SMult, SMinus]"
by simp

(* Exercise: 3 stars, advanced (stack_compiler_correct) *)

lemma s_compile_correct_app: "\<And>st l. s_execute st l (e1 @ e2) = s_execute st (s_execute st l e1) e2"
apply (induct e1, auto)
apply (case_tac a, auto)
apply (case_tac l, auto, case_tac list, auto)
apply (case_tac l, auto, case_tac list, auto)
apply (case_tac l, auto, case_tac list, auto)
done

lemma s_compile_correct': "\<And>st l. s_execute st l (s_compile e) \<equiv> [aeval3 st e] @ l"
apply (induct e, auto) by (auto simp add: s_compile_correct_app)

theorem s_compile_correct: "s_execute st [] (s_compile e) = [aeval3 st e]"
by (simp add: s_compile_correct' [of st "[]"])

(* Exercise: 5 stars, advanced (break_imp) *)
datatype com' = CSkip | CBreak | CAss id aexp3 | CSeq com' com' | CIf bexp3 com' com' | CWhile bexp3 com'

notation
  CSkip ("SKIP'") and
  CBreak ("BREAK'") and
  CAss ("_ ::=' _" [50,50] 90) and
  CSeq (infixr ";;;" 30) and
  CWhile ("WHILE' _ DO _ END" 90) and
  CIf ("IF' _ THEN _ ELSE _ FI" 80)

datatype status = SContinue | SBreak

inductive ceval' :: "com' \<Rightarrow> state \<Rightarrow> status \<Rightarrow> state \<Rightarrow> bool" ("_ %: _ \<Down> _ %: _") where
  E_Skip: "SKIP' %: st \<Down> SContinue %: st"
  | E_Break: "BREAK' %: st \<Down> SBreak %: st"
  | E_Ass: "aeval3 st a1 = n \<Longrightarrow> (x ::=' a1) %: st \<Down> SContinue %: (update st x n)"
  | E_Seq_Break: "c1 %: st \<Down> SBreak %: st' \<Longrightarrow> (c1 ;;; c2) %: st \<Down> SBreak %: st'"
  | E_Seq_Continue: "\<lbrakk> c1 %: st \<Down> SContinue %: st'; c2 %: st' \<Down> s %: st'' \<rbrakk> \<Longrightarrow> (c1 ;;; c2) %: st \<Down> s %: st''"
  | E_IfTrue: "\<lbrakk> beval3 st b = True; c1 %: st \<Down> s %: st' \<rbrakk> \<Longrightarrow> (IF' b THEN c1 ELSE c2 FI) %: st \<Down> s %: st'"
  | E_IfFalse: "\<lbrakk> beval3 st b = False; c2 %: st \<Down> s %: st' \<rbrakk> \<Longrightarrow> (IF' b THEN c1 ELSE c2 FI) %: st \<Down> s %: st'"
  | E_WhileEnd: "beval3 st b = False \<Longrightarrow> (WHILE' b DO c END) %: st \<Down> SContinue %: st"
  | E_WhileLoop_Break: "\<lbrakk> beval3 st b = True; c %: st \<Down> SBreak %: st' \<rbrakk> \<Longrightarrow> (WHILE' b DO c END) %: st \<Down> SContinue %: st''"
  | E_WhileLoop_Continue: "\<lbrakk> beval3 st b = True; c %: st \<Down> SContinue %: st'; (WHILE' b DO c END) %: st' \<Down> SContinue %: st'' \<rbrakk>
      \<Longrightarrow> (WHILE' b DO c END) %: st \<Down> SContinue %: st''"

theorem break_ignore: "(BREAK' ;;; c) %: st \<Down> s %: st' \<Longrightarrow> st = st'"
apply (induct c)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
  apply (erule ceval'.cases, auto)
done

theorem while_continue: "WHILE' b DO c END %: st \<Down> s %: st' \<Longrightarrow> s = SContinue"
by (erule ceval'.cases, auto)

theorem while_stops_on_break: "\<lbrakk> beval3 st b; c %: st \<Down> SBreak %: st' \<rbrakk> \<Longrightarrow> WHILE' b DO c END %: st \<Down> SContinue %: st'"
by (rule E_WhileLoop_Break, auto)

(*
(* Exercise: 3 stars, advanced, optional (while_break_true) *)
theorem while_break_true: "\<lbrakk> WHILE' b DO c END %: st \<Down> SContinue %: st'; beval3 st' b \<rbrakk>
  \<Longrightarrow> \<exists>st''. (c %: st'' \<Down> SBreak %: st')"
sorry

(* Exercise: 4 stars, advanced, optional (ceval_deterministic) *)
theorem ceval'_deterministic: "\<lbrakk> c %: st \<Down> s1 %: st1; c %: st \<Down> s2 %: st2 \<rbrakk> \<Longrightarrow> st1 = st2 \<and> s1 = s2"
sorry

(*
counterexample ?

  c = WHILE' bexp3.BTrue DO BREAK' END
  s1 = SContinue
  s2 = SContinue
  st = (\<lambda>x. ?)(i\<^sub>1 := 2, i\<^sub>2 := 3)
  st1 = (\<lambda>x. ?)(i\<^sub>1 := 2, i\<^sub>2 := 2)
  st2 = (\<lambda>x. ?)(i\<^sub>1 := 2, i\<^sub>2 := 3)
*)

*)

(* Exercise: 3 stars, optional (short_circuit) *)
fun beval3_shortcircuit :: "state \<Rightarrow> bexp3 \<Rightarrow> bool" where
  "beval3_shortcircuit st BTrue = True"
  | "beval3_shortcircuit st BFalse = False"
  | "beval3_shortcircuit st (BEq a1 a2) = (aeval3 st a1 = aeval3 st a2)"
  | "beval3_shortcircuit st (BLe a1 a2) = (aeval3 st a1 \<le> aeval3 st a2)"
  | "beval3_shortcircuit st (BNot b1) = (\<not> beval3_shortcircuit st b1)"
  | "beval3_shortcircuit st (BAnd b1 b2) = (if beval3_shortcircuit st b1 then beval3_shortcircuit st b2 else False)"

theorem short_circuit: "beval3 st b = beval3_shortcircuit st b"
by (induct b, auto)

(* Exercise: 4 stars, optional (add_for_loop) *)
(* Omitted *)

end

