theory Basics
imports Main
begin

section {* Basics *}
subsection {* Enumerated Types *}
subsubsection {* Days of the Week *}

datatype day =
  monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

definition next_weekday :: "day \<Rightarrow> day" where
  "next_weekday d \<equiv> case d of
    monday \<Rightarrow> tuesday
    | tuesday \<Rightarrow> wednesday
    | wednesday \<Rightarrow> thursday
    | friday \<Rightarrow> monday
    | saturday \<Rightarrow> monday
    | sunday \<Rightarrow> monday"

value "next_weekday friday"
  (* \<Longrightarrow> "monday" :: "day" *)
value "next_weekday (next_weekday saturday)"
  (* \<Longrightarrow> "tuesday" :: "day" *)

lemma test_next_weekday:
  "(next_weekday (next_weekday saturday)) = tuesday"
using next_weekday_def by simp

subsubsection {* Booleans *}

datatype bool = true | false

fun negb :: "bool \<Rightarrow> bool" where
  "negb true = false"
  | "negb false = true"

fun andb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "andb true b2 = b2"
  | "andb false _ = false"

fun orb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "orb true _ = true"
  | "orb false b2 = b2"

lemma test_orb1: "(orb true false) = true" by simp
lemma test_orb2: "(orb false false) = false" by simp
lemma test_orb3: "(orb false true) = true" by simp
lemma test_orb4: "(orb true true) = true" by simp

(* Exercise: 1 star (nandb) *)

fun nandb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "nandb true b2 = negb b2"
  | "nandb false _ = true"

lemma test_nandb1: "(nandb true false) = true" by simp
lemma test_nandb2: "(nandb false false) = true" by simp
lemma test_nandb3: "(nandb false true) = true" by simp
lemma test_nandb4: "(nandb true true) = false" by simp

(* Exercise: 1 star (andb3) *)

fun andb3 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "andb3 b1 b2 b3 = andb b1 (andb b2 b3)"

lemma test_andb31: "(andb3 true true true) = true" by simp
lemma test_andb32: "(andb3 false true true) = false" by simp
lemma test_andb33: "(andb3 true false true) = false" by simp
lemma test_andb34: "(andb3 true true false) = false" by simp

subsubsection {* Function Types *}

value "true"
  (* \<Longrightarrow> "true" :: "Basics.bool" *)
value "negb true"
  (* \<Longrightarrow> "false" :: "Basics.bool" *)
value "negb"
  (* \<Longrightarrow> "_" :: "Basics.bool \<Rightarrow> Basics.bool"*)

subsubsection {* Numbers *}

datatype nat = zero | suc nat

fun pred :: "nat \<Rightarrow> nat" where
  "pred zero = zero"
  | "pred (suc n') = n'"

fun minustwo :: "nat \<Rightarrow> nat" where
  "minustwo zero = zero"
  | "minustwo (suc zero) = zero"
  | "minustwo (suc (suc n')) = n'"

value "suc (suc (suc (suc zero)))"
  (* \<Longrightarrow> "suc (suc (suc (suc zero)))" :: "Basics.nat" *)
value "minustwo (suc (suc (suc (suc zero))))"
  (* \<Longrightarrow> "suc (suc zero)" :: "Basics.nat" *)

value "suc"
  (* \<Longrightarrow> "_" :: "Basics.nat \<Rightarrow> Basics.nat" *)
value "pred"
  (* \<Longrightarrow> "_" :: "Basics.nat \<Rightarrow> Basics.nat" *)
value "minustwo"
  (* \<Longrightarrow> "_" :: "Basics.nat \<Rightarrow> Basics.nat" *)

fun evenb :: "nat \<Rightarrow> bool" where
  "evenb zero = true"
  | "evenb (suc zero) = false"
  | "evenb (suc (suc b)) = evenb b"

fun oddb where "oddb n = negb (evenb n)"

lemma test_oddb1: "(oddb (suc zero)) = true" by simp
lemma test_oddb2: "(oddb (suc (suc (suc (suc zero))))) = false" by simp

fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus zero m = m"
  | "plus (suc n') m = suc (plus n' m)"

value "plus (suc (suc (suc zero))) (suc (suc zero))"
  (* \<Longrightarrow> "suc (suc (suc (suc (suc zero))))" :: "Basics.nat" *)

fun mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mult zero m = zero"
  | "mult (suc n') m = plus m (mult n' m)"

(* test_mult1: "3 * 3 = 9" *)
lemma test_mult1:
  "mult (suc (suc (suc zero))) (suc (suc (suc zero))) = (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))"
by simp

fun minus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "minus zero _ = zero"
  | "minus (suc n) zero = suc n"
  | "minus (suc n) (suc m) = minus n m"

fun exp :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "exp base zero = suc zero"
  | "exp base (suc p) = mult base (exp base p)"

(* Exercise: 1 star (factorial) *)

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial zero = suc zero"
  | "factorial (suc n) = mult (suc n) (factorial n)"

lemma test_factorial1: "(factorial (suc (suc (suc zero)))) = suc (suc (suc (suc (suc (suc zero)))))" by simp
(* Example test_factorial2: (factorial 5) = (mult 10 12) *)

no_notation
  Groups.plus (infixl "+" 65) and
  Product_Type.Times (infixr "\<times>" 80)

notation
  plus (infixl "+" 65) and
  minus (infixl "-" 65) and
  mult (infixl "\<times>" 80)

value "(zero + suc zero) + suc zero"
  (* \<Longrightarrow> "suc (suc zero)" :: "Basics.nat" *)

fun beq_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "beq_nat zero zero = true"
  | "beq_nat zero (suc m) = false"
  | "beq_nat (suc n) zero = false"
  | "beq_nat (suc n) (suc m) = beq_nat n m"

fun ble_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ble_nat zero _ = true"
  | "ble_nat (suc n) zero = false"
  | "ble_nat (suc n) (suc m) = ble_nat n m"

lemma test_ble_nat1: "ble_nat (suc (suc zero)) (suc (suc zero)) = true" by simp
lemma test_ble_nat2: "ble_nat (suc (suc zero)) (suc (suc (suc (suc zero)))) = true" by simp
lemma test_ble_nat3: "ble_nat (suc (suc (suc (suc zero)))) (suc (suc zero)) = false" by simp

(* Exercise: 2 stars (blt_nat) *)

fun blt_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "blt_nat n m = andb (ble_nat n m) (negb (beq_nat n m))"

lemma test_blt_nat1: "blt_nat (suc (suc zero)) (suc (suc zero)) = false" by simp
lemma test_blt_nat2: "blt_nat (suc (suc zero)) (suc (suc (suc (suc zero)))) = true" by simp
lemma test_blt_nat3: "blt_nat (suc (suc (suc (suc zero)))) (suc (suc zero)) = false" by simp

subsection {* Proof by Simplification *}

theorem plus_O_n: "\<forall>(n :: nat). zero + n = n" by simp
theorem plus_1_l: "\<forall>(n :: nat). (suc zero) + n = suc n" by simp
theorem mult_0_l: "\<forall>(n :: nat). zero \<times> n = zero" by simp

subsection {* Proof by Rewriting *}

theorem plus_id_example: "\<forall>n m :: nat. n = m \<longrightarrow> n + n = m + m" by simp

(* Exercise: 1 star (plus_id_exercise) *)

theorem plus_id_exercise: "\<forall>n m l :: nat. n = m \<longrightarrow> m = l \<longrightarrow> n + m = m + l" by simp
theorem mult_0_plus: "\<forall>n m :: nat. (zero + n) \<times> m = n \<times> m" by simp

(* Exercise: 2 stars (mult_S_1) *)

theorem mult_S_1: "\<forall>n m :: nat. m = suc n \<longrightarrow> m \<times> (suc zero + n) = m \<times> m" by simp

subsection {* Proof by Case Analysis *}

theorem plus_1_neq_0: "\<forall>n :: nat. beq_nat (n + suc zero) zero = false"
apply (rule allI) by (case_tac n, simp, simp)

theorem negb_involutive: "\<forall>b :: bool. negb (negb b) = b"
apply (rule allI) by (case_tac b, simp, simp)

(* Exercise: 1 star (zero_nbeq_plus_1) *)

theorem zero_nbeq_plus_1: "\<forall>n :: nat. beq_nat zero (n + suc zero) = false"
apply (rule allI) by (case_tac n, simp, simp)

subsection {* More Exercises *}

(* Exercise: 2 stars (boolean functions) *)

theorem identity_fn_applied_twice:
  "\<forall>(f :: bool \<Rightarrow> bool). (\<forall>(x :: bool). f x = x) \<longrightarrow> (\<forall>(b :: bool). f (f b) = b)"
by simp

theorem negation_fn_applied_twice:
  "\<forall>(f :: bool \<Rightarrow> bool). (\<forall>(x :: bool). f x = negb x) \<longrightarrow> (\<forall>(b :: bool). f (f b) = b)"
apply auto by (case_tac b, simp, simp)

(* Exercise: 2 stars (andb_eq_orb) *)

theorem andb_eq_orb: "\<forall>b c :: bool. (andb b c = orb b c) \<longrightarrow> b = c"
apply auto by (case_tac b, simp, simp)

(* Exercise: 3 stars (binary) *)

datatype bin = zero | twice bin | twice_one bin

fun incr :: "bin \<Rightarrow> bin" where
  "incr bin.zero = twice_one bin.zero"
  | "incr (twice n) = twice_one n"
  | "incr (twice_one n) = twice (incr n)"

fun double :: "nat \<Rightarrow> nat" where
  "double nat.zero = nat.zero"
  | "double (suc n) = suc (suc (double n))"

fun bin_nat :: "bin \<Rightarrow> nat" where
  "bin_nat bin.zero = nat.zero"
  | "bin_nat (twice n) = double (bin_nat n)"
  | "bin_nat (twice_one n) = suc (double (bin_nat n))"

lemma incr_nat_comm: "\<forall>b :: bin. bin_nat (incr b) = suc (bin_nat b)"
apply auto by (induct_tac b, auto)

subsection {* Optional Material *}

subsubsection {* More on Notation *}
subsubsection {* Fixpoints and Structural Recursion *}

end
