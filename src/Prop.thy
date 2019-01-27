theory Prop
  imports Main
begin

section {* Prop *}
subsection {* From Boolean Functions to Propositions *}

(* abbreviation "even n \<equiv> (n mod 2 = 0)" *)

subsection {* Inductively Defined Propositions *}

inductive ev where
  ev_0: "ev 0"
  | ev_SS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

(* Exercise: 1 star (double_even) *)

fun double where
  "double n = n + n"
theorem double_even: "\<forall>n. ev (double n)"
apply auto by (induct_tac n, simp, rule ev_0, simp, rule ev_SS, simp)

subsubsection {* Discussion: Computational vs. Inductive Definitions *}

(* Exercise: 1 star (ev__even) *)

theorem ev_even: "\<forall>n :: nat. ev n \<longrightarrow> even n"
apply auto by (erule ev.induct, auto)

(* Exercise: 1 star (l_fails) *)
(* Exercise: 2 stars (ev_sum) *)

theorem ev_sum: "\<forall>n m. ev n \<longrightarrow> ev m \<longrightarrow> ev (n+m)"
apply auto by (erule ev.induct, auto simp add: ev_SS)

subsubsection {* Example *}
subsubsection {* Inference Rules *}

(* Exercise: 1 star (varieties_of_beauty) *)

inductive beautiful :: "nat \<Rightarrow> bool" where
  b_0: "beautiful 0"
  | b_3: "beautiful 3"
  | b_5: "beautiful 5"
  | b_sum: "\<lbrakk> beautiful n; beautiful m \<rbrakk> \<Longrightarrow> beautiful (n + m)"

theorem three_is_beautiful: "beautiful 3" using b_3 by simp
theorem eight_is_beautiful: "beautiful 8" using beautiful.b_sum [of 3 5] b_3 b_5 by simp
theorem beautiful_plus_eight: "\<forall>n. beautiful n \<longrightarrow> beautiful (8 + n)"
apply auto by (rule, auto simp add: eight_is_beautiful)

(* Exercise: 2 stars (b_times2) *)
theorem b_times2: "\<forall>n. beautiful n \<longrightarrow> beautiful (2 * n)" by (simp add: mult_2 b_sum)

(* Exercise: 3 stars (b_timesm) *)
theorem b_timesm: "\<forall>n m. beautiful n \<longrightarrow> beautiful (m * n)"
apply auto by (induct_tac m, auto simp add: b_0 b_sum)

subsubsection {* Induction Over Evidence *}

inductive gorgeous :: "nat \<Rightarrow> bool" where
  g_0: "gorgeous 0"
  | g_plus3: "gorgeous n \<Longrightarrow> gorgeous (3+n)"
  | g_plus5: "gorgeous n \<Longrightarrow> gorgeous (5+n)"

(* Exercise: 1 star (gorgeous_tree) *)
(* Exercise: 1 star (gorgeous_plus13) *)

theorem gorgeous_plus13: "\<forall>n :: nat. gorgeous n \<longrightarrow> gorgeous (13+n)"
proof auto
  fix n :: nat assume "gorgeous n"
  hence "gorgeous (3 + n)" using g_plus3 by simp
  hence "gorgeous (8 + n)" using g_plus5 [of "3 + n"] by simp
  thus "gorgeous (13 + n)" using g_plus5 [of "8 + n"] by simp
qed

theorem gorgeous_beautiful: "\<forall>n :: nat. gorgeous n \<longrightarrow> beautiful n"
apply auto by (erule gorgeous.induct, auto simp add: b_0 b_3 b_5 b_sum)

(* Exercise: 2 stars (gorgeous_sum) *)

theorem gorgeous_sum: "\<forall>n m :: nat. gorgeous n \<longrightarrow> gorgeous m \<longrightarrow> gorgeous (n + m)"
apply auto apply (erule gorgeous.induct, simp)
apply (fastforce simp add: add.assoc g_plus3)
apply (fastforce simp add: add.assoc g_plus5)
done

(* Exercise: 3 stars, advanced (beautiful__gorgeous) *)

theorem beautiful_gorgeous: "\<forall>n :: nat. beautiful n \<longrightarrow> gorgeous n"
apply auto apply (erule beautiful.induct, rule)
using g_plus3 [OF g_0] apply simp
using g_plus5 [OF g_0] apply simp
apply (simp add: gorgeous_sum)
done

(* Exercise: 3 stars, optional (g_times2) *)

lemma helper_g_times2: "\<forall>x y z :: nat. x + (z + y) = z + x + y" by simp

theorem g_times2: "\<forall>n. gorgeous n \<longrightarrow> gorgeous (2 * n)"
by (auto simp add: mult_2 gorgeous_sum)

subsubsection {* Inversion on Evidence *}

fun pred :: "nat \<Rightarrow> nat" where
  "pred 0 = 0"
  | "pred (Suc n) = n"

theorem ev_minus2: "\<forall>n. ev n \<longrightarrow> ev (pred (pred n))"
apply auto by (erule ev.induct, auto simp add: ev_0)

(* Exercise: 1 star, optional (ev_minus2_n) *)

theorem SSev_even: "ev (Suc (Suc n)) \<Longrightarrow> ev n"
using ev_minus2 by fastforce

subsubsection {* inversion revisited *}

(* Exercise: 1 star (inversion_practice) *)
theorem SSSSev_even: "\<forall>n. ev (Suc (Suc (Suc (Suc n)))) \<longrightarrow> ev n"
using SSev_even by fastforce

theorem even5_nonsense: "ev 5 \<longrightarrow> 2 + 2 = 9"
using SSSSev_even apply simp
using One_nat_def ev.simps
by (metis inc.simps Suc_eq_numeral Suc_numeral add_One numeral_One old.nat.distinct(2))

(* Exercise: 3 stars, advanced (ev_ev__ev) *)
lemma ev_in: "ev n \<Longrightarrow> n mod 2 = 0"
by (erule ev.inducts, simp add: ev.simps, simp)

lemma ev_destruct: "ev n \<Longrightarrow> n = 0 \<or> (\<exists>m. n = Suc (Suc m) \<and> ev m)"
  apply (induct rule: ev.induct, simp, simp)
  done

theorem ev_ev_ev: "ev n \<Longrightarrow> ev (n+m) \<Longrightarrow> ev m"
  apply (induct rule: ev.induct, simp, simp)
  using SSev_even by blast

(* Exercise: 3 stars, optional (ev_plus_plus) *)
theorem ev_plus_plus : "\<forall>n m p. ev (n+m) \<longrightarrow> ev (n+p) \<longrightarrow> ev (m+p)"
apply auto
apply (erule_tac ev.cases, auto)
proof -
  fix n :: nat and m :: nat and p :: nat and na :: nat
  assume a1: "ev (n + p)"
  assume a2: "n + m = Suc (Suc na)"
  assume a3: "ev na"
  have "\<And>x\<^sub>1. ev (x\<^sub>1 + x\<^sub>1)" using double_even by auto
  hence "\<And>x\<^sub>1. ev (x\<^sub>1 + (n + (x\<^sub>1 + p)))" using a1 by (metis (no_types) ev_ev_ev helper_g_times2)
  thus "ev (m + p)" using a2 a3 by (metis ev.ev_SS ev_ev_ev helper_g_times2)
qed

subsection {* Additional Exercises *}

(* Exercise: 4 stars (palindromes) *)
inductive_set pal :: "('a list) set" where
  pal_nil: "[] \<in> pal"
  | pal_singleton: "[x] \<in> pal"
  | pal_cons: "l \<in> pal \<Longrightarrow> x # (l @ [x]) \<in> pal"

theorem pal_app: "(l @ rev l) \<in> pal"
proof (induct_tac l, auto, rule pal_nil)
  fix a and list :: "'a list"
  assume "list @ rev list \<in> pal"
  thus "a # list @ rev list @ [a] \<in> pal"
    using pal_cons [of "list @ rev list" a] by auto
qed

theorem pal_palindrome: "l \<in> pal \<Longrightarrow> l = rev l"
apply (erule pal.cases)
apply (simp, simp)
proof simp
  fix l :: "'a list" and la x assume "l = x # la @ [x]" "la \<in> pal"
  show "la = rev la"
    by (rule pal.inducts [OF `la \<in> pal`], auto)
qed

(* Exercise: 5 stars, optional (palindrome_converse) *)
lemma nat_inducts_all:
  "\<And>P n. P 0 \<Longrightarrow> (\<And>n :: nat. (\<And>m :: nat. m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n"
proof-
  fix P and n :: nat
  assume a: "P 0" "\<And>n :: nat. (\<And>m :: nat. m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)"
  show "P n"
    proof (rule nat_less_induct)
      fix na
      assume a2: "\<forall>m<na. P m"
      show "P na"
        apply (cases na, simp, rule a(1), simp, rule a(2))
        using a2 by simp
    qed
qed

lemma induct_by_length:
  fixes l :: "'a list"
  assumes P_0: "P []"
  and P_step: "\<And>l n. length l = Suc n \<Longrightarrow> (\<And>la. length la \<le> n \<Longrightarrow> P la) \<Longrightarrow> P l"
  shows "P l"
using nat_inducts_all [of "\<lambda>k. \<forall>l. length l = k \<longrightarrow> P l"] apply rule
proof (simp, rule P_0, auto)
  fix n and x :: "'a list"
  assume h: "\<And>m. m \<le> n \<Longrightarrow> \<forall>x. length x = m \<longrightarrow> P x" "length x = Suc n"
  hence "\<And>la. length la \<le> n \<Longrightarrow> P la" by simp
  thus "P x" using P_step [OF h(2)] by simp
qed

theorem palindrome_converse: "l = rev l \<Longrightarrow> l \<in> pal"
using induct_by_length [of "\<lambda>l. l = rev l \<longrightarrow> l \<in> pal"] apply rule
proof (auto, rule)
  fix la :: "'a list" and n
  assume "l = rev l"
  and a: "length la = Suc n" "\<And>la :: 'a list. length la \<le> n \<Longrightarrow> la = rev la \<longrightarrow> la \<in> pal" "la = rev la"
  from a(1) obtain x xs where xxs: "la = x # xs" using neq_Nil_conv [of la] by auto
  from a(3) have 1: "last la = x" using xxs by simp

  have 2: "(la = [x]) \<or> (\<exists>ys. la = x # ys @ [x])"
    using xxs 1 by (metis append_Cons append_butlast_last_id butlast.simps(2) list.distinct(1))

  have "la = [x] \<Longrightarrow> la \<in> pal"
    by (simp, rule)
  moreover have "\<exists>ys. la = x # ys @ [x] \<Longrightarrow> la \<in> pal"
    proof-
      assume "\<exists>ys. la = x # ys @ [x]"
      then obtain ys where ys: "la = x # ys @ [x]" by auto
      have "rev ys = ys" using a(3) by (simp add: ys)
      have "length ys \<le> n"
        using a(1) by (simp add: ys)
      thus "la \<in> pal"
        using a(2) [OF `length ys \<le> n`]
        by (simp add: `rev ys = ys` ys, rule_tac pal_cons, simp)
    qed
  ultimately
    show "la \<in> pal" by (metis 2)
qed

fun init where
  "init [] = []"
  | "init [x] = []"
  | "init (x # xs) = x # init xs"

lemma init_length: "\<And>x. length (init (x # xs)) = length xs"
by (induct xs, simp, simp)

fun cut1 where
  "cut1 [] = []"
  | "cut1 [x] = []"
  | "cut1 xs = init (tl xs)"

lemma cut1_length: "length l \<le> Suc n \<Longrightarrow> length (cut1 l) \<le> n"
apply (rule cut1.cases [of l], simp, simp, simp)
by (simp add: init_length)

lemma cut1_head_last: "cut1 (x # l @ [x]) = l"
proof-
  have "cut1 (x # l @ [x]) = init (l @ [x])" by (cases l, auto)
  also have "\<dots> = l"
    proof (induct l, auto)
      fix a l
      assume a: "init (l @ [x]) = l"
      have 1: "l @ [x] = hd (l @ [x]) # tl (l @ [x])" by (cases l, auto)
      hence "init (a # l @ [x]) = a # init (l @ [x])"
        using init.simps(3) [of a "hd (l @ [x])" "tl (l @ [x])"] by simp
      thus "init (a # l @ [x]) = a # l"
        by (simp add: a)
    qed
  finally show ?thesis by simp
qed

lemma rev_cut1': "l \<in> pal \<Longrightarrow> cut1 l = rev (cut1 l)"
using induct_by_length [of "\<lambda>l. l \<in> pal \<longrightarrow> cut1 l = rev (cut1 l)"] apply rule
proof auto
  fix la :: "'a list" and n
  assume "l \<in> pal"
  and a: "length la = Suc n" "(\<And>la :: 'a list. length la \<le> n \<Longrightarrow> la \<in> pal \<longrightarrow> cut1 la = rev (cut1 la))" "la \<in> pal"
  have 1: "(\<exists>x. la = [x]) \<or> (\<exists>x xs. la = x # xs @ [x])"
    apply (rule pal.cases [OF a(3)])
    using a(1) by auto

  have "(\<exists>x. la = [x]) \<Longrightarrow> cut1 la = rev (cut1 la)" by auto
  moreover have "(\<exists>x xs. la = x # xs @ [x]) \<Longrightarrow> cut1 la = rev (cut1 la)"
    proof-
      assume "\<exists>x xs. la = x # xs @ [x]"
      then obtain x xs where xxs: "la = x # xs @ [x]" by auto
      have 1: "xs \<in> pal"
        apply (rule pal.cases [OF a(3)])
        using a(1) xxs by auto
      show ?thesis
        by (simp add: xxs cut1_head_last, rule pal_palindrome, rule 1)
    qed
  ultimately
    show "cut1 la = rev (cut1 la)" using 1 by auto
qed

lemma rev_cut1: "l = rev l \<Longrightarrow> cut1 l = rev (cut1 l)"
by (rule rev_cut1', simp add: palindrome_converse)

lemma cut_append: "\<And>x l2. \<lbrakk> l = x # l2; l2 \<noteq> [] \<rbrakk> \<Longrightarrow> hd l # (cut1 l) @ [last l] = l"
apply (induct l, auto) by (fastforce simp add: neq_Nil_conv)

lemma rev_pal_length: "\<And>l. \<lbrakk> length l \<le> n; l = rev l \<rbrakk> \<Longrightarrow> l \<in> pal"
proof (induct n, simp, rule pal_nil)
  fix n and l :: "'a list"
  assume hyp: "(\<And>(l :: 'a list). length l \<le> n \<Longrightarrow> l = rev l \<Longrightarrow> l \<in> pal)" and "length l \<le> Suc n" "l = rev l"
  have "l = [] \<Longrightarrow> l \<in> pal" by (simp, rule pal_nil)
  moreover have "\<And>x. l = [x] \<Longrightarrow> l \<in> pal" by (simp, rule pal_singleton)
  moreover have "\<And>x l2. \<lbrakk> l = x # l2; l2 \<noteq> [] \<rbrakk> \<Longrightarrow> l \<in> pal"
    proof -
      fix x l2
      assume "l = x # l2" "l2 \<noteq> []"
      have "length (cut1 l) \<le> n" using cut1_length [OF `length l \<le> Suc n`] by simp
      moreover have "cut1 l = rev (cut1 l)" using rev_cut1 [OF `l = rev l`] by simp
      ultimately
        have "cut1 l \<in> pal" using hyp [of "cut1 l"] by simp
        moreover have "hd l = last l"
          using `l = rev l` apply (subst last_rev [symmetric]) by (auto simp add: `l = x # l2`)
        ultimately
          have "hd l # cut1 l @ [last l] \<in> pal" using pal_cons by simp
          moreover have "l = hd l # cut1 l @ [last l]" using cut_append [OF `l = x # l2` `l2 \<noteq> []`] by simp
          ultimately show "l \<in> pal" by simp
    qed
  ultimately show "l \<in> pal" by (metis list.exhaust)
qed

theorem pal_converse: "l = rev l \<Longrightarrow> l \<in> pal"
using rev_pal_length [of l "length l"] by simp

(* Exercise: 4 stars, advanced (subsequence) *)
inductive subseq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  subseq_nil: "subseq [] []"
  | subseq_cons: "subseq xs ys \<Longrightarrow> subseq xs (y # ys)"
  | subseq_cons_both: "subseq xs ys \<Longrightarrow> subseq (x # xs) (x # ys)"

abbreviation is_subseq_of ("_ {subseq of} _") where
  "is_subseq_of xs ys \<equiv> subseq xs ys"

theorem subseq_reflexive: "subseq xs xs"
apply (induct xs) by (rule subseq_nil, rule subseq_cons_both, simp)

lemma subseq_empty: "[] {subseq of} xs"
apply (induct xs) by (rule subseq_nil, rule subseq_cons, simp)

lemma subseq_app': "ys {subseq of} xs \<Longrightarrow> ys {subseq of} (xs' @ xs)"
apply (induct xs') by (simp, simp, rule subseq_cons, simp)

theorem subseq_app: "\<lbrakk> l1 {subseq of} l2; l1 {subseq of} l3 \<rbrakk> \<Longrightarrow> l1 {subseq of} (l2 @ l3)"
by (auto simp add: subseq_app')

lemma subseq_empty_of: "xs {subseq of} [] \<Longrightarrow> xs = []"
by (erule subseq.cases, simp+)

(*
lemma subseq_split_l:
  "l1 {subseq of} (l2 @ l3) \<Longrightarrow> \<exists>l4. \<exists>l5. (l4 {subseq of} l2) & (l5 {subseq of} l3) & (l1 = l4 @ l5)"
sorry

theorem subseq_trans: "\<And>l1 l3. \<lbrakk> l1 {subseq of} l2; l2 {subseq of} l3 \<rbrakk> \<Longrightarrow> l1 {subseq of} l3"
apply (induct l2)
  using subseq_empty_of apply fastforce
proof -
  fix a l2 l1 l3
  assume hyp: "\<And>l1 l3 :: 'a list. l1 {subseq of} l2 \<Longrightarrow> l2 {subseq of} l3 \<Longrightarrow> l1 {subseq of} l3"
  and 1: "l1 {subseq of} (a # l2)" "(a # l2) {subseq of} l3"
  obtain l4 l5 where
    l45: "l4 {subseq of} [a]" "l5 {subseq of} l2" "l1 = l4 @ l5"
    using subseq_split_l [of l1 "[a]" l2] by (fastforce simp add: 1(1))
  have "l5 {subseq of} l3"
    using hyp [OF l45(2)]

  show "l1 {subseq of} l3"
*)

(* Exercise: 2 stars, optional (R_provability) *)
inductive R where
  c1: "R 0 []"
  | c2: "R n l \<Longrightarrow> R (Suc n) (n # l)"
  | c3: "R (Suc n) l \<Longrightarrow> R n l"

lemma R_2: "R 2 [1,0]"
by (metis (no_types) One_nat_def R.simps Suc_1)

lemma R_1: "R 1 [1,2,1,0]"
by (metis R_2 Suc_1 c2 c3)

(*
"R 6 [3,2,1,0] \<Longrightarrow> False"
unprovable
*)

subsection {* Relations *}

inductive le :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  le_n: "le n n"
  | le_S: "le n m \<Longrightarrow> le n (Suc m)"

theorem test_le1: "le 3 3" by (rule le_n)
theorem test_le2: "le 3 6"
proof -
  have "le 3 (Suc (Suc (Suc 3)))" by (rule le_S, rule le_S, rule le_S, rule le_n)
  thus ?thesis by simp
qed

theorem test_le3: "le 2 1 \<Longrightarrow> 2 + 2 = 5"
proof -
  assume "le 2 1" hence "le (Suc 1) 1" by (simp add: numeral_eq_Suc)
  hence False by (metis One_nat_def Suc_eq_numeral le.cases numeral_One old.nat.distinct(2))
  thus "2 + 2 = 5" by meson
qed

fun lt where
  "lt n m = le (Suc n) m"

inductive square_of where
  sq: "square_of n (n * n)"
inductive next_nat where
  nn: "next_nat n (Suc n)"
inductive next_even where
  ne_1: "ev (Suc n) \<Longrightarrow> next_even n (Suc n)"
  | ne_2: "ev (Suc (Suc n)) \<Longrightarrow> next_even n (Suc (Suc n))"

(* Exercise: 2 stars (total_relation) *)
inductive total_relation where
  lt: "n < m \<Longrightarrow> total_relation n m"
  | gte: "n \<ge> m \<Longrightarrow> total_relation n m"

(* Exercise: 2 stars (empty_relation) *)
inductive empty_relation where
  empty_r: "\<lbrakk> n < m; m > n \<rbrakk> \<Longrightarrow> empty_relation n m"

(* Exercise: 2 stars, optional (le_exercises) *)
lemma le_Suc: "le m n \<Longrightarrow> \<exists>a :: nat. n = m + a"
by (rule le.inducts, auto)

lemma Suc_le: "\<And>n. n = m + a \<Longrightarrow> le m n"
apply (induct a, simp, rule le_n) by (simp add: le_S)

lemma le_trans: "\<And>m n o'. le m n \<Longrightarrow> le n o' \<Longrightarrow> le m o'"
proof -
  fix m n o' assume "le m n" "le n o'"
  then obtain a b where "n = m + a" "o' = n + b" by (metis le_Suc)
  thus "le m o'" using Suc_le [of o' m "a + b"] by simp
qed

theorem le_0_n: "le 0 n"
by (induct n, rule le_n, rule le_S, simp)

theorem n_le_m_Sn_le_Sm: "le n m \<Longrightarrow> le (Suc n) (Suc m)"
using Suc_le le_Suc by (metis add_Suc)

theorem Sn_le_Sm_n_le_m: "le (Suc n) (Suc m) \<Longrightarrow> le n m"
using Suc_le le_Suc by (metis Prop.le_trans Prop.pred.simps(2) le.cases le_S le_n)

theorem le_plus_l: "le a (a+b)"
by (induct b, auto, rule, rule, simp)

theorem plus_lt: "le (n1 + n2) m \<Longrightarrow> le n1 m \<and> le n2 m"
using Suc_le le_Suc by (metis Prop.le_trans add.commute)

theorem lt_S: "le n m \<Longrightarrow> le n (Suc m)" by (rule, simp)
theorem ble_nat_true: "n \<le> m \<Longrightarrow> le n m" using Suc_le [of m n "m - n"] by simp
theorem le_ble_nat: "le n m \<Longrightarrow> n \<le> m" using le_Suc [of n m] by fastforce
theorem ble_nat_true_trans: "n = m \<Longrightarrow> m = o' \<Longrightarrow> n = o'" by simp

(* Exercise: 2 stars, optional (ble_nat_false) *)
theorem ble_nat_false: "\<not> (n \<le> m) \<Longrightarrow> \<not> (le n m)" using le_ble_nat by auto

(* Exercise: 3 stars (R_provability2) *)
inductive R' where
  c1: "R' 0 0 0"
  | c2: "R' l m n \<Longrightarrow> R' (Suc l) m (Suc n)"
  | c3: "R' l m n \<Longrightarrow> R' l (Suc m) (Suc n)"
  | c4: "R' (Suc l) (Suc m) (Suc (Suc n)) \<Longrightarrow> R' l m n"
  | c5: "R' l m n \<Longrightarrow> R' m l n"

lemma R'_112: "R' 1 1 2"
by (metis One_nat_def R'.c1 R'.c2 R'.c3 Suc_1)

(*
"R' 2 2 6"
unprovable
*)

(* Exercise: 3 stars, optional (R_fact) *)
fun sum_le where
  "sum_le l m n = ((l + m) = n)"

theorem R'_sumle: "R' l m n \<Longrightarrow> sum_le l m n"
by (erule R'.inducts, auto)

theorem sumle_R': "\<And>m n. sum_le l m n \<Longrightarrow> R' l m n"
proof (induct l, auto)
  fix n show "R' 0 n n"
  by (induct n, rule c1, rule c3, simp)
next
  fix l m n
  assume hyp: "\<And>m n. l + m = n \<Longrightarrow> R' l m n"
  show "R' (Suc l) m (Suc (l + m))" by (rule c2, rule hyp, simp)
qed

subsection {* Programming with Propositions Revisited *}

end

