theory MoreCoq
imports Main
begin

section {* MoreCoq *}
subsection {* The apply Tactic *}

theorem silly1: "\<forall>n m l p. n = m \<longrightarrow> [n,l] = [n,p] \<longrightarrow> [n,l] = [m,p]"
by simp

theorem silly2: "\<forall>n m l p. n = m \<longrightarrow> (\<forall>q r. q = r \<longrightarrow> [q,l] = [r,p]) \<longrightarrow> [n,l] = [m,p]"
by simp

theorem silly2a: "\<forall>n m. (n,n) = (m,m) \<longrightarrow> (\<forall>q r. (q,q) = (r,r) \<longrightarrow> [q] = [r]) \<longrightarrow> [n] = [m]"
by simp

(* Exercise: 2 stars, optional (silly_ex) *)

fun evenb where "evenb n = (n mod 2 = 0)"
fun oddb where "oddb n = (n mod 2 = 1)"

theorem silly_ex: "(\<forall>(n :: nat). evenb n = True \<longrightarrow> oddb (Suc n) = True) \<longrightarrow> evenb (3 :: nat) = True \<longrightarrow> oddb 4 = True" by simp
theorem silly3_firsttry: "\<forall>(n :: nat). True = (n = 5) \<longrightarrow> (Suc (Suc n)) = 7 = True" by simp
theorem silly3: "\<forall>(n :: nat). True = (n = 5) \<longrightarrow> (Suc (Suc n)) = 7 = True" by simp

(* Exercise: 3 stars (apply_exercise1) *)

theorem rev_exercise1: "\<forall>l l' :: nat list. l = rev l' \<longrightarrow> l' = rev l" by simp

(* Exercise: 1 star, optional (apply_rewrite) *)

subsection {* The apply ... with ... Tactic *}

lemma trans_eq_example: "\<forall>a b c d e f :: nat. [a,b] = [c,d] \<longrightarrow> [c,d] = [e,f] \<longrightarrow> [a,b] = [e,f]" by simp
theorem trans_eq: "\<forall>n m o'. n = m \<longrightarrow> m = o' \<longrightarrow> n = o'" by simp
lemma trans_eq_example': "\<forall>a b c d e f :: nat. [a,b] = [c,d] \<longrightarrow> [c,d] = [e,f] \<longrightarrow> [a,b] = [e,f]"
by auto

(* Exercise: 3 stars, optional (apply_with_exercise) *)

fun minustwo where "minustwo n = n - 2"
lemma trans_eq_exercise: "\<forall>n m o' p :: nat. m = (minustwo o') \<longrightarrow> (n + p) = m \<longrightarrow> (n + p) = (minustwo o')" by simp

subsection {* The inversion tactic *}

theorem eq_add_S: "\<forall>n m :: nat. Suc n = Suc m \<longrightarrow> n = m" by simp
theorem silly4: "\<forall>n m :: nat. [n] = [m] \<longrightarrow> n = m" by simp
theorem silly5: "\<forall>n m o' :: nat. [n,m] = [o',o'] \<longrightarrow> [n] = [m]" by simp

(* cut *)

end

