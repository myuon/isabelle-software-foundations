theory Poly
imports Main
begin

section {* Poly *}
subsection {* Polymorphism *}
subsubsection {* Polymorphic Lists *}

datatype 'a list = nil | cons 'a "'a list"

no_notation
  List.Nil ("[]")

notation
  nil ("[]") and
  cons (infixr ";" 60)

no_syntax
  "_list" :: "args \<Rightarrow> 'a list" ("[(_)]")

syntax
  "_polylist" :: "args \<Rightarrow> 'a list" ("[(_)]")

translations
  "[x; xs]" == "x;[xs]"
  "[x]" == "x;[]"

term "nil"
  (* \<Longrightarrow> "nil" :: "'a Poly.list" *)
term "cons"
  (* \<Longrightarrow> "cons" :: "'a \<Rightarrow> 'a Poly.list \<Rightarrow> 'a Poly.list" *)

value "cons 2 (cons (1 :: nat) nil)"
  (* \<Longrightarrow> "cons (Suc (Suc 0)) (cons (Suc 0) nil)" :: "nat Poly.list" *)

fun length :: "'a list \<Rightarrow> nat" where
  "length nil = 0"
  | "length (cons h t) = Suc (length t)"

lemma test_length1: "length (cons 1 (cons 2 nil)) = 2" by simp
lemma test_length2: "length (cons True nil) = 1" by simp

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app nil l2 = l2"
  | "app (cons h t) l2 = cons h (app t l2)"

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc nil v = cons v nil"
  | "snoc (cons h t) v = cons h (snoc t v)"

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev nil = nil"
  | "rev (cons h t) = snoc (rev t) h"

lemma test_rev1: "rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil))" by simp
lemma test_rev2: "rev nil = nil" by simp

(* Exercise: 2 stars (mumble_grumble) *)

datatype mumble = a' | b' mumble nat | c'
datatype 'a grumble = d' mumble | e' 'a

term "d' (b' a' 5)"
  (* \<Longrightarrow> "d' (b' a' 5)" :: "'a grumble" *)
term "d' (b' a' 5) :: mumble grumble"
  (* \<Longrightarrow> "d' (b' a' 5)" :: "mumble grumble" *)
term "d' (b' a' 5) :: bool grumble"
  (* \<Longrightarrow> "d' (b' a' 5)" :: "bool grumble" *)
term "e' True"
  (* \<Longrightarrow> "e' True" :: "bool grumble" *)
term "e' (b' c' 0) :: mumble grumble"
  (* \<Longrightarrow> "e' (b' c' 0)" :: "mumble grumble" *)
(* term "e' (b' c' 0) :: bool grumble" \<Longrightarrow> error *)
term "c'"
  (* \<Longrightarrow> "c'" :: "mumble" *)

(* Exercise: 2 stars (baz_num_elts) *)

(*
datatype baz = x baz | y baz bool

baz has no element
*)

subsubsection {* Type Annotation Inference *}
subsubsection {* Type Argument Synthesis *}
subsubsection {* Implicit Arguments *}
subsubsection {* Exercises: Polymorphic Lists *}

(* Exercise: 2 stars, optional (poly_exercises) *)

fun repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "repeat x 0 = nil"
  | "repeat x (Suc n) = cons x (repeat x n)"

lemma test_repeat1: "repeat True 2 = cons True (cons True nil)"
proof -
  have 2: "2 = Suc 1" by simp
  show ?thesis by (simp add: 2)
qed

theorem nil_app: "\<forall>l::'a list. app nil l = l" by simp
theorem rev_snoc: "\<forall>v :: 'a. \<forall>s :: 'a list. rev (snoc s v) = cons v (rev s)"
apply auto by (induct_tac s, auto)

theorem rev_involutive: "\<forall>l :: 'a list. rev (rev l) = l"
apply auto by (induct_tac l,  auto simp add: rev_snoc)

theorem snoc_with_append: "\<forall>l1 l2 :: 'a list. \<forall>v :: 'a. snoc (app l1 l2) v = app l1 (snoc l2 v)"
apply auto by (induct_tac l1, auto)

subsubsection {* Polymorphic Pairs *}

datatype ('a,'b) prod = pair 'a 'b

no_type_notation
  Product_Type.prod  ("(_ \<times>/ _)" [21, 20] 20)

type_notation
  prod  ("_ \<times> _")

primrec fst :: "('a \<times> 'b) \<Rightarrow> 'a" where
  "fst (pair x _) = x"
primrec snd :: "('a \<times> 'b) \<Rightarrow> 'b" where
  "snd (pair _ y) = y"

fun combine :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "combine nil _ = nil"
  | "combine _ nil = nil"
  | "combine (cons x xs) (cons y ys) = cons (pair x y) (combine xs ys)"

(* Exercise: 1 star, optional (combine_checks) *)

value "combine [1;2] [false;false;true;true]"
  (* \<Longrightarrow> "[pair 1 false ; pair (1 + 1) false]" :: "'a \<times> 'b Poly.list" *)

(* Exercise: 2 stars (split) *)

fun pair_map :: "(('a \<Rightarrow> 'c) \<times> ('b \<Rightarrow> 'd)) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('c \<times> 'd)" where
  "pair_map (pair f g) (pair x y) = pair (f x) (g y)"

fun split :: "('a \<times> 'b) list \<Rightarrow> (('a list) \<times> ('b list))" where
  "split nil = pair nil nil"
  | "split (pair x y ; zs) = pair_map (pair (cons x) (cons y)) (split zs)"

lemma test_split: "split [pair 1 false; pair 2 false] = pair [1;2] [false;false]" by simp

subsubsection {* Polymorphic Options *}

datatype 'a option = Some 'a | None

fun index :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "index _ nil = None"
  | "index n (cons a l) = (if n = 0 then Some a else index (n - 1) l)"

lemma test_index1: "index 0 [4;5;6;7] = Some 4" by simp
lemma test_index2: "index 1 [[1];[2]] = Some [2]" by simp
lemma test_index3: "index 2 [True] = None" by simp

(* Exercise: 1 star, optional (hd_opt_poly) *)

fun hd_opt :: "'a list \<Rightarrow> 'a option" where
  "hd_opt nil = None"
  | "hd_opt (h ; t) = Some h"

term "hd_opt"
  (* \<Longrightarrow> "hd_opt" :: "'a Poly.list \<Rightarrow> 'a Poly.option" *)

lemma test_hd_opt1: "hd_opt [1;2] = Some 1" by simp
lemma test_hd_opt2: "hd_opt [[1];[2]] = Some [1]" by simp

subsection {* Functions as Data *}
subsubsection {* Higher-Order Functions *}

fun doit3times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "doit3times f x = f (f (f x))"

term "doit3times"
  (* \<Longrightarrow> "doit3times" :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" *)

lemma test_doit3times: "doit3times (\<lambda>(x :: nat). x - 2) 9 = 3" by simp
lemma test_doit3times': "doit3times (\<lambda>x. \<not> x) True = False" by simp

subsubsection {* Partial Application *}

definition "plus3 = plus (3 :: nat)"
term "plus3"
  (* \<Longrightarrow> "plus3" :: "nat \<Rightarrow> nat" *)

lemma test_plus3: "plus3 4 = 7" unfolding plus3_def by simp
lemma test_plus3': "doit3times plus3 0 = 9" unfolding plus3_def by simp
lemma test_plus3'' : "doit3times (plus (3 :: nat)) 0 = 9" by simp

subsubsection {* Digression: Currying *}

(* Exercise: 2 stars, advanced (currying) *)

fun prod_curry :: "(('a \<times> 'b) \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" where
  "prod_curry f x y = f (pair x y)"
fun prod_uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> 'c" where
  "prod_uncurry f (pair x y) = f x y"

term prod_curry
  (* "prod_curry" :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" *)
term prod_uncurry
  (* "prod_uncurry" :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c" *)

theorem uncurry_curry: "\<forall>(f :: 'a \<Rightarrow> 'b \<Rightarrow> 'c) x y. prod_curry (prod_uncurry f) x y = f x y" by simp
theorem curry_uncurry: "\<forall>(f :: ('a \<times> 'b) \<Rightarrow> 'c) (p :: 'a \<times> 'b). prod_uncurry (prod_curry f) p = f p"
apply auto by (case_tac p, auto)

subsubsection {* Filter *}

fun filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter test nil = nil"
  | "filter test (h;t) = (if test h then h ; (filter test t) else filter test t)"

lemma test_filter1: "filter (\<lambda>(x :: nat). x mod 2 = 0) [1;2;3;4] = [2;4]" by simp

fun length_is_1 :: "'a list \<Rightarrow> bool" where
  "length_is_1 l = (length l = 1)"

lemma test_filter2: "filter length_is_1 [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]]" by simp

fun countoddmembers' :: "nat list \<Rightarrow> nat" where
  "countoddmembers' l = length (filter (\<lambda>x. x mod 2 = 1) l)"

lemma test_countoddmembers'1: "countoddmembers' [1;0;3;1;4;5] = 4" by simp
lemma test_countoddmembers'2: "countoddmembers' [0;2;4] = 0" by simp
lemma test_countoddmembers'3: "countoddmembers' nil = 0" by simp

subsubsection {* Anonymous Functions *}

lemma test_anon_fun': "doit3times (\<lambda>(n :: nat). n * n) 2 = 256" by simp
lemma test_filter2': "filter (\<lambda>l. length l = 1) [[1; 2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]]" by simp

(* Exercise: 2 stars (filter_even_gt7) *)

fun filter_even_gt7 :: "nat list \<Rightarrow> nat list" where
  "filter_even_gt7 l = filter (\<lambda>x. x mod 2 = 0 & x \<ge> 7) l"

lemma test_filter_even_gt7_1: "filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8]" by simp
lemma test_filter_even_gt7_2: "filter_even_gt7 [5;2;6;19;129] = []" by simp

(* Exercise: 3 stars (partition) *)
fun partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> (('a list) \<times> ('a list))" where
  "partition f xs = pair (filter f xs) (filter (\<lambda>x. \<not> f x) xs)"

lemma test_partition1: "partition (\<lambda>(x :: nat). x mod 2 = 1) [1;2;3;4;5] = pair [1;3;5] [2;4]" by simp
lemma test_partition2: "partition (\<lambda>_. False) [5;9;0] = pair [] [5;9;0]" by simp

subsubsection {* Map *}

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map f nil = nil"
  | "map f (h;t) = f h ; map f t"

lemma test_map1: "map (\<lambda>(x :: nat). x + 3) [2;0;2] = [5;3;5]" by simp
lemma test_map2: "map (\<lambda>(x :: nat). x mod 2 = 1) [2;1;2;5] = [False;True;False;True]" by simp
lemma test_map3: "map (\<lambda>(n :: nat). [(n mod 2 = 0) ; (n mod 2 = 1)]) [2;1;2;5] = [[True;False];[False;True];[True;False];[False;True]]"
by simp

subsubsection {* Map for options *}

(* Exercise: 3 stars (map_rev) *)

lemma map_rev_lem: "\<And>f l a. map f (snoc l a) = snoc (map f l) (f a)"
by (induct_tac l, auto)

theorem map_rev: "\<forall>(f :: 'a \<Rightarrow> 'b) (l :: 'a list). map f (rev l) = rev (map f l)"
apply auto by (induct_tac l, auto simp add: map_rev_lem)

(* Exercise: 2 stars (flat_map) *)

fun flat_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "flat_map f nil = nil"
  | "flat_map f (h;t) = app (f h) (flat_map f t)"

lemma test_flat_map1: "flat_map (\<lambda>n. [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4]" by simp

fun option_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
  "option_map f None = None"
  | "option_map f (Some a) = Some (f a)"

(* Exercise: 2 stars, optional (implicit_args) *)

subsubsection {* Fold *}

fun fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold f nil b = b"
  | "fold f (h;t) b = f h (fold f t b)"

term "fold (\<lambda>x y. x \<and> y)"
  (* \<Longrightarrow> "Poly.fold op \<and>" :: "bool Poly.list \<Rightarrow> bool \<Rightarrow> bool" *)

lemma fold_example1: "fold (\<lambda>(x :: nat) y. x * y) [1;2;3;4] 1 = 24" by simp
lemma fold_example2: "fold (\<lambda>x y. x \<and> y) [True;True;False;True] True = False" by simp
lemma fold_example3: "fold app [[1];[];[2;3];[4]] [] = [1;2;3;4]" by simp

(* Exercise: 1 star, advanced (fold_types_different) *)

subsubsection {* Functions For Constructing Functions *}

fun constfun :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "constfun x = (\<lambda>_. x)"
fun ftrue where
  "ftrue x = constfun True x"

lemma constfun_example1: "ftrue 0 = True" by simp
lemma constfun_example2: "(constfun 5) 99 = 5" by simp

fun override :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "override f k x = (\<lambda>(k' :: nat). if k = k' then x else f k')"
fun fmostlytrue where
  "fmostlytrue x = override (override ftrue 1 False) 3 False x"

lemma override_example1: "fmostlytrue 0 = True" by simp
lemma override_example2: "fmostlytrue 1 = False" by simp
lemma override_example3: "fmostlytrue 2 = True" by simp
lemma override_example4: "fmostlytrue 3 = False" by simp

(* Exercise: 1 star (override_example) *)

theorem override_example: "\<forall>(b::bool). (override (constfun b) 3 True) 2 = b" by simp

subsection {* The unfold Tactic *}

theorem unfold_example: "\<forall>(m :: nat) n. 3 + n = m \<longrightarrow> plus3 n + 1 = m + 1"
unfolding plus3_def by simp

theorem override_eq: "\<forall>x k (f :: nat \<Rightarrow> 'a). (override f k x) k = x" by simp
theorem override_neq: "\<forall>x1 x2 k1 k2 (f :: nat \<Rightarrow> 'a). f k1 = x1 \<longrightarrow> k2 \<noteq> k1 \<longrightarrow> (override f k2 x2) k1 = x1" by simp

(* Additional Exercises *)

fun fold_length :: "'a list \<Rightarrow> nat" where
  "fold_length l = fold (\<lambda>_ n. Suc n) l 0"

lemma test_fold_length1: "fold_length [4;7;0] = 3" by simp

theorem fold_length_correct: "\<forall>(l :: 'a list). fold_length l = length l"
apply auto by (induct_tac l, auto)

(* Exercise: 3 stars (fold_map) *)

fun fold_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "fold_map f xs = fold (\<lambda>a b. f a ; b) xs nil"

lemma fold_map_correct: "\<forall>f l. fold_map f l = map f l"
apply auto by (induct_tac l, auto)

end

