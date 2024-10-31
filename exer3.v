From mathcomp Require Import all_ssreflect.


(* Prove the following lemmas: *)

(* Lemma exer0 p : true && p = p. 

Lemma exer1 p q : p || q = q || p.

Lemma exer2 p q : p ==> q = ~~ p || q.

Lemma exer3 b : ~~ ~~ ~~ b = ~~ b.

Lemma exer4 n m : False -> n + m = n - m.

Lemma exer5 n : (0 == 0) = (0 == 1) -> n < n - 1.
*)

Lemma exer6 b0 b1 b2 b3 : ~~ (b0 && ~~ ~~ ~~ b0) || ((b1 && ~~ b2) || ~~ b3).

Proof. by case: b0. Qed.

(* In the mathcomp library we have the operation maxn : nat -> nat -> nat.

   Use maxn to define the function max3 : nat -> nat -> nat -> nat such that
   max3 n0 n1 n2 returns the maximum of n0, n1 and n2.

   State and prove the following properties:
   1. ∀n ∈ N, max3(n, n, n) = n;
   2. ∀n0, n1, n2 ∈ N, max3(n0, n1, n2) = maxn(maxn(n0, n1), n2);
   3. ∀n0, n1, n2 ∈ N, max3(n0, n1, n2) = max3(n1, n0, n2);  *)

Definition max3 n0 n1 n2 := maxn (maxn n0 n1) n2.

Lemma L1 n : max3 n n n = n.
Proof. by rewrite /max3; do 2! rewrite maxnn. Qed.

Lemma L2 n0 n1 n2 : max3 n0 n1 n2 = maxn (maxn n0 n1) n2.
Proof. by []. Qed.

Lemma L3 n0 n1 n2 : max3 n0 n1 n2 = max3 n1 n0 n2.
Proof. by rewrite /max3 (maxnC n0 n1). Qed. 

(* Copy-paste the solutions to exercise 2 in exers02.v. Using the injective
   predicate, state and prove that next_month is injective *)

Print injective.

Inductive month := January | February | March | April | May | June | July 
| August | September | October | November | December.

Definition next_month (m: month) : month := match m with 
    January => February
|   February => March
|   March => April
|   April => May
|   May => June
|   June => July
|   July => August
|   August => September
|   September => October
|   October => November
|   November => December
|   December => January
end.



Lemma next_month_inj : injective next_month.
Proof. 
rewrite /injective. (*not necesary*)
by case; case. (* move => x1; case: x1; move => x2; case: x2*)
Qed.
