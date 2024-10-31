From mathcomp Require Import all_ssreflect.

(* Prove the following Lemma *)
Lemma maxn_subn m n : maxn n m = n -> m - n = 0.
Proof. by move => /maxn_idPl /eqP. Qed.

(* If we have as a goal a proposition that is existentially quantified
   (that is, something of the form exists x : T, A(x) ) we need to provide
   a witness for such proposition.
   A proof of an existential statement is composed by a witness t, and a proof 
   that t satisfies the statement. In Coq, we provide the witnees by using the
   exists command together with the particular element i.e. "exists t".
 *)

Example existential_ex : exists n, 0 < n.
Proof.
exists 1.
by [].
(* Or just: by exists 1. *)
Qed.

Example existential_ex2 : exists n m, n + m = 17.
Proof.
exists 10.
exists 7.
by [].
(* Or just: by exists 10; exists 7. *)
Qed.

(* Prove the following lemma *)
Lemma leq_Eaddn n m :
  n <= m -> exists n0 : nat, n0 + n = m.
Proof. move => leq. 
by exists (m-n); rewrite addnC; apply subnKC. 
Qed.

Lemma leq_eqVltP n m :
  reflect (n == m \/ n < m) (n <= m).
Proof.  rewrite (leq_eqVlt n). by apply /orP.
Qed.

(* Prove the following Lemma. You are *NOT* allowed to use iffP or idP *)
Lemma andP_rev (b1 b2 : bool) : reflect (b1 /\ b2) (b2 && b1).
Proof. 
by rewrite andbC; apply: andP.
Qed.
