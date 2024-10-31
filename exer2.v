From mathcomp Require Import all_ssreflect.

(* Given the definition: *)

Inductive T := con (n : nat).

(* Define a function con1 : T -> nat such that con1 (con n) = n. *)

Definition con1 (t: T): nat := match t with con n => n end.

(* Define the following objects:
   1. The set month containing the months of the year: January, February, etc;
   2. The function next_month : month -> month that computes the succeeding
      month i.e. next_month January = February, etc. *)

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


(* Define the regular mathematical factorial function. *)

Fixpoint fact (n:nat):nat := if n is k.+1 then n*fact(k) else 1.


(* Define the following predicates:
   1. A binary predicate fibo such that fibo n m specifies that m is the n-th
      Fibonacci number;
 1 1 2 3 5 8 13 21 *)

Definition fibo (n: nat) (m:nat) : bool := let fix fibaux (nk: nat) : nat := match nk with
    | 0 => 0
    | S k => if k is kk.+1 then fibaux(kk)+fibaux(k) else 1
end
 in fibaux(n)==m. 

Inductive fibopro: nat-> nat -> Prop :=
| fibo1 : fibopro 0 0
| fibo2 : fibopro 1 1
| fibo3 : forall n m1 m2, fibopro n m1 -> fibo n.+1 m2 -> fibopro n.+2 (m1+m2).

(*  2. A ternary predicate coll such that coll n m p specifies that p is the m-th
      number in the Collatz sequence starting with n. *)

Fixpoint even1 (n: nat ) : bool := match n with
|    0 => true
|    S k => ~~(even1 k)
end.

Definition funcoll1 (n : nat) : nat :=  if even1 n then n%/2 else (3*n).+1.

Definition coll (n m l: nat) : bool := let fix collaux (nk: nat) (mk: nat) : nat := 
iter mk funcoll1 nk in collaux n m == l.

(* same but all in one*)
Definition coll2 (n m l: nat) : bool := let fix collaux (nk: nat) (mk: nat) : nat := let
funcoll (n : nat) : nat := let fix even (n: nat ) : bool := match n with
|    0 => true
|    S k => ~~(even k)
end in
if even n then n%/2 else (3*n).+1 in
iter mk funcoll nk in collaux n m == l.

Inductive collpro: nat -> nat -> nat -> Prop :=
| coll0 : forall n, collpro n 0 n
| collod : forall n m p, collpro n m p -> odd n -> collpro n m.+1 (3*n).+1
| collev : forall n m p, collpro n m p -> ~~(odd n) -> collpro n m.+1 (n%/2).


(* Implement the Ackermann function. *)

Fixpoint acker (n m : nat) : nat := match n with
|   0 => S m
|   S k => let fix ackeraux (m: nat) : nat := match m with 
                      |   0 => acker k 1
                      |   S l => acker k (ackeraux l)
                      end in ackeraux m
end.

(* Using the existing iter and map functions to define a function that maps the
   natural number n to the list containing the n first odd numbers. *)

Print map.

Definition oddseq (s: seq nat): seq nat := 2*(size s)+1 :: s.

Definition odds (n : nat) : list nat := rev
  (iter n oddseq [::]).
  
Definition odds2 (n: nat) : list nat := let oddseq2 (s: seq nat): seq nat := 2*(size s)+1 :: s in 
rev (iter n oddseq [::]).


Definition odad (s : seq nat): seq nat := map (fun x => x.+2) s.

Definition odds3 (n: nat) : list nat := iter n (fun s =>  1 :: odad s) [::].


(* Define a type formalizing the set of propositional modal formulas built from
   the following syntax:
    p_i for i \in N | ~ A | A /\ B | [] A  *)

Print nat.

Inductive mod_forms : Set:=
| p : nat -> mod_forms
| neg : mod_forms -> mod_forms 
| land : mod_forms -> mod_forms -> mod_forms 
| box : mod_forms -> mod_forms.

Compute land (box (neg (p 2))) (p 5). 

