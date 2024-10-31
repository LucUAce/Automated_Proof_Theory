(* EXERCISES #1: FUNCTIONS; BASIC TYPES & CONTAINERS *)

From mathcomp Require Import all_ssreflect.


(*
  1. Define arbitrary functions of type:

       a. nat -> nat;
       b. bool -> bool -> bool -> bool;
       c. (nat -> nat -> nat) -> nat -> nat -> nat.

*)

Definition arb1 (n: nat) := n.+1.

Definition arb2 (bb : bool) (cb: bool) (db: bool): bool := (bb && cb) || db. 

Definition arb3 (natfun : nat->nat->nat) (n: nat) (m:nat) : nat := natfun n m.


(*

  2. Define the logical operation known as the Sheffer stroke and use the
     Compute command to test it:

       p q | ShS
       1 1 |  0
       1 0 |  1
       0 1 |  1
       0 0 |  1
*)

Definition ShS (p q: bool) := ~~(p&&q).

(*
  3. Define the function check_add satisfying the following specification:

       a. check_add: nat -> nat -> nat -> bool;

       b. check_add(n, m, r) = true,  if n + m = r
                               false, otherwise
*)

Definition check_add (n m r: nat) : bool := n+m==r.
 

(*
  4. Define the function headl2 satisfying the following specification:

       a. headl2 : list nat -> list nat

       b. headl2(l) = [:: n0],   if l := [:: n0; n1]
                      [::],      otherwise

*)

Definition headl2 (l: list nat) : list nat := match l with  
[:: n0; n1] => [:: n0] | _ => [::]
  end.
