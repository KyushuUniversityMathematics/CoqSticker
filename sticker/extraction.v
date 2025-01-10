From mathcomp Require Import all_ssreflect.
(*From mathcomp Require Import all_ssreflect.*)
Require Import Extraction.
Extraction Language Haskell.
Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive sumbool => "Prelude.Bool"["Prelude.True" "Prelude.False"].
Extract Inductive nat => "Prelude.Int"["0" "Prelude.succ"]"(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.-1))".
Fixpoint f(n:nat):=
match n with
|0 => 0
|S n' => n+f n'
end.
Definition g(n:nat):=n*n.+1 %/ 2.
Theorem sigma:forall n:nat,f n = g n.
Proof.
elim=>[|n H].
done.
have H0:2 %| n.+1 * 2.
by rewrite dvdn_mull.
have H1:0<2.
done.
by rewrite/=H/g-(add2n n)mulnDr(divnDl _ H0)(mulnK _ H1)mulnC.
Qed.
Structure automaton:=Automaton{
  init:nat;
  fin:seq nat;
  delta:nat->nat->nat
}.
Fixpoint dstar(w:seq nat)(d:nat->nat->nat)(n:nat):=
match w with
|nil => n
|h::w' => d(dstar w' d n)h
end.
Definition d(n m:nat):=
match n,m with
|0,0 => 1
|1,0 => 0
|_,_ => n
end.
Definition a:={|
  init := 0;
  fin := [::1];
  delta := d
|}.
Definition accept(M:automaton)(s:seq nat):=dstar s(delta M)(init M)\in(fin M).
Compute accept a [::0;1;0;0].

Definition EQ(n m:nat):bool := n==m.
Definition t := true.
Definition h(b:bool):=if b then 1 else 0.
Extraction "automaton.hs" f g automaton dstar d a accept EQ t h.
Definition add (n m : nat) : nat := n + m.
Extraction "add.hs" add.





Require Import Arith.

Definition double (n : nat) := n + n.

Extraction "double.ml" double.




Extraction Language Haskell.

From mathcomp Require Import all_ssreflect.
Fixpoint sum(n:nat):=
match n with
|0 => 0
|S n' => n + sum n'
end.
Theorem sumP:forall n:nat,2*(sum n) = n*(n+1).
Proof.
by elim=>[|n H];[|rewrite/=mulnDr H!addn1-mulnDl add2n mulnC].
Qed.


