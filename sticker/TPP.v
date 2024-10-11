From mathcomp Require Import all_ssreflect.

Fixpoint Rewrite{t:Type}(n:nat)(x:t)(s:seq t):seq t:=
match n, s with
|0, h::s' => x::s'
|S n', h::s' => h::Rewrite n' x s'
|_, nil => nil
end.
Compute Rewrite 2 5 [::1;2;3;4;5].
Definition Swap(n m:nat)(s:seq nat):seq nat :=
Rewrite n(nth 0 s m)(Rewrite m(nth 0 s n)s).
Compute Swap 2 5 [::0;1;2;3;4;5;6].
(*indexは0から*)
Notation "( x | y ) z":=(Swap x y z)(at level 41,right associativity) .

Fixpoint Cycle(x s:seq nat): seq nat :=
match x with
|a::x' =>
  match x' with
  |nil => s
  |b::_ => Swap a b(Cycle x' s)
  end
|nil => nil
end.

Compute Cycle[::1;4;3][::5;9;1;3;7].
Compute Cycle[::0;1;3;4;2][::0;1;2;3;4].
Eval simpl in Cycle[::0;1;3;4;2].
Theorem minSwapCycle(x:seq nat)