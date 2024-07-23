From mathcomp Require Import all_ssreflect.
Require Import Ascii String.

Inductive domino{symbol:finType}:=
|null : domino
|Domino :seq symbol -> seq symbol -> nat -> nat -> domino.
Definition mu{symbol:finType}(d1 d2:@domino symbol):@domino symbol:=
match d1,d2 with
|Domino nil _ _ _ ,Domino nil _ _ _ => null
|Domino _ nil _ _ ,Domino nil _ _ _ => null
|Domino nil _ _ _ ,Domino _ nil _ _ => null
|Domino _ nil _ _ ,Domino _ nil _ _ => null
|Domino l1 r1 x1 y1 ,Domino nil r2 _ _ => Domino l1 (r1++r2) x1 y1
|Domino l1 r1 x1 y1 ,Domino l2 nil _ _ => Domino (l1++l2) r1 x1 y1
|Domino nil r1 _ _ ,Domino l2 r2 x2 y2 =>
  Domino l2 (r1++r2) (x2 - (size r1)) (size r1 - x2)
|Domino l1 nil _ _ ,Domino l2 r2 x2 y2 =>
  Domino (l1++l2) r2 (size l1 - y2) (y2 - (size l1))
|Domino l1 r1 x1 y1 ,Domino l2 r2 x2 y2 =>
  if y1 + (size l1) + x2 == x1 + (size r1) + y2
    then Domino(l1++l2)(r1++r2)x1 y1 else null
|_,_ => null
end.
Definition mu'{s:finType}(a:@domino s)(d:@domino s*@domino s):@domino s:=
let (d1,d2) := d in mu (mu d1 a) d2.
Definition wk{s:finType}(rh:seq (s*s))(d:@domino s):bool :=
match d with
|Domino l r 0 0 =>
  if size l == size r then
    all(fun p=>p\in rh)(zip l r)
  else
    false
|_ => false
end.
Structure sticker{symbol:finType}:= Sticker{
  rho : seq (symbol*symbol);
  start : seq (@domino symbol);
  extend : seq (@domino symbol*@domino symbol)
}.
Fixpoint ss_generate{symbol:finType}(n:nat)(stk:@sticker symbol):seq domino:=
match n with
|0 => start stk
|S n' => let A' := ss_generate n' stk in
  A'++[seq mu' a d|a<-A',d <- (extend stk)]
end.

Fixpoint ss_generate_prime{s:finType}(n:nat)(stk:@sticker s):seq domino:=
match n with
|0 => start stk
|S n' =>
  let A' := ss_generate_prime n' stk in
  let A_wk := [seq a<-A'|wk (rho stk) a] in
  let A_nwk := [seq a<-A'|~~ wk (rho stk) a] in
  A_wk++[seq mu' a d|a<-A_nwk,d <- (extend stk)]
end.

Definition ss_language_f{s:finType}(d:@domino s):seq s :=
match d with
|Domino l _ _ _ => l
|_ => nil
end.
Definition ss_language{s:finType}(n:nat)(stk:@sticker s):seq (seq s) :=
[seq ss_language_f d | d <- [seq d <- ss_generate n stk|wk (rho stk) d]].
Definition ss_language_prime{s:finType}(n:nat)(stk:@sticker s):seq (seq s) :=
[seq ss_language_f d | d <- [seq d <- ss_generate_prime n stk|wk (rho stk) d]].
