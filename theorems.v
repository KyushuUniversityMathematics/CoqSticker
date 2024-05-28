From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.

Require Import Ascii String.

Require Import AutomatonModule AutomatonEx.
Open Scope nat_scope.
Open Scope string_scope.

Lemma dstarLemma :
forall d : State -> Symbol -> State,forall q :State,
forall u v : string,
(dstar d q (u ++ v)) = (dstar d (dstar d q u) v).
Proof.
move => d q u v.
move : q.
elim : u.
simpl.
by [].
move => a s H q;simpl.
rewrite H.
by [].
Qed.


Fixpoint abword (w:string):bool:=
match w with
|"" => true
|String "a" w' => abword w'
|String "b" w' => abword w'
|_ => false
end.

Fixpoint numb (w:string):nat:=
match w with
|"" => 0
|String "b" w' => S (numb w')
|String _ w' => numb w'
end.

Fixpoint ban n:=
match n with
|0 => ""
|S n' => "ba" ++ ban n'
end.
Definition aban n := "a" ++ ban n.

Lemma head_ab :
forall (x : ascii)(w :string),
abword (String x w) -> x = "a"%char \/ x = "b"%char.
Proof.
move => x w H.
destruct x.
destruct b ;destruct b0;
destruct b1;destruct b2;
destruct b3;destruct b4;
destruct b5;destruct b6;
by [left | right].
Qed.


Lemma sub_abword_lemma :
forall (x : ascii)(w : string), abword (String x w) -> abword w.
Proof.
move => x w H.
move : (head_ab x w H) => H'.
by case : H' => H'; rewrite H' in H; move : H; simpl.
Qed.

Lemma m1_A_odd1_lemma :
forall w : string, abword w ->
(~~ odd (numb w) ->
(odd (numb w) -> dstar m1_d 0 w = 1) -> dstar m1_d 1 w = 1) /\
(odd (numb w) ->
(~~ odd (numb w) -> dstar m1_d 1 w = 1) -> dstar m1_d 0 w = 1).
Proof.
elim.
by [].
move => x w H1 H2.
move : ((head_ab x w) H2) => Hab.
move : H2.
case : Hab => [Ha | Hb].
rewrite Ha //=.
rewrite Hb /=.
move => H2.
move : (H1 H2) => H.
clear H1.
case : H => Hx Hy.
by split;rewrite Bool.negb_involutive.
Qed.

Lemma m1_A_odd2_lemma :
forall w : string,
abword w ->
(dstar m1_d 1 w == 1 -> (dstar m1_d 0 w == 1 -> odd (numb w)) -> ~~ odd (numb w)) /\
(dstar m1_d 0 w == 1 -> (dstar m1_d 1 w == 1 -> ~~ odd (numb w) ) -> odd (numb w) ).
Proof.
elim.
by simpl.
move => x s H Hs.
move : ((head_ab x s) Hs) => Hab.
move : Hs.
case : Hab => Hab; rewrite Hab //=.
move => Hs.
move : (H Hs).
case => H1 H2.
clear H Hs.
by split;rewrite Bool.negb_involutive.
Qed.

Lemma m2lemma : forall w : string, abword w ->
(dstar m2_d 0 w \in [:: 1] -> exists n : nat, w = aban n)
/\
(dstar m2_d 1 w \in [:: 1] -> exists n : nat, w = ban n)
/\
(dstar m2_d 2 w \in [:: 1] -> False).
Proof.
elim.
simpl.
move => _.
split.
by [].
split;move => H.
by exists 0.
by [].
move => a s H1 H2.
move : ((head_ab a s) H2) => Hab.
move : ((sub_abword_lemma a s) H2) => Hs.
move : (H1 Hs).
case => K1.
case.
move => K2 K3.
move : H1 H2 Hs => _ _ _.
case : Hab => H1;rewrite H1;simpl;split.
move => H2.
move : (K2 H2) => H.
destruct H as [i K].
exists i.
by rewrite K.
by split => H2;move : (K3 H2).
by move => H2; move : (K3 H2).
split;move => H2;rewrite //.
move : (K1 H2) => H.
destruct H as [i K].
exists (i.+1).
rewrite K.
by rewrite /aban.
Qed.

Lemma m1_A_odd1 :
forall w : string, abword w -> odd (numb w) -> accept m1 w.
Proof.
simpl.
move => w H H'.
rewrite inE.
apply /eqP.
move : w H H'.
elim.
by [].
move => x s H0 H1 H2.
move : ((head_ab x s) H1).
move => Hab.
move : H1 H2.
case : Hab => [Ha | Hb].
rewrite Ha.
by simpl.
rewrite Hb.
simpl.
move => H Heven.
move : ((m1_A_odd1_lemma s) H).
case => H1 H2.
move : (H0 H) => H3.
clear H0 H2.
by move : (H1 Heven H3).
Qed.

Lemma m1_A_odd2 :
forall w : string, abword w -> accept m1 w -> odd (numb w).
Proof.
simpl.
move => Hx Hy Hz.
rewrite inE in Hz.
elim : Hx Hy Hz.
by simpl.
move => x s H1 H2.
move : ((head_ab x s) H2) => Hab.
move : H2.
case : Hab => H;rewrite H //=.
move => Hs H2.
move : ((m1_A_odd2_lemma s) Hs).
case => H3 H4.
apply H3.
by [].
by apply H1.
Qed.

Lemma abnaAm2 : forall n : nat, accept m2 (aban n).
Proof.
elim; rewrite //.
Qed.

Lemma abnaAm2' :
forall w : string, abword w ->
accept m2 w -> exists n, w = aban n.
Proof.
elim.
by simpl.
rewrite /accept.
rewrite /m2.
move => x s H1 H2.
move : ((head_ab x s) H2) => Hab.
move : ((sub_abword_lemma x s) H2) => Hs.
move : (H1 Hs) => H.
move : H1 H2 => _ _.
move : ((m2lemma s) Hs);case=> K1;case => K2 K3.
case : Hab => Haob;rewrite Haob;simpl;move => H1;rewrite //.
move : (K2 H1) => H2.
destruct H2 as [i H3].
exists i.
by rewrite H3.
Qed.