From mathcomp Require Import all_ssreflect.
Require Import Ascii String.

(* 有限オートマトンの定義 *)
Structure automaton{state symbol:finType}:= Automaton {
  init : state;
  delta : state -> symbol -> state;
  final : {set state}
}.

(*記号を複数個まとめて読み込む関数*)
Fixpoint dstar{state symbol:finType}(delta:state->symbol->state)
  (q:state)(str:seq symbol):state :=
match str with
|nil => q
|h::str' => dstar delta (delta q h) str'
end.

(*受理判定の関数*)
Definition accept{state symbol:finType}(M:@automaton state symbol)
  (str:seq symbol):bool := dstar (delta M) (init M) str\in final M.

(*与えられた文字列のうち、acceptされるものだけを残す*)
Definition accepts{state symbol:finType}(M:@automaton state symbol)
  (l:seq (seq symbol)):seq (seq symbol):=
[seq str<-l|accept M str].

(*文字の読み込みを二段階に分割*)
Lemma dstarLemma {state symbol : finType}(delta:state->symbol->state)(q:state)
(s t:seq symbol):dstar delta q (s++t) = dstar delta (dstar delta q s) t.
Proof. move:q;by elim:s;[|move=>a s' H;simpl]. Qed.






(*以下はasciiやboolに有限型(finType)をつけて具体的なオートマトンを構成している。
証明とは無関係*)
Open Scope nat_scope.

Definition eq_string a b :=
  match string_dec a b with left _ => true | _ => false end.

Lemma eq_stringP : Equality.axiom eq_string.
Proof. move=> ??; apply: (iffP idP); rewrite /eq_string; by case: string_dec. Qed.

Canonical string_eqMixin := EqMixin eq_stringP.
Canonical string_eqType := Eval hnf in EqType _ string_eqMixin.

Definition eq_ascii a b :=
  match ascii_dec a b with left _ => true | _ => false end.

Lemma eq_asciiP : Equality.axiom eq_ascii.
Proof. move=> ??; apply: (iffP idP); rewrite /eq_ascii; by case: ascii_dec. Qed.

Definition ascii_eqMixin := EqMixin eq_asciiP.
Canonical ascii_eqType := Eval hnf in EqType _ ascii_eqMixin.
Lemma ascii_count_spec :pcancel nat_of_ascii 
(fun n:nat=>Some (ascii_of_nat n)).
Proof. rewrite/pcancel=>a.
destruct a as [[|][|][|][|][|][|][|][|]]; vm_compute; reflexivity. Qed.
Definition ascii_countMixin := CountMixin ascii_count_spec.
Definition ascii_choiceMixin := CountChoiceMixin ascii_countMixin.
Canonical ascii_choiceType := Eval hnf in ChoiceType ascii ascii_choiceMixin.
Canonical ascii_countType := Eval hnf in CountType ascii ascii_countMixin.
Definition enum_ascii := [seq ascii_of_nat n|n<-List.seq 0 256].
Lemma enum_asciiP :Finite.axiom enum_ascii.
Proof. rewrite/Finite.axiom=>a.
destruct a as [[|][|][|][|][|][|][|][|]]; vm_compute; reflexivity. Qed.
Definition ascii_finMixin := FinMixin enum_asciiP.
Canonical ascii_finType := Eval hnf in FinType ascii ascii_finMixin.

Definition p1_d (state:bool_finType)(symbol:ascii_finType) :=
match symbol with
|"a"%char => state
|"b"%char => ~~state
|_=>false
end.

Definition p1 := Automaton bool_finType ascii_finType true p1_d [set true].
Compute accept p1 [::"a"%char;"b"%char;"a"%char].

