From mathcomp Require Import all_ssreflect.
Require Import AutomatonModule myLemma.

(*列挙型の定義*)
Inductive Z2 := zero|one.
Inductive Z3 := _0|_1|_2.
Inductive ab := a|b.


Lemma Z2_eq_dec(x y:Z2):{x=y}+{x<>y}. Proof. decide equality. Qed.
Lemma Z3_eq_dec(x y:Z3):{x=y}+{x<>y}. Proof. decide equality. Qed.
Lemma ab_eq_dec(x y:ab):{x=y}+{x<>y}. Proof. decide equality. Qed.
(*Equalの判定関数*)
Definition Z2_eqb(x y:Z2):=
match Z2_eq_dec x y with|left _=>true|right _=>false end.
Definition Z3_eqb(x y:Z3):=
match Z3_eq_dec x y with|left _=>true|right _=>false end.
Definition ab_eqb(x y:ab):=
match ab_eq_dec x y with|left _=>true|right _=>false end.

(*a=bとa==bの互換性の保証*)
Lemma eq_Z2P:Equality.axiom Z2_eqb.
Proof. move=>x y;apply/(iffP idP);rewrite/Z2_eqb;by case:Z2_eq_dec. Qed.
Lemma eq_Z3P:Equality.axiom Z3_eqb.
Proof. move=>x y;apply/(iffP idP);rewrite/Z3_eqb;by case:Z3_eq_dec. Qed.
Lemma eq_abP:Equality.axiom ab_eqb.
Proof. move=>x y;apply/(iffP idP);rewrite/ab_eqb;by case:ab_eq_dec. Qed.

(*eqType属性の付与*)
Definition Z2_eqMixin := EqMixin eq_Z2P.
Canonical Z2_eqType := Eval hnf in EqType _ Z2_eqMixin.
Definition Z3_eqMixin := EqMixin eq_Z3P.
Canonical Z3_eqType := Eval hnf in EqType _ Z3_eqMixin.
Definition ab_eqMixin := EqMixin eq_abP.
Canonical ab_eqType := Eval hnf in EqType _ ab_eqMixin.

(*natとの変換関数を定義*)
Definition nat_of_Z2(x:Z2):=match x with zero=>0|one=>1 end.
Definition Z2_of_nat(n:nat):=match n with|0=>Some zero|1=>Some one|_=>None end.
Definition nat_of_Z3(x:Z3):=match x with _0=>0|_1=>1|_2=>2 end.
Definition Z3_of_nat(n:nat):=
match n with|0=>Some _0|1=>Some _1|2=>Some _2|_=>None end.
Definition nat_of_ab(x:ab):=match x with a=>0|b=>1 end.
Definition ab_of_nat(n:nat):=match n with 0=>Some a|1=>Some b|_=>None end.

(*正しく逆関数になっているかの証明*)
Lemma Z2_count_spec :pcancel nat_of_Z2 Z2_of_nat.
Proof. rewrite/pcancel=>x;by destruct x. Qed.
Lemma Z3_count_spec :pcancel nat_of_Z3 Z3_of_nat.
Proof. rewrite/pcancel=>x;by destruct x. Qed.
Lemma ab_count_spec :pcancel nat_of_ab ab_of_nat.
Proof. rewrite/pcancel=>x;by destruct x. Qed.

(*countType,choiceType属性の付与*)
Definition Z2_countMixin := CountMixin Z2_count_spec.
Definition Z2_choiceMixin := CountChoiceMixin Z2_countMixin.
Canonical Z2_choiceType := Eval hnf in ChoiceType Z2 Z2_choiceMixin.
Canonical Z2_countType := Eval hnf in CountType Z2 Z2_countMixin.
Definition Z3_countMixin := CountMixin Z3_count_spec.
Definition Z3_choiceMixin := CountChoiceMixin Z3_countMixin.
Canonical Z3_choiceType := Eval hnf in ChoiceType Z3 Z3_choiceMixin.
Canonical Z3_countType := Eval hnf in CountType Z3 Z3_countMixin.
Definition ab_countMixin := CountMixin ab_count_spec.
Definition ab_choiceMixin := CountChoiceMixin ab_countMixin.
Canonical ab_choiceType := Eval hnf in ChoiceType ab ab_choiceMixin.
Canonical ab_countType := Eval hnf in CountType ab ab_countMixin.

(*型の一覧となるリストを定義*)
Definition enum_Z2 := [::zero;one].
Definition enum_Z3 := [::_0;_1;_2].
Definition enum_ab := [::a;b].


(*各要素が重複なくリストに含まれることを示す*)
Lemma enum_Z2P :Finite.axiom enum_Z2.
Proof. move=>x;destruct x;rewrite/=/eq_op/=/Z2_eqb;
by repeat case:Z2_eq_dec. Qed.
Lemma enum_Z3P :Finite.axiom enum_Z3.
Proof. move=>x;destruct x;rewrite/=/eq_op/=/Z3_eqb;
by repeat case:Z3_eq_dec. Qed.
Lemma enum_abP :Finite.axiom enum_ab.
Proof. move=>x;destruct x;rewrite/=/eq_op/=/ab_eqb;
by repeat case:ab_eq_dec. Qed.

(*finType属性を付与*)
Definition Z2_finMixin := FinMixin enum_Z2P.
Canonical Z2_finType := Eval hnf in FinType Z2 Z2_finMixin.
Definition Z3_finMixin := FinMixin enum_Z3P.
Canonical Z3_finType := Eval hnf in FinType Z3 Z3_finMixin.
Definition ab_finMixin := FinMixin enum_abP.
Canonical ab_finType := Eval hnf in FinType ab ab_finMixin.



Definition delta_mp(s:Z2)(w:ab):Z2 :=
match s,w with
|_ , a => s
|one, b => zero
|zero, b => one
end.
Definition delta_m1(s:Z3)(w:ab):Z3:=
match s,w with
|_0, a => _1
|_1, b => _0
|_ , _ => _2
end.

Definition mp:automaton := {|init:=zero;delta:=delta_mp;final:=[set one]|}.
Definition m1:automaton := {|init:=_0;delta:=delta_m1;final:=[set _1]|}.

Lemma ac_b : accept mp[::b].
Proof. by rewrite/accept/=set11. Qed.
Lemma ac_bbab : accept mp[::b;b;a;b].
Proof. by rewrite/accept/=set11. Qed.