From mathcomp Require Import all_ssreflect.
Require Import MyLib.AutomatonModule.

(*列挙型の定義*)
Inductive Z2 := zero|one.
Inductive ab := a|b.


(*Equalの判定関数*)
Definition Z2_eqb(x1 x2:Z2) :=
match x1,x2 with |zero,zero=>true|one,one=>true|_,_=>false end.
Definition ab_eqb(x1 x2:ab) :=
match x1,x2 with |a,a=>true|b,b=>true|_,_=>false end.

(*a=bとa==bの互換性の保証*)
Lemma eq_Z2P:Equality.axiom Z2_eqb.
Proof. move=>x y;apply: (iffP idP); rewrite /Z2_eqb; by destruct x,y. Qed.
Lemma eq_abP:Equality.axiom ab_eqb.
Proof. move=>x y;apply: (iffP idP); rewrite /ab_eqb; by destruct x,y. Qed.

Definition Z2_eqMixin := eqMixin eq_Z2P.
Canonical Z2_eqType := Eval hnf in EqType _ Z2_eqMixin.
Definition ab_eqMixin := EqMixin eq_abP.
Canonical ab_eqType := Eval hnf in EqType _ ab_eqMixin.

Compute zero==one.

(*natとの変換関数を定義*)
Definition nat_of_Z2(x:Z2):=match x with zero=>0|one=>1 end.
Definition Z2_of_nat(n:nat):=match n with 0=>Some zero|1=>Some one|_=>None end.
Definition nat_of_ab(x:ab):=match x with a=>0|b=>1 end.
Definition ab_of_nat(n:nat):=match n with 0=>Some a|1=>Some b|_=>None end.

(*正しく逆関数になっているかの証明*)
Lemma Z2_count_spec :pcancel nat_of_Z2 Z2_of_nat.
Proof. rewrite/pcancel=>x;by destruct x. Qed.
Lemma ab_count_spec :pcancel nat_of_ab ab_of_nat.
Proof. rewrite/pcancel=>x;by destruct x. Qed.

(*countType,choiceType属性の付与*)
Definition Z2_countMixin := CountMixin Z2_count_spec.
Definition Z2_choiceMixin := CountChoiceMixin Z2_countMixin.
Canonical Z2_choiceType := Eval hnf in ChoiceType Z2 Z2_choiceMixin.
Canonical Z2_countType := Eval hnf in CountType Z2 Z2_countMixin.
Definition ab_countMixin := CountMixin ab_count_spec.
Definition ab_choiceMixin := CountChoiceMixin ab_countMixin.
Canonical ab_choiceType := Eval hnf in ChoiceType ab ab_choiceMixin.
Canonical ab_countType := Eval hnf in CountType ab ab_countMixin.

(*型の一覧となるリストを定義*)
Definition enum_Z2 := [::zero;one].
Definition enum_ab := [::a;b].

(*各要素が重複なくリストに含まれることを示す*)
Lemma enum_Z2P :Finite.axiom enum_Z2.
Proof. rewrite/Finite.axiom=>x;by destruct x. Qed.
Lemma enum_abP :Finite.axiom enum_ab.
Proof. rewrite/Finite.axiom=>x;by destruct x. Qed.

(*finType属性を付与*)
Definition Z2_finMixin := FinMixin enum_Z2P.
Canonical Z2_finType := Eval hnf in FinType Z2 Z2_finMixin.
Definition ab_finMixin := FinMixin enum_abP.
Canonical ab_finType := Eval hnf in FinType ab ab_finMixin.

Definition p1_d(x:Z2)(y:ab):Z2 :=
match x,y with
|zero,a => zero
|zero,b => one
|one,a => one
|one,b => zero
end.
Definition p1 := Automaton Z2_finType ab_finType zero p1_d [set one].
Compute accept p1 [::b;b;b].


















