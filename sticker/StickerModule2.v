From mathcomp Require Import all_ssreflect.

(*ドミノの定義　nullはエラー型で、通常のドミノは二本のリストと2つのnatで表現*)
Inductive domino{symbol:finType}:=
|null : domino
|Domino :seq symbol -> seq symbol -> nat -> nat -> domino.



(*ドミノにeqTypeを付ける。ドミノに==の関数を適用できるように*)
Definition eqb_domino{s:finType}(d1 d2:@domino s):bool :=
match d1,d2 with
|null,null => true
|Domino l1 r1 x1 y1,Domino l2 r2 x2 y2 =>
  (l1==l2)&&(r1==r2)&&(x1==x2)&&(y1==y2)
|_,_ => false
end.
Lemma eq_dominoP{s:finType}:Equality.axiom (@eqb_domino s).
Proof. move=>a b;rewrite/eqb_domino;apply/(iffP idP);case:a;case:b.
done.
done.
done.
move=>l l0 n n0 l1 l2 n1 n2.
move/andP=>[H]/eqP=>H1.
move:H;move/andP=>[/andP H]/eqP=>H2.
move:H=>[/eqP H3 /eqP H4].
congruence.
done.
done.
done.
move=>l l0 n n0 l1 l2 n1 n2.
move=>[H H1 H2 H3].
apply/andP.
split;[|apply/eqP/H3].
apply/andP.
split;[|apply/eqP/H2].
apply/andP.
split;[apply/eqP/H|apply/eqP/H1].
Qed.
Canonical domino_eqMixin{symbol:finType} := EqMixin (@eq_dominoP symbol).
Canonical domino_eqType{symbol:finType} := 
  Eval hnf in EqType _ (@domino_eqMixin symbol).

(*ドミノの粘着演算　粘着できない組み合わせはnullとなる*)
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

(*ドミノに対し、ドミノ対を左右から挟み込むように粘着させる*)
Definition mu'{s:finType}(a:@domino s)(d:@domino s*@domino s):@domino s:=
let (d1,d2) := d in mu (mu d1 a) d2.

(*ドミノの両端が揃っていること、
上側鎖と下側鎖が相補的関係(rho)で対応付けられているかのチェック*)
Definition wk{s:finType}(rh:seq (s*s))(d:@domino s):bool :=
match d with
|Domino l r 0 0 =>
  if size l == size r then
    all(fun p=>p\in rh)(zip l r)
  else
    false
|_ => false
end.

(*スティッカー本体 これ自体はデータの塊で、計算機能は別で定義する*)
Structure sticker{symbol:finType}:= Sticker{
  rho : seq (symbol*symbol);
  start : seq (@domino symbol);
  extend : seq (@domino symbol*@domino symbol)
}.

(*ドミノをn回作用させた際に作られ得るドミノの一覧*)
Fixpoint ss_generate{symbol:finType}(n:nat)(stk:@sticker symbol):seq domino:=
match n with
|0 => start stk
|S n' => let A' := ss_generate n' stk in
  A'++[seq mu' a d|a<-A',d <- (extend stk)]
end.

(*原始的な計算(粘着末端が消えたら計算終了)に限ったバージョン*)
Fixpoint ss_generate_prime{s:finType}(n:nat)(stk:@sticker s):seq domino:=
match n with
|0 => start stk
|S n' =>
  let A' := ss_generate_prime n' stk in
  let A_wk := [seq a<-A'|wk (rho stk) a] in
  let A_nwk := [seq a<-A'|~~ wk (rho stk) a] in
  A_wk++[seq mu' a d|a<-A_nwk,d <- (extend stk)]
end.

(*ドミノからのコーディング　上側鎖の文字列情報を読み取る*)
Definition ss_language_f{s:finType}(d:@domino s):seq s :=
match d with
|Domino l _ _ _ => l
|_ => nil
end.

(*stickerがn回の作用で生成できる言語一覧*)
Definition ss_language{s:finType}(n:nat)(stk:@sticker s):seq (seq s) :=
[seq ss_language_f d | d <- [seq d <- ss_generate n stk|wk (rho stk) d]].

(*原始的な計算ver.*)
Definition ss_language_prime{s:finType}(n:nat)(stk:@sticker s):seq (seq s) :=
[seq ss_language_f d | d <- [seq d <- ss_generate_prime n stk|wk (rho stk) d]].