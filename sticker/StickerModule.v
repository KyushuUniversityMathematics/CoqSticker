From mathcomp Require Import all_ssreflect.
(*ProofIrrelevanceは同じ言明ならば異なる証明も同じとみなす*)
Require Import myLemma ProofIrrelevance.

(*対象関係の定義*)
Definition Rho(symbol:finType):=seq(symbol*symbol).

(*二本鎖部分の構造体を定義
文字列情報を持ち、空で無いこと、対象関係を満たしていることを要求する*)
Structure wk{symbol:finType}{rho:Rho symbol} := Wk{
  str : seq (symbol*symbol);
  nilP : str <> nil;
  rhoP : all(fun p=>p\in rho)str
}.
(*粘着末端の定義　上側鎖かどうかと文字列の情報を持ち、文字が空でないことを要求する*)
Structure stickyend{symbol:finType}:= Se{
  is_upper : bool;
  end_str : seq symbol;
  end_nilP : end_str <> nil
}.
(*ドミノを定義　二本鎖部分と粘着末端、もしくは空白部の組み合わせからなる*)
Inductive domino{symbol:finType}{rho:Rho symbol}:=
|null : domino
|Simplex : @stickyend symbol -> domino
|WK : @wk symbol rho -> domino
|L : @stickyend symbol -> @wk symbol rho -> domino
|R : @wk symbol rho -> @stickyend symbol -> domino
|LR : @stickyend symbol -> @wk symbol rho -> @stickyend symbol -> domino.

(*#########################################################################*)
(*ドミノにeqType属性を付与する*)
Definition wk_eqb{symbol:finType}{rho:Rho symbol}(x y:@wk symbol rho):bool:=
str x == str y.
Lemma eq_wkP{symbol:finType}{rho:Rho symbol}:
Equality.axiom (@wk_eqb symbol rho).
Proof.
move=>a b;rewrite/wk_eqb;apply/(iffP idP);[|move=>ab;by rewrite ab].
move/eqP.
destruct a,b.
simpl=>H.
subst.
f_equal.
apply/proof_irrelevance.
apply/eq_irrelevance.
Qed.
Canonical wk_eqMixin{f:finType}{rho:Rho f} := EqMixin (@eq_wkP f rho).
Canonical wk_eqType{symbol:finType}{rho:Rho symbol} := 
  Eval hnf in EqType _ (@wk_eqMixin symbol rho).
Definition end_eqb{symbol:finType}(x y:@stickyend symbol):bool:=
match x,y with
|Se true s1 _,Se true s2 _ => s1==s2
|Se false s1 _,Se false s2 _ => s1==s2
|_,_ => false
end.
Lemma eq_endP{symbol:finType}:Equality.axiom(@end_eqb symbol).
Proof.
move=>x y;rewrite/end_eqb;apply/(iffP idP).
destruct x,y.
case:is_upper0;case:is_upper1;[|done|done|];
move/eqP=>H;subst;f_equal;apply/proof_irrelevance.
move=>H.
subst.
case:y;case=>H _;by apply/eqP.
Qed.
Canonical end_eqMixin{symbol:finType} := EqMixin (@eq_endP symbol).
Canonical end_eqType{f:finType}:= Eval hnf in EqType _ (@end_eqMixin f).
Lemma domino_eq_dec{symbol:finType}{rho:Rho symbol}(x y:@domino symbol rho):
{x=y}+{x<>y}.
Proof.
decide equality.
case_eq(s==s0);move/eqP=>H;by [left|right].
case_eq(w==w0);move/eqP=>H;by [left|right].
case_eq(w==w0);move/eqP=>H;by [left|right].
case_eq(s==s0);move/eqP=>H;by [left|right].
case_eq(s==s0);move/eqP=>H;by [left|right].
case_eq(w==w0);move/eqP=>H;by [left|right].
case_eq(s0==s2);move/eqP=>H;by [left|right].
case_eq(w==w0);move/eqP=>H;by [left|right].
case_eq(s==s1);move/eqP=>H;by [left|right].
Qed.
Definition domino_eqb{symbol:finType}{rho:Rho symbol}(x y:@domino symbol rho):=
match domino_eq_dec x y with |left _=> true|_=> false end.
Lemma eq_dominoP{symbol:finType}{rho:Rho symbol}:
Equality.axiom (@domino_eqb symbol rho).
Proof. move=>a b;rewrite/domino_eqb;apply/(iffP idP);
by case:(domino_eq_dec a b). Qed.
Canonical domino_eqMixin{f:finType}{rho:Rho f} := EqMixin (@eq_dominoP f rho).
Canonical domino_eqType{symbol:finType}{rho:Rho symbol} := 
  Eval hnf in EqType _ (@domino_eqMixin symbol rho).
(*##########################################################################*)


(*粘着末端同士の粘着を定義　特定の条件を満たしたときのみwk(二本鎖構造)となる*)
(*DNAで言うとアニーリングに対応*)
Lemma cons_nilP{t:Type}(a:t)(l:seq t):a::l<>nil. Proof. done. Qed.
Definition mu_end{symbol:finType}(rho:Rho symbol)(x y:seq symbol):option wk:=
match zip x y with
|nil => None
|a::l=> match Bool.bool_dec(all(fun p=>p\in rho)(a::l)) true with
  |left H => Some{|str:=a::l;nilP:=cons_nilP a l;rhoP := H|}
  |right _=> None
  end
end.
Definition zip'{t:Type}(x y:seq t):seq(t*t):=rev(zip(rev x)(rev y)).
Definition mu_end'{symbol:finType}(rho:Rho symbol)(x y:seq symbol):option wk:=
match zip' x y with
|nil => None
|a::l=> match Bool.bool_dec(all(fun p=>p\in rho)(a::l)) true with
  |left H => Some{|str:=a::l;nilP:=cons_nilP a l;rhoP := H|}
  |right _=> None
  end
end.



(*同じ側の粘着末端同士の結合　DNAのライゲーション*)
Lemma cat00{t:Type}(x y:seq t):x++y=nil<->x=nil/\y=nil.
Proof. by split;[case:x;case:y|case=>x' y';rewrite x' y']. Qed.
Lemma mu_end2_nilP{symbol:finType}(x y:@stickyend symbol):
end_str x++end_str y<>nil.
Proof. rewrite cat00;case=>x'_;by move:(end_nilP x). Qed.
Definition mu_end2{symbol:finType}(x y:@stickyend symbol):option stickyend:=
match x,y with
|Se true _ _,Se true _ _ =>Some
{|is_upper:=true;end_str:=end_str x++end_str y;end_nilP:=mu_end2_nilP x y|}
|Se false _ _,Se false _ _ =>Some
{|is_upper:=false;end_str:=end_str x++end_str y;end_nilP:=mu_end2_nilP x y|}
|_,_=>None
end.

(*wk同士の結合を定義　DNAでのライゲーションが近い*)
Lemma mu_nilP{symbol:finType}{rho:Rho symbol}(x y:@wk symbol rho):
str x++str y<>nil.
Proof. rewrite cat00;case=>x'_;by move:(nilP x). Qed.
Lemma mu_rhoP{symbol:finType}{rho:Rho symbol}(x y:@wk symbol rho):
all(fun p=>p\in rho)(str x++str y).
Proof. rewrite all_cat;apply/andP;by move:(rhoP x)(rhoP y). Qed.
Definition mu_wk{symbol:finType}{rho:Rho symbol}(x y:@wk symbol rho):=
{|str := (str x ++ str y);nilP := (mu_nilP x y);rhoP := (mu_rhoP x y)|}.
Notation "x # y" := (mu_wk x y)(at level 1,left associativity).

(*ドミノの結合演算を考える際、新たにできる粘着末端が空でないことを示すための補題*)
Lemma takenil{t:Type}{x y:seq t}:size x<size y -> take(size y-size x)y<>nil.
Proof.
rewrite/not=>H H1.
have{H1}:size(take(size y - size x)y)=0.
by rewrite H1.
rewrite size_take ltn_subrL.
case:((0 < size x) && (0 < size y)).
move/lesub.
by rewrite leqNgt H.
by destruct y.
Qed.
Lemma dropnil{t:Type}{x y:seq t}:size x<size y ->drop(size x)y<>nil.
Proof.
rewrite/not=>H H1.
have{H1}:size(drop(size x)y)=0.
by rewrite H1.
by rewrite size_drop-lesub leqNgt H.
Qed.

(*一本鎖のドミノ（Simplex）を結合させる際、新たに生成される粘着末端を出力*)
Definition mu_endr{symbol:finType}(x y:seq symbol):=
match nat_compare(size x)(size y)with
|inleft(left P) =>
  Some{|
    is_upper:=false;
    end_str:=take(size y-size x)y;
    end_nilP:=takenil P
  |}
|inleft(right _)=> None
|inright P =>
  Some{|
    is_upper:=false;
    end_str:=take(size x-size y)x;
    end_nilP:=takenil P
  |}
end.
Definition mu_endl{symbol:finType}(x y:seq symbol):=
match nat_compare(size x)(size y)with
|inleft(left P) =>
  Some{|
    is_upper:=false;
    end_str:=drop(size x)y;
    end_nilP:=dropnil P
  |}
|inleft(right _)=> None
|inright P =>
  Some{|
    is_upper:=false;
    end_str:=drop(size y)x;
    end_nilP:=dropnil P
  |}
end.

(*ドミノの粘着演算を定義　粘着しない組み合わせはNoneを返す*)
Definition mu{symbol:finType}{rho:Rho symbol}(x y:@domino symbol rho):=
match x,y with
|null,_ => Some y
|_,null => Some x
|Simplex s1,WK w2 => Some (L s1 w2)
|Simplex (Se true l1 P1),L (Se true l2 P2) w2=>
  match mu_end2(Se _ true l1 P1)(Se _ true l2 P2) with
  |Some s => Some(L s w2)
  |None => None
  end
|Simplex (Se false l1 P1),L (Se false l2 P2) w2=>
  match mu_end2(Se _ false l1 P1)(Se _ false l2 P2) with
  |Some s => Some(L s w2)
  |None => None
  end
|Simplex (Se true l1 _),L (Se false l2 _) w2=>
  match mu_end' rho l1 l2 with
  |Some w =>
    match mu_endr l1  l2 with
    |Some s => Some(L s w#w2)
    |None => Some(WK w#w2)
    end
  |None => None
  end
|Simplex (Se false l1 _),L (Se true l2 _) w2=>
  match mu_end' rho l2 l1 with
  |Some w =>
    match mu_endr l2 l1 with
    |Some s => Some(L s w#w2)
    |None => Some(WK w#w2)
    end
  |None => None
  end
|Simplex s1,R w2 r2 => Some (LR s1 w2 r2)
|Simplex (Se true l1 P1),LR (Se true l2 P2) w2 r2=>
  match mu_end2(Se _ true l1 P1)(Se _ true l2 P2) with
  |Some s => Some(LR s w2 r2)
  |None => None
  end
|Simplex (Se false l1 P1),LR (Se false l2 P2) w2 r2=>
  match mu_end2(Se _ false l1 P1)(Se _ false l2 P2) with
  |Some s => Some(LR s w2 r2)
  |None => None
  end
|Simplex (Se true l1 _),LR (Se false l2 _) w2 r2=>
  match mu_end' rho l1 l2 with
  |Some w =>
    match mu_endr l1  l2 with
    |Some s => Some(LR s w#w2 r2)
    |None => Some(WK w#w2)
    end
  |None => None
  end
|Simplex (Se false l1 _),LR (Se true l2 _) w2 r2=>
  match mu_end' rho l2 l1 with
  |Some w =>
    match mu_endr l2 l1 with
    |Some s => Some(LR s w#w2 r2)
    |None => Some(WK w#w2)
    end
  |None => None
  end
|WK w1,Simplex s2 => Some (R w1 s2)
|WK w1,WK w2 => Some (WK w1#w2)
|WK w1,R w2 r2 => Some (R w1#w2 r2)
|L l1 w1,Simplex s2 => Some (LR l1 w1 s2)
|L l1 w1,WK w2 => Some (L l1 w1#w2)
|L l1 w1,R w2 r2 => Some (LR l1 w1#w2 r2)
|R w1 (Se true r1 P1),Simplex (Se true l2 P2)=>
  match mu_end2(Se _ true r1 P1)(Se _ true l2 P2) with
  |Some s => Some(R w1 s)
  |None => None
  end
|R w1 (Se false r1 P1),Simplex (Se false l2 P2)=>
  match mu_end2(Se _ false r1 P1)(Se _ false l2 P2) with
  |Some s => Some(R w1 s)
  |None => None
  end
|R w1 (Se true r1 _),Simplex (Se false l2 _)=>
  match mu_end rho r1 l2 with
  |Some w =>
    match mu_endr r1 l2 with
    |Some s => Some(R w1#w s)
    |None => Some(WK w1#w)
    end
  |None => None
  end
|R w1 (Se false r1 _),Simplex (Se true l2 _)=>
  match mu_end rho l2 r1 with
  |Some w =>
    match mu_endr l2 r1 with
    |Some s => Some(R w1#w s)
    |None => Some(WK w1#w)
    end
  |None => None
  end
|R w1 (Se true r1 _),L (Se false l2 _) w2 =>
  if size r1 == size l2 then
    match mu_end rho r1 l2 with
    |Some w => Some (WK w1#w#w2)
    |None => None
    end
  else
      None
|R w1 (Se false r1 _),L (Se true l2 _) w2 =>
  if size r1 == size l2 then
    match mu_end rho l2 r1 with
    |Some w => Some (WK w1#w#w2)
    |None => None
    end
  else
      None
|R w1 (Se true r1 _),LR (Se false l2 _) w2 r2 =>
  if size r1 == size l2 then
    match mu_end rho r1 l2 with
    |Some w => Some (R w1#w#w2 r2)
    |None => None
    end
  else
      None
|R w1 (Se false r1 _),LR (Se true l2 _) w2 r2 =>
  if size r1 == size l2 then
    match mu_end rho l2 r1 with
    |Some w => Some (R w1#w#w2 r2)
    |None => None
    end
  else
      None
|LR l1 w1 (Se true r1 P1),Simplex (Se true l2 P2)=>
  match mu_end2(Se _ true r1 P1)(Se _ true l2 P2) with
  |Some s => Some(LR l1 w1 s)
  |None => None
  end
|LR l1 w1 (Se false r1 P1),Simplex (Se false l2 P2)=>
  match mu_end2(Se _ false r1 P1)(Se _ false l2 P2) with
  |Some s => Some(LR l1 w1 s)
  |None => None
  end
|LR l1 w1 (Se true r1 _),Simplex (Se false l2 _)=>
  match mu_end rho r1 l2 with
  |Some w =>
    match mu_endr r1 l2 with
    |Some s => Some(LR l1 w1#w s)
    |None => Some(L l1 w1#w)
    end
  |None => None
  end
|LR l1 w1 (Se false r1 _),Simplex (Se true l2 _)=>
  match mu_end rho l2 r1 with
  |Some w =>
    match mu_endr l2 r1 with
    |Some s => Some(LR l1 w1#w s)
    |None => Some(L l1 w1#w)
    end
  |None => None
  end
|LR l1 w1 (Se true r1 _),L (Se false l2 _) w2 =>
  if size r1 == size l2 then
    match mu_end rho r1 l2 with
    |Some w => Some (L l1 w1#w#w2)
    |None => None
    end
  else
      None
|LR l1 w1 (Se false r1 _),L (Se true l2 _) w2 =>
  if size r1 == size l2 then
    match mu_end rho l2 r1 with
    |Some w => Some (L l1 w1#w#w2)
    |None => None
    end
  else
      None
|LR l1 w1 (Se true r1 _),LR (Se false l2 _) w2 r2 =>
  if size r1 == size l2 then
    match mu_end rho r1 l2 with
    |Some w => Some (LR l1 w1#w#w2 r2)
    |None => None
    end
  else
      None
|LR l1 w1 (Se false r1 _),LR (Se true l2 _) w2 r2 =>
  if size r1 == size l2 then
    match mu_end rho l2 r1 with
    |Some w => Some (LR l1 w1#w#w2 r2)
    |None => None
    end
  else
      None
|_,_ => None
end.

(*ドミノAに対し、ドミノ対（B,C）を順に結合させ、ドミノBACを生成　結合しない場合はNone*)
Definition mu'{symbol:finType}{rho:Rho symbol}
(x:@domino symbol rho)(y:@domino symbol rho*@domino symbol rho):=
let (d1,d2) := y in
match mu d1 x with
|Some d => mu d d2
|None => None
end.

(*スティッカーシステムの開始ドミノは二本鎖部分を持つ必要がある。その判定関数*)
Definition st_correct{symbol:finType}{rho:Rho symbol}(x:@domino symbol rho):=
match x with
|WK _ => true
|L _ _ => true
|R _ _ => true
|LR _ _ _ => true
|_ => false
end.
(*スティッカーの定義　開始ドミノとそこに結合させていくドミノ対の情報を持ち、
開始ドミノが二本鎖部分を持つ証明を要求する*)
Structure sticker{symbol:finType}{rho:Rho symbol}:= Sticker{
  start : seq (@domino symbol rho);
  extend : seq (@domino symbol rho*@domino symbol rho);
  startP : all st_correct start
}.

Open Scope nat_scope.
(*ドミノがWK、すなわち粘着末端を持たないかどうかの判定関数*)
Definition is_wk{symbol:finType}{rho:Rho symbol}(x:@domino symbol rho):bool:=
match x with WK _ => true|_ => false end.

(*スティッカーシステムでnステップ進めた際のドミノ群を求める関数
原始的な計算、すなわち粘着末端を持たないドミノを計算から除外している*)
Fixpoint ss_generate_prime{symbol:finType}{rho:Rho symbol}
(n:nat)(stk:@sticker symbol rho):seq domino:=
match n with
|0 => start stk
|S n' =>
  let A' := ss_generate_prime n' stk in
  let A_wk := [seq a <- A'|is_wk a] in
  let A_nwk := [seq a <- A'|~~ is_wk a] in
  undup(A_wk++filter_option[seq mu' a d|a<-A_nwk,d <- (extend stk)])
end.

(*ドミノから文字列を抽出する　単に上側鎖を読み取るが、粘着末端を持つ場合は空文字で返す*)
Definition decode{symbol:finType}{rho:Rho symbol}(d:@domino symbol rho):=
match d with|WK (Wk w _ _) => unzip1 w|_ => nil end.

(*nステップ進めた際にスティッカーシステムが生成できる言語族を返す関数*)
Definition ss_language_prime{symbol:finType}{rho:Rho symbol}(n:nat)
(stk:@sticker symbol rho):seq (seq symbol) :=
[seq decode d | d <- ss_generate_prime n stk & is_wk d].


(*以下はstickerと直接関係ないもの*)
(*粘着末端を生成する関数　空文字だと粘着末端にならないが、
頭文字を別入力として要求することで回避している*)
Definition mkend{symbol:finType}(b:bool)(a:symbol)(s:seq symbol):stickyend :=
{|is_upper:=b;end_str:=a::s;end_nilP:=cons_nilP a s|}.

(*同じ文字同士のみの対称関係、すなわちaはaと、bはbとのみ結合するようにrhoを定義した場合、
上下同じ文字列のドミノを生成できる。*)
Lemma zip_rhoP{symbol:finType}(s:seq symbol):
all(fun p=>p\in(zip(enum symbol)(enum symbol)))(zip s s).
Proof.
elim:s.
done.
move=>a l H.
rewrite/=H Bool.andb_true_r=>{l H}.
have:a\in enum symbol.
apply/mem_enum.
elim:(enum symbol).
done.
move=>b l H.
rewrite/=!in_cons.
move/orP.
case.
move/eqP=>H1.
subst.
apply/orP.
left.
by apply/eqP.
move/H=>{}H.
apply/orP.
by right.
Qed.
Lemma cons_zip_nilP{symbol:finType}(a:symbol)(s:seq symbol):
zip (a::s) (a::s) <> nil.
Proof. done. Qed.
Definition mkwkzip{symbol:finType}(a:symbol)(s:seq symbol):wk :=
{|str:=zip(a::s)(a::s);nilP:=cons_zip_nilP a s;rhoP:=zip_rhoP(a::s)|}.
Definition mkWK{symbol:finType}(s:seq symbol):option domino:=
match s with
|nil => None
|a::s' => Some(WK(mkwkzip a s'))
end.













