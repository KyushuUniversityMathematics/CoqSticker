From mathcomp Require Import all_ssreflect.
Require Import Arith ProofIrrelevance.

Definition Rho(symbol:finType):=seq(symbol*symbol).
Structure wk{symbol:finType}{rho:Rho symbol} := Wk{
  str : seq (symbol*symbol);
  nilP : str <> nil;
  rhoP : all(fun p=>p\in rho)str
}.
Structure stickyend{symbol:finType}:= Se{
  is_upper : bool;
  end_str : seq symbol;
  end_nilP : end_str <> nil
}.
Inductive domino{symbol:finType}{rho:Rho symbol}:=
|null : domino
|Simplex : @stickyend symbol -> domino
|WK : @wk symbol rho -> domino
|L : @stickyend symbol -> @wk symbol rho -> domino
|R : @wk symbol rho -> @stickyend symbol -> domino
|LR : @stickyend symbol -> @wk symbol rho -> @stickyend symbol -> domino.

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

Lemma cons_nilP{t:Type}(a:t)(l:seq t):a::l<>nil. Proof. done. Qed.

Definition mu_end{symbol:finType}(rho:Rho symbol)(x y:seq symbol):option wk:=
match zip x y with
|nil => None
|a::l=> match Bool.bool_dec(all(fun p=>p\in rho)(a::l)) true with
  |left H => Some{|str:=a::l;nilP:=cons_nilP a l;rhoP := H|}
  |right _=> None
  end
end.

Lemma cat00{t:Type}(x y:seq t):x++y=nil<->x=nil/\y=nil.
Proof. by split;[case:x;case:y|case=>x' y';rewrite x' y']. Qed.
Lemma mu_nilP{symbol:finType}{rho:Rho symbol}(x y:@wk symbol rho):
str x++str y<>nil.
Proof. rewrite cat00;case=>x'_;by move:(nilP x). Qed.
Lemma mu_rhoP{symbol:finType}{rho:Rho symbol}(x y:@wk symbol rho):
all(fun p=>p\in rho)(str x++str y).
Proof. rewrite all_cat;apply/andP;by move:(rhoP x)(rhoP y). Qed.
Definition mu_wk{symbol:finType}{rho:Rho symbol}(x y:@wk symbol rho):=
{|str := (str x ++ str y);nilP := (mu_nilP x y);rhoP := (mu_rhoP x y)|}.

Lemma mu_wkA{symbol:finType}{rho:Rho symbol}:associative (@mu_wk symbol rho).
move=>x y z;apply/eqP;rewrite/mu_wk/=/eq_op/=/wk_eqb/=catA;by apply/eqP. Qed.
Notation "x # y" := (mu_wk x y)(at level 1,left associativity).

Definition mu{symbol:finType}{rho:Rho symbol}(x y:@domino symbol rho):=
match x,y with
|null,_ => Some y
|_,null => Some x
|Simplex s1,WK w2 => Some (L s1 w2)
|Simplex s1,R w2 r2 => Some (LR s1 w2 r2)
|WK w1,Simplex s2 => Some (R w1 s2)
|WK w1,WK w2 => Some (WK w1#w2)
|WK w1,R w2 r2 => Some (R w1#w2 r2)
|L l1 w1,Simplex s2 => Some (LR l1 w1 s2)
|L l1 w1,WK w2 => Some (L l1 w1#w2)
|L l1 w1,R w2 r2 => Some (LR l1 w1#w2 r2)
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

Definition mu'{symbol:finType}{rho:Rho symbol}
(x:@domino symbol rho)(y:@domino symbol rho*@domino symbol rho):=
let (d1,d2) := y in
match mu d1 x with
|Some d => mu d d2
|None => None
end.
Fixpoint filter_option{T:Type}(s:seq (option T)):seq T:=
match s with
|nil => nil
|Some t::s' => t::(filter_option s')
|None::s' => filter_option s'
end.

Definition st_correct{symbol:finType}{rho:Rho symbol}(x:@domino symbol rho):=
match x with
|WK _ => true
|L _ _ => true
|R _ _ => true
|LR _ _ _ => true
|_ => false
end.
Structure sticker{symbol:finType}{rho:Rho symbol}:= Sticker{
  start : seq (@domino symbol rho);
  extend : seq (@domino symbol rho*@domino symbol rho);
  startP : all st_correct start
}.

Open Scope nat_scope.
Definition is_wk{symbol:finType}{rho:Rho symbol}(x:@domino symbol rho):bool:=
match x with WK _ => true|_ => false end.
Fixpoint ss_generate_prime{symbol:finType}{rho:Rho symbol}
(n:nat)(stk:@sticker symbol rho):seq domino:=
match n with
|0 => start stk
|S n' =>
  let A' := ss_generate_prime n' stk in
  let A_wk := [seq a <- A'|is_wk a] in
  let A_nwk := [seq a <- A'|~~ is_wk a] in
  A_wk++filter_option[seq mu' a d|a<-A_nwk,d <- (extend stk)]
end.
Definition decode{symbol:finType}{rho:Rho symbol}(d:@domino symbol rho):=
match d with|WK (Wk w _ _) => unzip1 w|_ => nil end.
Definition ss_language_prime{symbol:finType}{rho:Rho symbol}(n:nat)
(stk:@sticker symbol rho):seq (seq symbol) :=
[seq decode d | d <- ss_generate_prime n stk & is_wk d].


(*以下はstickerと直接関係ないもの*)
Definition mkend{symbol:finType}(b:bool)(a:symbol)(s:seq symbol):stickyend :=
{|is_upper:=b;end_str:=a::s;end_nilP:=cons_nilP a s|}.
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













