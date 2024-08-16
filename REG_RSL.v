
From mathcomp Require Import all_ssreflect.

Require Import myAutomaton mySticker myTheorems Arith.

Fixpoint language(n:nat)(symbol:finType):seq (seq symbol):=
match n with
|0 => [::nil]
|S n' => [seq s::l|l<-language n' symbol,s<-enum symbol]
end.

Fixpoint language' (n:nat)(symbol:finType):seq (seq symbol):=
(*1文字以上n文字以下の文字列を生成
Ex:language 2 [::"a"%char;"b"%char] -> [::"a";"b";"aa";"ab";"ba;";"bb"]*)
match n with
|0 => [::]
|S n' => app (language' n' symbol) (language n symbol)
end.

Lemma add_subABB(m n:nat):m+n-n=m.
Proof.
elim:n.
by rewrite addn0 subn0.
move=>n H.
by rewrite addnS subSS.
Qed.
Lemma add_subABA(m n:nat):n+m-n=m.
Proof.
elim:n.
by rewrite add0n subn0.
move=>n H.
by rewrite addSn subSS.
Qed.

Definition startDomino{state symbol:finType}(M:@automaton state symbol)
(s:seq symbol):domino :=
Domino s(take(size s-(index(dstar(delta M)(init M)s)(enum state)+1)) s) 0 0.
Definition extentionDomino{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol):(@domino symbol)*(@domino symbol):=
let s0 := nth (init M) (enum state) (size t - 1) in
let n := index (dstar (delta M) s0 s) (enum state) + 1 in
(Domino nil nil 0 0,Domino s (t++(take (size s - n) s)) 0 (size t)).
Definition stopDomino{symbol:finType}(s t:seq symbol):
(@domino symbol)*(@domino symbol) :=
(Domino nil nil 0 0,Domino s (t++s) 0 (size t)).

(*Definition startDomino{symbol:finType}(n:nat)(s:seq symbol):domino :=
Domino s (take (size s - n) s) 0 0.
(*
Definition startDomino_inverse (d:Domino):nat*string:=
let '(s,t,_,_) := d in
(length s - length t,s).
Lemma startDominoCollect (n:nat)(s:string):
n<=length s->startDomino_inverse (startDomino n s) = (n,s).
Proof. move=>H;apply/pair_equal_spec;split;[|done];rewrite substringlemma2;
[by rewrite subKn|rewrite add0n;apply/leq_subr]. Qed.*)
Definition extentionDomino{symbol:finType}(n:nat)(s t:seq symbol):
(@domino symbol)*(@domino symbol):=
(Domino nil nil 0 0,Domino s (t++(take (size s - n) s)) 0 (size t)).
(*
Definition extentionDomino_inverse (D:Domino*Domino):nat*string*string:=
let '((_,_,_,_),(s,t,_,n)) := D in
(length s + n - length t,s,substring 0 n t).
Lemma extentionDominoCollect (n:nat)(s t:string):
n<=length s -> extentionDomino_inverse (extentionDomino n s t) = (n,s,t).
Proof.
move=>H;apply/pair_equal_spec;split.
apply/pair_equal_spec;split;[|done].
rewrite stringlength.
rewrite subnDA.
rewrite substringlemma2.
rewrite-addnBA;[|by[]].
rewrite subnn.
rewrite addn0.
by rewrite subKn.
rewrite add0n.
apply/leq_subr.
elim:t.
simpl.
apply substringn0.
move=>a t H1.
simpl.
by f_equal. Qed.*)
Definition stopDomino{symbol:finType}(s t:seq symbol):
  (@domino symbol)*(@domino symbol) :=
(Domino nil nil 0 0,Domino s (t++s) 0 (size t)).

(*Definition stopDomino_inverce (D:Domino*Domino):string*string :=
let '((_,_,_,_),(s,t,_,n)) := D in
(s,substring 0 n t).
Lemma stopDominoCollect (s t:string):
stopDomino_inverce (stopDomino s t) = (s,t).
Proof.
apply/pair_equal_spec;split;[done|].
elim:t.
apply substringn0.
move=>a t H.
simpl.
by f_equal. Qed.*)*)

(*Definition dstar_num{state symbol:finType}(n:nat)(s:seq symbol)
(M:@automaton state symbol):nat :=
index (dstar (delta M) (nth (init M) (enum state) (n-1)) s) (enum state) + 1.*)
Definition Aut_to_Stk{state symbol:finType}(M:@automaton state symbol):sticker:=
let k := #|state| in
let l := language (k+1) symbol in
let A1 := [seq Domino l' l' 0 0|l'<- 
            [seq str<-(language'(k+1)symbol)|accept M str]] in
let A2 := [seq startDomino M s|s <- l] in
let l' := language' k symbol in
let D1 := [seq extentionDomino M s t|s<-l,t<-l'] in
let D2 := [seq stopDomino s t|t <- l',
  s <-[seq str<-language'(k+1)symbol|
    dstar(delta M)(nth(init M)(enum state)(size t-1))str\in (final M)]] in
Sticker symbol (zip(enum symbol)(enum symbol)) (A1++A2) (D1++D2).

Lemma lang_gen{state symbol:finType}(M:@automaton state symbol)(s:seq symbol)
(n:nat):(s\in (ss_language_prime n (Aut_to_Stk M))) 
 = ((Domino s s 0 0)\in ss_generate_prime n (Aut_to_Stk M)).
Proof.
simpl.
apply/bool_eqsplit.
split.
rewrite/ss_language_prime.
elim(ss_generate_prime n (Aut_to_Stk M)).
done.
move=>a l H {n}.
simpl.
case H1:(wk (zip (enum symbol) (enum symbol)) a);
[simpl|move/H=>{}H;apply/orP;by right].
rewrite!in_cons.
move/orP.
case;[move/eqP=>{}H;apply/orP;left;apply/eqP|move/H=>{}H;apply/orP;by right].
move:H1 H {l state M}.
case:a.
done.
move=>l r x y.
case:x;case:y;[|done|done|done].
simpl.
case_eq(size l == size r);[move/eqP|done].
move=>H H1 H2.
f_equal.
done.
rewrite H2=>{H2}.
move:{s}r H H1.
elim:l.
by case.
move=>a l H.
case.
done.
move=>b r.
simpl.
move=>[H1].
move/andP=>[H2].
have{}H2:a=b.
move:H2.
elim:(enum symbol).
done.
move=>d e H2.
simpl.
rewrite in_cons.
move/orP.
case;[move/eqP=>[];congruence|apply/H2].
rewrite-H2=>{}H2.
f_equal.
by apply/H.

rewrite{3}(_:s=ss_language_f (Domino s s 0 0));[move=>H|done].
apply/map_f.
rewrite mem_filter.
apply/andP.
split;[|done].
simpl=>{state M n H}.
rewrite(_:size s == size s=true);[|by elim:s].
elim:s.
done.
move=>a s H.
simpl.
apply/andP.
split;[move=>{s H}|done].
have:a\in (enum symbol).
apply/mem_enum.
elim:(enum symbol).
done.
move=>h l H.
simpl.
rewrite!in_cons.
move/orP.
case.
move/eqP=>{}H.
apply/orP;left;apply/eqP;by f_equal.
move/H=>{}H;apply/orP;by right.
Qed.

Lemma languagelemma{V:finType}(s:seq V):s\in (language (size s) V).
Proof. by elim:s;[|move=>a l H;simpl;apply/map_f';[|apply/mem_enum]]. Qed.
Lemma language'lemma{f:finType}(s:seq f)(n:nat):
s<>nil -> size s <= n -> s \in language' n f.
Proof.
move=>H/subnKC=>H1.
rewrite-H1=>{H1}.
elim:(n - size s).
rewrite addn0.
rewrite/language'.
case_eq(size s).
move:H.
by case s.
move=>n0 H1.
rewrite mem_cat.
apply/orP.
right.
rewrite-H1.
apply/languagelemma.
move=>{H}n H.
rewrite addnS.
simpl.
rewrite mem_cat.
apply/orP.
by left.
Qed.

Lemma fin_index{f:finType}(a:f):index a (enum f) < #|f|.
Proof.
rewrite cardE.
have:a\in (enum f).
apply/mem_enum.
elim:(enum f).
done.
move=>f0 ef H.
rewrite in_cons.
move/orP.
case.
simpl.
move/eqP=>af0.
rewrite-af0=>{f0 af0}.
rewrite (_:a==a=true);[done|by apply/eqP].
move/H=>{}H.
simpl.
by case:(f0 == a).
Qed.
Lemma add00(m n:nat):m+n=0<->m=0/\n=0.
Proof.
split;[|move=>[m0 n0];by rewrite n0 addn0].
case:m;[by rewrite add0n|move=>m;by rewrite addSn].
Qed.
Lemma mu'lemma{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol):#|state|+1<=size s -> size t = #|state|+1 ->
mu' (startDomino M s)(extentionDomino M t (
  drop (size s - (index(dstar(delta M)(init M)s)(enum state)+1)) s
    ))=startDomino M (s++t).
Proof.
simpl.
case s':s;[by rewrite addn1|rewrite-s'].
case t':t;[by rewrite addn1|rewrite-t'].
remember (index(dstar(delta M)(init M)s)(enum state)+1) as n.
rewrite-Heqn.
move=>lens lent.
have lens':n<=#|state|.
rewrite Heqn!addn1.
apply/fin_index.
have{}lens':n<size s.
apply/(leq_ltn_trans lens').
by rewrite-addn1.

case s'':(take(size s-n)s);[|rewrite-s'' subn0].
have:size(take(size s-n)s)=0.
by rewrite s''.
rewrite size_take ltn_subrL 
(_:(0 < n) && (0 < size s)=true);[|by rewrite Heqn s' addn1].
move/lesub/leq_gtF.
by rewrite lens'.

simpl.
rewrite s'-s' s''-s'' t'-t'.
remember (index(dstar(delta M)(nth(init M)(enum state)
  (size (drop (size s - n) s) - 1))t)(enum state)+1) as m.
have lent':m<size t.
rewrite Heqm lent!addn1 ltnS.
apply/fin_index.
rewrite-Heqm.
case t'':((drop (size s - n) s) ++ take (size t - m) t);[|rewrite-t''=>{t''}].
have:size((drop (size s - n) s) ++ take (size t - m) t)=0.
by rewrite t''.
rewrite size_cat size_take ltn_subrL (_:(0 < m) && (0 < size t)=true);
[|by rewrite Heqm lent!addn1].
move/add00=>[_].
move/lesub/leq_gtF.
by rewrite lent'.

rewrite!add0n addn0-size_cat catA cat_take_drop (_:size s==size s=true);
[|by apply/eqP].
rewrite/startDomino dstarLemma.
move:Heqm.
rewrite size_drop (_:size s - (size s - n)=n);[|apply/subKn/ltnW/lens'].
rewrite Heqn!addn1 subn1-pred_Sn nth_index=>{n Heqn lens' s''};
[|apply/mem_enum]=>Heqm.
rewrite-Heqm take_cat size_cat (_:size s + size t - m < size s=false)=>{Heqm}.
f_equal;f_equal;f_equal.
by rewrite-(addBnAC _ (ltnW lent'))(add_subABB (size t - m) (size s)).
rewrite-addnBA.
apply/leq_gtF/leq_addr.
apply/ltnW/lent'.
Qed.


Lemma mu'lemma2{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol): #|state|+1<=size s -> t <> nil ->
mu' (startDomino M s)(stopDomino t 
  (drop (size s - (index(dstar(delta M)(init M)s)(enum state)+1)) s)
    ) = Domino (s++t)(s++t) 0 0.
Proof.
simpl.
case s':s;[by rewrite addn1|rewrite-s'].
case t':t;[by rewrite addn1|rewrite-t'].
remember (index(dstar(delta M)(init M)s)(enum state)+1) as n.
rewrite-Heqn.
move=>lens lent.
have lens':n<=#|state|.
rewrite Heqn!addn1.
apply/fin_index.
have{}lens':n<size s.
apply/(leq_ltn_trans lens').
by rewrite-addn1.

case s'':(take (size s - n) s);[|rewrite-s'' subn0].
have:size(take (size s - n) s)=0.
by rewrite s''.
rewrite size_take ltn_subrL 
(_:(0 < n) && (0 < size s)=true);[|by rewrite Heqn s' addn1].
move/lesub/leq_gtF.
by rewrite lens'.

simpl.
rewrite s'-s' s''-s'' t'-t'.
case t'':(drop (size s - n) s ++ t).
have:size(drop (size s - n) s ++ t)=0.
by rewrite t''.
rewrite size_cat.
rewrite t'.
simpl.
by rewrite addnS.
rewrite!add0n addn0-t''-size_cat catA cat_take_drop (_:size s==size s=true);
[done|by apply/eqP].
Qed.


Lemma startDomino_gen_prime{state symbol:finType}(M:@automaton state symbol)
(s:seq symbol)(n:nat):size s = n.+1*(#|state|+1) ->
startDomino M s\in ss_generate_prime n (Aut_to_Stk M).
Proof.
move:s.
elim:n.
rewrite mul1n=>s lens.
simpl.
rewrite mem_cat-lens.
apply/orP.
right.
apply/map_f/languagelemma.

move=>n H s.
rewrite-{2}(cat_take_drop (n.+1* (#|state| + 1)) s).
remember (take (n.+1 * (#|state| + 1)) s) as t.
remember (drop (n.+1 * (#|state| + 1)) s) as u.
move=>lens.
have lent:size t = n.+1 * (#|state| + 1).
rewrite Heqt size_take.
suff H1:n.+1 * (#|state| + 1) < size s.
by rewrite H1.
rewrite lens (mulSn n.+1) addn1 addSn ltnS.
apply/leq_addl.
have lenu:size u = (#|state| + 1).
by rewrite Hequ size_drop lens mulSn add_subABB.

move:(H _ lent)=>{}H.

rewrite-(mu'lemma M t u).
have H1:(ss_generate_prime n.+1 (Aut_to_Stk M)=
  [seq d<- ss_generate_prime n (Aut_to_Stk M)|wk (rho (Aut_to_Stk M)) d] ++
    [seq mu' a d|a<-
     [seq d<-ss_generate_prime n (Aut_to_Stk M)|~~wk (rho (Aut_to_Stk M)) d],
       d<-(extend (Aut_to_Stk M))]).
done.
rewrite H1.
rewrite mem_cat.
apply/orP.
right.
apply/map_f'.
rewrite mem_filter.
apply/andP.
split;[|done].
simpl.
rewrite size_take ltn_subrL
(_:(0<index(dstar(delta M)(init M)t)(enum state) + 1) && (0 < size t)=true).
case H2:(size t==size t-(index(dstar(delta M)(init M) t) (enum state) + 1)).
have:size t > size t - (index (dstar (delta M) (init M) t) (enum state) + 1).
rewrite ltn_subrL.
apply/andP.
split;[|rewrite lent];by rewrite addn1.
by rewrite-(eqP H2) ltnn.
done.
apply/andP.
split;[|rewrite lent];by rewrite addn1.

simpl.
rewrite mem_cat.
apply/orP.
left.
apply/map_f'.
rewrite-lenu.
apply/languagelemma.

remember(drop(size t-(index(dstar(delta M)(init M)t)(enum state)+1))t) as v.
rewrite-Heqv.

have lenv:size v<=#|state|.
rewrite Heqv size_drop subnA.
rewrite subnn add0n addn1.
apply/fin_index.
rewrite lent mulSn addn1.
apply/ltn_addr/ltn_addr.
apply/fin_index.
done.
have lenv':0<size v.
rewrite Heqv size_drop subnA.
by rewrite subnn add0n addn1.
rewrite lent mulSn addn1.
apply/ltn_addr/ltn_addr.
apply/fin_index.
done.
apply/language'lemma.
move:lenv'.
by case v.
done.
rewrite lent mulSn.
apply/leq_addr.
done.
Qed.


Lemma size_take_ne{T:Type}(n:nat)(s:seq T):s<>nil->
  size s <> size (take (size s - n.+1) s).
Proof.
rewrite/not=>H.
rewrite size_take ltn_subrL(_:(0 < n.+1) && (0 < size s)).
move:H.
case:s.
done.
simpl.
move=>_ l _.
rewrite subSS=>H.
have{}H:size l - n = (size l).+1.
by rewrite H.
move:(sub_ord_proof (size l) n).
by rewrite-H ltnn.
simpl.
move:H.
by case:s.
Qed.
Lemma take_ne{T:Type}(n:nat)(s:seq T):s<>nil->s <> take (size s - n.+1) s.
Proof.
move/(size_take_ne n).
rewrite/not=>H H1.
apply/H.
by rewrite-H1.
Qed.
Lemma filter_nil{e:eqType}(l:seq e)(P:e->bool):
[seq a<-[seq b <- l|P b]|~~P a]=nil.
Proof. by elim:l;[|move=>a l H;simpl;case H1:(P a);[rewrite/=H1|]]. Qed.

Lemma startDomino_gen_prime2{state symbol:finType}(M:@automaton state symbol)
(n:nat):[seq startDomino M s|s <- language (n.+1*(#|state|+1)) symbol] =i
  [seq d<-ss_generate_prime n (Aut_to_Stk M)|~~wk (rho (Aut_to_Stk M)) d].
Proof.
elim:n.
rewrite/=filter_cat.
have H:[seq d <- [seq Domino l' l' 0 0| l' <- language' (#|state| + 1) symbol
           & accept M l']| ~~ wk (zip (enum symbol) (enum symbol)) d]=nil.
elim:(language'(#|state|+1)symbol).
done.
move=>a l H.
simpl.
case:(accept M a).
rewrite/=H(_:size a==size a).
rewrite(_:all(in_mem^~(mem(zip (enum symbol) (enum symbol)))) (zip a a))/=.
done.
elim:a.
done.
move=>a l0{}H.
rewrite/=H Bool.andb_true_r.
have:(a\in(enum symbol)).
apply/mem_enum.
elim:(enum symbol).
done.
move=>a0 l1{}H.
rewrite/=!in_cons.
move/orP.
case.
move/eqP=>aa0.
apply/orP.
left.
apply/eqP.
by f_equal.
move/H=>{}H.
apply/orP.
by right.
by apply/eqP.
done.
rewrite H cat0s.

have{}H:[seq d <- [seq startDomino M s | s <- language (#|state| + 1) symbol]
        | ~~ wk (zip (enum symbol) (enum symbol)) d]=
  [seq startDomino M s | s <- language (#|state| + 1) symbol].
rewrite addn1/=.
elim:(language #|state| symbol).
done.
move=>a l{}H.
rewrite/=!map_cat!filter_cat.
have H1:[seq d <- [seq startDomino M s | s <- [seq s :: a | s <- enum symbol]]
   | ~~ wk (zip (enum symbol) (enum symbol)) d]=
  [seq startDomino M s | s <- [seq s :: a | s <- enum symbol]].
remember (wk (zip (enum symbol) (enum symbol))) as w.
elim:(enum symbol).
done.
rewrite Heqw=>{w Heqw}.
move=>a0 l0 H1.
rewrite/=(_:~~wk (zip (enum symbol) (enum symbol)) (startDomino M (a0 :: a))).
by f_equal.
rewrite/startDomino/wk(_:size (a0 :: a) == size (take (size (a0 :: a) -
        (index (dstar (delta M) (init M) (a0 :: a)) (enum state) + 1))
       (a0 :: a))=false).
done.
rewrite addn1.
by apply/eqP/size_take_ne.
rewrite H1.
by f_equal.
by rewrite H mul1n.

move=>n H.
rewrite/=filter_cat filter_nil cat0s.
Search (_=i_).
rewrite map_cat.

elim:a.
map_id
simpl.
done.
move=>a0 l0 H1.
rewrite/=(_:(size a).+1 == size (take((size a).+1 -
          (index (dstar (delta M) (delta M (init M) a0) a) (enum state) + 1))
         (a0 :: a))=false)/=.
f_equal.
rewrite filter_cons.
simpl.
 (_:size a == size
  (take(size a-(index(dstar(delta M) (init M) a) (enum state)+1)) a)=false)/=.
by f_equal.
rewrite addn1.
apply/eqP/size_take_ne.

suff H:[seq startDomino M s | s <- language (1 * (#|state| + 1)) symbol] =i
  [seq d <- [seq startDomino M s | s <- language (#|state| + 1) symbol]
        | ~~ wk (zip (enum symbol) (enum symbol)) d].
Search (_=i_).

Lemma stopaccept{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol):s<>nil->size s <= #|state| + 1 -> t<>nil->size t<=#|state| -> 
dstar (delta M)(nth (init M) (enum state) (size t - 1))s\in final M->
stopDomino s t\in extend (Aut_to_Stk M).
Proof.
move=>snil lens tnil lent H.
rewrite/=mem_cat.
apply/orP.
right.
have:t\in language'#|state| symbol.
by apply/language'lemma.
elim:(language' #|state| symbol).
done.
move=>a l H1.
simpl.
rewrite in_cons mem_cat.
move/orP.
case.
move/eqP=>ta.
apply/orP.
left.
rewrite-ta=>{a ta}.
apply/map_f.
rewrite mem_filter.
apply/andP.
split.
done.
by apply/language'lemma.
move/H1=>{}H1.
apply/orP.
by right.
Qed.

Lemma onestep_prime{symbol:finType}(n:nat)(stk:@sticker symbol):
ss_generate_prime n.+1 stk = [seq d<-ss_generate_prime n stk|wk (rho stk)d] ++ 
[seq mu' a d|a<-[seq a'<-ss_generate_prime n stk|~~wk (rho stk)a']
  ,d<-(extend stk)].
Proof. done. Qed.



(*
Lemma dominolength{state symbol:finType}(n:nat)(M:@automaton state symbol):
all (fun d=>size (ss_language_f d) == n.+1*(#|state|+1))
  [seq d<-ss_generate_prime n (Aut_to_Stk M)|~~wk (rho (Aut_to_Stk M)) d].
Proof.
elim:n.
admit.
move=>n H.
rewrite onestep_prime filter_cat all_cat.
apply/andP.
split.
by rewrite filter_nil.
Search filter.
simpl.
rewrite filter_all.
d\in ss_generate_prime n (Aut_to_Stk M) -> ~~wk (rho (Aut_to_Stk M)) d ->
size (ss_language_f d)=n.+1*(#|state|+1).
Proof.
elim:n.
rewrite/=mem_cat.
move/orP.
case.
elim:(language' (#|state| + 1) symbol).
done.
move=>a l H.
simpl.
case:(accept M a).
rewrite/= in_cons.
move/orP.
case.
move/eqP=>d'.
rewrite d'/=(_:size a == size a)=>{d'}.
rewrite/negb(_:all (in_mem^~(mem(zip(enum symbol) (enum symbol)))) (zip a a)).
done.
elim:a.
done.
move=>a l0 H1.
simpl.
apply/andP.
split;[|done].
have:a\in(enum symbol).
apply/mem_enum.
elim:(enum symbol).
done.
move=>a0 l1 H2.
rewrite/=!in_cons.
move/orP.
case.
move/eqP=>H3.
apply/orP.
left.
apply/eqP.
by f_equal.
move/H2=>{}H2.
apply/orP.
by right.
by apply/eqP.
done.
done.

move=>H H1.
move:H.
destruct d.
elim:(language (#|state| + 1) symbol).
done.
move=>a l H.
rewrite/=in_cons.
move/orP.
case.
by move/eqP.
by move/H.
rewrite/=/startDomino.
Search all.
move/map_f.
remember (language (#|state|+1) symbol).
rewrite-Heql.
move:l Heql.
elim:(language (#|state| + 1) symbol).
move=>l H.
by rewrite H.
move=>a l H.
case.
done.
move=>a0 l0.
move:(H l0)=>{}H[a0a l0l].
move:(H l0l)=>{}H.
rewrite/=in_cons.
move/orP.
case.
move/eqP.
rewrite in_cons=>H1.
have H2:a\in language(#|state|+1) symbol.
move:H1.
case:(language (#|state| + 1) symbol).
done.
move=>a0 l0 [aa0 _].
rewrite in_cons.
apply/orP.
left.
by apply/eqP.
by split.
move/orP.

move/H1.
case.


elim:(#|state| + 1).
rewrite muln0.
move=>H H1.
move:H.
elim:n.
rewrite/=mem_cat.
move/orP.
case.
elim:
move/map_f.
destruct d.
simpl.
rewrite mem_filter.
all (fun p=>(size (ss_language_f p))==n.+1*(#|state|+1))
[seq d<-ss_generate_prime n (Aut_to_Stk M)|~~wk (rho (Aut_to_Stk M)) d].
Proof.
elim:n.
rewrite/=filter_cat all_cat.
apply/andP.
split.
rewrite filter_map.
elim:[seq str <- language' (#|state| + 1) symbol | accept M str].
done.
move=>a l.
rewrite-!filter_map=>H.
rewrite map_cons filter_cons
(_:wk (zip (enum symbol) (enum symbol)) (Domino a a 0 0))/=.
done.
rewrite(_:size a==size a);[|by apply/eqP].
apply/all_filterP.
elim:a.
done.
move=>a a' H1.
rewrite/=(_:(a, a) \in zip (enum symbol) (enum symbol)).
by f_equal.
have:a\in (enum symbol).
apply/mem_enum.
elim:(enum symbol).
done.
move=>b e H2.
rewrite/=!in_cons.
move/orP.
case.
move/eqP=>ab.
apply/orP.
left.
apply/eqP.
by f_equal.
move/H2=>{}H2.
apply/orP.
by right.

have:[seq d <- [seq startDomino M s | s <- language (#|state| + 1) symbol]
     | ~~ wk (zip (enum symbol) (enum symbol)) d]
        =[seq startDomino M s | s <- language (#|state| + 1) symbol].
rewrite filter_map.
f_equal.
elim:(language (#|state| + 1) symbol).
done.
move=>a l H.
rewrite map_cons filter_cons
  (_:~~ wk (zip (enum symbol) (enum symbol)) (startDomino M a)).
by f_equal.
rewrite/=(_:size a ==  size
    (take(size a-(index(dstar(delta M)(init M) a) (enum state) + 1)) a)=false).
done.
rewrite size_take.

rewrite mul1n all_filter.

Search all.


Search (_\in _).
case_eq (language (#|state| + 1) symbol)

done.
move=>H1.
rewrite map_cons filter_cons.
have: ~~ wk (zip (enum symbol) (enum symbol)) (startDomino M _a_)=true.
simpl.
move:l Heql.
fix H 1.
rewrite-Heql.
elim l.
done.
move=>a l0 H.
rewrite 



elim (language (#|state| + 1) symbol) as [|a l].
done.
move=>H1.
rewrite map_cons filter_cons
(_:wk (zip (enum symbol) (enum symbol)) (startDomino M a))/=.
done.
rewrite size_take ltn_subrL addn1.
Search (_-_<_).
rewrite:(_:size a == size
   (take (size a - (index (dstar (delta M) (init M) a) (enum state) + 1)) a)=false).

Search filter.

simpl.
rewrite filter_map.
simpl.

Search filter.
rewrite filter_map.

elim:[seq startDomino M s | s <- language (#|state| + 1) symbol].
done.
move=>a l H.
simpl.

apply/all_filterP.

Search filter.



Search ([seq _ <- _|_]).
simpl.
rewrite filter_cat.
simpl.
 filter_map.
Search filter_map.*)




Theorem REG_RSL{state symbol:finType}(M:@automaton state symbol)(s:seq symbol)
(n:nat):s <> nil -> exists m:nat , m <= n ->
accept M s = (s\in(ss_language_prime n (Aut_to_Stk M))).
Proof.
move=>scons.
apply ex_intro with ((size s - 1)/(#|state|+1)).
remember ((size s-1)/(#|state|+1)) as n.
rewrite lang_gen.
move:Heqn.
case:n.
simpl.
rewrite addn1.
move:(Nat.neq_succ_0 #|state|)=>H.

move/Nat.eq_sym_iff/(Nat.div_small_iff _ _ H)/ltP.
rewrite-(ltn_add2r 1)!addn1 subn1 prednK.
move/(language'lemma _ _ scons).
rewrite-addn1 mem_cat=>{}H.
have H1:(Domino s s 0 0
     \in [seq startDomino M s0 | s0 <- language (#|state| + 1) symbol])=false.
move:H.
elim:(language (#|state| + 1) symbol).
done.
move=>a l H/H=>{}H.
rewrite/=in_cons H Bool.orb_false_r/startDomino.
case_eq(Domino s s 0 0 ==
 Domino a
   (take (size a - (index (dstar (delta M) (init M) a) (enum state) + 1)) a) 0
   0);[move/eqP=>[sa];rewrite-sa=>H1|done].
have:size s = size(
     take (size s - (index (dstar (delta M) (init M) s) (enum state) + 1)) s).
by rewrite-H1.
have{}H1:(0<index(dstar(delta M) (init M) s) (enum state) + 1) && (0 < size s).
rewrite addn1/=.
move:scons.
by case s.
rewrite size_take ltn_subrL H1=>H2.
move:H1.
rewrite-ltn_subrL.
by rewrite-H2 ltnn.

rewrite H1 Bool.orb_false_r-map_f_eq.
rewrite mem_filter.
by case:(accept M s).
by move=>x y[].
move:scons.
by case s.

move=>n H.
have{H}lens:size s = n.+1*(#|state| + 1)+(size s - 1) mod (#|state|+1) +1.
rewrite H.
apply/Nat.pred_inj.
move:scons.
by case s.
by rewrite addn1.
by rewrite addn1-pred_Sn-subn1 mulnC-multE-plusE-Nat.div_mod_eq.
have H:n.+1 * (#|state| + 1) < size s.
by rewrite lens!addn1 ltnS leq_addr.

rewrite onestep_prime mem_cat-(cat_take_drop (n.+1 * (#|state| + 1)) s).
remember (take (n.+1 * (#|state| + 1)) s) as t.
remember (drop (n.+1 * (#|state| + 1)) s) as u.
have lent:size t = n.+1*(#|state|+1).
by rewrite Heqt size_take H.
have lenu:size u=(size s - 1) mod (#|state| + 1) + 1.
by rewrite Hequ size_drop{1}lens-addnA add_subABA.
have lenu':size u <= (#|state|+1).
rewrite lenu!addn1.
by apply/ltP/Nat.mod_upper_bound.

rewrite-(mu'lemma2 M).
apply/bool_eqsplit.
split.
move=>acc.
apply/orP.
right.


apply/map_f'.
rewrite mem_filter.
apply/andP.
split.
simpl.
case H1:(size t ==
  size
    (take (size t - (index (dstar (delta M) (init M) t) (enum state) + 1)) t)).
move:H1.
move/eqP.
have H1:(size t-(index(dstar(delta M) (init M) t) (enum state) + 1) < size t).
rewrite ltn_subrL.
apply/andP.
split.
by rewrite addn1.
by rewrite lent addn1 mulSn addSn.
rewrite size_take H1=>H2.
move:H1.
by rewrite-H2 ltnn.
done.

by apply/startDomino_gen_prime.
apply/stopaccept.
case_eq(u==nil);move/eqP;[move=>unil|done].
move:lenu.
by rewrite unil addn1.
done.
case_eq(drop(size t-(index(dstar(delta M)(init M) t)(enum state)+1))t==nil);
move/eqP;[move=>H1|done].
have:size(drop(size t-(index(dstar(delta M)(init M)t)(enum state) + 1)) t)=0.
by rewrite H1.
rewrite size_drop subKn.
by rewrite addn1.
rewrite lent mulSn!addn1 addSn-addnS.
apply/ltn_addr/fin_index.
rewrite size_drop subKn addn1.
apply/fin_index.
rewrite lent mulSn!addn1 addSn-addnS.
apply/ltn_addr/fin_index.

rewrite size_drop subKn.
rewrite addn1 subn1 nth_index.
move:acc.
by rewrite/accept dstarLemma.
apply/mem_enum.
rewrite lent mulSn!addn1 addSn-addnS.
apply/ltn_addr/fin_index.

move/orP.
case.
rewrite mem_filter.
move/andP.
case=>_.
rewrite/wk.
simpl.
rewrite onestep_prime mem_cat.
move/orP.
case.
Search map.
Search (_<=_+_).


Search(_-(_-_)).

rewrite Hequ.
move:lenu.
rewrite addn1.
by case u.
Search (_<_=false).
rewrite addn1 subnS Heqt size_take.
Search (_-_<_).

rewrite size_take.

case H1:(size t-(index(dstar(delta M) (init M) t) (enum state) + 1) < size t).
move=>H2.
move:H1.
by rewrite-H2 ltnn.
Search(_<=_=false).
move/eqP.
Search (_<_=false).
move/eqP.
rewrite onestep_prime.
apply/map_f.


simpl.

move:H.
rewrite subn1.
Search (_.+1<=_.+1).
 (#|state|+1)(size s - 1)).
move/leP.
rewrite multE H.
Search (_*_)%coq_nat.
move:Nat.div_mod_eq.
Search (_/_).
move:n s {scons}.
elim.
move/(ltnn (size s)).
Search (_<_=false).


Search (_.+1<=_.+1).
rewrite subnS.
Search (_.+1<=_.+1).
subnS
Search size_take.
rewrite-{1}(cat_take_drop (size s - n.+1) s).
done.


rewrite!addn1.
move/(map_f (fun p=>Domino p p 0 0)).
rewrite mem_cat.
Search 
have{}H:s\in language (#|state|+1) symbol.

rewrite/Aut_to_Stk.
simpl.
rewrite mem_cat.



Search (_/_=0).
have{}H:size
elim:n.
case:n.
split.
move=>acc.

rewrite lang_gen.
suff H:s\in ss_language_prime 1 (Aut_to_Stk M).
rewrite H.
case.
destruct exists.
suff H:
rewrite/Aut_to_Stk.
rewrite/exists.

Lemma ss_generatelemma (m n:nat)(stk:Sticker)(d:Domino):
  m <= n -> d \in (ss_generate_prime m stk)-> d \in (ss_generate_prime n stk).
Proof. move/subnKC=>H H1;rewrite-H;elim (n-m);[by rewrite addn0|].
move=>n0 H2;rewrite addnS;destruct stk as (((V,rho),A),D);simpl;
rewrite in_app;rewrite in_undup. by rewrite H2. Qed.


(*Lemma ss_accept_A (V:list Symbol)(rho:list (Symbol*Symbol))(A:list Domino)
(D:list (Domino*Domino))(s:string):Vword s V->
  ((s,s,0,0)\in A)->ss_accept_prime (V,rho,A,D) s.
Proof.
move=>Vwords;rewrite/ss_accept_prime;rewrite Vwords;rewrite andb_true_l;
rewrite/ss_language_prime;move=>H;
have {}H:(s,s,0,0)\in(ss_generate_prime (length s) (V, rho, A, D));
[by elim (length s);[|move=>n;apply ss_generatelemma]|];
have H1:(s = ss_language_f (s,s,0,0));[by[]|rewrite{1}H1=>{H1}].
have {H}:
(s,s,0,0)\in[seq d<-ss_generate_prime(length s)(V, rho, A, D)|wk rho d].
move:H;elim (ss_generate_prime (length s) (V, rho, A, D));[done|];simpl;
move=>a l H;rewrite in_cons;case H1:((s,s,0,0)==a).
simpl;rewrite-(eqP H1).
simpl;rewrite (_:length s == length s=true);[|by elim s];rewrite in_cons;
rewrite (_:(s,s,0,0)==(s,s,0,0)=true);[done|];rewrite!xpair_eqE;
have H2:(s==s);[by elim s|by rewrite!H2].
by case:(wk a);[rewrite in_cons;case ((s,s,0,0)==a);simpl|].
apply map_f. Qed.*)

Lemma languagelemma (s:string)(V:list ascii):
Vword s V -> s \in language (length s) V.
Proof. by elim:s;[|move=>a s H;simpl;
case H2:(a\in V);[simpl;move/H=>{}H;apply map_f'|]]. Qed.

Lemma language'lemma (s:string)(V:Symbols)(n:nat):
0 < length s ->Vword s V-> s \in language' (length s + n) V.
Proof. by move:s;elim:n;[move=>s;rewrite addn0;case H2:(length s);
[|move =>H{}H;rewrite/language';rewrite-H2;rewrite in_app;
rewrite languagelemma;[rewrite orb_true_r|]]|move=>n H s H1 H2;rewrite addnS;
simpl;rewrite in_app;rewrite H]. Qed.

(*
Lemma p1 (K:States)(V:Symbols)(delta:State->Symbol->State)(s0:State)(F:States)
(s:string):accept (K,V,delta,s0,F) s -> 0<length s ->
(length s <= List.length K + 1) ->(ss_accept (Aut_to_Stk (K,V,delta,s0,F)) s).
Proof.
move => H H1 H2.
have H3:(Vword s V);[by move:H;simpl;case (Vword s V)|].
simpl.
apply/(ss_accept_A H3);rewrite in_app.
have {}H2:
(Datatypes.length K + 1 = length s + (Datatypes.length K +1 - length s));
[by rewrite subnKC|].
have {H2}H1:(s\in(language' (Datatypes.length K + 1) V));
[by rewrite H2;rewrite language'lemma|].
have {H1 H3}H:(s\in accepts (K, V, delta, s0, F)
                    (language' (Datatypes.length K + 1) V)).
move:H1.
elim (language' (Datatypes.length K + 1) V);[by[]|].
move=>a l H4;rewrite in_cons;
case H5:(s==a).
rewrite<-(eqP H5);move:H;simpl;
by case:(Vword s V && (s0 \in K) && ([::] == [seq f <- F | f \notin K]) &&
        (dstar delta s0 s \in F));
[rewrite in_cons;have H6:(s==s);[by []|];rewrite H6|].
by rewrite orb_false_l;simpl;
case:(Vword a V && (s0 \in K) && ([::] == [seq f <- F | f \notin K]) &&
        (dstar delta s0 a \in F));
[rewrite in_cons;rewrite H5;rewrite orb_false_l|].
have {}H:((s,s,0,0) \in [seq (l', l', 0, 0)
          | l' <- accepts (K, V, delta, s0, F)
                    (language' (Datatypes.length K + 1) V)]).
move:H.
elim (accepts (K, V, delta, s0, F) (language' (Datatypes.length K + 1) V));
[by[]|move=>a l;simpl;rewrite !in_cons];
case H:(s==a).
by have {}H:((s, s, 0, 0) == (a, a, 0, 0));[rewrite (eqP H)|rewrite H].
by simpl;move=>H1 H2;rewrite (H1 H2);case ((s, s, 0, 0) == (a, a, 0, 0)).
by rewrite H.
Qed.*)
Lemma Vwordlemma (V:Symbols)(m n:nat)(s:string):
Vword s V->Vword (substring m n s) V.
Proof.
move:m n.
elim:s.
by case;case.
move=>a s H.
case;case;[done| | |];
(simpl;move=>n;case:(a\in V);[rewrite!andb_true_l|done];apply H).
Qed.
Lemma Vwordlemma2 (V:Symbols)(s t:string):
(Vword s V)&&(Vword t V)=Vword(s++t)V.
Proof. by elim:s;[|simpl;move=>a s H;case:(a\in V)]. Qed.
Lemma in_pair (V:Symbols)(a:Symbol):
(a \in V)=((a, a) \in [seq (v, v) | v <- V]).
Proof. elim:V;[done|];move=>v V H;simpl;rewrite!in_cons.
have H1:(a==v=((a, a) == (v, v))).
apply/bool_eqsplit;split;[move/eqP=>av;by rewrite av|
move/eqP=>[av {}av];apply/eqP/av]. rewrite-H1;by case:(a==v). Qed.
Lemma lrcheck'C (V:Symbols)(s t:string):
lrcheck' [seq (v,v)|v<-V] s t = lrcheck' [seq (v,v)|v<-V] t s.
Proof. move:t;elim:s;[by case|];move=>a s H;case;[done|];move=>b t;simpl.
rewrite H=>{H};f_equal=>{s t};elim:V;[done|];move=>v V H;simpl;
rewrite!in_cons;rewrite H;f_equal;apply/bool_eqsplit;
split;move/eqP=>[{}H H1];by rewrite H;rewrite H1. Qed.
Lemma lrcheck'Vword (V:Symbols)(s t:string):length s = length t ->
lrcheck' [seq (v,v)|v<-V] s t -> Vword s V.
Proof.
case Vwords:(Vword s V);[done|].
move:t Vwords.
elim:s.
done.
move=>a s H.
case.
done.
move=>b t.
simpl.
case ainV:(a \in V);simpl.
move/H=>{}H.
move=>[].
move/H=>{}H.
by case:((a, b) \in [seq (v, v) | v <- V]).
move=>_ _ {H}.
case:(lrcheck' [seq (v, v) | v <- V] s t);
[rewrite andb_true_r|by rewrite andb_false_r].
move:ainV=>{s t}.
elim:V.
done.
move=>v V H.
simpl.
rewrite!in_cons.
case av:(a==v);[done|move/H=>{}H].
rewrite (_:(a, b) == (v, v) = false);[done|move=>{H}].
apply/eqP.
move=>[].
move/eqP.
by rewrite av.
Qed.
Lemma lrcheck'Vword_eq (V:Symbols)(s:string):
  lrcheck' [seq (v,v)|v<-V] s s = Vword s V.
Proof. by elim:s;[|move=>a s H;simpl;rewrite-in_pair;case:(a \in V)]. Qed.
Lemma lrcheck'append_eq (V:Symbols)(s t:string):
lrcheck' [seq (v,v)|v<-V] (s++t) s = Vword s V. Proof.
by elim:s;[case:t|move=>a s H;simpl;rewrite-in_pair;case:(a\in V)]. Qed.
Lemma lrcheck'append (V:Symbols)(s t u:string):length s = length t ->
lrcheck' [seq (v,v)|v<-V] (s++u) t = lrcheck' [seq (v,v)|v<-V] s t. Proof.
move:t;elim:s;[by case;case:u|];move=>a s H;case;[done|];
move=>b t;simpl;move=>[len];f_equal;apply/H/len. Qed.
Lemma lrcheck'eq (V:Symbols)(s t:string):Vword s V->Vword t V->
length s = length t -> lrcheck' [seq (v, v) | v <- V] s t = (s==t).
Proof.
move=>Vwords Vwordt len.
apply/bool_eqsplit.
split;[|move/eqP=>H;rewrite H;by rewrite lrcheck'Vword_eq].

move:t Vwords Vwordt len;elim:s.
by case.
move=>a s H.
case;[done|].
simpl.
move=>b t.
case:(a\in V);[simpl|done].
case:(b\in V);[simpl|done].
move/H=>{}H.
move/H=>{}H.
move=>[].
move/H=>{}H.
case lr:(lrcheck' [seq (v, v) | v <- V] s t);
[rewrite andb_true_r|by rewrite andb_false_r].
move:(H lr)=>/eqP {lr H}st.
have H:(a, b) \in [seq (v, v) | v <- V] -> a = b.



elim:V.
by[].
move=>v V H.
simpl.
rewrite!in_cons.
suff:((a, b) == (v, v))->a=b.
by case ((a, b) == (v, v)).
move/eqP.
congruence.
move/H=>ab.
apply/eqP.
by f_equal.
Qed.


Lemma mu'lemma (V:Symbols)(n m:nat)(s t u:string):Vword s V -> Vword t V ->
Vword u V -> n< length s -> m < length t ->
mu' [seq (v,v)|v <- V] (extentionDomino m t u) (startDomino n s) =
if (substring (length s - n) n s) == u then
  [::startDomino m (s++t)]
else nil.
Proof.
move=>Vwords Vwordt Vwordu.
move=>lens;move:(lens)(lens);move/ltnW/subKn=>lens';move/ltnW/subnK=>lens''.
move=>lent;move:(lent)(lent);move/ltnW/subKn=>lent';move/ltnW/subnK=>lent''.

simpl.
rewrite addn0.
rewrite!subn0.
rewrite!substringeq.
rewrite-{1}(substringlemma1 (length s - n) s).
rewrite lrcheck'append_eq.
rewrite(Vwordlemma _ _ _ _ Vwords).
have H2:(forall d1 d2:Domino,flatten  [seq mu [seq (v, v) | v <- V] d' d2
     | d' <- [:: d1]] = 
    mu [seq (v,v)|v<-V] d1 d2).
simpl.
move=>d1 d2.
by rewrite-appnil.
rewrite H2.
rewrite/mu.
case s':s;[move:lens;by rewrite s'|rewrite-s'].
case s1':(substring 0 (length s - n) s).
have:(length (substring 0 (length s-n) s)=0).
by rewrite s1'.
rewrite substringlemma2;[|rewrite add0n;apply/leq_subr].
have H3:(forall m n:nat,m-n=0->m<=n);[elim;[by[]|];move=>m0 H3;case;[by[]|];
move=>n0;rewrite subSS;apply H3|].
move/H3/leq_gtF;by rewrite lens.
case t':t;[move:lent;by rewrite t'|].
rewrite-t'.
case ut':(u ++ substring 0 (length t - m) t).
have:(length (u ++ substring 0 (length t - m) t)=0).
by rewrite ut'.
rewrite stringlength.
rewrite substringlemma2;[|rewrite add0n;apply/leq_subr].
have H3:(length t - m) >0.
move:(lent).
rewrite-{1}lent''.
rewrite-{1}(add0n m).
by rewrite ltn_add2r.
by case (length u);
[rewrite add0n;move=>H4;move:H3;rewrite H4|move=>n0;rewrite addSn].
rewrite!add0n.
rewrite-s1'.
rewrite substringlemma2;[|rewrite add0n;apply/leq_subr].
rewrite-ut'.
simpl.

rewrite!substringeq.
rewrite-{3}(substringlemma1 (length s - n) s).
rewrite lens'.
rewrite-{1}(substringlemma1 (length t - m) t).
rewrite lent'.

rewrite-{2}(subnKC (ltnW lens)).
have H4:(length u + (length s - n) == n + (length s - n)=(length u == n)).
elim (length s - n).
by rewrite!addn0.
move=>n0 H4.
rewrite!addnS.
by rewrite eqSS.
rewrite H4.
have H5:(length u == n = false -> substring (length s - n) n s == u = false).
move=>H5.
case H6:(substring (length s - n) n s == u);[|done].
have {H6}:(length (substring (length s - n) n s) == length u).
by rewrite (eqP H6).
rewrite substringlemma2;[|by rewrite lens''].
move/eqP=>H6.
move:H5.
rewrite H6.
by move/eqP.
case lenu:(length u == n);[|by rewrite H5].
rewrite appstring.
rewrite-(appstring 
  (substring 0 (length s - n) s) (substring (length s - n) n s)).
have len:length
  (substring 0 (length s - n) s ++
   substring (length s - n) n s ++ substring 0 (length t - m) t) =
length (substring 0 (length s - n) s ++ u ++ substring 0 (length t - m) t).
rewrite!stringlength;rewrite(eqP lenu);
rewrite (substringlemma2 (length s - n));[done|by rewrite lens''].
rewrite lrcheck'append;[|apply/len].
rewrite lrcheck'eq;[|rewrite-!Vwordlemma2;by rewrite!Vwordlemma|
by rewrite-!Vwordlemma2;rewrite Vwordu;rewrite!Vwordlemma|apply/len].

rewrite append_eqlr.
case H8:(substring (length s - n) n s == u);[|done].
rewrite/startDomino.
repeat f_equal.
rewrite-(eqP H8).
rewrite-{3}lens'.
rewrite appstring.
rewrite substringlemma1.
rewrite stringlength.
rewrite-addnBA;[|apply/ltnW/lent].
elim s.
by[].
move=>a0 s0 H9.
simpl.
by f_equal.
Qed.
Lemma mu'lemma2 (V:Symbols)(n:nat)(s t u:string):Vword s V -> Vword t V ->
Vword u V -> n< length s -> t != "" ->
mu' [seq (v,v)|v <- V] (stopDomino t u) (startDomino n s) = 
  if substring (length s - n) n s == u then
    [::(s++t,s++t,0,0)]
  else nil.
Proof.
move=>Vwords Vwordt Vwordu lens t'.
simpl.
rewrite!add0n;rewrite!subn0.
move:(lens);move/ltnW/subKn=>lens'.

rewrite!substringeq.
rewrite-{1}(substringlemma1 (length s - n) s).
rewrite lens'.
rewrite lrcheck'append_eq.
rewrite(Vwordlemma _ _ _ _ Vwords).
simpl.

case s':s;[move:lens;by rewrite s'|rewrite-s'].
case s1':(substring 0 (length s - n) s).
have:(length (substring 0 (length s-n) s)=0).
by rewrite s1'.
rewrite substringlemma2;[|rewrite add0n;apply/leq_subr].
have H3:(forall m n:nat,m-n=0->m<=n);[elim;[by[]|];move=>m0 H3;case;[by[]|];
move=>n0;rewrite subSS;apply H3|].
move/H3/leq_gtF;by rewrite lens.
rewrite-s1'.
rewrite!substringeq.
rewrite!add0n.

case t'':t.
move:t'.
by rewrite t''.
rewrite-t''.
case ut':(u++t).
move:ut'.
rewrite t''.
by case u.
rewrite-ut'.
rewrite substringlemma2;[|rewrite add0n;apply/leq_subr].
move:lens;move/ltnW/subnK=>lens''.
rewrite-{2}lens''.
rewrite (addnC (length s-n)).


have H:(length u + (length s - n) == n + (length s - n)=(length u == n)).
elim (length s - n).
by rewrite!addn0.
move=>n0 H.
rewrite!addnS.
by rewrite eqSS.
rewrite H.
have H2:(length u == n = false -> substring (length s - n) n s == u = false).
move=>H2.
case H3:(substring (length s - n) n s == u);[|done].
have {H3}:(length (substring (length s - n) n s) == length u).
by rewrite (eqP H3).

rewrite substringlemma2;[|by rewrite lens''].
move/eqP=>H3.
move:H2.
rewrite H3.
by move/eqP.
case lenu:(length u == n);[|by rewrite H2].
rewrite-{1}(substringlemma1 (length s - n) s).
rewrite-appstring.
rewrite lens'.

have len:length (substring 0 (length s - n) s++substring (length s - n) n s ++ t) =
length (substring 0 (length s - n) s ++ u ++ t).
rewrite!stringlength;rewrite(eqP lenu);
rewrite (substringlemma2 (length s - n));[done|by rewrite lens''].
rewrite lrcheck'eq;[|rewrite-!Vwordlemma2;by rewrite!Vwordlemma|
by rewrite-!Vwordlemma2;rewrite Vwordu;rewrite!Vwordlemma|apply/len].

rewrite append_eqlr.
case H3:(substring (length s - n) n s == u);[|done].
rewrite-appnil.
rewrite-(eqP H3).
rewrite appstring.
rewrite-{3}lens'.
by rewrite substringlemma1.
Qed.
Lemma complementarity(n:nat)(V:Symbols)(A:list Domino)(D:list(Domino*Domino))
(s t:string):Vword s V -> Vword t V ->
(s,t,0,0)\in[seq d<-ss_generate n (V,[seq (v,v)|v<-V],A,D)|
wk [seq (v,v)|v<-V] d] -> s=t.
Proof.
rewrite mem_filter.
case H:(wk [seq (v,v)|v<-V] (s, t, 0, 0));[simpl|done].
move=>Vwords Vwordt x{x}.
move:H.
simpl.
case H:(length s == length t);[simpl|done].
rewrite!substringeq.
by rewrite lrcheck'eq;[move/eqP| | |apply/eqP].
Qed.

Lemma wklemma (V:Symbols)(d:Domino):wk [seq (v,v)|v<-V] d ->
  d = (ss_language_f d,ss_language_f d,0,0).
Proof. destruct d as (((s,t),m),n).
simpl.
case m0:(m==0);[rewrite(eqP m0)|done]=>{m0}.
case n0:(n==0);[rewrite(eqP n0)|done]=>{n0}.
case len:(length s == length t);[move:len;move/eqP=>len|done].
rewrite!substringeq.
simpl=>lr.
move:(lrcheck'Vword _ _ _ len lr)=>Vwords.
move:(lr);rewrite lrcheck'C=>rl.
have len':(length t = length s).
by rewrite len.
move:(lrcheck'Vword _ _ _ len' rl)=>{len' rl}Vwordt.
move:lr.
rewrite(lrcheck'eq _ _ _ Vwords Vwordt len).
move/eqP=>st.
by repeat f_equal.
Qed.

Lemma wk_sslanguage_prime (V:Symbols)(l:list Domino)(s:string):
s\in[seq ss_language_f d|d<-l & wk [seq (v,v)|v<-V] d] -> (s,s,0,0)\in l.
Proof.
elim:l.
by[].
move=>a l H.
simpl.
case wka:(wk [seq (v, v) | v <- V] a).
simpl.
rewrite!in_cons.
case sa:(s==ss_language_f a);simpl.
case:((s, s, 0, 0) \in l);[by rewrite orb_true_r|rewrite orb_false_r;move=>_].
move:(wklemma _ _ wka).
rewrite-(eqP sa)=>H1.
by apply/eqP.
move/H.
by case:((s, s, 0, 0) \in l);case:((s, s, 0, 0) == a).
rewrite in_cons.
move/H.
by case:((s, s, 0, 0) \in l);case:((s, s, 0, 0) == a).
Qed.

Theorem REG_RSL (M:Automaton)(s:string):
s!="" -> accept M s = (ss_accept_prime (Aut_to_Stk M) s).
Proof.
move=>s_notempty.
destruct M as ((((K,V),delta),k0),F).

(*オートマトンとして成立しない場合、スティッカーは空になる*)
have bad_definition:
  ((k0 \in K) && ([::] == [seq f <- F | f \notin K]) = false ->
    accept (K, V, delta, k0, F) s = 
      ss_accept_prime (Aut_to_Stk (K, V, delta, k0, F)) s);
[move=>H;simpl;case:(Vword s V);simpl;rewrite H;simpl;by case s|].
case automaton_collect:((k0 \in K) && ([::] == [seq f <- F | f \notin K]));
[|by rewrite bad_definition]=>{bad_definition}.
have Vwords':(Vword s V = false ->
accept (K, V, delta, k0, F) s =
  ss_accept_prime (Aut_to_Stk (K, V, delta, k0, F))s);
[by rewrite/accept/ss_accept_prime/Aut_to_Stk;move=>H;
case:((k0 \in K) && ([::] == [seq f <- F | f \notin K]));rewrite H;
rewrite!andb_false_l;[|have H1:(Vword s nil)=false;
[move:s_notempty;by case s|by rewrite H1]]|].
case Vwords:(Vword s V);[|by apply Vwords'];move=>{Vwords'}.
have concatlemma:(forall(s:string)(l:list string),
  s++(concat "" l)=concat "" (s::l));
[move=>s' l;have appends0:(forall s:string,s++""=s);
[by elim;[|move=>a s1 H';simpl;f_equal]|];by case:l|].
have dstarlemma:(forall(s1 s2:string)(k:State)(delta:State->Symbol->State),
  dstar delta k (s1++s2) = dstar delta (dstar delta k s1) s2);
[by move=>s2 s3 k d;move:k;elim:s2;simpl|].
have {concatlemma dstarlemma}concatdstar:
  (forall (s:string)(l:list string)(k:State)(delta:State->Symbol->State),
  dstar delta k(concat "" (s::l))=dstar delta(dstar delta k s)(concat "" l));
[move=>s2 l k d;rewrite-dstarlemma;by rewrite concatlemma|].




rewrite/accept;rewrite Vwords;rewrite automaton_collect;rewrite andb_true_l.
move:(dividestringlemma (List.length K + 1) s)=>s_.
suff H:(forall m n:nat,n=Datatypes.length K + 1 ->
  List.length (dividestring n s) = m -> (dstar delta k0 s \in F) =
    ss_accept_prime (Aut_to_Stk (K, V, delta, k0, F)) s).
by apply (H (List.length (dividestring (Datatypes.length K + 1) s))
  (Datatypes.length K + 1)).
move=>m n H H1.
suff:((dstar delta k0 s \in F) =
(s \in ss_language_prime (length s) (Aut_to_Stk (K, V, delta, k0, F)))).
by simpl;rewrite/ss_accept_prime;rewrite automaton_collect;rewrite Vwords.

have H2:((s,s,0,0)\in ss_generate_prime (length s)
    (Aut_to_Stk (K, V, delta, k0, F))) = 
(s \in ss_language_prime (length s) (Aut_to_Stk (K, V, delta, k0, F))).
apply/bool_eqsplit.
split;simpl;rewrite automaton_collect;move=>H2.
rewrite{1}(_:s=ss_language_f (s,s,0,0));[|done].
apply/map_f.
rewrite mem_filter.
simpl.
rewrite (_:length s == length s = true);[simpl|by apply/eqP].
rewrite!substringeq.
rewrite lrcheck'Vword_eq.
rewrite Vwords.
by rewrite H2.

by move:(wk_sslanguage_prime _ _ _ H2).
rewrite-H2=>{H2}.
have H2:(dstar delta k0 s \in F) =
((s, s, 0, 0)
   \in ss_generate_prime m.-1 (Aut_to_Stk (K, V, delta, k0, F))).

move:H1.
case:m.
move:s_notempty.
rewrite-{1}s_.
rewrite-H.
by case:(dividestring n s).
elim.
move=>H1.
have {H1}:(length s<=n).
move:H1.
rewrite dividestringlength.
case smodn0:(length s mod n == 0).
move=>sn1.
move:smodn0.
move/eqP.
rewrite Nat.Div0.mod_eq.
rewrite sn1.
rewrite multE.
rewrite muln1.
move=>H1.
apply/lesub.
by rewrite-minusE.
rewrite-{2}(add0n 1).
rewrite!addn1.
move=>[sn].
apply/ltnW/ltP/Nat.div_small_iff;[rewrite H;by rewrite addn1|done].
move/subnKC=>H1.
simpl.
rewrite automaton_collect.
rewrite in_app.
have H2:(dstar delta k0 s \in F) =
((s, s, 0, 0)
   \in [seq (l', l', 0, 0)
          | l' <- accepts (K, V, delta, k0, F)
                    (language' (Datatypes.length K + 1) V)]).


have H2:(forall (l:list string)(s:string),(s,s,0,0)\in[seq (t,t,0,0)|t<-l]
=(s\in l)).
elim.
done.
move=>a l H2 s0.
simpl.
rewrite!in_cons.
have H3:((s0, s0, 0, 0) == (a, a, 0, 0))=(s0==a).
apply/bool_eqsplit.
split.
move/eqP=>[_ s0a].
apply/eqP/s0a.
move/eqP=>s0a.
apply/eqP.
repeat f_equal;apply/s0a.
rewrite H3.
case:(s0==a);simpl;[done|apply/H2].
rewrite H2=>{H2}.
rewrite/accepts.
rewrite mem_filter.
simpl.
rewrite Vwords.
simpl.
rewrite automaton_collect.
suff H2:(s \in language' (Datatypes.length K + 1) V).
rewrite H2;by case:(dstar delta k0 s \in F).
rewrite-H.
rewrite-H1.
apply/language'lemma.
move:s_notempty.
by case s.
done.

rewrite-H2.
suff H3:((s, s, 0, 0)
      \in [seq startDomino (l_index (dstar delta k0 s0) K + 1) s0
             | s0 <- language (Datatypes.length K + 1) V])=false.
by rewrite H3;case:(dstar delta k0 s \in F).
apply/bool_eqsplit.
split;[|done].
case lens:(length s == n).

elim (language (Datatypes.length K + 1) V).
done.
move=>a l H3.
simpl.
rewrite in_cons.
suff H4:((s, s, 0, 0) == startDomino (l_index (dstar delta k0 a) K + 1) a)=false.
by rewrite H4.
apply/bool_eqsplit.
split;[|done].
move/eqP=>H4.
have:startDomino_inverse (s, s, 0, 0) =
 startDomino_inverse (startDomino (l_index (dstar delta k0 a) K + 1) a).
by rewrite H4.
case sa:(s==a).
rewrite-(eqP sa).
rewrite startDominoCollect.
simpl.
rewrite subnn.
move=>[].
by rewrite addn1.
rewrite (eqP lens).
rewrite H.
rewrite!addn1.

done.
move:H5.
rewrite-sa=>{sa}.
move/(map_f _ _ startDomino_inverse).
Compute startDomino_inverse (s,s,0,0).
map_f
case:




rewrite


r
map_f.

move:H1.

move:s_.
rewrite-H.
move:H1.
case:m.
move=>H1 s_.
move:s_notempty.
rewrite-{1}s_.
move:H1.
by case:(dividestring n s).
case.
rewrite dividestringlength.
move=>H1.
have {}H1:(length s<=n).
move:H1.
case smodn0:(length s mod n == 0).
move=>sn1.
move:smodn0.
move/eqP.
rewrite Nat.Div0.mod_eq.
rewrite sn1.
rewrite multE.
rewrite muln1.
move=>H1.
apply/lesub.
by rewrite-minusE.
rewrite-{2}(add0n 1).
rewrite!addn1.
move=>[sn].
apply/ltnW/ltP/Nat.div_small_iff;[rewrite H;by rewrite addn1|done].
move:H1.
move/subnKC=>H1 _.


Search (_+(_-_)=_).
move=>_.
simpl.
p := 2.
have {}H1:(s\in(accepts(K,V,delta,k0,F)(language'(Datatypes.length K+1)V))).
rewrite/accepts.
rewrite mem_filter.


Search (_/_=0).
apply/leP.
Search (_<=_).
simpl.


Search (_ mod _ = _).

sort.
pass.
move=>
have lens:(length s <= n).


rewrite-{1}s_.
move:s_ H1.
rewrite
elim:m.
case:(dividestring n s);[|done].

rewrite/ss_generate_prime.
have H2:(forall d:Domino,s = ss_language_f (s,t,m,n)).
done.
rewrite H2.
rewrite-{1}(appendEmp s).
rewrite lrcheck'lemma;[|apply/Vwords|apply/Vwords|done].
rewrite (_:s==s=true);[simpl;apply/H2|by apply/eqP].
have:()


move:H2.
by simpl;rewrite automaton_collect.

suff H2:((dstar delta k0 s \in F)<->((s,s,0,0)\in ss_generate_prime (length s)
                   (Aut_to_Stk (K, V, delta, k0, F)))).
destruct H2.
apply/bool_eqsplit.
split.
move=>H3.
simpl.
rewrite{1}(_:s=ss_language_f (s,s,0,0));[|done].
rewrite automaton_collect.
apply/map_f.
rewrite mem_filter.
simpl.
rewrite (_:length s == length s = true);[simpl|by apply/eqP].
rewrite!substringeq.
rewrite-{1}(appendEmp s).
rewrite lrcheck'lemma;[|apply/Vwords|apply/Vwords|done].
rewrite (_:s==s=true);[simpl|by apply/eqP].

move:(H0 H3).
by simpl;rewrite automaton_collect.
simpl.
rewrite{1}(_:s=ss_language_f (s,s,0,0));[|done].
rewrite automaton_collect.
move/map_f.
rewrite mem_filter.
simpl.
rewrite (_:length s == length s = true);[simpl|by apply/eqP].
rewrite!substringeq.
rewrite-{1}(appendEmp s).
rewrite lrcheck'lemma;[|apply/Vwords|apply/Vwords|done].
rewrite (_:s==s=true);[simpl|by apply/eqP].
case H2:(dstar delta k0 s \in F).
move=>H3.

apply/bool_eqsplit.
split.
move=>H2.
simpl.
rewrite automaton_collect.
rewrite/ss_language_prime.
rewrite{1}(_:s=ss_language_f (s,s,0,0));[|done].
rewrite map_f.
done.
rewrite mem_filter.
Search filter.
rewrite-filter_map.
rewrite mem_filter.
simpl.
suff H2:((dstar delta k0 s \in F)<->((s,s,0,0)\in ss_generate_prime (length s)
                   (Aut_to_Stk (K, V, delta, k0, F)))).
destruct H2.
split.

rewrite/ss_language_prime.
simpl.
rewrite automaton_collect.
rewrite mem_filter.
simpl.

rewrite-{1}(dividestringlemma n s).
elim m
case H2:(dividestring n s).
rewrite concatdstar.

rewrite/ss_language_prime.
suff:((dstar delta k0 s \in F)=((s,s,0,0)\in ss_generate_prime (length s)
                   (Aut_to_Stk (K, V, delta, k0, F)))).
case:(dstar delta k0 s \in F)=>H2.
rewrite{1}(_:s=ss_language_f (s,s,0,0));[|done].
rewrite map_f;[done|].
rewrite mem_filter.
rewrite-H2.
by elim s.
rewrite{1}(_:s=ss_language_f (s,s,0,0));[|done].
rewrite map_f.
Search filter.
rewrite-filter_map.
rewrite mem_filter.
rewrite map_f.

suff:(dstar delta k0 s \in F) =
(s \in ss_language_prime m (Aut_to_Stk (K, V, delta, k0, F))).

have:(m<=length s);[rewrite-H1;apply/dividestringlength|].
move/subnKC=>H2.
rewrite-H2=>{H2}.
rewrite/ss_language_prime.
suff H2:()
elim (length s - m).
by rewrite addn0.
move=>n0 H2.
rewrite addnS.
rewrite/ss_language_prime.
have H3:((s\in ss_language_prime(m + n0).+1(Aut_to_Stk (K, V, delta, k0, F)))
=
  )
simpl.
have H3:(Aut_to_Stk (K, V, delta, k0, F) = 
  (if (k0 \in K) && ([::] == [seq f <- F | f \notin K])
          then
           (V, [seq (v, v) | v <- V],
            ([seq (l', l', 0, 0)
                | l' <- accepts (K, V, delta, k0, F)
                          (language' (Datatypes.length K + 1) V)] ++
             [seq startDomino (l_index (dstar delta k0 s0) K + 1) s0
                | s0 <- language (Datatypes.length K + 1) V])%list,
            ([seq extentionDomino
                    (l_index (dstar delta (nth 999 K (length t - 1)) s0) K +1)
                    s0 t
                | s0 <- language (Datatypes.length K + 1) V,
                  t <- language' (Datatypes.length K) V] ++
             [seq stopDomino s0 t
                | t <- language' (Datatypes.length K) V,
                  s0 <- accepts (K, V, delta, nth 999 K (length t - 1), F)
                          (language' (Datatypes.length K + 1) V)])%list)
          else ([::], [::], [::], [::]))).
by simpl.
rewrite-H1.
elim s.
by case n.
move=>a s0 H2.
simpl.
by[].
case n.
simpl.
case s.
move:s_notempty;by rewrite H2.

case n.
by[].
rewrite-H2.

simpl.
by[].
rewrite/ss_language_prime.




destruct m.
have {}H1:(dividestring n s)=nil;[move:H1;by case (dividestring n s)|];
move:s_;rewrite-H;rewrite H1;simpl;move:s_notempty;by case s.

move:s_;rewrite-H=>s_.
apply bool_eqsplit.

destruct m.
rewrite/ss_accept_prime.
rewrite/Aut_to_Stk.
rewrite automaton_collect;rewrite Vwords;simpl.
rewrite/ss_language.

rewrite/Aut_to_Stk.
suff H2:()
move/H.
by[].
rewrite-s_.
(dividestring (Datatypes.length K + 1) s).
move:s_;rewrite s_length;move:s_notempty;by case s.
move=>s_length;move:(dividestring)
rewrite concatdstar.

have nonaccept:(forall s:string,accept (K, V, delta, k0, F) s = false).
move=>s0;simpl;case:(Vword s0 V);[simpl|done];by rewrite H.
rewrite H.
rewrite andb_false
case:H.
move:k0inK;[|].
Search (~~_->_).

have{}k0inK:(k0\in K = false);[move:k0inK;by case (k0\in K)|].
have nonaccept:(forall s:string,accept (K, V, delta, k0, F) s = false).
by move=>s0;simpl;rewrite k0inK;rewrite!andb_false_r;rewrite!andb_false_l.
have acceptsempty:(forall l:list string,accepts (K,V,delta,k0,F) l = nil).
rewrite/accepts.

rewrite k0inK. rewrite!andb_false_r;rewrite!andb_false_l.
rewrite nonaccept.
[|rewrite!andb_false_r;rewrite!andb_false_l].
simpl.
.case H2:(length s <= Datatypes.length K + 1).
simpl.
(*↓の定義では不十分*)
Theorem REG_RSL (M:Automaton)(s:string):
s!="" -> accept M s -> (ss_accept (Aut_to_Stk M) s).
Proof.
move=>s_notempty H.
destruct M as ((((K,V),delta),k0),F).
have H1:(Vword s V);[by move:H;rewrite/accept;case (Vword s V)|].
case H2:(length s <= Datatypes.length K + 1).
by have {}s_notempty:(0<length s);[move:s_notempty;elim s|rewrite p1].
have {s_notempty}H2:(length s > Datatypes.length K + 1);
[by rewrite ltnNge;move:H2;case (length s <= Datatypes.length K + 1)|].

have concatlemma:(forall(s:string)(l:list string),
  s++(concat "" l)=concat "" (s::l));
[move=>s' l;have appends0:(forall s:string,s++""=s);
[by elim;[|move=>a s1 H';simpl;f_equal]|];by case:l|].

have dstarlemma:(forall(s1 s2:string)(k:State)(delta:State->Symbol->State),
  dstar delta k (s1++s2) = dstar delta (dstar delta k s1) s2);
[by move=>s2 s3 k d;move:k;elim:s2;simpl|].

have {concatlemma dstarlemma}concatdstar:
  (forall (s:string)(l:list string)(k:State)(delta:State->Symbol->State),
  dstar delta k(concat "" (s::l))=dstar delta(dstar delta k s)(concat "" l));
[move=>s2 l k d;rewrite-dstarlemma;by rewrite concatlemma|].

case K':K;[move:H;rewrite K';simpl;rewrite (_:k0 \in [::]=false);[|done];
by rewrite!andb_false_r;rewrite!andb_false_l|];rewrite-K'.
case V':V;[move:H1;rewrite V';move:H2;by case s|];rewrite-V'.

simpl.


have StartDomino:(forall (s1:string),Vword s1 V ->
length s1 = Datatypes.length K + 1 ->
  (s1, substring 0 (Datatypes.length K - l_index (dstar delta k0 s1) K)
  s1, 0, 0) \in [seq startDomino (l_index (dstar delta k0 s0) K + 1) s0
       | s0 <- language (Datatypes.length K + 1) V]).
move=>s1 H3 H4;rewrite-H4;
have {H3}:(s1\in language (length s1) V);[by apply languagelemma|].
elim (language (length s1) V);[done|];
move=>a l H3;simpl;rewrite !in_cons.
case H5:(s1==a).
rewrite-(eqP H5).
rewrite/startDomino.
rewrite H4.
rewrite!addn1.
rewrite subSS.
case:((s1, substring 0 (Datatypes.length K - l_index (dstar delta k0 s1) K)
  s1, 0, 0)
      \in [seq (s0,
                substring 0 (length s0 - (l_index (dstar delta k0 s0) K + 1))
                  s0, 0, 0)
          |s0 <- l]);[by rewrite orb_true_r|move=>H6{H6};rewrite orb_false_r].
by case (substring 0 (Datatypes.length K - l_index (dstar delta k0 s1) K) s1).
simpl.
by case:((s1, substring 0 (Datatypes.length K - l_index (dstar delta k0 s1) K)
  s1, 0, 0) == startDomino (l_index (dstar delta k0 a) K + 1) a).

have ExtentionDomino:(forall (s1 s2:string)(k:State),k\in K -> Vword s1 V ->
  Vword s2 V -> length s1 = Datatypes.length K + 1 -> 
  length s2 = l_index k K + 1 -> (("","",0,0),(s1,s2++
    (substring 0 (Datatypes.length K - l_index (dstar delta k s1) K) s1),
    0,length s2)) \in [seq extentionDomino
           (l_index (dstar delta (nth 999 K (length t - 1)) s0) K + 1) s0 t
       | s0 <- language (Datatypes.length K + 1) V,
         t <- language' (Datatypes.length K) V]).
move=>s1 s2 k kinK vwords1 vwords2 H3 H4.
have H5:(s1\in language (length s1) V);[by apply languagelemma|].
have H6:(s2\in language' (Datatypes.length K) V).
have:(l_index k K < Datatypes.length K);[by move:kinK;elim K;[|
move=>a l H6;simpl;rewrite in_cons;case:(k==a)]|].
rewrite-(ltn_add2r 1 (l_index k K) (Datatypes.length K)).
rewrite-H4.
rewrite addn1.
move/ltnSE.
have {}H4:(0<length s2);[move:H4;rewrite addn1;by case s2|].
move/subnKC=>{}H3.
move:(language'lemma s2 V ((Datatypes.length K)-length s2) H4 vwords2).
by rewrite H3.
rewrite-subSS.
rewrite-addn1.
rewrite-(addn1 (l_index (dstar delta k s1) K)).
rewrite-H3=>{vwords1 vwords2 H3}.
have H7:(("", "", 0, 0,(s1,s2 ++ 
  substring 0 (length s1 - (l_index (dstar delta k s1) K + 1)) s1, 0,
  length s2))=extentionDomino (l_index (dstar delta
    (nth 999 K (length s2 - 1)) s1) K + 1) s1 s2).
rewrite{2}H4.
have H7:(nth 999 K (l_index k K + 1 - 1))=k.
rewrite addn1;rewrite subn1;simpl;move:kinK;elim K;[done|];move=>a l H7;simpl;
rewrite in_cons;by case H8:(k==a);[rewrite (eqP H8)|].
rewrite H7=>{H7}.
by rewrite/extentionDomino.
rewrite H7=>{H7}.
apply (map_f' (fun s t=> extentionDomino 
  (l_index (dstar delta (nth 999 K (length t - 1)) s) K + 1) s t)
    (language (length s1) V) (language' (Datatypes.length K) V) s1 s2 H5 H6).

have StopDomino:(forall s t:string,Vword s V -> Vword t V -> )

elim (l_index (dstar delta k s1) K + 1).
simpl.

orb_true_r
move/(map_f H5).
rewrite/convert_D.
move:H6.
elim (language' (Datatypes.length K) V).
by[].
move=>a l H6.
move:H5.
elim (language (length s1) V).
by[].
move=>a0 l0 H5.

simpl.
rewrite!in_cons.
case H7:(s1==a);[|simpl].


Search (_+(_-_)).


Search (_+_<_+_).
rewrite-addnA.
move=>

simpl.
languagelemma
rewrite/createDomino.
case H4:(language (Datatypes.length K + 1) V).
have H5:(forall n:nat,language n V == nil=false);
[by elim;[|move=>n H5;simpl;case H6:(language n V);
[move:H5;rewrite H6|rewrite V']]|].
move:H4.
move/eqP.
by rewrite H5.


rewrite addn1.
case (Datatypes.length K).

simpl.
case (Datatypes.length K + 1)
simpl.




simpl.
have H3:(let s1 := substring 0 (Datatypes.length K + 1) s in
  let s2 := substring (Datatypes.length K + 1)
    (length s - (Datatypes.length K + 1)) s in
  let s1' := substring 0 
    (length s1 - (l_index (dstar delta s0 s1) K) - 1) s1 in
  (s1,s1',0,0)\in (createDomino (language (Datatypes.length K + 1) V)
    s0 (K, V, delta, s0, F))%list).
move=>s1 s2 s1'.
have H3:(s1++s2=s);[by rewrite substringlemma1|].
have H4:(Vword s1 V);[move:H1;rewrite-H3;by elim s1;
[|simpl;move=>a s3;case:(a\in V)]|].
have H5:(Vword s2 V);[move:H1;rewrite-H3;by elim s1;
[|simpl;move=>a s3;case:(a\in V)]|].
have H6:(length s1 == (Datatypes.length K + 1));
[by move:H2;move/ltnW=>H2;rewrite substringlemma2|].
rewrite-(eqP H6).
have:(s1\in language (length s1) V);
[by rewrite languagelemma|].
elim (language (length s1) V).
by [].
move=>a l H7;rewrite !in_cons;case H8:(s1==a).
by rewrite-(eqP H8);rewrite/s1';
case:((s1, substring 0 (length s1 - l_index (dstar delta s0 s1) K - 1)
  s1, 0, 0) \in createDomino l s0 (K, V, delta, s0, F));
[rewrite orb_true_r|rewrite orb_false_r].
by case:((s1, s1', 0, 0) ==
 (a, substring 0 (length a - l_index (dstar delta s0 a) K - 1) a, 0, 0));
[rewrite orb_true_l|rewrite orb_false_l].

have H4:(forall s)
by [].
rewrite (_=(s1==a)).
rewrite/createDomino.

have {substringlemma}split_s:
  (let s1 := substring 0 (Datatypes.length K + 1) s in
   let s2 := substring (Datatypes.length K + 1)
    (length s - (Datatypes.length K + 1)) s in
   let state := ).
move=>s2 s3.
by rewrite substringlemma.
move:(let a := 2 in _).
move=>s2 s3.

congruence.
rewrite substring0s.
;[by move:H2;elim s2|].
simpl.
move=>H3.
by [].
have H2:(forall (n:nat),s=(substring 0 n s)++(substring n (length s - n) s)).
elim.
by rewrite substring00.
simpl.
case s.
by [].
move=>a s2.
case.
simpl.
by rewrite substring00.
simpl.
move=>n H2.

simpl.
f_equal.
congr H2.
move=>n.
case s.
by case n.
simpl.
elim n.
by [].
move=>n0.
case n0.
simpl.
have 
by [].
simpl.
have H2:(s = (substring 0 (Datatypes.length K + 1) s)++
  (substring (Datatypes.length K + 1) (length s) s)).
elim (Datatypes.length K + 1).
by have H2:(substring 0 0 s="");[case s|
rewrite H2;elim s;[|simpl;move=>a s2 H3;rewrite-H3]].
case s.
simpl.
by [].
move=>a s2 n H2.
simpl.
move=>a s2 H2.
elim s;[by case (Datatypes.length K + 1)|].
move=>a s2 H2.
have H3:(substring 0 (Datatypes.length K + 1) (String a s2)=
  String a (substring 0 (Datatypes.length K + 1) s2)).

simpl.
case (Datatypes.length K + 1).
simpl.
Search (_-> substring _ ).





Lemma p2 (K:States)(V:Symbols)(delta:State->Symbol->State)(s0:State)(F:States)
(s1 s2:string):accept (K,V,delta,s0,F) (s1++s2) ->
(length s1) = (List.length K + 1) -> (length s2 <= (List.length K + 1)) ->
(ss_accept (Aut_to_Stk (K,V,delta,s0,F)) (s1++s2)).

move=>H H1 H2.
case H3:(length s2).
have {}H3:(s2="");[by move:H3;elim s2|].
have {}H3:(s1 ++ s2 = s1);
[by rewrite H3;elim s1;[|move => a s H4;simpl;f_equal]|rewrite H3].
have H4:(0<length s1);[by rewrite H1;rewrite addn1|].
move:H;rewrite H3;move=>H.
have {}H1:(length s1 <= Datatypes.length K + 1);[by rewrite H1|].
by rewrite p1.


simpl.
Locate "++".
Search (append _ _ = _).
case H3:(length s <= (Datatypes.length K + 1));[by rewrite p1|].
have{H3}H2:(s = (substring 0 (Datatypes.length K + 1) s)++
  (substring (Datatypes.length K + 1) (length s) s)).
elim s;[by case:(Datatypes.length K + 1)|].
rewrite/=.
case H4:(Datatypes.length K + 1);[by move:H4;rewrite addn1|].
move=>a s2 H5.
rewrite/=.



simpl.


Theorem REG_RSL (M:Automaton)(s:string):
accept M s -> (ss_accept (Aut_to_Stk M) s).
Proof.
split.

elim s.
move => H.

















