From mathcomp Require Import all_ssreflect.

Require Import AutomatonModule StickerModule myLemma Arith.

Fixpoint language(n:nat)(symbol:finType):seq (seq symbol):=
match n with
|0 => [::nil]
|S n' => [seq s::l|l<-language n' symbol,s<-enum symbol]
end.

Fixpoint language' (n:nat)(symbol:finType):seq (seq symbol):=
(*n文字以下の文字列を生成
Ex:language 2 [::"a"%char;"b"%char] -> [::"a";"b";"aa";"ab";"ba;";"bb"]*)
match n with
|0 => nil
|S n' => (language' n' symbol)++(language n symbol)
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

Definition wkaccept{state symbol:finType}(M:@automaton state symbol)
(s:seq symbol):option domino :=
match s with
|a::s'=>
  if accept M s then
    Some(WK(mkwkzip a s'))
  else
    None
|_ => None
end.
Definition startDomino{state symbol:finType}(M:@automaton state symbol)
(s:seq symbol):domino :=
let n := (index(dstar(delta M)(init M)s)(enum state) + 1) in
let w := take(size s - n)s in
let r := drop(size s - n)s in
let rho := zip (enum symbol) (enum symbol) in
match w,r with
|a::w',b::r' => R(mkwkzip a w')(mkend true b r')
|_,_ => null
end.
Definition extentionDomino{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol):domino*domino:=
let s0 := nth (init M) (enum state) (size t - 1) in
let n := index (dstar (delta M) s0 s) (enum state) + 1 in
let w := take(size s - n)s in
let r := drop(size s - n)s in
match t,w,r with
|a::t',b::w',c::r'=>(null,LR(mkend false a t')(mkwkzip b w')(mkend true c r'))
|_,_,_ => (null:@domino symbol (zip(enum symbol)(enum symbol)),null)
end.
Definition stopDomino{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol):option(domino*domino):=
let s0 := nth (init M) (enum state) (size t - 1) in
match s,t with
|a::s',b::t'=>
  if (dstar (delta M) s0 s)\in final M then
    Some(null:@domino symbol (zip(enum symbol)(enum symbol)),
      L(mkend false a s')(mkwkzip b t'))
  else
    None
|_,_=>None
end.

Lemma language'nil(n:nat)(symbol:finType):
all(fun p=>p!=nil)(language' n symbol).
Proof.
elim:n.
done.
move=>n H.
rewrite/=all_cat H/==>{H}.
elim:(language n symbol).
done.
move=>a l H{n}.
rewrite/=all_cat H Bool.andb_true_r.
elim:(enum symbol).
done.
move=>b{}l{}H.
by rewrite/=.
Qed.
Lemma languagelength(n:nat)(symbol:finType):
all(fun p=>size p==n)(language n symbol).
Proof.
elim:n.
done.
move=>n.
rewrite/=.
elim:(language n symbol).
done.
move=>a l H.
simpl.
move/andP.
case.
move=>H1/H=>{}H.
rewrite all_cat H Bool.andb_true_r=>{l H}.
elim:(enum symbol).
done.
move=>b l H.
by rewrite/=H Bool.andb_true_r eqSS/eqP H1.
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
Lemma st_correctP{state symbol:finType}(M:@automaton state symbol):
all st_correct(filter_option[seq wkaccept M s|s<-language'(#|state|.+1)symbol]
  ++[seq startDomino M s|s <- language(#|state|.+1)symbol]).
Proof.
rewrite all_cat.
apply/andP.
split.
move:(language'nil #|state|.+1 symbol).
elim:(language' #|state|.+1 symbol).
done.
move=>a l H.
simpl.
move/andP.
case=>H1.
move/H=>{}H.
rewrite{1}/wkaccept.
move:H1.
case:a.
done.
move=>a l0 _.
by case:(accept M (a::l0)).

move:(languagelength #|state|.+1 symbol).
elim:(language #|state|.+1 symbol).
done.
move=>a l H.
rewrite/=.
move/andP.
case=>/eqP H1.
move/H=>{}H.
rewrite H Bool.andb_true_r.
move:H1.
case:a.
done.
simpl.
move=>a{H}l[H1].
rewrite/startDomino/=.
rewrite H1.
remember(dstar (delta M) (delta M (init M) a) l) as s.
case H:(take(#|state|.+1 - (index s(enum state) + 1))(a :: l)).
have:size(take(#|state|.+1-(index s(enum state) + 1))(a :: l))=0.
by rewrite H.
have H2:(0 < index s (enum state) + 1);[by rewrite addn1|].
have H3:(0 < #|state|.+1);[done|].
rewrite size_take/=H1 ltn_subrL H2 H3/=addn1 subSS =>{H1 H2 H3 Heqs a l}H.
move:(fin_index s).
by rewrite-subn_gt0 H.
rewrite addn1.
case H2:(drop(#|state|.+1 - (index s(enum state)).+1)(a :: l)).
have{H2}:size(drop(#|state|.+1 - (index s(enum state)).+1)(a :: l))=0.
by rewrite H2.
rewrite size_drop/=H1 subSS subSn.
done.
apply/leq_subr.
done.
Qed.

Definition Aut_to_Stk{state symbol:finType}(M:@automaton state symbol):=
let A1 := filter_option[seq wkaccept M s|s<-language'(#|state|.+1)symbol] in
let A2 := [seq startDomino M s|s <- language(#|state|.+1)symbol] in
let D1 := [seq extentionDomino M s t|s<-language(#|state|.+1)symbol,
                                     t<-language'(#|state|)symbol] in
let D2 := filter_option[seq stopDomino M s t|
  s <- language'(#|state|.+1)symbol,t <- language'(#|state|)symbol] in
{|start:=(A1++A2);extend:=(D1++D2);startP:=st_correctP M|}.


Lemma lang_gen{state symbol:finType}(M:@automaton state symbol)(a:symbol)
(s:seq symbol)(n:nat):(a::s\in (ss_language_prime n (Aut_to_Stk M))) 
 = (WK(mkwkzip a s)\in ss_generate_prime n (Aut_to_Stk M)).
Proof.
apply/bool_eqsplit.
split.
rewrite/ss_language_prime.
elim(ss_generate_prime n (Aut_to_Stk M)).
done.
move=>a0 l H {n}.
rewrite/=.
case H1:(is_wk a0);[simpl|move/H=>{}H;apply/orP;by right].
rewrite!in_cons.
move/orP=>[/eqP{}H|].
apply/orP.
left.
rewrite/mkwkzip.
move:H.
rewrite/decode{H1}.
case:a0;(try done).
case=>st ni rh H.
apply/eqP.
f_equal.
apply/eqP.
rewrite/eq_op/=/wk_eqb/=(_:(a,a)::zip s s=zip(a::s)(a::s));[|done].
have H1:unzip1 st=unzip2 st.
move:rh{ni H}.
elim:st.
done.
move=>a0 l0 H.
destruct a0.
simpl.
move/andP=>[]H1/H{}H.
f_equal;[|apply/H].
move:H1.
elim:(enum symbol).
done.
move=>{}a{}l{}H.
rewrite/=!in_cons.
move/orP=>[/eqP[H1 H2]|].
by subst.
done.
by rewrite H{2}H1 zip_unzip.
move/H=>{}H.
apply/orP.
by right.

rewrite/ss_language_prime/mkwkzip.
elim:(ss_generate_prime n (Aut_to_Stk M)).
done.
move=>b l H.
rewrite/=in_cons=>/orP[/eqP|/H]{}H.
rewrite-H/=in_cons.
apply/orP.
left.
apply/eqP.
f_equal.
by rewrite unzip1_zip.
case:(is_wk b);[rewrite/=in_cons;case:(a :: s == decode b)|];by rewrite H.
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


Lemma add00(m n:nat):m+n=0<->m=0/\n=0.
Proof.
split;[|move=>[m0 n0];by rewrite n0 addn0].
case:m;[by rewrite add0n|move=>m;by rewrite addSn].
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
Lemma fin_zip_neq{f:finType}(x y:seq f):x<>y->size x=size y->
all(fun p=>p\in zip(enum f)(enum f))(zip x y)=false.
Proof.
move:y.
elim:x.
by case.
move=>a x H.
case.
done.
move=>b y H1.
have{}H1:a<>b\/x<>y.
case_eq(a==b)=>/eqP ab;case_eq(x==y)=>/eqP xy;subst;by [|right|left|right].
destruct H1.
suff H2:(a, b) \in zip (enum f) (enum f)=false;[by rewrite/=H2|].
elim:(enum f).
done.
move=>a0 l H1.
rewrite/=in_cons H1 Bool.orb_false_r.
apply/eqP.
move=>[H2 H3].
by subst.
move:H0.
move/H=>{}H.
move=>[]/H=>{}H.
by rewrite/=H Bool.andb_false_r.
Qed.

Lemma mu'lemma{state symbol:finType}(M:@automaton state symbol)
(s t u:seq symbol):#|state|.+1<=size s -> size t = #|state|.+1 -> u<>nil->
mu' (startDomino M s)(extentionDomino M t u)=
if drop(size s-((index(dstar(delta M)(init M)s)(enum state)).+1))s == u then
  Some (startDomino M (s++t))
else
  None.
Proof.
case_eq s;[done|move=>a0 l0 s';rewrite-s'].
case_eq t;[done|move=>a1 l1 t';rewrite-t'].
case_eq u;[done|move=>a2 l2 u';rewrite-u'].
remember ((index(dstar(delta M)(init M)s)(enum state)).+1) as n.
move=>lens lent unil.
have lens':n<=#|state|;[rewrite Heqn;apply/fin_index|].
have{}lens':n<size s;[by apply/(leq_ltn_trans lens')|].
have lens'':n<=size s;[apply/ltnW/lens'|].

rewrite/extentionDomino u'-u'.
case_eq(take(size t -
       (index (dstar (delta M) (nth (init M) (enum state) (size u - 1)) t)
          (enum state) + 1)) t);[move=>H|move=>a3 l3 t1].
have{H}:size(take(size t -
       (index (dstar (delta M) (nth (init M) (enum state) (size u - 1)) t)
          (enum state) + 1)) t)=0;[by rewrite H|].
have H:(0 < index (dstar (delta M) (nth (init M) (enum state) (size u - 1)) t)
         (enum state) + 1);[by rewrite addn1|].
have H1:(0 < size t);[by rewrite t'|].
rewrite size_take ltn_subrL H H1/=lent addn1 subSS=>{H1}H.
move:(fin_index (dstar (delta M) (nth (init M) (enum state) (size u - 1)) t)).
by rewrite-subn_gt0 H.
case_eq(drop(size t -
       (index (dstar (delta M) (nth (init M) (enum state) (size u - 1)) t)
          (enum state) + 1)) t);[move=>H|move=>a4 l4 d2].
have:size(drop(size t -
       (index (dstar (delta M) (nth (init M) (enum state) (size u - 1)) t)
          (enum state) + 1)) t)=0;[by rewrite H|].
have{}H:index(dstar (delta M) (nth (init M) (enum state) (size u - 1)) t)
          (enum state) < size t.
rewrite lent ltnS;apply/ltnW/fin_index.
by rewrite size_drop addn1(subKn H).

rewrite/=/startDomino addn1-Heqn.
case_eq(take (size s - n) s);[move=>H|move=>a5 l5 t2].
have:size(take(size s - n)s)=0;[by rewrite H|].
have{}H:(0<n);[by rewrite Heqn|].
have H1:(0<size s);[by rewrite s'|].
rewrite size_take ltn_subrL H H1/==>{H1}H.
move:lens';by rewrite-subn_gt0 H.
case_eq(drop (size s - n) s);[move=>H|move=>a6 l6 d1;rewrite-d1].
have:size(drop(size s - n)s)=0;[by rewrite H|].
by rewrite size_drop (subKn(ltnW lens')) Heqn.

have cons_zip:forall(T:Type)(a:T)(l:seq T),zip(a::l)(a::l)=(a,a)::zip l l.
done.
rewrite/mu/mkend/mu_end.
case_eq(drop (size s - n) s == u)=>/eqP ueq.
rewrite-u'-d1 ueq(_:size u==size u);[rewrite u' cons_zip|by apply/eqP].
remember(Bool.bool_dec(all(in_mem^~ (mem (zip (enum symbol) (enum symbol))))
         ((a2, a2) :: zip l2 l2)) true)as B.
rewrite-HeqB{HeqB}.
have{}H:all (in_mem^~ (mem (zip (enum symbol) (enum symbol))))
       ((a2, a2) :: zip l2 l2) = true;[rewrite-cons_zip;apply/zip_rhoP|].
destruct B;[f_equal=>{H}|contradiction].

case_eq((take(size (s ++ t) -
  (index (dstar (delta M) (init M) (s ++ t)) (enum state) + 1))(s ++ t)))
;[move=>H|move=>a7 l7 t3].
have:size(take(size (s ++ t) -
        (index (dstar (delta M) (init M) (s ++ t)) (enum state) + 1)) 
       (s ++ t))=0;[by rewrite H|].
have{}H:0<index(dstar(delta M)(init M)(s++t))(enum state)+1;
[by rewrite addn1|].
have H1:0 < size (s ++ t).
by rewrite size_cat s'/=addSn.
rewrite size_take ltn_subrL H H1/=size_cat lent addn1 addnS subSS-addnBA.
by rewrite s'/=addSn.
apply/ltnW/fin_index.

case_eq(drop(size (s ++ t) -
     (index (dstar (delta M) (init M) (s ++ t)) (enum state) + 1)) 
    (s ++ t));[move=>H|move=>a8 l8 d3].
have:size(drop(size (s ++ t) -
        (index (dstar (delta M) (init M) (s ++ t)) (enum state) + 1)) 
       (s ++ t))=0;[by rewrite H|].
rewrite size_drop subKn addn1.
done.
rewrite size_cat lent.
apply/ltn_addl.
rewrite ltnS.
apply/ltnW/fin_index.

f_equal.
rewrite/mkwkzip/mu_wk/=.
apply/eqP.
rewrite/eq_op/=/wk_eqb/=.
apply/eqP.
rewrite-!cons_zip-!zip_cat;[|done|done].
rewrite-cons_zip-!cat_cons-catA{cons_zip}.
suff H:((a5::l5)++(a2::l2)++(a3::l3)=(a7::l7)).
by f_equal.

rewrite-t2-u'-ueq-t1-t3 catA cat_take_drop take_cat-ueq(_:
size(s++t)-(index(dstar(delta M)(init M)(s++t))(enum state)+1)<size s=false)=>
{a2 a3 a4 a5 a6 a7 a8 l2 l3 l4 l5 l6 l7 l8 d1 d2 d3 t1 t2 t3 e u'}.
f_equal.
f_equal.
rewrite size_cat-addnBA.
rewrite add_subABA size_drop dstarLemma.
repeat f_equal.
by rewrite(subKn lens'')subn1 Heqn/=nth_index;[|apply/mem_enum].
rewrite addn1 lent ltnS.
apply/ltnW/fin_index.

rewrite size_cat-addnBA.
rewrite ltnNge.
apply/negbF/leq_addr.
rewrite addn1 lent ltnS.
apply/ltnW/fin_index.


rewrite/mkend.
have:a4::l4=a8::l8.
rewrite-d3-d2 drop_cat size_cat (_:size s+size t - 
(index(dstar(delta M)(init M)(s++t))(enum state)+1)<size s=false).
rewrite-addnBA.
rewrite add_subABA dstarLemma-ueq size_drop.
repeat f_equal.
by rewrite(subKn lens'')subn1 Heqn/=nth_index;[|apply/mem_enum].
rewrite addn1 lent ltnS.
apply/ltnW/fin_index.

rewrite-addnBA.
rewrite ltnNge.
apply/negbF/leq_addr.
rewrite addn1 lent ltnS.
apply/ltnW/fin_index.

move=>[H H1].
by subst.



case sizeu:(size (a6 :: l6) == size (a2 :: l2));[|done].
have H:zip (a6 :: l6) (a2 :: l2)=(a6,a2)::zip l6 l2;[done|].

remember(Bool.bool_dec
      (all (in_mem^~ (mem (zip (enum symbol) (enum symbol))))
         ((a6, a2) :: zip l6 l2)) true)as B.
rewrite H-HeqB.
have{}H:(all (in_mem^~ (mem (zip (enum symbol) (enum symbol))))
            ((a6, a2) :: zip l6 l2))=false.
move:sizeu.
rewrite-H-d1-u'=>/eqP sizeu.
by apply/fin_zip_neq.
destruct B.
move:H.
by rewrite e.
done.
Qed.


Lemma mu'lemma2{state symbol:finType}(M:@automaton state symbol)
(a:symbol)(s t u:seq symbol)(d:domino*domino): #|state|<=size s ->
Some d = (stopDomino M u t)->
mu'(startDomino M (a::s))d = 
if (drop (size s - (index(dstar(delta M)(init M)(a::s))(enum state)))(a::s))
  ==u then
  Some(WK(mkwkzip a (s++t)))
else
  None.
Proof.
move=>lens.
rewrite/stopDomino.
case_eq u;[done|move=>a0 l0 u'].
case_eq t;[done|move=>a1 l1 t'].

case:(dstar (delta M)(nth (init M)(enum state)(size(a1::l1) - 1)) (a0 :: l0)
    \in final M);[move=>[d'];rewrite d'{d'}/=/mu/startDomino|done].
case_eq(take(size (a :: s) -
       (index (dstar (delta M) (init M) (a :: s)) (enum state) + 1)) 
      (a :: s));[move=>H|move=>a2 l2 t1].
have:size(take(size (a :: s) -
       (index (dstar (delta M) (init M) (a :: s)) (enum state) + 1)) 
      (a :: s))=0.
by rewrite H.
have{}H:(0 < index (dstar (delta M) (init M) (a :: s)) (enum state) + 1).
by rewrite addn1.
have H1:(0 < size (a :: s));[done|].
rewrite size_take ltn_subrL H H1/=addn1 subSS{H H1}.
move/lesub/(leq_trans lens).
rewrite leqNgt.
suff H:index(dstar(delta M)(delta M(init M) a) s) (enum state) < #|state|.
by rewrite H.
apply/fin_index.
case_eq(drop(size (a :: s) - (index (dstar (delta M) (init M) (a :: s))
          (enum state) + 1))(a :: s));[move=>H|move=>a3 l3 d1].
have:size(drop(size (a :: s) -
       (index (dstar (delta M) (init M) (a :: s)) (enum state) + 1)) 
      (a :: s))=0;[by rewrite H|].
rewrite size_drop subKn addn1/=.
done.
rewrite ltnS.
suff H1:index (dstar (delta M) (delta M (init M) a) s) (enum state)<=#|state|.
by apply/(leq_trans H1).
apply/ltnW/fin_index.

case_eq(drop (size s - index (dstar (delta M) (delta M (init M) a) s) (enum state))
    (a :: s) == a0 :: l0).
have{}d1:drop(size s-(index(dstar (delta M) (init M) (a :: s)) (enum state))) 
       (a :: s) = a3 :: l3.
move:d1.
by rewrite/=addn1 subSS.
rewrite d1.
move/eqP=>ueq.
rewrite/mkend ueq(_:size(a0::l0)==size(a0::l0));[rewrite/mu_end|by apply/eqP].
have H:zip (a0 :: l0) (a0 :: l0)=(a0,a0)::zip l0 l0;[done|].
rewrite H.
remember(Bool.bool_dec
      (all (in_mem^~ (mem (zip (enum symbol) (enum symbol))))
         ((a0, a0) :: zip l0 l0)) true)as B.
rewrite-HeqB.
have{}H:all (in_mem^~ (mem (zip (enum symbol) (enum symbol))))
            ((a0, a0) :: zip l0 l0);[rewrite-H;apply/zip_rhoP|].
destruct B;[f_equal;f_equal=>{H}|contradiction].
rewrite(_:a0 :: l0 == a0 :: l0);[|by apply/eqP].
f_equal.
f_equal.
apply/eqP.
rewrite/eq_op/=/wk_eqb/=.
apply/eqP.
have H:forall(a:symbol)(l:seq symbol),
  zip (a :: l) (a :: l)=(a,a)::zip l l;[done|].
rewrite-!H-!zip_cat;[|done|done].
rewrite-!H-!cat_cons{H}.
suff H:((a2 :: l2) ++ a0 :: l0) ++ a1 :: l1=(a :: s) ++ a1 :: l1.
by f_equal.
f_equal.
by rewrite-t1-ueq-d1/=addn1 subSS cat_take_drop.


move=>ueq.
rewrite ueq.
move:ueq.
move/eqP=>ueq.
rewrite/mkend.
case sizeu:(size (a3 :: l3) == size (a0 :: l0));[|done].
rewrite/mu_end.
have H:forall(T:Type)(a b:T)(x y:seq T),zip(a::x)(b::y)=(a,b)::zip x y;[done|].
rewrite H.
remember(Bool.bool_dec
      (all (in_mem^~ (mem (zip (enum symbol) (enum symbol))))
         ((a3, a0) :: zip l3 l0)) true) as B.
rewrite-HeqB.
have H1:(all (in_mem^~ (mem (zip (enum symbol) (enum symbol))))
            ((a3, a0) :: zip l3 l0))=false.
rewrite-H.
have{}d1:drop(size s-(index(dstar(delta M)(init M)(a:: s)) (enum state))) 
       (a :: s) = a3 :: l3.
move:d1.
by rewrite/=addn1 subSS.
move:ueq.
rewrite d1=>ueq.
have{}sizeu:size (a3::l3)=size (a0::l0).
move:sizeu.
by move/eqP.

by apply/fin_zip_neq.

destruct B;[|done].
move:H1.
by rewrite e.
Qed.



Lemma filter_nil{e:eqType}(l:seq e)(P:e->bool):
[seq a<-[seq b <- l|P b]|~~P a]=nil.
Proof. by elim:l;[|move=>a l H;simpl;case H1:(P a);[rewrite/=H1|]]. Qed.
Lemma eq_mem_cons{e:eqType}(a:e)(l1 l2:seq e):l1 =i l2 -> a::l1 =i a::l2.
Proof.
rewrite/eq_mem=>H x.
rewrite!in_cons.
apply/orP.
case:(x==a);simpl.
by left.
move:(H x).
case:(x \in l2)=>{}H;rewrite H.
by right.
by case.
Qed.

Lemma eq_mem_cat{e:eqType}(x y z w:seq e):x=i y->z=i w->x++z=i y++w.
Proof.
rewrite/eq_mem=>H H1 x0.
move:(H x0)(H1 x0)=>{}H{}H1.
rewrite!mem_cat.
by destruct (x0\in z),(x0\in x),(x0\in y).
Qed.


Lemma filter_option_cat{T:Type}(x y:seq (option T)):
filter_option(x++y)=filter_option x++filter_option y.
Proof.
elim:x.
done.
move=>a x H.
simpl.
case:a;[|done].
move=>a.
rewrite cat_cons.
by f_equal.
Qed.
Lemma eq_memS{e:eqType}(x y:seq e):(x =i y)<->(y =i x).
Proof. split;by rewrite/eq_mem. Qed.
Lemma eq_memT{e:eqType}(x y z:seq e):(x =i y)->(y =i z)->(x=i z).
Proof.
rewrite/eq_mem=>H H1 x0.
move:(H x0)(H1 x0)=>{}H.
by rewrite-H.
Qed.
Lemma eq_mem_filter{e:eqType}(x y:seq e)(f:e->bool):(x =i y)->
[seq a<-x|f a]=i[seq a<-y|f a].
Proof.
rewrite/eq_mem=>H x0.
by rewrite!mem_filter-H.
Qed.
Lemma eq_mem_catC{e:eqType}(x y:seq e):x++y=i y++x.
Proof.
rewrite/eq_mem=>x0.
rewrite!mem_cat.
by destruct(x0\in x),(x0\in y).
Qed.
Lemma eq_mem_map'{e1 e2 e3:eqType}(x y:seq e1)(z:seq e2)(f:e1->e2->e3):
x=i y->[seq f a b|a<-x,b<-z]=i[seq f a b|a<-y,b<-z].
Proof.
move=>H.
elim:z.
have H1:forall(l:seq e1),[seq f a b|a<-l,b<-nil]=nil;[by elim|].
by rewrite!H1.
move=>c z H1.
have H2:forall(l:seq e1),[seq f a b | a <- l, b <- c::z]=i
  [seq f a c|a<-l]++[seq f a b|a<-l,b<-z].
elim.
done.
move=>a l H2.
remember(c::z)as z'.
rewrite/={1}Heqz'/=.
apply/eq_mem_cons.
rewrite catA.
have H3:([seq f a0 c | a0 <- l] ++ [seq f a b | b <- z]) ++
     [seq f a0 b | a0 <- l, b <- z]=i
      ([seq f a b | b <- z]++[seq f a0 c | a0 <- l]) ++
     [seq f a0 b | a0 <- l, b <- z].
apply/eq_mem_cat;[apply/eq_mem_catC|done].
apply/eq_memT;[|apply/eq_memS/H3].
rewrite-catA.
by apply/eq_mem_cat.
apply/eq_memS.
apply/eq_memT.
apply/H2.
apply/eq_memT;[|apply/eq_memS/H2].
apply/eq_mem_cat.
apply/eq_mem_map/eq_memS/H.
apply/eq_memS/H1.
Qed.

Lemma mem_filter_option(T : eqType)(x : T)(s : seq (option T)):
       x \in (filter_option s) <-> (Some x) \in s.
Proof.
elim:s.
done.
move=>a s H.
case:a;[move=>a|];rewrite/=!in_cons.
case H1:(Some x == Some a).
move:H1;move/eqP=>[/eqP H1];by rewrite H1.
have{}H1:x==a=false.
apply/eqP.
rewrite/not=>H2.
subst.
move:H1.
by move/eqP.
by rewrite H1.

have H1:(Some x == None)=false.
by apply/eqP.
by rewrite H1.
Qed.

Lemma eq_mem_filter_option{e:eqType}(x y:seq(option e)):
x=i y -> filter_option x =i filter_option y.
Proof.
rewrite/eq_mem=>H x0.
move:(H(Some x0))=>{H}.
elim:x.
case:y.
done.
move=>b y.
destruct b.
rewrite/=!in_cons.
case_eq(Some x0==Some s);[done|move/eqP=>H].
have{}H:x0==s=false.
apply/eqP.
rewrite/not=>H1.
by subst.
rewrite H/=!in_nil=>{}H.
rewrite{}H.
elim:y.
done.
move=>b y H.
destruct b.
rewrite/=!in_cons.
case_eq(Some x0==Some s0).
move/eqP=>[H1].
by rewrite H1(_:s0==s0).
move/eqP=>H1.
have{}H1:x0==s0=false.
apply/eqP.
rewrite/not=>H2.
by subst.
by rewrite H1.
by rewrite/=in_cons.
rewrite!in_nil=>H.
rewrite{}H/=in_cons(_:Some x0 == None=false)/=;[|done].
elim:y.
done.
move=>b y H.
destruct b.
rewrite/=!in_cons.
case_eq(Some x0==Some s).
move/eqP=>[H1].
by rewrite H1(_:s==s).
move/eqP=>H1.
have{}H1:x0==s=false.
apply/eqP.
rewrite/not=>H2.
by subst.
by rewrite H1.
by rewrite/=in_cons(_:Some x0==None=false).

move=>a x H.
destruct a.
rewrite/=!in_cons.
case_eq(Some x0 == Some s).
move/eqP=>[H1].
rewrite{}H1(_:s==s)/=;[|done]=>H1.
rewrite{H}H1.
elim:y.
done.
move=>b y H.
destruct b.
rewrite/=!in_cons.
case_eq(Some s==Some s0).
move/eqP=>[H1].
by rewrite H1(_:s0==s0).
move/eqP=>H1.
have{}H1:s==s0=false.
apply/eqP.
rewrite/not=>H2.
by subst.
by rewrite H1.
by rewrite/=in_cons.
move/eqP=>H1.
have{}H1:x0==s=false.
apply/eqP.
rewrite/not=>H2.
by subst.
by rewrite H1.
by rewrite/=in_cons(_:Some x0==None=false).
Qed.



Lemma startDomino_gen_prime2{state symbol:finType}(M:@automaton state symbol)
(n:nat):[seq startDomino M s|s <- language (n.+1*(#|state|.+1)) symbol] =i
  [seq d<-ss_generate_prime n (Aut_to_Stk M)|~~is_wk d].
Proof.
elim:n.
rewrite/=plusE addn0 map_cat filter_cat.
have H:[seq d <- filter_option
                 ([seq wkaccept M s | s <- language' #|state| symbol] ++
                  [seq wkaccept M s
                     | s <- [seq s :: l
                               | l <- language #|state| symbol,
                                 s <- enum symbol]])
        | ~~ is_wk d]=nil.
rewrite-map_cat/wkaccept.
elim:(language' #|state| symbol ++ [seq s :: l
                      | l <- language #|state| symbol, s <- enum symbol]).
done.
simpl.
move=>a l H.
case:a.
done.
move=>a l0.
by case:(accept M (a :: l0)).

rewrite H cat0s.
elim:[seq s :: l | l <- language #|state| symbol, s <- enum symbol].
done.
move=>a l{}H.
rewrite/=(_:~~ is_wk (startDomino M a)).
apply/eq_mem_cons/H.
rewrite/startDomino.
case:(take (size a - (index (dstar (delta M) (init M) a) (enum state) + 1)) a).
done.
move=>a0 l0.
by case:(drop(size a-(index(dstar (delta M) (init M) a) (enum state) + 1)) a).


move=>n H.
remember[seq startDomino M s | s <- language (n.+2 * #|state|.+1) symbol]as l.
remember(Aut_to_Stk M)as ASM.
rewrite/=filter_undup filter_cat filter_nil cat0s.
have H1:undup[seq d <- filter_option[seq mu' a d
                  | a <- [seq a <- ss_generate_prime n ASM | ~~ is_wk a],
                        d <- extend ASM]| ~~ is_wk d]=i
       [seq d <- filter_option [seq mu' a d
                  | a <- [seq a <- ss_generate_prime n ASM | ~~ is_wk a],
                        d <- extend ASM]   | ~~ is_wk d].
rewrite/eq_mem=>x.
by rewrite mem_undup.
apply/eq_memT/eq_memS/H1.
have{}H1:extend ASM = [seq extentionDomino M s t
  | s <- language #|state|.+1 symbol,t <- language' #|state| symbol] ++
     filter_option[seq stopDomino M s t
        | s <- language' #|state|.+1 symbol,t <- language' #|state| symbol].
by rewrite HeqASM.
move:H.
rewrite{}H1{ASM}HeqASM=>H.
remember[seq extentionDomino M s t | s <- language #|state|.+1 symbol,
                                t <- language' #|state| symbol]as A.
remember[seq stopDomino M s t | s <- language' #|state|.+1 symbol,
                                  t <- language' #|state| symbol]as B.
have{}H1:[seq d <- filter_option[seq mu' a d
                    | a <- [seq a <- ss_generate_prime n (Aut_to_Stk M)
                   | ~~ is_wk a], d <- A ++ filter_option B]| ~~ is_wk d] =i
          [seq d <- filter_option([seq mu' a d
                    | a <- [seq a <- ss_generate_prime n (Aut_to_Stk M)
                              | ~~ is_wk a], d <- A]++[seq mu' a d
                    | a <- [seq a <- ss_generate_prime n (Aut_to_Stk M)
                            | ~~ is_wk a],d <- filter_option B])| ~~ is_wk d].
apply/eq_mem_filter/eq_mem_filter_option/mem_allpairs_catr.
apply/eq_memT/eq_memS/H1.
have{H1}H:[seq d <- filter_option([seq mu' a d
                     | a <- [seq a <- ss_generate_prime n (Aut_to_Stk M)
                               | ~~ is_wk a], d <- A] ++
              [seq mu' a d| a <- [seq a <- ss_generate_prime n (Aut_to_Stk M)
                          | ~~ is_wk a],d <- filter_option B])| ~~ is_wk d]=i
          [seq d <- filter_option([seq mu' a d
     | a <- [seq startDomino M s | s <- language (n.+1 * #|state|.+1) symbol], d <- A] ++
               [seq mu' a d| a <- [seq startDomino M s |
      s <- language (n.+1 * #|state|.+1) symbol],
      d <- filter_option B])| ~~ is_wk d].
apply/eq_mem_filter/eq_mem_filter_option/eq_mem_cat;
apply/eq_mem_map'/eq_memS/H.
apply/eq_memT/eq_memS/H.
rewrite filter_option_cat filter_cat.
have{}H:[seq d<-filter_option[seq mu' a d| a <- [seq startDomino M s
              | s <- language (n.+1 * #|state|.+1) symbol],
                      d <- filter_option B]|~~is_wk d]=nil.
have{H}:all(fun p=>#|state|.+1<=size p)(language (n.+1 * #|state|.+1) symbol).
move:(languagelength(n.+1 * #|state|.+1)symbol).
elim:(language (n.+1 * #|state|.+1) symbol).
done.
move=>a0 l0{}H.
simpl.
case H1:(size a0 == n.+1 * #|state|.+1);[move/H=>{}H|done].
rewrite{}H Bool.andb_true_r.
move:H1.
move/eqP.
rewrite mulSn=>H.
rewrite H addSn.
apply/leq_addr.

elim:(language (n.+1 * #|state|.+1) symbol).
done.
move=>a0 l0{A HeqA}H.
rewrite/=.
case H1:(#|state| < size a0);[move/H=>{}H|done].
rewrite filter_option_cat filter_cat{}H cats0{B}HeqB.
elim:(language' #|state|.+1 symbol).
done.
move=>a1 l1 H.
rewrite/=filter_option_cat map_cat filter_option_cat filter_cat{}H cats0.
elim:(language' #|state| symbol).
done.
move=>a2 l2 H.
simpl.
case_eq(stopDomino M a1 a2);[move=>p H2|done].
move:a0 H H1.
case.
done.
move=>a' a0 H.
simpl=>H1.
rewrite (mu'lemma2 _ _ _ a2 a1 _ H1);[|done].
case:(drop(size a0- index (dstar (delta M) (init M) (a' :: a0)) (enum state))
                (a' :: a0) == a1);apply/H.
rewrite{B HeqB}H cats0{A}HeqA.
have H:l =i [seq startDomino M(s++t)|s<-language(n.+1*#|state|.+1)symbol,
                                      t<-language(#|state|.+1)symbol].
rewrite Heql mulSn addnC.

have:forall m n:nat,[seq startDomino M s|s<-language(m+n)symbol]=i
  [seq startDomino M(s++t)|s<-language m symbol,t<-language n symbol].
move=>m n0.
suff H:language(m+n0)symbol=i
[seq s++t|s<-language m symbol,t<-language n0 symbol].
have{}H:[seq startDomino M s | s <- language (m + n0) symbol]=i[seq 
  startDomino M s|s<-[seq s++t|s<-language m symbol,t<-language n0 symbol]].
apply/eq_mem_map/H.
apply/eq_memT.
apply/H.
elim:(language m symbol).
done.
move=>a l0{}H.
rewrite/=map_cat.
apply/eq_mem_cat/H.
elim:(language n0 symbol).
done.
move=>a0 l1{}H.
rewrite/=.
apply/eq_mem_cons/H.
rewrite/eq_mem=>s.
apply/bool_eqsplit.
have languagelength2:forall(n:nat)(s:seq symbol),
size s=n->s\in language n symbol.
move=>n1 s0 H.
rewrite-{n1}H.
elim:s0.
done.
move=>a l0 H.
simpl.
apply/map_f'/mem_enum/H.
move:(cat_take_drop m s)=>H.
split=>H1.
have{}H1:size s = m+n0.
move:H1(languagelength(m+n0)symbol).
elim:(language(m+n0)symbol).
done.
move=>a l0 H1.
rewrite/=in_cons.
move/orP=>[/eqP H2|].
subst.
by move/andP=>[/eqP].
move/H1=>{}H1/andP[_].
apply/H1.
rewrite-H.
have H2:size(take m s)=m.
rewrite size_take{}H1.
case:n0.
by rewrite addn0;case(m<m).
move=>n0.
by rewrite addnS leq_addr.
have{}H1:size(drop m s)=n0.
move:H1.
rewrite-{1}H size_cat H2.
remember(size(drop m s))as d.
elim m.
done.
move=>n1 H1.
rewrite!addSn.
by move=>[].
apply/map_f'/languagelength2/H1/languagelength2/H2.
apply/languagelength2.
move:H1(languagelength m symbol)(languagelength n0 symbol).
elim:(language m symbol).
done.
move=>a l0 H1.
rewrite/=mem_cat.
move/orP=>[H2|/H1{}H1]/andP[]/eqP H3.
subst.
move:H2.
elim:(language n0 symbol).
done.
move=>a0 l H2.
rewrite/=in_cons.
move/orP=>[/eqP H3 _ /andP[]/eqP H4 _|/H2{}H2].
by rewrite H3 size_cat-H4.
by move/H2=>{}H2/andP[]/eqP _/H2{}H2.
done.
apply=>_.


apply/eq_memT.
apply/H.
suff H1:filter_option
                 [seq mu' a d
                    | a <- [seq startDomino M s
                              | s <- language (n.+1 * #|state|.+1) symbol],
                      d <- [seq extentionDomino M s t
                              | s <- language #|state|.+1 symbol,
                                t <- language' #|state| symbol]]=i
  [seq startDomino M (s ++ t)
   | s <- language (n.+1 * #|state|.+1) symbol,
     t <- language #|state|.+1 symbol].
have{}H1:[seq d <- filter_option
                 [seq mu' a d
                    | a <- [seq startDomino M s
                              | s <- language (n.+1 * #|state|.+1) symbol],
                      d <- [seq extentionDomino M s t
                              | s <- language #|state|.+1 symbol,
                                t <- language' #|state| symbol]]
        | ~~ is_wk d]=i[seq d <- [seq startDomino M (s ++ t)
   | s <- language (n.+1 * #|state|.+1) symbol,
     t <- language #|state|.+1 symbol]
        | ~~ is_wk d].
apply/eq_mem_filter/H1.
apply/eq_memT/eq_memS/H1.
move=>{l Heql H H1}x.
repeat f_equal.
remember(language #|state|.+1 symbol)as l.
elim:(language (n.+1 * #|state|.+1) symbol).
done.
move=>a0 l0{}H.
rewrite/=filter_cat.
f_equal;[move{Heql H}|done].
elim:l.
done.
move=>a l H.
rewrite/=(_:~~ is_wk (startDomino M (a0 ++ a)));[by f_equal|]=>{H l0 l x n}.
rewrite/startDomino.
by case:(take
      (size (a0 ++ a) -
       (index (dstar (delta M) (init M) (a0 ++ a)) (enum state) + 1))
      (a0 ++ a));case:(drop
      (size (a0 ++ a) -
       (index (dstar (delta M) (init M) (a0 ++ a)) (enum state) + 1))
      (a0 ++ a)).
move:{l Heql H}(languagelength(n.+1 * #|state|.+1)symbol).
elim:(language (n.+1 * #|state|.+1) symbol).
done.
move=>s l H.
remember(language #|state|.+1 symbol)as t.
rewrite/=filter_option_cat.
move/andP=>[]/eqP H1/H{}H.
have{}H1:#|state|<size s;[by rewrite H1 mulSn addSn leq_addr|].
apply/eq_mem_cat;[|done].
rewrite{H t}Heqt.
move:(languagelength#|state|.+1symbol).
elim:(language#|state|.+1symbol).
done.
move=>t l0 H.
rewrite/=map_cat filter_option_cat.
move/andP=>[]/eqP H2/H{}H.
have H3:startDomino M (s ++ t) :: [seq startDomino M (s ++ t0) | t0 <- l0]=
[::startDomino M (s ++ t)] ++ [seq startDomino M (s ++ t0) | t0 <- l0].
done.
rewrite{}H3.
apply/eq_mem_cat;[|apply/H].
have:drop(size s-(index(dstar(delta M)(init M)s)(enum state)).+1)s\in 
language' #|state| symbol.
have{}H:0<size(drop(size s-(index(dstar(delta M)(init M)s)(enum state)).+1)s).
rewrite size_drop subKn.
done.
apply/ltn_trans/H1/fin_index.
have{}H1:size(drop(size s-(index(dstar(delta M)(init M)s)(enum state)).+1)s)
<=#|state|.
rewrite size_drop subKn;[|apply/ltn_trans/H1];apply/fin_index.
suff H3:drop (size s - (index (dstar (delta M) (init M) s) (enum state)).+1)s
  \in language'
  (size(drop(size s-(index(dstar(delta M)(init M)s)(enum state)).+1)s))symbol.
rewrite-(subnKC H1).
elim:(#|state| -size
     (drop(size s - (index (dstar (delta M) (init M) s) (enum state)).+1)s)).
by rewrite addn0.
move=>{}n{H1 H2 H3}H.
by rewrite addnS/=mem_cat H.
move:H{H1 H2 n t l l0}.
remember(drop(size s-(index(dstar(delta M)(init M)s)(enum state)).+1) s)as l.
move{s Heql}.
destruct l.
done.
move=>_.
suff:s :: l \in language (size (s :: l)) symbol.
case:(size (s :: l)).
done.
move=>n.
rewrite/=mem_cat=>H.
apply/orP.
by right.
elim:(s :: l).
done.
move=>a{s}l H.
rewrite/=.
apply/map_f'/mem_enum/H.

have:all(fun p=>p!=nil)(language' #|state| symbol).
elim:#|state|.
done.
move=>{}n{}H.
rewrite/=all_cat H/=.
elim:(language n symbol).
done.
move=>a{}l{}H.
rewrite/=all_cat H.
by elim:(enum symbol).

elim:(language' #|state| symbol).
done.
move=>u{l0 H}l H.
rewrite/=in_cons.
move/andP=>[]/eqP H3 H4.
rewrite(mu'lemma M _ _ _ H1 H2 H3){H3 n}.
have H3:[:: startDomino M (s ++ t)]=i 
(startDomino M (s ++ t))::[:: startDomino M (s ++ t)].
move=>x.
rewrite!in_cons.
by case:(x == startDomino M (s ++ t)).
move/orP=>[H5|/H{}H].
rewrite{}H5.
case_eq(drop(size s-(index(dstar(delta M)(init M) s)(enum state)).+1) s\in l).
move/(H H4)=>{}H.
apply/eq_memT/eq_memS/H3/eq_mem_cons/H.
move:{H H3}H4.
elim:l.
done.
move=>a l H.
rewrite/=in_cons=>/andP[]/eqP H3/H{}H.
rewrite(mu'lemma M _ _ _ H1 H2 H3).
by case:(drop(size s-(index(dstar(delta M)(init M)s)(enum state)).+1)s == a).
case:(drop(size s-(index (dstar (delta M) (init M) s) (enum state)).+1) s ==u).
apply/eq_memT/eq_memS/H3/eq_mem_cons/H/H4.
apply/H/H4.
Qed.


(*Lemma stopaccept{state symbol:finType}(M:@automaton state symbol)
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
Search filter_map.*)*)




Theorem REG_RSL{state symbol:finType}(M:@automaton state symbol)(s:seq symbol)
(m:nat):s <> nil -> exists n:nat , n <= m ->
accept M s = (s\in(ss_language_prime m (Aut_to_Stk M))).
Proof.
case_eq s.
done.
move=>a s0 s' _.
apply ex_intro with (size s0/(#|state|.+1)).
remember ((size s0)/(#|state|.+1)) as n.
rewrite/ss_language_prime.
rewrite lang_gen.
suff H:accept M (a :: s0) =
(WK (mkwkzip a s0) \in ss_generate_prime n (Aut_to_Stk M)).
move/subnKC=>H1.
rewrite-{}H1.
elim:(m-n).
by rewrite addn0.
move=>{}m{}H.
rewrite addnS/=mem_undup mem_cat.
have{}H:accept M (a :: s0)=(WK (mkwkzip a s0)
   \in [seq a0 <- ss_generate_prime (n + m) (Aut_to_Stk M) | is_wk a0]).
by rewrite{}H mem_filter(_:is_wk (WK (mkwkzip a s0))).
rewrite-{}H.
remember[seq extentionDomino M s1 t  | s1 <- [seq s1 :: l
            | l <- language #|state| symbol,s1 <- enum symbol],
                           t <- language' #|state| symbol]as A.
remember[seq stopDomino M s1 t| s1 <- language' #|state| symbol ++[seq s1 :: l
       | l <- language #|state| symbol,s1 <- enum symbol],
                             t <- language' #|state| symbol]as B.
rewrite-HeqA-HeqB.
have H:filter_option [seq mu' a0 d
               | a0 <- [seq a0 <- ss_generate_prime (n + m) (Aut_to_Stk M)
                          | ~~ is_wk a0], d <- A ++ filter_option B]=i
        filter_option [seq mu' a0 d | a0 <- [seq startDomino M s |
 s <- language ((n + m).+1 * #|state|.+1) symbol],d <- A ++ filter_option B].
move:(startDomino_gen_prime2 M(n+m))=>H.
apply/eq_mem_filter_option/eq_mem_map'/eq_memS/H.

done.
 
case H:(WK (mkwkzip a s0)
      \in filter_option
            [seq mu' a0 d
               | a0 <- [seq a0 <- ss_generate_prime (n + m) (Aut_to_Stk M)
                          | ~~ is_wk a0],
                 d <- [seq extentionDomino M s1 t
                         | s1 <- [seq s1 :: l
                                    | l <- language #|state| symbol,
                                      s1 <- enum symbol],
                           t <- language' #|state| symbol] ++
                      filter_option
                        [seq stopDomino M s1 t
                           | s1 <- language' #|state| symbol ++
                                   [seq s1 :: l
                                      | l <- language #|state| symbol,
                                        s1 <- enum symbol],
          t <- language' #|state| symbol]]);[|by case:(accept M (a :: s0))].

by rewrite H Bool.orb_false_r.
apply/eqP.
Search (_+(_-_)).
mu'lemma2
startDomino_gen_prime2
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

















