From mathcomp Require Import all_ssreflect.

From MyLib Require Import AutomatonModule StickerModule myLemma.
(** %
asdkjabjs
% **)
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
|a::w',b::r' => R(mkend true b r')(mkwkzip a w')
|_,_ => null
end.
Definition extentionDomino{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol):domino*domino:=
let s0 := nth (init M) (enum state) (size t - 1) in
let n := index (dstar (delta M) s0 s) (enum state) + 1 in
let w := take(size s - n)s in
let r := drop(size s - n)s in
match t,w,r with
|a::t',b::w',c::r'=>(null,LR(mkend false a t')(mkend true c r')(mkwkzip b w'))
|_,_,_ => (null:@domino symbol (zip(enum symbol)(enum symbol)),null)
end.
Definition stopDomino{state symbol:finType}(M:@automaton state symbol)
(s t:seq symbol):option(domino*domino):=
let s0 := nth (init M) (enum state) (size s - 1) in
match s,t with
|a::s',b::t'=>
  if (dstar (delta M) s0 t)\in final M then
    Some(null:@domino symbol (zip(enum symbol)(enum symbol)),
      L(mkend false a s')(mkwkzip b t'))
  else
    None
|_,_=>None
end.


Lemma st_correctP{state symbol:finType}(M:@automaton state symbol):
all st_correct(filter_option[seq wkaccept M s|s<-language'(#|state|.+1)symbol]
  ++[seq startDomino M s|s <- language(#|state|.+1)symbol]).
Proof.
rewrite all_cat;apply/andP;split.
move:(language'nil #|state|.+1 symbol).
elim:(language' #|state|.+1 symbol);[done|]=>a l H.
move/andP;case=>H1.
move/H=>{}H.
rewrite{1}/wkaccept/=.
by destruct a;[|case:(accept M (s :: a))].

move:(languagelength #|state|.+1 symbol).
elim:(language #|state|.+1 symbol);[done|]=>a l H.
move/andP;case=>/eqP H1/H{}H.
rewrite/={l}H Bool.andb_true_r.
destruct a as [|a l];[done|].
rewrite/startDomino H1.
remember(dstar (delta M) (init M) (a :: l)) as s.
case H:(take(#|state|.+1 - (index s(enum state) + 1))(a :: l)).
have:size(take(#|state|.+1-(index s(enum state) + 1))(a :: l))=0;[by rewrite H|].
have H2:(0 < index s (enum state) + 1);[by rewrite addn1|].
have H3:(0 < #|state|.+1);[done|].
rewrite size_take H1 ltn_subrL H2 H3/=addn1 subSS =>{H1 H2 H3 Heqs a l}H.
move:(fin_index s).
by rewrite-subn_gt0 H.
rewrite addn1.
case H2:(drop(#|state|.+1 - (index s(enum state)).+1)(a :: l));[|done].
have{H2}:size(drop(#|state|.+1 - (index s(enum state)).+1)(a :: l))=0;[by rewrite H2|].
by rewrite size_drop H1 subSS subSn;[|apply/leq_subr].
Qed.

Definition Aut_to_Stk{state symbol:finType}(M:@automaton state symbol):=
let A1 := filter_option[seq wkaccept M s|s<-language'(#|state|.+1)symbol] in
let A2 := [seq startDomino M s|s <- language(#|state|.+1)symbol] in
let D1 := [seq extentionDomino M s t|s<-language(#|state|.+1)symbol,
                                     t<-language'(#|state|)symbol] in
let D2 := filter_option[seq stopDomino M t s|
  s <- language'(#|state|.+1)symbol,t <- language'(#|state|)symbol] in
{|start:=(A1++A2);extend:=(D1++D2);startP:=st_correctP M|}.


Lemma lang_gen{state symbol:finType}(M:@automaton state symbol)(a:symbol)
(s:seq symbol)(n:nat):(a::s\in (ss_language_prime n (Aut_to_Stk M))) 
 = (WK(mkwkzip a s)\in[seq d<-ss_generate_prime n (Aut_to_Stk M)|is_wk d]).
Proof.
rewrite/ss_language_prime.
elim:(ss_generate_prime n (Aut_to_Stk M));[done|]=>d l H.
simpl;case:(is_wk d);[|by subst].
rewrite/=!in_cons H.
case:(WK (mkwkzip a s) \in [seq d0 <- l | is_wk d0]);[by rewrite!Bool.orb_true_r|].
rewrite!Bool.orb_false_r.
apply/bool_eqsplit;split;[|move=>/eqP{}H];(destruct d;[done|done|destruct w|done|done|done]).

have{}H:unzip1 str=unzip2 str.
move:rhoP{nilP}.
elim:str;[done|]=>a0 l0{}H/andP.
case=>H1/H{}H.
rewrite/=H;f_equal.
move:H1.
elim:(enum symbol);[done|]=>a1 l1{}H.
rewrite/=in_cons=>/orP.
by case=>[/eqP{}H|];[subst|].

simpl=>/eqP H1.
apply/eqP.
f_equal.
apply/eqP.
rewrite/eq_op/=/wk_eqb/=(_:(a, a) :: zip s s=zip(a::s)(a::s));[|done].
by rewrite!H1{2}H zip_unzip.
by rewrite-H/=unzip1_zip.
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
(s t u:seq symbol)(d:domino*domino): #|state|<size s ->
Some d = (stopDomino M u t)->
mu'(startDomino M s)d = 
if (drop (size s-(index(dstar(delta M)(init M)s)(enum state)).+1)s)
  ==u then
  mkWK (s++t)
else
  None.
Proof.
move=>lens.
rewrite/stopDomino.
case_eq u;[done|move=>a0 l0 u'].
case_eq t;[done|move=>a1 l1 t'].

case:(dstar (delta M)(nth (init M)(enum state)(size(a0::l0) - 1)) (a1 :: l1)
    \in final M);[move=>[d'];rewrite d'{d'}/=/mu/startDomino|done].
case_eq(take(size s-(index (dstar (delta M) (init M) s) (enum state) + 1)) s)
;[move=>H|move=>a2 l2 t1].
have:size(take(size s-(index(dstar(delta M)(init M)s)(enum state) + 1)) s)=0.
by rewrite H.
have{}H:(0 < index (dstar (delta M) (init M)s) (enum state) + 1).
by rewrite addn1.
have H1:(0 < size s);[apply/leq_ltn_trans/lens/leq0n|].
rewrite size_take ltn_subrL H H1/={H H1}.
move/lesub/(leq_trans lens).
rewrite leqNgt.
suff H:((index (dstar (delta M) (init M) s) (enum state) ).+1 < #|state|.+1).
by rewrite addn1 H.
apply/fin_index.
case_eq(drop (size s - (index (dstar (delta M) (init M)s)(enum state)+1))s);
[move=>H|move=>a3 l3 d1].
have:size(drop(size s-(index(dstar(delta M)(init M)s)(enum state) + 1)) s)=0;
[by rewrite H|].
rewrite size_drop subKn addn1/=.
done.
apply/leq_ltn_trans/lens/ltnW/fin_index.
case_eq s=>[|a s']s_.
move:lens.
by rewrite s_.
rewrite/mkWK(_:(a :: s') ++ a1 :: l1=a::(s'++a1::l1));[|done].
rewrite-s_.

case_eq(drop(size s-(index(dstar(delta M)(init M)s)(enum state)).+1)s==a0::l0).
rewrite-addn1 d1.
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
suff H:((a2 :: l2) ++ a0 :: l0) ++ a1 :: l1=(a :: s') ++ a1 :: l1.
by f_equal.
f_equal.
by rewrite-t1-ueq-d1/=cat_take_drop.


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
move:ueq.
rewrite-addn1 d1=>ueq.
have{}sizeu:size (a3::l3)=size (a0::l0).
move:sizeu.
by move/eqP.

by apply/fin_zip_neq.

destruct B;[|done].
move:H1.
by rewrite e.
Qed.






Lemma start_extend{state symbol:finType}(M:@automaton state symbol)
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
apply/eq_memT/eq_memS/mem_undup.
have{}H1:extend ASM = [seq extentionDomino M s t
  | s <- language #|state|.+1 symbol,t <- language' #|state| symbol] ++
     filter_option[seq stopDomino M s t
        | t <- language' #|state|.+1 symbol,s <- language' #|state| symbol].
by rewrite HeqASM.
move:H.
rewrite{}H1{ASM}HeqASM=>H.
remember[seq extentionDomino M s t | s <- language #|state|.+1 symbol,
                                t <- language' #|state| symbol]as A.
remember[seq stopDomino M s t | t <- language' #|state|.+1 symbol,
                                  s <- language' #|state| symbol]as B.
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
case_eq(stopDomino M a2 a1);[move=>p H2|done].
rewrite/=.
have{}H2:Some p = stopDomino M a2 a1;[done|].
rewrite (mu'lemma2 _ _ _ _ _ H1 H2)/mkWK.
case:(drop(size a0-(index(dstar(delta M)(init M) a0) (enum state)).+1) a0 ==
              a2).
case:(a0 ++ a1)=>[|a l3];apply/H.
apply/H.

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


Lemma start_stop{state symbol:finType}(M:@automaton state symbol)(n:nat):
[seq d<-ss_generate_prime n.+1 (Aut_to_Stk M)|is_wk d]=i
[seq d<-ss_generate_prime n (Aut_to_Stk M)|is_wk d] ++
filter_option[seq wkaccept M s|s<- 
[seq s++t|s <-language(n.+1*#|state|.+1)symbol,t<-language'#|state|.+1symbol]].
Proof.
remember(#|state|.+1)as k.
simpl.
remember[seq extentionDomino M s t
    | s <- language #|state|.+1 symbol,t <- language' #|state| symbol]as A.
rewrite(_:[seq extentionDomino M s t
         | s <- [seq s :: l| l <- language #|state| symbol,s <- enum symbol],
                              t <- language' #|state| symbol]=A);[|done].
remember[seq stopDomino M t s | s <- language' #|state|.+1 symbol,
                                t <- language' #|state| symbol] as B.
rewrite(_:[seq stopDomino M t s | s <- language' #|state| symbol ++
           [seq s :: l| l <- language #|state| symbol, s <- enum symbol],
                                t <- language' #|state| symbol]=B);[|done].
apply/eq_memT.
apply/eq_mem_filter/mem_undup.
rewrite filter_cat filter_id.
apply/eq_mem_cat;[done|].
apply/eq_memT.
apply/eq_mem_filter/eq_mem_filter_option/eq_mem_map'/eq_memS/start_extend.
apply/eq_memT.
apply/eq_mem_filter/eq_mem_filter_option/mem_allpairs_catr.
rewrite filter_option_cat filter_cat(_:[seq a <- filter_option
            [seq mu' x y    | x <- [seq startDomino M s
        | s <- language (n.+1 * #|state|.+1) symbol],y <- A]| is_wk a]=nil).
rewrite cat0s-Heqk.

move:(languagelength(n.+1 * k)symbol).
elim:(language (n.+1 * k) symbol).
done.
move=>a l H/andP[sizea]/H{}H.
rewrite/=map_cat!filter_option_cat filter_cat.
apply/eq_mem_cat/H.
rewrite{A HeqA H B l}HeqB-Heqk.
case_eq a=>[H4|s l a_].
move:sizea.
by rewrite H4 Heqk.
rewrite-a_.
move:(language'nil k symbol).
elim:(language' k symbol).
done.
move=>a0 l0 H/andP[a0nil]/H{}H.
rewrite/=filter_option_cat map_cat filter_option_cat filter_cat.
case_eq(wkaccept M (a ++ a0))=>[d|]H2.
rewrite-cat1s.
apply/eq_mem_cat/H.

have:drop(size a-(index(dstar(delta M)(init M)a)(enum state)).+1)a\in
language' #|state| symbol.
apply/language'lemma.
rewrite/not=>{}H.
have:size(drop(size a-(index(dstar(delta M)(init M)a)(enum state)).+1) a)=0.
by rewrite H.
rewrite size_drop/=subKn.
done.
rewrite(eqP sizea)Heqk mulSn addSn ltnS.
apply/leq_trans/leq_addr/ltnW/fin_index.
rewrite size_drop/=subKn.
apply/fin_index.
rewrite(eqP sizea)Heqk mulSn addSn ltnS.
apply/leq_trans/leq_addr/ltnW/fin_index.
move:(language'nil#|state|symbol).
elim:(language' #|state| symbol).
done.
move=>a1 l1{}H/andP[]a1nil/H{}H/orP[H3|/H{}H];rewrite/=. 
case_eq(stopDomino M a1 a0).
move=>p H1.
have{}sizea:#|state|<size a;[by rewrite(eqP sizea)Heqk leq_addr|].
have{}H1:Some p = stopDomino M a1 a0;[done|].
rewrite/=(mu'lemma2 _ _ _ _ _ sizea H1)H3/mkWK.
have{}H2:WK (mkwkzip s (l ++ a0))=d.
move:H2.
rewrite/wkaccept a_ cat_cons.
by case:(accept M (s :: l ++ a0))=>[[]|].
rewrite a_ cat_cons/=H2-a_.
move:H.
rewrite(eqP H3).
case H4:(a1 \in l1)=>H.
apply/eq_memT.
apply/eq_mem_cons.
by apply/H.
move=>x.
rewrite!in_cons.
by case:(x == d).
apply/eq_mem_cons.
move:H4{H}.
elim:l1.
done.
move=>a2 l2 H.
rewrite in_cons.
case H4:(a1 == a2);[done|move=>/H{}H].
rewrite/=.
case_eq(stopDomino M a2 a0)=>[p0|]H5.
have{}H5:Some p0 = stopDomino M a2 a0;[done|].
by rewrite/=(mu'lemma2 _ _ _ _ _ sizea H5)(eqP H3)H4.
done.

have{}H2:accept M(a++a0).
move:H2.
rewrite/wkaccept a_ cat_cons.
by case(accept M (s :: l ++ a0)).
rewrite{1}/stopDomino.
have{}H3:size a1 = (index (dstar (delta M) (init M) a) (enum state)).+1.
rewrite-(eqP H3)size_drop subKn.
done.
rewrite(eqP sizea)Heqk mulSn addSn ltnS.
apply/leq_trans/leq_addr/ltnW/fin_index.
rewrite H3 subn1/=nth_index;[|apply/mem_enum].
move:H2.
rewrite/accept dstarLemma=>H2.
rewrite H2.
by destruct a1,a0.

case_eq(stopDomino M a1 a0)=>[p|]H1.
have{}sizea:#|state|<size a;[by rewrite(eqP sizea)Heqk leq_addr|].
have{}H1:Some p = stopDomino M a1 a0;[done|].
rewrite/=(mu'lemma2 _ _ _ _ _ sizea H1).
case H3:(drop(size a -
     (index (dstar (delta M) (init M) a) (enum state)).+1) a ==a1);[|apply/H].
rewrite/mkWK a_ cat_cons/=.
have{}H2:WK (mkwkzip s (l ++ a0))=d.
move:H2.
rewrite/wkaccept a_ cat_cons.
by case:(accept M (s :: l ++ a0))=>[[]|].
rewrite H2-a_.
apply/eq_memT.
apply/eq_mem_cons/H.
move=>x.
rewrite!in_cons.
by case(x==d).
apply/H.


rewrite-(cat0s(filter_option 
[seq wkaccept M s0 | s0 <- [seq a ++ t | t <- l0]])).
apply/eq_mem_cat/H.
have:drop(size a-(index(dstar(delta M)(init M)a)(enum state)).+1)a\in
language' #|state| symbol.
apply/language'lemma.
rewrite/not=>{}H.
have:size(drop(size a-(index(dstar(delta M)(init M)a)(enum state)).+1) a)=0.
by rewrite H.
rewrite size_drop/=subKn.
done.
rewrite(eqP sizea)Heqk mulSn addSn ltnS.
apply/leq_trans/leq_addr/ltnW/fin_index.
rewrite size_drop/=subKn.
apply/fin_index.
rewrite(eqP sizea)Heqk mulSn addSn ltnS.
apply/leq_trans/leq_addr/ltnW/fin_index.
move:(language'nil#|state|symbol).
elim:(language' #|state| symbol).
done.
move=>a1 l1{}H/andP[]a1nil/H{}H/orP[H1|/H{}H].
have{}H2:dstar(delta M)(nth(init M)(enum state)(size a1-1))a0\in final M=false.
rewrite-(eqP H1)size_drop subKn.
rewrite subn1/=nth_index.
move:H2.
rewrite/wkaccept a_ cat_cons.
case_eq(accept M (s :: l ++ a0));[done|].
by rewrite/accept-cat_cons-a_ dstarLemma.
apply/mem_enum.
rewrite(eqP sizea)Heqk mulSn addSn ltnS.
apply/leq_trans/leq_addr/ltnW/fin_index.

rewrite/={1}/stopDomino H2.
destruct a1 ,a0;[done|done|done|].
move:H.
rewrite (eqP H1).
case H3:(s0::a1 \in l1).
move=>H.
by apply/H.
move=>_.
move:H3.
elim:l1.
done.
move=>a2 l2 H.
rewrite in_cons.
case H3:(s0::a1 == a2);[done|]=>/H{}H.
simpl.
case_eq(stopDomino M a2 (s1 :: a0))=>[p|]H4.
have{}sizea:#|state|<size a;[by rewrite(eqP sizea)Heqk leq_addr|].
have{}H4:Some p = stopDomino M a2 (s1 :: a0);[done|].
by rewrite/=(mu'lemma2 _ _ _ _ _ sizea H4)(eqP H1)H3.
done.
rewrite/=.

case_eq(stopDomino M a1 a0)=>[p|]H4.
have{}sizea:#|state|<size a;[by rewrite(eqP sizea)Heqk leq_addr|].
have{}H4:Some p = stopDomino M a1 a0;[done|].
rewrite/=(mu'lemma2 _ _ _ _ _ sizea H4).
case H1:(drop(size a-(index(dstar(delta M)(init M)a)(enum state)).+1)a==a1).
move:H4.
rewrite/stopDomino-{2}(eqP H1)size_drop subKn.
rewrite subn1/=nth_index.
move:H2.
rewrite/wkaccept a_ cat_cons/accept-cat_cons-a_ dstarLemma.
case:(dstar (delta M) (dstar (delta M) (init M) a) a0 \in final M).
done.
by destruct a1,a0.
apply/mem_enum.
apply/ltn_trans/sizea/fin_index.
apply/H.
apply/H.




rewrite{A B HeqB}HeqA-Heqk.
move:(languagelength(n.+1*k)symbol).
elim:(language (n.+1 * k) symbol).
done.
move=>a l H/andP[]H1/H{}H.
have{}H1:#|state|<size a.
by rewrite(eqP H1)Heqk mulSn addSn leq_addr.
rewrite/=filter_option_cat filter_cat{}H cats0.
move:(languagelength k symbol).
elim:(language k symbol).
done.
move=>a0 l0 H/andP[]H2/H{}H.
have{}H2:size a0 = #|state|.+1.
by rewrite-Heqk-(eqP H2).
rewrite/=map_cat filter_option_cat filter_cat{n k Heqk}H cats0.
move:(language'nil#|state|symbol).
elim:(language' #|state| symbol).
done.
move=>a1 l1 H/andP[]H3/H{}H.
move:H3=>/eqP H3.
rewrite/={H1 H2 H3}(mu'lemma _ _ _ _ H1 H2 H3).
case H1:(drop(size a -
        (index (dstar (delta M) (init M) a) (enum state)).+1) a == a1).
rewrite/=/startDomino.
by case:(take
        (size (a ++ a0) -
         (index (dstar (delta M) (init M) (a ++ a0)) (enum state) + 1))
        (a ++ a0));case:(drop
        (size (a ++ a0) -
         (index (dstar (delta M) (init M) (a ++ a0)) (enum state) + 1))
        (a ++ a0)).
apply/H.
Qed.

Lemma accept_gen{state symbol:finType}(M:@automaton state symbol)(n:nat):
[seq d<-ss_generate_prime n (Aut_to_Stk M)|is_wk d] =i
filter_option[seq wkaccept M s|s<-language'(n.+1*#|state|.+1)symbol].
Proof.
elim:n=>[|n H].
rewrite mul1n/=filter_cat.
have H:[seq d <- [seq startDomino M s| s <- [seq s :: l
           | l <- language #|state| symbol,s <- enum symbol]]|is_wk d]=nil.
elim:[seq s :: l| l <- language #|state| symbol, s <- enum symbol].
done.
move=>a l H.
rewrite/={1}/startDomino.
by case:(take(size a-(index(dstar (delta M) (init M) a) (enum state) + 1)) a);
case:(drop (size a - (index(dstar (delta M) (init M) a) (enum state) + 1)) a).
rewrite{}H cats0.
elim:(language' #|state| symbol ++[seq s :: l
                    | l <- language #|state| symbol,s <- enum symbol]).
done.
move=>a l H.
rewrite/=.
case_eq(wkaccept M a)=>[d|];[|done].
rewrite/={1}/wkaccept.
destruct a;[done|].
case:(accept M (s :: a));[|done].
move=>[H1].
rewrite-H1/=.
apply/eq_mem_cons/H.


apply/eq_memT.
apply/start_stop.
apply/eq_memT.
apply/eq_mem_cat.
apply/H.
done.
remember#|state|.+1as k=>{Heqk H}.
rewrite-filter_option_cat-map_cat.
apply/eq_mem_filter_option/eq_mem_map.

move=>x.
rewrite{M}mem_cat.
have H:forall(n:nat)(x:seq symbol),x\in language' n symbol=(0<size x<=n).
move=>m x0.
apply/bool_eqsplit.
split.
move:(language'nil m symbol)(language'length m symbol).
elim:(language' m symbol);[done|].
move=>a l H/andP[]H1/H{}H/andP[]H2/H{}H/orP[/eqP H3|/H{}H];[|done].
by subst.
move=>/andP[]H H1.
have{}H:x0<>nil;[by destruct x0|].
apply/language'lemma/H1/H.

rewrite!H.
have H1:(x\in [seq s ++ t| s <- language (n.+1 * k) symbol,
               t <- language' k symbol])=(n.+1*k<size x<=n.+2*k).
apply/bool_eqsplit.
split.
move:(languagelength(n.+1*k)symbol).
elim:(language (n.+1 * k) symbol).
done.
move=>a l{}H1/andP[]/eqP H2/H1{}H1.
rewrite/=mem_cat=>/orP[|/H1{}H1];[|apply/H1].
move:(language'length k symbol).
elim:(language' k symbol).
done.
move=>a0 l0{}H1/andP[]H3/H1{}H1/orP[/eqP H4|/H1{}H1];[|apply/H1].
rewrite{}H4 size_cat{}H2.
move:H3=>/andP[]{}H1 H2.
apply/andP.
split.
by rewrite-{1}(addn0(n.+1*k)) ltn_add2l.
by rewrite(mulSn n.+1)addnC leq_add2r.

move=>/andP[]H1 H2.
have H3:size(take(n.+1*k)x)=n.+1*k.
by rewrite size_take H1.
have{H1 H2}:0<size(drop(n.+1*k)x)<=k.
apply/andP.
split.
move:H1.
rewrite-{1}(cat_take_drop(n.+1*k)x)size_cat.
case:(size (drop(n.+1*k)x)).
by rewrite H3 addn0 ltnn.
done.
move:H2.
by rewrite-{1}(cat_take_drop(n.+1*k)x)size_cat H3(mulSn(n.+1))addnC leq_add2r.
rewrite-H=>{}H.
have{}H3:take (n.+1 * k) x\in language (n.+1 * k) symbol.
by rewrite-{2}H3 languagelemma.
by rewrite-{1}(cat_take_drop(n.+1*k)x)map_f'.

rewrite{H}H1(ltnNge(n.+1 * k)).
case H:(0 < size x).
move{H}.
case H:(size x <= n.+1 * k).
have{}H:size x <= n.+2*k.
rewrite mulSn.
apply/leq_trans/leq_addl/H.
by rewrite H.
by case:(size x <= n.+2 * k).
have{}H:size x = 0;[by destruct x|].
by rewrite H.
Qed.




Theorem REG_RSL{state symbol:finType}(M:@automaton state symbol)(s:seq symbol):
s <> nil -> exists n:nat ,forall m:nat, n <= m ->
accept M s = (s\in(ss_language_prime m (Aut_to_Stk M))).
Proof.
destruct s as[|a s];[done|]=>_.
apply ex_intro with (size s)=>m H.
rewrite lang_gen accept_gen.
have{H}:a::s\in language' (m.+1 * #|state|.+1) symbol.
apply/language'lemma.
done.
rewrite/=mulnS addSn ltnS.
apply/leq_trans/leq_addr/H.

elim:(language' (m.+1 * #|state|.+1) symbol).
done.
move=>a0 l0 H.
rewrite in_cons.
case_eq(a :: s == a0)=>[/eqP H1 _|H1/H{}H].
subst.
move:H.
case H:(a :: s \in l0).
rewrite/=.
case H1:(accept M (a :: s))=>H2.
by rewrite in_cons(_:(WK (mkwkzip a s) == WK (mkwkzip a s))).
by apply/H2.
move=>_.
move:H.
simpl.
case H:(accept M (a :: s)).
by rewrite in_cons(_:(WK (mkwkzip a s) == WK (mkwkzip a s))).
elim:l0.
done.
move=>a0 l0 H1.
rewrite in_cons.
case H2:(a :: s == a0).
done.
move=>/H1{}H1.
rewrite/={1}/wkaccept.
destruct a0.
apply/H1.
case H3:(accept M (s0 :: a0));[|apply/H1].
rewrite in_cons-{}H1 Bool.orb_false_r.

case_eq(WK (mkwkzip a s) == WK (mkwkzip s0 a0));[|done].
remember(mkwkzip a s)as A.
remember(mkwkzip s0 a0)as B.
move/eqP=>[]/eqP.
rewrite/eq_op/=/wk_eqb{H A}HeqA{B}HeqB/mkwkzip/=.
have cons_zip:forall(t:Type)(a:t)(s:seq t),(a,a)::zip s s = zip(a::s)(a::s).
done.
move=>H.
exfalso.
move:H.
rewrite!cons_zip=>/eqP H.
have{}H:a::s = s0::a0.
have:unzip1(zip(a::s)(a::s)) = unzip1(zip(s0::a0)(s0::a0)).
by rewrite H.
by rewrite!unzip1_zip.
by move:H2=>/eqP.
rewrite/={1}/wkaccept.
destruct a0.
done.
case H2:(accept M (s0 :: a0));[|apply/H].
rewrite in_cons-{}H.
case H:(accept M (a :: s)).
by case:(WK (mkwkzip a s) == WK (mkwkzip s0 a0)).
rewrite Bool.orb_false_r.
case_eq(WK (mkwkzip a s) == WK (mkwkzip s0 a0));[|done].
remember(mkwkzip a s)as A.
remember(mkwkzip s0 a0)as B.
move/eqP=>[]/eqP.
rewrite/eq_op/=/wk_eqb{H A}HeqA{B}HeqB/mkwkzip/=.
have cons_zip:forall(t:Type)(a:t)(s:seq t),(a,a)::zip s s = zip(a::s)(a::s).
done.
move=>H.
exfalso.
move:H.
rewrite!cons_zip=>/eqP H.
have{}H:a::s = s0::a0.
have:unzip1(zip(a::s)(a::s)) = unzip1(zip(s0::a0)(s0::a0)).
by rewrite H.
by rewrite!unzip1_zip.
by move:H1=>/eqP.
Qed.
