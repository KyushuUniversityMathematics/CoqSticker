From mathcomp Require Import all_ssreflect.

Require Import Ascii String Bool ListSet Arith.
Require Import AutomatonModule StickerModule2 myTheorems.

Fixpoint language (n:nat)(V:list Symbol):list SymbolString :=
(*n文字の文字列を生成
Ex:language 2 [::"a"%char;"b"%char] -> [::"aa";"ab";"ba;";"bb"]*)
match n with
|0 => [::""]
|S n' => flatten [seq (map (String v) (language n' V))| v <- V]
end.
Fixpoint language' (n:nat)(V:list Symbol):list SymbolString :=
(*1文字以上n文字以下の文字列を生成
Ex:language 2 [::"a"%char;"b"%char] -> [::"a";"b";"aa";"ab";"ba;";"bb"]*)
match n with
|0 => [::]
|S n' => app (language' n' V) (language n V)
end.

Fixpoint l_index {e:eqType}(a:e)(l:list e):nat :=
match l with
|nil => 0 - 1
|h::l' =>
  if a == h then
    0
  else
    S (l_index a l')
end.
Definition startDomino (n:nat)(s:string):Domino :=
(s,substring 0 (length s - n) s,0,0).
Definition startDomino_inverse (d:Domino):nat*string:=
let '(s,t,_,_) := d in
(length s - length t,s).
Lemma startDominoCollect (n:nat)(s:string):
n<=length s->startDomino_inverse (startDomino n s) = (n,s).
Proof. move=>H;apply/pair_equal_spec;split;[|done];rewrite substringlemma2;
[by rewrite subKn|rewrite add0n;apply/leq_subr]. Qed.
Definition extentionDomino (n:nat)(s t:string):Domino*Domino :=
(("","",0,0),(s,t++(substring 0 (length s - n) s),0,length t)).
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
by f_equal. Qed.
Definition stopDomino (s t:string):Domino*Domino :=
(("","",0,0),(s,t++s,0,length t)).
Definition stopDomino_inverce (D:Domino*Domino):string*string :=
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
by f_equal. Qed.
Definition dstar_num (n:nat)(s:string)(M:Automaton):nat :=
let ' (K,V,delta,s0,F) := M in
let k := nth 999 K (n - 1) in
l_index (dstar delta k s) K + 1.

Fixpoint createDomino (l:list string)(state:State)(M:Automaton):list Domino :=
let ' (K,V,delta,s0,F) := M in
match l with
|nil => nil
|s::l' =>
  let state_num := l_index (dstar delta state s) K in
  (s,substring 0 ((length s)- state_num - 1) s,0,0)::(createDomino l' state M)
end.
Fixpoint convert_D (l1 l2:list string)(M:Automaton):list (Domino*Domino) :=
let ' (K,V,delta,s0,F) := M in
match l2 with
|nil => nil
|s::l2' =>
  let state := List.nth (length s - 1) K s0 in
  app (map 
    (fun d =>let ' (l,r,x,y) := d in (("","",0,0),(l,s++r,x,y+(length s))))
    (createDomino l1 state M))
  (convert_D l1 l2' M)
end.
Fixpoint convert_D' (l1 l2:list string)(M:Automaton):list (Domino*Domino) :=
let ' (K,V,delta,s0,F) := M in
match l2 with
|nil => nil
|s::l2' =>
  let state := List.nth (length s - 1) K s0 in
  let X := accepts (K,V,delta,state,F) l1 in
  app [seq (("","",0,0),(x,s++x,0,length s))|x <- X] (convert_D' l1 l2' M)
end.

Definition Aut_to_Stk (M:Automaton):Sticker :=
let ' (K,V,delta,s0,F) := M in
if (s0\in K)&&(nil==[seq f<-F|(fun x=>x\notin K) f]) then
let k := List.length K in
let l := language (k+1) V in
let A1 := [seq (l',l',0,0)|l' <- accepts M (language' (k+1) V)] in
let A2 := [seq startDomino (l_index (dstar delta s0 s) K + 1) s|s <- l] in
let A := app A1 A2 in
let l' := language' k V in
let D1 := [seq extentionDomino (dstar_num (length t) s M) s t|s<-l,t<-l'] in
let D2 := [seq stopDomino s t|
  t <- l',s <- (accepts (K,V,delta,nth 999 K (length t - 1),F)
    (language' (k+1) V))] in
let D := app D1 D2 in
let rho := [seq (v,v)|v <- V] in
(V,rho,A,D)
else (nil,nil,nil,nil).
Definition m1_d : State->Symbol->State :=
fun q x =>
match q with
  | 0 =>
    match x with
      | "a"%char => 0
      | "b"%char => 1
      | _ => 999
    end
  | 1 => 
    match x with
      | "a"%char => 1
      | "b"%char => 0
      | _ => 999
    end
  | _ => 999
end.
Compute dstar m1_d 1 "b".
Definition m1: Automaton:=
([::0;1],[::"a"%char;"b"%char],m1_d, 0,[::1]).
Definition s1 := Aut_to_Stk m1.
Compute accepts m1 (language' 3 [:: "a"%char;"b"%char]).
Compute s1.
Compute ss_language 1 s1.
Definition ss_accept_prime (stk:Sticker) (a:SymbolString):bool:=
let ' (V,_,_,_) := stk in
(Vword a V)&&(a \in (ss_language_prime (length a) stk)).


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

















