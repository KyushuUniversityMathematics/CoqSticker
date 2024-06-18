From mathcomp Require Import all_ssreflect.

Require Import Ascii String Bool ListSet Recdef Arith.
Require Import AutomatonModule StickerModule2 ListTheorems.

Fixpoint language (n:nat)(V:list Symbol):list SymbolString :=
(*n文字の文字列を生成 Ex:language 2 [::"a"%char;"b"%char] -> [::"aa";"ab";"ba;";"bb"]*)
match n with
|0 => [::""]
|S n' => flatten [seq (map (String v) (language n' V))| v <- V]
end.
Fixpoint language' (n:nat)(V:list Symbol):list SymbolString :=
(*1文字以上n文字以下の文字列を生成 Ex:language 2 [::"a"%char;"b"%char] -> [::"a";"b";"aa";"ab";"ba;";"bb"]*)
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
  app (map (fun d =>let ' (l,r,x,y) := d in (("","",0,0),(l,s++r,x,y+(length s)))) (createDomino l1 state M))
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
let k := List.length K in
let l := language (k+1) V in
let A1 := [seq (l',l',0,0)|l' <- accepts M (language' (k+1) V)] in
let A2 := createDomino l s0 M in
let A := app A1 A2 in
let l' := language' (k) V in
let D1 := convert_D l l' M in
let D2 := convert_D' (language' (k+1) V) l' M in
let D := app D1 D2 in
let rho := [seq (v,v)|v <- V] in
(V,rho,A,D).
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
Definition ss_accept (stk:Sticker) (a:SymbolString):bool:=
a \in (ss_language (length a) stk).


Definition m_length (M:Automaton):nat :=
let ' (K,V,delta,s0,F) := M in
List.length K.
Compute nstep 5 (fun x=> [::S x]) [::1;2;3].
Compute ss_generate 10 ([::"a"%char],[::("a"%char,"a"%char)],[::("a","a",0,0)],[::(("","",0,0),("a","a",0,0))]).
Compute ss_onestep [::("a"%char,"a"%char)] [::(("","",0,0),("a","a",0,0))] ("a","a",0,0).


Lemma onesteplemma (rho:Rho)(rr:list (Domino*Domino))(d:Domino):d \in ss_onestep rho rr d.
Proof.
elim rr.
simpl.
by rewrite inE.
unfold ss_onestep.
move => a l H.
rewrite in_undup.
rewrite in_app.
by rewrite H;case_eq (d \in mu' rho a d);move => H';rewrite H'.
Qed.

Lemma ss_generatelemma (n m:nat)(V:list Symbol)(rho:Rho)(A:list Domino)
(D:list (Domino * Domino))(d:Domino):
d \in (ss_generate n (V,rho,A,D)) -> d \in (ss_generate (n+m) (V,rho,A,D)).
Proof.
unfold ss_generate;elim m;[by rewrite addn0|].
move => n0 H H';rewrite addnS;simpl;unfold power;rewrite in_undup;move :(H H');
elim (nstep (n + n0) (ss_onestep rho D) A);[by []|].
simpl;move => a l H1;rewrite in_app;case_eq (d==a).
move => H2 H3;rewrite (eqP H2);by rewrite onesteplemma.
move => H2;move:H1;unfold in_mem;simpl;move => H1;rewrite H2;simpl;move => H3;
rewrite (H1 H3);by case (mem_seq (ss_onestep rho D a) d).
Qed.

Lemma ss_accept_A (V:list Symbol)(rho:list (Symbol*Symbol))(A:list Domino)
(D:list (Domino*Domino))(s:string):((s,s,0,0)\in A)->ss_accept (V,rho,A,D) s.
Proof.
unfold ss_accept;unfold ss_language;move => H.
assert ((s,s,0,0) \in (ss_generate 0 (V, rho, A, D)));[by[]|].
assert ((s,s,0,0) \in (ss_generate (length s) (V, rho, A, D)) -> (s
  \in List.map ss_language_f
        (List.filter wk (ss_generate (length s) (V, rho, A, D))))).
elim (ss_generate (length s) (V, rho, A, D));[by[]|].
simpl;move => a l H1.
case_eq ((s,s,0,0)==a).
move => H2;rewrite <-(eqP H2);simpl.
by assert (length s==length s);[elim s|
rewrite H3;unfold in_mem;simpl;assert (s==s);[elim s|rewrite H4]].
move => H2;move:H1;unfold in_mem;simpl;rewrite H2;simpl;case (wk a);simpl;
by case (s == ss_language_f a).
apply H1;rewrite <-(add0n (length s));by apply (ss_generatelemma).
Qed.

Lemma languagelemma (s:string)(V:list ascii):
Vword s V -> s \in language (length s) V.
Proof.
elim s;[by []|].
move => a s0;unfold Vword.
case H:(a \in V);[simpl|by []].
move => H1 H2.
have{H1 H2}:(s0 \in language (length s0) V);[by rewrite (H1 H2)|].
elim (language (length s0) V);[by []|].
move => a0 l;rewrite in_cons;
have H1:(String a s0 \in [seq String v y | v <- V, y <- a0 :: l]=
  (String a s0 \in 
    (app [seq String v a0 | v <- V] [seq String v y | v <- V, y <- l]))).
elim V;[by []|].
simpl;move => a1 l0 H3;rewrite !in_cons.
case (String a s0 == String a1 a0);[by []|].
rewrite !in_app;rewrite H3;rewrite in_app.
case_eq (String a s0 \in [seq String a1 y | y <- l]);move=>H4;rewrite H4;
case_eq (String a s0 \in [seq String v a0 | v <- l0]);move=>H5;rewrite H5;
case_eq (String a s0 \in [seq String v y | v <- l0, y <- l]);move=>H6;
by rewrite H6.
rewrite H1;rewrite in_app;move => H2.
case H3:(s0==a0);move => H4.
rewrite (eqP H3).
assert (String a a0 \in [seq String v a0 | v <- V]).
move:H.
elim V;[by []|].
move => a1 l0 H6.
rewrite in_cons.
rewrite in_cons.
case_eq (a==a1);move=>H7.
by assert (String a a0 == String a1 a0);[rewrite (eqP H7)|rewrite H].
by case (String a a0 == String a1 a0).
by rewrite H0.
move:H4;simpl=>H4.
rewrite (H2 H4).
by rewrite orb_true_r.
Qed.
Lemma language'lemma (s:string)(V:Symbols)(n:nat):
0 < length s ->Vword s V-> s \in language' (length s + n) V.
Proof.
unfold andb.
move => H H1.
elim n.
rewrite addn0.
move:H.
unfold language'.
case_eq (length s).
by [].
move => n0 H.
rewrite <- H.
rewrite in_app.
by case_eq (s
   \in (fix language' (n1 : nat) (V0 : seq Symbol) {struct n1} :
            seq SymbolString :=
          match n1 with
          | 0 => [::]
          | n'.+1 => (language' n' V0 ++ language n1 V0)%list
          end) n0 V);move=>H2;rewrite H2;simpl;[|move=>H3;apply languagelemma].
move=> n0 H2.
rewrite addnS.
simpl.
rewrite in_app.
by rewrite H2.
Qed.

Lemma p1 (K:States)(V:Symbols)(delta:State->Symbol->State)(s0:State)(F:States)
(s:string):accept (K,V,delta,s0,F) s -> 0<length s ->
(length s <= List.length K + 1) -> (ss_accept (Aut_to_Stk (K,V,delta,s0,F)) s).
Proof.
move => H H1 H2.
have H3:(Vword s V);[by move:H;simpl;case (Vword s V)|].
apply/ss_accept_A;rewrite in_app.
have {}H2:(Datatypes.length K + 1 = length s + (Datatypes.length K +1 - length s));
[by rewrite subnKC|].
have {H2}H1:(s\in(language' (Datatypes.length K + 1) V));
[by rewrite H2;rewrite language'lemma|].
have {H1 H3}H:(s\in accepts (K, V, delta, s0, F)
                    (language' (Datatypes.length K + 1) V)).
move:H1.
elim (language' (Datatypes.length K + 1) V);[by[]|].
move=>a l H4;rewrite in_cons;
case H5:(s==a).
by rewrite<-(eqP H5);move:H;simpl;
case:(Vword s V && (dstar delta s0 s \in F));
[rewrite in_cons;have H6:(s==s);[by []|];rewrite H6|].
by rewrite orb_false_l;simpl;
case:(Vword a V && (dstar delta s0 a \in F));
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
Qed.

Definition dividestring (n:nat)(s:string):list string :=
match n,s with
|0,_ => [::s]
|_,"" => nil
|_,_ =>
let m :=
  if (length s) mod n == 0 then
    (length s)/n
  else
    (length s)/n + 1 in
[seq substring (i*n) n s|i <- List.seq 0 m]
end.
Compute dividestring 3 "abcdefg".
Compute concat "" (dividestring 3 "abcdefg").
Lemma substringlemma1 (n:nat)(s:string):
substring 0 n s ++ substring n (length s - n) s = s.
Proof. have substring00:(forall (s:string),substring 0 0 s="");[by elim|];
have substring0s:(forall (s:string),substring 0 (length s) s=s);
[by elim;[|move=>a s2 H3;simpl;rewrite H3]|];move:s;
elim n;[by move=>s;rewrite substring00;rewrite subn0;rewrite substring0s|];
by move=>n0 H;case;[|simpl;move=>a s;rewrite subSS;f_equal]. Qed.
Lemma substringlemma2 (m n:nat)(s:string):m+n<=length s ->
length (substring m n s) = n.
Proof. have substring00:(forall (s:string),substring 0 0 s="");[by elim|];
have substring0s:(forall (s:string),substring 0 (length s) s=s);
[by elim;[|move=>a s2 H3;simpl;rewrite H3]|];
have {substring00 substring0s}substringlength:(forall (n:nat)(s:string),
n <= length s -> length (substring 0 n s) = n);
[elim;[by move=>s2;rewrite substring00|];by move=>n0 H3;case;[|simpl;move=>a s2;
move/ltnSE=>H4;move:(H3 s2 H4)=>H5;by f_equal]|];
by move:s;elim:m;[rewrite add0n;apply/substringlength|move=>n0 H;case;
[|simpl;move=>a s;rewrite addSn;move/ltnSE;apply H]]. Qed.
Lemma substringlemma3 (m n:nat)(s:string):
substring m n (substring 0 (m+n) s) = substring m n s.
Proof.
case H:(length s <= m+n).
have H1:(substring 0 (m+n) s = s).
rewrite-{2}(substringlemma1 (m+n) s).
have H1:(forall (m n:nat)(s:string),length s <= m ->substring m n s = "").
move=>m0 n0;elim m0;[by case;case n0|].
move=>n1 H1;case;[by[]|];simpl;move=>H2{H2}s0;move/ltnSE;apply H1.
rewrite (H1 (m+n) (length s - (m+n)) s H).
by elim (substring 0 (m + n) s);[|move=>a s0 H2;simpl;f_equal].
by rewrite H1.

move:H;rewrite leqNgt;move/negbFE;move:m n;elim:s;[by[]|];
move=>a s H m n;case m':m;[case n;[by[]|];simpl;move=>n0;rewrite addnS;
move/ltnSE=>H1;f_equal;rewrite-{2}(add0n n0);by rewrite H|];
rewrite addSn;simpl;move/ltnSE=>H1;by rewrite H. Qed.

Lemma dividestringlemma (n:nat)(s:string):
concat "" (dividestring n s) = s.
Proof.
have appends0:(forall s:string,s++""=s);[by elim;[|move=>a s0 H;simpl;f_equal]|].
have maplemma:(forall (f:nat->string)(m n:nat),
[seq f i|i <- List.seq m n.+1]=(f m)::[seq f (1+i)|i <- List.seq m n]);
[by move=>f m n0;simpl;f_equal;move:m;elim n0;[|move=>n1 H8 m;simpl;f_equal]|].
case n':n;[by[]|].

suff:(forall (a b:nat)(s:string),b < n -> length s = a*n+b ->
  concat "" (dividestring n s) = s).
have H:(forall (m:nat),m = ((m/n*n)+m mod n));
[move=>m;rewrite{1}(Nat.Div0.div_mod m n);rewrite plusE;
rewrite multE;by rewrite mulnC|].
move:(H (length s))=>{}H.
move:(leq0n (length s));move/leP=>H1.
move:(Nat.lt_0_succ n.-1);rewrite n';rewrite-n';move=>H2.
move:(Nat.mod_bound_pos (length s) n H1 H2)=>{H2}H1.
destruct H1.
move:H1;move/ltP=>{H0}H1 H2.
by move:(H2 (length s/n) (length s mod n) s H1 H).

move=>{s}a b s H;move:s;elim:a.

move=>s; rewrite mul0n;rewrite add0n;move=>H1;move:H;rewrite-H1=>{H1}H;
rewrite n';case s':s;[by[]|];rewrite/dividestring;move:H;move/ltP=>H;
rewrite-n';rewrite-s';rewrite (Nat.mod_small (length s) n H);
have H1:(length s == 0 = false);[by rewrite s'|];rewrite H1=>{H1};
rewrite (Nat.div_small (length s) n H);simpl;rewrite mul0n;move:H;move/ltP=>H;
by suff H1:(forall (n:nat)(s:string),length s<n->substring 0 n s=s);
[by rewrite H1|];elim;[|move=>n0 H3;case;[|simpl;move=>a1 s0;move/ltnSE=>H4;
f_equal;by apply H3]].

move=>a;move:b H=> b H H1 s;rewrite mulSn;move:(substringlemma1 n s)=>H2 H3.
have H4:(n <= length s);[rewrite H3;rewrite-addnA;apply leq_addr|].
move:(H3).
rewrite-{1}H2.
have H5:(forall (s1 s2:string),length (s1++s2)=length s1 + length s2);
[by move=>s1 s2;elim s1;[|move=>a0 s0 H5;simpl;rewrite addSn;f_equal]|].
rewrite H5.
rewrite substringlemma2;[|by[]];move=>H6.
have H7:(forall (m n p:nat),p+n= p+m->n=m);[by move=>m n0;elim;
[|move=> p H7;rewrite!addSn;move/Nat.succ_inj]|].
move:H6;rewrite-addnA;move/H7=>{H7}H6.

suff H7:(dividestring n s = 
  (substring 0 n s)::(dividestring n (substring n (length s - n) s))).
rewrite H7=>{H7}.
suff H7:(forall (s:string)(l:list string),concat "" (s::l) = s++(concat "" l)).
rewrite H7=>{H7}.
by rewrite (H1 (substring n (length s - n) s) H6).
by move=>s0 l;elim l;[elim s0;[|move=>a0 s2 H7;simpl;f_equal]|].
rewrite/dividestring.
rewrite n';rewrite-n'.

case s':s;[by move:H4;rewrite s';rewrite n'|].
rewrite-s'.
rewrite {1 2 3}H3.
rewrite H6.
rewrite-mulSn.
have H7:(forall (a:nat),(a*n+b) mod n = b);[move=>a0;rewrite addnC;
rewrite-plusE;rewrite Nat.Div0.mod_add;move:H;move/ltP=>H;
by rewrite Nat.mod_small|].
rewrite !H7=>{H7}.
have H7:(forall (a:nat),(a*n+b)/n = a);
[move=>a0;rewrite Nat.div_add_l;[|by rewrite n'];move:H;move/ltP=>H;
by rewrite Nat.div_small;[rewrite plusE;rewrite addn0|]|].
rewrite !H7=>{H7}.

case s'':(substring n (length s - n) s).
move:H6.
rewrite s''.
simpl.
move=>H7.
have H8:(b==0 = true);[by move:H7;case (a*n);
[rewrite add0n;move=>H7;rewrite-H7|]|];rewrite H8=>{H8}.
have {}H7:(a=0);[by move:H7;case a;[|rewrite n']|];rewrite H7=>{H7}.
by simpl;rewrite mul0n.

rewrite-s''=>{s''}.
suff H7:(forall a:nat,[seq substring (i * n) n s
   | i <- List.seq 0 a.+1] =
substring 0 n s
:: [seq substring (i * n) n (substring n (length s - n) s)
      | i <- List.seq 0 a]).
by case (b==0);[rewrite (H7 a)|rewrite (H7 (a+1))].
move=>a0.
rewrite maplemma.
rewrite mul0n.

f_equal.
elim:a0.
by [].
move=>a0 H7.
have H8:(forall n m:nat,List.seq m n.+1 = app (List.seq m n) [::m+n]).
elim.
move=>m.
rewrite addn0.
by[].
simpl.
move=>n0 H8 m.
f_equal.

rewrite (H8 m.+1).
rewrite addSn.
by rewrite addnS.
rewrite H8.
rewrite!map_cat.
f_equal.
by [].
simpl.
f_equal.
rewrite add0n.


have {H7 H8}H6:(forall (s1 s2:string)(m n:nat),length s1 = n ->
  substring n m (s1++s2)=substring 0 m s2).
by move=>s1 s2 m n0;move:s1;elim:n0;[by case|move=>n0 H9;case;
[|simpl;move=>H10{H10}s1;move/eq_add_S;apply H9]].
have {}H6:(forall (s1 s2:string)(m n:nat),
  substring (length s1 + n) m (s1++s2)=substring n m s2).
move=>s1 s2 m n0.
move:s1 s2.
elim n0.
move=>s1 s2.
rewrite addn0.
by apply H6.
move=>n1 H7.
move=>s1.
case.
rewrite appends0.
simpl.
move:(substringlemma1 (length s1 + n1.+1) s1).
have H8:(forall (n:nat)(s:string),substring 0 (length s + n) s = s);
[move=>n2 s0;elim s0;[simpl;by case (0+n2)|move=> a1 s2 H8;simpl;by f_equal]|].
have H9:(forall (m n:nat)(s:string),substring (length s + m) n s = "");
[by move=>m0 n2 s0;elim s0;[rewrite add0n;case n2;case m0|]|].
by rewrite (H9 n1.+1 m s1).
move=>a1 s0.
have H8:(forall (s1 s2:string)(a:ascii),
s1++(String a s2)=(s1++(String a ""))++s2);
[by move=>s2 s3 a2;elim:s2;[|move=>a3 s2 H8;simpl;rewrite H8]|].
rewrite H8=>{H8}.
have H8:(forall (s1:string)(n:nat)(a:ascii),
length s1 + n.+1=length (s1++(String a "")) + n);
[by move=>s2 n2 a2;rewrite addnS;rewrite-addSn;f_equal;elim:s2;
[|move=>a3 s2 H8;simpl;f_equal]|].
rewrite (H8 s1 n1 a1)=>{H8}.
case:(s1 ++ String a1 "").
by[].
move=>a2 s2.
simpl.
apply (H7 s2 s0).
rewrite-{1}H2.
rewrite mulnC.
rewrite mulnDr.
rewrite muln1.
rewrite mulnC.
move:H4;rewrite-{1}(add0n n)=>H4.
rewrite-{1}(substringlemma2 0 n s H4).
apply H6. Qed.

Theorem REG_RSL (M:Automaton)(s:string):
s!="" -> accept M s -> (ss_accept (Aut_to_Stk M) s).
Proof.
move=>s_notempty H.
destruct M as ((((K,V),delta),s0),F).
have H1:(Vword s V);[by move:H;rewrite/accept;case (Vword s V)|].
case H2:(length s <= Datatypes.length K + 1).
by have {}s_notempty:(0<length s);[move:s_notempty;elim s|rewrite p1].
have {s_notempty}H2:(length s > Datatypes.length K + 1);
[by rewrite ltnNge;move:H2;case (length s <= Datatypes.length K + 1)|].



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
case:((s1, substring 0 (length s1 - l_index (dstar delta s0 s1) K - 1) s1, 0, 0)
      \in createDomino l s0 (K, V, delta, s0, F));
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


Theorem REG_RSL (M:Automaton)(s:string):accept M s -> (ss_accept (Aut_to_Stk M) s).
Proof.
split.

elim s.
move => H.

















