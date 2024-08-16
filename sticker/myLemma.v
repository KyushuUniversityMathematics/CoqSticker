From mathcomp Require Import all_ssreflect.
Require Import Bool Ascii String Arith AutomatonModule Recdef.

Lemma lesub (m n:nat):m <= n <-> (m - n = 0).
Proof. split;[move/(subnBl_leq 0);by rewrite subn0|].
move:m;elim:n;[move=>m;rewrite subn0=>H;by rewrite H|].
move=>n H;by case;[|move=>m;rewrite subSS;move/H]. Qed.

Lemma filter_cons{T : Type}(p : pred T)(a:T)(s:seq T):
[seq x <- a::s | p x] = 
  if p a then a::[seq x<-s|p x] else [seq x<-s|p x].
Proof. done. Qed.

Lemma bool_eqsplit (a b:bool):(a=b)<->(a<->b).
Proof. split;[by move=>H;rewrite H|];case;have t:true;[done|];
case:a;case:b;[done| | |done];[move=>H|move=>H' H];by move:(H t). Qed.

Lemma map_f' {t1 t2 t3:eqType}(f:t1->t2->t3)(l1:list t1)(l2:list t2)(x1:t1)(x2:t2):
x1\in l1->x2\in l2->f x1 x2 \in [seq f x y|x<-l1,y<-l2].
Proof. move=>H H1;move:H;elim:l1;[done|];simpl;move=>a l H2;rewrite in_cons;
rewrite mem_cat;case H3:(x1==a);[rewrite (eqP H3);move=>H4{H4};move:H1;
case:(f a x2 \in [seq f x y | x <- l, y <- l2]);
[by rewrite orb_true_r|rewrite orb_false_r;apply map_f]|];
case:(f x1 x2 \in [seq f a y | y <- l2]);
[by rewrite orb_true_l|by rewrite!orb_false_l]. Qed.
Lemma map_f_eq{t1 t2:eqType}(f:t1->t2)(l:list t1)(x:t1):
(forall x y:t1,f x= f y -> x = y) -> x\in l = (f x \in [seq f i|i<-l]).
Proof.
move=>H.
elim:l.
done.
move=>a l H1.
simpl.
rewrite!in_cons-H1.
case:(x \in l);[by rewrite!orb_true_r|rewrite!orb_false_r].
case_eq(f x==f a).
move/eqP/H=>{}H.
apply/eqP/H.
case xa:(x==a).
rewrite-(eqP xa).
by move/eqP.
done.
Qed.
Lemma map_f'_eq{t1 t2 t3:eqType}(f:t1->t2->t3)(l1:list t1)(l2:list t2)(x1:t1)
(x2:t2):(forall (x1 x2:t1)(y1 y2:t2),f x1 y1 = f x2 y2 -> x1=x2/\y1=y2)->
  (x1\in l1)&&(x2\in l2)=(f x1 x2 \in [seq f x y|x<-l1,y<-l2]).
Proof.
move=>H.
elim:l1.
done.
move=>a l H1.
simpl.
rewrite in_cons mem_cat-H1=>{H1}.
case x1a:(x1==a);simpl.
rewrite-(eqP x1a)-map_f_eq=>{x1a a}.
by case:(x2\in l2);case:(x1\in l).
move=>x y.
move/H.
by case.
case:((x1 \in l) && (x2 \in l2));[by rewrite orb_true_r|rewrite orb_false_r].
elim:l2.
done.
move=>b{}l H1.
simpl.
rewrite in_cons-H1 orb_false_r.
case_eq(f x1 x2 == f a b);[move/eqP/H|done].
case.
move:x1a.
by move/eqP.
Qed.

Lemma map_length {t1 t2}(f:t1->t2)(l:list t1):
List.length [seq f x|x<-l] = List.length l.
Proof. by elim:l;[|move=>a l H;simpl;f_equal]. Qed.

Function divide{t:Type}(n:nat)(l:seq t){measure size l}:seq(seq t) :=
match n,l with
|0,_ => [::l]
|_,nil => nil
|_,_=>(take n l)::(divide n (drop n l))
end.
Proof.
move=>t n l n0 H t0 l0 H1.
rewrite-{2}(cat_take_drop n0.+1 (t0::l0)).
rewrite size_cat.
simpl.
rewrite addSn.
apply/leP/leq_addl.
Qed.





Open Scope string_scope.
Definition dividestring (n:nat)(s:string):list string :=
match n,s with
|_,"" => nil
|0,_ => [::s]
|_,_ =>
let m :=
  if (length s) mod n == 0 then
    (length s)/n
  else
    (length s)/n + 1 in
[seq substring (i*n) n s|i <- List.seq 0 m]
end.

Lemma appendEmp (s:string):s++""=s.
Proof. by elim:s;[|move=>a s H;simpl;rewrite H]. Qed.
Lemma substringeq (s:string):substring 0 (length s) s = s.
Proof. by elim:s;[|move=>a s H;simpl;rewrite H]. Qed.
Lemma substringn0 (n:nat)(s:string):substring n 0 s = "".
Proof. move:n;elim:s;[|move=>a s H];by case. Qed.
Lemma substringlemma1 (n:nat)(s:string):
substring 0 n s ++ substring n (length s - n) s = s.
Proof. move:s;elim n;
[by move=>s;rewrite substringn0;rewrite subn0;rewrite substringeq|];
by move=>n0 H;case;[|simpl;move=>a s;rewrite subSS;f_equal]. Qed.
Lemma substringlemma2 (m n:nat)(s:string):m+n<=length s ->
length (substring m n s) = n.
Proof. have substringlength:(forall (n:nat)(s:string),
n <= length s -> length (substring 0 n s) = n);
[elim;[by move=>s2;rewrite substringn0|];by move=>n0 H3;case;
[|simpl;move=>a s2;move/ltnSE=>H4;move:(H3 s2 H4)=>H5;by f_equal]|];
by move:s;elim:m;[rewrite add0n;apply/substringlength|move=>n0 H;case;
[|simpl;move=>a s;rewrite addSn;move/ltnSE;apply H]]. Qed.
Lemma substringlemma3 (s t:string):substring 0 (length s) (s++t) = s.
Proof. elim:s;[apply/substringn0|move=>a s H;simpl;by rewrite H]. Qed.
Lemma substringlemma4 (m n:nat)(s t:string):
substring (length s + m) n (s++t) = substring m n t.
Proof. move:m;elim:s;[simpl;move=>m;by rewrite add0n|
move=>a s H m;simpl;apply H]. Qed.
Lemma substringlemma5 (n:nat)(s t:string):
substring 0 (length s + n) (s++t) = s++substring 0 n t.
Proof. by elim:s;[|move=>a s H;simpl;rewrite H]. Qed.




Lemma dividestringlemma (n:nat)(s:string):
concat "" (dividestring n s) = s.
Proof.
have maplemma:(forall (f:nat->string)(m n:nat),
[seq f i|i <- List.seq m n.+1]=(f m)::[seq f (1+i)|i <- List.seq m n]);
[by move=>f m n0;simpl;f_equal;move:m;elim n0;
[|move=>n1 H8 m;simpl;f_equal]|].
case n':n;[by case s|].

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
suff H7:(forall (s:string)(l:list string),
concat "" (s::l) = s++(concat "" l)).
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

rewrite-{1}H2.
rewrite mulnC.
rewrite mulnDr.
rewrite muln1.
rewrite mulnC.

move:H4;rewrite-{1}(add0n n)=>H4.
rewrite-{1}(substringlemma2 0 n s H4).
apply substringlemma4.
Qed.

Compute 5/2.
Lemma dividestringlength (n:nat)(s:string): List.length (dividestring n s) =
 if length s mod n == 0 then length s/n else length s/n + 1.
rewrite/dividestring.
Proof.
case:n;case:s;[done|done|
move=>n;rewrite Nat.Div0.mod_0_l;by rewrite (_:0==0);[|done]|
].
move=>a s n.
rewrite map_length.
suff H:(forall m n:nat,List.length (List.seq m n) = n).
rewrite H.
by case:(length (String a s) mod n.+1 == 0).
move=>m{}n.
move:m.
elim:n.
by[].
move=>n H m.
simpl.
by f_equal.
Qed.


Lemma dividestringlength2 (n:nat)(s:string):
 List.length (dividestring n s) <= length s.
Proof.
rewrite dividestringlength.
case:n.
simpl.
by case:s.
move=>n.
case smodn0:(length s mod n.+1 == 0). 
apply/leP/Nat.Div0.div_le_upper_bound.
rewrite multE.
rewrite mulSn.
apply/leP/leq_addr.
move:smodn0.
case:n.
by rewrite Nat.mod_1_r.
move=>n.
case:s.
by rewrite Nat.Div0.mod_0_l.
move=>a s _.

rewrite addn1.
apply/ltP/Nat.Div0.div_lt_upper_bound.
apply/ltP.
rewrite multE.
rewrite!mulSn.
rewrite{3}(_:length (String a s) = (length s).+1);[|done].
rewrite addSn.
rewrite addnS.
apply/leq_addr.
Qed.



Lemma stringlength (s t:string):length (s++t)=length s + length t.
Proof. by elim:s;[|move=>a s H;simpl;rewrite addSn;f_equal]. Qed.
Lemma appstring (s t u:string):s++t++u=(s++t)++u.
Proof. by elim:s;[|move=>a s H;simpl;f_equal]. Qed.
Lemma append_eqr (s t u:string):s++t==s++u=(t==u).
Proof. apply/bool_eqsplit;split;[|move/eqP=>H;by rewrite H];
by elim:s;[|move=>a s H;simpl;move/eqP=>[]/eqP]. Qed.
Lemma append_eql (s t u:string):s++t==u++t=(s==u).
Proof. apply/bool_eqsplit;split;[|move/eqP=>H;by rewrite H].
have H:(forall s t:string,s++t=t->s="").
move=> s0 t0 H.
have{H}:(length (s0++t0)=length t0).
by rewrite H.
rewrite stringlength.
elim (length t0).
rewrite addn0.
by case s0.
move=>n H.
rewrite addnS;by move=>[].
have H1:(forall s t : string,t = s++t -> "" = s).
move=>s0 t0 H1.
have:s0++t0=t0.
by rewrite-H1.
by move/H.

move:u.
elim:s.
simpl=>u.
by move/eqP/H1/eqP.
move=>a s H2.
elim.
rewrite (_:""++t=t);[|done].
by move/eqP/H/eqP.
move=>b u H3.
simpl.
by move/eqP=>[]=>ab/eqP/H2/eqP=>su;rewrite ab;rewrite su.
Qed.
Lemma append_eqlr (s t u v:string):s++u++t==s++v++t=(u==v).
Proof. by rewrite append_eqr;rewrite append_eql. Qed.




























