From mathcomp Require Import all_ssreflect.


Lemma lesub (m n:nat):m <= n <-> (m - n = 0).
Proof. split;[move/(subnBl_leq 0);by rewrite subn0|].
move:m;elim:n;[move=>m;rewrite subn0=>H;by rewrite H|].
move=>n H;by case;[|move=>m;rewrite subSS;move/H]. Qed.

Lemma filter_cons{T : Type}(p : pred T)(a:T)(s:seq T):
[seq x <- a::s | p x] = 
  if p a then a::[seq x<-s|p x] else [seq x<-s|p x].
Proof. done. Qed.

Fixpoint filter_option{T:Type}(s:seq (option T)):seq T:=
match s with
|nil => nil
|Some t::s' => t::(filter_option s')
|None::s' => filter_option s'
end.

Lemma bool_eqsplit (a b:bool):(a=b)<->(a<->b).
Proof. split;[by move=>H;rewrite H|];case;have t:true;[done|];
case:a;case:b;[done| | |done];[move=>H|move=>H' H];by move:(H t). Qed.

Lemma map_f' {t1 t2 t3:eqType}(f:t1->t2->t3)(l1:list t1)(l2:list t2)(x1:t1)(x2:t2):
x1\in l1->x2\in l2->f x1 x2 \in [seq f x y|x<-l1,y<-l2].
Proof. move=>H H1;move:H;elim:l1;[done|];simpl;move=>a l H2;rewrite in_cons;
rewrite mem_cat;case H3:(x1==a);[rewrite (eqP H3);move=>H4{H4};move:H1;
case:(f a x2 \in [seq f x y | x <- l, y <- l2]);
[by rewrite Bool.orb_true_r|rewrite Bool.orb_false_r;apply map_f]|];
case:(f x1 x2 \in [seq f a y | y <- l2]);
[by rewrite Bool.orb_true_l|by rewrite!Bool.orb_false_l]. Qed.

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

Lemma language'length(n:nat)(symbol:finType):
all(fun p=>0<size p<=n)(language' n symbol).
Proof.
elim:n.
done.
move=>n H.
rewrite/=all_cat.
apply/andP.
split.
apply/sub_all/H.
rewrite/subpred=>x{H}.
case H:(size x<=n).
by rewrite(leqW H).
by case x.
move:(languagelength n.+1 symbol)=>{}H.
apply/sub_all/H.
rewrite/subpred=>x/eqP{}H.
by rewrite H leqnn.
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
Lemma map_f_eq{t1 t2:eqType}(f:t1->t2)(l:list t1)(x:t1):
(forall x y:t1,f x= f y -> x = y) -> x\in l = (f x \in [seq f i|i<-l]).
Proof.
move=>H.
elim:l.
done.
move=>a l H1.
simpl.
rewrite!in_cons-H1.
case:(x \in l);[by rewrite!Bool.orb_true_r|rewrite!Bool.orb_false_r].
case_eq(f x==f a).
move/eqP/H=>{}H.
apply/eqP/H.
case xa:(x==a).
rewrite-(eqP xa).
by move/eqP.
done.
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
case:((x1 \in l) && (x2 \in l2));
[by rewrite Bool.orb_true_r|rewrite Bool.orb_false_r].
elim:l2.
done.
move=>b{}l H1.
simpl.
rewrite in_cons-H1 Bool.orb_false_r.
case_eq(f x1 x2 == f a b);[move/eqP/H|done].
case.
move:x1a.
by move/eqP.
Qed.

Lemma map_length {t1 t2}(f:t1->t2)(l:list t1):
List.length [seq f x|x<-l] = List.length l.
Proof. by elim:l;[|move=>a l H;simpl;f_equal]. Qed.

























