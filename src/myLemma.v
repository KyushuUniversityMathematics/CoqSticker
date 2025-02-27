From mathcomp Require Import all_ssreflect.

(** %
\vspace{0.3cm}
\begin{screen}
$m,n:nat\\
m\le n\Rightarrow m-n=0$
\end{screen}% **)
Lemma lesub (m n:nat):m <= n <-> (m - n = 0).
Proof. split;[move/(subnBl_leq 0);by rewrite subn0|].
move:m;elim:n;[move=>m;rewrite subn0=>H;by rewrite H|].
move=>n H;by case;[|move=>m;rewrite subSS;move/H].
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
option型のリストからNoneを除外しSomeの中身のみを取り出す関数\\
例:[Some 1, None, None, Some 2, Some 0]$\mapsto$[1, 2, 0]
\end{screen}% **)
Fixpoint filter_option{T:Type}(s:seq (option T)):seq T:=
match s with
|nil => nil
|Some t::s' => t::(filter_option s')
|None::s' => filter_option s'
end.

(** %
\vspace{0.3cm}
\begin{screen}
filter\_option関数はリスト結合に対して分配的に働く
\end{screen}% **)
Lemma filter_option_cat{T:Type}(x y:seq (option T)):
filter_option(x++y)=filter_option x++filter_option y.
Proof. elim:x;[done|]=>a x H;case:a;[|done]=>a;by rewrite cat_cons/=;f_equal. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$a,b:bool\\
a=b\Leftrightarrow(a\Leftrightarrow b)$
\end{screen}% **)
Lemma bool_eqsplit (a b:bool):(a=b)<->(a<->b).
Proof. split;[by move=>H;rewrite H|];case;have t:true;[done|];
case:a;case:b;[done| | |done];[move=>H|move=>H' H];by move:(H t).
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$x\in X,y\in Y\Rightarrow f(x,y)\in f(X,Y)$
\end{screen}% **)
Lemma map_f' {t1 t2 t3:eqType}(f:t1->t2->t3)(l1:list t1)(l2:list t2)(x1:t1)(x2:t2):
x1\in l1->x2\in l2->f x1 x2 \in [seq f x y|x<-l1,y<-l2].
Proof. move=>H H1;move:H;elim:l1;[done|];simpl;move=>a l H2;rewrite in_cons;
rewrite mem_cat;case H3:(x1==a);[rewrite (eqP H3);move=>H4{H4};move:H1;
case:(f a x2 \in [seq f x y | x <- l, y <- l2]);
[by rewrite Bool.orb_true_r|rewrite Bool.orb_false_r;apply map_f]|];
case:(f x1 x2 \in [seq f a y | y <- l2]);
[by rewrite Bool.orb_true_l|by rewrite!Bool.orb_false_l].
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
n:nat, $\Sigma$:alphabet\\
language n $\Sigma$ : $\Sigma^n$
\end{screen}% **)
Fixpoint language(n:nat)(symbol:finType):seq (seq symbol):=
match n with
 |0 => [::nil]
 |S n' => [seq s::l|l<-language n' symbol,s<-enum symbol]
end.

(** %
\vspace{0.3cm}
\begin{screen}
n:nat, $\Sigma$:alphabet\\
language' n $\Sigma$ : $\bigcup_{k=1}^n\Sigma^k$
\end{screen}% **)
Fixpoint language' (n:nat)(symbol:finType):seq (seq symbol):=
match n with
|0 => nil
|S n' => (language' n' symbol)++(language n symbol)
end.

(** %
\vspace{0.3cm}
\begin{screen}
n:nat, $\Sigma$:alphabet\\
$\forall w\in$ language' n $\Sigma$, $|w|>0$
\end{screen}% **)
Lemma language'nil(n:nat)(symbol:finType):
all(fun p=>p!=nil)(language' n symbol).
Proof.
elim:n;[done|]=>n H.
rewrite/=all_cat H/=.
elim:(language n symbol);[done|]=>a l{n}H.
rewrite/=all_cat H Bool.andb_true_r.
by elim:(enum symbol).
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
n:nat, $\Sigma$:alphabet\\
$\forall w\in$ language n $\Sigma$, $|w|=n$
\end{screen}% **)
Lemma languagelength(n:nat)(symbol:finType):
all(fun p=>size p==n)(language n symbol).
Proof.
elim:n;[done|]=>n;simpl.
elim:(language n symbol);[done|]=>a l H.
move/andP.
case=>H1/H=>{}H.
rewrite all_cat H Bool.andb_true_r=>{l H}.
elim:(enum symbol);[done|]=>b l H.
by rewrite/=H Bool.andb_true_r eqSS/eqP H1.
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
n:nat, $\Sigma$:alphabet\\
$\forall w\in$ language' n $\Sigma, 0<|w|\le n$
\end{screen}% **)
Lemma language'length(n:nat)(symbol:finType):
all(fun p=>0<size p<=n)(language' n symbol).
Proof.
elim:n;[done|]=>n H.
rewrite/=all_cat;apply/andP.
split.
apply/sub_all/H;rewrite/subpred=>x{H}.
by case H:(size x<=n);[rewrite(leqW H)|case x].
apply/sub_all/(languagelength n.+1 symbol);rewrite/subpred=>x/eqP{}H.
by rewrite H leqnn.
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$\Sigma$:alphabet, $w\in\Sigma^*$\\
$w\in $language $|w|$ $\Sigma$
\end{screen}% **)
Lemma languagelemma{V:finType}(s:seq V):s\in (language (size s) V).
Proof. by elim:s;[|move=>a l H;simpl;apply/map_f';[|apply/mem_enum]]. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$\Sigma$:alphabet, $w\in\Sigma^+$\\
$w\in$ language' $|w|$ $\Sigma$
\end{screen}% **)
Lemma language'lemma{f:finType}(s:seq f)(n:nat):
s<>nil -> size s <= n -> s \in language' n f.
Proof.
move=>H/subnKC=>H1;rewrite-H1=>{H1}.
elim:(n - size s)=>[|{}n{}H].
rewrite addn0.
rewrite/language'.
case_eq(size s)=>[|n0 H1].
by move:H;case s.
by rewrite mem_cat;apply/orP;right;rewrite-H1 languagelemma.
by rewrite addnS/=mem_cat;apply/orP;left.
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
有限型はenumによって図鑑化されている\\
任意の有限型の要素の図鑑番号はその有限型の濃度より低い\\
$\Sigma$:alphabet\\
$\forall s\in\Sigma$, index $s$ $\Sigma<|\Sigma|$
\end{screen}% **)
Lemma fin_index{f:finType}(a:f):index a (enum f) < #|f|.
Proof.
rewrite cardE.
have:a\in (enum f);[apply/mem_enum|].
elim:(enum f);[done|]=>f0 ef H.
rewrite in_cons;move/orP;case.
move=>/eqP af0.
rewrite-af0=>{f0 af0}.
rewrite/=(_:a==a=true);[done|by apply/eqP].
simpl=>/H{}H.
by case:(f0 == a).
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
同じ長さで等しくないリストx,yを並べて各要素を見比べたとき、必ず異なる部分がある
\end{screen}% **)
Lemma fin_zip_neq{f:finType}(x y:seq f):x<>y->size x=size y->
all(fun p=>p\in zip(enum f)(enum f))(zip x y)=false.
Proof.
move:y.
elim:x;[by case|]=>a x H.
case;[done|]=>b y H1.
have{}H1:a<>b\/x<>y.
case_eq(a==b)=>/eqP ab;case_eq(x==y)=>/eqP xy;subst;by [|right|left|right].
destruct H1.
suff H2:(a, b) \in zip (enum f) (enum f)=false;[by rewrite/=H2|].
elim:(enum f);[done|]=>a0 l H1.
rewrite/=in_cons H1 Bool.orb_false_r;apply/eqP.
by move=>[H2 H3];subst.
move:H0=>/H{}H[]/H{}H.
by rewrite/=H Bool.andb_false_r.
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$X:set$\\
$X\cap X^c=\phi$
\end{screen}% **)
Lemma filter_nil{e:eqType}(l:seq e)(P:e->bool):
[seq a<-[seq b <- l|P b]|~~P a]=nil.
Proof. by elim:l;[|move=>a l H;simpl;case H1:(P a);[rewrite/=H1|]]. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$X:set$, $x\in X$, $A,B\subseteq X$\\
$A=B\Rightarrow A\cup{x}=B\cup{x}$
\end{screen}% **)
Lemma eq_mem_cons{e:eqType}(a:e)(l1 l2:seq e):l1 =i l2 -> a::l1 =i a::l2.
Proof.
rewrite/eq_mem=>H x.
rewrite!in_cons;apply/orP.
case:(x==a);[by left|].
move:(H x).
by case:(x \in l2)=>{}H;rewrite H;[right|case].
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$A,B,C,D:set$\\
$A=B,C=D => A\cup C＝B\cup D$
\end{screen}% **)
Lemma eq_mem_cat{e:eqType}(x y z w:seq e):x=i y->z=i w->x++z=i y++w.
Proof.
rewrite/eq_mem=>H H1 x0.
move:(H x0)(H1 x0)=>{}H{}H1.
rewrite!mem_cat.
by destruct (x0\in z),(x0\in x),(x0\in y).
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$A,B:set$\\
$A=B\Leftrightarrow B=A$
\end{screen}% **)
Lemma eq_memS{e:eqType}(x y:seq e):(x =i y)<->(y =i x).
Proof. split;by rewrite/eq_mem. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$A,B,C:set\\
A=B,B=C\Rightarrow A=C$
\end{screen}% **)
Lemma eq_memT{e:eqType}(x y z:seq e):(x =i y)->(y =i z)->(x=i z).
Proof. by rewrite/eq_mem=>H H1 x0;move:(H x0)(H1 x0)=>{}H;rewrite-H. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$X:set$, $f:X\rightarrow$bool, $A,B\subseteq X$\\
$A=B\Rightarrow \{a\in A|f a = true\}=\{b\in B|f b = true\}$
\end{screen}% **)
Lemma eq_mem_filter{e:eqType}(x y:seq e)(f:e->bool):(x =i y)->
[seq a<-x|f a]=i[seq a<-y|f a].
Proof. by rewrite/eq_mem=>H x0;rewrite!mem_filter-H. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$A,B:set$
$A\cup B＝B\cup A$
\end{screen}% **)
Lemma eq_mem_catC{e:eqType}(x y:seq e):x++y=i y++x.
Proof. by rewrite/eq_mem=>x0;rewrite!mem_cat;destruct(x0\in x),(x0\in y). Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$X,Y,Z:set$, $f:X\times Y\rightarrow Z$\\
$X=Y\Rightarrow f(X,Z)=f(Y,Z)$
\end{screen}% **)
Lemma eq_mem_map'{e1 e2 e3:eqType}(x y:seq e1)(z:seq e2)(f:e1->e2->e3):
x=i y->[seq f a b|a<-x,b<-z]=i[seq f a b|a<-y,b<-z].
Proof.
move=>H.
elim:z=>[|c z H1].
by have H1:forall(l:seq e1),[seq f a b|a<-l,b<-nil]=nil;[elim|rewrite!H1].
have H2:forall(l:seq e1),[seq f a b | a <- l, b <- c::z]=i
  [seq f a c|a<-l]++[seq f a b|a<-l,b<-z].
elim;[done|]=>a l H2.
remember(c::z)as z';rewrite/={1}Heqz'/=;apply/eq_mem_cons;rewrite catA.
have H3:([seq f a0 c | a0 <- l] ++ [seq f a b | b <- z]) ++
     [seq f a0 b | a0 <- l, b <- z]=i
      ([seq f a b | b <- z]++[seq f a0 c | a0 <- l]) ++
     [seq f a0 b | a0 <- l, b <- z].
by apply/eq_mem_cat;[apply/eq_mem_catC|].
apply/eq_memT;[|apply/eq_memS/H3];rewrite-catA;by apply/eq_mem_cat.
apply/eq_memS/eq_memT/eq_memT/eq_memS/H2/eq_mem_cat/eq_memS/H1/eq_mem_map/eq_memS/H/H2.
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$X,Y:set$\\
filter\_option $X$ = filter\_option $Y$
\end{screen}% **)
Lemma eq_mem_filter_option{e:eqType}(x y:seq(option e)):
x=i y -> filter_option x =i filter_option y.
Proof.
have H:(forall x:e,forall l:seq(option e),(Some x\in l) = (x\in filter_option l)).
move=>x0 l.
elim:l;[done|]=>a l H.
by destruct a;[rewrite/=!in_cons H;case:(x0 \in filter_option l)|].
rewrite/eq_mem=>H1 x0.
by rewrite-!H.
Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$n,m:nat$\\
m+n-n=m
\end{screen}% **)
Lemma add_subABB(m n:nat):m+n-n=m.
Proof. by elim:n=>[|n H];[rewrite addn0 subn0|rewrite addnS subSS]. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$n,m:nat$\\
n+m-n=m
\end{screen}% **)
Lemma add_subABA(m n:nat):n+m-n=m.
Proof. by elim:n=>[|n H];[rewrite add0n subn0|rewrite addSn subSS]. Qed.

(** %
\vspace{0.3cm}
\begin{screen}
$n,m:nat$\\
$n<m$ or $n=m$ or $n>m$
\end{screen}% **)
Lemma nat_compare(n m:nat):{n<m}+{n=m}+{n>m}.
Proof. by move:(Compare_dec.lt_eq_lt_dec n m)=>
[[/ltP|]|/ltP];[left;left|left;right|right]. Qed.