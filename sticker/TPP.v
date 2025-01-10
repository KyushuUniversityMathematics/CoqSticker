From mathcomp Require Import all_ssreflect.
Require Import Coq.Sorting.Permutation.
Fixpoint Rewrite{t:Type}(n:nat)(x:t)(s:seq t):seq t:= match n, s with 0, h::s' => x::s'|S n', h::s' => h::Rewrite n' x s'|_, nil => nil end.
Definition Swap(n m:nat)(s:seq nat):seq nat := Rewrite n(nth 0 s m)(Rewrite m(nth 0 s n)s).
Fixpoint Swaps(x:seq(nat*nat))(s:seq nat):seq nat:=
match x with
|nil => s
|(a,b)::x' => Swap a b(Swaps x' s)
end.
Compute Swap 2 5 [::0;1;2;3;4;5;6].
(*indexは0から*)


Fixpoint FindCycle'(x y z:seq nat)(n:nat):seq nat:=
match n with
|0 => z
|S n' =>
  let i := index(nth 0 x(head 0 z))y in
  if i == last 0 z then
    z
  else
    FindCycle' x y(rcons z i)n'
end.
Fixpoint FindCycle'(x y z:seq nat)(n:nat):seq(seq nat):=
Compute FindCycle[::5;9;1;3;7][::1;3;5;7;9].
Fixpoint CycleSwap'(x:seq nat):seq(nat*nat):=
match x with
|nil => nil
|a::x' =>
  match x' with
  |nil => nil
  |b::_ =>(a,b)::CycleSwap' x'
  end
end.
Fixpoint CycleSwap(x:seq(seq nat)):seq(nat*nat):=
match x with
|nil => nil
|a::x' => CycleSwap' a ++ CycleSwap x'
end.
Definition Cycle'(x y:seq nat):seq nat:=

Theorem CycleP
Fixpoint CycleDivide'(x y:seq nat)(z:seq(seq nat))(n:nat):seq(seq nat):=
match n with
|0 => z
|S n' =>
  if n'\in flatten z then
    CycleDivide' x y z n'
  else
    CycleDivide' x y((FindCycle x y[::n'](size x))::z)n'
end.
Definition CycleDivide(x y:seq nat):seq(seq nat):=CycleDivide' x y nil(size x).
Compute CycleDivide[::5;7;1;9;3][::1;3;5;7;9].

Fixpoint Cycle(x s:seq nat): seq nat :=
match x with
|a::x' =>
  match x' with
  |nil => s
  |b::_ => Swap a b(Cycle x' s)
  end
|nil => nil
end.
Fixpoint Cycles(x:seq(seq nat))(y:seq nat):seq nat:=
match x with
|nil => y
|a::x' => Cycles x'(Cycle(rev a)y)
end.
Compute Cycles(CycleDivide[::5;7;1;9;3][::1;3;5;9;7])[::5;7;1;9;3].
Lemma CycleDivideP(x y:seq nat):uniq x -> Permutation x y -> Cycles(CycleDivide x y)x = y.
Proof.
move=>u P.


Definition rotate{t:Type}(x:seq t):seq t:=
match x with
|nil => nil
|a::x => x++[::a]
end.
Fixpoint cyclic_eq'{e:eqType}(n:nat)(x y:seq e):bool :=
if x == y then
  true
else
  match n with
  |0 => false
  |S n' => cyclic_eq' n'(rotate x)y
  end.

  if (rotate x)==y then
    true
  else

Fixpoint my_in_mem{e:eqType}(x:seq e)(s:seq(seq e)):bool :=
match s with
|nil => false
|a::s' =>
  if a =i x then
    true
  else
    my_in_mem x s'
end.
Compute (mem[::2;1;3])=(mem [::1;2;3]).
Fixpoint myUndup(x:seq(seq nat)):seq(seq nat):=
match x with
|nil => nil
|a::x' => if a


Fixpoint CycleDivide(x y:seq nat)(z:seq(seq nat))(n:nat):seq(seq nat):=
match n with
|0 => z
|S n' =>
  match z with
  |nil => nil
  |a::z' =>
    match a with
    |nil => nil
    |b::a'=>
      let n := index(nth 0 x b)y in
      if n\in flatten z
      (n::a)::z'
end.
Fixpoint S'(x:seq(nat*nat)):seq(nat*nat):=match x with nil=>nil|(a,b)::x'=>(S a,S b)::S' x' end.
Fixpoint SortSwap(x y:seq nat):seq(nat*nat):=
match x with
|nil => nil
|a::x' =>
  let i := index a y in
  let y_ := Swap 0 i y in
  match y_ with
  |nil => nil
  |_::y' =>
    if i==0 then
      S'(SortSwap x' y')
    else
      (0,i)::S'(SortSwap x' y')
  end
end.
Compute SortSwap[::5;9;1;3;7][::1;3;5;7;9].
Compute SortSwap[::3;4;2;1][::1;2;3;4].
Compute SortSwap[::3;3;2;1][::1;2;3;3].
Compute Swaps(SortSwap[::5;9;1;3;7][::1;3;5;7;9])[::5;9;1;3;7].
Lemma SwapsS'(n:nat)(s:seq nat)(x:seq(nat*nat)):Swaps(S' x)(n::s)=n::Swaps x s.
Proof.
elim:x=>[|a x H];[done|].
destruct a.
rewrite/={}H.
by elim:(Swaps x s).
Qed.
Theorem SortSwapP(x y:seq nat):(forall n:nat,count_mem n x=count_mem n y)->
Swaps(SortSwap x y)x = y.
Proof.
move:y.
elim:x=>[|a x H].
case=>[|a l H];[done|].
move:(H a).
by rewrite/=eqxx/=add1n.
case=>[|b y]H1.
move:(H1 a).
by rewrite/=eqxx/=add1n.
simpl.
case_eq(b==a)=>[/eqP|]ab.
subst.
have{H1}:(forall n : nat, count_mem n x = count_mem n y).
move=>n.
move:(H1 n).
by simpl;case:(a==n);rewrite/=;[rewrite!add1n;move=>[]|rewrite!add0n].
move=>{}/H{}H.
by rewrite/=SwapsS' H.
have H2:a\in y.
move:(H1 a).
rewrite/=ab eqxx/=add1n add0n{H1 b ab}.
elim:y.
done.
move=>b y H1.
simpl.
case_eq(b==a)=>/eqP ab.
by rewrite in_cons ab eqxx.
rewrite add0n in_cons =>/H1{}H1.
by case:(a==b).
rewrite/=SwapsS'{}H.
rewrite/Swap/=.
f_equal;move:{H1}H2.
elim:y.
done.
move=>c y H.
rewrite/=in_cons.
case_eq(a==c)=>[/eqP ac _|/eqP ac/H{}H].
subst.
by rewrite eqxx.
rewrite(_:c==a=false)/=;[by rewrite H|apply/eqP;rewrite/not=>ca].
by subst.
elim:y=>[|c y H].
done.
rewrite in_cons.
case_eq(a==c)=>[/eqP ac _|/eqP/nesym ac/H{}H].
by rewrite/=ac eqxx.
rewrite/=(_:c==a=false)/=;[by f_equal|by apply/eqP].
move=>n.
move:{H1}(H1 n).
simpl.
case_eq(a==n)=>[/eqP|]an.
rewrite-{}an ab/=add1n add0n=>H.
apply/eq_add_S.
rewrite{x n}H.
move:H2.
elim:y=>[|c x H].
done.
rewrite in_cons.
case_eq(a==c)=>[/eqP ac _|/eqP ac/H{}H].
by rewrite-ac/=eqxx/=ab/=.
have{}ac:c==a=false;[by apply/eqP/not_eq_sym|].
by rewrite/=ac/=ac/=!add0n H.

rewrite/=add0n=>H.
rewrite{x}H.
move:H2.
elim:y=>[|c x H].
done.
rewrite in_cons.
case_eq(a==c)=>[/eqP ac _|/eqP ac/H{}H].
by rewrite/=-ac an/=add0n eqxx.
have{}ac:c==a=false;[by apply/eqP/not_eq_sym|].
rewrite/=ac/=.
case:(c==n).
rewrite/=!add1n addnS.
by f_equal.
done.
Qed.

Definition RemoveCycle(x y:seq nat):seq nat:=
match x with
|nil => nil
|a::x' =>a::drop(size x'-index(nth 0 y a)(rev[seq nth 0 y n|n<-x']))x'
end.
Compute RemoveCycle[::5;2;4;3;1;0][::1;2;2;3;4;5].

Compute SortSwap[::4;5;2;3;6;1][::1;2;3;4;5;6].
Compute Swaps(SortSwap[::4;5;2;3;6;1][::1;2;3;4;5;6])[::4;5;2;3;6;1].
Fixpoint LocateCycle(x y z:seq nat)(n:nat):seq nat:=
match n with
|0 => z
|S n' =>
  match z with
  |nil => nil
  |a::_ =>
    let i := index(nth 0 x a)y in
    LocateCycle x(Rewrite i 0 y)(i::z)n'
  end
end.
Definition LocateCycle'(x y:seq nat) :=
match y with
|nil => nil
|_::y' => rev(LocateCycle[seq S n|n<-x](0::[seq S n|n<-y'])[::0](size x).-1)
end.

Fixpoint CycleSwaps(x:seq nat):seq(nat*nat):=
match x with
|nil => nil
|a::x' =>
  match x' with
  |nil => nil
  |b::_ => (a,b)::CycleSwaps x'
  end
end.

Compute CycleSwaps [::5;3;1;4;2;0].
Compute Swaps(CycleSwaps(LocateCycle'[::2;3;4;4;1;1][::1;1;2;3;4;4]))[::2;3;4;4;1;1].

Definition Cycle(x y:seq nat):seq nat:=
let x' := rev(last 0 x::x) in
[seq nth 0 y(nth 0 x'(index n x').+1)|n <- List.seq 0(size y)].
Compute Cycle[::0;2;4;1;3;5][::2;3;4;4;1;1].
(*Lemma CycleP(x y:seq nat):Permutation x y -> Cycle(LocateCycle' x y)x = y.
Proof.
move=>P.
move:P=>/Permutation_length.
elim:x.
by case:y.
have H:size x = size y.
Search (size _ = length _).

List.seq*)
Compute LocateCycle'[::5;9;1;3;7][::1;3;5;7;9].
Theorem SwapsCorrect(x y:seq nat):Permutation x y -> Swaps(CycleSwaps(LocateCycle' x y))x = y.
Proof.
move/Permutation_length.
move:y.
elim:x;[by case|]=>a x H.
case;[done|]=>b y.
rewrite/=.
move=>[]/H{}H.
rewrite/LocateCycle'.
Compute LocateCycle[::2;3;4;4;1;1][::0;1;2;3;4;4][::0]5.
Compute LocateCycle'[::2;3;4;4;1;1][::0;1;2;3;4;4].
Compute LocateCycle[::2;3;5;4;2;1][::0;2;2;3;4;5][::0]5.
Definition DupIndex(x:seq nat):
let l := size x in


Fixpoint LocateCycle'(x y z:seq nat):seq nat:=
match x with
|nil => nil
|a::x' => 

Definition LocateCycle
Fixpoint MyIndex{e:eqType}(a:e)(x y:seq e):nat:=
match x with
|nil => size x
|h::x' =>
  match y with
  |nil => size x



Definition CycleDivide(x y:seq nat):

perm


case_eq(b==n)=>/eqP bn.


Search (_.+1=_.+1->_=_).
Locate"!=".

Bool.eqb_sym
move:H1.
simpl.


nth_index

move:H1.
elim:y=>[H|c y H H1].
move:(H a).
by rewrite/=eqxx ab add1n addn0.
simpl.
case_eq(c==a)=>/eqP ac.
subst.
have{H1}:forall n : nat, count_mem n (a :: x) = count_mem n (b :: y).
move=>n.
move:(H1 n).

simpl.
simpl.
rewrite!add1n.
by move=>[].
simpl.
rewrite/=.
rewrite/=SwapsS' H.
done.
admit.
case:(count_mem a l).
by rewrite addn0/=(_:a==a).
by rewrite addnS.
simpl.

case;[done|].
move=>b y.
rewrite/=eqSS=>/H{}H.
case_eq(b==a)=>[/eqP ab|].
subst.
rewrite/=SwapsS'.
admit.
simpl.



move=>H H1.

    match y with
    |
  match y with
  |nil => nil
  |a::y' => [seq S' n|n<- (SortSwap x' y')]
  |_ =>
    match Swap 1(index a y)y with
    |nil => nil
    |_::y' => (1,index a y)::S'(SortSwap x' y')
    end
  end
end.
  if index a y == 1 then
    match Swap 1 with
  match y with
  |nil => nil
  |b::y' =>
    if a==b then
      S'(SortSwap x' y')
    else
      (1,index a y)S'(SortSwap x' y')

Fixpoint Cycle(x s:seq nat): seq nat :=
match x with
|a::x' =>
  match x' with
  |nil => s
  |b::_ => Swap a b(Cycle x' s)
  end
|nil => nil
end.

Compute Cycle[::1;4;3][::5;9;1;3;7].
Compute Cycle[::0;1;3;4;2][::0;1;2;3;4].
Eval simpl in Cycle[::0;1;3;4;2].
Theorem minSwapCycle(x:seq nat)