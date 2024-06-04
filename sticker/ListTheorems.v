From mathcomp Require Import all_ssreflect.
Require Import List Arith.

Lemma appnil {e:eqType}(l:list e):l = l++nil.
Proof. by elim l;[|simpl;move => a l0 H;rewrite <- H]. Qed.

Lemma in_undup {e:eqType}(l:list e)(a:e):(a \in (undup l)) = (a \in l).
Proof.
elim l;[by []|simpl;unfold in_mem;simpl;move => a0 l0 H].
by case_eq (mem_seq l0 a0);simpl;rewrite <- H;[case_eq (a==a0)
;[simpl;move => H';rewrite <-(eqP H');rewrite H|]|].
Qed.

Lemma in_app {e:eqType}(l1 l2:list e)(a:e):a \in l1++l2 = (a \in l1)||(a \in l2).
Proof. by elim l1;[|move => a0 l H;unfold in_mem;simpl;case (a==a0);simpl]. Qed.























