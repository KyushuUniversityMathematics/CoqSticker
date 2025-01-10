Require Import Ascii String.
Inductive Expression:Type:=
|Nat(n:nat)
|Var(a:ascii)
|Plus(x y:Expression)
|Minus(x y:Expression)
|Mult(x y:Expression).
Notation "x _+_ y":=(Plus x y)(at level 2).
Notation "x _-_ y":=(Minus x y)(at level 1).
Notation "x _*_ y":=(Mult x y)(at level 1).

Definition state:=ascii->nat.
Fixpoint Exnat(e:Expression)(s:state):nat:=
match e with
|Nat n => n
|Var a => s a
|x _+_ y => Exnat x s + Exnat y s
|x _-_ y => Exnat x s - Exnat y s
|x _*_ y => Exnat x s * Exnat y s
end.
Definition st(x:ascii):=
match x with
|"x"%char => 2
|"y"%char => 3
|_ => 0
end.
Definition prop(c:comparison)(n m:nat):bool:=
match c with
|Eq => Nat.eqb n m
|Lt => Nat.ltb n m
|Gt => Nat.ltb m n
end.

Print comparison.
Inductive Statement:Type.
|Null
|Assign(x:ascii)(n:nat)
|Seq(s t:Statement)
|If(p:prop)(s t:Statement)
Inductive com : Type :=
  | Skip
  | Assign (x : ascii) (e : nat)
  | Seq (c1 c2 : com)
  | If (b : bool) (c1 c2 : com)
  | While (b : bool) (c : com).
Definition state := ascii -> nat.

Definition assertion := state -> Prop.
Definition excec:
Inductive exec : com -> state -> state -> Prop :=
  | Exec_Skip : forall st, exec Skip st st
  | Exec_Assign : forall st x e n, 
      exec (Assign x e) st (fun st' => st' x = n)
  | Exec_Seq : forall c1 c2 st st' st'', 
      exec c1 st st' -> exec c2 st' st'' -> exec (Seq c1 c2) st st''
  | Exec_IfTrue : forall b c1 c2 st st', 
      b = true -> exec c1 st st' -> exec (If b c1 c2) st st'
  | Exec_IfFalse : forall b c1 c2 st st', 
      b = false -> exec c2 st st' -> exec (If b c1 c2) st st'
  | Exec_WhileTrue : forall b c st st', 
      b = true -> exec c st st' -> exec (While b c) st st'
  | Exec_WhileFalse : forall b c st,
      b = false -> exec (While b c) st st.


Definition hoare_triple (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st st', 
    exec c st st' -> P st -> Q st'.


