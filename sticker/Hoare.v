Inductive Expression:Type:=
|Na : nat -> Expression
|Plus : Expression -> Expression -> Expression
|Minus : Expression -> Expression -> Expression
|Mult : Expression -> Expression -> Expression.
Inductive Statement:Type:=
|Eq Expression -> Expression -> Statement
|IF Expression
|
Variable Expression:Type.
Definition IF:=Prop