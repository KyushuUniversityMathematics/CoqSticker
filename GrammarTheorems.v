From mathcomp Require Import all_ssreflect.

Require Import Ascii String Bool ListSet.
Require Import GrammarModule4.
Fixpoint isREGr {a:eqType}(P:RuleSet a)(T:TerminalSymbol a)(N:NonTerminalSymbol a):bool :=
match P with
|nil => true
|(_,nil)::P' => isREGr P' T N
|(_,[::t])::P' => (t \in T)&&(isREGr P' T N)
|(_,[::t;n])::P' => (t \in T)&&(n \in N)&&(isREGr P' T N)
|(_,_)::P' => false
end.
Fixpoint isREGl {a:eqType}(P:RuleSet a)(T:TerminalSymbol a)(N:NonTerminalSymbol a):bool :=
match P with
|nil => true
|(_,nil)::P' => isREGl P' T N
|(_,[::t])::P' => (t \in T)&&(isREGl P' T N)
|(_,[::t;n])::P' => (t \in T)&&(n \in N)&&(isREGl P' T N)
|(_,_)::P' => false
end.
Definition isREG {a:eqType}(g:Grammar a):bool :=
let ' (T,N,P,s) := g in
(isREGr P T N)||(isREGl P T N).
Lemma lin_to_reg {e:eqType}(g:Grammar e):g_is_lin g -> true.