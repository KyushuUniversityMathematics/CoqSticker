(***************************************************************************)
(* Coq Modules for Automata and Sticker Systems                            *)
(* Hisaharu Tanaka, Issei sakashita, Shuichi Inokuchi, Yoshihiro Mizoguchi *)
(*                                                                         *)
(* Yoshihiro Mizoguchi ( ym@imi.kyushu-u.ac.jp )                           *)
(* Institute of Mathematics for Industry, Kyushu University 2014.01.29     *)
(***************************************************************************)

(* StickerEx1.v *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

Require Import Ascii String.

From sticker Require Import AutomatonModule StickerModule AutomatonEx.

Definition dmnnull:Domino := (""%string,""%string,0,0).
Definition dmn1:Domino := ("aaa"%string,"aa"%string,0,0).
Definition dmn2:Domino := ("aaa"%string,"aaa"%string,0,1).
Definition rho1:Rho := [:: ("a"%char,"a"%char); ("b"%char,"b"%char)].
Definition s1:list Symbol := [:: "a"%char; "b"%char].
Definition stk1:Sticker := (s1,rho1,[:: dmn1],[:: (dmnnull,dmn2)]).

Definition aA1 (m:Automaton) : list Domino :=
let ' (q,s,d,q0,f) := m in
[seq (x,x,0,0) | x <- (accepts m (sigmann s ((List.length q) +1)))].

Open Scope string_scope.

Definition xupair (m:Automaton) (i:nat) : list (string*string) :=
let ' (q,s,d,q0,f) := m in
filter (fun xu => let ' (x,u) := xu in ((dstar d 0 (x++u)) == (i-1))) 
(flatten [seq [seq (x,u)|x<-(sigman s ((List.length q) + 1 - i))]|u <- (sigman s i)]).

Definition aA2' (m:Automaton) (i:nat) : list Domino :=
let ' (q,s,d,q0,f) := m in
[seq let ' (x,u) := xu in (x++u,x,0,0)|xu <- (xupair m i)].

Definition aA2 (m:Automaton) : list Domino :=
let ' (q,s,d,q0,f) := m in
flatten [seq (aA2' m i) |i <- (List.seq 1 (List.length q))].

Close Scope string_scope.

Definition aA (m:Automaton) : list Domino :=
(aA1 m)++(aA2 m).

Open Scope string_scope.

Definition xuvtripe (m:Automaton) (i j:nat) : list (string*string*string) :=
let ' (q,s,d,q0,f) := m in
filter (fun xuv => let ' (x,u,v) := xuv in ((dstar d (j-1) (x++u)) == (i-1))) 
(flatten (flatten [seq [seq [seq (x,u,v)|x<-(sigman s ((List.length q) + 1 - i))]|u <- (sigman s i)]|v <- (sigman s j)])).


Definition dD' (m:Automaton) (i j:nat) : list Domino :=
let ' (q,s,d,q0,f) := m in
[seq let ' (x,u,v) := xuv in (x++u,v++x,0,String.length v)|xuv <- (xuvtripe m i j)].

Definition dD (m:Automaton) : list Domino :=
let ' (q,s,d,q0,f) := m in
flatten (flatten [seq [seq (dD' m i j)| i <- (List.seq 1 (List.length q))]|j <- (List.seq 1 (List.length q))]).

Definition xvpair (m:Automaton) (i j:nat) : list (string*string) :=
let ' (q,s,d,q0,f) := m in
filter (fun xv => let ' (x,v) := xv in ((dstar d ((String.length v)-1) x) \in f))
(flatten [seq [seq (x,v)|x<-(sigman s i)]|v <- (sigman s j)]).

Definition dF' (m:Automaton) (i j:nat) : list Domino :=
let ' (q,s,d,q0,f) := m in
[seq let ' (x,v) := xv in  (x,v++x,0,String.length v)|xv <- (xvpair m i j)].

Definition dF (m:Automaton) : list Domino :=
let ' (q,s,d,q0,f) := m in
flatten (flatten [seq [seq (dF' m i j)| i <- (List.seq 1 ((List.length q)+1))]|j <- (List.seq 1 (List.length q))]).

Definition dF_R (m:Automaton) : list Domino :=
let ' (q,s,d,q0,f) := m in
flatten (flatten [seq [seq (dF' m i j)| i <- (List.seq 1 ((List.length q)-1))]|j <- (List.seq 1 (List.length q))]).


Definition mGamma_dd (m:Automaton) : list (Domino*Domino) :=
map (fun x => (("","",0,0),x)) (undup ((dD m)++(dF m))).

Definition mGamma_dd_R (m:Automaton) : list (Domino*Domino) :=
map (fun x => (("","",0,0),x)) (undup ((dD m)++(dF_R m))).

Definition mGamma_rho (m:Automaton) : list (Symbol*Symbol) :=
let ' (q,s,d,q0,f) := m in
map (fun x=> (x,x)) s.

Definition mGamma (m:Automaton) : Sticker :=
let ' (q,s,d,q0,f) := m in
(s,(mGamma_rho m),(aA m),(mGamma_dd m)).

Definition mGamma_R (m:Automaton) : Sticker :=
let ' (q,s,d,q0,f) := m in
(s,(mGamma_rho m),(aA m),(mGamma_dd_R m)).

Open Scope string_scope.

Fixpoint member_check (a:SymbolString) (l:list SymbolString) : bool :=
match l with
  | [::] => false
  | (l0::l1) =>
  if  l0 == a 
  then true
  else member_check a l1
end.

Close Scope string_scope.
Definition ss_accept (stk:Sticker) (a:SymbolString):bool:=
member_check a (ss_language (String.length a) stk).

Definition ss_accepts (stk:Sticker) (ss:SymbolStrings): SymbolStrings:=
(filter (ss_accept stk) ss). 

Compute xupair m1 0.
Compute aA1 m1.
