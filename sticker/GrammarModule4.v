(***************************************************************************)
(* Coq Modules for Automata and Sticker Systems                            *)
(* Hisaharu Tanaka, Issei sakashita, Shuichi Inokuchi, Yoshihiro Mizoguchi *)
(*                                                                         *)
(* Yoshihiro Mizoguchi ( ym@imi.kyushu-u.ac.jp )                           *)
(* Institute of Mathematics for Industry, Kyushu University 2014.01.29     *)
(***************************************************************************)

(* GrammarModule.v *)

From mathcomp Require Import all_ssreflect.

Require Import Ascii String Bool ListSet.
Require Import AutomatonModule StickerModule.
Close Scope nat_scope.

Definition Rule(e:Type) := e * list e.
Definition RuleSet(e:Type) := list (Rule e).
Definition StartSymbol(e:Type) := e.
Definition TerminalSymbol(e:Type) :=list e.
Definition NonTerminalSymbol(e:Type) := list e.
Definition Grammar (e:Type) := TerminalSymbol e * NonTerminalSymbol e * RuleSet e * StartSymbol e.

Open Scope nat_scope.
Fixpoint TerminalQ {e:eqType} (ts:TerminalSymbol e) (ss:list e):bool := 
match ss with
| nil => true
| h::t => if (h \in ts) then (TerminalQ ts t) else false
end.

Fixpoint g_onestep {e:eqType} (rl:Rule e) (s:list e) :list (list e) :=
let ' (l, r):=rl in
match s with
| nil => [::]
| h::t => 
  if (h == l) then 
    undup (app (map (cons h) (g_onestep rl t)) [::(app r t)]) 
  else undup (map (cons h) (g_onestep rl t))
end.


Definition g_onestep'{e:eqType} (rs:RuleSet e) (s:list e) : list (list e) :=
undup(flatten [seq (g_onestep r s)|r <- rs]).

Definition g_generate'{e:eqType} (n:nat) (g:Grammar e) : list (list e) :=
let ' (ts, nts, rs, s0) := g in 
  (nstep n (g_onestep' rs)) [::[::s0]].

Definition g_generate{e:eqType} (n:nat) (g:Grammar e) : list (list e) :=
  undup (flatten [seq (g_generate' i g) | i<- (List.seq 1 n)]).

Definition g_language'{e:eqType} (n:nat) (g:Grammar e) : list (list e) :=
let ' (ts, nts, rs, s0) := g in
  (filter 
    (TerminalQ ts)
    (g_generate n g)
  ).

Definition g_language{e:eqType} (n:nat) (g:Grammar e) : list (list e) :=
  undup (flatten [seq (g_language' i g) | i<- (List.seq 1 n)]).

Definition nfgen'{e:eqType} (n:nat) (f:list e->bool) (g:Grammar e) (s1:e): list (list e) :=
let ' (ts, nts, rs, s0):=g in 
  (filter
    (TerminalQ ts) 
    ((nfstep f n (g_onestep' rs)) [::[::s1]])
  ).

Definition nfgen {e:eqType}(n:nat) (f:list e->bool) (g:Grammar e) (s1:e): list (list e) :=
  undup (flatten [seq (nfgen' i f g s1) | i<- (List.seq 1 n)]).

Definition nffgen' {e:eqType}(n:nat) (f:list e->bool) (g:Grammar e) (s1:e) (s2:e): list (list e) :=
  let ' (ts, nts, rs, s0):=g in
    (filter 
      (fun x => s2 \in x) 
      ((nfstep f n (g_onestep' rs)) [::[::s1]])
    ).

Definition nffgen {e:eqType}(n:nat) (f:list e->bool) (g:Grammar e) (s1:e) (s2:e): list (list e) :=
  undup (flatten [seq (nffgen' i f g s1 s2) | i<- (List.seq 1 n)]). 

Definition lincheck' {e:eqType}(nts:NonTerminalSymbol e) (w:list e): bool :=
(List.length 
  (filter 
    (fun x => x \in nts) 
    w
  )
)<2.

Fixpoint list_logical_and (l:seq bool) : bool :=
match l with
| [::] => true
| h::t => h&&(list_logical_and t)
end.

Definition lincheck {e:eqType}(g:Grammar e) : bool :=
  let ' (ts, nts, rs, s0):=g in
    list_logical_and 
    (map 
      (fun x => let ' (c,s):=x in (lincheck' nts s))
      rs
    ).

Fixpoint lpart {e:eqType}(n:NonTerminalSymbol e) (w:list e): list e :=
match w with
| nil => nil
| h::t  => if (h \in n) then nil 
                 else h::(lpart n t)
end.

Fixpoint rpart {e:eqType}(n:NonTerminalSymbol e) (w:list e): list e :=
match w with
| nil => nil
| h::t => if (h \in n) then t 
                 else (rpart n t)
end.

Fixpoint jth_n {e:eqType}(nts:NonTerminalSymbol e) (h:e):nat :=
match nts with
|[::] => 0
| hn::tn => if (h==hn) then 1
            else  (jth_n tn h) + 1
end.

Fixpoint jpart {e:eqType}(nts:NonTerminalSymbol e) (w:list e): nat :=
match w with
| nil => 0
| h::t  =>
  if (h \in nts) then (jth_n nts h)
  else (jpart nts t)
end.

Definition g_flanguage' {e:eqType}(n:nat) (f:list e->bool) (g:Grammar e):list (list e) :=
let ' (ts, nts, rs, s0) := g in
  (filter 
    (TerminalQ ts)
    (nfstep f n (g_onestep' rs) [::[::s0]])
  ).

Definition g_flanguage {e:eqType}(n:nat) (f:list e->bool) (g:Grammar e):list (list e) :=
  undup(
    flatten [seq (g_flanguage' i f g) | i<- (List.seq 1 n)]
  ). 