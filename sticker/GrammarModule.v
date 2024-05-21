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
From sticker Require Import AutomatonModule StickerModule.

Close Scope nat_scope.

Definition Rule := Symbol * SymbolString.
Definition RuleSet := list Rule.
Definition StartSymbol := Symbol.
Definition TerminalSymbol :=Symbols.
Definition NonTerminalSymbol := Symbols.
Definition Grammar := TerminalSymbol * NonTerminalSymbol * RuleSet * StartSymbol.

Open Scope nat_scope.

Fixpoint list_inQ {a:eqType} (s:a) (ss:list a):bool :=
match ss with
  | nil => false
  | h::t => if s == h then true
            else list_inQ s t
end.

Fixpoint string_inQ (a:ascii) (s:string):bool :=
match s with
  | EmptyString => false
  | (String h t) => 
    if a==h then true
    else string_inQ a t
end.

Fixpoint TerminalQ (ts:TerminalSymbol) (ss:SymbolString):bool := 
match ss with
| EmptyString => true
| String h t => if (h \in ts) then (TerminalQ ts t) else false
end.

Fixpoint g_onestep (rl:Rule) (s:SymbolString) :list SymbolString :=
let ' (l, r):=rl in
match s with
| EmptyString => [::]
| String h t => 
  if (h == l) then 
    undup (app (map (String h) (g_onestep rl t)) [::(append r t)]) 
  else undup (map (String h) (g_onestep rl t))
end.


Fixpoint g_onestep' (rs:RuleSet) (s:SymbolString) : seq SymbolString :=
undup(flatten(map (fun rl => g_onestep rl s) rs)).

Fixpoint g_generate' (n:nat) (g:Grammar) : list SymbolString :=
let ' (ts, nts, rs, s0) := g in 
  (nstep n (g_onestep' rs)) [:: (String s0 EmptyString)].

Fixpoint g_generate (n:nat) (g:Grammar) : list SymbolString :=
  undup (flatten [seq (g_generate' i g) | i<- (List.seq 1 n)]).

Fixpoint g_language' (n:nat) (g:Grammar) : list SymbolString :=
let ' (ts, nts, rs, s0) := g in
  (filter 
    (TerminalQ ts)
    (g_generate n g)
  ).

Fixpoint g_language (n:nat) (g:Grammar) : list SymbolString :=
  undup (flatten [seq (g_language' i g) | i<- (List.seq 1 n)]).

Fixpoint nfgen' (n:nat) (f:SymbolString->bool) (g:Grammar) (s1:Symbol): list SymbolString :=
let ' (ts, nts, rs, s0):=g in 
  (filter
    (TerminalQ ts) 
    ((nfstep f n (g_onestep' rs)) [:: (String s1 EmptyString)])
  ).

Definition nfgen (n:nat) (f:SymbolString->bool) (g:Grammar) (s1:Symbol): list SymbolString :=
  undup (flatten [seq (nfgen' i f g s1) | i<- (List.seq 1 n)]).

Fixpoint nffgen' (n:nat) (f:SymbolString->bool) (g:Grammar) (s1:Symbol) (s2:Symbol): list SymbolString :=
  let ' (ts, nts, rs, s0):=g in
    (filter 
      (string_inQ s2) 
      ((nfstep f n (g_onestep' rs)) [:: (String s1 EmptyString)])
    ).

Definition nffgen (n:nat) (f:SymbolString->bool) (g:Grammar) (s1:Symbol) (s2:Symbol): list SymbolString :=
  undup (flatten [seq (nffgen' i f g s1 s2) | i<- (List.seq 1 n)]). 

Fixpoint lincheck' (nts:NonTerminalSymbol) (w:SymbolString): bool :=
(List.length 
  (filter 
    (fun x => x \in nts) 
    (str_to_chars w)
  )
)<2.

Fixpoint list_logical_and (l:seq bool) : bool :=
match l with
| [::] => true
| h::t =>
  if h==true then (list_logical_and t)
  else false
end.

Fixpoint lincheck (g:Grammar) : bool :=
  let ' (ts, nts, rs, s0):=g in
    list_logical_and 
    (map 
      (fun x => let ' (c,s):=x in (lincheck' nts s))
      rs
    ).

Fixpoint lpart (n:NonTerminalSymbol) (w:SymbolString): SymbolString :=
match w with
| EmptyString => EmptyString
| String h t  => if (h \in n) then EmptyString 
                 else String h (lpart n t)
end.

Fixpoint rpart (n:NonTerminalSymbol) (w:SymbolString): SymbolString :=
match w with
| EmptyString => EmptyString
| String h t  => if (h \in n) then t 
                 else (rpart n t)
end.

Fixpoint jth_n (nts:NonTerminalSymbol) (h:Symbol):nat :=
match nts with
|[::] => 0
| hn::tn => if (h==hn) then 1
            else  (jth_n tn h) + 1
end.

Fixpoint jpart (nts:NonTerminalSymbol) (w:SymbolString): nat :=
match w with
| EmptyString => 0
| String h t  =>
  if (h \in nts) then (jth_n nts h)
  else (jpart nts t)
end.

Fixpoint g_flanguage' (n:nat) (f:SymbolString->bool) (g:Grammar):list SymbolString :=
let ' (ts, nts, rs, s0) := g in
  (filter 
    (TerminalQ ts)
    (nfstep f n (g_onestep' rs) [:: (chars_to_str [::s0])])
  ).

Fixpoint g_flanguage (n:nat) (f:SymbolString->bool) (g:Grammar):list SymbolString :=
  undup(
    flatten [seq (g_flanguage' i f g) | i<- (List.seq 1 n)]
  ).
