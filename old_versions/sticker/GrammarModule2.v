(***************************************************************************)
(* Coq Modules for Automata and Sticker Systems                            *)
(* Hisaharu Tanaka, Issei sakashita, Shuichi Inokuchi, Yoshihiro Mizoguchi *)
(*                                                                         *)
(* Yoshihiro Mizoguchi ( ym@imi.kyushu-u.ac.jp )                           *)
(* Institute of Mathematics for Industry, Kyushu University 2014.01.29     *)
(***************************************************************************)

(* GrammarModule2.v *)

From mathcomp Require Import all_ssreflect.

Require Import Ascii String Bool ListSet.
Require Import AutomatonModule StickerModule.

Close Scope nat_scope.

Definition ascii' := ascii * ascii.
Definition string' := string * string.
Definition String' (a:ascii')(s:string') :=
let (a1,a2) := a in
let (s1,s2) := s in
(String a1 s1,String a2 s2).
Definition append' (s t:string'):string':=
let (s1,s2) := s in
let (t1,t2) := t in
(s1 ++ t1, s2 ++ t2).
Notation "A ++' B" := (append' A B)(at level 50).
Definition St (a:ascii')(s:string') : string' :=
let ' (a1,a2) := a in
let ' (s1,s2) := s in
(String a1 s1,String a2 s2).
Definition a := ("askdj","odfkp").
Definition head' (s:string') : string' :=
match s with
|("","") => ("","")
|(String a1 s1,String a2 s2) =>(s1,s2)
|_ => ("","")
end.


Definition Rule := ascii' * string'.
Definition RuleSet := list Rule.
Definition StartSymbol := ascii'.
Definition TerminalSymbol :=list ascii'.
Definition NonTerminalSymbol := list ascii'.
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
Definition string'_inQ (a:ascii') (s:string'):bool :=
let (a1,a2) := a in
let (s1,s2) := s in
(string_inQ a1 s1) && (string_inQ a2 s2).

Fixpoint TerminalQ' (ts:TerminalSymbol) (s:string'):bool := 
match ts with
| nil => false
| h::ts' =>
  if (string'_inQ h s)
    then true
    else TerminalQ' ts' s
end.

Fixpoint __g'_onestep (l:ascii')(r1 r2 s1 s2:string) : list string' :=
match s1 with
|"" => [::]
|String h1 s1' =>
  match s2 with
  |"" => [::]
  |String h2 s2' =>
    if (l == (h1,h2))
      then undup (app (map (String' (h1,h2)) (__g'_onestep l r1 r2 s1' s2')) [::append' (r1,r2) (s1',s2')])
      else undup (map (String' (h1,h2)) (__g'_onestep l r1 r2 s1' s2'))
  end
end.
Definition g'_onestep (s:string') (rl:Rule) :list string' :=
let ' (l,(r1,r2)) := rl in
let (s1,s2) := s in
__g'_onestep l r1 r2 s1 s2.

Definition g'_onestep' (rs:RuleSet) (s:string') : seq string' :=
undup(flatten(map (g'_onestep s) rs)).



Definition g'_generate' (n:nat) (g:Grammar) : seq string' :=
let ' (ts, nts, rs, s0) := g in 
  nstep n (g'_onestep' rs) [:: (String' s0 ("",""))].

Definition g'_generate (n:nat) (g:Grammar) : list string' :=
  undup (flatten [seq (g'_generate' i g) | i<- (List.seq 1 n)]).

Definition g'_language' (n:nat) (g:Grammar) : list string' :=
let ' (ts, nts, rs, s0) := g in
  (filter 
    (TerminalQ' ts)
    (g'_generate n g)
  ).

Definition g'_language (n:nat) (g:Grammar) : list string' :=
  undup (flatten [seq (g'_language' i g) | i<- (List.seq 1 n)]).

Definition nfstep {a:eqType} (fp:(a->bool)) (n:nat)
  (f:(a->(seq a))) (s:seq a):seq a:=
match n with
|0 => [::]
|1 => filter fp ((power f) s)
|S p => filter fp ((power f) (nstep p f s))
end.
(*
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
  ).*)
