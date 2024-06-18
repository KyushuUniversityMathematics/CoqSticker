(***************************************************************************)
(* Coq Modules for Automata and Sticker Systems                            *)
(* Hisaharu Tanaka, Issei sakashita, Shuichi Inokuchi, Yoshihiro Mizoguchi *)
(*                                                                         *)
(* Yoshihiro Mizoguchi ( ym@imi.kyushu-u.ac.jp )                           *)
(* Institute of Mathematics for Industry, Kyushu University 2014.01.29     *)
(***************************************************************************)

(* AutomatonModule.v *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq
               choice fintype.

Require Import Ascii String.

Open Scope nat_scope.

Definition eq_string a b :=
  match string_dec a b with left _ => true | _ => false end.

Lemma eq_stringP : Equality.axiom eq_string.
Proof. move=> ??; apply: (iffP idP); rewrite /eq_string; by case: string_dec. Qed.

Canonical string_eqMixin := EqMixin eq_stringP.
Canonical string_eqType := Eval hnf in EqType _ string_eqMixin.

Definition eq_ascii a b :=
  match ascii_dec a b with left _ => true | _ => false end.

Lemma eq_asciiP : Equality.axiom eq_ascii.
Proof. move=> ??; apply: (iffP idP); rewrite /eq_ascii; by case: ascii_dec. Qed.

Canonical ascii_eqMixin := EqMixin eq_asciiP.
Canonical ascii_eqType := Eval hnf in EqType _ ascii_eqMixin.

Fixpoint str_to_chars (s:string) :(list ascii):=
match s with
|EmptyString => [::]
|String a s' => (a::(str_to_chars s'))
end.

Fixpoint chars_to_str (l:list ascii): string:=
match l with
| [::]   => ""%string
| (x::y) => String x (chars_to_str y)
end.

Fixpoint sstar {a:eqType} (n:nat) (s:seq a):seq (seq a) := 
if n is m.+1 then
if s is h :: tl then
   [:: [::]] ++ (undup (flatten [seq [seq [:: x] ++ w | w <- (sstar m s)]|x <- s ]))
else[::]
else[::].

Fixpoint sigman' {a:eqType} (s:seq a) (n:nat):seq (seq a) :=
if n is m.+1 then
   undup (flatten [seq [seq [:: x] ++ w | w <- (sigman' s m)]|x <- s ]) 
else [::[::]].

Definition sigman (s:seq ascii_eqType) (n:nat):seq string :=
   map chars_to_str (sigman' s n). 

Fixpoint sigmann (s:seq ascii_eqType) (n:nat):seq string :=
if n is m.+1 then
   (sigmann s m) ++ (sigman s n)
else [::].

Fixpoint star {a:eqType} (n:nat) (s:seq (seq a)):seq (seq  a) :=
if n is m.+1 then
    [:: [::]] ++ (undup (flatten [seq [seq x ++ w | w <- (star m s)]|x <- s ]))
else[::].

Close Scope nat_scope.
Definition State := nat.
Definition States := seq State.
Definition Symbol := ascii.
Definition Symbols := list Symbol.
Definition SymbolString := string.
Definition SymbolStrings := list string.

Definition Automaton := (States * Symbols * (State->Symbol->State) * State * States).

Fixpoint dstar (d:State -> Symbol -> State) (s:State) (ss:SymbolString):State :=
if ss is (String a x) then
      dstar d (d s a) x
else s.
Fixpoint Vword (s:string)(V:Symbols):bool :=
match s with
|EmptyString => true
|String h s' => (h \in V)&&(Vword s' V)
end.

Definition accept (m:Automaton) (w:SymbolString): bool :=
let ' (q, s, d, s0, f):=m in (Vword w s)&&((dstar d s0 w) \in f).

Definition accepts (m:Automaton) (ss:SymbolStrings): SymbolStrings :=
(filter (accept m) ss).

Definition power {a:eqType} {b:eqType} (f:(a -> (seq b))) (s:seq a):seq b:=
(undup (flatten (map f s))).

Open Scope nat_scope.
Fixpoint nstep {a:eqType} (n:nat) (f:(a->(seq a))) (s:seq a):seq a:=
match n with
|0 => s
|S p => (power f) (nstep p f s)
end.

Definition nfstep {a:eqType} (fp:(a->bool)) (n:nat)
  (f:(a->(seq a))) (s:seq a):seq a:=
match n with
|0 => [::]
|1 => filter fp ((power f) s)
|S p => filter fp ((power f) (nstep p f s))
end.

Fixpoint delta_collect (s:State)(n:nat)(K:States)(V:Symbols)
(delta:State->Symbol->State):bool :=
let a := ascii_of_nat n in
let b := ((a \in V) == ((delta s a)\in K)) in
match n with
|0 => b
|S n' => b&&(delta_collect s n' K V delta)
end.
Fixpoint delta_collectK (K K1:States)(V:Symbols)(delta:State->Symbol->State)
:bool :=
match K1 with
|nil => true
|s::K1' => (delta_collect s 255 K V delta)&&(delta_collectK K K1' V delta)
end.
