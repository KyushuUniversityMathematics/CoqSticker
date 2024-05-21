(***************************************************************************)
(* Coq Modules for Automata and Sticker Systems                            *)
(* Hisaharu Tanaka, Issei sakashita, Shuichi Inokuchi, Yoshihiro Mizoguchi *)
(*                                                                         *)
(* Yoshihiro Mizoguchi ( ym@imi.kyushu-u.ac.jp )                           *)
(* Institute of Mathematics for Industry, Kyushu University 2014.01.29     *)
(***************************************************************************)

(* AutomatonEx.v *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq
               choice fintype.

Require Import Ascii String.
From sticker Require Import AutomatonModule.

Open Scope nat_scope.
Definition m1_d : State->Symbol->State :=
fun q x =>
match q with
  | 0 =>
    match x with
      | "a"%char => 0
      | "b"%char => 1
      | _ => 999
    end
  | 1 => 
    match x with
      | "a"%char => 1
      | "b"%char => 0
      | _ => 999
    end
  | _ => 999
end.

Definition m1: Automaton:=
([:: 0;1], [:: "a"%char;"b"%char], m1_d, 0, [:: 1]).

Definition m2_d : State->Symbol->State :=
fun q x =>
match q with
  | 0 =>
    match x with
      | "a"%char => 1
      | "b"%char => 2
      | _ => 999
    end
  | 1 => 
    match x with
      | "a"%char => 2
      | "b"%char => 0
      | _ => 999
    end
  | 2 =>
    match x with
      | "a"%char => 2
      | "b"%char => 2
      | _ => 999
    end
  | _ => 999
end.

Definition m2: Automaton:=
([:: 0;1;2], [:: "a"%char;"b"%char], m2_d, 0, [:: 1]).

