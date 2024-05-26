(***************************************************************************)
(* Coq Modules for Automata and Sticker Systems                            *)
(* Hisaharu Tanaka, Issei sakashita, Shuichi Inokuchi, Yoshihiro Mizoguchi *)
(*                                                                         *)
(* Yoshihiro Mizoguchi ( ym@imi.kyushu-u.ac.jp )                           *)
(* Institute of Mathematics for Industry, Kyushu University 2014.01.29     *)
(***************************************************************************)

(* StickerModule.v *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

Require Import Ascii String List.

Require Import AutomatonModule.

Close Scope nat_scope.

Definition Domino := (SymbolString * SymbolString * nat * nat).
Definition Rho := list (Symbol * Symbol).
Definition Lrset := list (Symbol * Symbol).
Definition Sticker := ( list Symbol * Rho * list Domino * list (Domino * Domino)). 

Open Scope nat_scope.

Fixpoint lru (s:string) (s0:string) (x:nat) (y:nat):Lrset:=
match s with
  | ""%string => 
  match s0 with
    | ""%string => [::]
    | String _ _ => [::]
  end
  | String f f1 =>
  match s0 with
    | ""%string => [::]
    | String e e1 =>
      if x > 0%nat
      then lru f1 (String e e1) (x-1) y
      else      
      if x == 0
      then (f,e)::(lru f1 e1 0 y)
      else [::]
   end
end.

Fixpoint lrl (s:string) (s0:string) (x:nat) (y:nat):Lrset:=
match s with
  | ""%string => 
  match s0 with
    | ""%string => [::]
    | String _ _ => [::]
  end
  | String f f1 =>
  match s0 with
    | ""%string => [::]
    | String e e1 =>
      if y > 0
      then lrl (String f f1) e1 x (y-1)
      else      
      if y == 0
      then (f,e)::(lrl f1 e1 x 0)
      else [::]
   end
end.

Definition lr  (d:Domino): Lrset :=
match d with
  | (s,s0,x,0) => lru s s0 x 0
  | (s,s0,0,y) => lrl s s0 0 y
  |_ => [::]
end.

Close Scope nat_scope.

Fixpoint lr_membermember (a:Lrset) (b:Lrset):Lrset:=
match b with
  |[::] => [::]
  |(b1::b0) =>
  if  (b1 \in a)
  then b1::lr_membermember a b0
  else lr_membermember a b0
end.

Definition lr_pmember (rho:Rho) (d:Domino):Lrset :=
lr_membermember rho (lr d).

Definition lrcheck (rho:Rho) (d:Domino) :bool :=
if length (lr d) == length (lr_pmember rho d)
then true
else false. 

Open Scope string_scope.

Definition wk (d:Domino) : bool :=
match d with
  |(s,s0,0%nat,0%nat) =>
  if (String.length s) == (String.length s0)
  then true
  else false
  |_ => false
end.

Open Scope nat_scope.

Definition mu (rho:Rho) (d1:Domino) (d2:Domino): list Domino :=
match d1 with
  |(l1,r1,x1,y1) =>
  match d2 with
    |(l2,r2,x2,y2) => 
    if (x1 + y2 + (String.length r1)) ==   (x2 + y1 + (String.length l1))
    then 
       if lrcheck rho ((l1 ++ l2),(r1 ++ r2), x1, y1)
       then [:: ((l1 ++ l2), (r1 ++ r2), x1, y1)]
       else [::]
    else [::]
  end
end.


Definition mu' (rho:Rho) (rr:Domino*Domino) (d:Domino) : list Domino :=
let ' (l,r) := rr in
undup((mu rho l d) ++ (mu rho d r)).

Fixpoint ss_onestep (rho:Rho) (rr:list (Domino*Domino)) (d:Domino) : list Domino :=
match rr with
  | [::] => [::]
  | rr0::rr1 => undup((mu' rho rr0 d) ++ (ss_onestep rho rr1 d))
end.

Definition ss_generate (n:nat) (stk:Sticker) : list Domino :=
let ' (s,rho,a,r) := stk in
 (nstep n (ss_onestep rho r)) a.

Definition ss_language_f (d:Domino) : SymbolString :=
let ' (x,y,i,j) := d in
x.

Definition ss_language (n:nat) (stk:Sticker) : list SymbolString :=
map ss_language_f (filter wk (ss_generate n stk)).

