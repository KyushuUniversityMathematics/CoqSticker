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
Open Scope string_scope.
Fixpoint remove_head (n:nat)(s:string):string :=
match n,s with
|0,_ => s
|S n',String h s' => remove_head n' s'
|_,_ => ""
end.
Fixpoint lrcheck' (rho:Rho)(s t:string):bool :=
match s,t with
|"",_ => true
|_,"" => true
|String hs s',String ht t' => ((hs,ht)\in rho)&&(lrcheck' rho s' t')
end.
Definition lrcheck (rho:Rho)(d:Domino):bool :=
let ' (s,t,x,y) := d in
let s' := remove_head x s in
let t' := remove_head y t in
lrcheck' rho s' t'.

Definition wk (d:Domino) : bool :=
let ' (s,t,x,y) := d in
(x==0)&&(y==0)&&((String.length s)==(String.length t)).


Open Scope nat_scope.

Definition mu (rho:Rho) (d1:Domino) (d2:Domino): list Domino :=
let ' (l1,r1,x1,y1) := d1 in
let ' (l2,r2,x2,y2) := d2 in
if (x1 + y2 + (String.length r1)) == (x2 + y1 + (String.length l1)) then 
  if lrcheck rho ((l1 ++ l2),(r1 ++ r2), x1, y1) then
    [:: ((l1 ++ l2), (r1 ++ r2), x1, y1)]
  else [::]
else [::].


Definition mu' (rho:Rho) (rr:Domino*Domino) (d:Domino) : list Domino :=
let ' (l,r) := rr in
if (mu rho l d) == nil then
  [::d]
else
  if (mu rho d r) == nil then
    [::d]
  else
    d::(flatten [seq mu rho d' r|d' <- mu rho l d]).

Fixpoint ss_onestep (rho:Rho) (rr:list (Domino*Domino)) (d:Domino) : list Domino :=
match rr with
  | [::] => [::d]
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
