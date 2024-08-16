(***************************************************************************)
(* Coq Modules for Automata and Sticker Systems                            *)
(* Hisaharu Tanaka, Issei sakashita, Shuichi Inokuchi, Yoshihiro Mizoguchi *)
(*                                                                         *)
(* Yoshihiro Mizoguchi ( ym@imi.kyushu-u.ac.jp )                           *)
(* Institute of Mathematics for Industry, Kyushu University 2014.01.29     *)
(***************************************************************************)

(* StickerModule.v *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

Require Import Ascii List String.

Require Import AutomatonModule.

Close Scope nat_scope.

Definition Domino := (SymbolString * SymbolString * nat * nat).
Definition Rho := list (Symbol * Symbol).
Definition Lrset := list (Symbol * Symbol).
Definition Sticker := ( list Symbol * Rho * list Domino * list (Domino * Domino)). 

Open Scope nat_scope.
Open Scope string_scope.
Fixpoint lrcheck' (rho:Rho)(s t:string):bool :=
match s,t with
|"",_ => true
|_,"" => true
|String hs s',String ht t' => ((hs,ht)\in rho)&&(lrcheck' rho s' t')
end.
Definition lrcheck (rho:Rho)(d:Domino):bool :=
let ' (s,t,x,y) := d in
let s' := substring x (length s) s in
let t' := substring y (length t) t in
lrcheck' rho s' t'.

Definition wk (rho:Rho)(d:Domino) : bool :=
let ' (s,t,x,y) := d in
(x==0)&&(y==0)&&((length s)==(length t))&&(lrcheck rho d).


Open Scope nat_scope.

Definition mu (rho:Rho) (d1:Domino) (d2:Domino): list Domino :=
match d1,d2 with
|("",r1,_,_),(l2,r2,x2,y2) => filter (lrcheck rho) [::(l2,r1++r2,max 0 (x2 - y2 - (length r1)),max 0 (length r1 + y2 - x2))]
|(l1,"",_,_),(l2,r2,x2,y2) => filter (lrcheck rho) [::(l1++l2,r2,max 0 (x2 - y2 + (length l1)),max 0 (y2 - x2 - (length l1)))]
|(l1,r1,x1,y1),("",r2,_,_) => filter (lrcheck rho) [::(l1,r1++r2,x1,y1)]
|(l1,r1,x1,y1),(l2,"",_,_) => filter (lrcheck rho) [::(l1++l2,r1,x1,y1)]
|(l1,r1,x1,y1),(l2,r2,x2,y2) =>
  if (x1 + y2 + (length r1)) == (x2 + y1 + (length l1)) then 
    filter (lrcheck rho) [:: ((l1 ++ l2), (r1 ++ r2), x1, y1)]
  else [::]
end.


Definition mu' (rho:Rho) (rr:Domino*Domino) (d:Domino) : list Domino :=
let ' (l,r) := rr in
flatten [seq mu rho d' r|d' <- mu rho l d].

Fixpoint ss_generate (n:nat) (stk:Sticker) : list Domino :=
let ' (_,rho,A,D) := stk in
match n with
|0 => A
|S n' => let dmn := ss_generate n' stk in
  undup dmn++(flatten [seq mu' rho rr d|rr <- D,d<-dmn])
end.

Fixpoint ss_generate_prime (n:nat)(stk:Sticker):list Domino :=
let ' (_,rho,A,D) := stk in
match n with
|0 => A
|S n' => let dmn := ss_generate_prime n' stk in
  undup dmn++(flatten [seq mu' rho rr d|rr<-D,d <- [seq d<-dmn|~~ wk rho d]])
end.

Definition ss_language_f (d:Domino) : SymbolString :=
let ' (x,y,i,j) := d in
x.

Definition ss_language (n:nat) (stk:Sticker) : list SymbolString :=
let ' (_,rho,_,_) := stk in
map ss_language_f (filter (wk rho) (ss_generate n stk)).

Definition ss_language_prime (n:nat)(stk:Sticker):list SymbolString :=
let ' (_,rho,_,_) := stk in
[seq ss_language_f d | d <- [seq d <- ss_generate_prime n stk|wk rho d]].