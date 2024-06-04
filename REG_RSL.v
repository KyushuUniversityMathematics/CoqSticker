From mathcomp Require Import all_ssreflect.

Require Import Ascii String Bool ListSet.
Require Import AutomatonModule StickerModule2 ListTheorems.

Fixpoint language (n:nat)(V:list Symbol):list SymbolString :=
(*n文字の文字列を生成 Ex:language 2 [::"a"%char;"b"%char] -> [::"aa";"ab";"ba;";"bb"]*)
match n with
|0 => [::""]
|S n' => flatten [seq (map (String v) (language n' V))| v <- V]
end.
Fixpoint language' (n:nat)(V:list Symbol):list SymbolString :=
(*1文字以上n文字以下の文字列を生成 Ex:language 2 [::"a"%char;"b"%char] -> [::"a";"b";"aa";"ab";"ba;";"bb"]*)
match n with
|0 => [::]
|S n' => app (language' n' V) (language n V)
end.

Fixpoint l_index {e:eqType}(a:e)(l:list e):nat :=
match l with
|nil => 0 - 1
|h::l' =>
  if a == h then
    0
  else
    S (l_index a l')
end.
Fixpoint createDomino (l:list string)(state:State)(M:Automaton):list Domino :=
let ' (K,V,delta,s0,F) := M in
match l with
|nil => nil
|s::l' =>
  let state_num := l_index (dstar delta state s) K in
  (s,substring 0 ((length s)- state_num - 1) s,0,0)::(createDomino l' state M)
end.
Fixpoint convert_D (l1 l2:list string)(M:Automaton):list (Domino*Domino) :=
let ' (K,V,delta,s0,F) := M in
match l2 with
|nil => nil
|s::l2' =>
  let state := List.nth (length s - 1) K s0 in
  app (map (fun d =>let ' (l,r,x,y) := d in (("","",0,0),(l,s++r,x,y+(length s)))) (createDomino l1 state M))
      (convert_D l1 l2' M)
end.
Fixpoint convert_D' (l1 l2:list string)(M:Automaton):list (Domino*Domino) :=
let ' (K,V,delta,s0,F) := M in
match l2 with
|nil => nil
|s::l2' =>
  let state := List.nth (length s - 1) K s0 in
  let X := accepts (K,V,delta,state,F) l1 in
  app [seq (("","",0,0),(x,s++x,0,length s))|x <- X] (convert_D' l1 l2' M)
end.

Definition Aut_to_Stk (M:Automaton):Sticker :=
let ' (K,V,delta,s0,F) := M in
let k := List.length K - 1 in
let l := language (k+2) V in
let A := createDomino l s0 M in
let l' := language' (k+1) V in
let D := convert_D l l' M in
let D' := convert_D' (language' (k+2) V) l' M in
(V,[seq (v,v)|v <- V],app [seq (l',l',0,0)|l' <- accepts M (language' (k+2) V)] A,app D D').
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
Compute dstar m1_d 1 "b".
Definition m1: Automaton:=
([::0;1],[::"a"%char;"b"%char],m1_d, 0,[::1]).
Definition s1 := Aut_to_Stk m1.
Compute accepts m1 (language' 3 [:: "a"%char;"b"%char]).
Compute s1.
Compute ss_language 1 s1.
Definition ss_accept (stk:Sticker) (a:SymbolString):bool:=
a \in (ss_language (length a) stk).


Definition m_length (M:Automaton):nat :=
let ' (K,V,delta,s0,F) := M in
List.length K.
Fixpoint sublist {e:eqType}(l1 l2:list e):bool :=
match l1 with
|nil => true
|h::l1' => (h \in l2)&&(sublist l1' l2)
end.
Compute nstep 5 (fun x=> [::S x]) [::1;2;3].
Compute ss_generate 10 ([::"a"%char],[::("a"%char,"a"%char)],[::("a","a",0,0)],[::(("","",0,0),("a","a",0,0))]).
Compute ss_onestep [::("a"%char,"a"%char)] [::(("","",0,0),("a","a",0,0))] ("a","a",0,0).


Lemma onesteplemma (rho:Rho)(rr:list (Domino*Domino))(d:Domino):d \in ss_onestep rho rr d.
Proof.
elim rr.
simpl.
by rewrite inE.
unfold ss_onestep.
move => a l H.
apply in_undup.
move : in_app.


elim l;simpl.
unfold in_mem;simpl.
unfold ss_onestep.

Lemma ss_generatelemma (n m:nat)(S:Sticker):n <= m -> sublist (ss_generate n S) (ss_generate m S).
Proof.
move => H.
unfold ss_generate.
unfold ss_onestep.
unfold nstep.
Lemma ss_accept_A (V:list Symbol)(rho:list (Symbol*Symbol))(A:list Domino)(D:list (Domino*Domino))(s:string)
:((s,s,0,0)\in A)->ss_accept (V,rho,A,D) s.
Proof.
move => H.
unfold ss_accept.
unfold ss_language.

Proof.
destruct S.
move => H.
Lemma shortstring (M:Automaton)(s:string):accept M s -> (length s <= m_length M) -> (ss_accept (Aut_to_Stk M) s).
Proof.
move => H H'.
destruct Aut_to_Stk.
Theorem REG_RSL (M:Automaton)(s:string):accept M s -> (ss_accept (Aut_to_Stk M) s).
Proof.
split.

elim s.
move => H.

















