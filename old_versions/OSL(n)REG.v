From mathcomp Require Import all_ssreflect.

Require Import Ascii String Bool ListSet.
Require Import AutomatonModule StickerModule GrammarModule4.
Close Scope nat_scope.

Definition fst {a:Type} (p:a*a):a :=
match p with
|pair p1 _ => p1
end.
Definition snd {a:Type} (p:a*a):a :=
match p with
|pair _ p2 => p2
end.
Definition hd {a:Type} (default:a)(l:list a):a :=
match l with
|nil => default
|h::l' => h
end.

Close Scope nat_scope.
Definition Domino' := (string*string)*(string*string)*(string*string).
Definition ascii' := string*string.
Open Scope nat_scope.

Fixpoint generate_str' (s t:string):list ascii' :=
match s,t with
|String h1 s',String h2 t' => (String h1 "",String h2 "")::(generate_str' s' t')
|_,_ => nil
end.
Notation "s & t" := (generate_str' s t) (at level 1).

Definition N:NonTerminalSymbol ascii' := [::("l","l");("r","r");("s","s")].
Definition T:TerminalSymbol ascii' := [::("A","A");("B","B")].
Definition rule1:Rule ascii' := (("s","s"),"lBr"&"lBr").
Definition rule2:Rule ascii' := (("r","r"),"ABr"&"ABr").
Definition rule3:Rule ascii' := (("l","l"),nil).
Definition rule4:Rule ascii' := (("r","r"),nil).
Definition R:RuleSet ascii' := [::rule1;rule2;rule3;rule4].
Definition s:StartSymbol ascii' := ("s","s").
Definition g1:Grammar ascii' := (T,N,R,s).
Definition g2:Grammar nat := ([::1],[::0],[::(0,[::0;1]);(0,[::1;0]);(0,[::1])],0).
Compute g_language 8 g2.
Fixpoint string_of_list_ascii' (s : list ascii') : string*string :=
match s with
|nil => ("","")
|(ch1,ch2)::s =>
  let (s',t') := (string_of_list_ascii' s) in
  (ch1++s',ch2++t')
end.
Definition g_gen (n:nat)(g:Grammar ascii'):list (string*string):=
map string_of_list_ascii' (g_language n g).
Compute g_gen 10 g1.


Fixpoint language (n:nat)(V:list Symbol):list SymbolString :=
(*n文字の文字列を生成 Ex:language 2 [::"a"%char;"b"%char] -> [::"aa";"ab";"ba;";"bb"]*)
match n with
|0 => [::""]
|S n' => flatten [seq (map (String v) (language n' V))| v <- V]
end.
Compute language 3 [::"a"%char;"b"%char].
Fixpoint language' (n:nat)(V:list Symbol):list SymbolString :=
(*1文字以上n文字以下の文字列を生成*)
match n with
|0 => nil
|S n' => app (language' n' V) (language n V)
end.
Compute language' 3 [::"a"%char;"b"%char].
Fixpoint articulation (n:nat)(a:ascii):string :=
match n with
|0 => ""
|S n' => String a (articulation n' a)
end.
Compute articulation 7 "f"%char.
Notation "a # n" := (articulation n a) (at level 1).

Definition Domino2Domino' (d:Domino):Domino' :=
let ' (s, t, x, y):=d in
let l := max x y in
let m := min ((length s)-x) ((length t)-y) in
let r := (max ((length s)-x) ((length t)-y))-m in
let s' := "l"#y ++ s ++ "r"#r in
let t' := "l"#x ++ t ++ "r"#r in
((substring 0 l s',substring 0 l t'),
 (substring l m s',substring l m t'),
 (substring (m+l) r s',substring (m+l) r t')).
Compute Domino2Domino' ("atgc","cta",0,1).
Definition Domino'2Domino (D:Domino'):Domino :=
let ' ((s1,t1),(s2,t2),(s3,t3)) := D in
match s1 with
|String "l" _ =>
  match s3 with
  |String "r" _ => (s2,t1++t2++t3,0,length s1)
  |_ => (s2++s3,t1++t2,0,length s1)
  end
|_ =>
  match s3 with
  |String "r" _ => (s1++s2,t2++t3,length s1,0)
  |_ => (s1++s2++s3,t2,length s1,0)
  end
end.

Definition Domino'2str' (D:Domino'):list ascii' :=
let ' (d1,(s1,s2),d3) := D in
if d1 == ("","") then
  if d3 == ("","") then
    s1&s2
  else
    app s1&s2 [::d3]
else
  if d3 == ("","") then
    d1::(s1&s2)
  else
    app (d1::(s1&s2)) [::d3].
Fixpoint max_stick (A:list Domino'):nat :=
(*指定したドミノ列の中で最長の粘着末端の長さ*)
match A with
|nil => 0
|h::A' =>
  let ' ((s1,t1),(s2,t2),(s3,t3)) := h in
  max (max (length s1) (length s3)) (max_stick A')
end.
Definition convert_n (V:list Symbol)(A:list Domino'):NonTerminalSymbol ascii':=
(*非終端文字*)
let U := language' (max_stick A) V in
app [::("l","l");("r","r");("s","s")]
  (app [seq (u,"l"#(length u))|u <- U]
    (app [seq ("l"#(length u),u)|u <- U]
      (app [seq (u,"r"#(length u))|u <- U]
        [seq ("r"#(length u),u)|u <- U]))).
Fixpoint convert_t (rho:list (Symbol * Symbol)):TerminalSymbol ascii':=
(*終端文字*)
match rho with
|nil => nil
|h::rho' =>
  let (a, b):= h in
  (String a "",String b "")::(convert_t rho')
end.

Fixpoint convert_rule_right (N:NonTerminalSymbol ascii')(rho:Rho)(D:Domino):RuleSet ascii':=
let ' (s,t,x,y) := D in
match N with
|nil => nil
|("r","r")::N' =>
  if (x==0)&&(y==0) then
    if (y+(length s))==(x+(length t)) then
      (("r","r"),Domino'2str' (Domino2Domino' (s++"r",t++"r",x,y)))::convert_rule_right N' rho D
    else
      (("r","r"),Domino'2str' (Domino2Domino' D))::convert_rule_right N' rho D
  else
    convert_rule_right N' rho D
|(String "r" r,u)::N' =>
  let ' (s',t',x',y') := hd ("","",1,1) (mu rho ("",u,0,0) D) in
  if (x'==0)&&(y'==0) then
    if (y'+(length s'))==(x'+(length t')) then
      ((String "r" r,u),Domino'2str' (Domino2Domino' (s'++"r",t'++"r",x',y')))::convert_rule_right N' rho D
    else
      ((String "r" r,u),Domino'2str' (Domino2Domino' (s',t',x',y')))::convert_rule_right N' rho D
  else
    convert_rule_right N' rho D
|(u,String "r" r)::N' =>
  let ' (s',t',x',y') := hd ("","",1,1) (mu rho (u,"",0,0) D) in
  if (x'==0)&&(y'==0) then
    if (y'+(length s'))==(x'+(length t')) then
      ((u,String "r" r),Domino'2str' (Domino2Domino' (s'++"r",t'++"r",x',y')))::convert_rule_right N' rho D
    else
      ((u,String "r" r),Domino'2str' (Domino2Domino' (s',t',x',y')))::convert_rule_right N' rho D
  else
    convert_rule_right N' rho D
|_::N' => convert_rule_right N' rho D
end.
Compute mu [::("a"%char,"a"%char)]("aaa","",3,0) ("a","aaaa",0,3).
Fixpoint convert_rule_left (N:NonTerminalSymbol ascii')(rho:Rho)(D:Domino):RuleSet ascii':=
let ' (s,t,x,y) := D in
match N with
|nil => nil
|("l","l")::N' =>
  if (y+(length s))==(x+(length t)) then
    if x==y then
      (("l","l"),Domino'2str' (Domino2Domino' ("l"++s,"l"++t,x,y)))::convert_rule_left N' rho D
    else
      (("l","l"),Domino'2str' (Domino2Domino' D))::convert_rule_left N' rho D
  else
    convert_rule_left N' rho D
|(String "l" l,u)::N' =>
  let ' (s',t',x',y') := hd ("","",1,1) (mu rho D ("",u,0,length u)) in
  if (y'+(length s'))==(x'+(length t')) then
    if x'==y' then
      ((String "l" l,u),Domino'2str' (Domino2Domino' ("l"++s',"l"++t',x',y')))::convert_rule_left N' rho D
    else
      ((String "l" l,u),Domino'2str' (Domino2Domino' (s',t',x',y')))::convert_rule_left N' rho D
  else
    convert_rule_left N' rho D
|(u,String "l" l)::N' =>
  let ' (s',t',x',y') := hd ("","",1,1) (mu rho D (u,"",0,length u)) in
  if (y'+(length s'))==(x'+(length t')) then
    if x'==y' then
      ((u,String "l" l),Domino'2str' (Domino2Domino' ("l"++s',"l"++t',x',y')))::convert_rule_left N' rho D
    else
      ((u,String "l" l),Domino'2str' (Domino2Domino' (s',t',x',y')))::convert_rule_left N' rho D
  else
    convert_rule_left N' rho D
|_::N' => convert_rule_left N' rho D
end.
Fixpoint convert_rule_start (A:list Domino'):RuleSet ascii' :=
match A with
|nil => [::(("r","r"),""&"");(("l","l"),""&"")]
|(("",""),(s,t),("",""))::A' => (("s","s"),("l"++s++"r")&("l"++t++"r"))::(convert_rule_start A')
|(("",""),(s2,t2),(s3,t3))::A' => (("s","s"),("l"++s2++s3)&("l"++t2++t3))::(convert_rule_start A')
|(asc',(s2,t2),("",""))::A' => (("s","s"),asc'::((s2++"r")&(t2++"r")))::(convert_rule_start A')
|a::A' => (("s","s"),(Domino'2str' a))::(convert_rule_start A')
end.
Fixpoint convert_rule (N:NonTerminalSymbol ascii')(rho:Rho)(A:list Domino')(D:list (Domino*Domino)):RuleSet ascii':=
match D with
|nil => convert_rule_start A
|(("","",0,0),d)::D' => app (convert_rule_right N rho d) (convert_rule N rho A D')
|(d,("","",0,0))::D' => app (convert_rule_left N rho d) (convert_rule N rho A D')
|_ => nil
end. 

Definition Sticker_to_Grammar (S:Sticker):Grammar ascii':=
let ' (V, rho, A, D) := S in
let A' := map Domino2Domino' A in
let D_left := map Domino2Domino' (map fst D) in
let D_right := map Domino2Domino' (map snd D) in
let ' n := convert_n V (app A' (app D_left D_right)) in
let ' t := convert_t rho in
let ' r := convert_rule n rho A' D in
(t, n, r, ("s","s")).

Definition stk1:Sticker := ([::"A"%char;"B"%char],[::("A"%char,"A"%char);("B"%char,"B"%char)],[::("B","B",0,0)],[::(("","",0,0),("AB","AB",0,0))]).
Compute Sticker_to_Grammar stk1.

Definition stk2:Sticker := ([::"A"%char;"B"%char;"C"%char],[::("A"%char,"A"%char);("B"%char,"B"%char);("C"%char,"C"%char)],[::("AB","CA",0,1)],[::(("C","",0,0),("","",0,0));(("","",0,0),("","BB",0,1));(("","",0,0),("BB","",1,0));(("","",0,0),("BC","",1,0));(("","",0,0),("","CC",0,1));(("","",0,0),("CC","",1,0));(("","",0,0),("C","",1,0))]).
(*CAB^{2n}C^m, n,mは1以上　となる文字列を生成すスティッカー*)
Compute ss_language 10 stk2.
Definition V := [::"A"%char;"B"%char].
Definition rho := [::("A"%char,"A"%char);("B"%char,"B"%char)].
Definition A := [::("BA","B",0,0)].
Definition D := [::(("","",0,0),("BA","AB",0,1));
                   (("","",0,0),("B","AB",0,1))].
Definition stk3 := (V,rho,A,D).
Compute Sticker_to_Grammar stk2.
Compute g_generate 3 (Sticker_to_Grammar stk2).
Compute g_gen 10 (Sticker_to_Grammar stk2).
Definition g3 := Sticker_to_Grammar stk1.
Definition isequal (g1 g2:Grammar ascii'):list bool :=
let ' (N1,T1,r1,s1) := g1 in
let ' (N2,T2,r2,s2) := g2 in
[::N1==N2;T1==T2;r1==r2;s1==s2].















