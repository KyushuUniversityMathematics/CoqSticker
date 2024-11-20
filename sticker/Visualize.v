
From mathcomp Require Import all_ssreflect.
Require Import AutomatonModule StickerModule String Ascii Ex.

Open Scope string_scope.


Fixpoint SymbolString{symbol:finType}(f:symbol->ascii)(s:seq symbol):=
match s with
|nil => ""
|h::s' => String(f h)(SymbolString f s')
end.

Definition EndVisualize{symbol:finType}(f:symbol->ascii)(x:@stickyend symbol):=
match is_upper x with
|true => "\begin{pmatrix}"++SymbolString f(end_str x)++"\\\lambda\end{pmatrix}"
|false => "\begin{pmatrix}\lambda\\"++SymbolString f(end_str x)++"\end{pmatrix}"
end.
Definition WkVisualize{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)(x:@wk symbol rho):=
"\begin{pmatrix}"++SymbolString f(unzip1(str x))++"\\"++SymbolString f(unzip2(str x))++"\end{pmatrix}".

Definition DominoVisualize{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)
(x:@domino symbol rho):string :=
match x with
|null => "\begin{pmatrix}\lambda\\\lambda\end{pmatrix}"
|Simplex s => EndVisualize f s
|WK w => WkVisualize f w
|L s w => EndVisualize f s ++ WkVisualize f w
|R w s => WkVisualize f w++ EndVisualize f s
|LR l w r => EndVisualize f l ++ WkVisualize f w ++ EndVisualize f r
end.

Fixpoint DominoVisualize'{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)
(s:seq(@domino symbol rho)):string:=
match s with
|nil => ""
|x::s' => (DominoVisualize f x)++"//"++(DominoVisualize' f s')
end.
Definition DominoPairVisualize{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)(x:(@domino symbol rho)*(@domino symbol rho)):=
let (l,r):= x in "\left("++DominoVisualize f l ++ DominoVisualize f r++"\right)".
Fixpoint DominoPairVisualize'{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)
(s:seq((@domino symbol rho)*(@domino symbol rho))):string:=
match s with
|nil => ""
|x::s' => (DominoPairVisualize f x)++"//"++(DominoPairVisualize' f s')
end.
Definition abAscii(x:ab):ascii:=match x with|a=>"A"|b=>"B"end.


Definition StickerVisualize{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)
(s:@sticker symbol rho):string :=
DominoVisualize' f (start s) ++"\\\\"++DominoPairVisualize' f(extend s).


Compute (Aut_to_Stk mp).
Compute mp.
Compute StickerVisualize abAscii(Aut_to_Stk mp).
Compute DominoVisualize abAscii(WK(mkwkzip a[::b;a;a;b])).
Definition s:sticker := Sticker ab_finType (zip (enum ab_finType)(enum ab_finType)) [::(WK(mkwkzip a[::b;a;a;b]))] [::((WK(mkwkzip a[::b;a;a;b])),(WK(mkwkzip a[::b;a;a;b])))] erefl.
Compute StickerVisualize abAscii s.
Compute enum bool_finType. (*=[::true;false]と本来は表示されるはず*)


