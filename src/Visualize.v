From mathcomp Require Import all_ssreflect.
Require Import AutomatonModule StickerModule String Ascii Ex.

Open Scope string_scope.


Fixpoint SymbolString{symbol:finType}(f:symbol->ascii)(s:seq symbol):=
match s with
|nil => ""
|h::s' => String(f h)(SymbolString f s')
end.

Definition DominoVisualize{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)
(x:@domino symbol rho):string :=
match x with
|null => "\begin{pmatrix}\lambda\\\lambda\end{pmatrix}"
|Simplex (Se true w _) => "\begin{pmatrix}"++SymbolString f w++"\\\lambda\end{pmatrix}"
|Simplex (Se false w _) => "\begin{pmatrix}\lambda\\"++SymbolString f w++"\end{pmatrix}"
|WK (Wk w _ _) => "\begin{pmatrix}"++SymbolString f(unzip1 w)++"\\"++SymbolString f(unzip2 w)++"\end{pmatrix}"
|_ => ""
end.

Fixpoint DominoVisualize'{symbol:finType}{rho:Rho symbol}(f:symbol->ascii)
(s:seq(@domino symbol rho)):string:=
match s with
|nil => ""
|x::s' => (DominoVisualize f x)++"//"++(DominoVisualize' f s')
end.
Definition abAscii(x:ab):ascii:=match x with|a=>"A"|b=>"B"end.

Definition StickerVisualize{symbol:finType}{rho:Rho symbol}
(s:@sticker symbol rho):String :=



