(********
忘備メモ
20130712:
具体的な文字列を与えて、それがグラマーから生成される文字列になっているかどうか?
i>j ならば a^ib^jが言語に入っているかどうか
lemmaが証明できるか?


20130709:
tilr
nfgen
nffgen
g_generate
g_language
g_flanguage
は、それそれhaskellのものから変更している。
nfgen'
nffgen'
g_generate'
g_language'
g_flanguage'
が本来haskellに書いてある通りのもの、のはず。
Print LoadPath.
********)


From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq
               choice fintype.
Require Import Ascii String Bool ListSet.
From sticker Require Import AutomatonModule StickerModule  GrammarModule.

(** ** Section 4.3 Examples *)

Open Scope string_scope.

(** gex1の定義 *)
Definition ts1:TerminalSymbol :=  [::"a"%char;"b"%char].
Definition nts1:NonTerminalSymbol :=  [::"S"%char].
Definition rl1_1:Rule := ("S"%char,"aSb"%string).
Definition rl1_2:Rule := ("S"%char,""%string).
Definition rs1:RuleSet := [:: rl1_1;rl1_2].
Definition ss1:StartSymbol := "S"%char.
Definition gex1:Grammar := (ts1, nts1, rs1, ss1).

(** gex2の定義 *)
Definition ts2:TerminalSymbol := [::"a"%char;"b"%char].
Definition nts2:NonTerminalSymbol :=  [::"S"%char;"A"%char].
Definition rl2_1:Rule := ("S"%char,"A"%string).
Definition rl2_2:Rule := ("S"%char,"aSb"%string).
Definition rl2_3:Rule := ("A"%char,"aA"%string).
Definition rl2_4:Rule := ("A"%char,""%string).
Definition rs2:RuleSet := [:: rl2_1;rl2_2;rl2_3;rl2_4].
Definition ss2:StartSymbol := "S"%char.
Definition gex2:Grammar := (ts2, nts2, rs2, ss2).

(** gex3の定義 *)
Definition ts3:TerminalSymbol :=  [::"0"%char;"1"%char;"("%char;")"%char;"+"%char].
Definition nts3:NonTerminalSymbol :=  [::"S"%char].
Definition rl3_1:Rule := ("S"%char,"(S+S)"%string).
Definition rl3_2:Rule := ("S"%char,"0"%string).
Definition rl3_3:Rule := ("S"%char,"1"%string).
Definition rs3:RuleSet := [:: rl3_1;rl3_2;rl3_3].
Definition ss3:StartSymbol := "S"%char.
Definition gex3:Grammar := (ts3, nts3, rs3, ss3).

(** * Section 4.4 Sticker System vs Linear Grammar *)

Fixpoint nth_element (n:nat) (l:seq Symbol) : Symbol :=
  match n, l with
    | O, x :: l => x
    | O, [::] => "E"%char
    | S m, [::] => "E"%char
    | S m, x :: t => nth_element m t 
  end.

Definition tik (n:nat) (g: Grammar) (i k:nat):list SymbolString :=
  let ' (ts,nts,rs,s0):= g in
    [seq w |
      w <- (filter (fun x => ((length x)==k))
      (nfgen n (fun x => ((length x)<=(k+1))) g (nth_element (i-1) nts)))
    ].

Definition tilr' (n:nat) (g: Grammar) (i l r j:nat):list (SymbolString * nat * SymbolString) :=
  let ' (ts,nts,rs,s0):= g in
    [seq ((lpart nts w),j,(rpart nts w)) |
      w <- 
      (filter 
        (fun x => (((length (lpart nts x))==l) (*/\ ((length (rpart nts x))==r)*)))
        (nffgen n 
          (fun x => ((length x)<=(l+r+1)))
          g 
          (nth_element (i-1) nts)
          (nth_element (j-1) nts)
        )
      )
    ].

(** Haskellのまま書いたのがこっち。

Definition tilr (n:nat) (g: Grammar) (i l r:nat)
  :list (SymbolString * nat * SymbolString) 
  := let ' (ts,nts,rs,s0):= g in
    flatten [seq (tilr' n g i l r j) | j <- ( List.seq 1 (List.length nts) )].

n以下のものについて出力する様に変更したのが
   下のもの。

*)

Definition tilr (n:nat) (g: Grammar) (i l r:nat):list (SymbolString * nat * SymbolString) :=
  let ' (ts,nts,rs,s0):= g in
    undup 
    (flatten [seq 
      flatten [seq (tilr' n g i l r j) | j <- ( List.seq 1 (List.length nts) )]
      | i <- (List.seq 1 n)
    ]).

Definition string_drop (i:nat) (s:string):string:=
  chars_to_str (drop i (str_to_chars s)).

Definition string_take (i:nat) (s:string):string:=
  chars_to_str (take i (str_to_chars s)).

(** * Definition of gA *)

Definition gA1 (n:nat) (g:Grammar) :list  Domino :=
  let ' (ts,nts,rs,s0):= g in
    flatten [seq [seq (x,x,0,0) |x <- (tik n g 1 m)] | m <- (List.seq 1 (3 * (List.length nts) + 1))].

Definition gA2' (n:nat) (i:nat) (g:Grammar) :list Domino :=
  let ' (ts,nts,rs,s0):= g in
    flatten [seq 
      [seq 
        (w,(string_drop i w),i,0) 
        |w <- (tik n g i m)] 
      | m <- (List.seq 1 (3 * (List.length nts) + 1))].

(**
gA2'において
drop：nat -> seq T -> seq Tで、wはstringなので、そのままではdropできない
ゆえに、chars_to_str、str_to_charsをかましている。
*)

Definition gA2 (n:nat) (g:Grammar) :list Domino :=
  let ' (ts,nts,rs,s0):= g in
    flatten [seq (gA2' n i g) | i <- (List.seq 1 (List.length nts))].

Definition gA3' (n:nat) (i:nat) (g:Grammar) :list Domino :=
  let ' (ts,nts,rs,s0):= g in
    flatten [seq 
      [seq 
        (w,(string_take (m-i) w),0,0) 
        |w <- (tik n g i m)] 
      | m <- (List.seq 1 (3 * (List.length nts) + 1))].

(**
gA2'と同様に、gA3'においても
take：nat -> seq T -> seq Tで、wはstringなので、そのままではtakeできない
ゆえに、chars_to_str、str_to_charsをかましている。
*)

Definition gA3 (n:nat) (g:Grammar) :list Domino :=
  let ' (ts,nts,rs,s0):= g in
    flatten [seq (gA3' n i g) | i <- (List.seq 1 (List.length nts))].

Definition gA (n:nat) (g:Grammar): list Domino:=
  app (app (gA1 n g) (gA2 n g)) (gA3 n g).

(**
gAを下の様に記述しても良いが、
演算子++がListに対するものであることを明示する為、
「Close Scope string_scope.」することが必要。
上のgA定義内のappはlistに対する++を意味する。

Definition gA (n:nat) (g:Grammar): list Domino:=
  (gA1 n g)++(gA2 n g)++(gA3 n g).
*)
(* *)
(** * Definition of gR *)

Definition gR1' (n:nat) (i l:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    flatten 
    [seq let ' (w,j,z) := wjz in 
      [seq ((w,((string_drop i w)++v),i,0),(z,z,0,0)) |
        v <- (sigman ts j)
      ] | 
      wjz <- (tilr n g i ((List.length nts)+1) l)
    ].

Definition gR1 (n:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    undup 
    (flatten 
      (flatten 
        [seq 
          [seq (gR1' n i l g) |
            i <- (List.seq 1 (List.length nts))
          ]|
          l <- (List.seq 0 ((List.length nts)+2))
        ]
      )
    ).

Definition gR2' (n:nat) (i l:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    flatten 
    [seq let ' (x,j,w) := xjw in 
      [seq ((x,(x++v),0,0),(w,(string_take ((List.length nts)+1-i) w),0,0)) |
        v <- (sigman ts j)
      ] | 
      xjw <- (tilr n g i l ((List.length nts)+1))
    ].

Definition gR2 (n:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    undup 
    (flatten 
      (flatten 
        [seq 
          [seq (gR2' n i l g) |
            i <- (List.seq 1 (List.length nts))
          ]|
          l <- (List.seq 0 ((List.length nts)+2))
        ]
      )
    ).

Definition gR3' (n:nat) (l m:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    flatten 
    [seq let ' (x,j,z) := xjz in 
      [seq ((x,(x++v),0,0),(z,z,0,0)) |
        v <- (sigman ts j)
      ] | 
      xjz <- (tilr n g 1 l m)
    ].

Definition gR3 (n:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    undup (
      flatten 
      (flatten 
        [seq 
          [seq (gR3' n l m g) |
            m <- (List.seq 0 (2*(List.length nts)+1-l+1))
          ]|
          l <- (List.seq 1 (2*(List.length nts)+1))
        ]
      )
    ).

Definition gR4' (n:nat) (i l:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    flatten 
    [seq let ' (z,j,w) := zjw in 
      [seq ((z,z,0,0),(w,(v++(string_take ((List.length nts)+1-i) w)),0,j)) |
        v <- (sigman ts j)
      ] | 
      zjw <- (tilr n g i l ((List.length nts)+1))
    ].

Definition gR4 (n:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    undup 
    (flatten 
      (flatten 
        [seq 
          [seq (gR4' n i l g) |
            i <- (List.seq 1 (List.length nts))
          ]|
          l <- (List.seq 0 ((List.length nts)+2))
        ]
      )
    ).

Definition gR5' (n:nat) (i l:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    flatten 
    [seq let ' (w,j,x) := wjx in 
      [seq ((w,(string_drop i w),i,0),(x,(v++x),0,j)) |
        v <- (sigman ts j)
      ] | 
      wjx <- (tilr n g 1 ((List.length nts)+1) l)
    ].

Definition gR5 (n:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    undup 
    (flatten 
      (flatten 
        [seq 
          [seq (gR5' n i l g) |
            i <- (List.seq 1 (List.length nts))
          ]|
          l <- (List.seq 0 ((List.length nts)+2))
        ]
      )
    ).

Definition gR6' (n:nat) (l m:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    flatten 
    [seq let ' (z,j,x) := zjx in 
      [seq ((z,z,0,0),(x,(v++x),0,j)) |
        v <- (sigman ts j)
      ] | 
      zjx <- (tilr n g 1 m l)
    ].

Definition gR6 (n:nat) (g:Grammar) :list (Domino * Domino) :=
  let ' (ts,nts,rs,s0):= g in
    undup 
    (flatten 
      (flatten 
        [seq 
          [seq (gR6' n l m g) |
            m <- (List.seq 0 (2*(List.length nts)+1-l+1))
          ]|
          l <- (List.seq 1 (2*(List.length nts)+1))
        ]
      )
    ).

Definition gR (n:nat) (g:Grammar): list (Domino * Domino) :=
undup (flatten [:: (gR1 n g);(gR2 n g);(gR3 n g);(gR4 n g);(gR5 n g);(gR6 n g)]).

Definition gGamma (n:nat) (g:Grammar):Sticker :=
  let ' (ts,nts,rs,s0):= g in
    (ts, (map (fun x => (x,x)) ts), (gA n g), (gR n g)).


(** * L(γ_G)=L(G)を示す *)
(** とりあえずは長さをnに制限したところで示す。
    
*)
(** ** example 8 *)
Definition gex_ex8:Grammar :=gex1.

(** ** example 9 *)

Definition gex_ex9:Grammar := gex2.

(** * ss5 *)
Definition ss5:Sticker := ([:: "a"%char; "b"%char],
       [:: ("a"%char, "a"%char); ("b"%char, "b"%char)],
       [:: ("a", "a", 0, 0); ("ab", "ab", 0, 0); ("aa", "aa", 0, 0);
           ("aab", "aab", 0, 0); ("aaa", "aaa", 0, 0);
           ("aabb", "aabb", 0, 0); ("aaab", "aaab", 0, 0);
           ("aaabb", "aaabb", 0, 0); ("aaabbb", "aaabbb", 0, 0);
           ("a", "", 1, 0); ("ab", "b", 1, 0); ("aa", "a", 1, 0);
           ("aab", "ab", 1, 0); ("aaa", "aa", 1, 0); 
          ("aabb", "abb", 1, 0); ("aaab", "aab", 1, 0);
           ("aaabb", "aabb", 1, 0); ("aaabbb", "aabbb", 1, 0);
           ("a", "", 2, 0); ("aa", "", 2, 0); ("aaa", "a", 2, 0);
           ("aaaa", "aa", 2, 0); ("a", "", 0, 0); ("ab", "a", 0, 0);
           ("aa", "a", 0, 0); ("aab", "aa", 0, 0); 
          ("aaa", "aa", 0, 0); ("aabb", "aab", 0, 0); 
          ("aaab", "aaa", 0, 0); ("aaabb", "aaab", 0, 0);
           ("aaabbb", "aaabb", 0, 0); ("a", "", 0, 0); 
          ("aa", "", 0, 0); ("aaa", "a", 0, 0); ("aaaa", "aa", 0, 0)],
       [:: ("aaa", "aaa", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aab", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaaa", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aaab", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aaba", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aabb", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aaaa", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaab", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaba", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aabb", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaa", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaab", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaba", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aabb", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaaa", 1, 0, ("", "", 0, 0));
           ("aaa", "aaab", 1, 0, ("", "", 0, 0));
           ("aaa", "aaba", 1, 0, ("", "", 0, 0));
           ("aaa", "aabb", 1, 0, ("", "", 0, 0));
           ("aaa", "aa", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "ab", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaa", 2, 0, ("b", "b", 0, 0));
           ("aaa", "aab", 2, 0, ("b", "b", 0, 0));
           ("aaa", "aba", 2, 0, ("b", "b", 0, 0));
           ("aaa", "abb", 2, 0, ("b", "b", 0, 0));
           ("aaa", "aaa", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "aab", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "aba", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "abb", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaa", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aab", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aba", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "abb", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaa", 2, 0, ("", "", 0, 0));
           ("aaa", "aab", 2, 0, ("", "", 0, 0));
           ("aaa", "aba", 2, 0, ("", "", 0, 0));
           ("aaa", "abb", 2, 0, ("", "", 0, 0));
           ("", "aa", 0, 0, ("", "", 0, 0));
           ("", "ab", 0, 0, ("", "", 0, 0));
           ("", "ba", 0, 0, ("", "", 0, 0));
           ("", "bb", 0, 0, ("", "", 0, 0));
           ("aa", "aaa", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aab", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aaaa", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aaab", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aaba", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aabb", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaa", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaab", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaa", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaab", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bbb", "b", 0, 0));
           ("a", "aa", 0, 0, ("b", "b", 0, 0));
           ("a", "ab", 0, 0, ("b", "b", 0, 0));
           ("a", "aaa", 0, 0, ("b", "b", 0, 0));
           ("a", "aab", 0, 0, ("b", "b", 0, 0));
           ("a", "aba", 0, 0, ("b", "b", 0, 0));
           ("a", "abb", 0, 0, ("b", "b", 0, 0));
           ("a", "aaa", 0, 0, ("", "", 0, 0));
           ("a", "aab", 0, 0, ("", "", 0, 0));
           ("a", "aba", 0, 0, ("", "", 0, 0));
           ("a", "abb", 0, 0, ("", "", 0, 0));
           ("aa", "aaa", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aab", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaaa", 0, 0, ("b", "b", 0, 0));
           ("aa", "aaab", 0, 0, ("b", "b", 0, 0));
           ("aa", "aaba", 0, 0, ("b", "b", 0, 0));
           ("aa", "aabb", 0, 0, ("b", "b", 0, 0));
           ("aa", "aaaa", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaab", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaba", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aabb", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaaa", 0, 0, ("", "", 0, 0));
           ("aa", "aaab", 0, 0, ("", "", 0, 0));
           ("aa", "aaba", 0, 0, ("", "", 0, 0));
           ("aa", "aabb", 0, 0, ("", "", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaaab", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaaba", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaabb", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("", "", 0, 0));
           ("aaa", "aaaab", 0, 0, ("", "", 0, 0));
           ("aaa", "aaaba", 0, 0, ("", "", 0, 0));
           ("aaa", "aaabb", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaaaa", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaaab", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaaba", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaabb", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaaaa", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaaab", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaaba", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaabb", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaaaa", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaaab", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaaba", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaabb", 0, 0, ("", "", 0, 0));
           ("aa", "aa", 0, 0, ("bb", "ab", 0, 1));
           ("aa", "aa", 0, 0, ("bb", "bb", 0, 1));
           ("aa", "aa", 0, 0, ("bb", "aab", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "abb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "bab", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "bbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "abb", 0, 1));
           ("aaa", "aaa", 0, 0, ("bbb", "bbb", 0, 1));
           ("aaa", "aaa", 0, 0, ("bbb", "aabb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "abbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "babb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "bbbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "ab", 0, 1));
           ("aaa", "aaa", 0, 0, ("bbb", "bb", 0, 1));
           ("aaa", "aaa", 0, 0, ("bb", "aab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "abb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "bab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "bbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "aab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "abb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "bab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "bbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "abbb", 0, 1));
           ("aaa", "aa", 1, 0, ("bbb", "bbbb", 0, 1));
           ("aaa", "aa", 1, 0, ("b", "aab", 0, 2));
           ("aaa", "aa", 1, 0, ("b", "abb", 0, 2));
           ("aaa", "aa", 1, 0, ("b", "bab", 0, 2));
           ("aaa", "aa", 1, 0, ("b", "bbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "aabb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "abbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "babb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "bbbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "aabbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "abbbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "babbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "bbbbb", 0, 2));
           ("aaa", "aa", 1, 0, ("", "aa", 0, 2));
           ("aaa", "aa", 1, 0, ("", "ab", 0, 2));
           ("aaa", "aa", 1, 0, ("", "ba", 0, 2));
           ("aaa", "aa", 1, 0, ("", "bb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "abbb", 0, 1));
           ("aaa", "a", 2, 0, ("bbb", "bbbb", 0, 1));
           ("aaa", "a", 2, 0, ("b", "aab", 0, 2));
           ("aaa", "a", 2, 0, ("b", "abb", 0, 2));
           ("aaa", "a", 2, 0, ("b", "bab", 0, 2));
           ("aaa", "a", 2, 0, ("b", "bbb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "aabb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "abbb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "babb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "bbbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "aabbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "abbbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "babbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "bbbbb", 0, 2));
           ("aaa", "a", 2, 0, ("", "aa", 0, 2));
           ("aaa", "a", 2, 0, ("", "ab", 0, 2));
           ("aaa", "a", 2, 0, ("", "ba", 0, 2));
           ("aaa", "a", 2, 0, ("", "bb", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "aab", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "abb", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "bab", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "bbb", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "aa", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "ab", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "ba", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "bb", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "aab", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "abb", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "bab", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "bbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "aabb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "abbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "babb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "bbbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "aa", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "ab", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "ba", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "bb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "abb", 0, 1));
           ("aa", "aa", 0, 0, ("bb", "bbb", 0, 1));
           ("aa", "aa", 0, 0, ("b", "aab", 0, 2));
           ("aa", "aa", 0, 0, ("b", "abb", 0, 2));
           ("aa", "aa", 0, 0, ("b", "bab", 0, 2));
           ("aa", "aa", 0, 0, ("b", "bbb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "aabb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "abbb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "babb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "bbbb", 0, 2));
           ("aa", "aa", 0, 0, ("", "aa", 0, 2));
           ("aa", "aa", 0, 0, ("", "ab", 0, 2));
           ("aa", "aa", 0, 0, ("", "ba", 0, 2));
           ("aa", "aa", 0, 0, ("", "bb", 0, 2));
           ("a", "a", 0, 0, ("b", "ab", 0, 1));
           ("a", "a", 0, 0, ("b", "bb", 0, 1));
           ("a", "a", 0, 0, ("b", "aab", 0, 2));
           ("a", "a", 0, 0, ("b", "abb", 0, 2));
           ("a", "a", 0, 0, ("b", "bab", 0, 2));
           ("a", "a", 0, 0, ("b", "bbb", 0, 2));
           ("a", "a", 0, 0, ("", "aa", 0, 2));
           ("a", "a", 0, 0, ("", "ab", 0, 2));
           ("a", "a", 0, 0, ("", "ba", 0, 2));
           ("a", "a", 0, 0, ("", "bb", 0, 2));
           ("", "", 0, 0, ("", "aa", 0, 2));
           ("", "", 0, 0, ("", "ab", 0, 2));
           ("", "", 0, 0, ("", "ba", 0, 2)); ("", "", 0, 0, ("", "bb", 0, 2))]).

(* Compute (ss5 == (gGamma 5 gex_ex9)).*)
(* Compute (ss_language 5 ss5).
Lemma equal5 : ss5 == (gGamma 5 gex_ex9).
Proof.
(*unfold ss5.*)
compute.
*)
(** *  *)
(** ss9 = (gGamma 9 gex_ex9). *)
Definition ss9 : Sticker := ([:: "a"%char; "b"%char],
       [:: ("a"%char, "a"%char); ("b"%char, "b"%char)],
       [:: ("a", "a", 0, 0); ("ab", "ab", 0, 0); ("aa", "aa", 0, 0);
           ("aab", "aab", 0, 0); ("aaa", "aaa", 0, 0);
           ("aabb", "aabb", 0, 0); ("aaab", "aaab", 0, 0);
           ("aaaa", "aaaa", 0, 0); ("aaabb", "aaabb", 0, 0);
           ("aaaab", "aaaab", 0, 0); ("aaaaa", "aaaaa", 0, 0);
           ("aaabbb", "aaabbb", 0, 0); ("aaaabb", "aaaabb", 0, 0);
           ("aaaaab", "aaaaab", 0, 0); ("aaaaaa", "aaaaaa", 0, 0);
           ("aaaabbb", "aaaabbb", 0, 0); ("aaaaabb", "aaaaabb", 0, 0);
           ("aaaaaab", "aaaaaab", 0, 0); ("aaaaaaa", "aaaaaaa", 0, 0);
           ("a", "", 1, 0); ("ab", "b", 1, 0); ("aa", "a", 1, 0);
           ("aab", "ab", 1, 0); ("aaa", "aa", 1, 0); 
          ("aabb", "abb", 1, 0); ("aaab", "aab", 1, 0);
           ("aaaa", "aaa", 1, 0); ("aaabb", "aabb", 1, 0);
           ("aaaab", "aaab", 1, 0); ("aaaaa", "aaaa", 1, 0);
           ("aaabbb", "aabbb", 1, 0); ("aaaabb", "aaabb", 1, 0);
           ("aaaaab", "aaaab", 1, 0); ("aaaaaa", "aaaaa", 1, 0);
           ("aaaabbb", "aaabbb", 1, 0); ("aaaaabb", "aaaabb", 1, 0);
           ("aaaaaab", "aaaaab", 1, 0); ("aaaaaaa", "aaaaaa", 1, 0);
           ("a", "", 2, 0); ("aa", "", 2, 0); ("aaa", "a", 2, 0);
           ("aaaa", "aa", 2, 0); ("aaaaa", "aaa", 2, 0);
           ("aaaaaa", "aaaa", 2, 0); ("aaaaaaa", "aaaaa", 2, 0);
           ("a", "", 0, 0); ("ab", "a", 0, 0); ("aa", "a", 0, 0);
           ("aab", "aa", 0, 0); ("aaa", "aa", 0, 0); 
          ("aabb", "aab", 0, 0); ("aaab", "aaa", 0, 0);
           ("aaaa", "aaa", 0, 0); ("aaabb", "aaab", 0, 0);
           ("aaaab", "aaaa", 0, 0); ("aaaaa", "aaaa", 0, 0);
           ("aaabbb", "aaabb", 0, 0); ("aaaabb", "aaaab", 0, 0);
           ("aaaaab", "aaaaa", 0, 0); ("aaaaaa", "aaaaa", 0, 0);
           ("aaaabbb", "aaaabb", 0, 0); ("aaaaabb", "aaaaab", 0, 0);
           ("aaaaaab", "aaaaaa", 0, 0); ("aaaaaaa", "aaaaaa", 0, 0);
           ("a", "", 0, 0); ("aa", "", 0, 0); ("aaa", "a", 0, 0);
           ("aaaa", "aa", 0, 0); ("aaaaa", "aaa", 0, 0);
           ("aaaaaa", "aaaa", 0, 0); ("aaaaaaa", "aaaaa", 0, 0)],
       [:: ("aaa", "aaa", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aab", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaaa", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aaab", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aaba", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aabb", 1, 0, ("b", "b", 0, 0));
           ("aaa", "aaaa", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaab", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaba", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aabb", 1, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaa", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaab", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaba", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aabb", 1, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaaa", 1, 0, ("", "", 0, 0));
           ("aaa", "aaab", 1, 0, ("", "", 0, 0));
           ("aaa", "aaba", 1, 0, ("", "", 0, 0));
           ("aaa", "aabb", 1, 0, ("", "", 0, 0));
           ("aaa", "aa", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "ab", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaa", 2, 0, ("b", "b", 0, 0));
           ("aaa", "aab", 2, 0, ("b", "b", 0, 0));
           ("aaa", "aba", 2, 0, ("b", "b", 0, 0));
           ("aaa", "abb", 2, 0, ("b", "b", 0, 0));
           ("aaa", "aaa", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "aab", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "aba", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "abb", 2, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaa", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aab", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aba", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "abb", 2, 0, ("bbb", "bbb", 0, 0));
           ("aaa", "aaa", 2, 0, ("", "", 0, 0));
           ("aaa", "aab", 2, 0, ("", "", 0, 0));
           ("aaa", "aba", 2, 0, ("", "", 0, 0));
           ("aaa", "abb", 2, 0, ("", "", 0, 0));
           ("", "aa", 0, 0, ("", "", 0, 0));
           ("", "ab", 0, 0, ("", "", 0, 0));
           ("", "ba", 0, 0, ("", "", 0, 0));
           ("", "bb", 0, 0, ("", "", 0, 0));
           ("aa", "aaa", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aab", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aaaa", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aaab", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aaba", 0, 0, ("bb", "b", 0, 0));
           ("aa", "aabb", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaa", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaab", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bbb", "bb", 0, 0));
           ("aaa", "aaaa", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaab", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bb", "b", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bbb", "b", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bbb", "b", 0, 0));
           ("a", "aa", 0, 0, ("b", "b", 0, 0));
           ("a", "ab", 0, 0, ("b", "b", 0, 0));
           ("a", "aaa", 0, 0, ("b", "b", 0, 0));
           ("a", "aab", 0, 0, ("b", "b", 0, 0));
           ("a", "aba", 0, 0, ("b", "b", 0, 0));
           ("a", "abb", 0, 0, ("b", "b", 0, 0));
           ("a", "aaa", 0, 0, ("", "", 0, 0));
           ("a", "aab", 0, 0, ("", "", 0, 0));
           ("a", "aba", 0, 0, ("", "", 0, 0));
           ("a", "abb", 0, 0, ("", "", 0, 0));
           ("aa", "aaa", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aab", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaaa", 0, 0, ("b", "b", 0, 0));
           ("aa", "aaab", 0, 0, ("b", "b", 0, 0));
           ("aa", "aaba", 0, 0, ("b", "b", 0, 0));
           ("aa", "aabb", 0, 0, ("b", "b", 0, 0));
           ("aa", "aaaa", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaab", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaba", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aabb", 0, 0, ("bb", "bb", 0, 0));
           ("aa", "aaaa", 0, 0, ("", "", 0, 0));
           ("aa", "aaab", 0, 0, ("", "", 0, 0));
           ("aa", "aaba", 0, 0, ("", "", 0, 0));
           ("aa", "aabb", 0, 0, ("", "", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaaab", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaaba", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaabb", 0, 0, ("b", "b", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaab", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaba", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaabb", 0, 0, ("bb", "bb", 0, 0));
           ("aaa", "aaaaa", 0, 0, ("", "", 0, 0));
           ("aaa", "aaaab", 0, 0, ("", "", 0, 0));
           ("aaa", "aaaba", 0, 0, ("", "", 0, 0));
           ("aaa", "aaabb", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaaaa", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaaab", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaaba", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaabb", 0, 0, ("b", "b", 0, 0));
           ("aaaa", "aaaaaa", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaaab", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaaba", 0, 0, ("", "", 0, 0));
           ("aaaa", "aaaabb", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaaaa", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaaab", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaaba", 0, 0, ("", "", 0, 0));
           ("aaaaa", "aaaaabb", 0, 0, ("", "", 0, 0));
           ("aa", "aa", 0, 0, ("bb", "ab", 0, 1));
           ("aa", "aa", 0, 0, ("bb", "bb", 0, 1));
           ("aa", "aa", 0, 0, ("bb", "aab", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "abb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "bab", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "bbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "abb", 0, 1));
           ("aaa", "aaa", 0, 0, ("bbb", "bbb", 0, 1));
           ("aaa", "aaa", 0, 0, ("bbb", "aabb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "abbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "babb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "bbbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "ab", 0, 1));
           ("aaa", "aaa", 0, 0, ("bbb", "bb", 0, 1));
           ("aaa", "aaa", 0, 0, ("bb", "aab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "abb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "bab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "bbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "aab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "abb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "bab", 0, 2));
           ("aaa", "aaa", 0, 0, ("bbb", "bbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "abbb", 0, 1));
           ("aaa", "aa", 1, 0, ("bbb", "bbbb", 0, 1));
           ("aaa", "aa", 1, 0, ("b", "aab", 0, 2));
           ("aaa", "aa", 1, 0, ("b", "abb", 0, 2));
           ("aaa", "aa", 1, 0, ("b", "bab", 0, 2));
           ("aaa", "aa", 1, 0, ("b", "bbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "aabb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "abbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "babb", 0, 2));
           ("aaa", "aa", 1, 0, ("bb", "bbbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "aabbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "abbbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "babbb", 0, 2));
           ("aaa", "aa", 1, 0, ("bbb", "bbbbb", 0, 2));
           ("aaa", "aa", 1, 0, ("", "aa", 0, 2));
           ("aaa", "aa", 1, 0, ("", "ab", 0, 2));
           ("aaa", "aa", 1, 0, ("", "ba", 0, 2));
           ("aaa", "aa", 1, 0, ("", "bb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "abbb", 0, 1));
           ("aaa", "a", 2, 0, ("bbb", "bbbb", 0, 1));
           ("aaa", "a", 2, 0, ("b", "aab", 0, 2));
           ("aaa", "a", 2, 0, ("b", "abb", 0, 2));
           ("aaa", "a", 2, 0, ("b", "bab", 0, 2));
           ("aaa", "a", 2, 0, ("b", "bbb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "aabb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "abbb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "babb", 0, 2));
           ("aaa", "a", 2, 0, ("bb", "bbbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "aabbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "abbbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "babbb", 0, 2));
           ("aaa", "a", 2, 0, ("bbb", "bbbbb", 0, 2));
           ("aaa", "a", 2, 0, ("", "aa", 0, 2));
           ("aaa", "a", 2, 0, ("", "ab", 0, 2));
           ("aaa", "a", 2, 0, ("", "ba", 0, 2));
           ("aaa", "a", 2, 0, ("", "bb", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "aab", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "abb", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "bab", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("b", "bbb", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "aa", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "ab", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "ba", 0, 2));
           ("aaaa", "aaaa", 0, 0, ("", "bb", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "aab", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "abb", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "bab", 0, 2));
           ("aaa", "aaa", 0, 0, ("b", "bbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "aabb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "abbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "babb", 0, 2));
           ("aaa", "aaa", 0, 0, ("bb", "bbbb", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "aa", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "ab", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "ba", 0, 2));
           ("aaa", "aaa", 0, 0, ("", "bb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "abb", 0, 1));
           ("aa", "aa", 0, 0, ("bb", "bbb", 0, 1));
           ("aa", "aa", 0, 0, ("b", "aab", 0, 2));
           ("aa", "aa", 0, 0, ("b", "abb", 0, 2));
           ("aa", "aa", 0, 0, ("b", "bab", 0, 2));
           ("aa", "aa", 0, 0, ("b", "bbb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "aabb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "abbb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "babb", 0, 2));
           ("aa", "aa", 0, 0, ("bb", "bbbb", 0, 2));
           ("aa", "aa", 0, 0, ("", "aa", 0, 2));
           ("aa", "aa", 0, 0, ("", "ab", 0, 2));
           ("aa", "aa", 0, 0, ("", "ba", 0, 2));
           ("aa", "aa", 0, 0, ("", "bb", 0, 2));
           ("a", "a", 0, 0, ("b", "ab", 0, 1));
           ("a", "a", 0, 0, ("b", "bb", 0, 1));
           ("a", "a", 0, 0, ("b", "aab", 0, 2));
           ("a", "a", 0, 0, ("b", "abb", 0, 2));
           ("a", "a", 0, 0, ("b", "bab", 0, 2));
           ("a", "a", 0, 0, ("b", "bbb", 0, 2));
           ("a", "a", 0, 0, ("", "aa", 0, 2));
           ("a", "a", 0, 0, ("", "ab", 0, 2));
           ("a", "a", 0, 0, ("", "ba", 0, 2));
           ("a", "a", 0, 0, ("", "bb", 0, 2));
           ("", "", 0, 0, ("", "aa", 0, 2));
           ("", "", 0, 0, ("", "ab", 0, 2));
           ("", "", 0, 0, ("", "ba", 0, 2)); ("", "", 0, 0, ("", "bb", 0, 2))]).

Lemma equal9to10:
(gGamma 9 gex_ex9)==(gGamma 10 gex_ex9).
Proof.
compute.
done.
Qed.

Lemma equal9:
ss9 == (gGamma 9 gex_ex9).
Proof.
compute.
done.
Qed.