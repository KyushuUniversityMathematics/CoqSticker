From mathcomp Require Import all_ssreflect.

(* 有限オートマトンの定義 *)
Structure automaton{state symbol:finType}:= Automaton {
  init : state;
  delta : state -> symbol -> state;
  final : {set state}
}.

(*記号を複数個まとめて読み込む関数*)
Fixpoint dstar{state symbol:finType}(delta:state->symbol->state)
  (q:state)(str:seq symbol):state :=
match str with
|nil => q
|h::str' => dstar delta (delta q h) str'
end.

(*受理判定の関数*)
Definition accept{state symbol:finType}(M:@automaton state symbol)
  (str:seq symbol):bool := dstar (delta M) (init M) str\in final M.

(*与えられた文字列のうち、acceptされるものだけを残す*)
Definition accepts{state symbol:finType}(M:@automaton state symbol)
  (l:seq (seq symbol)):seq (seq symbol):=
[seq str<-l|accept M str].

(*文字の読み込みを二段階に分割*)
Lemma dstarLemma {state symbol : finType}(delta:state->symbol->state)(q:state)
(s t:seq symbol):dstar delta q (s++t) = dstar delta (dstar delta q s) t.
Proof. move:q;by elim:s;[|move=>a s' H;simpl]. Qed.
