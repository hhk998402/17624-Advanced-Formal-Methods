--------------------------- MODULE FiniteSetsExt ---------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences

MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, by choosing the set *)
(* elements with `choose`. If there are multiple ways for choosing an element,*)
(* op should be associative and commutative. Otherwise, the result may depend *)
(* on the concrete implementation of `choose`.                                *)
(*                                                                            *)
(*                                                                            *)
(* Example:                                                                   *)
(*  MapThenFoldSet(LAMBDA x,y: x \cup y,                                      *)
(*                 {},                                                        *)
(*                 LAMBDA x: {{x}},                                           *)
(*                 LAMBDA set: CHOOSE x \in set: TRUE,                        *)
(*                 {1,2})                                                     *)
(*       = {{1},{2}}                                                          *)
(******************************************************************************)
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]


(*************************************************************************)
(* Fold op over the elements of set using base as starting value.        *)
(*                                                                       *)
(* Example:                                                              *)
(*         ReduceSet(LAMBA x,y : x + y, 0, 0 .. 10) = 55                 *)
(*************************************************************************)
ReduceSet(op(_,_), base, set) ==
   MapThenFoldSet(op, base, LAMBDA x : x, LAMBDA s : CHOOSE x \in s : TRUE, set)

(*************************************************************************)
(* Convert Sequence Range to Set                                         *)
(*                                                                       *)
(* Example:                                                              *)
(*         RangeSeq(<<'a', 'b'>>) = {'a', 'b'}                           *)
(*************************************************************************)
RangeSeq(seq) == { seq[i]: i \in 1..Len(seq) }

(*************************************************************************)
(* Convert Sequence Range filtered by start and end index to a Set       *)
(*                                                                       *)
(* Example:                                                              *)
(*         RangeSeqSubset(<<'a', 'b', 'c', 'd'>>, 2, 3) = {'b', 'c'}     *)
(*************************************************************************)
RangeSeqSubset(seq, start, end) == { seq[i]: i \in start..end }


(*************************************************************************)
(* Find maximum/minimum in the set provided                              *)
(*                                                                       *)
(* Example:                                                              *)
(*         SetMax({1,3,5}) = 5                                           *)
(*         SetMin({1,3,5}) = 1                                           *)
(*************************************************************************)
SetMax (S) == IF Cardinality(S) = 0 THEN 0 ELSE CHOOSE t \in S : \A s \in S : t >= s
SetMin (S) == IF Cardinality(S) = 0 THEN 0 ELSE CHOOSE t \in S : \A s \in S : t <= s
=============================================================================
\* Modification History
\* Last modified Sun Dec 11 12:28:26 EST 2022 by Dennis
\* Created Fri Dec 02 00:36:27 EST 2022 by Dennis
