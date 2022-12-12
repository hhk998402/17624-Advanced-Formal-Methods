------------------------- MODULE ConsensusLengthExt -------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE Naturals

(*************************************************************************)
(* Find maximum/minimum in the set provided                              *)
(*                                                                       *)
(* Example:                                                              *)
(*         FilterRoundIndicesWithExactlyOneWinner(                       *)
(*           <1, 2, 3, 1, 2>                                             *)
(*         ) = {1, 4}                                                    *)
(*                                                                       *)
(*************************************************************************)
FilterRoundIndicesWithExactlyOneWinner(seq) ==
    ReduceSet(
        LAMBDA x,y: IF seq[x] = 1 THEN {x} \cup y ELSE y,
        {},
        DOMAIN seq)

(*************************************************************************)
(* Find the shortest blockchain among the miners                         *)
(*                                                                       *)
(* Example:                                                              *)
(*         ShortestBlockchainLength( <<                                  *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m1), >>             *)
(*           << (T1,T2 | m1), (T3,T4 | m2) >>                            *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m3), >>             *)
(*         >> ) = 2                                                      *)
(*                                                                       *)
(*************************************************************************)
ShortestBlockchainLength(b, num_miners) ==
    ReduceSet(
        LAMBDA x,y: SetMin({y, Len(b[x])}),
        100000, \* Theoretical int_max
        1..num_miners
    )

(*************************************************************************)
(* Find the miners that won the ith round                                *)
(*                                                                       *)
(* Example:                                                              *)
(*         MinerSet( <<                                                  *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m1), >>             *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m3), >>             *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m3), >>             *)
(*         >>, 3 ) = {1, 3}                                              *)
(*                                                                       *)
(*************************************************************************)
MinerSet(b, i, num_miners) ==
    ReduceSet(
        LAMBDA x,y: y \union { b[x][i].miner },
        {},
        1..num_miners
    )

(*************************************************************************)
(* Find the number of winners in each round and return as a sequence     *)
(*                                                                       *)
(* Example:                                                              *)
(*         WinnerCountList( <<                                           *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m1), >>             *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m3), >>             *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m3), >>             *)
(*         >> ) = <1, 1, 2>                                              *)
(*                                                                       *)
(*************************************************************************)
WinnerCountList(b, num_miners) ==
    MapThenFoldSet(
        LAMBDA x,y: Append(y, Cardinality(MinerSet(b, x, num_miners)) ),
        << >>,
        LAMBDA x : x, 
        LAMBDA x : SetMax(x),
        1..ShortestBlockchainLength(b, num_miners))

(*************************************************************************)
(* Find consensus length for the blockchain state                        *)
(*                                                                       *)
(* Example:                                                              *)
(*         ConsensusLength( <<                                           *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m1), >>             *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m3), >>             *)
(*           << (T1,T2 | m1), (T3,T4 | m2), (T5,T6 | m3), >>             *)
(*         >> ) = 2                                                      *)
(*                                                                       *)
(*************************************************************************)
ConsensusLength(b, num_miners) == SetMax(FilterRoundIndicesWithExactlyOneWinner(WinnerCountList(b, num_miners)))

=============================================================================
\* Modification History
\* Last modified Sun Dec 11 19:56:47 EST 2022 by Dennis
\* Created Sun Dec 11 12:18:46 EST 2022 by Dennis
