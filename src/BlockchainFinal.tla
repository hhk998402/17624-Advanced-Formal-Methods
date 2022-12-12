----------------------------- MODULE BlockchainFinal -----------------------------
EXTENDS SimpleInput, Randomization, FiniteSetsExt, ConsensusLengthExt
VARIABLE Unconfirmed_Transaction_Pool, BlockchainData, transaction_index, winner_count

\* State structure

Transaction == [
    payer: Users,
    payee: Users,
    amount: Amounts
]

Block ==  [i \in 1..BLOCK_TRANSACTION_COUNT |-> Transaction]


vars == <<Unconfirmed_Transaction_Pool, BlockchainData, transaction_index, winner_count>>

\* Operations

(*********************************************************************************)
(* Operation that creates Next Transaction from the Transaction list constant    *)
(*********************************************************************************)
CreateNextTransaction ==
    /\ transaction_index <= Len(TransactionList)
    /\ Unconfirmed_Transaction_Pool' = Unconfirmed_Transaction_Pool \union {[
           payer |-> TransactionList[transaction_index].payer,
           payee |-> TransactionList[transaction_index].payee,
           amount |-> TransactionList[transaction_index].amount
       ]}
    /\ transaction_index' = transaction_index + 1
    /\ UNCHANGED <<BlockchainData, winner_count>>


(********************************************************************************)
(* Function to return the set of all transactions in a user's blockchain        *)
(*                                                                              *)
(* Example:                                                                     *)
(*         TransactionsInChain(<< a(a1, a2), b(b1, b2) >>) =                    *)
(*                                                  {a1, a2, b1, b2}            *)
(* a,b refer to blocks in the blockchain                                        *)
(* a1, a2 are transactions in block a and b1, b2 are transactions in block b    *)
(********************************************************************************)
TransactionsInChain(miner_blockchain) == ReduceSet(LAMBDA x,y : x.block \union y, {}, RangeSeq(miner_blockchain))

(*********************************************************************************)
(* Operation that lets the user create a block                                   *)
(* Additionally, the ability of a user to win the lottery is controlled by       *)
(* the winner_count variable to prevent scenario-space explosion                 *)
(*********************************************************************************)
CreateBlock(user) ==
    /\ Cardinality(Unconfirmed_Transaction_Pool \ TransactionsInChain(BlockchainData[user.userId])) >= BLOCK_TRANSACTION_COUNT
    /\ BlockchainData' = [BlockchainData EXCEPT
           ![user.userId] = Append(
               BlockchainData[user.userId],
               [
                   miner |-> user.userId,
                   block |-> RandomSubset(BLOCK_TRANSACTION_COUNT, Unconfirmed_Transaction_Pool \ TransactionsInChain(BlockchainData[user.userId]))
               ]
       )]
    /\ UNCHANGED <<Unconfirmed_Transaction_Pool, transaction_index, winner_count>>

(*********************************************************************************)
(* Operation that models a miner sending a mined block to other users            *)
(*********************************************************************************)
ReceiveBlockchainData(sender, receiver) ==
    /\ sender # receiver
    /\ Len(BlockchainData[sender.userId]) > Len(BlockchainData[receiver.userId])
    /\ BlockchainData' = [BlockchainData EXCEPT
        ![receiver.userId] = BlockchainData[sender.userId]
       ]
    /\ UNCHANGED <<Unconfirmed_Transaction_Pool, transaction_index, winner_count>>

\* Spec

Init == 
    /\ Unconfirmed_Transaction_Pool = {}
    /\ BlockchainData = [i \in 1..NUM_USERS |-> << >> ]
    /\ transaction_index = 1
    /\ winner_count = 0
Next == 
    \/ CreateNextTransaction
    \/ \E m \in Miners: CreateBlock(m)
    \/ \E m1,m2 \in Miners: ReceiveBlockchainData(m1, m2)
    \/ (transaction_index > Len(TransactionList) /\ UNCHANGED vars)
Fairness == 
    /\ WF_<<Unconfirmed_Transaction_Pool, transaction_index>>(CreateNextTransaction)
    /\ \A m \in Miners: WF_<<BlockchainData, winner_count>>(CreateBlock(m))
    /\ \A m1,m2 \in Miners: WF_<<BlockchainData>>(ReceiveBlockchainData(m1,m2))
Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ Fairness

\* Properties

(*********************************************************************************)
(* Property stating that all transactions in the transaction list get added      *)
(* Note: The transactions must be an exact multiple of BLOCK_TRANSACTION_COUNT   *)
(*********************************************************************************)
TransactionsGetAdded == 
    /\ <>(\A i \in 1..NUM_MINERS: Len(BlockchainData[i]) = BLOCKCHAIN_LENGTH)

(*********************************************************************************)
(* Property stating that all miners will always agree on chains upto the         *)
(* calculated consensus point                                                    *)
(* This length is effectively 2*BLOCKCHAIN_LENGTH - TOTAL_WINNERS                *)
(* Note: Restricted to miners to ensure quick execution                          *)
(*********************************************************************************)
MinersAgreeUptoConsensusLength == 
    LET cLength == ConsensusLength(BlockchainData, NUM_MINERS)
    IN [](\A blockchain_a, blockchain_b \in RangeSeqSubset(BlockchainData, 1, NUM_MINERS): 
        1..cLength \subseteq (DOMAIN blockchain_a \intersect DOMAIN blockchain_b)
        => SubSeq(blockchain_a, 1, cLength) = SubSeq(blockchain_b, 1, cLength))

=============================================================================
\* Modification History
\* Last modified Sun Dec 11 19:58:04 EST 2022 by Dennis
\* Created Thu Dec 01 17:55:14 EST 2022 by Dennis
