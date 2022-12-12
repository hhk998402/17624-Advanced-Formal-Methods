----------------------------- MODULE Blockchain -----------------------------
EXTENDS SimpleInput, Randomization, FiniteSetsExt
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
    /\ winner_count <= TOTAL_WINNERS
    /\ winner_count + BLOCKCHAIN_LENGTH - Len(BlockchainData[user.userId]) <= TOTAL_WINNERS
    /\ Cardinality(Unconfirmed_Transaction_Pool \ TransactionsInChain(BlockchainData[user.userId])) >= BLOCK_TRANSACTION_COUNT
    /\ BlockchainData' = [BlockchainData EXCEPT
           ![user.userId] = Append(
               BlockchainData[user.userId],
               [
                   miner |-> user.userId,
                   block |-> RandomSubset(BLOCK_TRANSACTION_COUNT, Unconfirmed_Transaction_Pool \ TransactionsInChain(BlockchainData[user.userId]))
               ]
       )]
    /\ winner_count' = winner_count + 1
    /\ UNCHANGED <<Unconfirmed_Transaction_Pool, transaction_index>>

(*********************************************************************************)
(* Operation that simulates a user winning the lottery of obtaining the hash     *)
(* Chooses a miner at random                                                     *)
(* the winner_count variable to prevent scenario-space explosion                 *)
(*********************************************************************************)
WinBlock(miner) ==
    /\ miner.userId = (CHOOSE x \in RandomSubset(1, 1..NUM_MINERS): TRUE) 
    /\ CreateBlock(miner)

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
    \/ \E m \in Miners: WinBlock(m)
    \/ \E m1,m2 \in Miners: ReceiveBlockchainData(m1, m2)
Fairness == 
    /\ WF_Unconfirmed_Transaction_Pool(CreateNextTransaction)
    /\ \A m \in Miners: SF_BlockchainData(WinBlock(m))
    /\ \A m \in Miners: SF_BlockchainData(CreateBlock(m))
    /\ \A m1,m2 \in Miners: SF_BlockchainData(ReceiveBlockchainData(m1,m2))
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
(* Property stating that all miners finally reach a consensus                    *)
(* on transaction history                                                        *)
(* Note: This ceases to hold if TOTAL_WINNERS > BLOCKCHAIN_LENGTH                *)
(* Note: Restricted to miners to ensure quick execution                          *)
(*********************************************************************************)
MinersAgree == 
    /\ <>[](\A blockchain_a, blockchain_b \in RangeSeqSubset(BlockchainData, 1, NUM_MINERS): blockchain_a = blockchain_b)

(*********************************************************************************)
(* Property stating that all miners will finally agree on chains upto a point    *)
(* This length is effectively 2*BLOCKCHAIN_LENGTH - TOTAL_WINNERS                *)
(* Note: Restricted to miners to ensure quick execution                          *)
(*********************************************************************************)
MinersAgreeOnOlderChain == 
    /\ <>[](\A blockchain_a, blockchain_b \in RangeSeqSubset(BlockchainData, 1, NUM_MINERS): 
        1..CONSENSUS_LENGTH \subseteq (DOMAIN blockchain_a \intersect DOMAIN blockchain_b)
        => SubSeq(blockchain_a, 1, CONSENSUS_LENGTH) = SubSeq(blockchain_b, 1, CONSENSUS_LENGTH))

=============================================================================
\* Modification History
\* Last modified Wed Dec 07 22:15:00 EST 2022 by Dennis
\* Created Thu Dec 01 17:55:14 EST 2022 by Dennis
