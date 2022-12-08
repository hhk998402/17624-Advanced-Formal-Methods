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
CreateNextTransaction ==
    /\ transaction_index <= Len(TransactionList)
    /\ Unconfirmed_Transaction_Pool' = Unconfirmed_Transaction_Pool \union {[
           payer |-> TransactionList[transaction_index].payer,
           payee |-> TransactionList[transaction_index].payee,
           amount |-> TransactionList[transaction_index].amount
       ]}
    /\ transaction_index' = transaction_index + 1
    /\ UNCHANGED <<BlockchainData, winner_count>>
    
TransactionsInChain(miner_BlockchainData) == ReduceSet(LAMBDA x,y : x.block \union y, {}, RangeSeq(miner_BlockchainData))

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

WinBlock(miner) ==
    /\ miner.userId = (CHOOSE x \in RandomSubset(1, 1..NUM_MINERS): TRUE) 
    /\ CreateBlock(miner)

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
TransactionsGetAdded == 
\*    /\ <>(winner_count = 3) => <>(\A i,i2 \in 1..NUM_MINERS: BlockchainData[i] = BlockchainData[i2])
    /\ <>(\A i \in 1..NUM_MINERS: Len(BlockchainData[i]) = BLOCKCHAIN_LENGTH)


MinersAgree == 
    /\ <>[](\A blockchain_a, blockchain_b \in RangeSeqSubset(BlockchainData, NUM_MINERS): blockchain_a = blockchain_b)
\*    /\ <>[](BlockchainData[1] = BlockchainData[2] /\ BlockchainData[2] = BlockchainData[3])
\*    /\ [][winner_count <= 2]_<<Unconfirmed_Transaction_Pool, BlockchainData, transaction_index>>

MinersAgreeOnOlderChain == 
    /\ <>[](\A blockchain_a, blockchain_b \in RangeSeqSubset(BlockchainData, NUM_MINERS): 
        1..CONSENSUS_LENGTH \subseteq (DOMAIN blockchain_a \intersect DOMAIN blockchain_b)
        => SubSeq(blockchain_a, 1, CONSENSUS_LENGTH) = SubSeq(blockchain_b, 1, CONSENSUS_LENGTH))

=============================================================================
\* Modification History
\* Last modified Wed Dec 07 18:01:46 EST 2022 by Dennis
\* Created Thu Dec 01 17:55:14 EST 2022 by Dennis
