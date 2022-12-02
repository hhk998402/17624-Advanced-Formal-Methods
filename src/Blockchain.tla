----------------------------- MODULE Blockchain -----------------------------
EXTENDS SimpleInput, Randomization, FiniteSetsExt
VARIABLE Unconfirmed_Transaction_Pool, Blockchain, Miner_Status, transaction_index

\* State structure
Transaction == [
    payer: Users,
    payee: Users,
    amount: Amounts
]

Block ==  [i \in 1..5 |-> Transaction]
READY_TO_MINE == 0
READY_TO_TRANSMIT == 1


vars == <<Unconfirmed_Transaction_Pool, Blockchain, Miner_Status, transaction_index>>

\* Operations
CreateNextTransaction ==
    /\ transaction_index < Len(TransactionList)
    /\ Unconfirmed_Transaction_Pool' = Unconfirmed_Transaction_Pool \union {[
           payer |-> TransactionList[transaction_index].payer,
           payee |-> TransactionList[transaction_index].payee,
           amount |-> TransactionList[transaction_index].amount
       ]}
    /\ transaction_index' = transaction_index + 1
    /\ UNCHANGED <<Blockchain, Miner_Status>>
    
TransactionsInChain(miner_blockchain) == ReduceSet(LAMBDA x,y : x.block \union y, {}, RangeSeq(miner_blockchain))

CreateBlock(user) ==
    /\ Miner_Status[user.userId] = READY_TO_MINE
    /\ Cardinality(Unconfirmed_Transaction_Pool \ TransactionsInChain(Blockchain[user.userId])) >= 5
    /\ Blockchain' = [Blockchain EXCEPT
           ![user.userId] = Append(
               Blockchain[user.userId],
               [
                   miner |-> user.userId,
                   block |-> RandomSubset(5, Unconfirmed_Transaction_Pool \ TransactionsInChain(Blockchain[user.userId]))
               ]
       )]
    /\ UNCHANGED <<Unconfirmed_Transaction_Pool, Miner_Status, transaction_index>>  

\* Spec
Init == 
    /\ Unconfirmed_Transaction_Pool = {}
    /\ Blockchain = [i \in 1..8 |-> << >> ]
    /\ Miner_Status = [i \in 1..5 |-> READY_TO_MINE ]
    /\ transaction_index = 1
Next == 
    \/ CreateNextTransaction
    \/ \E m \in Miners: CreateBlock(m)
Fairness == 
    /\ WF_Unconfirmed_Transaction_Pool(CreateNextTransaction)
    /\ \A m \in Miners: WF_Blockchain(CreateBlock(m))
Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ Fairness

\* Properties
TransactionsNeverGetAdded == 
    /\ [](transaction_index <= 11)

=============================================================================
\* Modification History
\* Last modified Fri Dec 02 01:38:49 EST 2022 by Dennis
\* Created Thu Dec 01 17:55:14 EST 2022 by Dennis
