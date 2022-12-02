----------------------------- MODULE Blockchain -----------------------------
EXTENDS FiniteSets, Naturals, Sequences, SimpleInput
VARIABLE Unconfirmed_Transaction_Pool, Blockchain, transaction_index

Users == <<"u1", "u2", "u3", "u4", "u5", "u6", "u7", "u8">>
Miners == <<"u1", "u2", "u3", "u4", "u5">>
Amounts == 1..10

\* State structure
Transaction == [
    payer: Users,
    payee: Users,
    amount: Amounts
]

Block ==  [i \in 1..5 |-> Transaction]


vars == <<Unconfirmed_Transaction_Pool, Blockchain, transaction_index>>

\* Operations
CreateNextTransaction ==
    /\ transaction_index < Len(TransactionList)
    /\ Unconfirmed_Transaction_Pool' = Unconfirmed_Transaction_Pool \union {[
           payer |-> TransactionList[transaction_index].payer,
           payee |-> TransactionList[transaction_index].payee,
           amount |-> TransactionList[transaction_index].amount
       ]}
    /\ transaction_index' = transaction_index + 1
    /\ UNCHANGED <<Blockchain>>

\* CreateBlock() ==
\*     /\ Cardinality(Unconfirmed_Transaction_Pool) >= 5



\* Spec
Init == 
    /\ Unconfirmed_Transaction_Pool = {}
    /\ Blockchain = [i \in 1..8 |-> << >> ]
    /\ transaction_index = 1
Next == 
    \/ CreateNextTransaction
Fairness == 
    /\ WF_Unconfirmed_Transaction_Pool(CreateNextTransaction)
Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ Fairness

\* Properties
TransactionsNeverGetAdded == 
    /\ [](transaction_index = 1)

=============================================================================
\* Modification History
\* Last modified Thu Dec 01 22:13:40 EST 2022 by Dennis
\* Created Thu Dec 01 17:55:14 EST 2022 by Dennis
