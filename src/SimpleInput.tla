---------------------------- MODULE SimpleInput ----------------------------
EXTENDS FiniteSets, Naturals, Sequences, Reals

(*********************************************************************************)
(* Captures the users participating in the blockchain                            *)
(*********************************************************************************)
Users == {
    [
        username |-> "u1",
        userId |-> 1
    ],
    [
        username |-> "u2",
        userId |-> 2
    ],
    [
        username |-> "u3",
        userId |-> 3
    ],
    [
        username |-> "u3",
        userId |-> 4
    ],
    [
        username |-> "u4",
        userId |-> 5
    ],
    [
        username |-> "u5",
        userId |-> 5
    ],
    [
        username |-> "u6",
        userId |-> 6
    ],
    [
        username |-> "u7",
        userId |-> 7
    ],
    [
        username |-> "u8",
        userId |-> 8
    ]
}

(*********************************************************************************)
(* Captures the miners participating in the blockchain                           *)
(* They also represent the first n users in the blockchain                       *)
(*********************************************************************************)
Miners == {
    [
        username |-> "u1",
        userId |-> 1
    ],
    [
        username |-> "u2",
        userId |-> 2
    ],
    [
        username |-> "u3",
        userId |-> 3
    ]
}

(*********************************************************************************)
(* Permitted Transaction Amount                                                  *)
(*********************************************************************************)
Amounts == 1..10

(*********************************************************************************)
(* Transaction stream represnting the transactions carried out by the user       *)
(*********************************************************************************)
TransactionList == <<
    [
        payer |-> "u1",
        payee |-> "u2",
        amount |-> 10
    ],
    [
        payer |-> "u8",
        payee |-> "u2",
        amount |-> 5
    ],
    [
        payer |-> "u7",
        payee |-> "u6",
        amount |-> 8
    ],
    [
        payer |-> "u3",
        payee |-> "u5",
        amount |-> 1
    ],
    [
        payer |-> "u4",
        payee |-> "u8",
        amount |-> 3
    ],
    [
        payer |-> "u3",
        payee |-> "u6",
        amount |-> 6
    ]
>>


(************************************************)
(* Number of transactions in a block            *)
(************************************************)
BLOCK_TRANSACTION_COUNT == 2
(************************************************)
(* Number of miners                             *)
(************************************************)
NUM_MINERS == Cardinality(Miners)
(************************************************)
(* Number of users                              *)
(************************************************)
NUM_USERS == Cardinality(Users)
(************************************************)
(* Number of transactions in total              *)
(************************************************) 
NUM_TRANSACTIONS == Len(TransactionList)
(************************************************)
(* Final length of the blockchain                *)
(************************************************)
\* 
BLOCKCHAIN_LENGTH == 3
(************************************************)
(* Total number of permitted wins in a scenario *)
(************************************************)
TOTAL_WINNERS == 5
(************************************************)
(* Length upto which users reach consensus      *)
(************************************************)
CONSENSUS_LENGTH == 2 * BLOCKCHAIN_LENGTH - TOTAL_WINNERS

=============================================================================
\* Modification History
\* Last modified Wed Dec 07 22:28:14 EST 2022 by Dennis
\* Created Thu Dec 01 17 |->59 |->06 EST 2022 by Dennis
