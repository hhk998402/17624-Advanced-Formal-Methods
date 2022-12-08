---------------------------- MODULE SimpleInput ----------------------------
EXTENDS FiniteSets, Naturals, Sequences, Reals

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
\*    [
\*        username |-> "u4",
\*        userId |-> 4
\*    ],
\*    [
\*        username |-> "u5",
\*        userId |-> 5
\*    ]
}

Amounts == 1..10

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
\*    [
\*        payer |-> "u7",
\*        payee |-> "u2",
\*        amount |-> 10
\*    ]
\*    [
\*        payer |-> "u8",
\*        payee |-> "u2",
\*        amount |-> 6
\*    ],
\*    [
\*        payer |-> "u1",
\*        payee |-> "u3",
\*        amount |-> 7
\*    ],
\*    [
\*        payer |-> "u3",
\*        payee |-> "u5",
\*        amount |-> 9
\*    ]
>>

BLOCK_TRANSACTION_COUNT == 2
NUM_MINERS == Cardinality(Miners)
NUM_USERS == Cardinality(Users)
NUM_TRANSACTIONS == Len(TransactionList)
BLOCKCHAIN_LENGTH == 3
TOTAL_WINNERS == 5
CONSENSUS_LENGTH == 2 * BLOCKCHAIN_LENGTH - TOTAL_WINNERS

=============================================================================
\* Modification History
\* Last modified Wed Dec 07 17:58:30 EST 2022 by Dennis
\* Created Thu Dec 01 17 |->59 |->06 EST 2022 by Dennis
