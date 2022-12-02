---------------------------- MODULE SimpleInput ----------------------------
EXTENDS FiniteSets, Naturals, Sequences

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
    ],
    [
        username |-> "u4",
        userId |-> 5
    ],
    [
        username |-> "u5",
        userId |-> 5
    ]
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
        payer |-> "u2",
        payee |-> "u1",
        amount |-> 6
    ],
    [
        payer |-> "u8",
        payee |-> "u6",
        amount |-> 9
    ],
    [
        payer |-> "u3",
        payee |-> "u5",
        amount |-> 5
    ],
    [
        payer |-> "u7",
        payee |-> "u1",
        amount |-> 10
    ],
    [
        payer |-> "u6",
        payee |-> "u7",
        amount |-> 2
    ]
>>

=============================================================================
\* Modification History
\* Last modified Fri Dec 02 01:24:38 EST 2022 by Dennis
\* Created Thu Dec 01 17 |->59 |->06 EST 2022 by Dennis
