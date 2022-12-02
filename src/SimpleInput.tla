---------------------------- MODULE SimpleInput ----------------------------
EXTENDS FiniteSets, Naturals

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
\* Last modified Thu Dec 01 19 |->10 |->54 EST 2022 by Dennis
\* Created Thu Dec 01 17 |->59 |->06 EST 2022 by Dennis
