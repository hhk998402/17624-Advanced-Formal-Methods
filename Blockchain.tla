---------------------------- MODULE Blockchain ----------------------------
EXTENDS FiniteSets, Naturals

\* State structure
Users = {"u1", "u2", "u3", "u4", "u5", "u6", "u7", "u8"}
Miners = {"u1", "u2", "u3", "u4", "u5"}
Amounts = 1..10

Transaction = [
    payer: Users,
    payee: Users,
    amount: Amounts
]

Block =  [i \in 1..5 |-> Transaction]

VARIABLE Unconfirmed_Transaction_Pool, Blockchain

=============================================================================