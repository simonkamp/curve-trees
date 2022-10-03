# Full security through PRF
The coins are commitments in the curve $E_{even}$. $E_{even}$ and $E_{odd}$ form a 2-cycle.

A public key is a rerandomizable commitments to PRF key: $$C_{sk} = [sk] \cdot G + [r_{sk}] \cdot H_{odd} $$
(Could $r_{sk}$ just be zero?)

### Minting
When minting a coin to a receiver with public key $C_{sk}$:
- Let $C^*_{sk} = C_{sk}+r_{rerandomization}\cdot H_{odd}$ be a rerandomization of $C^*_{sk}$. 
(Not necessarily permissible.)
- Let $tx = v \cdot G_{value} + r_v \cdot H_{even}$ be a commitment to the value of the coin $v$. 
(Also not necessarily permissible.)
- Prove $v$ has appropiate range and balance with outher inputs/outputs.
- Send $(tx, C^*_{sk})$ to the network.

The network:
1. verifies $tx$ with the rest of the inputs and outputs. 
2. computes a hash of tx into the scalar field of $E_{odd}$: $H(tx)$.
3. homomorphically adds $H(tx)$ to $C^*_{sk}$ and then adds $H_{odd}$ until the result is permissible, obtaining $C_{sk+H(tx)}$. I.e:
$$C_{sk+H(tx)}=C^*_{sk}+[H(tx)]\cdot G + r_{permissible} \cdot H_{odd}$$
4. adds the $x$-coordinate of $C_{sk+H(tx)}$ to $tx$ (using the $G_{PRF}$ generator) and then adds $H_{even}$ until the result is permissible, obtaining $tx'$. Where $tx' = tx + [C_{sk+H(tx)}.x] \cdot G_{PRF} + [r_{permissible}'] \cdot H_{even}$.
5. add the $x$-coordinate of $tx'$ to the curve tree.

When the receiver gets passed $r_{rerandomization}$, $v$, and $r_v$ it can (based on the transaction and its private state) compute the opening of:
- $C_{sk+H(tx)} = [sk + H(tx)] \cdot G + [r_{sk} + r_{rerandomization} + r_{permissible}]\cdot H_{odd}$.
- $tx' = [v] \cdot G_{value} + [C_{sk+H(tx)}.x] \cdot G_{PRF} + [r_v + r_{permissible}'] \cdot H_{even}$.

### Spending
Assume a prover knows the opening of a coin $tx'$ as described above.

The prover:
1. Computes the tag $t = [(sk + H(tx))^{-1}] \cdot G$.
2. Selects and rerandomizes $tx'$ as $tx^* = tx' + [r_{coin}] \cdot H_{even}$ from the curve tree.
3. It then selects and rerandomizes $C_{sk+H(tx)}$ as $C^*_{sk+H(tx)} = C_{sk+H(tx)} + [r_{t}] \cdot H_{odd}$  from $tx^*$.
(This is a bit overkill, the index does not need to be secret. In fact it could cause soundness issues or at least complicate the proof. It should be selected with public index).
3. Proves that $C^*_{sk+H(tx)} = [x] \cdot G + [r^*] \cdot H_{odd} \land [x^{-1}] \cdot G = t$. Only revealing $t$.
Concretely:
    - show opening of commitment $C^*_{sk+H(tx)}$ obtaining variable for $x$
    - then either:
        - treat $t$ as a commitment with randomness zero, show opening, obtaining variable for $x^{-1}$ and constrain $x*x^{-1}-1 = 0$.
        - constrain a free variable to be inverse of $x$. ($x*x^{-1}-1$) and relate $t$ to $x^{-1}$ using ???


