# crush-lean

Machine-checked mathematics about CRUSH, the placement algorithm of
[Ceph](https://ceph.io), in Lean 4 with Mathlib.

## Results

**1. Which data distributions are possible.** A placement of `r` replicas on
distinct items with data in proportion to the weights exists if and only if no
item has more than `1 / r` of the weight (`Crush.Design.exists_proportional_iff`).

**2. The multi-pick anomaly can always be corrected by a weight-set.** When a
CRUSH rule picks several items from a bucket, low-weight items get more than
their share ([tracker 15653](https://tracker.ceph.com/issues/15653)). The
correction is to draw with adjusted weights. Such weights always exist:

```lean
theorem exists_weights {r : ℕ} (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1)
    (hsum : ∑ i, π i = r) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ i, seqIncl w r Finset.univ i = π i
```

Here `seqIncl w r S i` is the probability that item `i` is among `r` items
picked from `S` one after the other, each in proportion to the weights `w`
among the items not yet picked (CRUSH's draw-and-retry, with the hash
idealised as independent random draws), and `π` is any target strictly inside
the possible region of result 1.

**3. straw2 moves only what it must.** When one item's weight changes, every
input keeps its item or moves to or from that item, for every input and every
hash value (`Crush.Chooses.of_weight_le`, `Crush.Chooses.of_le_weight`).

**[docs/PROOF.md](docs/PROOF.md) explains the proofs in words**, including
what is *not* proved: uniqueness of the weights, the boundary case,
positional weight-sets, convergence of any solver, and everything about the C
implementation.

The existence theorem is the mathematical basis of the weight-set solver
proposed in [tracker 83478](https://tracker.ceph.com/issues/83478) /
[ceph/ceph#74223](https://github.com/ceph/ceph/pull/74223): it shows that the
solver has a solution to find whenever no item exceeds `1 / r` of the weight.
It says nothing about that code.

## Checking it

```
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh    # Lean toolchain manager
lake exe cache get                                        # prebuilt Mathlib
lake build
```

Lean 4.36.0 and Mathlib v4.36.0 (pinned in `lean-toolchain` and
`lake-manifest.json`). About 2,100 lines. There is no `sorry` and no added
axiom: `#print axioms Crush.exists_weights` lists `propext`,
`Classical.choice` and `Quot.sound`, the three axioms all of Mathlib uses.

What "machine-checked" does and does not buy: Lean guarantees that the
theorems follow from the definitions. Whether the definitions say what CRUSH
does is for a human to judge; the ones to read are `Crush.seqIncl`
(`Crush/Sequential.lean`), `Crush.Design` (`Crush/Design.lean`) and
`Crush.Wins` / `Crush.Chooses` (`Crush/Straw2.lean`), about 30 lines in all.

## Files

| File | What is proved |
|---|---|
| `Crush/Straw2.lean` | straw2 selection (longest straw wins). If one item's straw gets longer, every input keeps its item or moves to that item; if it gets shorter, only inputs on that item move. For every input and every hash: only that an item's straw depends on its own weight is used. The straw `log u / w` grows with `w`. |
| `Crush/Design.lean` | Any way of putting each input on `r` distinct items is a probability on `r`-subsets. Its inclusion probabilities add up to `r` and none exceeds 1, so no placement can give an item more than `1/r` of the data. |
| `Crush/Existence.lean` | The converse: for any inclusion probabilities in `[0, 1]` that add up to `r`, a placement exists. Hence: data in proportion to the weights is possible **iff** no item has more than `1/r` of the weight (`Crush.Design.exists_proportional_iff`). |
| `Crush/Potential.lean` | The analytic half of "flat weights exist": if the inclusion probabilities are a continuous subgradient of a potential that grows like the sum of the `r` largest, every target strictly between 0 and 1 that adds up to `r` is reached (`Crush.exists_incl_eq`). |
| `Crush/TopR.lean` | Choosing the `r` largest for one vector: the chosen set is a subgradient of the largest sum where there are no ties, plus bounds. The deterministic input to the next step. |
| `Crush/RandomTop.lean` | For random values with integrable entries and ties of probability 0, the expected largest sum is such a potential, so choosing the `r` largest of `θ i + G i` reaches every interior set of inclusion probabilities (`Crush.exists_inclusion_eq`). |
| `Crush/Iid.lean` | Independent values with a common law in which no single value has positive probability almost never tie (`Crush.ae_noTies`); with a mean, the theorem above applies (`Crush.exists_inclusion_eq_iid`). |
| `Crush/Gumbel.lean` | The law of `-log E` for an exponential `E` is a probability measure with a mean and no point masses, so the theorem holds for Gumbel values (`Crush.exists_inclusion_eq_gumbel`). |
| `Crush/Sequential.lean` | CRUSH's draw-and-retry as a recursive definition (`Crush.seqIncl`), the statement `Crush.ClockBridge` that it agrees with "the `r` largest of `log w i` + Gumbel", and what follows from that statement (`Crush.exists_weights_of_clockBridge`). |
| `Crush/Rank.lean` | With distinct values, an item is among the `r` largest exactly when fewer than `r` items have a larger value (`Crush.inTop_iff_card_lt`). |
| `Crush/Clock.lean` | Independent exponential clocks: memorylessness of one (`Crush.expMeasure_shift`) and of the family (`Crush.pi_shift`), integration over one coordinate (`Crush.pi_eq_lintegral_update`), `E exp(-cX) = 1/(1+c)`. |
| `Crush/Bridge.lean` | Clock `j` rings first with probability `w j / W`, independently of the order of the others (`Crush.clocks_firstIn_inter`); hence the recursion of `seqIncl` (`Crush.clocks_early`), `Crush.clockBridge`, and the final theorem. |

## How this was written

The Lean code and the text were written by Claude Code (Claude Fable 5.2),
directed by Dan van der Ster. The proofs are checked by Lean, not by trust in
either.

## Licence

Copyright (c) 2026 Clyso Technologies Inc. Released under the GNU Lesser
General Public License version 2.1, see [LICENSE](LICENSE).
