# crush-lean

Machine-checked statements about CRUSH, in Lean 4 with Mathlib. A pilot.

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

**Final theorem** (`Crush.exists_weights`, no hypotheses left, no `sorry`;
`#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem exists_weights {r : ℕ} (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1)
    (hsum : ∑ i, π i = r) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ i, seqIncl w r Finset.univ i = π i
```

For any inclusion probabilities strictly between 0 and 1 that add up to `r`,
there are positive weights with which picking `r` distinct items one after the
other, in proportion to the weights among the items not yet picked, gives item
`i` the probability `π i`. This is the existence of a flat weight-set that
corrects the multi-pick anomaly.

Not covered: uniqueness of the weights up to scale, the boundary cases
(`π i = 1`), positional weight-sets, and anything about the C code or the
numerical solver.

No `sorry`; the theorems depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

Not proved here: anything probabilistic about CRUSH itself (that straw2 picks
in proportion to the weights needs a model of the hash), the multi-pick
anomaly, that the weight-set solvers converge, and anything about `mapper.c`.

    lake exe cache get && lake build

Copyright (c) 2026 Clyso Technologies Inc. LGPL-2.1.
