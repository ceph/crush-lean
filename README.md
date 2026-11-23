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

Still to do for "flat weights exist for CRUSH": (1) the Gumbel law, minus the
logarithm of an exponential variable, has a mean and no atoms; (2) choosing the
`r` largest of `log w i + Gumbel` is CRUSH's draw-and-retry (successive
sampling).

No `sorry`; the theorems depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

Not proved here: anything probabilistic about CRUSH itself (that straw2 picks
in proportion to the weights needs a model of the hash), the multi-pick
anomaly, that the weight-set solvers converge, and anything about `mapper.c`.

    lake exe cache get && lake build

Copyright (c) 2026 Clyso Technologies Inc. LGPL-2.1.
