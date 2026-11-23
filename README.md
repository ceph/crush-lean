# crush-lean

Machine-checked statements about CRUSH, in Lean 4 with Mathlib. A pilot.

| File | What is proved |
|---|---|
| `Crush/Straw2.lean` | straw2 selection (longest straw wins). If one item's straw gets longer, every input keeps its item or moves to that item; if it gets shorter, only inputs on that item move. For every input and every hash: only that an item's straw depends on its own weight is used. The straw `log u / w` grows with `w`. |
| `Crush/Design.lean` | Any way of putting each input on `r` distinct items is a probability on `r`-subsets. Its inclusion probabilities add up to `r` and none exceeds 1, so no placement can give an item more than `1/r` of the data. |
| `Crush/Existence.lean` | The converse: for any inclusion probabilities in `[0, 1]` that add up to `r`, a placement exists. Hence: data in proportion to the weights is possible **iff** no item has more than `1/r` of the weight (`Crush.Design.exists_proportional_iff`). |

No `sorry`; the theorems depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

Not proved here: anything probabilistic about CRUSH itself (that straw2 picks
in proportion to the weights needs a model of the hash), the multi-pick
anomaly, that the weight-set solvers converge, and anything about `mapper.c`.

    lake exe cache get && lake build

Copyright (c) 2026 Clyso Technologies Inc. LGPL-2.1.
