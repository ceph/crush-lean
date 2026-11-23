# The proof, in words

This is a reader's guide to what the Lean files prove and how. It follows the
order of the argument, not the order of the files. Every statement marked
**(Lean: `name`)** is machine-checked; anything else is commentary.

## 1. The setting

A CRUSH rule that picks `r` distinct items from a bucket (hosts in a root,
OSDs in a host) does this for every input (a placement group):

1. draw one item, with probability in proportion to the weights `w`;
2. if that item was drawn before for this input, draw again;
3. repeat until there are `r` items.

A draw that is repeated until it gives a new item is a draw among the items
not yet picked, in proportion to their weights. This is *successive sampling
without replacement*. The Lean definition is recursive:

```lean
def seqIncl (w : ι → ℝ) : ℕ → Finset ι → ι → ℝ
  | 0, _, _ => 0
  | r + 1, S, i =>
    if i ∈ S then
      w i / (∑ k ∈ S, w k) + ∑ j ∈ S.erase i, w j / (∑ k ∈ S, w k) * seqIncl w r (S.erase j) i
    else 0
```

`seqIncl w r S i` is the probability that item `i` is among `r` items picked
this way from the set `S`: either `i` is picked first, or some other `j` is
picked first and `i` is among the next `r - 1` picks from `S` without `j`.
This number is the share of the data that `i` receives, times `r`. We call it
the *inclusion probability* of `i`.

**Idealisation.** The hash is treated as a source of independent random
draws. Nothing here is about the C code, its fixed-point logarithm table, or
its retry limits.

## 2. The multi-pick anomaly

For one pick, `seqIncl w 1 S i = w i / W` **(Lean: `seqIncl_one`)**: data in
proportion to weight. For `r > 1` it is not `r * w i / W`. With weights
`[3, 3, 3, 1]` and three picks, the small item gets about 1.4 times its
share, because every time a large item is picked first the small one competes
for the next pick against a smaller total. This has been known since 2016
(https://tracker.ceph.com/issues/15653).

The fix is to draw with other weights `w'` than the ones we want the data to
follow (a *weight-set*). Two questions come first:

* **Which shares can any placement give at all?** (Section 3.)
* **Are there always weights `w'` with which draw-and-retry gives them?**
  (Sections 4 to 7; this is the main theorem.)

## 3. Which shares are possible

Forget CRUSH. Any rule that puts each input on `r` distinct items is, in
distribution, a probability `p` on the sets of `r` items
**(Lean: `Design`)**. Its inclusion probabilities `π i = ∑ p S` over the sets
containing `i` satisfy `0 ≤ π i ≤ 1` and `∑ π i = r`
**(Lean: `Design.incl_le_one`, `Design.sum_incl`)**. So no rule whatsoever
can give an item more than `1 / r` of the data: with three replicas, a host
with 40% of the weight cannot hold 40% of the data.

Conversely, every `π` with `0 ≤ π i ≤ 1` and `∑ π i = r` is the inclusion
probability of some `p` **(Lean: `Design.exists_of_incl`)**. The proof is by
induction on the number of items whose `π` is strictly between 0 and 1. Take
two such items and move probability from one to the other, in both
directions, until one of them hits 0 or 1. `π` is a mixture of the two end
points, each of which has fewer fractional items; when none is left, `π` is
the indicator of a set of `r` items.

Together **(Lean: `Design.exists_proportional_iff`)**:

> A placement with data in proportion to the weights exists **if and only
> if** no item has more than `1 / r` of the weight.

This also settles when the linear system of the 2017 "matrix method" (one
unknown per replica set, one equation per item) has a non-negative solution.

## 4. Draw-and-retry as a race of clocks

Give item `k` a clock that rings at time `E k / w k`, where the `E k` are
independent exponential variables with rate 1. (straw2 does exactly this for
one draw: its straw `ln(u) / w` is minus such a ring time, and the longest
straw is the first clock to ring.)

Two facts about exponential clocks carry the whole section.

* **Memorylessness** **(Lean: `expMeasure_shift`, `pi_shift`)**: given that
  none of a family of clocks has rung by time `t`, the times that remain are
  again independent exponentials. In Lean this is a statement about the
  product measure: the event "`E k > a k` for all `k`, and `E - a` is in `C`"
  has probability `exp (-∑ a k)` times the probability of `C`. It is proved on
  boxes, where it is the one-dimensional statement in each coordinate, and
  extended by uniqueness of the product measure.
* **The first to ring** **(Lean: `clocks_firstIn_inter`)**: clock `j` rings
  first among a set `S` with probability `w j / ∑ k ∈ S, w k`, *independently*
  of any event `B` that only concerns the order in which the other clocks of
  `S` ring afterwards. Proof: fix the ring time `t` of clock `j`
  (`pi_eq_lintegral_update`, Fubini for one coordinate). The others must all
  ring after `t`; by memorylessness that costs a factor
  `exp (-t * W' / w j)`, with `W'` the weight of the others, and leaves `B`
  with its probability. Integrating that factor over `t` gives
  `1 / (1 + W' / w j) = w j / W` (`lintegral_exp_neg_mul`).

Now let `early S n i` be the event that fewer than `n` clocks of `S` ring
before clock `i`. Split by which clock of `S` rings first (these events are
disjoint and their probabilities add up to 1). If it is `i`, the event holds.
If it is another `j`, then one clock is before `i` already, and the event
becomes "fewer than `n - 1` clocks of `S` without `j` ring before `i`", which
is an event `B` as above. This is the recursion that defines `seqIncl`, so by
induction on `n` **(Lean: `clocks_early`)**:

> P(fewer than `n` clocks of `S` ring before clock `i`) = `seqIncl w n S i`.

## 5. The same race, as "the `r` largest"

Take minus the logarithm of the ring times:
`-log (E k / w k) = θ k + G k`, with `θ k = log (w k)` and `G k = -log (E k)`.
The `G k` are independent Gumbel variables **(Lean: `gumbel`)**. The first
`r` clocks to ring are the `r` largest values of `θ k + G k`. When the values
are distinct, which has probability 1, "`i` is in the set of `r` items with
the largest sum" is the same as "fewer than `r` items have a larger value
than `i`" **(Lean: `inTop_iff_card_lt`)**. So **(Lean: `clockBridge`)**:

> P(`i` is among the `r` largest of `θ k + G k`) = `seqIncl (exp ∘ θ) r univ i`.

This is why it is worth changing the description: "the `r` largest of
`θ + G`" is an optimisation problem, and optimisation problems have
potentials.

## 6. A potential whose gradient is the inclusion probabilities

For a vector `v`, let `topSum v` be the largest sum of `v` over a set of `r`
items. For fixed `G`, the function `θ ↦ topSum (θ + G)` is a maximum of
linear functions, so it is convex, and where the maximising set `T` is unique
its indicator is a subgradient:
`topSum (θ + h + G) ≥ topSum (θ + G) + ∑ i ∈ T, h i`
**(Lean: `score_le_topSum`, `topSum_add_le`)**.

Take expectations: `Φ θ = E topSum (θ + G)` **(Lean: `potential`)**, and
`incl θ i = P(i is among the r largest)` **(Lean: `inclusion`)**. If ties
have probability 0 and `G` is integrable:

| Property | Lean |
|---|---|
| `Φ (θ + h) ≥ Φ θ + ∑ incl θ i * h i` (the inclusion probabilities are a subgradient) | `potential_add_le` |
| `Φ (θ + c) = Φ θ + r * c` (scaling all weights changes nothing) | `potential_add_const` |
| `Φ θ ≥ ∑ i ∈ S, θ i - C` for every set `S` of `r` items | `sum_sub_le_potential` |
| `Φ` is continuous (Lipschitz) | `continuous_potential` |
| `incl` is continuous (dominated convergence; no ties) | `continuous_inclusion` |

Independent variables with a common law that has no point masses almost
never tie **(Lean: `ae_noTies`)**, and the Gumbel law is such a law and has a
mean **(Lean: `integrable_id_gumbel`)**.

## 7. Minimising

Let `π` be the target: `0 < π i < 1`, `∑ π i = r`. Consider
`F θ = Φ θ - ∑ π i * θ i` **(Lean: `exists_incl_eq`)**.

* `F` does not change when a constant is added to every `θ i`, because
  `∑ π i = r`. So we may assume the smallest `θ i` is 0.
* `F` grows when the `θ i` spread out: with `ε ≤ π i ≤ 1 - ε`,
  `F θ ≥ ε * (θ a - θ b) - C` for any two items `a`, `b`
  (`sum_mul_add_le`; this is where `π` being strictly inside is used, and it
  uses Section 3 to write `π` as a mixture of sets of `r` items).
* So outside a large box `F` is larger than `F 0`, and on the box the
  continuous `F` has a minimum `θ₀`, which is then a minimum everywhere.
* At a minimum the subgradient is `π`. For a step `t` in the direction of
  item `i`, the subgradient inequality at `θ₀ + t` and minimality at `θ₀`
  give `(π i - incl (θ₀ + t) i) * t ≤ 0` for both signs of `t`; letting
  `t → 0` and using continuity of `incl` gives `incl θ₀ i = π i`.

With Section 5, the weights `w i = exp (θ₀ i)` are what we wanted.

## 8. The theorem

```lean
theorem exists_weights {r : ℕ} (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1)
    (hsum : ∑ i, π i = r) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ i, seqIncl w r Finset.univ i = π i
```

> For any shares strictly between 0 and `1 / r` of the data each, there are
> positive weights with which draw-and-retry gives every item exactly its
> share.

With Section 3: the multi-pick anomaly can be corrected by a weight-set
whenever it can be corrected at all, except possibly on the boundary where an
item has exactly `1 / r` of the weight.

## 9. What is not proved

* **Uniqueness.** One expects the weights to be unique up to a common factor
  (the potential should be strictly convex apart from that direction). This
  is neither proved nor formalised here.
* **The boundary**, `π i = 1` for some item: it needs an infinite weight
  ratio, so no finite weights exist there; not formalised.
* **Positional weight-sets** (a different weight per replica position, which
  also makes the *order* of the replicas right, as needed for primaries).
* **Hierarchies.** The theorem is about one bucket. A rule that descends
  through several levels applies it at the level where it picks `r` items.
* **The joint law.** Only inclusion probabilities are shown to agree between
  the clock race and draw-and-retry, which is all the theorem needs. The full
  statement (the same distribution over ordered `r`-tuples) is true and not
  formalised.
* **Any algorithm.** The proof is not constructive in a useful way; it says a
  solver has something to find, not that a given iteration converges to it.
* **The implementation**: hashes, the fixed-point `ln` table, retries.

## 10. Separately: straw2 moves only what it must

`Crush/Straw2.lean` is independent of the above. For straw2 selection (each
item gets a straw that depends on the input, the item and the item's own
weight; the longest wins): if one item's straw gets longer, every input keeps
its item or moves to that item, and if it gets shorter only inputs on that
item move **(Lean: `Wins.of_longer`, `Wins.of_shorter`)**. The straw
`log u / w` grows with `w` **(Lean: `straw2_draw_le`)**, so this applies to a
weight change **(Lean: `Chooses.of_weight_le`, `Chooses.of_le_weight`)**. It
holds for every input and every hash value, not just on average.
