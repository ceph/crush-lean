/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Mathlib

/-!
# Which shares can a placement give its items?

A rule that picks `r` distinct items of a bucket for every input puts each
input on a set of `r` items. However the sets are chosen, by CRUSH with any
weights or weight-sets, or by any other method, the outcome is a probability
on the `r`-subsets of the items: a `Crush.Design`.

The *inclusion probability* of an item is the probability that it is in the
chosen set; `r` times its share of the data. This file proves what no
placement can avoid:

* `Crush.Design.sum_incl`: the inclusion probabilities add up to `r`;
* `Crush.Design.incl_le_one`: none exceeds 1;
* `Crush.Design.weight_le_of_proportional`: so if every item holds data in
  proportion to its weight, no item has more than `1 / r` of the weight.

That is the condition under which the weight-set solvers give up, and under
which the placement of the 2017 "matrix method" has no solution.
-/

namespace Crush

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A probability on the sets of `r` items. -/
structure Design (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) where
  /-- the probability of each set -/
  p : Finset ι → ℝ
  nonneg : ∀ S, 0 ≤ p S
  card_eq : ∀ S, p S ≠ 0 → S.card = r
  sum_eq_one : ∑ S, p S = 1

namespace Design

variable {r : ℕ} (d : Design ι r)

/-- The probability that item `i` is in the chosen set. -/
def incl (i : ι) : ℝ := ∑ S, if i ∈ S then d.p S else 0

theorem incl_nonneg (i : ι) : 0 ≤ d.incl i :=
  Finset.sum_nonneg fun S _ => by split_ifs <;> simp [d.nonneg S]

/-- No item is chosen with a probability above 1. -/
theorem incl_le_one (i : ι) : d.incl i ≤ 1 := by
  rw [← d.sum_eq_one]
  exact Finset.sum_le_sum fun S _ => by split_ifs <;> simp [d.nonneg S]

/-- The inclusion probabilities add up to the number of picks. -/
theorem sum_incl : ∑ i, d.incl i = r := by
  unfold incl
  rw [Finset.sum_comm]
  have h : ∀ S : Finset ι, (∑ i, if i ∈ S then d.p S else 0) = r * d.p S := by
    intro S
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    by_cases hS : d.p S = 0
    · simp [hS]
    · rw [d.card_eq S hS]
  simp_rw [h]
  rw [← Finset.mul_sum, d.sum_eq_one, mul_one]

/-- **No placement can give an item more than `1 / r` of the data.** If the
items hold data in proportion to weights `w`, i.e. item `i` is in the chosen
set with probability `r * w i / W`, then `r * w i ≤ W` for every item. -/
theorem weight_le_of_proportional {w : ι → ℝ} (hW : 0 < ∑ i, w i)
    (h : ∀ i, d.incl i = r * w i / ∑ j, w j) (i : ι) :
    r * w i ≤ ∑ j, w j := by
  have := d.incl_le_one i
  rw [h i, div_le_one hW] at this
  exact this

end Design

end Crush
