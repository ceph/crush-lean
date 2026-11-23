/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.Gumbel

/-!
# CRUSH's draw-and-retry, and what is left to prove

A rule that picks `r` distinct items from a bucket draws an item with
probability in proportion to the weights, and draws again if the item was
picked before. A draw that is repeated until it gives a new item is a draw
among the items not yet picked, in proportion to their weights. So:

* `Crush.seqIncl w r S i`: the probability that `i` is among `r` items picked
  that way from the set `S` with weights `w`.

`Crush.exists_inclusion_eq_gumbel` is about another description: give item
`i` the value `log (w i)` plus an independent Gumbel variable and take the `r`
largest. That the two agree is the classical fact that the order in which
independent exponential clocks ring is the order of successive draws in
proportion to their rates. It is stated here as `Crush.ClockBridge` and proved
in `Crush/Bridge.lean`. `Crush.exists_weights_of_clockBridge` is what follows
from it: weights for every interior set of inclusion probabilities.
-/

namespace Crush

open Finset MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability that `i` is among `r` items picked one after the other from
`S`, each in proportion to the weights `w` among the items not yet picked. -/
noncomputable def seqIncl (w : ι → ℝ) : ℕ → Finset ι → ι → ℝ
  | 0, _, _ => 0
  | r + 1, S, i =>
    if i ∈ S then
      w i / (∑ k ∈ S, w k) + ∑ j ∈ S.erase i, w j / (∑ k ∈ S, w k) * seqIncl w r (S.erase j) i
    else 0

/-- One pick is in proportion to the weights. -/
theorem seqIncl_one (w : ι → ℝ) (S : Finset ι) {i : ι} (hi : i ∈ S) :
    seqIncl w 1 S i = w i / ∑ k ∈ S, w k := by
  simp [seqIncl, hi]

theorem seqIncl_of_notMem (w : ι → ℝ) (r : ℕ) (S : Finset ι) {i : ι} (hi : i ∉ S) :
    seqIncl w r S i = 0 := by
  cases r <;> simp [seqIncl, hi]

/-- With positive weights these are probabilities: not negative. -/
theorem seqIncl_nonneg {w : ι → ℝ} (hw : ∀ i, 0 < w i) (r : ℕ) (S : Finset ι) (i : ι) :
    0 ≤ seqIncl w r S i := by
  induction r generalizing S with
  | zero => simp [seqIncl]
  | succ r ih =>
    by_cases hi : i ∈ S
    · have hS : 0 < ∑ k ∈ S, w k := Finset.sum_pos (fun k _ => hw k) ⟨i, hi⟩
      simp only [seqIncl, hi, if_true]
      refine add_nonneg (div_nonneg (hw i).le hS.le) (Finset.sum_nonneg fun j _ => ?_)
      exact mul_nonneg (div_nonneg (hw j).le hS.le) (ih (S.erase j))
    · simp [seqIncl, hi]

/-- **Not proved.** The `r` largest of `θ i` plus independent Gumbel values are
the items of `r` successive draws in proportion to `exp (θ i)`. -/
def ClockBridge (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (r : ℕ) (θ : ι → ℝ) (i : ι), r ≤ Fintype.card ι →
    inclusion (Measure.pi fun _ : ι => gumbel) (fun ω : ι → ℝ => ω) r θ i =
      seqIncl (fun k => Real.exp (θ k)) r univ i

/-- **Flat weights exist for every interior set of shares, given the bridge.**
If the two descriptions of the choice agree, then for inclusion probabilities
`π` strictly between 0 and 1 that add up to `r` there are positive weights
with which draw-and-retry picks item `i` with probability `π i`. -/
theorem exists_weights_of_clockBridge (hb : ClockBridge ι) {r : ℕ} (π : ι → ℝ)
    (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1) (hsum : ∑ i, π i = r) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ i, seqIncl w r univ i = π i := by
  obtain ⟨θ, hθ⟩ := exists_inclusion_eq_gumbel π h0 h1 hsum
  have hr : r ≤ Fintype.card ι := by
    have h : (r : ℝ) ≤ Fintype.card ι := by
      rw [← hsum]
      calc ∑ i, π i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (h1 i).le
        _ = Fintype.card ι := by simp
    exact_mod_cast h
  exact ⟨fun k => Real.exp (θ k), fun k => Real.exp_pos _, fun i => by
    rw [← hb r θ i hr, hθ i]⟩

end Crush
