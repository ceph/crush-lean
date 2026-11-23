/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.Potential

/-!
# The `r` largest: the deterministic part

Choosing the `r` items with the largest values of `v` is choosing the set of
`r` items with the largest sum. This file has what is needed about that choice
for one `v`, before any probability:

* `Crush.topSum r v`: the largest sum of `v` over a set of `r` items;
* `Crush.inTop r v i`: `i` is in a set that attains it;
* `Crush.topSum_add_le`: if only one set attains it at `v` (no ties), then
  `topSum r v + ∑ i with inTop r v i, h i ≤ topSum r (v + h)`: the chosen set
  is a subgradient of `topSum`;
* bounds and the effect of adding a constant.
-/

namespace Crush

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sets of `r` items. -/
abbrev rsets (ι : Type*) [Fintype ι] (r : ℕ) : Finset (Finset ι) := powersetCard r univ

/-- The sum of `v` over a set. -/
def score (v : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, v i

/-- The largest sum of `v` over a set of `r` items. -/
noncomputable def topSum (r : ℕ) (hr : (rsets ι r).Nonempty) (v : ι → ℝ) : ℝ :=
  (rsets ι r).sup' hr (score v)

/-- `S` is a set of `r` items with the largest sum. -/
def IsTop (r : ℕ) (v : ι → ℝ) (S : Finset ι) : Prop :=
  S ∈ rsets ι r ∧ ∀ T ∈ rsets ι r, score v T ≤ score v S

/-- `i` is in a set of `r` items with the largest sum. -/
def inTop (r : ℕ) (v : ι → ℝ) (i : ι) : Prop := ∃ S, IsTop r v S ∧ i ∈ S

/-- No two sets of `r` items have the same sum. -/
def NoTies (r : ℕ) (v : ι → ℝ) : Prop :=
  ∀ S ∈ rsets ι r, ∀ T ∈ rsets ι r, S ≠ T → score v S ≠ score v T

variable {r : ℕ} (hr : (rsets ι r).Nonempty)

omit [DecidableEq ι] in
theorem exists_isTop (v : ι → ℝ) : ∃ S, IsTop r v S ∧ score v S = topSum r hr v := by
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (rsets ι r) (score v) hr
  refine ⟨S, ⟨hS, hmax⟩, le_antisymm (Finset.le_sup' (score v) hS) ?_⟩
  exact Finset.sup'_le hr (score v) hmax

omit [DecidableEq ι] in
theorem score_le_topSum (v : ι → ℝ) {S : Finset ι} (hS : S ∈ rsets ι r) :
    score v S ≤ topSum r hr v :=
  Finset.le_sup' (score v) hS

omit [Fintype ι] [DecidableEq ι] in
theorem score_add (v h : ι → ℝ) (S : Finset ι) : score (v + h) S = score v S + score h S := by
  simp [score, Finset.sum_add_distrib]

open scoped Classical in
/-- **The chosen set is a subgradient of the largest sum**, where it is the
only choice. -/
theorem topSum_add_le {v : ι → ℝ} (hv : NoTies r v) (h : ι → ℝ) :
    topSum r hr v + ∑ i, (if inTop r v i then h i else 0) ≤ topSum r hr (v + h) := by
  obtain ⟨S, hS, hSv⟩ := exists_isTop hr v
  have hiff : ∀ i, inTop r v i ↔ i ∈ S := by
    intro i
    constructor
    · rintro ⟨T, hT, hiT⟩
      by_contra hiS
      have hne : T ≠ S := fun h => hiS (h ▸ hiT)
      exact hv T hT.1 S hS.1 hne (le_antisymm (hS.2 T hT.1) (hT.2 S hS.1))
    · exact fun hi => ⟨S, hS, hi⟩
  have hsum : ∑ i, (if inTop r v i then h i else 0) = score h S := by
    simp_rw [hiff]
    rw [Finset.sum_ite_mem, Finset.univ_inter, score]
  rw [hsum, ← hSv, ← score_add]
  exact score_le_topSum hr (v + h) hS.1

omit [DecidableEq ι] in
/-- Adding `c` to every value adds `r * c`. -/
theorem topSum_add_const (v : ι → ℝ) (c : ℝ) :
    topSum r hr (fun i => v i + c) = topSum r hr v + r * c := by
  have hsc : ∀ S ∈ rsets ι r, score (fun i => v i + c) S = score v S + r * c := by
    intro S hS
    simp [score, Finset.sum_add_distrib, (Finset.mem_powersetCard.1 hS).2]
  unfold topSum
  apply le_antisymm
  · refine Finset.sup'_le hr _ fun S hS => ?_
    rw [hsc S hS]
    linarith [Finset.le_sup' (score v) hS]
  · obtain ⟨S, hS, hSv⟩ := exists_isTop hr v
    unfold topSum at hSv
    rw [← hSv, ← hsc S hS.1]
    exact Finset.le_sup' (score fun i => v i + c) hS.1

omit [DecidableEq ι] in
/-- The largest sum moves by at most the total change of the values. -/
theorem topSum_sub_le (v w : ι → ℝ) : topSum r hr v - topSum r hr w ≤ ∑ i, |v i - w i| := by
  obtain ⟨S, hS, hSv⟩ := exists_isTop hr v
  have h1 := score_le_topSum hr w hS.1
  have h2 : score v S - score w S ≤ ∑ i, |v i - w i| := by
    unfold score
    rw [← Finset.sum_sub_distrib]
    calc ∑ i ∈ S, (v i - w i) ≤ ∑ i ∈ S, |v i - w i| :=
          Finset.sum_le_sum fun i _ => le_abs_self _
      _ ≤ ∑ i, |v i - w i| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => abs_nonneg _
  linarith

end Crush
