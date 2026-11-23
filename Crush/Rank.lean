/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.TopR

/-!
# The `r` largest, by rank

With distinct values, an item is in the set of `r` items with the largest sum
exactly when fewer than `r` items have a larger value
(`Crush.inTop_iff_card_lt`). This turns the choice into a statement about the
order of the values only, which is what the clock argument needs.
-/

namespace Crush

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

omit [Fintype ι] in
theorem score_insert_erase (v : ι → ℝ) {T : Finset ι} {t k : ι} (ht : t ∈ T) (hk : k ∉ T) :
    score v (insert k (T.erase t)) = score v T - v t + v k := by
  unfold score
  rw [Finset.sum_insert fun h => hk (Finset.mem_of_mem_erase h)]
  have := Finset.add_sum_erase T v ht
  linarith

omit [Fintype ι] in
theorem card_insert_erase {T : Finset ι} {t k : ι} (ht : t ∈ T) (hk : k ∉ T) :
    (insert k (T.erase t)).card = T.card := by
  rw [Finset.card_insert_of_notMem fun h => hk (Finset.mem_of_mem_erase h),
    Finset.card_erase_of_mem ht]
  have := Finset.card_pos.2 ⟨t, ht⟩
  omega

/-- **With distinct values, the chosen items are those with fewer than `r`
larger values.** -/
theorem inTop_iff_card_lt {v : ι → ℝ} (hv : Function.Injective v) (hr : r ≤ Fintype.card ι)
    (i : ι) : inTop r v i ↔ (univ.filter fun k => v i < v k).card < r := by
  have hne : (rsets ι r).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simpa using hr
  constructor
  · rintro ⟨T, ⟨hT, hmax⟩, hiT⟩
    by_contra hcon
    push Not at hcon
    have hTcard := (Finset.mem_powersetCard.1 hT).2
    -- a larger item outside `T` could replace `i`
    obtain ⟨u, huU, huT⟩ : ∃ u ∈ univ.filter (fun k => v i < v k), u ∉ T := by
      by_contra h
      push Not at h
      have hsub : (univ.filter fun k => v i < v k) ⊆ T.erase i := fun k hk =>
        Finset.mem_erase.2 ⟨fun hki => by
          rw [hki] at hk
          exact lt_irrefl _ (Finset.mem_filter.1 hk).2, h k hk⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hiT, hTcard] at hle
      have hrpos : 0 < r := by
        rw [← hTcard]
        exact Finset.card_pos.2 ⟨i, hiT⟩
      omega
    have hlt : v i < v u := (Finset.mem_filter.1 huU).2
    have hT' : insert u (T.erase i) ∈ rsets ι r :=
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, by rw [card_insert_erase hiT huT, hTcard]⟩
    have := hmax _ hT'
    rw [score_insert_erase v hiT huT] at this
    linarith
  · intro hlt
    obtain ⟨T, hT, -⟩ := exists_isTop hne v
    refine ⟨T, hT, ?_⟩
    by_contra hiT
    have hTcard := (Finset.mem_powersetCard.1 hT.1).2
    -- otherwise `i` could replace a smaller item of `T`
    obtain ⟨t, htT, hti⟩ : ∃ t ∈ T, v t < v i := by
      by_contra h
      push Not at h
      have hsub : T ⊆ univ.filter fun k => v i < v k := fun t ht =>
        Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne (h t ht) fun heq =>
          hiT (by rw [hv heq]; exact ht)⟩
      have hle := Finset.card_le_card hsub
      omega
    have hT' : insert i (T.erase t) ∈ rsets ι r :=
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, by rw [card_insert_erase htT hiT, hTcard]⟩
    have := hT.2 _ hT'
    rw [score_insert_erase v htT hiT] at this
    linarith

end Crush
