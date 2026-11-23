/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.Design

/-!
# Every feasible set of shares has a placement

`Crush.Design.exists_of_incl`: for inclusion probabilities `π` between 0 and 1
that add up to `r`, there is a probability on the `r`-subsets of the items
with exactly those inclusion probabilities.

Together with `Crush.Design.incl_le_one` and `Crush.Design.sum_incl` this
settles which shares a placement can give: exactly those where no item has
more than `1 / r` of the data. In the terms of the 2017 "matrix method" for
placing PGs on weighted items: the linear system `A x = B` over the replica
sets has a solution with non-negative `x` if and only if no item has more than
`1 / r` of the weight. No heuristic constraints are needed for that; they only
select one of the solutions.

The proof moves weight between two items whose probability is strictly between
0 and 1, in both directions, until one of them reaches 0 or 1; `π` is a mixture
of the two results, and each has fewer such items.
-/

namespace Crush

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Design

variable {r : ℕ}

/-- The design that always chooses the set `S`. -/
def point (S : Finset ι) (hS : S.card = r) : Design ι r where
  p T := if T = S then 1 else 0
  nonneg T := by split_ifs <;> norm_num
  card_eq T h := by
    by_cases hT : T = S
    · rw [hT, hS]
    · simp [hT] at h
  sum_eq_one := by simp

theorem incl_point (S : Finset ι) (hS : S.card = r) (i : ι) :
    (point S hS).incl i = if i ∈ S then 1 else 0 := by
  unfold incl point
  simp only
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hT
    simp [hT]
  · simp

/-- Choose with `d₁` with probability `t`, and with `d₂` otherwise. -/
def mix (d₁ d₂ : Design ι r) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Design ι r where
  p S := t * d₁.p S + (1 - t) * d₂.p S
  nonneg S := add_nonneg (mul_nonneg ht0 (d₁.nonneg S))
    (mul_nonneg (sub_nonneg.2 ht1) (d₂.nonneg S))
  card_eq S h := by
    by_contra hc
    have h1 : d₁.p S = 0 := by_contra fun h' => hc (d₁.card_eq S h')
    have h2 : d₂.p S = 0 := by_contra fun h' => hc (d₂.card_eq S h')
    exact h (by simp [h1, h2])
  sum_eq_one := by
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, d₁.sum_eq_one, d₂.sum_eq_one]

theorem incl_mix (d₁ d₂ : Design ι r) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : ι) :
    (mix d₁ d₂ t ht0 ht1).incl i = t * d₁.incl i + (1 - t) * d₂.incl i := by
  unfold incl mix
  simp only
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs <;> ring

end Design

/-- The items whose probability is strictly between 0 and 1. -/
noncomputable def frac (π : ι → ℝ) : Finset ι := univ.filter fun i => 0 < π i ∧ π i < 1

omit [DecidableEq ι] in
theorem mem_frac {π : ι → ℝ} {i : ι} : i ∈ frac π ↔ 0 < π i ∧ π i < 1 := by
  simp [frac]

omit [DecidableEq ι] in
/-- Outside `frac π` a probability is 0 or 1. -/
theorem eq_zero_or_one_of_not_mem_frac {π : ι → ℝ} (h0 : ∀ i, 0 ≤ π i) (h1 : ∀ i, π i ≤ 1)
    {i : ι} (hi : i ∉ frac π) : π i = 0 ∨ π i = 1 := by
  rw [mem_frac, not_and_or, not_lt, not_lt] at hi
  rcases hi with h | h
  · exact Or.inl (le_antisymm h (h0 i))
  · exact Or.inr (le_antisymm (h1 i) h)

omit [Fintype ι] [DecidableEq ι] in
/-- A sum of zeros and ones is the number of ones. -/
theorem sum_eq_card_of_zero_or_one (s : Finset ι) (π : ι → ℝ)
    (h : ∀ i ∈ s, π i = 0 ∨ π i = 1) :
    ∑ i ∈ s, π i = ((s.filter fun i => π i = 1).card : ℝ) := by
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases h i hi with h | h <;> simp [h]

/-- **Every feasible set of inclusion probabilities has a placement.** -/
theorem Design.exists_of_incl {r : ℕ} (π : ι → ℝ) (h0 : ∀ i, 0 ≤ π i) (h1 : ∀ i, π i ≤ 1)
    (hsum : ∑ i, π i = r) : ∃ d : Design ι r, ∀ i, d.incl i = π i := by
  induction' hn : (frac π).card using Nat.strong_induction_on with n ih generalizing π
  by_cases hF : frac π = ∅
  · -- every probability is 0 or 1: always choose the items that have 1
    have h01 : ∀ i, π i = 0 ∨ π i = 1 := fun i =>
      eq_zero_or_one_of_not_mem_frac h0 h1 (by simp [hF])
    have hcard : (univ.filter fun i => π i = 1).card = r := by
      have := sum_eq_card_of_zero_or_one univ π fun i _ => h01 i
      rw [hsum] at this
      exact_mod_cast this.symm
    refine ⟨Design.point _ hcard, fun i => ?_⟩
    rw [Design.incl_point]
    rcases h01 i with h | h <;> simp [h]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hF
    -- a second such item: otherwise the sum would not be a whole number
    have hb : ∃ b ∈ frac π, b ≠ a := by
      by_contra hcon
      push Not at hcon
      have hrest : ∀ i ∈ univ.erase a, π i = 0 ∨ π i = 1 := fun i hi =>
        eq_zero_or_one_of_not_mem_frac h0 h1 fun hfi =>
          (Finset.mem_erase.1 hi).1 (hcon i hfi)
      have hsplit := Finset.add_sum_erase univ π (Finset.mem_univ a)
      rw [sum_eq_card_of_zero_or_one _ π hrest, hsum] at hsplit
      obtain ⟨ha0, ha1⟩ := mem_frac.1 ha
      set m := ((univ.erase a).filter fun i => π i = 1).card
      have hz : π a = ((r : ℤ) - (m : ℤ) : ℤ) := by push_cast; linarith
      rw [hz] at ha0 ha1
      have h0' : (0 : ℤ) < (r : ℤ) - m := by exact_mod_cast ha0
      have h1' : (r : ℤ) - m < 1 := by exact_mod_cast ha1
      omega
    obtain ⟨b, hb, hba⟩ := hb
    obtain ⟨ha0, ha1⟩ := mem_frac.1 ha
    obtain ⟨hb0, hb1⟩ := mem_frac.1 hb
    -- move weight from `b` to `a` (`δ`), by `e₁` forwards and by `e₂` backwards
    set δ : ι → ℝ := fun i => (if i = a then 1 else 0) - (if i = b then 1 else 0) with hδ
    have hδa : δ a = 1 := by simp [hδ, hba.symm]
    have hδb : δ b = -1 := by simp [hδ, hba]
    have hδo : ∀ i, i ≠ a → i ≠ b → δ i = 0 := fun i hia hib => by simp [hδ, hia, hib]
    have hδsum : ∑ i, δ i = 0 := by simp [hδ]
    set e₁ := min (1 - π a) (π b) with he₁
    set e₂ := min (π a) (1 - π b) with he₂
    have he₁pos : 0 < e₁ := lt_min (by linarith) hb0
    have he₂pos : 0 < e₂ := lt_min ha0 (by linarith)
    have he₁a : e₁ ≤ 1 - π a := min_le_left _ _
    have he₁b : e₁ ≤ π b := min_le_right _ _
    have he₂a : e₂ ≤ π a := min_le_left _ _
    have he₂b : e₂ ≤ 1 - π b := min_le_right _ _
    -- the two ends, and what is needed to apply the induction hypothesis to them
    have key : ∀ (e : ℝ) (π' : ι → ℝ), (∀ i, π' i = π i + e * δ i) →
        0 ≤ π a + e → π a + e ≤ 1 → 0 ≤ π b - e → π b - e ≤ 1 →
        (π a + e = 1 ∨ π a + e = 0 ∨ π b - e = 0 ∨ π b - e = 1) →
        ∃ d : Design ι r, ∀ i, d.incl i = π' i := by
      intro e π' hπ' hal hau hbl hbu hend
      have hval : ∀ i, i ≠ a → i ≠ b → π' i = π i := fun i hia hib => by
        rw [hπ', hδo i hia hib]; ring
      have hπ'a : π' a = π a + e := by rw [hπ', hδa]; ring
      have hπ'b : π' b = π b - e := by rw [hπ', hδb]; ring
      refine ih (frac π').card ?_ π' ?_ ?_ ?_ rfl
      · -- fewer items strictly between 0 and 1
        rw [← hn]
        have hsub : frac π' ⊆ frac π := fun i hi => by
          by_cases hia : i = a
          · rw [hia]; exact ha
          by_cases hib : i = b
          · rw [hib]; exact hb
          rw [mem_frac] at hi ⊢
          rwa [hval i hia hib] at hi
        have hne : ∃ c ∈ frac π, c ∉ frac π' := by
          rcases hend with h | h | h | h
          · exact ⟨a, ha, fun hc => by rw [mem_frac, hπ'a, h] at hc; exact lt_irrefl _ hc.2⟩
          · exact ⟨a, ha, fun hc => by rw [mem_frac, hπ'a, h] at hc; exact lt_irrefl _ hc.1⟩
          · exact ⟨b, hb, fun hc => by rw [mem_frac, hπ'b, h] at hc; exact lt_irrefl _ hc.1⟩
          · exact ⟨b, hb, fun hc => by rw [mem_frac, hπ'b, h] at hc; exact lt_irrefl _ hc.2⟩
        obtain ⟨c, hc, hc'⟩ := hne
        exact Finset.card_lt_card ⟨hsub, fun h => hc' (h hc)⟩
      · intro i
        by_cases hia : i = a
        · rw [hia, hπ'a]; exact hal
        by_cases hib : i = b
        · rw [hib, hπ'b]; exact hbl
        rw [hval i hia hib]; exact h0 i
      · intro i
        by_cases hia : i = a
        · rw [hia, hπ'a]; exact hau
        by_cases hib : i = b
        · rw [hib, hπ'b]; exact hbu
        rw [hval i hia hib]; exact h1 i
      · simp_rw [hπ']
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hδsum, mul_zero, add_zero, hsum]
    obtain ⟨d₁, hd₁⟩ := key e₁ (fun i => π i + e₁ * δ i) (fun _ => rfl)
      (by linarith) (by linarith) (by linarith) (by linarith) (by
        rcases min_choice (1 - π a) (π b) with h | h
        · left; rw [he₁, h]; ring
        · right; right; left; rw [he₁, h]; ring)
    obtain ⟨d₂, hd₂⟩ := key (-e₂) (fun i => π i + -e₂ * δ i) (fun _ => rfl)
      (by linarith) (by linarith) (by linarith) (by linarith) (by
        rcases min_choice (π a) (1 - π b) with h | h
        · right; left; rw [he₂, h]; ring
        · right; right; right; rw [he₂, h]; ring)
    -- `π` is between the two
    have hpos : 0 < e₁ + e₂ := by linarith
    have ht0 : 0 ≤ e₂ / (e₁ + e₂) := div_nonneg he₂pos.le hpos.le
    have ht1 : e₂ / (e₁ + e₂) ≤ 1 := (div_le_one hpos).2 (by linarith)
    refine ⟨Design.mix d₁ d₂ _ ht0 ht1, fun i => ?_⟩
    rw [Design.incl_mix, hd₁, hd₂]
    field_simp
    ring

/-- **A placement with data in proportion to the weights exists if and only if
no item has more than `1 / r` of the weight**, for non-negative weights that
are not all zero. -/
theorem Design.exists_proportional_iff {r : ℕ} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hW : 0 < ∑ i, w i) :
    (∃ d : Design ι r, ∀ i, d.incl i = r * w i / ∑ j, w j) ↔ ∀ i, r * w i ≤ ∑ j, w j := by
  constructor
  · rintro ⟨d, hd⟩ i
    exact d.weight_le_of_proportional hW hd i
  · intro h
    refine Design.exists_of_incl _ (fun i => ?_) (fun i => ?_) ?_
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg r) (hw i)) hW.le
    · exact (div_le_one hW).2 (h i)
    · rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc, div_self hW.ne', mul_one]

end Crush
