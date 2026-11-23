/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.Existence

/-!
# Weights for every feasible set of shares: the analytic half

Picking `r` items with one weight per item ("flat" weights) gives each item an
inclusion probability that depends on all the weights. The weight-set solver
looks for weights whose inclusion probabilities are `r * w i / W`. Does such a
solution always exist?

This file proves the part of the answer that is real analysis and has nothing
to do with how the items are picked. Write the weights as `exp (θ i)` and let
`incl θ i` be the inclusion probabilities. Suppose there is a function `Φ`
with

* `Φ θ + ∑ i, incl θ i * h i ≤ Φ (θ + h)`: `incl θ` is a subgradient of `Φ`,
  so `Φ` is convex and `incl` is its gradient where it has one;
* `Φ (θ + c) = Φ θ + r * c`: scaling all weights changes nothing;
* `∑ i ∈ S, θ i - C ≤ Φ θ` for every set `S` of `r` items;
* `Φ` and `incl` are continuous.

Then every `π` strictly between 0 and 1 that adds up to `r` is `incl θ` for
some `θ` (`Crush.exists_incl_eq`). The proof minimises `Φ θ - ∑ i, π i * θ i`.

For a choice by the `r` largest of `θ i + G i` with random `G`, the function
`Φ θ = E (sum of the r largest)` has these properties. Successive sampling, which
is what CRUSH does, is that choice with Gumbel `G`. Neither of the last two
sentences is proved here.
-/

namespace Crush

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `t` at item `i` and 0 elsewhere. -/
def bump (i : ι) (t : ℝ) : ι → ℝ := fun j => if j = i then t else 0

omit [Fintype ι] in
theorem bump_zero (i : ι) : bump i 0 = 0 := by
  funext j; simp [bump]

omit [Fintype ι] in
theorem continuous_bump (i : ι) : Continuous (bump i) :=
  continuous_pi fun j => by
    by_cases h : j = i
    · simp only [bump, h, ite_true]; exact continuous_id
    · simp only [bump, h, ite_false]; exact continuous_const

/-- The expectation of a sum over the chosen set, by item or by set. -/
theorem Design.sum_incl_mul {r : ℕ} (d : Design ι r) (θ : ι → ℝ) :
    ∑ i, d.incl i * θ i = ∑ S, d.p S * ∑ i ∈ S, θ i := by
  unfold Design.incl
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- If `Φv` is at least the sum of `θ` over every set of `r` items, up to `C`,
then it is at least `∑ π i * θ i` for every feasible `π`, and more than that by
`ε * (θ a - θ b)` if `π` stays `ε` away from 0 and 1. -/
theorem sum_mul_add_le {r : ℕ} {π θ : ι → ℝ} {ε C Φv : ℝ}
    (hlo : ∀ i, ε ≤ π i) (hhi : ∀ i, π i ≤ 1 - ε) (hε : 0 ≤ ε) (hsum : ∑ i, π i = r)
    (hΦ : ∀ S : Finset ι, S.card = r → ∑ i ∈ S, θ i - C ≤ Φv) (a b : ι) :
    ∑ i, π i * θ i + ε * (θ a - θ b) - C ≤ Φv := by
  set δ : ι → ℝ := fun i => (if i = a then 1 else 0) - (if i = b then 1 else 0) with hδ
  have hδsum : ∑ i, δ i = 0 := by simp [hδ]
  have hδθ : ∑ i, δ i * θ i = θ a - θ b := by simp [hδ, sub_mul, Finset.sum_sub_distrib]
  have hδlo : ∀ i, -1 ≤ δ i := fun i => by
    simp only [hδ]; split_ifs <;> norm_num
  have hδhi : ∀ i, δ i ≤ 1 := fun i => by
    simp only [hδ]; split_ifs <;> norm_num
  obtain ⟨d, hd⟩ := Design.exists_of_incl (r := r) (fun i => π i + ε * δ i)
    (fun i => by nlinarith [hlo i, hδlo i])
    (fun i => by nlinarith [hhi i, hδhi i])
    (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hδsum, mul_zero, add_zero, hsum])
  have h1 : ∑ i, d.incl i * θ i = ∑ i, π i * θ i + ε * (θ a - θ b) := by
    simp_rw [hd, add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hδθ]
  have h2 : ∑ S, d.p S * ∑ i ∈ S, θ i ≤ ∑ S, d.p S * (Φv + C) := by
    refine Finset.sum_le_sum fun S _ => ?_
    by_cases hS : d.p S = 0
    · simp [hS]
    · exact mul_le_mul_of_nonneg_left (by linarith [hΦ S (d.card_eq S hS)]) (d.nonneg S)
  rw [← Finset.sum_mul, d.sum_eq_one, one_mul, ← d.sum_incl_mul, h1] at h2
  linarith

/-- **Every interior set of shares is reached.** See the header of this file. -/
theorem exists_incl_eq {r : ℕ} (Φ : (ι → ℝ) → ℝ) (incl : (ι → ℝ) → ι → ℝ)
    (hsub : ∀ θ h : ι → ℝ, Φ θ + ∑ i, incl θ i * h i ≤ Φ (θ + h))
    (hshift : ∀ (θ : ι → ℝ) (c : ℝ), Φ (fun i => θ i + c) = Φ θ + r * c)
    (hbelow : ∃ C, ∀ (θ : ι → ℝ) (S : Finset ι), S.card = r → ∑ i ∈ S, θ i - C ≤ Φ θ)
    (hΦ : Continuous Φ) (hincl : Continuous incl)
    (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1) (hsum : ∑ i, π i = r) :
    ∃ θ, ∀ i, incl θ i = π i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ => 0, fun i => (hι.false i).elim⟩
  obtain ⟨C, hC⟩ := hbelow
  -- `π` stays `ε` away from 0 and 1
  obtain ⟨ε, hε, hlo, hhi⟩ : ∃ ε, 0 < ε ∧ (∀ i, ε ≤ π i) ∧ ∀ i, π i ≤ 1 - ε := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image univ π univ_nonempty
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image univ π univ_nonempty
    refine ⟨min (π i₀) (1 - π i₁), lt_min (h0 i₀) (by linarith [h1 i₁]), fun i => ?_, fun i => ?_⟩
    · exact le_trans (min_le_left _ _) (hi₀ i (mem_univ i))
    · have := min_le_right (π i₀) (1 - π i₁)
      linarith [hi₁ i (mem_univ i)]
  -- the function to minimise; it does not change if all weights are scaled
  set F : (ι → ℝ) → ℝ := fun θ => Φ θ - ∑ i, π i * θ i with hF
  have hFc : Continuous F := hΦ.sub (by fun_prop)
  have hFshift : ∀ (θ : ι → ℝ) (c : ℝ), F (fun i => θ i + c) = F θ := fun θ c => by
    simp only [hF, hshift]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
    ring
  have hFgrow : ∀ (θ : ι → ℝ) (a b : ι), ε * (θ a - θ b) - C ≤ F θ := fun θ a b => by
    have := sum_mul_add_le hlo hhi hε.le hsum (hC θ) a b
    simp only [hF]
    linarith
  -- a minimum over a large box
  set M : ℝ := max 0 ((F 0 + C) / ε) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMF : F 0 ≤ ε * M - C := by
    have : (F 0 + C) / ε ≤ M := le_max_right _ _
    rw [div_le_iff₀ hε] at this
    linarith
  have hK : IsCompact (Set.pi Set.univ fun _ : ι => Set.Icc (0 : ℝ) M) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hK0 : (0 : ι → ℝ) ∈ Set.pi Set.univ fun _ : ι => Set.Icc (0 : ℝ) M := fun i _ =>
    ⟨le_refl _, hM0⟩
  obtain ⟨θ', hθ'K, hθ'min⟩ := hK.exists_isMinOn ⟨0, hK0⟩ hFc.continuousOn
  -- which is a minimum over everything
  have hmin : ∀ θ, F θ' ≤ F θ := by
    intro θ
    obtain ⟨b, -, hb⟩ := Finset.exists_min_image univ θ univ_nonempty
    rw [← hFshift θ (-θ b)]
    set θ₀ : ι → ℝ := fun i => θ i + -θ b with hθ₀
    have hθ₀nn : ∀ i, 0 ≤ θ₀ i := fun i => by
      simp only [hθ₀]; linarith [hb i (mem_univ i)]
    by_cases hbig : ∀ i, θ₀ i ≤ M
    · exact hθ'min (a := θ₀) fun i _ => ⟨hθ₀nn i, hbig i⟩
    · push Not at hbig
      obtain ⟨a, ha⟩ := hbig
      have hb0 : θ₀ b = 0 := by simp [hθ₀]
      have h := hFgrow θ₀ a b
      rw [hb0, sub_zero] at h
      have h' : F θ' ≤ F 0 := hθ'min hK0
      nlinarith
  -- at the minimum, moving one weight up or down cannot help
  have hup : ∀ (i : ι) (t : ℝ), π i * t ≤ incl (θ' + bump i t) i * t := by
    intro i t
    have hlow := hmin (θ' + bump i t)
    have hupp := hsub (θ' + bump i t) (-bump i t)
    rw [add_neg_cancel_right] at hupp
    have e1 : ∑ j, π j * (θ' + bump i t) j = ∑ j, π j * θ' j + π i * t := by
      simp [bump, mul_add, Finset.sum_add_distrib]
    have e2 : ∑ j, incl (θ' + bump i t) j * (-bump i t) j =
        -(incl (θ' + bump i t) i * t) := by
      simp [bump]
    simp only [hF] at hlow
    rw [e1] at hlow
    rw [e2] at hupp
    linarith
  refine ⟨θ', fun i => ?_⟩
  have hcont : Tendsto (fun t : ℝ => incl (θ' + bump i t) i) (𝓝 0) (𝓝 (incl θ' i)) := by
    have hc : Continuous fun t : ℝ => incl (θ' + bump i t) i :=
      (continuous_apply i).comp (hincl.comp (continuous_const.add (continuous_bump i)))
    have h := hc.tendsto 0
    simpa [bump_zero] using h
  apply le_antisymm
  · -- from below zero
    have hl : Tendsto (fun t : ℝ => incl (θ' + bump i t) i) (𝓝[<] 0) (𝓝 (incl θ' i)) :=
      hcont.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hl (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have := hup i t
    have ht' : t < 0 := ht
    nlinarith
  · -- from above zero
    have hr : Tendsto (fun t : ℝ => incl (θ' + bump i t) i) (𝓝[>] 0) (𝓝 (incl θ' i)) :=
      hcont.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hr (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have := hup i t
    have ht' : 0 < t := ht
    nlinarith

end Crush
