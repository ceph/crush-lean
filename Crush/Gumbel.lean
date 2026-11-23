/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.Iid

/-!
# Gumbel values

straw2 gives item `i` the straw `log u / w i` for a hash value `u` in `(0, 1]`
and picks the longest. With `E = -log u`, which is exponential with rate 1 for
uniform `u`, the longest straw is the largest `log (w i) - log E`: the value
`log (w i)` plus `-log E`, a Gumbel variable.

`Crush.gumbel` is the law of `-log E`. It is a probability measure without
point masses and with a mean, so `Crush.exists_inclusion_eq_iid` applies
(`Crush.exists_inclusion_eq_gumbel`).
-/

namespace Crush

open MeasureTheory ProbabilityTheory Set

/-- The law of `-log E` for `E` exponential with rate 1. -/
noncomputable def gumbel : Measure ℝ := (expMeasure 1).map fun t => -Real.log t

theorem measurable_neg_log : Measurable fun t : ℝ => -Real.log t :=
  Real.measurable_log.neg

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

instance : NullSingletonClass (expMeasure 1) := by
  unfold expMeasure gammaMeasure
  infer_instance

instance : IsProbabilityMeasure gumbel :=
  (Measure.isProbabilityMeasure_map_iff measurable_neg_log.aemeasurable).2 inferInstance

instance : NullSingletonClass gumbel where
  measure_singleton x := by
    unfold gumbel
    rw [Measure.map_apply measurable_neg_log (measurableSet_singleton x)]
    have hsub : (fun t : ℝ => -Real.log t) ⁻¹' {x} ⊆
        {Real.exp (-x)} ∪ ({-Real.exp (-x)} ∪ {0}) := by
      intro t ht
      have hlog : Real.log t = -x := by
        have : -Real.log t = x := ht
        linarith
      by_cases h0 : t = 0
      · exact Or.inr (Or.inr h0)
      · have habs : |t| = Real.exp (-x) := by rw [← Real.exp_log_eq_abs h0, hlog]
        rcases abs_choice t with h | h
        · exact Or.inl (by rw [← habs, h]; rfl)
        · refine Or.inr (Or.inl ?_)
          have : t = -|t| := by rw [h]; ring
          rw [this, habs]
          rfl
    exact measure_mono_null hsub (measure_union_null (measure_singleton _)
      (measure_union_null (measure_singleton _) (measure_singleton _)))

/-- `|log t| ≤ 2 / √t + t`. -/
theorem abs_log_le {t : ℝ} (ht : 0 < t) :
    |Real.log t| ≤ 2 * t ^ ((1 : ℝ) / 2 - 1) + t ^ ((2 : ℝ) - 1) := by
  have h1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht
  have hp : 0 < t ^ ((1 : ℝ) / 2 - 1) := Real.rpow_pos_of_pos ht _
  have h2 := Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow ht] at h2
  have ht1 : t ^ ((2 : ℝ) - 1) = t := by norm_num
  rw [ht1, abs_le]
  constructor <;> nlinarith

/-- `-log` of an exponential variable has a mean. -/
theorem integrable_id_gumbel : Integrable id gumbel := by
  unfold gumbel
  rw [integrable_map_measure aestronglyMeasurable_id measurable_neg_log.aemeasurable]
  unfold expMeasure gammaMeasure
  have hmeas : Measurable (gammaPDF 1 1) :=
    (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [integrable_withDensity_iff hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  -- the integrand vanishes outside `(0, ∞)`
  have hfun : (fun x : ℝ => (id ∘ fun t => -Real.log t) x * (gammaPDF 1 1 x).toReal) =
      (Ioi (0 : ℝ)).indicator fun x => -Real.log x * Real.exp (-x) := by
    funext x
    by_cases hx : 0 < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hx)]
      simp [gammaPDF, gammaPDFReal, hx.le, Real.exp_nonneg]
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      rcases eq_or_lt_of_le (not_lt.1 hx) with h | h
      · simp [h]
      · simp [gammaPDF, gammaPDFReal, not_le.2 h]
  rw [hfun, integrable_indicator_iff measurableSet_Ioi]
  -- and is dominated by two Gamma integrands
  have hdom : IntegrableOn (fun x : ℝ => 2 * (Real.exp (-x) * x ^ ((1 : ℝ) / 2 - 1)) +
      Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Ioi 0) :=
    ((Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2).add
      (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2))
  refine Integrable.mono' hdom (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
  have := abs_log_le hx0
  have he := Real.exp_pos (-x)
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- **Choosing the `r` largest of `θ i + G i` for independent Gumbel `G i`
reaches every interior set of inclusion probabilities.** -/
theorem exists_inclusion_eq_gumbel (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1)
    (hsum : ∑ i, π i = r) :
    ∃ θ, ∀ i, inclusion (Measure.pi fun _ : ι => gumbel) (fun ω : ι → ℝ => ω) r θ i = π i :=
  exists_inclusion_eq_iid gumbel integrable_id_gumbel π h0 h1 hsum

end Crush
