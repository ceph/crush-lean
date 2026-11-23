/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.Gumbel
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Independent exponential clocks

Facts about a family of independent exponential variables with rate 1:

* `Crush.expMeasure_shift`: memorylessness of one variable.
* `Crush.pi_shift`: memorylessness of the family, for a shift by a vector.
* `Crush.pi_eq_lintegral_update`: the probability of an event is the mean, over
  one coordinate, of the probability of the event with that coordinate fixed.
* `Crush.lintegral_exp_neg_mul`: `E exp (-c X) = 1 / (1 + c)`.
-/

namespace Crush

open MeasureTheory ProbabilityTheory Set ENNReal

theorem gammaPDF_one_one (x : ℝ) :
    gammaPDF 1 1 x = ENNReal.ofReal (if 0 ≤ x then Real.exp (-x) else 0) := by
  simp [gammaPDF, gammaPDFReal, Real.Gamma_one]

theorem measurable_gammaPDF_one_one : Measurable (gammaPDF 1 1) :=
  (measurable_gammaPDFReal 1 1).ennreal_ofReal

/-- **An exponential variable is memoryless.** -/
theorem expMeasure_shift {a : ℝ} (ha : 0 ≤ a) {s : Set ℝ} (hs : MeasurableSet s) :
    expMeasure 1 {x | a < x ∧ x - a ∈ s} = ENNReal.ofReal (Real.exp (-a)) * expMeasure 1 s := by
  classical
  have hs' : MeasurableSet {x : ℝ | a < x ∧ x - a ∈ s} :=
    (measurableSet_lt measurable_const measurable_id).inter
      ((measurable_id.sub measurable_const) hs)
  unfold expMeasure gammaMeasure
  rw [withDensity_apply _ hs', withDensity_apply _ hs, ← lintegral_indicator hs',
    ← lintegral_indicator hs, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_right_eq_self _ a]
  have h0 : ∀ᵐ y : ℝ, y ≠ 0 := by
    rw [ae_iff]
    simp
  refine lintegral_congr_ae ?_
  filter_upwards [h0] with y hy
  rw [Set.indicator_apply, Set.indicator_apply, gammaPDF_one_one, gammaPDF_one_one]
  by_cases hpos : 0 < y
  · by_cases hys : y ∈ s
    · have h1 : (0 : ℝ) ≤ y + a := by linarith
      have hm : y + a ∈ {x : ℝ | a < x ∧ x - a ∈ s} :=
        ⟨by linarith, by rw [add_sub_cancel_right]; exact hys⟩
      rw [if_pos hm, if_pos hys, if_pos h1, if_pos hpos.le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    · have hm : y + a ∉ {x : ℝ | a < x ∧ x - a ∈ s} := fun h => by
        have h' : a < y + a ∧ y + a - a ∈ s := h
        rw [add_sub_cancel_right] at h'
        exact hys h'.2
      rw [if_neg hm, if_neg hys, mul_zero]
  · have hneg : y < 0 := lt_of_le_of_ne (not_lt.1 hpos) hy
    have h1 : ¬ (0 : ℝ) ≤ y := not_le.2 hneg
    have hm : y + a ∉ {x : ℝ | a < x ∧ x - a ∈ s} := fun h => by
      have h' : a < y + a ∧ y + a - a ∈ s := h
      linarith [h'.1]
    rw [if_neg hm, if_neg h1]
    simp

/-- An exponential variable is positive. -/
theorem expMeasure_pos : ∀ᵐ x ∂(expMeasure 1), 0 < x := by
  have h := expMeasure_shift (le_refl (0 : ℝ)) MeasurableSet.univ
  simp only [sub_zero, mem_univ, and_true, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
    one_mul, measure_univ] at h
  have hm : MeasurableSet {x : ℝ | 0 < x} := measurableSet_lt measurable_const measurable_id
  have := (prob_compl_eq_zero_iff hm).2 h
  rw [ae_iff]
  exact this

variable {ι : Type*} [Fintype ι]

/-- **Independent exponential variables are memoryless**: given that each is
past its `a k`, what is left of them is again independent and exponential. -/
theorem pi_shift (a : ι → ℝ) (ha : ∀ k, 0 ≤ a k) {C : Set (ι → ℝ)} (hC : MeasurableSet C) :
    (Measure.pi fun _ : ι => expMeasure 1)
        {E | (∀ k, a k < E k) ∧ (fun k => E k - a k) ∈ C} =
      ENNReal.ofReal (Real.exp (-∑ k, a k)) * (Measure.pi fun _ : ι => expMeasure 1) C := by
  set P := Measure.pi fun _ : ι => expMeasure 1 with hP
  set c := ENNReal.ofReal (Real.exp (-∑ k, a k)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hshift : Measurable fun (E : ι → ℝ) (k : ι) => E k - a k :=
    measurable_pi_iff.2 fun k => (measurable_pi_apply k).sub measurable_const
  have hpos : MeasurableSet {E : ι → ℝ | ∀ k, a k < E k} := by
    have : {E : ι → ℝ | ∀ k, a k < E k} = Set.pi univ fun k => Ioi (a k) := by
      ext E
      simp
    rw [this]
    exact MeasurableSet.univ_pi fun k => measurableSet_Ioi
  have key : P = c⁻¹ • (P.restrict {E | ∀ k, a k < E k}).map fun E k => E k - a k := by
    rw [hP]
    refine Measure.pi_eq fun s hs => ?_
    rw [smul_apply, Measure.map_apply hshift (MeasurableSet.univ_pi hs),
      Measure.restrict_apply (hshift (MeasurableSet.univ_pi hs))]
    have hbox : (fun (E : ι → ℝ) (k : ι) => E k - a k) ⁻¹' Set.pi univ s ∩
        {E | ∀ k, a k < E k} = Set.pi univ fun k => {x | a k < x ∧ x - a k ∈ s k} := by
      ext E
      simp only [mem_inter_iff, mem_preimage, Set.mem_pi, mem_univ, forall_true_left,
        mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩ k
        exact ⟨h2 k, h1 k⟩
      · intro h
        exact ⟨fun k => (h k).2, fun k => (h k).1⟩
    rw [hbox, Measure.pi_pi]
    simp_rw [expMeasure_shift (ha _) (hs _)]
    rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le,
      ← Real.exp_sum, Finset.sum_neg_distrib, ← hc, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have hset : {E : ι → ℝ | (∀ k, a k < E k) ∧ (fun k => E k - a k) ∈ C} =
      (fun (E : ι → ℝ) (k : ι) => E k - a k) ⁻¹' C ∩ {E | ∀ k, a k < E k} := by
    ext E
    simp [and_comm]
  conv_rhs => rw [key]
  rw [smul_apply, Measure.map_apply hshift hC, Measure.restrict_apply (hshift hC),
    smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul, hset]

/-- Independent exponential variables are all positive. -/
theorem pi_pos : ∀ᵐ E ∂(Measure.pi fun _ : ι => expMeasure 1), ∀ k, 0 < E k := by
  have h := pi_shift (ι := ι) (fun _ => 0) (fun _ => le_refl _) MeasurableSet.univ
  simp only [sub_zero, mem_univ, and_true, Finset.sum_const_zero, neg_zero, Real.exp_zero,
    ENNReal.ofReal_one, one_mul, measure_univ] at h
  have hm : MeasurableSet {E : ι → ℝ | ∀ k, 0 < E k} := by
    have : {E : ι → ℝ | ∀ k, 0 < E k} = Set.pi univ fun _ => Ioi 0 := by
      ext E
      simp
    rw [this]
    exact MeasurableSet.univ_pi fun k => measurableSet_Ioi
  have := (prob_compl_eq_zero_iff hm).2 h
  rw [ae_iff]
  exact this

variable [DecidableEq ι]

/-- **The probability of an event is the mean over one coordinate of the
probability of the event with that coordinate fixed.** -/
theorem pi_eq_lintegral_update (ν : Measure ℝ) [IsProbabilityMeasure ν] (j : ι)
    {D : Set (ι → ℝ)} (hD : MeasurableSet D) :
    (Measure.pi fun _ : ι => ν) D =
      ∫⁻ t, (Measure.pi fun _ : ι => ν) {E | Function.update E j t ∈ D} ∂ν := by
  set f : (ι → ℝ) → ℝ≥0∞ := D.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hD
  have hupd : ∀ t : ℝ, Measurable fun E : ι → ℝ => Function.update E j t := fun t =>
    measurable_pi_iff.2 fun k => by
      by_cases hk : k = j
      · rw [show (fun E : ι → ℝ => Function.update E j t k) = fun _ => t from by
          ext E; rw [hk, Function.update_self]]
        exact measurable_const
      · rw [show (fun E : ι → ℝ => Function.update E j t k) = fun E => E k from by
          ext E; rw [Function.update_of_ne hk]]
        exact measurable_pi_apply k
  have hslice : ∀ (x : ι → ℝ) (t : ℝ),
      (∫⋯∫⁻_(Finset.univ.erase j), f ∂(fun _ : ι => ν)) (Function.update x j t) =
        (Measure.pi fun _ : ι => ν) {E | Function.update E j t ∈ D} := by
    intro x t
    have h1 : (Measure.pi fun _ : ι => ν) {E | Function.update E j t ∈ D} =
        ∫⁻ E, (f ∘ fun E => Function.update E j t) E ∂(Measure.pi fun _ : ι => ν) := by
      have : {E : ι → ℝ | Function.update E j t ∈ D} = (fun E => Function.update E j t) ⁻¹' D :=
        rfl
      rw [this, ← lintegral_indicator_one ((hupd t) hD)]
      rfl
    rw [h1, lintegral_eq_lmarginal_univ x,
      lmarginal_erase _ (hfm.comp (hupd t)) (Finset.mem_univ j) x]
    have h2 : ∀ s : ℝ,
        (∫⋯∫⁻_(Finset.univ.erase j), (f ∘ fun E => Function.update E j t) ∂(fun _ : ι => ν))
            (Function.update x j s) =
          (∫⋯∫⁻_(Finset.univ.erase j), f ∂(fun _ : ι => ν)) (Function.update x j t) := by
      intro s
      simp only [lmarginal, Function.comp]
      refine lintegral_congr fun y => ?_
      congr 1
      ext k
      by_cases hk : k = j
      · subst hk
        simp [Function.updateFinset]
      · simp [Function.updateFinset, hk]
    simp_rw [h2]
    simp
  have h0 : (Measure.pi fun _ : ι => ν) D = ∫⁻ E, f E ∂(Measure.pi fun _ : ι => ν) := by
    rw [hf, lintegral_indicator_one hD]
  rw [h0, lintegral_eq_lmarginal_univ (fun _ => 0), lmarginal_erase _ hfm (Finset.mem_univ j)]
  simp_rw [hslice]

/-- `E exp (-c X) = 1 / (1 + c)` for an exponential variable `X`. -/
theorem lintegral_exp_neg_mul {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (-(c * t))) ∂(expMeasure 1) = ENNReal.ofReal (1 / (1 + c)) := by
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(c * t))) := by fun_prop
  unfold expMeasure gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_gammaPDF_one_one hmeas]
  have hneg : -(1 + c) < 0 := by linarith
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-(1 + c) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi hneg 0
  have h1 : ∀ᵐ x : ℝ, (gammaPDF 1 1 * fun t : ℝ => ENNReal.ofReal (Real.exp (-(c * t)))) x =
      (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal (Real.exp (-(1 + c) * x))) x := by
    have h0 : ∀ᵐ y : ℝ, y ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with x hx
    simp only [Pi.mul_apply, gammaPDF_one_one, Set.indicator, mem_Ioi]
    by_cases hpos : 0 < x
    · simp only [hpos, hpos.le, ite_true]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    · have hneg : ¬ (0 : ℝ) ≤ x := not_le.2 (lt_of_le_of_ne (not_lt.1 hpos) hx)
      simp [hpos, hneg]
  rw [lintegral_congr_ae h1, lintegral_indicator measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
    integral_exp_mul_Ioi hneg 0]
  congr 1
  simp only [mul_zero, Real.exp_zero]
  field_simp

end Crush
