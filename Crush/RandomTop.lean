/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.TopR

/-!
# The `r` largest of random values: the potential

Item `i` gets the value `θ i + G ω i` for random `G`, and the `r` items with
the largest values are chosen. `Crush.potential` is the expected largest sum,
`Crush.inclusion θ i` the probability that `i` is chosen. This file proves the
properties of the potential that `Crush.exists_incl_eq` asks for, except the
continuity of `inclusion`.
-/

namespace Crush

open Finset MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : (rsets ι r).Nonempty)
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → ι → ℝ)

/-- The expected largest sum of `θ i + G i` over a set of `r` items. -/
noncomputable def potential (θ : ι → ℝ) : ℝ := ∫ ω, topSum r hr (θ + G ω) ∂μ

open scoped Classical in
/-- The probability that `i` is among the `r` items with the largest `θ i + G i`. -/
noncomputable def inclusion (r : ℕ) (θ : ι → ℝ) (i : ι) : ℝ :=
  ∫ ω, (if inTop r (θ + G ω) i then (1 : ℝ) else 0) ∂μ

omit [DecidableEq ι] in
theorem topSum_zero : topSum r hr (0 : ι → ℝ) = 0 := by
  obtain ⟨S, -, hS⟩ := exists_isTop hr (0 : ι → ℝ)
  rw [← hS]
  simp [score]

omit [DecidableEq ι] in
theorem abs_topSum_le (v : ι → ℝ) : |topSum r hr v| ≤ ∑ i, |v i| := by
  have h1 := topSum_sub_le hr v 0
  have h2 := topSum_sub_le hr 0 v
  simp only [topSum_zero, Pi.zero_apply, sub_zero, zero_sub, abs_neg] at h1 h2
  rw [abs_le]
  constructor <;> linarith

variable {G}

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_score (hG : ∀ i, Measurable fun ω => G ω i) (θ : ι → ℝ) (S : Finset ι) :
    Measurable fun ω => score (θ + G ω) S := by
  unfold score
  simp only [Pi.add_apply]
  fun_prop

omit [DecidableEq ι] in
theorem measurable_topSum (hG : ∀ i, Measurable fun ω => G ω i) (θ : ι → ℝ) :
    Measurable fun ω => topSum r hr (θ + G ω) := by
  have h : (fun ω => topSum r hr (θ + G ω)) =
      (rsets ι r).sup' hr fun S ω => score (θ + G ω) S := by
    funext ω
    simp [topSum, Finset.sup'_apply]
  rw [h]
  exact Finset.measurable_sup' hr fun S _ => measurable_score hG θ S

omit [DecidableEq ι] in
theorem integrable_topSum (hG : ∀ i, Measurable fun ω => G ω i)
    (hGi : ∀ i, Integrable (fun ω => G ω i) μ) [IsFiniteMeasure μ] (θ : ι → ℝ) :
    Integrable (fun ω => topSum r hr (θ + G ω)) μ := by
  have hb : Integrable (fun ω => ∑ i, |θ i + G ω i|) μ :=
    integrable_finsetSum _ fun i _ => ((integrable_const (θ i)).add (hGi i)).abs
  refine hb.mono' (measurable_topSum hr hG θ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_topSum_le hr (θ + G ω)

end Crush
