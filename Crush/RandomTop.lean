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

open Finset MeasureTheory Filter Topology

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


section Potential

variable [IsProbabilityMeasure μ] (hG : ∀ i, Measurable fun ω => G ω i)
  (hGi : ∀ i, Integrable (fun ω => G ω i) μ)
include hG hGi

omit [DecidableEq ι] in
/-- Adding `c` to every `θ i` adds `r * c` to the potential. -/
theorem potential_add_const (θ : ι → ℝ) (c : ℝ) :
    potential hr μ G (fun i => θ i + c) = potential hr μ G θ + r * c := by
  unfold potential
  have h : ∀ ω, topSum r hr ((fun i => θ i + c) + G ω) = topSum r hr (θ + G ω) + r * c := by
    intro ω
    have e : ((fun i => θ i + c) + G ω) = fun i => (θ + G ω) i + c := by
      funext i
      simp only [Pi.add_apply]
      ring
    rw [e, topSum_add_const]
  simp_rw [h]
  rw [integral_add (integrable_topSum hr μ hG hGi θ) (integrable_const _), integral_const]
  simp

omit [DecidableEq ι] in
/-- The potential is at least the sum of `θ` over any set of `r` items, up to
a constant. -/
theorem sum_sub_le_potential (θ : ι → ℝ) (S : Finset ι) (hS : S.card = r) :
    ∑ i ∈ S, θ i - ∫ ω, ∑ i, |G ω i| ∂μ ≤ potential hr μ G θ := by
  have hb : Integrable (fun ω => ∑ i, |G ω i|) μ :=
    integrable_finsetSum _ fun i _ => (hGi i).abs
  have hSm : S ∈ rsets ι r := Finset.mem_powersetCard.2 ⟨Finset.subset_univ S, hS⟩
  have key : ∫ ω, (∑ i ∈ S, θ i - ∑ i, |G ω i|) ∂μ ≤ ∫ ω, topSum r hr (θ + G ω) ∂μ := by
    refine integral_mono ((integrable_const _).sub hb) (integrable_topSum hr μ hG hGi θ)
      fun ω => ?_
    have h1 := score_le_topSum hr (θ + G ω) hSm
    have h2 : -(∑ i, |G ω i|) ≤ ∑ i ∈ S, G ω i := by
      calc -(∑ i, |G ω i|) ≤ -(∑ i ∈ S, |G ω i|) :=
            neg_le_neg (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              fun _ _ _ => abs_nonneg _)
        _ = ∑ i ∈ S, -|G ω i| := by rw [Finset.sum_neg_distrib]
        _ ≤ ∑ i ∈ S, G ω i := Finset.sum_le_sum fun i _ => neg_abs_le _
    rw [score_add] at h1
    simp only [score] at h1
    show ∑ i ∈ S, θ i - ∑ i, |G ω i| ≤ topSum r hr (θ + G ω)
    linarith
  rw [integral_sub (integrable_const _) hb, integral_const] at key
  simpa [potential] using key

omit [DecidableEq ι] in
theorem potential_sub_le (θ θ' : ι → ℝ) :
    potential hr μ G θ - potential hr μ G θ' ≤ ∑ i, |θ i - θ' i| := by
  unfold potential
  rw [← integral_sub (integrable_topSum hr μ hG hGi θ) (integrable_topSum hr μ hG hGi θ')]
  have key : ∫ ω, (topSum r hr (θ + G ω) - topSum r hr (θ' + G ω)) ∂μ ≤
      ∫ _ω, (∑ i, |θ i - θ' i|) ∂μ := by
    refine integral_mono ((integrable_topSum hr μ hG hGi θ).sub
      (integrable_topSum hr μ hG hGi θ')) (integrable_const _) fun ω => ?_
    have := topSum_sub_le hr (θ + G ω) (θ' + G ω)
    simpa using this
  rw [integral_const] at key
  simpa using key

omit [DecidableEq ι] in
theorem continuous_potential : Continuous (potential hr μ G) := by
  have key : ∀ a b : ι → ℝ, ∑ i, |a i - b i| ≤ Fintype.card ι * dist a b := fun a b => by
    calc ∑ i, |a i - b i| ≤ ∑ _i : ι, dist a b :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.dist_eq]; exact dist_le_pi_dist a b i
      _ = Fintype.card ι * dist a b := by simp
  refine (LipschitzWith.of_dist_le_mul (K := Fintype.card ι) fun θ θ' => ?_).continuous
  rw [Real.dist_eq, abs_le]
  have h1 := potential_sub_le hr μ hG hGi θ θ'
  have h2 := potential_sub_le hr μ hG hGi θ' θ
  have k1 := key θ θ'
  have k2 := key θ' θ
  rw [dist_comm] at k2
  push_cast
  constructor <;> linarith

omit hGi in
/-- The event that `i` is chosen. -/
theorem measurableSet_inTop (θ : ι → ℝ) (i : ι) :
    MeasurableSet {ω | inTop r (θ + G ω) i} := by
  have h : {ω | inTop r (θ + G ω) i} =
      ⋃ S ∈ (rsets ι r).filter (i ∈ ·), ⋂ T ∈ rsets ι r,
        {ω | score (θ + G ω) T ≤ score (θ + G ω) S} := by
    ext ω
    simp only [Set.mem_setOf_eq, inTop, IsTop, Set.mem_iUnion, Set.mem_iInter,
      Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨S, ⟨hS, hmax⟩, hi⟩
      exact ⟨S, ⟨hS, hi⟩, hmax⟩
    · rintro ⟨S, ⟨hS, hi⟩, hmax⟩
      exact ⟨S, ⟨hS, hmax⟩, hi⟩
  rw [h]
  exact Finset.measurableSet_biUnion _ fun S _ => Finset.measurableSet_biInter _ fun T _ =>
    measurableSet_le (measurable_score hG θ T) (measurable_score hG θ S)

open scoped Classical in
omit hGi in
theorem measurable_indicator_inTop (θ : ι → ℝ) (i : ι) (c : ℝ) :
    Measurable fun ω => if inTop r (θ + G ω) i then c else 0 :=
  Measurable.ite (measurableSet_inTop hG θ i) measurable_const measurable_const

open scoped Classical in
omit hGi in
theorem integrable_indicator_inTop (θ : ι → ℝ) (i : ι) (c : ℝ) :
    Integrable (fun ω => if inTop r (θ + G ω) i then c else 0) μ := by
  refine (integrable_const |c|).mono' (measurable_indicator_inTop hG θ i c).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  split_ifs
  · exact le_of_eq (Real.norm_eq_abs c)
  · simp

/-- **The inclusion probabilities are a subgradient of the potential**, if
ties have probability 0. -/
theorem potential_add_le (hnt : ∀ θ : ι → ℝ, ∀ᵐ ω ∂μ, NoTies r (θ + G ω)) (θ h : ι → ℝ) :
    potential hr μ G θ + ∑ i, inclusion μ G r θ i * h i ≤ potential hr μ G (θ + h) := by
  classical
  have hsum : ∑ i, inclusion μ G r θ i * h i =
      ∫ ω, ∑ i, (if inTop r (θ + G ω) i then h i else 0) ∂μ := by
    rw [integral_finsetSum _ fun i _ => integrable_indicator_inTop μ hG θ i (h i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold inclusion
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases hc : inTop r (θ + G ω) i <;> simp [hc]
  have hint : Integrable (fun ω => ∑ i, (if inTop r (θ + G ω) i then h i else 0)) μ :=
    integrable_finsetSum _ fun i _ => integrable_indicator_inTop μ hG θ i (h i)
  rw [hsum]
  unfold potential
  rw [← integral_add (integrable_topSum hr μ hG hGi θ) hint]
  refine integral_mono_ae ((integrable_topSum hr μ hG hGi θ).add hint)
    (integrable_topSum hr μ hG hGi (θ + h)) ?_
  filter_upwards [hnt θ] with ω hω
  have key := topSum_add_le hr hω h
  have e : θ + h + G ω = θ + G ω + h := by abel
  rw [e]
  convert key using 3

include hr in
/-- **The inclusion probabilities are continuous**, if ties have probability
0: where there is no tie the choice does not change nearby. -/
theorem continuous_inclusion (hnt : ∀ θ : ι → ℝ, ∀ᵐ ω ∂μ, NoTies r (θ + G ω)) :
    Continuous (inclusion μ G r) := by
  classical
  refine continuous_pi fun i => ?_
  rw [continuous_iff_seqContinuous]
  intro θs θ hθ
  show Tendsto (fun n => inclusion μ G r (θs n) i) atTop (𝓝 (inclusion μ G r θ i))
  unfold inclusion
  refine tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => (measurable_indicator_inTop hG (θs n) i 1).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun ω => by
      by_cases hc : inTop r (θs n + G ω) i <;> simp [hc]) ?_
  filter_upwards [hnt θ] with ω hω
  obtain ⟨ε, hε, hloc⟩ := exists_inTop_iff_of_noTies hr hω
  have hev : ∀ᶠ n in atTop, ∀ j, |θs n j - θ j| < ε := by
    rw [Filter.eventually_all]
    intro j
    have hj : Tendsto (fun n => θs n j) atTop (𝓝 (θ j)) := (tendsto_pi_nhds.1 hθ) j
    have := (Metric.tendsto_nhds.1 hj) ε hε
    simpa [Real.dist_eq] using this
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  have hclose : ∀ j, |(θs n + G ω) j - (θ + G ω) j| < ε := fun j => by simpa using hn j
  have := hloc (θs n + G ω) hclose i
  by_cases hc : inTop r (θ + G ω) i <;> simp [hc, this]

end Potential

/-- **Choosing the `r` largest of `θ i + G i` reaches every interior set of
inclusion probabilities.** `G` is any random vector with integrable entries
for which ties have probability 0. -/
theorem exists_inclusion_eq [IsProbabilityMeasure μ] (hG : ∀ i, Measurable fun ω => G ω i)
    (hGi : ∀ i, Integrable (fun ω => G ω i) μ)
    (hnt : ∀ θ : ι → ℝ, ∀ᵐ ω ∂μ, NoTies r (θ + G ω))
    (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1) (hsum : ∑ i, π i = r) :
    ∃ θ, ∀ i, inclusion μ G r θ i = π i := by
  have hr : (rsets ι r).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    have h : (r : ℝ) ≤ Fintype.card ι := by
      rw [← hsum]
      calc ∑ i, π i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (h1 i).le
        _ = Fintype.card ι := by simp
    exact_mod_cast h
  exact exists_incl_eq (potential hr μ G) (inclusion μ G r)
    (potential_add_le hr μ hG hGi hnt) (potential_add_const hr μ hG hGi)
    ⟨_, sum_sub_le_potential hr μ hG hGi⟩ (continuous_potential hr μ hG hGi)
    (continuous_inclusion hr μ hG hGi hnt) π h0 h1 hsum

end Crush
