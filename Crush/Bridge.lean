/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.Clock
import Crush.Rank
import Crush.Sequential

/-!
# The clock bridge

Give item `k` a clock that rings at `E k / lam k`, for independent exponential
`E k` with rate 1. The order in which the clocks ring is the order of
successive draws in proportion to `lam` among the items not yet drawn:

* `Crush.clocks_firstIn_inter`: clock `j` rings first among `S` with
  probability `lam j / ∑ k ∈ S, lam k`, independently of what the other
  clocks of `S` do after that.
* `Crush.clocks_early`: the probability that fewer than `n` clocks of `S` ring
  before clock `i` is `Crush.seqIncl lam n S i`.
* `Crush.clockBridge`: `Crush.ClockBridge` holds, and with it
  `Crush.exists_weights`: **draw-and-retry reaches every interior set of
  inclusion probabilities.**
-/

namespace Crush

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Independent exponential variables with rate 1, one per item. -/
noncomputable abbrev clocks (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => expMeasure 1

variable (lam : ι → ℝ)

/-- Clock `j` rings before the other clocks of `S`. -/
def firstIn (S : Finset ι) (j : ι) : Set (ι → ℝ) :=
  {E | ∀ k ∈ S.erase j, E j / lam j < E k / lam k}

/-- Fewer than `n` clocks of `S` ring before clock `i`. -/
def early (S : Finset ι) (n : ℕ) (i : ι) : Set (ι → ℝ) :=
  {E | (S.filter fun k => E k / lam k < E i / lam i).card < n}

theorem measurable_clock (k : ι) : Measurable fun E : ι → ℝ => E k / lam k :=
  (measurable_pi_apply k).div_const _

theorem measurableSet_firstIn (S : Finset ι) (j : ι) : MeasurableSet (firstIn lam S j) := by
  have : firstIn lam S j = ⋂ k ∈ S.erase j, {E : ι → ℝ | E j / lam j < E k / lam k} := by
    ext E
    simp [firstIn]
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ =>
    measurableSet_lt (measurable_clock lam j) (measurable_clock lam k)

theorem measurableSet_early (S : Finset ι) (n : ℕ) (i : ι) : MeasurableSet (early lam S n i) := by
  have hm : Measurable fun E : ι → ℝ =>
      ∑ k ∈ S, if E k / lam k < E i / lam i then (1 : ℕ) else 0 :=
    Finset.measurable_sum _ fun k _ => Measurable.ite
      (measurableSet_lt (measurable_clock lam k) (measurable_clock lam i))
      measurable_const measurable_const
  have : early lam S n i =
      (fun E : ι → ℝ => ∑ k ∈ S, if E k / lam k < E i / lam i then (1 : ℕ) else 0) ⁻¹'
        Set.Iio n := by
    ext E
    show (S.filter fun k => E k / lam k < E i / lam i).card < n ↔ _
    rw [Finset.card_filter]
    rfl
  rw [this]
  exact hm measurableSet_Iio

variable {lam} (hlam : ∀ k, 0 < lam k)
include hlam

/-- **Clock `j` rings first among `S` with probability in proportion to its
rate, independently of an event `B` that does not depend on clock `j` and is
unchanged when the other clocks of `S` all ring earlier by the same time.** -/
theorem clocks_firstIn_inter {S : Finset ι} {j : ι} (hj : j ∈ S) {B : Set (ι → ℝ)}
    (hB : MeasurableSet B) (hupd : ∀ (E : ι → ℝ) (t : ℝ), Function.update E j t ∈ B ↔ E ∈ B)
    (hsh : ∀ (c : ℝ) (E : ι → ℝ),
      (fun k => E k - if k ∈ S.erase j then lam k * c else 0) ∈ B ↔ E ∈ B) :
    clocks ι (firstIn lam S j ∩ B) =
      ENNReal.ofReal (lam j / ∑ k ∈ S, lam k) * clocks ι B := by
  set c : ℝ := (∑ k ∈ S.erase j, lam k) / lam j with hc
  have hT : 0 ≤ ∑ k ∈ S.erase j, lam k := Finset.sum_nonneg fun k _ => (hlam k).le
  have hc0 : 0 ≤ c := div_nonneg hT (hlam j).le
  have hposnull : clocks ι {E : ι → ℝ | ∀ k, 0 < E k}ᶜ = 0 := by
    have := pi_pos (ι := ι)
    rw [ae_iff] at this
    exact this
  rw [pi_eq_lintegral_update (expMeasure 1) j ((measurableSet_firstIn lam S j).inter hB)]
  have hslice : ∀ᵐ t ∂(expMeasure 1),
      clocks ι {E | Function.update E j t ∈ firstIn lam S j ∩ B} =
        ENNReal.ofReal (Real.exp (-(c * t))) * clocks ι B := by
    filter_upwards [expMeasure_pos] with t ht
    set a : ι → ℝ := fun k => if k ∈ S.erase j then lam k * (t / lam j) else 0 with ha
    have ha0 : ∀ k, 0 ≤ a k := fun k => by
      rw [ha]
      by_cases hk : k ∈ S.erase j
      · simp only [hk, ite_true]
        exact mul_nonneg (hlam k).le (div_nonneg ht.le (hlam j).le)
      · simp [hk]
    have hsum : ∑ k, a k = c * t := by
      rw [ha, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, hc]
      ring
    rw [← hsum, ← pi_shift a ha0 hB, ← measure_inter_conull hposnull,
      ← measure_inter_conull (s := {E : ι → ℝ | (∀ k, a k < E k) ∧ (fun k => E k - a k) ∈ B})
        hposnull]
    congr 1
    ext E
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine and_congr_left fun hE => ?_
    have h1 : Function.update E j t ∈ firstIn lam S j ↔
        ∀ k ∈ S.erase j, t / lam j < E k / lam k := by
      simp only [firstIn, Set.mem_ofPred_eq, Function.update_self]
      refine forall₂_congr fun k hk => ?_
      rw [Function.update_of_ne (Finset.mem_erase.1 hk).1]
    have h2 : (∀ k, a k < E k) ↔ ∀ k ∈ S.erase j, t / lam j < E k / lam k := by
      constructor
      · intro h k hk
        have := h k
        rw [ha] at this
        simp only [hk, ite_true] at this
        rw [lt_div_iff₀ (hlam k), mul_comm]
        exact this
      · intro h k
        rw [ha]
        by_cases hk : k ∈ S.erase j
        · simp only [hk, ite_true]
          have := h k hk
          rw [lt_div_iff₀ (hlam k), mul_comm] at this
          exact this
        · simp only [hk, if_false]
          exact hE k
    rw [h1, hupd, h2, hsh (t / lam j) E]
  rw [lintegral_congr_ae hslice, lintegral_mul_const _ (by fun_prop), lintegral_exp_neg_mul hc0]
  congr 2
  rw [hc, ← Finset.add_sum_erase S lam hj]
  have := (hlam j).ne'
  field_simp

/-- Clock `j` rings first among `S` with probability in proportion to its rate. -/
theorem clocks_firstIn {S : Finset ι} {j : ι} (hj : j ∈ S) :
    clocks ι (firstIn lam S j) = ENNReal.ofReal (lam j / ∑ k ∈ S, lam k) := by
  have := clocks_firstIn_inter hlam hj MeasurableSet.univ (fun _ _ => by simp) (fun _ _ => by simp)
  simpa using this

/-- **The clocks ring in the order of draw-and-retry**: fewer than `n` clocks
of `S` ring before clock `i` with the probability that `i` is among `n` items
drawn from `S` one after the other in proportion to the rates. -/
theorem clocks_early (n : ℕ) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    clocks ι (early lam S n i) = ENNReal.ofReal (seqIncl lam n S i) := by
  induction n generalizing S with
  | zero => simp [early, seqIncl]
  | succ n ih =>
    have hΛ : 0 < ∑ k ∈ S, lam k := Finset.sum_pos (fun k _ => hlam k) ⟨i, hi⟩
    have hdisj : Set.PairwiseDisjoint (S : Set ι) (firstIn lam S) := by
      intro j hj j' hj' hne
      refine Set.disjoint_left.2 fun E h1 h2 => ?_
      have a1 := h1 j' (Finset.mem_erase.2 ⟨hne.symm, hj'⟩)
      have a2 := h2 j (Finset.mem_erase.2 ⟨hne, hj⟩)
      exact lt_asymm a1 a2
    have hmeasU : MeasurableSet (⋃ j ∈ S, firstIn lam S j) :=
      Finset.measurableSet_biUnion _ fun j _ => measurableSet_firstIn lam S j
    have hU : clocks ι (⋃ j ∈ S, firstIn lam S j) = 1 := by
      rw [measure_biUnion_finset hdisj fun j _ => measurableSet_firstIn lam S j,
        Finset.sum_congr rfl fun j hj => clocks_firstIn hlam hj,
        ← ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (hlam j).le hΛ.le,
        ← Finset.sum_div, div_self hΛ.ne', ENNReal.ofReal_one]
    have hnull : clocks ι (⋃ j ∈ S, firstIn lam S j)ᶜ = 0 := (prob_compl_eq_zero_iff hmeasU).2 hU
    have hsplit : early lam S (n + 1) i ∩ ⋃ j ∈ S, firstIn lam S j =
        ⋃ j ∈ S, firstIn lam S j ∩ early lam S (n + 1) i := by
      ext E
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hA, j, hj, hM⟩
        exact ⟨j, hj, hM, hA⟩
      · rintro ⟨j, hj, hM, hA⟩
        exact ⟨hA, j, hj, hM⟩
    have hdisj' : Set.PairwiseDisjoint (S : Set ι)
        fun j => firstIn lam S j ∩ early lam S (n + 1) i := fun j hj j' hj' hne =>
      (hdisj hj hj' hne).mono Set.inter_subset_left Set.inter_subset_left
    rw [← measure_inter_conull hnull, hsplit, measure_biUnion_finset hdisj' fun j _ =>
      (measurableSet_firstIn lam S j).inter (measurableSet_early lam S (n + 1) i),
      ← Finset.add_sum_erase S _ hi]
    -- clock `i` rings first
    have hfirst : firstIn lam S i ∩ early lam S (n + 1) i = firstIn lam S i := by
      refine Set.inter_eq_left.2 fun E hE => ?_
      have hempty : (S.filter fun k => E k / lam k < E i / lam i) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun k hk hlt => ?_
        by_cases hki : k = i
        · rw [hki] at hlt
          exact lt_irrefl _ hlt
        · exact lt_asymm hlt (hE k (Finset.mem_erase.2 ⟨hki, hk⟩))
      show (S.filter fun k => E k / lam k < E i / lam i).card < n + 1
      rw [hempty]
      simp
    -- another clock `j` rings first
    have hother : ∀ j ∈ S.erase i, clocks ι (firstIn lam S j ∩ early lam S (n + 1) i) =
        ENNReal.ofReal (lam j / (∑ k ∈ S, lam k) * seqIncl lam n (S.erase j) i) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.1 hj).1
      have hjS : j ∈ S := (Finset.mem_erase.1 hj).2
      have hiT : i ∈ S.erase j := Finset.mem_erase.2 ⟨hji.symm, hi⟩
      have hset : firstIn lam S j ∩ early lam S (n + 1) i =
          firstIn lam S j ∩ early lam (S.erase j) n i := by
        ext E
        simp only [Set.mem_inter_iff]
        refine and_congr_right fun hE => ?_
        have hpj : E j / lam j < E i / lam i := hE i hiT
        have hins : (S.filter fun k => E k / lam k < E i / lam i) =
            insert j ((S.erase j).filter fun k => E k / lam k < E i / lam i) := by
          ext k
          by_cases hk : k = j <;> simp [hk, hjS, hpj]
        show (S.filter fun k => E k / lam k < E i / lam i).card < n + 1 ↔
          ((S.erase j).filter fun k => E k / lam k < E i / lam i).card < n
        rw [hins, Finset.card_insert_of_notMem (by simp)]
        omega
      rw [hset, clocks_firstIn_inter hlam hjS (measurableSet_early lam (S.erase j) n i) ?_ ?_,
        ih (S.erase j) hiT, ← ENNReal.ofReal_mul (div_nonneg (hlam j).le hΛ.le)]
      · intro E t
        show ((S.erase j).filter fun k => Function.update E j t k / lam k <
            Function.update E j t i / lam i).card < n ↔
          ((S.erase j).filter fun k => E k / lam k < E i / lam i).card < n
        rw [Finset.filter_congr fun k hk => by
          rw [Function.update_of_ne (Finset.mem_erase.1 hk).1, Function.update_of_ne hji.symm]]
      · intro c E
        have e : ∀ k ∈ S.erase j,
            (E k - if k ∈ S.erase j then lam k * c else 0) / lam k = E k / lam k - c := by
          intro k hk
          rw [if_pos hk]
          have := (hlam k).ne'
          field_simp
        show ((S.erase j).filter fun k =>
            (E k - if k ∈ S.erase j then lam k * c else 0) / lam k <
              (E i - if i ∈ S.erase j then lam i * c else 0) / lam i).card < n ↔
          ((S.erase j).filter fun k => E k / lam k < E i / lam i).card < n
        rw [Finset.filter_congr fun k hk => by rw [e k hk, e i hiT, sub_lt_sub_iff_right]]
    rw [hfirst, clocks_firstIn hlam hi, Finset.sum_congr rfl hother,
      ← ENNReal.ofReal_sum_of_nonneg fun j _ =>
        mul_nonneg (div_nonneg (hlam j).le hΛ.le) (seqIncl_nonneg hlam n _ i),
      ← ENNReal.ofReal_add (div_nonneg (hlam i).le hΛ.le)
        (Finset.sum_nonneg fun j _ =>
          mul_nonneg (div_nonneg (hlam j).le hΛ.le) (seqIncl_nonneg hlam n _ i))]
    simp only [seqIncl, hi, ite_true]

omit hlam

/-- Independent Gumbel values almost never coincide. -/
theorem ae_injective_gumbel (θ : ι → ℝ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : ι => gumbel), Function.Injective (θ + ω) := by
  have key : ∀ᵐ ω ∂(Measure.pi fun _ : ι => gumbel), ∀ j k : ι, j ≠ k →
      θ j + ω j ≠ θ k + ω k := by
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro k
    by_cases hjk : j = k
    · exact Filter.Eventually.of_forall fun ω h => absurd hjk h
    · have hmeas : MeasurableSet {ω : ι → ℝ | θ j + ω j = θ k + ω k} :=
        measurableSet_eq_fun (measurable_const.add (measurable_pi_apply j))
          (measurable_const.add (measurable_pi_apply k))
      have hnull := pi_null_of_coord gumbel j hmeas (by
        intro ω ω' hω hω' hagree
        have h1 : θ j + ω j = θ k + ω k := hω
        have h2 : θ j + ω' j = θ k + ω' k := hω'
        have h3 := hagree k (Ne.symm hjk)
        linarith)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω _
      exact hω
  filter_upwards [key] with ω hω a b hab
  by_contra hne
  exact hω a b hne hab

/-- **The clock bridge**: the `r` largest of `θ k` plus independent Gumbel
values are `r` successive draws in proportion to `exp (θ k)`. -/
theorem clockBridge : ClockBridge ι := by
  intro r θ i hr
  have hlam : ∀ k, 0 < Real.exp (θ k) := fun k => Real.exp_pos _
  have hmap : (Measure.pi fun _ : ι => gumbel) =
      (clocks ι).map fun E k => -Real.log (E k) := by
    rw [Measure.pi_map_pi fun _ => measurable_neg_log.aemeasurable]
    rfl
  have hmeasmap : Measurable fun (E : ι → ℝ) (k : ι) => -Real.log (E k) :=
    measurable_pi_iff.2 fun k => measurable_neg_log.comp (measurable_pi_apply k)
  have hme := measurableSet_early (fun k => Real.exp (θ k)) Finset.univ r i
  -- by rank, almost surely
  have h1 : inclusion (Measure.pi fun _ : ι => gumbel) (fun ω : ι → ℝ => ω) r θ i =
      ∫ ω, {v : ι → ℝ | (Finset.univ.filter fun k => θ i + v i < θ k + v k).card < r}.indicator
        (fun _ => (1 : ℝ)) ω ∂(Measure.pi fun _ : ι => gumbel) := by
    unfold inclusion
    refine integral_congr_ae ?_
    filter_upwards [ae_injective_gumbel θ] with ω hω
    have := inTop_iff_card_lt hω hr i
    simp only [Pi.add_apply] at this
    by_cases hc : inTop r (θ + ω) i
    · have hc' := this.1 hc
      rw [if_pos hc, Set.indicator_of_mem (by exact hc')]
    · have hc' : ¬ _ := fun h => hc (this.2 h)
      rw [if_neg hc, Set.indicator_of_notMem (by exact hc')]
  have hmv : MeasurableSet
      {v : ι → ℝ | (Finset.univ.filter fun k => θ i + v i < θ k + v k).card < r} := by
    have hm : Measurable fun v : ι → ℝ =>
        ∑ k, if θ i + v i < θ k + v k then (1 : ℕ) else 0 :=
      Finset.measurable_sum _ fun k _ => Measurable.ite
        (measurableSet_lt (measurable_const.add (measurable_pi_apply i))
          (measurable_const.add (measurable_pi_apply k)))
        measurable_const measurable_const
    have : {v : ι → ℝ | (Finset.univ.filter fun k => θ i + v i < θ k + v k).card < r} =
        (fun v : ι → ℝ => ∑ k, if θ i + v i < θ k + v k then (1 : ℕ) else 0) ⁻¹' Set.Iio r := by
      ext v
      show (Finset.univ.filter fun k => θ i + v i < θ k + v k).card < r ↔ _
      rw [Finset.card_filter]
      rfl
    rw [this]
    exact hm measurableSet_Iio
  rw [h1, hmap, integral_map hmeasmap.aemeasurable
    ((measurable_const.indicator hmv).aestronglyMeasurable)]
  -- as clocks
  have h2 : ∀ᵐ E ∂(clocks ι),
      {v : ι → ℝ | (Finset.univ.filter fun k => θ i + v i < θ k + v k).card < r}.indicator
        (fun _ => (1 : ℝ)) (fun k => -Real.log (E k)) =
      (early (fun k => Real.exp (θ k)) Finset.univ r i).indicator (fun _ => (1 : ℝ)) E := by
    filter_upwards [pi_pos (ι := ι)] with E hE
    have hiff : ∀ k, θ i + -Real.log (E i) < θ k + -Real.log (E k) ↔
        E k / Real.exp (θ k) < E i / Real.exp (θ i) := by
      intro k
      rw [← Real.log_lt_log_iff (div_pos (hE k) (hlam k)) (div_pos (hE i) (hlam i)),
        Real.log_div (hE k).ne' (hlam k).ne', Real.log_div (hE i).ne' (hlam i).ne',
        Real.log_exp, Real.log_exp]
      constructor <;> intro h <;> linarith
    have hmem : (fun k => -Real.log (E k)) ∈
        {v : ι → ℝ | (Finset.univ.filter fun k => θ i + v i < θ k + v k).card < r} ↔
        E ∈ early (fun k => Real.exp (θ k)) Finset.univ r i := by
      show (Finset.univ.filter fun k => θ i + -Real.log (E i) < θ k + -Real.log (E k)).card < r ↔
        (Finset.univ.filter fun k => E k / Real.exp (θ k) < E i / Real.exp (θ i)).card < r
      rw [Finset.filter_congr fun k _ => hiff k]
    by_cases hc : E ∈ early (fun k => Real.exp (θ k)) Finset.univ r i
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (hmem.2 hc)]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem fun h => hc (hmem.1 h)]
  rw [integral_congr_ae h2, integral_indicator_const _ hme, smul_eq_mul, mul_one, measureReal_def,
    clocks_early hlam r Finset.univ i (Finset.mem_univ i),
    ENNReal.toReal_ofReal (seqIncl_nonneg hlam r _ i)]

/-- **Draw-and-retry reaches every interior set of inclusion probabilities**:
for `π` strictly between 0 and 1 that sum to `r` there are positive weights
with which picking `r` items one after the other, in proportion to the weights
among the items not yet picked, picks item `i` with probability `π i`. -/
theorem exists_weights {r : ℕ} (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1)
    (hsum : ∑ i, π i = r) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ i, seqIncl w r Finset.univ i = π i :=
  exists_weights_of_clockBridge clockBridge π h0 h1 hsum

end Crush
