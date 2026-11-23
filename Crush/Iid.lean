/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Crush.RandomTop

/-!
# Independent values without atoms have no ties

`Crush.exists_inclusion_eq` needs that ties have probability 0. Here the
values are independent with a common law `ν` on the reals in which no single value has positive probability
and a mean: the measure is `Measure.pi fun _ => ν` on `ι → ℝ`.

* `Crush.pi_null_of_coord`: a measurable set that contains at most one point
  on every line parallel to one axis is null;
* `Crush.ae_noTies`: so two different sets of `r` items almost never have the
  same sum;
* `Crush.exists_inclusion_eq_iid`: every interior set of inclusion
  probabilities is reached.
-/

namespace Crush

open Finset MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A measurable set that meets every line parallel to the `j` axis in at most
one point is null for a product of measures without atoms. -/
theorem pi_null_of_coord (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] (j : ι)
    {A : Set (ι → ℝ)} (hA : MeasurableSet A)
    (h : ∀ ω ω' : ι → ℝ, ω ∈ A → ω' ∈ A → (∀ i, i ≠ j → ω i = ω' i) → ω j = ω' j) :
    Measure.pi (fun _ : ι => ν) A = 0 := by
  classical
  set p : ι → Prop := fun i => i ≠ j with hp
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p with he
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
  have hs : MeasurableSet (e.symm ⁻¹' A) := e.symm.measurable hA
  have hA' : Measure.pi (fun _ : ι => ν) A =
      ((Measure.pi fun _ : Subtype p => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν))
        (e.symm ⁻¹' A) := by
    have hpre : e ⁻¹' (e.symm ⁻¹' A) = A := by
      ext ω
      rw [Set.mem_preimage, Set.mem_preimage, e.symm_apply_apply]
    rw [← hmp.measure_preimage_equiv, hpre]
  rw [hA', Measure.measure_prod_null hs]
  refine Filter.Eventually.of_forall fun x => ?_
  show (Measure.pi fun _ : {i // ¬p i} => ν) (Prod.mk x ⁻¹' (e.symm ⁻¹' A)) = 0
  have jmem : ¬p j := by simp [hp]
  by_cases hne : (Prod.mk x ⁻¹' (e.symm ⁻¹' A)).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    refine measure_mono_null (t := {y | y ⟨j, jmem⟩ = y₀ ⟨j, jmem⟩}) (fun y hy => ?_)
      (Measure.pi_hyperplane (fun _ : {i // ¬p i} => ν) ⟨j, jmem⟩ _)
    have key := h (e.symm (x, y)) (e.symm (x, y₀)) hy hy₀ fun i hi => by
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hp, hi]
    simpa [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hp] using key
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp

variable {r : ℕ}

/-- **Independent values without atoms almost never tie.** -/
theorem ae_noTies (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] (θ : ι → ℝ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : ι => ν), NoTies r (θ + ω) := by
  suffices key : ∀ᵐ ω ∂(Measure.pi fun _ : ι => ν), ∀ S T : Finset ι,
      S ∈ rsets ι r → T ∈ rsets ι r → S ≠ T → score (θ + ω) S ≠ score (θ + ω) T by
    filter_upwards [key] with ω hω
    exact fun S hS T hT hne => hω S T hS hT hne
  rw [Filter.eventually_all]
  intro S
  rw [Filter.eventually_all]
  intro T
  by_cases hS : S ∈ rsets ι r
  · by_cases hT : T ∈ rsets ι r
    · by_cases hST : S = T
      · exact Filter.Eventually.of_forall fun ω _ _ hne => absurd hST hne
      · -- an item of `S` that is not in `T`
        obtain ⟨j, hjS, hjT⟩ : ∃ j ∈ S, j ∉ T := by
          by_contra hcon
          push Not at hcon
          have hsub : S ⊆ T := hcon
          have hc : T.card ≤ S.card := by
            rw [(Finset.mem_powersetCard.1 hS).2, (Finset.mem_powersetCard.1 hT).2]
          exact hST (Finset.eq_of_subset_of_card_le hsub hc)
        have hmeas : MeasurableSet {ω : ι → ℝ | score (θ + ω) S = score (θ + ω) T} :=
          measurableSet_eq_fun
            (measurable_score (G := fun ω : ι → ℝ => ω) (fun i => measurable_pi_apply i) θ S)
            (measurable_score (G := fun ω : ι → ℝ => ω) (fun i => measurable_pi_apply i) θ T)
        have hnull := pi_null_of_coord ν j hmeas (by
          intro ω ω' hω hω' hagree
          simp only [Set.mem_ofPred_eq, score] at hω hω'
          rw [← Finset.add_sum_erase S _ hjS] at hω hω'
          have e1 : ∑ i ∈ S.erase j, (θ + ω) i = ∑ i ∈ S.erase j, (θ + ω') i :=
            Finset.sum_congr rfl fun i hi => by
              simp only [Pi.add_apply]; rw [hagree i (Finset.mem_erase.1 hi).1]
          have e2 : ∑ i ∈ T, (θ + ω) i = ∑ i ∈ T, (θ + ω') i :=
            Finset.sum_congr rfl fun i hi => by
              simp only [Pi.add_apply]
              rw [hagree i fun hij => hjT (hij ▸ hi)]
          simp only [Pi.add_apply] at hω hω' e1 e2
          linarith)
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω _ _ _
        exact hω
    · exact Filter.Eventually.of_forall fun ω _ hT' => absurd hT' hT
  · exact Filter.Eventually.of_forall fun ω hS' => absurd hS' hS

/-- **Choosing the `r` largest of `θ i + G i` for independent `G i` with a
common law that has no atoms and a mean reaches every interior set of
inclusion probabilities.** -/
theorem exists_inclusion_eq_iid (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hν : Integrable id ν) (π : ι → ℝ) (h0 : ∀ i, 0 < π i) (h1 : ∀ i, π i < 1)
    (hsum : ∑ i, π i = r) :
    ∃ θ, ∀ i, inclusion (Measure.pi fun _ : ι => ν) (fun ω : ι → ℝ => ω) r θ i = π i :=
  exists_inclusion_eq _ (fun i => measurable_pi_apply i)
    (fun _ => integrable_eval hν) (fun θ => ae_noTies ν θ) π h0 h1 hsum

end Crush
