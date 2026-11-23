/-
Copyright (c) 2026 Clyso Technologies Inc.
Released under the GNU Lesser General Public License version 2.1.
-/
import Mathlib

/-!
# straw2: only the item whose weight changes gains or loses

A straw2 bucket maps an input to one of its items: every item draws a straw
whose length depends on the input, the item and the item's *own* weight, and
the longest straw wins (the first one, among equals).

This file states that selection rule and proves the property that the design
of CRUSH rests on: if one item's straw gets longer, an input either keeps its
item or moves to that item, and if it gets shorter, only inputs that were on
that item move. Nothing is assumed about the straws except that the straw of
an item does not depend on the weights of the others, so the statements hold
for every input and every hash function. That straws grow with the weight is
`Crush.straw2_draw_le` for the straw CRUSH uses, `log u / w`.

Nothing here is about probabilities: that an item is chosen in proportion to
its weight needs a model of the hash and is not part of this file.
-/

namespace Crush

variable {ι : Type*} [LinearOrder ι]

/-- `Wins s i`: with straw lengths `s`, item `i` is chosen: no straw is longer,
and no item before `i` has one as long. -/
def Wins (s : ι → ℝ) (i : ι) : Prop :=
  ∀ k, s k < s i ∨ (s k = s i ∧ i ≤ k)

/-- At most one item wins. -/
theorem Wins.unique {s : ι → ℝ} {i j : ι} (hi : Wins s i) (hj : Wins s j) : i = j := by
  rcases hi j with h | ⟨h, hij⟩
  · rcases hj i with h' | ⟨h', _⟩
    · exact absurd h (lt_asymm h')
    · exact absurd h (by rw [h']; exact lt_irrefl _)
  · rcases hj i with h' | ⟨_, hji⟩
    · exact absurd h' (by rw [h]; exact lt_irrefl _)
    · exact le_antisymm hij hji

/-- Some item wins, if there is one at all. -/
theorem exists_wins [Finite ι] [Nonempty ι] (s : ι → ℝ) : ∃ i, Wins s i := by
  classical
  have := Fintype.ofFinite ι
  -- the longest straw
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
  -- the first item that has it
  have hne : (Finset.univ.filter fun k => s k = s m).Nonempty := ⟨m, by simp⟩
  refine ⟨(Finset.univ.filter fun k => s k = s m).min' hne, fun k => ?_⟩
  have hmem := Finset.min'_mem _ hne
  have hsi : s ((Finset.univ.filter fun k => s k = s m).min' hne) = s m := by
    simpa using hmem
  rcases lt_or_eq_of_le (hm k (Finset.mem_univ k)) with h | h
  · exact Or.inl (by rw [hsi]; exact h)
  · exact Or.inr ⟨by rw [hsi]; exact h, Finset.min'_le _ k (by simp [h])⟩

/-- **A shorter straw only loses.** If the straw of `j` gets shorter and the
others stay as they are, every input that was not on `j` stays where it was. -/
theorem Wins.of_shorter [DecidableEq ι] {s : ι → ℝ} {i j : ι} {v : ℝ}
    (hi : Wins s i) (hij : i ≠ j) (hv : v ≤ s j) :
    Wins (Function.update s j v) i := by
  intro k
  rw [Function.update_of_ne hij]
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self]
    rcases hi k with h | ⟨h, hik⟩
    · exact Or.inl (lt_of_le_of_lt hv h)
    · rcases lt_or_eq_of_le hv with h' | h'
      · exact Or.inl (by rw [← h]; exact h')
      · exact Or.inr ⟨by rw [h', h], hik⟩
  · rw [Function.update_of_ne hk]
    exact hi k

/-- **A longer straw only gains.** If the straw of `j` gets longer and the
others stay as they are, an input either stays where it was or moves to `j`. -/
theorem Wins.of_longer [DecidableEq ι] {s : ι → ℝ} {i i' j : ι} {v : ℝ}
    (hi : Wins s i) (hv : s j ≤ v) (hi' : Wins (Function.update s j v) i') :
    i' = i ∨ i' = j := by
  by_cases h : i' = j
  · exact Or.inr h
  · left
    -- going back from `v` to `s j` makes the straw of `j` shorter
    have hback : Wins (Function.update (Function.update s j v) j (s j)) i' :=
      hi'.of_shorter h (by rw [Function.update_self]; exact hv)
    rw [Function.update_idem, Function.update_eq_self] at hback
    exact hback.unique hi

/-- The straw of straw2: `log u / w` for a hash value `u` in `(0, 1]` and a
weight `w > 0`. It is at most 0, and grows with the weight. -/
theorem straw2_draw_le {u w w' : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hw : 0 < w) (hww' : w ≤ w') :
    Real.log u / w ≤ Real.log u / w' := by
  have hlog : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
  have hw' : 0 < w' := lt_of_lt_of_le hw hww'
  rw [div_le_div_iff₀ hw hw']
  exact mul_le_mul_of_nonpos_left hww' hlog

section Weights

variable [DecidableEq ι] {X : Type*}

/-- The item straw2 chooses for input `x`, as a relation: `draw x i w` is the
straw of item `i` for input `x` when the weight of `i` is `w`. -/
def Chooses (draw : X → ι → ℝ → ℝ) (w : ι → ℝ) (x : X) (i : ι) : Prop :=
  Wins (fun k => draw x k (w k)) i

/-- **Raising one weight only moves inputs to that item**, whatever the hash:
all that is needed is that an item's straw grows with its own weight. -/
theorem Chooses.of_weight_le {draw : X → ι → ℝ → ℝ} {w : ι → ℝ} {x : X} {i i' j : ι} {v : ℝ}
    (hmono : draw x j (w j) ≤ draw x j v)
    (hi : Chooses draw w x i) (hi' : Chooses draw (Function.update w j v) x i') :
    i' = i ∨ i' = j := by
  have key : (fun k => draw x k (Function.update w j v k)) =
      Function.update (fun k => draw x k (w k)) j (draw x j v) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  unfold Chooses at hi'
  rw [key] at hi'
  exact Wins.of_longer hi hmono hi'

/-- **Lowering one weight only moves inputs away from that item.** -/
theorem Chooses.of_le_weight {draw : X → ι → ℝ → ℝ} {w : ι → ℝ} {x : X} {i j : ι} {v : ℝ}
    (hmono : draw x j v ≤ draw x j (w j))
    (hi : Chooses draw w x i) (hij : i ≠ j) :
    Chooses draw (Function.update w j v) x i := by
  have key : (fun k => draw x k (Function.update w j v k)) =
      Function.update (fun k => draw x k (w k)) j (draw x j v) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  unfold Chooses
  rw [key]
  exact Wins.of_shorter hi hij hmono

end Weights

end Crush
