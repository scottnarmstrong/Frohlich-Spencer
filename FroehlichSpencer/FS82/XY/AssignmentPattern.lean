/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.GaugeAverage
public import FroehlichSpencer.FS82.Poisson.PerAssignment

/-!
# the assignment fibre as a set of sign patterns

For a rooted tree gauge `T` and a mode assignment `q : E → ℕ`, the fibre of co-closed character
branches over `q` is in bijection with the sign patterns `σ : E → Sign` whose signed current
`e ↦ σ_e (q_e + 1)` is co-closed.

The relative coefficient of a branch is the product of the sign
coefficients of its pattern.

Hence the per-assignment moment `gaugeAssignmentMoment` is a sum over
all sign patterns in which the patterns that are not co-closed are multiplied by zero.

* `assignmentFiberEquiv`: the bijection.
* `gaugeAssignmentFiberSum_eq_patternSum`: the fibre sum as a sum over sign patterns.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.GaugeAverage

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ## Signs of integers -/

/-- The sign of an integer, as a mode of the cosine expansion. -/
def signOfInt (n : ℤ) : Sign := if n = 0 then 0 else if 0 < n then 1 else 2

theorem sign_cases (ε : Sign) : ε = 0 ∨ ε = 1 ∨ ε = 2 := by
  fin_cases ε <;> simp

@[simp] theorem signZ_zero : signZ (0 : Sign) = 0 := by simp [signZ]
@[simp] theorem signZ_one : signZ (1 : Sign) = 1 := by simp [signZ]
@[simp] theorem signZ_two : signZ (2 : Sign) = -1 := by simp [signZ]

theorem signZ_eq_zero_iff (ε : Sign) : signZ ε = 0 ↔ ε = 0 := by
  rcases sign_cases ε with h | h | h <;> simp [h]

theorem signZ_signOfInt_mul_natAbs (n : ℤ) : signZ (signOfInt n) * (n.natAbs : ℤ) = n := by
  unfold signOfInt
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases hpos : 0 < n
    · simp only [h0, hpos, ↓reduceIte, signZ_one, one_mul]
      omega
    · simp only [h0, hpos, ↓reduceIte, signZ_two]
      omega

theorem signOfInt_signZ_mul (ε : Sign) (m : ℕ) (hm : 0 < m) :
    signOfInt (signZ ε * (m : ℤ)) = ε := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rcases sign_cases ε with h | h | h
  · simp [h, signOfInt]
  · have hm0 : m ≠ 0 := by omega
    simp [h, signOfInt, hm0, hm]
  · have hm0 : m ≠ 0 := by omega
    simp [h, signOfInt, hm0]

theorem signCoeff_eq (K : ℝ) (ε : Sign) :
    signCoeff K ε = if ε = 0 then 1 else (K : ℂ) / 2 := by
  rcases sign_cases ε with h | h | h <;> simp [h, signCoeff]

/-! ## Pattern currents -/

/-- The signed current of a sign pattern over a mode assignment. -/
def patternCurrent (q : E → ℕ) (σ : E → Sign) : E → ℤ :=
  fun e => signZ (σ e) * ((q e + 1 : ℕ) : ℤ)

omit [Fintype E] [DecidableEq E] in
theorem patternCurrent_eq_zero_iff (q : E → ℕ) (σ : E → Sign) (e : E) :
    patternCurrent q σ e = 0 ↔ σ e = 0 := by
  unfold patternCurrent
  rw [mul_eq_zero, signZ_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · omega
  · exact fun h => Or.inl h

/-- The fibre of co-closed character branches over a mode assignment. -/
abbrev GaugeAssignmentFiber (T : RootedTreeGauge V E) (q : E → ℕ) :=
  {b : GaugeCharacterBranch T // GaugeCharacterBranch.assignment b = q}

/-- The sign patterns over a mode assignment with a co-closed signed current. -/
abbrev ClosedPattern (T : RootedTreeGauge V E) (q : E → ℕ) :=
  {σ : E → Sign // RootedTreeGauge.CoClosed T (patternCurrent q σ)}

/-- The sign pattern of a branch. -/
def branchPattern {T : RootedTreeGauge V E} (b : GaugeCharacterBranch T) : E → Sign :=
  fun e => signOfInt (b.1.1 e)

theorem patternCurrent_branchPattern {T : RootedTreeGauge V E} (q : E → ℕ)
    (b : GaugeCharacterBranch T) (hb : GaugeCharacterBranch.assignment b = q) :
    patternCurrent q (branchPattern b) = b.1.1 := by
  funext e
  have hassign := congrFun hb e
  change ModeBranch.assignment
      (fun j : {j : E → ℤ // RootedTreeGauge.CoClosed T j} => j.1) b e = q e at hassign
  by_cases hz : b.1.1 e = 0
  · simp [patternCurrent, branchPattern, signOfInt, hz]
  · have hnat : (b.1.1 e).natAbs - 1 = q e := by
      simpa [ModeBranch.assignment, hz] using hassign
    have hpos := Int.natAbs_pos.mpr hz
    have habs : (b.1.1 e).natAbs = q e + 1 := by omega
    unfold patternCurrent branchPattern
    rw [← habs, signZ_signOfInt_mul_natAbs]

/-- The inactive modes that a branch over `q` must carry. -/
noncomputable def canonicalInactiveModes {T : RootedTreeGauge V E} (q : E → ℕ)
    (j : {j : E → ℤ // RootedTreeGauge.CoClosed T j}) :
    Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ :=
  fun i => q ((Fintype.equivFin {e : E // j.1 e = 0}).symm i).1

omit [Fintype V] in
theorem canonicalInactiveModes_heq {T : RootedTreeGauge V E} (q : E → ℕ)
    (j j' : {j : E → ℤ // RootedTreeGauge.CoClosed T j}) (h : j = j') :
    canonicalInactiveModes q j ≍ canonicalInactiveModes q j' := by
  cases h
  rfl

theorem branch_modes_eq_canonical {T : RootedTreeGauge V E} (q : E → ℕ)
    (b : GaugeCharacterBranch T) (hb : GaugeCharacterBranch.assignment b = q) :
    b.2 = canonicalInactiveModes q b.1 := by
  funext i
  let e0 := (Fintype.equivFin {e : E // b.1.1 e = 0}).symm i
  have hq := congrFun hb e0.1
  have heq : b.1.1 e0.1 = 0 := e0.2
  have hmode : b.2 i = q e0.1 := by
    simpa [GaugeCharacterBranch.assignment, ModeBranch.assignment, heq, e0] using hq
  simpa [canonicalInactiveModes, e0] using hmode

/-- The raw branch of a co-closed sign pattern. -/
noncomputable def patternBranch (T : RootedTreeGauge V E) (q : E → ℕ)
    (σ : ClosedPattern T q) : GaugeCharacterBranch T :=
  ⟨⟨patternCurrent q σ.1, σ.2⟩, canonicalInactiveModes q ⟨patternCurrent q σ.1, σ.2⟩⟩

theorem patternBranch_assignment (T : RootedTreeGauge V E) (q : E → ℕ)
    (σ : ClosedPattern T q) :
    GaugeCharacterBranch.assignment (patternBranch T q σ) = q := by
  funext e
  dsimp only [GaugeCharacterBranch.assignment, ModeBranch.assignment, patternBranch,
    canonicalInactiveModes]
  split
  · rw [Equiv.symm_apply_apply]
  · rename_i hz
    have hσ : σ.1 e ≠ 0 := fun h => hz ((patternCurrent_eq_zero_iff q σ.1 e).mpr h)
    have hsign : (signZ (σ.1 e)).natAbs = 1 := by
      rcases sign_cases (σ.1 e) with h | h | h
      · exact absurd h hσ
      · simp [h]
      · simp [h]
    have habs : (patternCurrent q σ.1 e).natAbs = q e + 1 := by
      unfold patternCurrent
      rw [Int.natAbs_mul, Int.natAbs_natCast, hsign, one_mul]
    rw [habs]
    omega

/-- The branch of a co-closed sign pattern. -/
noncomputable def patternToBranch (T : RootedTreeGauge V E) (q : E → ℕ)
    (σ : ClosedPattern T q) : GaugeAssignmentFiber T q :=
  ⟨patternBranch T q σ, patternBranch_assignment T q σ⟩

theorem branchPattern_coClosed (T : RootedTreeGauge V E) (q : E → ℕ)
    (b : GaugeAssignmentFiber T q) :
    RootedTreeGauge.CoClosed T (patternCurrent q (branchPattern b.1)) := by
  rw [patternCurrent_branchPattern q b.1 b.2]
  exact b.1.1.2

/-- The co-closed sign pattern of a branch over `q`. -/
def branchToPattern (T : RootedTreeGauge V E) (q : E → ℕ)
    (b : GaugeAssignmentFiber T q) : ClosedPattern T q :=
  ⟨branchPattern b.1, branchPattern_coClosed T q b⟩

theorem branchToPattern_patternToBranch (T : RootedTreeGauge V E) (q : E → ℕ)
    (σ : ClosedPattern T q) : branchToPattern T q (patternToBranch T q σ) = σ := by
  apply Subtype.ext
  funext e
  change signOfInt (patternCurrent q σ.1 e) = σ.1 e
  unfold patternCurrent
  exact signOfInt_signZ_mul _ _ (Nat.succ_pos _)

theorem patternToBranch_branchToPattern (T : RootedTreeGauge V E) (q : E → ℕ)
    (b : GaugeAssignmentFiber T q) : patternToBranch T q (branchToPattern T q b) = b := by
  rcases b with ⟨br, hb⟩
  apply Subtype.ext
  change (patternToBranch T q (branchToPattern T q ⟨br, hb⟩)).1 = br
  have hbase : (patternToBranch T q (branchToPattern T q ⟨br, hb⟩)).1.1 = br.1 := by
    apply Subtype.ext
    exact patternCurrent_branchPattern q br hb
  refine Sigma.ext hbase ?_
  have hleft : (patternToBranch T q (branchToPattern T q ⟨br, hb⟩)).1.2 =
      canonicalInactiveModes q (patternToBranch T q (branchToPattern T q ⟨br, hb⟩)).1.1 := rfl
  have hright : br.2 = canonicalInactiveModes q br.1 := branch_modes_eq_canonical q br hb
  exact (heq_of_eq hleft).trans
    ((canonicalInactiveModes_heq q
      (patternToBranch T q (branchToPattern T q ⟨br, hb⟩)).1.1 br.1 hbase).trans
        (heq_of_eq hright).symm)

/-- The assignment fibre is the set of co-closed sign patterns. -/
noncomputable def assignmentFiberEquiv (T : RootedTreeGauge V E) (q : E → ℕ) :
    ClosedPattern T q ≃ GaugeAssignmentFiber T q where
  toFun := patternToBranch T q
  invFun := branchToPattern T q
  left_inv := branchToPattern_patternToBranch T q
  right_inv := patternToBranch_branchToPattern T q

theorem patternToBranch_current (T : RootedTreeGauge V E) (q : E → ℕ)
    (σ : ClosedPattern T q) : (patternToBranch T q σ).1.1.1 = patternCurrent q σ.1 := rfl

/-- The relative coefficient of the branch of a pattern is the product of its sign
coefficients. -/
theorem relativeCoefficient_patternToBranch (T : RootedTreeGauge V E) (q : E → ℕ)
    (z : ℕ → ℝ) (hz : ∀ n, 0 < z (positiveMode n)) (σ : ClosedPattern T q) :
    ((GaugeCharacterBranch.assignmentRelativeCoefficient z q (patternToBranch T q σ).1 : ℝ) : ℂ) =
      ∏ e, signCoeff (z (positiveMode (q e))) (σ.1 e) := by
  rw [gaugeCharacterBranch_assignmentRelativeCoefficient_eq_selectedProduct z q
    (patternToBranch T q σ).1 (patternToBranch T q σ).2 hz, patternToBranch_current,
    Finset.prod_filter, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [signCoeff_eq]
  by_cases hσ : σ.1 e = 0
  · have h0 : patternCurrent q σ.1 e = 0 := (patternCurrent_eq_zero_iff q σ.1 e).mpr hσ
    simp [hσ, h0]
  · have h0 : patternCurrent q σ.1 e ≠ 0 := fun h => hσ ((patternCurrent_eq_zero_iff q σ.1 e).mp h)
    simp [hσ, h0]

/-- **The fibre sum as a sum over sign patterns.** -/
theorem gaugeAssignmentFiberSum_eq_patternSum (T : RootedTreeGauge V E) (q : E → ℕ)
    (z : ℕ → ℝ) (hz : ∀ n, 0 < z (positiveMode n)) (F G : (E → ℤ) → ℂ)
    (hFG : ∀ j, RootedTreeGauge.CoClosed T j → F j = G j)
    (hG : ∀ j, ¬ RootedTreeGauge.CoClosed T j → G j = 0) :
    assignmentFiberMoment (GaugeCharacterBranch.assignment (T := T))
        (GaugeCharacterBranch.assignmentRelativeCoefficient (T := T) z)
        (fun b => F b.1.1) q =
      ∑ σ : E → Sign, (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) *
        G (patternCurrent q σ) := by
  classical
  unfold assignmentFiberMoment
  rw [← (assignmentFiberEquiv T q).tsum_eq, tsum_fintype]
  have hterm : ∀ σ : ClosedPattern T q,
      ((GaugeCharacterBranch.assignmentRelativeCoefficient z q
          ((assignmentFiberEquiv T q) σ).1 : ℝ) : ℂ) * F ((assignmentFiberEquiv T q) σ).1.1.1 =
        (∏ e, signCoeff (z (positiveMode (q e))) (σ.1 e)) * G (patternCurrent q σ.1) := by
    intro σ
    change ((GaugeCharacterBranch.assignmentRelativeCoefficient z q
      (patternToBranch T q σ).1 : ℝ) : ℂ) * F (patternToBranch T q σ).1.1.1 = _
    rw [relativeCoefficient_patternToBranch T q z hz σ, patternToBranch_current, hFG _ σ.2]
  simp_rw [hterm]
  rw [← Finset.sum_subtype (Finset.univ.filter fun σ : E → Sign =>
      RootedTreeGauge.CoClosed T (patternCurrent q σ)) (by simp)
    (fun σ => (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) * G (patternCurrent q σ))]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro σ _ hσ
  have hσ' : ¬ RootedTreeGauge.CoClosed T (patternCurrent q σ) := by simpa using hσ
  rw [hG _ hσ', mul_zero]

end FroehlichSpencer.FS82.XY.GaugeAverage

end
