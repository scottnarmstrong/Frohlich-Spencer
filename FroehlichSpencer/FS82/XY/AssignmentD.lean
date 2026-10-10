/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.ClosedLineageD
public import FroehlichSpencer.FS82.XY.AssignmentIntegral

/-!
# regrouping a sum over closed integer currents by mode assignments

The chart-free form of `Poisson/GaugeCharacter.lean`, `XY/AssignmentPattern.lean` and
`XY/AssignmentIntegral.lean`.

Those modules regroup the sum over the co-closed currents of a
rooted tree gauge; here the currents are those satisfying an arbitrary predicate `P` on `E → ℤ`,
and then `P = ClosedD D` for an integer divergence matrix `D`.

* `predRegroup_hasSum`: every current is counted once after the inactive cells are given
  independent positive modes with total mass one.
* `assignmentFiberEquiv`, `predAssignmentFiberSum_eq_patternSum`: the branches over a mode
  assignment `q` are the sign patterns `σ` with `P (σ · (q + 1))`.
* `closedCharacterSum_hasSum_assignment`: for a positive semidefinite `S` and a real shift `s`,

`∑_{j closed} e^{i⟨s, j⟩} e^{−⟨j, S j⟩/2} = ∑_q λ(q) ∫ ∏_e (1 + z_{q_e+1} cos((q_e+1)(φ_e + s_e)))`,

the integral against the gauge-averaged Gaussian of `XY/GaugeFieldD.lean`.

FS82 (4.28)–(4.29).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.XY.GaugeAverage
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {E : Type*} [Fintype E]

/-! ## Branches of currents with a predicate -/

/-- A current with the predicate `P`, with a positive mode at every inactive cell. -/
abbrev PredBranch (P : (E → ℤ) → Prop) := ModeBranch (fun j : {j : E → ℤ // P j} => j.1)

/-- The mode assignment of a branch. -/
noncomputable def PredBranch.assignment {P : (E → ℤ) → Prop} (b : PredBranch P) : E → ℕ :=
  ModeBranch.assignment (fun j : {j : E → ℤ // P j} => j.1) b

/-- The coefficient of a branch relative to its assignment. -/
noncomputable def PredBranch.relativeCoefficient {P : (E → ℤ) → Prop} (z : ℕ → ℝ) (q : E → ℕ)
    (b : PredBranch P) : ℝ :=
  assignmentRelativeCoefficient z q b

/-- The fibre of closed character branches over a mode assignment. -/
abbrev PredAssignmentFiber (P : (E → ℤ) → Prop) (q : E → ℕ) :=
  {b : PredBranch P // PredBranch.assignment b = q}

/-- The sign patterns over a mode assignment with a closed signed current. -/
abbrev ClosedPattern (P : (E → ℤ) → Prop) (q : E → ℕ) :=
  {σ : E → Sign // P (patternCurrent q σ)}

/-- The sign pattern of a branch. -/
def branchPattern {P : (E → ℤ) → Prop} (b : PredBranch P) : E → Sign :=
  fun e => signOfInt (b.1.1 e)

theorem patternCurrent_branchPattern {P : (E → ℤ) → Prop} (q : E → ℕ)
    (b : PredBranch P) (hb : PredBranch.assignment b = q) :
    patternCurrent q (branchPattern b) = b.1.1 := by
  funext e
  have hassign := congrFun hb e
  change ModeBranch.assignment
      (fun j : {j : E → ℤ // P j} => j.1) b e = q e at hassign
  by_cases hz : b.1.1 e = 0
  · simp [patternCurrent, branchPattern, signOfInt, hz]
  · have hnat : (b.1.1 e).natAbs - 1 = q e := by
      simpa [ModeBranch.assignment, hz] using hassign
    have hpos := Int.natAbs_pos.mpr hz
    have habs : (b.1.1 e).natAbs = q e + 1 := by omega
    unfold patternCurrent branchPattern
    rw [← habs, signZ_signOfInt_mul_natAbs]

/-- The inactive modes that a branch over `q` must carry. -/
noncomputable def canonicalInactiveModes {P : (E → ℤ) → Prop} (q : E → ℕ)
    (j : {j : E → ℤ // P j}) :
    Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ :=
  fun i => q ((Fintype.equivFin {e : E // j.1 e = 0}).symm i).1

theorem canonicalInactiveModes_heq {P : (E → ℤ) → Prop} (q : E → ℕ)
    (j j' : {j : E → ℤ // P j}) (h : j = j') :
    canonicalInactiveModes q j ≍ canonicalInactiveModes q j' := by
  cases h
  rfl

theorem branch_modes_eq_canonical {P : (E → ℤ) → Prop} (q : E → ℕ)
    (b : PredBranch P) (hb : PredBranch.assignment b = q) :
    b.2 = canonicalInactiveModes q b.1 := by
  funext i
  let e0 := (Fintype.equivFin {e : E // b.1.1 e = 0}).symm i
  have hq := congrFun hb e0.1
  have heq : b.1.1 e0.1 = 0 := e0.2
  have hmode : b.2 i = q e0.1 := by
    simpa [PredBranch.assignment, ModeBranch.assignment, heq, e0] using hq
  simpa [canonicalInactiveModes, e0] using hmode

/-- The raw branch of a closed sign pattern. -/
noncomputable def patternBranch (P : (E → ℤ) → Prop) (q : E → ℕ)
    (σ : ClosedPattern P q) : PredBranch P :=
  ⟨⟨patternCurrent q σ.1, σ.2⟩, canonicalInactiveModes q ⟨patternCurrent q σ.1, σ.2⟩⟩

theorem patternBranch_assignment (P : (E → ℤ) → Prop) (q : E → ℕ)
    (σ : ClosedPattern P q) :
    PredBranch.assignment (patternBranch P q σ) = q := by
  funext e
  dsimp only [PredBranch.assignment, ModeBranch.assignment, patternBranch,
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

/-- The branch of a closed sign pattern. -/
noncomputable def patternToBranch (P : (E → ℤ) → Prop) (q : E → ℕ)
    (σ : ClosedPattern P q) : PredAssignmentFiber P q :=
  ⟨patternBranch P q σ, patternBranch_assignment P q σ⟩

theorem branchPattern_closed (P : (E → ℤ) → Prop) (q : E → ℕ)
    (b : PredAssignmentFiber P q) :
    P (patternCurrent q (branchPattern b.1)) := by
  rw [patternCurrent_branchPattern q b.1 b.2]
  exact b.1.1.2

/-- The closed sign pattern of a branch over `q`. -/
def branchToPattern (P : (E → ℤ) → Prop) (q : E → ℕ)
    (b : PredAssignmentFiber P q) : ClosedPattern P q :=
  ⟨branchPattern b.1, branchPattern_closed P q b⟩

theorem branchToPattern_patternToBranch (P : (E → ℤ) → Prop) (q : E → ℕ)
    (σ : ClosedPattern P q) : branchToPattern P q (patternToBranch P q σ) = σ := by
  apply Subtype.ext
  funext e
  change signOfInt (patternCurrent q σ.1 e) = σ.1 e
  unfold patternCurrent
  exact signOfInt_signZ_mul _ _ (Nat.succ_pos _)

theorem patternToBranch_branchToPattern (P : (E → ℤ) → Prop) (q : E → ℕ)
    (b : PredAssignmentFiber P q) : patternToBranch P q (branchToPattern P q b) = b := by
  rcases b with ⟨br, hb⟩
  apply Subtype.ext
  change (patternToBranch P q (branchToPattern P q ⟨br, hb⟩)).1 = br
  have hbase : (patternToBranch P q (branchToPattern P q ⟨br, hb⟩)).1.1 = br.1 := by
    apply Subtype.ext
    exact patternCurrent_branchPattern q br hb
  refine Sigma.ext hbase ?_
  have hleft : (patternToBranch P q (branchToPattern P q ⟨br, hb⟩)).1.2 =
      canonicalInactiveModes q (patternToBranch P q (branchToPattern P q ⟨br, hb⟩)).1.1 := rfl
  have hright : br.2 = canonicalInactiveModes q br.1 := branch_modes_eq_canonical q br hb
  exact (heq_of_eq hleft).trans
    ((canonicalInactiveModes_heq q
      (patternToBranch P q (branchToPattern P q ⟨br, hb⟩)).1.1 br.1 hbase).trans
        (heq_of_eq hright).symm)

/-- The assignment fibre is the set of closed sign patterns. -/
noncomputable def assignmentFiberEquiv (P : (E → ℤ) → Prop) (q : E → ℕ) :
    ClosedPattern P q ≃ PredAssignmentFiber P q where
  toFun := patternToBranch P q
  invFun := branchToPattern P q
  left_inv := branchToPattern_patternToBranch P q
  right_inv := patternToBranch_branchToPattern P q

theorem patternToBranch_current (P : (E → ℤ) → Prop) (q : E → ℕ)
    (σ : ClosedPattern P q) : (patternToBranch P q σ).1.1.1 = patternCurrent q σ.1 := rfl

/-- The relative coefficient of the branch of a pattern is the product of its sign
coefficients. -/
theorem relativeCoefficient_patternToBranch (P : (E → ℤ) → Prop) (q : E → ℕ)
    (z : ℕ → ℝ) (hz : ∀ n, 0 < z (positiveMode n)) (σ : ClosedPattern P q) :
    ((PredBranch.relativeCoefficient z q (patternToBranch P q σ).1 : ℝ) : ℂ) =
      ∏ e, signCoeff (z (positiveMode (q e))) (σ.1 e) := by
  rw [PredBranch.relativeCoefficient, modeBranch_relativeCoefficient_eq_selectedProduct
    (fun j : {j : E → ℤ // P j} => j.1) z q
    (patternToBranch P q σ).1 (patternToBranch P q σ).2 hz, patternToBranch_current,
    Finset.prod_filter, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [signCoeff_eq]
  by_cases hσ : σ.1 e = 0
  · have h0 : patternCurrent q σ.1 e = 0 := (patternCurrent_eq_zero_iff q σ.1 e).mpr hσ
    simp [hσ, h0]
  · have h0 : patternCurrent q σ.1 e ≠ 0 := fun h => hσ ((patternCurrent_eq_zero_iff q σ.1 e).mp h)
    simp [hσ, h0]

/-- **The fibre sum as a sum over sign patterns.** -/
theorem predAssignmentFiberSum_eq_patternSum [DecidableEq E] (P : (E → ℤ) → Prop) (q : E → ℕ)
    (z : ℕ → ℝ) (hz : ∀ n, 0 < z (positiveMode n)) (F G : (E → ℤ) → ℂ)
    (hFG : ∀ j, P j → F j = G j)
    (hG : ∀ j, ¬ P j → G j = 0) :
    assignmentFiberMoment (PredBranch.assignment (P := P))
        (PredBranch.relativeCoefficient (P := P) z)
        (fun b => F b.1.1) q =
      ∑ σ : E → Sign, (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) *
        G (patternCurrent q σ) := by
  classical
  unfold assignmentFiberMoment
  rw [← (assignmentFiberEquiv P q).tsum_eq, tsum_fintype]
  have hterm : ∀ σ : ClosedPattern P q,
      ((PredBranch.relativeCoefficient z q
          ((assignmentFiberEquiv P q) σ).1 : ℝ) : ℂ) * F ((assignmentFiberEquiv P q) σ).1.1.1 =
        (∏ e, signCoeff (z (positiveMode (q e))) (σ.1 e)) * G (patternCurrent q σ.1) := by
    intro σ
    change ((PredBranch.relativeCoefficient z q
      (patternToBranch P q σ).1 : ℝ) : ℂ) * F (patternToBranch P q σ).1.1.1 = _
    rw [relativeCoefficient_patternToBranch P q z hz σ, patternToBranch_current, hFG _ σ.2]
  simp_rw [hterm]
  rw [← Finset.sum_subtype (Finset.univ.filter fun σ : E → Sign =>
      P (patternCurrent q σ)) (by simp)
    (fun σ => (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) * G (patternCurrent q σ))]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro σ _ hσ
  have hσ' : ¬ P (patternCurrent q σ) := by simpa using hσ
  rw [hG _ hσ', mul_zero]


/-! ## The regrouping -/

/-- Absolutely convergent regrouping of the branches over the currents with the predicate `P`:
the inactive modes have total mass one. -/
theorem predRegroup_hasSum (P : (E → ℤ) → Prop) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1) (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (Char : {j : E → ℤ // P j} → ℂ) (hChar : Summable Char) :
    HasSum (fun b : PredBranch P =>
      (ModeBranch.coefficient (fun j : {j : E → ℤ // P j} => j.1) z b : ℂ) * Char b.1)
      (∑' j, Char j) := by
  classical
  have hcoef0 : ∀ b : PredBranch P,
      0 ≤ ModeBranch.coefficient (fun j : {j : E → ℤ // P j} => j.1) z b := fun b =>
    Finset.prod_nonneg fun _ _ => hweight_nonneg _
  apply HasSum.sigma_of_hasSum hChar.hasSum
  · intro j
    have hs : HasSum (fun q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ =>
        ((∏ i, inactiveWeight z (q i) : ℝ) : ℂ)) 1 :=
      (Complex.hasSum_ofReal).mpr (hasSum_fin_inactiveWeight_one z hnorm hweight_nonneg _)
    convert HasSum.mul_right (Char j) hs using 1
    · rfl
    · exact (one_mul _).symm
  · let f : PredBranch P → ℝ := fun b =>
      ModeBranch.coefficient (fun j : {j : E → ℤ // P j} => j.1) z b * ‖Char b.1‖
    have hf_nonneg (b : PredBranch P) : 0 ≤ f b := mul_nonneg (hcoef0 b) (norm_nonneg _)
    have hf_fiber (j : {j : E → ℤ // P j}) :
        Summable (fun q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ =>
          f (⟨j, q⟩ : PredBranch P)) :=
      (hasSum_fin_inactiveWeight_one z hnorm hweight_nonneg
        (Fintype.card {e : E // j.1 e = 0})).summable.mul_right ‖Char j‖
    have hf_fiber_tsum (j : {j : E → ℤ // P j}) :
        (∑' q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ,
          f (⟨j, q⟩ : PredBranch P)) = ‖Char j‖ := by
      have hscaled := (hasSum_fin_inactiveWeight_one z hnorm hweight_nonneg
        (Fintype.card {e : E // j.1 e = 0})).mul_right ‖Char j‖
      change (∑' q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ,
        (∏ i, inactiveWeight z (q i)) * ‖Char j‖) = ‖Char j‖
      simpa using hscaled.tsum_eq
    have hf_outer : Summable (fun j : {j : E → ℤ // P j} =>
        ∑' q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ,
          f (⟨j, q⟩ : PredBranch P)) :=
      hChar.norm.congr fun j => (hf_fiber_tsum j).symm
    have hf_sigma : Summable f :=
      (summable_sigma_of_nonneg hf_nonneg).2 ⟨hf_fiber, hf_outer⟩
    refine Summable.of_norm_bounded hf_sigma fun b => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcoef0 b)]

/-! ## The sum over closed currents as a mixture of gauge-averaged integrals -/

variable {V : Type*} [Fintype V] [DecidableEq E]

/-- The integral of the cosine product of a mode assignment, as a sum over sign patterns. -/
theorem assignment_integral_eq_patternSum (D : V → E → ℤ) {S : Matrix E E ℝ}
    (hS : S.PosSemidef) (shift : E → ℝ) (z : ℕ → ℝ) (q : E → ℕ) :
    ((∫ ω, ∏ e, (1 + z (positiveMode (q e)) *
        Real.cos ((gaugeFieldD D ω e + shift e) * ((q e + 1 : ℕ) : ℝ)))
          ∂gaugeMeasureD V S : ℝ) : ℂ) =
      ∑ σ : E → Sign, (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) *
        (Complex.exp (Complex.I * (linkPairing shift (patternCurrent q σ) : ℝ)) *
          characterValueD D S (patternCurrent q σ)) := by
  have hint := integral_cosineProductD (V := V) D hS (fun e => z (positiveMode (q e)))
    (fun e => shift e * ((q e + 1 : ℕ) : ℝ)) (assignmentCurrent q)
  have hfun : (fun ω : EuclideanSpace ℝ E × (V → ℝ) =>
      ∏ e, (1 + z (positiveMode (q e)) *
        Real.cos (linkPairing (gaugeFieldD D ω) (assignmentCurrent q e) +
          shift e * ((q e + 1 : ℕ) : ℝ)))) =
      fun ω => ∏ e, (1 + z (positiveMode (q e)) *
        Real.cos ((gaugeFieldD D ω e + shift e) * ((q e + 1 : ℕ) : ℝ))) := by
    funext ω
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [linkPairing_assignmentCurrent, add_mul]
  rw [hfun] at hint
  rw [hint]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [signedSum_assignmentCurrent]
  have hw : signWeight (fun e => z (positiveMode (q e)))
      (fun e => shift e * ((q e + 1 : ℕ) : ℝ)) σ =
      (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) *
        Complex.exp (Complex.I * (linkPairing shift (patternCurrent q σ) : ℝ)) := by
    unfold signWeight
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum]
    congr 4
    unfold linkPairing patternCurrent
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [signValue_eq_signZ]
    push_cast
    ring
  rw [hw]
  ring

/-- **The sum over closed integer currents as a mixture over mode assignments.** -/
theorem closedCharacterSum_hasSum_assignment (D : V → E → ℤ) {S : Matrix E E ℝ}
    (hS : S.PosSemidef) (shift : E → ℝ) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1) (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q))
    (hsum : Summable fun j : {j : E → ℤ // ClosedD D j} =>
      Real.exp (-(quadraticD S j.1 / 2))) :
    HasSum (fun q : E → ℕ => (assignmentCoefficient z q : ℂ) *
        ((∫ ω, ∏ e, (1 + z (positiveMode (q e)) *
            Real.cos ((gaugeFieldD D ω e + shift e) * ((q e + 1 : ℕ) : ℝ)))
              ∂gaugeMeasureD V S : ℝ) : ℂ))
      (∑' j : {j : E → ℤ // ClosedD D j},
        Complex.exp (Complex.I * (linkPairing shift j.1 : ℝ)) *
          Complex.exp (-(quadraticD S j.1 / 2 : ℝ))) := by
  classical
  let F : (E → ℤ) → ℂ := fun j =>
    Complex.exp (Complex.I * (linkPairing shift j : ℝ)) * Complex.exp (-(quadraticD S j / 2 : ℝ))
  have hChar : Summable fun j : {j : E → ℤ // ClosedD D j} => F j.1 := by
    refine Summable.of_norm ?_
    refine hsum.congr fun j => ?_
    simp only [F]
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hReg := predRegroup_hasSum (ClosedD D) z hnorm hweight_nonneg
    (fun j : {j : E → ℤ // ClosedD D j} => F j.1) hChar
  have hfactor (b : PredBranch (ClosedD D)) :
      ModeBranch.coefficient (fun j : {j : E → ℤ // ClosedD D j} => j.1) z b =
        assignmentCoefficient z (PredBranch.assignment b) *
          PredBranch.relativeCoefficient z (PredBranch.assignment b) b := by
    have hc : assignmentCoefficient z (PredBranch.assignment b) ≠ 0 :=
      ne_of_gt (assignmentCoefficient_pos z _ hz)
    unfold PredBranch.relativeCoefficient assignmentRelativeCoefficient
    field_simp
  have hGrouped := hasSum_assignment_factor (PredBranch.assignment (P := ClosedD D))
    (fun q => modeBranch_assignmentFiber_finite
      (fun j : {j : E → ℤ // ClosedD D j} => j.1) Subtype.val_injective q)
    (fun b => ModeBranch.coefficient (fun j : {j : E → ℤ // ClosedD D j} => j.1) z b)
    (fun q => assignmentCoefficient z q)
    (PredBranch.relativeCoefficient (P := ClosedD D) z)
    (fun b => F b.1.1) _ hfactor hReg
  convert hGrouped using 1
  funext q
  congr 1
  rw [assignment_integral_eq_patternSum D hS shift z q]
  symm
  refine predAssignmentFiberSum_eq_patternSum (ClosedD D) q z hz F
    (fun j => Complex.exp (Complex.I * (linkPairing shift j : ℝ)) * characterValueD D S j)
    ?_ ?_
  · intro j hj
    rw [characterValueD_of_closed D S hj]
  · intro j hj
    rw [characterValueD_of_not_closed D S hj, mul_zero]

end FroehlichSpencer.FS82.XY.DualD

end
