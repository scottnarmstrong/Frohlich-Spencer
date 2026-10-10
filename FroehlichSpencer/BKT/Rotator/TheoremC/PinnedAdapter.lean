/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.Defs
public import FroehlichSpencer.BKT.Generic.Moment.Offset
public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter
public import FroehlichSpencer.BKT.Generic.EdgeLaw.Shear
public import FroehlichSpencer.BKT.Rotator.BesselInterp.Properties
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The augmented carrier and the rooted comb integral (FS81 Theorem C, finite comb duality)

The pinned dual of the free spin box (FS81 (1.35)) is carried by two isomorphic multigraphs on the
same vertex type `RotatorDualFace L` (bounded faces and the wired exterior `none`): the
`squareZero L`, on which the pinned charge layer is built (`Generic/PinnedCharges/WiredAdapter`),
and the dual-face graph `rotatorDualGraph L`, on which the finite XY duality and the comb live
(`Rotator/FreeBox`, `Rotator/FiniteComb`).

The isomorphism fixes the vertices and may reverse
edge orientations.

* `squareZeroField L θ`: an edge field on `rotatorDualGraph L` read on `squareZero L` with the
  orientation sign.

The root phase is sheared away (`integral_comp_shear`), the root integral gives
  `2π`, and the bounded faces are rescaled by `2π` (`integral_comp_smul`).

No integrability is
  needed: every step is a change of variables or a product integral.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open MeasureTheory
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges
  (squareZero_dualFace_carrier_isomorphism SquareZeroBond)
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-! ## Transport between `squareZero L` and `rotatorDualGraph L` -/

/-- The carrier isomorphism fixes the vertices and preserves each edge up to orientation. -/
theorem squareZero_iso_endpoints (L : ℕ) (e : SquareZeroBond L) :
    ((rotatorDualGraph L).src ((squareZero_dualFace_carrier_isomorphism L).edges e) =
        (squareZero L).src e ∧
      (rotatorDualGraph L).tgt ((squareZero_dualFace_carrier_isomorphism L).edges e) =
        (squareZero L).tgt e) ∨
    ((rotatorDualGraph L).src ((squareZero_dualFace_carrier_isomorphism L).edges e) =
        (squareZero L).tgt e ∧
      (rotatorDualGraph L).tgt ((squareZero_dualFace_carrier_isomorphism L).edges e) =
        (squareZero L).src e) :=
  (squareZero_dualFace_carrier_isomorphism L).endpoints e

/-- An edge field on the dual-face graph read on `squareZero` with its orientation. -/
def squareZeroField (L : ℕ) (θ : RotatorInternalBond L → ℝ) : SquareZeroBond L → ℝ := fun e =>
  if (rotatorDualGraph L).src ((squareZero_dualFace_carrier_isomorphism L).edges e) =
      (squareZero L).src e
  then θ ((squareZero_dualFace_carrier_isomorphism L).edges e)
  else -θ ((squareZero_dualFace_carrier_isomorphism L).edges e)

theorem squareZeroField_eq_or (L : ℕ) (θ : RotatorInternalBond L → ℝ) (e : SquareZeroBond L) :
    squareZeroField L θ e = θ ((squareZero_dualFace_carrier_isomorphism L).edges e) ∨
      squareZeroField L θ e = -θ ((squareZero_dualFace_carrier_isomorphism L).edges e) := by
  unfold squareZeroField
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem squareZeroField_grad (L : ℕ) (σ : RotatorDualFace L → ℝ) :
    squareZeroField L (fun e => (rotatorDualGraph L).grad σ e) =
      fun e => (squareZero L).grad σ e := by
  funext e
  unfold squareZeroField
  rcases squareZero_iso_endpoints L e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simp only [Multigraph.grad, hs, ht, ↓reduceIte]
  · have hne : ¬ (rotatorDualGraph L).src ((squareZero_dualFace_carrier_isomorphism L).edges e) =
        (squareZero L).src e := by
      rw [hs]; exact fun h => (squareZero L).src_ne_tgt e h.symm
    simp only [hne, ↓reduceIte]
    simp only [Multigraph.grad, hs, ht, neg_sub]

theorem squareZeroField_add (L : ℕ) (θ₁ θ₂ : RotatorInternalBond L → ℝ) :
    squareZeroField L (θ₁ + θ₂) = squareZeroField L θ₁ + squareZeroField L θ₂ := by
  funext e
  simp only [squareZeroField, Pi.add_apply]
  split_ifs <;> simp only [neg_add]

theorem sum_sq_squareZeroField (L : ℕ) (θ : RotatorInternalBond L → ℝ) :
    ∑ e, squareZeroField L θ e ^ 2 = ∑ e, θ e ^ 2 := by
  calc ∑ e, squareZeroField L θ e ^ 2
      = ∑ e, θ ((squareZero_dualFace_carrier_isomorphism L).edges e) ^ 2 := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rcases squareZeroField_eq_or L θ e with h | h <;> rw [h]
        rw [neg_sq]
    _ = ∑ e, θ e ^ 2 :=
        Equiv.sum_comp (squareZero_dualFace_carrier_isomorphism L).edges (fun e => θ e ^ 2)

theorem squareZeroField_eq_add_intMul_or (L : ℕ) (j : RotatorInternalBond L → ℤ)
    (e : SquareZeroBond L) :
    ∃ n : ℤ, squareZeroField L (fun e => 2 * Real.pi * (j e : ℝ)) e = n * (2 * Real.pi) := by
  rcases squareZeroField_eq_or L (fun e => 2 * Real.pi * (j e : ℝ)) e with h | h
  · exact ⟨j ((squareZero_dualFace_carrier_isomorphism L).edges e), by rw [h]; ring⟩
  · exact ⟨-j ((squareZero_dualFace_carrier_isomorphism L).edges e), by rw [h]; push_cast; ring⟩

section Densities

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- An even weight does not see the orientation sign. -/
theorem prod_re_squareZeroField (hw : Generic.IsStripWeight w W c) (L : ℕ)
    (F : RotatorInternalBond L → ℝ) :
    ∏ e, (w ((squareZeroField L F e : ℝ) : ℂ)).re = ∏ e, (w ((F e : ℝ) : ℂ)).re := by
  have heven : ∀ a : ℝ, (w ((-a : ℝ) : ℂ)).re = (w ((a : ℝ) : ℂ)).re := fun a => by
    rw [Complex.ofReal_neg, hw.even _ (by simpa using hw.width_nonneg)]
  calc ∏ e, (w ((squareZeroField L F e : ℝ) : ℂ)).re
      = ∏ e, (w ((F ((squareZero_dualFace_carrier_isomorphism L).edges e) : ℝ) : ℂ)).re := by
        refine Finset.prod_congr rfl fun e _ => ?_
        rcases squareZeroField_eq_or L F e with h | h <;> rw [h]
        exact heven _
    _ = ∏ e, (w ((F e : ℝ) : ℂ)).re :=
        Equiv.prod_comp (squareZero_dualFace_carrier_isomorphism L).edges
          (fun e => (w ((F e : ℝ) : ℂ)).re)

theorem edgeDensity_squareZero (hw : Generic.IsStripWeight w W c) (L : ℕ)
    (φ : RotatorDualFace L → ℝ) :
    Generic.edgeDensity (squareZero L) w none φ =
      Generic.edgeDensity (rotatorDualGraph L) w none φ := by
  unfold Generic.edgeDensity
  congr 1
  have h := congrFun (squareZeroField_grad L φ)
  simp_rw [← h]
  exact prod_re_squareZeroField hw L _

theorem offsetEdgeDensity_squareZeroField (hw : Generic.IsStripWeight w W c) (L : ℕ)
    (θ : RotatorInternalBond L → ℝ) (φ : RotatorDualFace L → ℝ) :
    Generic.offsetEdgeDensity (squareZero L) w (squareZeroField L θ) none φ =
      Generic.offsetEdgeDensity (rotatorDualGraph L) w θ none φ := by
  unfold Generic.offsetEdgeDensity
  congr 1
  have h : ∀ e, (squareZero L).grad φ e + squareZeroField L θ e =
      squareZeroField L ((fun e => (rotatorDualGraph L).grad φ e) + θ) e := fun e => by
    rw [squareZeroField_add, Pi.add_apply, squareZeroField_grad]
  simp_rw [h]
  exact prod_re_squareZeroField hw L _

end Densities

/-! ## The comb in the angle variable -/

/-- Folding a symmetric integer sum. -/
theorem sum_Icc_int_eq (N : ℕ) (h : ℤ → ℂ) :
    ∑ q ∈ Finset.Icc (-(N : ℤ)) N, h q = h 0 + ∑ n ∈ Finset.Icc 1 N, (h n + h (-(n : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    have h1 : ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]; push_cast; omega
    have h2 : -((N + 1 : ℕ) : ℤ) ∉ insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
    rw [hset, Finset.sum_insert h2, Finset.sum_insert h1, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast
    ring

theorem exp_add_exp_neg_mul_I (a : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) + Complex.exp (((-a : ℝ) : ℂ) * Complex.I) =
      2 * ((Real.cos a : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos]
  ring

/-- One site of the box comb is the Dirichlet comb in the angle variable. -/
theorem sum_Icc_exp_eq_dirichletComb (N : ℕ) (t : ℝ) :
    ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
        Complex.exp (((-2 * Real.pi * (t * (q : ℝ)) : ℝ) : ℂ) * Complex.I) =
      ((dirichletComb N (2 * Real.pi * t) : ℝ) : ℂ) := by
  rw [sum_Icc_int_eq]
  unfold dirichletComb
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      Complex.exp (((-2 * Real.pi * (t * ((n : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I) +
        Complex.exp (((-2 * Real.pi * (t * ((-(n : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I) =
      2 * ((Real.cos ((n : ℝ) * (2 * Real.pi * t)) : ℝ) : ℂ) := by
    intro n _
    have h := exp_add_exp_neg_mul_I (-2 * Real.pi * (t * ((n : ℤ) : ℝ)))
    have ha : (-(-2 * Real.pi * (t * ((n : ℤ) : ℝ))) : ℝ) =
        -2 * Real.pi * (t * ((-(n : ℤ) : ℤ) : ℝ)) := by push_cast; ring
    have hc : Real.cos (-2 * Real.pi * (t * ((n : ℤ) : ℝ))) =
        Real.cos ((n : ℝ) * (2 * Real.pi * t)) := by
      rw [← Real.cos_neg]; congr 1; push_cast; ring
    rw [ha, hc] at h
    exact h
  rw [Finset.sum_congr rfl hterm]
  simp only [Int.cast_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  push_cast
  rw [Finset.mul_sum]

/-- The box comb is the product of the one-site Dirichlet combs, a real function. -/
theorem faceCombCutoff_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) (x : ι → ℝ) :
    faceCombCutoff (ι := ι) N x = ((∏ i, dirichletComb N (2 * Real.pi * x i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod]
  simp_rw [← sum_Icc_exp_eq_dirichletComb]
  rw [Finset.prod_sum]
  unfold faceCombCutoff faceFrequencyBox
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold faceCombMode
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul, Finset.sum_attach Finset.univ
    (fun i => (((-2 * Real.pi * (x i * (q i (Finset.mem_univ i) : ℝ)) : ℝ) : ℂ))),
    ← Complex.ofReal_sum, ← Finset.mul_sum]

/-! ## The rooted comb integral -/

/-- The root-phase shear: `ψ ↦ ψ + ψ(root) 1_{bounded}`. -/
def rootShearVector (L : ℕ) : RotatorDualFace L → ℝ := fun k => k.elim 0 (fun _ => 1)

/-- The sheared field is the zero extension of the bounded coordinates plus the root phase. -/
theorem shear_rootShearVector_apply (L : ℕ) (φ : RotatorDualFace L → ℝ) (k : RotatorDualFace L) :
    Generic.shear none (rootShearVector L) φ k =
      (rotatorPinnedRealFieldOfCoords (fun x => φ (some x))).1 k + φ none := by
  rw [Generic.shear_apply_apply]
  cases k with
  | none => simp [rootShearVector, rotatorPinnedRealFieldOfCoords]
  | some x => simp [rootShearVector, rotatorPinnedRealFieldOfCoords]

/-- The bounded-coordinate integrand of the rooted comb integral. -/
def pinnedCombIntegrand (L N : ℕ) (β : ℝ) (j : RotatorInternalBond L → ℤ)
    (y : SquareFreeVertex L → ℝ) : ℝ :=
  (∏ e, (besselWeightψ β (((rotatorDualGraph L).grad (rotatorPinnedRealFieldOfCoords y).1 e +
    2 * Real.pi * (j e : ℝ) : ℝ) : ℂ)).re) * ∏ x, dirichletComb N (y x)

theorem offsetEdgeDensity_pinnedComb_shear (L N : ℕ) (β : ℝ) (j : RotatorInternalBond L → ℤ)
    (φ : RotatorDualFace L → ℝ) :
    (fun ψ : RotatorDualFace L → ℝ =>
        Generic.offsetEdgeDensity (rotatorDualGraph L) (besselWeightψ β)
          (fun e => 2 * Real.pi * (j e : ℝ)) none ψ *
        ∏ k, pinnedCombLam L N k (ψ k - ψ none)) (Generic.shear none (rootShearVector L) φ) =
      (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ none) *
        pinnedCombIntegrand L N β j (fun x => φ (some x)) := by
  simp only
  have hψ := shear_rootShearVector_apply L φ
  have hnone : Generic.shear none (rootShearVector L) φ none = φ none := by
    rw [hψ]; simp [rotatorPinnedRealFieldOfCoords]
  have hgrad : ∀ e, (rotatorDualGraph L).grad (Generic.shear none (rootShearVector L) φ) e =
      (rotatorDualGraph L).grad (rotatorPinnedRealFieldOfCoords (fun x => φ (some x))).1 e := by
    intro e
    simp only [Multigraph.grad, hψ]
    ring
  have hcomb : ∏ k, pinnedCombLam L N k (Generic.shear none (rootShearVector L) φ k -
      Generic.shear none (rootShearVector L) φ none) = ∏ x, dirichletComb N (φ (some x)) := by
    rw [Fintype.prod_option]
    simp only [pinnedCombLam, Option.elim, one_mul, hψ]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [rotatorPinnedRealFieldOfCoords]
  unfold Generic.offsetEdgeDensity pinnedCombIntegrand
  rw [hcomb, hnone]
  simp_rw [hgrad]
  ring

theorem measurePreserving_piOptionEquivProd_symm (α : Type) [Fintype α] :
    MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm
      ((Measure.pi fun _ : α => (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (volume : Measure (Option α → ℝ)) := by
  refine ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm.measurable, ?_⟩
  rw [volume_pi]
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option α => (volume : Measure ℝ))

/-- Splitting off the root coordinate. -/
theorem integral_option_mul (α : Type) [Fintype α] (f : ℝ → ℝ) (g : (α → ℝ) → ℝ) :
    ∫ φ : Option α → ℝ, f (φ none) * g (fun x => φ (some x)) =
      (∫ t, f t) * ∫ y, g y := by
  rw [← (measurePreserving_piOptionEquivProd_symm α).integral_comp
    (MeasurableEquiv.measurableEmbedding _)]
  have h : ∀ p : (α → ℝ) × ℝ,
      f ((MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm p none) *
        g (fun x => (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm p (some x)) =
      g p.1 * f p.2 := fun p => by rw [mul_comm]; rfl
  simp_rw [h]
  rw [integral_prod_mul, mul_comm, volume_pi]

theorem integral_indicator_Ico_pi :
    ∫ t : ℝ, (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) t = 2 * Real.pi := by
  rw [integral_indicator_one measurableSet_Ico, Real.volume_real_Ico]
  rw [max_eq_left (by linarith [Real.pi_pos])]
  ring

theorem rotatorPinnedRealFieldOfCoords_smul {L : ℕ} (R : ℝ) (y : SquareFreeVertex L → ℝ)
    (k : RotatorDualFace L) :
    (rotatorPinnedRealFieldOfCoords (R • y)).1 k = R * (rotatorPinnedRealFieldOfCoords y).1 k := by
  cases k with
  | none => show (0 : ℝ) = R * 0; ring
  | some x => rfl

theorem besselWeightψ_two_pi_mul {β : ℝ} (a : ℝ) :
    besselWeightψ β ((2 * Real.pi * a : ℝ) : ℂ) = besselInterp β (a : ℂ) := by
  unfold besselWeightψ
  congr 1
  have h2πc : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  push_cast
  exact mul_div_cancel_left₀ _ h2πc

theorem pinnedCombIntegrand_smul (L N : ℕ) {β : ℝ} (hβ : 0 < β) (j : RotatorInternalBond L → ℤ)
    (y : SquareFreeVertex L → ℝ) :
    ((pinnedCombIntegrand L N β j ((2 * Real.pi) • y) : ℝ) : ℂ) =
      faceCombCutoff (ι := SquareFreeVertex L) N y * rotatorPinnedMarkedDensityCoords L β j y := by
  have hreal : ∀ a : ℝ, (((besselInterp β (a : ℂ)).re : ℝ) : ℂ) = besselInterp β (a : ℂ) :=
    fun a => Complex.ext rfl (by simp [(besselInterp_ofReal_im_eq_zero_and_re_pos hβ a).1])
  have hedge : ∀ e, (besselWeightψ β (((rotatorDualGraph L).grad
      (rotatorPinnedRealFieldOfCoords ((2 * Real.pi) • y)).1 e + 2 * Real.pi * (j e : ℝ) : ℝ) :
        ℂ)).re =
      (besselInterp β ((((rotatorPinnedRealFieldOfCoords y).1 ((rotatorDualGraph L).src e) -
        (rotatorPinnedRealFieldOfCoords y).1 ((rotatorDualGraph L).tgt e) + (j e : ℝ) : ℝ)) :
          ℂ)).re := by
    intro e
    rw [← besselWeightψ_two_pi_mul]
    congr 3
    simp only [Multigraph.grad, rotatorPinnedRealFieldOfCoords_smul]
    ring
  have hB : rotatorPinnedMarkedDensityCoords L β j y =
      ((∏ e, (besselInterp β ((((rotatorPinnedRealFieldOfCoords y).1 ((rotatorDualGraph L).src e) -
        (rotatorPinnedRealFieldOfCoords y).1 ((rotatorDualGraph L).tgt e) + (j e : ℝ) : ℝ)) :
          ℂ)).re : ℝ) : ℂ) := by
    unfold rotatorPinnedMarkedDensityCoords
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun e _ => (hreal _).symm
  rw [faceCombCutoff_eq_prod, hB, ← Complex.ofReal_mul]
  congr 1
  unfold pinnedCombIntegrand
  simp_rw [hedge]
  rw [mul_comm]
  rfl

/-- **The rooted comb integral is the pinned comb pairing** (finite comb duality, angle variable).
-/
theorem integral_offsetEdgeDensity_pinnedComb {L : ℕ} (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (j : RotatorInternalBond L → ℤ) :
    ∫ φ : RotatorDualFace L → ℝ,
        Generic.offsetEdgeDensity (rotatorDualGraph L) (besselWeightψ β)
          (fun e => 2 * Real.pi * (j e : ℝ)) none φ *
        ∏ k, pinnedCombLam L N k (φ k - φ none) =
      (2 * Real.pi) ^ (Fintype.card (SquareFreeVertex L) + 1) *
        (rotatorPinnedMarkedCombCutoffPairing L β j N).re := by
  have hu : rootShearVector L none = 0 := rfl
  rw [← Generic.integral_comp_shear hu]
  simp_rw [offsetEdgeDensity_pinnedComb_shear]
  rw [integral_option_mul (SquareFreeVertex L) _ (pinnedCombIntegrand L N β j),
    integral_indicator_Ico_pi]
  -- rescale the bounded coordinates by `2π`
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsmul := Measure.integral_comp_smul (volume : Measure (SquareFreeVertex L → ℝ))
    (pinnedCombIntegrand L N β j) (2 * Real.pi)
  rw [Module.finrank_fintype_fun_eq_card, abs_of_pos (inv_pos.mpr (pow_pos h2π _)),
    smul_eq_mul] at hsmul
  have hscale : ∫ y, pinnedCombIntegrand L N β j y =
      (2 * Real.pi) ^ Fintype.card (SquareFreeVertex L) *
        ∫ y, pinnedCombIntegrand L N β j ((2 * Real.pi) • y) := by
    rw [hsmul, ← mul_assoc, mul_inv_cancel₀ (pow_pos h2π _).ne', one_mul]
  have hpair : (rotatorPinnedMarkedCombCutoffPairing L β j N).re =
      ∫ y, pinnedCombIntegrand L N β j ((2 * Real.pi) • y) := by
    unfold rotatorPinnedMarkedCombCutoffPairing
    simp_rw [← pinnedCombIntegrand_smul L N hβ j]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [hscale, hpair, pow_succ]
  ring

end FroehlichSpencer.BKT.Rotator.TheoremC

end
