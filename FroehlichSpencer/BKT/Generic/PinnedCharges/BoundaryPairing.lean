/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.BasicLemmaIdentity
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
public import FroehlichSpencer.BKT.Generic.PinnedCharges.Geometry

/-! # Boundary-aware one-pair expansion and finite packing selection

The local four-branch identity is algebraic and remains valid when the pair
selection is made with Appendix D's `d_Λ` geometry. This module records that
adapter and the finite maximal-packing step. It does not identify this local
step with the missing multiscale selection theorem that also proves boundary
isolation for every constituent.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- The Appendix D pair threshold for two charge densities. -/
def boundaryPairThreshold {L : ℕ} (M α : ℝ)
    (ρ σ : ChargeDensity L) : ℝ :=
  M * min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) ^ α

/-- A pair is eligible for the Appendix D pairing step when its supports are
closer than the `d_Λ` threshold. -/
def IsBoundaryPairConflict {L : ℕ} (M α : ℝ)
    (ρ σ : ChargeDensity L) : Prop :=
  euclideanSetDistance (chargeSupport ρ) (chargeSupport σ) <
    boundaryPairThreshold M α ρ σ ∨
  euclideanSetDistance (chargeSupport σ) (chargeSupport ρ) <
    boundaryPairThreshold M α σ ρ

/-- A free-box graph distance is at most twice the Euclidean distance. The
factor two is the elementary `ℓ¹` to `ℓ²` comparison. -/
theorem freeDistance_le_two_euclideanSiteDistance {L : ℕ}
    (x y : Site L) :
    (latticeDistance .free L x y : ℝ) ≤ 2 * euclideanSiteDistance x y := by
  let dx : ℝ := (x.1.val : ℝ) - y.1.val
  let dy : ℝ := (x.2.val : ℝ) - y.2.val
  have hcoordX :
      ((if x.1.val ≤ y.1.val then y.1.val - x.1.val else x.1.val - y.1.val : ℕ) : ℝ) =
        |dx| := by
    by_cases hxy : x.1.val ≤ y.1.val
    · rw [ite_eq_left hxy]
      rw [abs_of_nonpos]
      · simp [dx, Nat.cast_sub hxy]
      · have hxyR : (x.1.val : ℝ) ≤ y.1.val := by exact_mod_cast hxy
        dsimp [dx]
        linarith
    · have hyx : y.1.val ≤ x.1.val := by omega
      rw [ite_eq_right hxy]
      rw [abs_of_nonneg]
      · simp [dx, Nat.cast_sub hyx]
      · have hyxR : (y.1.val : ℝ) ≤ x.1.val := by exact_mod_cast hyx
        dsimp [dx]
        linarith
  have hcoordY :
      ((if x.2.val ≤ y.2.val then y.2.val - x.2.val else x.2.val - y.2.val : ℕ) : ℝ) =
        |dy| := by
    by_cases hxy : x.2.val ≤ y.2.val
    · rw [ite_eq_left hxy]
      rw [abs_of_nonpos]
      · simp [dy, Nat.cast_sub hxy]
      · have hxyR : (x.2.val : ℝ) ≤ y.2.val := by exact_mod_cast hxy
        dsimp [dy]
        linarith
    · have hyx : y.2.val ≤ x.2.val := by omega
      rw [ite_eq_right hxy]
      rw [abs_of_nonneg]
      · simp [dy, Nat.cast_sub hyx]
      · have hyxR : (y.2.val : ℝ) ≤ x.2.val := by exact_mod_cast hyx
        dsimp [dy]
        linarith
  have hfree := freeDistance_le_coordinateSum L x y
  have hfreeR : (latticeDistance .free L x y : ℝ) ≤ |dx| + |dy| := by
    have hcast :
        (latticeDistance .free L x y : ℝ) ≤
          ((if x.1.val ≤ y.1.val then y.1.val - x.1.val
            else x.1.val - y.1.val) +
            (if x.2.val ≤ y.2.val then y.2.val - x.2.val
              else x.2.val - y.2.val) : ℕ) := by
      exact_mod_cast hfree
    rw [Nat.cast_add, hcoordX, hcoordY] at hcast
    exact hcast
  have hsq : ((|dx| + |dy|) / 2) ^ 2 ≤ dx ^ 2 + dy ^ 2 := by
    nlinarith [sq_nonneg (|dx| - |dy|), sq_abs dx, sq_abs dy]
  have hroot := Real.le_sqrt_of_sq_le hsq
  have hbound : |dx| + |dy| ≤ 2 * Real.sqrt (dx ^ 2 + dy ^ 2) := by linarith
  dsimp [euclideanSiteDistance, dx, dy]
  exact hfreeR.trans hbound

/-- The source's two-factor identity applied to any pair selected by the
boundary conflict rule. The four coefficients are exactly `1/3, 1/3, 1/6,
1/6`, and the updated pair weights are `3K₁`, `3K₂`, and `3K₁K₂`. -/
theorem boundaryPair_fourBranch_identity {L : ℕ} (M α : ℝ)
    (E : ChargeEnsemble L) (hPinned : IsPinnedChargeEnsemble E)
    (K : ChargeDensity L → ℝ)
    (ψ : (Fin L × Fin L) → ℝ)
    (ρ σ : ChargeDensity L) (hρ : ρ ∈ E) (hσ : σ ∈ E)
    (hne : ρ ≠ σ) (_hconflict : IsBoundaryPairConflict M α ρ σ) :
    let R := E.erase ρ |>.erase σ
    chargeFactorProduct E K ψ =
      (1 / 3 : ℝ) * chargeFactorProduct (insert ρ R)
          (pairRewriteFirstCoefficient K ρ) ψ +
        (1 / 3 : ℝ) * chargeFactorProduct (insert σ R)
          (pairRewriteSecondCoefficient K σ) ψ +
        (1 / 6 : ℝ) * chargeFactorProduct (insert (ρ - σ) R)
          (pairRewriteDifferenceCoefficient K ρ σ) ψ +
        (1 / 6 : ℝ) * chargeFactorProduct (insert (ρ + σ) R)
          (pairRewriteSumCoefficient K ρ σ) ψ := by
  have hE : IsBKTEnsemble E := by
    refine ⟨hPinned.1, ?_⟩
    intro τ hτ υ hυ hne'
    apply Set.disjoint_left.mpr
    intro x hxτ hxυ
    have hxτ' : x ∈ chargeSupport τ := by
      simpa [chargeSupport, Function.mem_support] using hxτ
    have hxυ' : x ∈ chargeSupport υ := by
      simpa [chargeSupport, Function.mem_support] using hxυ
    exact (Finset.disjoint_left.mp (hPinned.2 τ hτ υ hυ hne') hxτ') hxυ'
  exact chargeFactorProduct_pairBranches_identity E hE K ψ ρ σ hρ hσ hne

/-- The finite search space of subensembles satisfying Appendix D's pair
separation clause. -/
noncomputable def boundarySeparatedSubfamilies {L : ℕ} (M α : ℝ)
    (E : Finset (ChargeDensity L)) : Finset (Finset (ChargeDensity L)) := by
  classical
  exact E.powerset.filter (IsBoundarySeparated M α)

/-- Every finite family has a maximal-cardinality pairwise `d_Λ`-separated
subfamily. Every omitted density conflicts with at least one retained density.
This is the finite selection step used inside a boundary pairing iteration. -/
theorem exists_maximalBoundarySeparatedSubensemble {L : ℕ} (M α : ℝ)
    (E : Finset (ChargeDensity L)) :
    ∃ S : Finset (ChargeDensity L), S ⊆ E ∧
      IsBoundarySeparated M α S ∧
      ∀ ρ ∈ E \ S, ∃ σ ∈ S, σ ≠ ρ ∧ IsBoundaryPairConflict M α ρ σ := by
  classical
  let P := boundarySeparatedSubfamilies M α E
  have hP : P.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [P, boundarySeparatedSubfamilies, IsBoundarySeparated]
  obtain ⟨S, hSP, hSmax⟩ := Finset.exists_max_image P Finset.card hP
  have hSsub : S ⊆ E := Finset.mem_powerset.mp
    ((Finset.mem_filter.mp hSP).1)
  have hSsep : IsBoundarySeparated M α S := (Finset.mem_filter.mp hSP).2
  refine ⟨S, hSsub, hSsep, ?_⟩
  intro ρ hρE
  by_contra hno
  have hρnotS : ρ ∉ S := (Finset.mem_sdiff.mp hρE).2
  have hnoConflict : ∀ σ ∈ S, ¬ IsBoundaryPairConflict M α ρ σ := by
    intro σ hσ hconf
    apply hno
    refine ⟨σ, hσ, ?_, hconf⟩
    intro heq
    exact hρnotS (heq ▸ hσ)
  let T := insert ρ S
  have hTsub : T ⊆ E := by
    intro σ hσ
    rcases Finset.mem_insert.mp hσ with rfl | hσ
    · exact (Finset.mem_sdiff.mp hρE).1
    · exact hSsub hσ
  have hTsep : IsBoundarySeparated M α T := by
    intro τ hτ υ hυ hne
    by_cases hτρ : τ = ρ
    · subst τ
      by_cases hυρ : υ = ρ
      · subst υ
        exact (hne rfl).elim
      · have hυS : υ ∈ S := (Finset.mem_insert.mp hυ).resolve_left hυρ
        have hnc := hnoConflict υ hυS
        simp only [IsBoundaryPairConflict, not_or] at hnc
        exact le_of_not_gt hnc.1
    · have hτS : τ ∈ S := (Finset.mem_insert.mp hτ).resolve_left hτρ
      by_cases hυρ : υ = ρ
      · subst υ
        have hnc := hnoConflict τ hτS
        simp only [IsBoundaryPairConflict, not_or] at hnc
        exact le_of_not_gt hnc.2
      · have hυS : υ ∈ S := (Finset.mem_insert.mp hυ).resolve_left hυρ
        exact hSsep τ hτS υ hυS hne
  have hTP : T ∈ P := by
    simp [P, boundarySeparatedSubfamilies, hTsub, hTsep]
  have hcard := hSmax T hTP
  have hcardInsert : T.card = S.card + 1 := by
    simp [T, hρnotS]
  omega

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
