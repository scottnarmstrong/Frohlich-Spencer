/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter
public import FroehlichSpencer.BKT.Generic.PinnedCharges.FiniteMixture

/-! # The finite cosine mixture in root-relative pinned coordinates

The free-box finite cosine mixture can be read on unrestricted wired-face fields by taking each
bounded-face angle relative to the exterior angle. Extending each frequency by its compensating
exterior charge makes every character neutral under the root phase. This is the algebraic
boundary adapter; it does not assert the Appendix D `d_Λ` separation or the boundary entropy
estimate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Rotator

/-- The existing finite positive mixture, expressed in root-relative coordinates and with each
frequency written as its neutralized charge on the augmented wired carrier. -/
theorem exists_rooted_neutral_cosine_mixture {L : ℕ} (hL : 1 < L)
    (z : Fin L × Fin L → ℝ) :
    ∃ (n : ℕ) (N : Fin n → Finset (ChargeDensity L))
      (c : Fin n → ℝ) (K : Fin n → ChargeDensity L → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧
      (∀ i, 0 < c i) ∧
      (∑ i, c i = 1) ∧
      (∀ θ : RotatorDualFace L → ℝ,
        ∏ x, (1 + z x * Real.cos (relativeToWiredRoot θ x)) =
          ∑ i, c i * ∏ q ∈ N i,
            (1 + K i q * Real.cos
              (∑ x : RotatorDualFace L, θ x * (neutralizeAtWiredRoot q x : ℝ)))) ∧
      (∀ i, AtMostOneNonNeutral (N i) ∧
        IsScaleSeparated .free L (N i) ∧
        NeutralSplitsAreCharged .free L (N i) ∧
        ∀ q ∈ N i, ∑ x, q x = 0 →
          |K i q| ≤ Real.exp (200 * chargeCoverCost .free L q) *
            ∏ x ∈ chargeSupport q, cosineMixtureLeaf z x (q x).natAbs) ∧
      (∀ q : ChargeDensity L,
        ∑ x : RotatorDualFace L, neutralizeAtWiredRoot q x = 0) := by
  obtain ⟨n, N, c, K, hN, hc, hcsum, hexp, hprops⟩ :=
    exists_finite_cosine_charge_mixture hL z
  refine ⟨n, N, c, K, hN, hc, hcsum, ?_, hprops, ?_⟩
  · intro θ
    calc
      ∏ x, (1 + z x * Real.cos (relativeToWiredRoot θ x)) =
          ∑ i, c i * ∏ q ∈ N i,
            (1 + K i q * Real.cos (∑ x, relativeToWiredRoot θ x * (q x : ℝ))) :=
        hexp (relativeToWiredRoot θ)
      _ = ∑ i, c i * ∏ q ∈ N i,
            (1 + K i q * Real.cos
              (∑ x : RotatorDualFace L, θ x * (neutralizeAtWiredRoot q x : ℝ))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine congrArg (fun r : ℝ => c i * r) ?_
        refine Finset.prod_congr rfl fun q _ => ?_
        exact congrArg (fun t : ℝ => 1 + K i q * Real.cos t)
          (pairing_neutralizeAtWiredRoot q θ).symm
  · intro q
    exact sum_neutralizeAtWiredRoot q

/-- The finite mixture as a genuine frequency family on the augmented `squareZero` vertex set.
Every frequency is neutral, so its character survives the rooted-law zero-mode. The geometric
claims here remain those of the bounded free-box mixture; this theorem does not identify them with
Appendix D's boundary separation. -/
theorem exists_squareZero_neutral_frequency_mixture {L : ℕ} (hL : 1 < L)
    (z : Fin L × Fin L → ℝ) :
    ∃ (n : ℕ) (N : Fin n → Finset (ChargeDensity L))
      (Nroot : Fin n → Finset (RotatorDualFace L → ℤ))
      (c : Fin n → ℝ) (K : Fin n → ChargeDensity L → ℝ)
      (Kroot : Fin n → (RotatorDualFace L → ℤ) → ℝ),
      (∀ i, Nroot i = (N i).image neutralizeAtWiredRoot) ∧
      (∀ i, 0 < c i) ∧
      (∑ i, c i = 1) ∧
      (∀ i, ∀ q ∈ Nroot i, ∑ x : RotatorDualFace L, q x = 0) ∧
      (∀ θ : RotatorDualFace L → ℝ,
        ∏ x, (1 + z x * Real.cos (relativeToWiredRoot θ x)) =
          ∑ i, c i * ∏ q ∈ Nroot i,
            (1 + Kroot i q * Real.cos (∑ x, θ x * (q x : ℝ)))) ∧
      (∀ i, AtMostOneNonNeutral (N i) ∧
        IsScaleSeparated .free L (N i) ∧
        NeutralSplitsAreCharged .free L (N i) ∧
        ∀ q ∈ N i, ∑ x, q x = 0 →
          |K i q| ≤ Real.exp (200 * chargeCoverCost .free L q) *
            ∏ x ∈ chargeSupport q, cosineMixtureLeaf z x (q x).natAbs) := by
  classical
  obtain ⟨n, N, c, K, hN, hc, hcsum, hexp, hprops⟩ :=
    exists_finite_cosine_charge_mixture hL z
  let Nroot : Fin n → Finset (RotatorDualFace L → ℤ) :=
    fun i => (N i).image neutralizeAtWiredRoot
  let Kroot : Fin n → (RotatorDualFace L → ℤ) → ℝ :=
    fun i q => K i (fun x => q (some x))
  have hneutral : ∀ i, ∀ q ∈ Nroot i, ∑ x : RotatorDualFace L, q x = 0 := by
    intro i q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
    exact sum_neutralizeAtWiredRoot q₀
  have hinj : Function.Injective (neutralizeAtWiredRoot (L := L)) := by
    intro q₁ q₂ h
    funext x
    have hx := congrFun h (some x)
    simpa [neutralizeAtWiredRoot] using hx
  have hprod : ∀ i, ∀ θ : RotatorDualFace L → ℝ,
      ∏ q ∈ Nroot i, (1 + Kroot i q * Real.cos (∑ x, θ x * (q x : ℝ))) =
        ∏ q ∈ N i, (1 + K i q * Real.cos
          (∑ x : RotatorDualFace L, θ x * (neutralizeAtWiredRoot q x : ℝ))) := by
    intro i θ
    simp only [Nroot]
    rw [Finset.prod_image]
    · refine Finset.prod_congr rfl fun q hq => ?_
      simp only [Kroot, neutralizeAtWiredRoot_some]
    · intro q hq q' hq' heq
      exact hinj heq
  refine ⟨n, N, Nroot, c, K, Kroot, ?_, hc, hcsum, hneutral, ?_, hprops⟩
  · intro i
    rfl
  · intro θ
    calc
      ∏ x, (1 + z x * Real.cos (relativeToWiredRoot θ x)) =
          ∑ i, c i * ∏ q ∈ N i,
            (1 + K i q * Real.cos (∑ x, relativeToWiredRoot θ x * (q x : ℝ))) :=
        hexp (relativeToWiredRoot θ)
      _ = ∑ i, c i * ∏ q ∈ Nroot i,
            (1 + Kroot i q * Real.cos (∑ x, θ x * (q x : ℝ))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hprod i θ]
        refine congrArg (fun r : ℝ => c i * r) ?_
        refine Finset.prod_congr rfl fun q _ => ?_
        exact congrArg (fun t : ℝ => 1 + K i q * Real.cos t)
          (pairing_neutralizeAtWiredRoot q θ).symm

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
