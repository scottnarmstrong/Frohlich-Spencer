/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.CompactShift
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
public import FroehlichSpencer.BKT.Generic.Moment.KPLayer
import Mathlib.Tactic

open FroehlichSpencer.BKT.SpinWaves
open FroehlichSpencer.BKT.SpinWaves.BoundaryShellPacking
open FroehlichSpencer.BKT.Reduction
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Lattice2D

/-!
# Free-square compact Fejér charge layer for the disorder shift

The KP mixture layer is instantiated with the compact clock Fejér multiplier. The compact assembly
then gives the exact shifted expansion on every free square, uniformly as an existential layer
construction for each site shift. The geometric Fejér mixture has leaf bound `exp (2q)`, so its
charge entropy input is explicit.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

/-- The Fejér multiplier and its finite-site mixture on a square. -/
def fejerClockMultiplier (n M : ℕ) (φ : ℝ) : ℝ :=
  fejerPolynomial M (φ - clockOffset n)

def fejerClockLeafMixture (n M : ℕ) (j : Fin n × Fin n) (q : ℕ) : ℝ :=
  mixtureLeaf (fun _ => M) (fun _ q => fejerShiftCoeff M (clockOffset n) q)
    (fun _ => geomMixture M) j q

theorem fejerClockLeafMixture_le {n M : ℕ} (hM : 0 < M)
    (j : Fin n × Fin n) (q : ℕ) :
    fejerClockLeafMixture n M j q ≤ Real.exp (2 * q) := by
  exact mixtureLeaf_fejer_le hM n j q

/-- The free-square KP charge layer expands the shifted Fejér multiplier for every real site
shift, through the compact clock charge-layer identity. -/
theorem exists_freeSquare_fejerChargeLayer {L n M : ℕ} (hL : 1 < L) (hn : 0 < n)
    (hM : 1 ≤ M) {β κ κ' W amp : ℝ} (hβ : 0 ≤ β)
    (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W) (hκ : 0 < κ)
    (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28) :
    ∃ (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
      (CL : ChargeLayer (squareFree L) (fun _ φ => fejerPolynomial M (φ - clockOffset n)) centerOf
        (fun ϱ => (chargeCoverCost .free L ϱ : ℝ))
        (fun ϱ => ∏ j ∈ chargeSupport ϱ,
          mixtureLeaf (fun _ => M) (fun _ q => fejerShiftCoeff M (clockOffset n) q)
            (fun _ => geomMixture M) j (ϱ j).natAbs)
        kpD₁ 200 (7 / 4) 4096 28),
      (∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i) ∧
        IsChargeEnsemble (CL.N i) ∧ IsScaleSeparated .free L (CL.N i)) ∧
      ∃ (z : Fin CL.n → (Fin L × Fin L → ℤ) → ℝ)
        (a : Fin CL.n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
        (∀ σ : Fin L × Fin L → ℝ,
          ∫ φ, ((∏ j, fejerClockMultiplier n M (φ j + σ j) : ℝ) : ℂ)
              ∂clockLaw β n (squareFree L) =
            ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i,
              ((1 : ℂ) + (z i ϱ : ℂ) *
                localFactor (clockEdgeWeight β n) (clockShiftCost β n)
                  (gradLinear (squareFree L) (a i ϱ))
                  (gradLinear (squareFree L) φ)
                  (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ)))
              ∂clockLaw β n (squareFree L)) ∧
        (∀ i, ∀ ϱ ∈ CL.R i,
          |z i ϱ| ≤ Real.exp (200 * (chargeCoverCost .free L ϱ : ℝ)) *
            (∏ j ∈ chargeSupport ϱ,
              mixtureLeaf (fun _ => M) (fun _ q => fejerShiftCoeff M (clockOffset n) q)
                (fun _ => geomMixture M) j (ϱ j).natAbs) *
            Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) -
              amp / (8 * kpD₁) * (chargeCoverCost .free L ϱ : ℝ))) := by
  have hMpos : 0 < M := hM
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j,
      ϱ ≠ 0 → (squareFree L).IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := (squareFree L).exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  obtain ⟨CL, hCL⟩ := exists_kpChargeLayer .free hL (Or.inl rfl) (squareFree L)
    (squareFree_connected L hL) (fun _ _ => rfl)
    (SpinWaves.squareFreeBipartiteDegreeFour L hL)
    (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).1 kpD₁_pos.le
    (p21Step_kpD₁ hL).1 centerOf hcenter
    (fun _ φ => fejerClockMultiplier n M φ) (fun _ => M)
    (fun _ q => fejerShiftCoeff M (clockOffset n) q) (fun _ => geomMixture M)
    (fun _ => hMpos)
    (by
      intro _ q hq
      unfold fejerShiftCoeff fejerFourierCoefficient
      rw [ite_eq_right (by intro h; omega), zero_mul])
    (by
      intro j φ
      exact fejerPolynomial_sub_clockOffset M n φ)
    (by
      intro j q
      unfold geomMixture
      exact div_pos (by positivity) (geomNorm_pos hMpos))
    (by
      intro j
      unfold geomMixture
      rw [← Finset.sum_div]
      exact div_self (geomNorm_pos hMpos).ne')
  have hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i) :=
    fun i => ⟨(hCL i).1, (hCL i).2.1⟩
  obtain ⟨z, a, hid, hz⟩ := clockLaw_renormalization_of_chargeLayer hn hβ CL hroot hc hκ
    (by norm_num) (by norm_num) kpD₁_pos hamp hampW hW1 hk₀ hexp hquad₁ hquad₂
  exact ⟨centerOf, CL, hCL, z, a, hid, fun i ϱ hϱ => (hz i ϱ hϱ).1⟩

/-- The Fejér mixture gives an explicit entropy estimate for every charge in the neutral
subensemble of the KP layer. -/
theorem fejerChargeLayer_entropy_bound {L n M : ℕ} (hM : 0 < M)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (CL : ChargeLayer (squareFree L) (fun _ φ => fejerPolynomial M (φ - clockOffset n)) centerOf
      (fun ϱ => (chargeCoverCost .free L ϱ : ℝ))
      (fun ϱ => ∏ j ∈ chargeSupport ϱ,
        mixtureLeaf (fun _ => M) (fun _ q => fejerShiftCoeff M (clockOffset n) q)
          (fun _ => geomMixture M) j (ϱ j).natAbs)
      kpD₁ 200 (7 / 4) 4096 28) :
    ∀ i, ∀ ϱ ∈ CL.R i,
      |CL.K i ϱ| ≤ Real.exp (200 * (chargeCoverCost .free L ϱ : ℝ)) *
        Real.exp (2 * ∑ j, |(ϱ j : ℝ)|) := by
  intro i ϱ hϱ
  have hbase := CL.entropy i ϱ hϱ
  have hleaf := prod_mixtureLeaf_le (fun _ => M)
    (fun _ q => fejerShiftCoeff M (clockOffset n) q) (fun _ => geomMixture M)
    (fun j q => div_pos (by positivity) (geomNorm_pos hM))
    (fun j q => mixtureLeaf_fejer_le hM n j q) ϱ
  have hZ := hbase.trans (mul_le_mul_of_nonneg_left hleaf (Real.exp_pos _).le)
  simpa only [fejerClockMultiplier, fejerClockLeafMixture, Real.exp_add] using hZ

/-- The explicit Fejér-layer activity bound has the KP scale-decay form consumed by T1.5.
The two strict losses are the mixture entropy `2∑|ϱ|` and the ensemble entropy `200 A(ϱ)`. -/
theorem fejerChargeLayer_decay_bound {L n M : ℕ} (hL : 1 < L) (hM : 0 < M)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (CL : ChargeLayer (squareFree L) (fun _ φ => fejerPolynomial M (φ - clockOffset n)) centerOf
      (fun ϱ => (chargeCoverCost .free L ϱ : ℝ))
      (fun ϱ => ∏ j ∈ chargeSupport ϱ,
        mixtureLeaf (fun _ => M) (fun _ q => fejerShiftCoeff M (clockOffset n) q)
          (fun _ => geomMixture M) j (ϱ j).natAbs)
      kpD₁ 200 (7 / 4) 4096 28)
    (hCL : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i) ∧
      IsChargeEnsemble (CL.N i) ∧ IsScaleSeparated .free L (CL.N i))
    (z : Fin CL.n → (Fin L × Fin L → ℤ) → ℝ) {amp b : ℝ}
    (hb₈ : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - 2)
    (hb₂ : b ≤ amp / (8 * kpD₁) - 200)
    (hz : ∀ i, ∀ ϱ ∈ CL.R i,
      |z i ϱ| ≤ Real.exp (200 * (chargeCoverCost .free L ϱ : ℝ)) *
        (∏ j ∈ chargeSupport ϱ,
          mixtureLeaf (fun _ => M) (fun _ q => fejerShiftCoeff M (clockOffset n) q)
            (fun _ => geomMixture M) j (ϱ j).natAbs) *
        Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) -
          amp / (8 * kpD₁) * (chargeCoverCost .free L ϱ : ℝ))) :
    ∀ i, ∀ ϱ ∈ CL.R i,
      |z i ϱ| ≤ Real.exp (-b * ((∑ j, |(ϱ j : ℝ)|) +
        Real.logb 2 ((squareFree L).densityDiameter ϱ + 1))) := by
  intro i ϱ hϱ
  have hne : ϱ ≠ 0 := by
    rw [(hCL i).1] at hϱ
    exact (hCL i).2.2.1.1 ϱ (mem_neutralPart.mp hϱ).1
  have hAlog : Real.logb 2 ((squareFree L).densityDiameter ϱ + 1) ≤
      chargeCoverCost .free L ϱ := by
    have h := (p21Step_kpD₁ hL).1
      (fun ρ k => sharedMinimumSquareCover .free L ρ (by omega) k) ϱ hne
    rw [chargeDiameter_eq_densityDiameter .free (squareFree L) (fun _ _ => rfl)] at h
    exact h.1
  have hA0 : 0 ≤ (chargeCoverCost .free L ϱ : ℝ) := Nat.cast_nonneg _
  have hX0 : 0 ≤ ∑ j, |(ϱ j : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hlog0 : 0 ≤ Real.logb 2 ((squareFree L).densityDiameter ϱ + 1) := by
    apply Real.logb_nonneg (by norm_num)
    have hd : 0 ≤ ((squareFree L).densityDiameter ϱ : ℝ) := Nat.cast_nonneg _
    linarith
  have hb0 : 0 ≤ b := le_trans (by positivity) hb₈
  have hcomb : b * ((∑ j, |(ϱ j : ℝ)|) +
      Real.logb 2 ((squareFree L).densityDiameter ϱ + 1)) ≤
      (amp / 8 - 2) * (∑ j, |(ϱ j : ℝ)|) +
        (amp / (8 * kpD₁) - 200) * (chargeCoverCost .free L ϱ : ℝ) := by
    calc
      _ = b * (∑ j, |(ϱ j : ℝ)|) +
          b * Real.logb 2 ((squareFree L).densityDiameter ϱ + 1) := by ring
      _ ≤ (amp / 8 - 2) * (∑ j, |(ϱ j : ℝ)|) +
          b * (chargeCoverCost .free L ϱ : ℝ) := by
            gcongr
      _ ≤ _ := by gcongr
  have hleaf := prod_mixtureLeaf_le (fun _ => M)
    (fun _ q => fejerShiftCoeff M (clockOffset n) q) (fun _ => geomMixture M)
    (fun _ q => div_pos (by positivity) (geomNorm_pos hM))
    (fun j q => mixtureLeaf_fejer_le hM n j q) ϱ
  have hz' := hz i ϱ hϱ
  have hupper : |z i ϱ| ≤ Real.exp (-((amp / 8 - 2) *
      (∑ j, |(ϱ j : ℝ)|) + (amp / (8 * kpD₁) - 200) *
        (chargeCoverCost .free L ϱ : ℝ))) := by
    calc
      |z i ϱ| ≤ Real.exp (200 * (chargeCoverCost .free L ϱ : ℝ)) *
          Real.exp (2 * ∑ j, |(ϱ j : ℝ)|) *
          Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) -
            amp / (8 * kpD₁) * (chargeCoverCost .free L ϱ : ℝ)) := by
              calc
                _ ≤ _ := hz'
                _ ≤ _ := by
                  gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact hupper.trans (Real.exp_le_exp.mpr (by linarith [hcomb]))

end FroehlichSpencer.BKT.Clock.Disorder

end
