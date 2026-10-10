/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Carrier
public import FroehlichSpencer.BKT.VillainDisorder.FejerCos
import Mathlib.Tactic

/-!
# Interfaces for the rooted Dirichlet marked estimate

The finite-square statements and global inputs for the finite disorder estimate.

The Fejér observable is normalized as
`cos (ξ * pairing φ f)`: `tendsto_gffFejerCosRatio_igff` then sends it to
`cos (2π ξ * pairing m f)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

/-- The source `δ_center - δ_axial` on the bounded sites, zero at the exterior root. -/
def dirichletDipoleSource (R n : ℕ) (hn : n ≤ R) : Option (Site R) → ℝ :=
  fun j => if j = some (center R) then 1
    else if j = some (axialSite R n hn) then -1 else 0

/-- Fejér GFF inverse temperature corresponding to the Villain height parameter `β`. -/
def dirichletGffParameter (β : ℝ) : ℝ := β⁻¹ / (2 * Real.pi) ^ 2

theorem dirichletGffParameter_pos {β : ℝ} (hβ : 0 < β) :
    0 < dirichletGffParameter β := by
  unfold dirichletGffParameter
  exact div_pos (inv_pos.mpr hβ) (sq_pos_of_ne_zero (by positivity))

theorem dirichletGffParameter_scale (β : ℝ) :
    (2 * Real.pi) ^ 2 * dirichletGffParameter β = β⁻¹ := by
  unfold dirichletGffParameter
  field_simp

/-- The real pairing of the source dipole is the endpoint difference. The positive displacement
keeps the two sites distinct. -/
theorem pairing_dirichletDipoleSource_eq {R n : ℕ} (hn : n ≤ R)
    (hnpos : 1 ≤ n) (φ : Option (Site R) → ℝ) :
    Multigraph.pairing φ (dirichletDipoleSource R n hn) =
      φ (some (center R)) - φ (some (axialSite R n hn)) := by
  have hsite : center R ≠ axialSite R n hn := by
    intro h
    have hv := congrArg (fun p : Site R => p.1.val) h
    simp [center, axialSite] at hv
    omega
  classical
  change (∑ j : Option (Site R), φ j * dirichletDipoleSource R n hn j) = _
  have hterm (j : Option (Site R)) :
      φ j * dirichletDipoleSource R n hn j =
        (if j = some (center R) then φ j else 0) -
          (if j = some (axialSite R n hn) then φ j else 0) := by
    by_cases h₁ : j = some (center R)
    · subst j
      simp [dirichletDipoleSource, hsite]
    · by_cases h₂ : j = some (axialSite R n hn)
      · subst j
        simp [dirichletDipoleSource, h₁]
      · simp [dirichletDipoleSource, h₁, h₂]
  calc
    (∑ j : Option (Site R), φ j * dirichletDipoleSource R n hn j) =
        ∑ j : Option (Site R),
          ((if j = some (center R) then φ j else 0) -
            (if j = some (axialSite R n hn) then φ j else 0)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hterm j
    _ = φ (some (center R)) - φ (some (axialSite R n hn)) := by
          rw [Finset.sum_sub_distrib]
          simp

/-- The Fejér denominator for the centered rooted square. -/
def dirichletFejerDenominator (R : ℕ) (hR : 1 ≤ R) (β : ℝ)
    (hβ : 0 < β) (N : ℕ) : ℝ :=
  ∫ φ, gffFejerWeight N φ ∂
    gffMeasure (graph R) (graph_connected R hR)
      (dirichletGffParameter β) (dirichletGffParameter_pos hβ) none

/-- The marked Fejér ratio for the real dipole. Its frequency is chosen to match the
`tendsto_gffFejerCosRatio_igff` normalization described in this module's header. -/
def dirichletFejerMarkedRatio (R n : ℕ) (hR : 1 ≤ R) (hn : n ≤ R)
    (β ξ : ℝ) (hβ : 0 < β) (N : ℕ) : ℝ :=
  (∫ φ, Real.cos (ξ * Multigraph.pairing φ (dirichletDipoleSource R n hn)) *
      gffFejerWeight N φ ∂
    gffMeasure (graph R) (graph_connected R hR)
      (dirichletGffParameter β) (dirichletGffParameter_pos hβ) none) /
    dirichletFejerDenominator R hR β hβ N

/-- A cutoff-uniform estimate in one buffered square, with the denominator positivity explicit. -/
def RootedDirichletFejerBoundAt (R n : ℕ) (hR : 1 ≤ R) (hn : n ≤ R)
    (β ξ η c : ℝ) (hβ : 0 < β) : Prop :=
  ∀ N : ℕ, 0 < N →
    0 < dirichletFejerDenominator R hR β hβ N ∧
      0 ≤ dirichletFejerMarkedRatio R n hR hn β ξ hβ N ∧
      dirichletFejerMarkedRatio R n hR hn β ξ hβ N ≤
        2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))

/-- The rooted square IGFF form of the same marked bound. -/
def RootedDirichletIGFFBoundAt (R n : ℕ) (hR : 1 ≤ R) (hn : n ≤ R)
    (β ξ η c : ℝ) (hβ : 0 < β) : Prop :=
  0 ≤ igffExpectation (graph R) (graph_connected R hR)
      β⁻¹ (inv_pos.mpr hβ) none (fun h => dipoleCosine R n hn ξ h) ∧
    igffExpectation (graph R) (graph_connected R hR)
      β⁻¹ (inv_pos.mpr hβ) none (fun h => dipoleCosine R n hn ξ h) ≤
      2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))

/-- The (1.35) zero-exterior finite-law form of the marked bound. -/
def RootedDirichletFiniteLawBoundAt (R n : ℕ) (_hR : 1 ≤ R)
    (hn : n ≤ R) (β ξ η c : ℝ) : Prop :=
  0 ≤ cosineExpectation R n hn β ξ ∧
    cosineExpectation R n hn β ξ ≤
      2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))

/-- The quantitative marked Fejér input: every positive cutoff has the same estimate on all sufficiently
large centered squares. -/
def RootedDirichletFejerGlobalInput : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      ∃ β₀ : ℝ, ∃ hβ₀ : 0 < β₀,
        ∀ β : ℝ, ∀ hβlarge : β₀ < β,
          ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
            ∀ n : ℕ, ∀ hnpos : 1 ≤ n,
              ∃ R₀ : ℕ, ∃ hnR₀ : n ≤ R₀,
                ∀ R : ℕ, ∀ hbuffer : R₀ ≤ R, ∀ hn : n ≤ R,
                  let hβ : 0 < β := lt_trans hβ₀ hβlarge
                  let hR : 1 ≤ R := Nat.le_trans hnpos (Nat.le_trans hnR₀ hbuffer)
                  RootedDirichletFejerBoundAt R n hR hn β ξ η c hβ

/-- The corresponding global bound for the rooted integer GFF expectations. -/
def RootedDirichletIGFFGlobalBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      ∃ β₀ : ℝ, ∃ hβ₀ : 0 < β₀,
        ∀ β : ℝ, ∀ hβlarge : β₀ < β,
          ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
            ∀ n : ℕ, ∀ hnpos : 1 ≤ n,
              ∃ R₀ : ℕ, ∃ hnR₀ : n ≤ R₀,
                ∀ R : ℕ, ∀ hbuffer : R₀ ≤ R, ∀ hn : n ≤ R,
                  let hβ : 0 < β := lt_trans hβ₀ hβlarge
                  let hR : 1 ≤ R := Nat.le_trans hnpos (Nat.le_trans hnR₀ hbuffer)
                  RootedDirichletIGFFBoundAt R n hR hn β ξ η c hβ

/-- The finite-law marked conclusion inherited from the IGFF global input. -/
def RootedDirichletMarkedBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      ∃ β₀ : ℝ, 0 < β₀ ∧
        ∀ β : ℝ, β₀ < β →
          ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
            ∀ n : ℕ, ∀ hnpos : 1 ≤ n,
              ∃ R₀ : ℕ, ∃ hnR₀ : n ≤ R₀,
                ∀ R : ℕ, ∀ hbuffer : R₀ ≤ R, ∀ hn : n ≤ R,
                  let hR : 1 ≤ R := Nat.le_trans hnpos (Nat.le_trans hnR₀ hbuffer)
                  RootedDirichletFiniteLawBoundAt R n hR hn β ξ η c

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet
