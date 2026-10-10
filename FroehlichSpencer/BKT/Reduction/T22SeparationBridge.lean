/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Reduction.T16AssemblyStatements
public import FroehlichSpencer.BKT.SpinWaves.Components
import FroehlichSpencer.BKT.Charges.PatchIsolation

/-!
# T2.2(b) of P2.4's hypotheses in the spin-wave distance API

`p24Statement` (`Reduction/T16AssemblyStatements.lean`) assumes KP Theorem 2.2(b) as
`IsScaleSeparated boundary L N`, in the charge API (`densityDistance`, `chargeDiameter`).

The
spin-wave construction uses `SpinWaves.densitySupportDistance` and `Multigraph.densityDiameter`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

section

variable (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
  (Λ : Multigraph (Fin L × Fin L) E)

/-- The charge-API distance between densities is the spin-wave support distance. -/
theorem densityDistance_eq_densitySupportDistance
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (ϱ σ : ChargeDensity L) :
    densityDistance boundary L ϱ σ = SpinWaves.densitySupportDistance Λ ϱ σ := by
  classical
  have hmem : ∀ {τ : ChargeDensity L} {x}, τ x ≠ 0 → x ∈ chargeSupport τ :=
    fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  by_cases hne : (∃ x, ϱ x ≠ 0) ∧ ∃ y, σ y ≠ 0
  · obtain ⟨x, y, hx, hy, heq⟩ :=
      SpinWaves.densitySupportDistance_attained Λ ϱ σ hne.1 hne.2
    have hprod : ((chargeSupport ϱ).product (chargeSupport σ)).Nonempty :=
      ⟨(x, y), Finset.mem_product.mpr ⟨hmem hx, hmem hy⟩⟩
    obtain ⟨a, b, ha, hb, heq'⟩ : ∃ a b, ϱ a ≠ 0 ∧ σ b ≠ 0 ∧
        densityDistance boundary L ϱ σ = latticeDistance boundary L a b := by
      have hmin := Finset.min'_mem (((chargeSupport ϱ).product (chargeSupport σ)).image
        fun p : (Fin L × Fin L) × (Fin L × Fin L) => latticeDistance boundary L p.1 p.2)
        (Finset.image_nonempty.mpr hprod)
      obtain ⟨⟨a, b⟩, hab, hval⟩ := Finset.mem_image.mp hmin
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      refine ⟨a, b, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, ?_⟩
      rw [densityDistance, squareDistance, dite_eq_left hprod, ← hval]
    apply le_antisymm
    · rw [heq, ← hdist]
      exact squareDistance_le_latticeDistance_of_mem boundary L _ _ x y (hmem hx) (hmem hy)
    · rw [heq', hdist]
      exact SpinWaves.densitySupportDistance_le Λ ϱ σ ha hb
  · have hempty : ∀ p : (Fin L × Fin L) × (Fin L × Fin L), ϱ p.1 ≠ 0 → σ p.2 ≠ 0 → False :=
      fun p h₁ h₂ => hne ⟨⟨p.1, h₁⟩, ⟨p.2, h₂⟩⟩
    rw [SpinWaves.densitySupportDistance_eq_support_minimum]
    rw [densityDistance, squareDistance, dite_eq_right, dite_eq_right]
    · rintro ⟨d, hd⟩
      obtain ⟨p, hp, -⟩ := Finset.mem_image.mp hd
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
      exact hempty p (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2
    · rintro ⟨p, hp⟩
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
      exact hempty p (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2

/-- T2.2(b) for distinct densities, in the spin-wave API with `M = 2^16`, `α = 7/4`. -/
theorem IsScaleSeparated.le_densitySupportDistance
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    {N : Finset (ChargeDensity L)} (hN : IsScaleSeparated boundary L N)
    {ϱ σ : ChargeDensity L} (hϱ : ϱ ∈ N) (hσ : σ ∈ N) (hne : ϱ ≠ σ) :
    (2 ^ 16 : ℝ) * ((min (Λ.densityDiameter ϱ) (Λ.densityDiameter σ) : ℕ) : ℝ) ^ (7 / 4 : ℝ) ≤
      SpinWaves.densitySupportDistance Λ ϱ σ := by
  have h := hN.1 ϱ hϱ σ hσ hne
  rw [chargeDiameter_eq_densityDiameter boundary Λ hdist,
    chargeDiameter_eq_densityDiameter boundary Λ hdist,
    densityDistance_eq_densitySupportDistance boundary Λ hdist] at h
  have hM : (chargeCoverScale : ℝ) = 2 ^ 16 := by norm_num [chargeCoverScale]
  rwa [hM, show chargeCoverExponent = (7 / 4 : ℝ) from rfl] at h


theorem IsScaleSeparated.half_le_densitySupportDistance
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    {N : Finset (ChargeDensity L)} (hN : IsScaleSeparated boundary L N)
    {ϱ ϱstar : ChargeDensity L} (hϱ : ϱ ∈ N) (hstar : ϱstar ∈ N) (hne : ϱ ≠ ϱstar)
    (hscale : Λ.densityDiameter ϱ ≤ 2 * Λ.densityDiameter ϱstar) :
    (2 ^ 16 : ℝ) * ((Λ.densityDiameter ϱ : ℝ) / 2) ^ (7 / 4 : ℝ) ≤
      SpinWaves.densitySupportDistance Λ ϱ ϱstar := by
  refine le_trans ?_ (hN.le_densitySupportDistance boundary Λ hdist hϱ hstar hne)
  have hmin : (Λ.densityDiameter ϱ : ℝ) / 2 ≤
      ((min (Λ.densityDiameter ϱ) (Λ.densityDiameter ϱstar) : ℕ) : ℝ) := by
    rw [Nat.cast_min, le_min_iff]
    have h0 : (0 : ℝ) ≤ Λ.densityDiameter ϱ := Nat.cast_nonneg _
    have h2 : (Λ.densityDiameter ϱ : ℝ) ≤ 2 * Λ.densityDiameter ϱstar := by exact_mod_cast hscale
    constructor <;> linarith
  gcongr

end

end FroehlichSpencer.BKT

end
