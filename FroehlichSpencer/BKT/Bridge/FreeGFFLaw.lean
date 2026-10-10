/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SquareCarriers
public import FroehlichSpencer.BKT.Surface.GFFLaw
public import FroehlichSpencer.BKT.Surface.VillainWellDefined

/-!
# Laws of the free GFF and the pinned Villain angle

The GFF law depends on the graph only through its edge energy, hence the free square
and its internal positive-step model have the same law.

The Villain angle at the wired vertex is
pinned to `0`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open MeasureTheory

/-- The GFF law depends on the graph only through its edge energy. -/
theorem gffLaw_congr_energy {V : Type*} {E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (G : Multigraph V E) (H : Multigraph V F) (hG : G.toSimpleGraph.Connected)
    (hH : H.toSimpleGraph.Connected)
    (h : ∀ φ : V → ℝ, ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2 = ∑ e, (φ (H.src e) - φ (H.tgt e)) ^ 2)
    (β : ℝ) (hβ : 0 < β) (v : V) :
    gffLaw G hG β hβ v = gffLaw H hH β hβ v := by
  simp only [gffLaw, h]

/--
The free square and its internal positive-step model have the same GFF law.
-/
theorem gffLaw_squareFree_eq_squareFreeGraph {L : ℕ} (hL : 1 < L)
    (hF : (Lattice2D.squareFreeGraph L).Connected) (β : ℝ) (hβ : 0 < β) (v : Fin L × Fin L) :
    gffLaw (squareFree L) (squareFree_connected L hL) β hβ v =
      gffLaw (Lattice2D.squareFreeGraph L) hF β hβ v := by
  apply gffLaw_congr_energy
  intro φ
  have h := (squareFreeSourceGraphIsomorphism L).energy_transport φ
  have hp : (squareFreeSourceGraphIsomorphism L).pushField φ = φ := rfl
  rw [hp] at h
  exact h.symm

/-- The Villain angle is pinned to `0` at the wired vertex, so `E^Vil[cos θ_z] = 1`. -/
theorem integral_cos_none_villainLaw (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∫ θ, Real.cos (θ none) ∂(villainLaw L β hβ) = 1 := by
  have hnull : (Measure.pi fun j : Option (Fin L × Fin L) =>
        if j = none then Measure.dirac (0 : ℝ)
        else volume.restrict (Set.Ico (-Real.pi) Real.pi))
      {θ | θ none ≠ 0} = 0 := by
    have : {θ : Option (Fin L × Fin L) → ℝ | θ none ≠ 0} =
        Set.pi Set.univ (fun j => if j = none then ({0}ᶜ : Set ℝ) else Set.univ) := by
      ext θ
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h j
        by_cases hj : j = none
        · subst hj; simpa using h
        · simp [hj]
      · intro h
        simpa using h none
    have hsf : ∀ i : Option (Fin L × Fin L), SigmaFinite
        (if i = none then Measure.dirac (0 : ℝ)
          else volume.restrict (Set.Ico (-Real.pi) Real.pi)) := by
      intro i
      split_ifs <;> infer_instance
    rw [this, Measure.pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ none) (by simp)
  have hae : ∀ᵐ θ ∂(villainLaw L β hβ), θ none = 0 := by
    have hac : villainLaw L β hβ ≪ (Measure.pi fun j : Option (Fin L × Fin L) =>
        if j = none then Measure.dirac (0 : ℝ)
        else volume.restrict (Set.Ico (-Real.pi) Real.pi)) := by
      unfold villainLaw
      exact Measure.AbsolutelyContinuous.smul_left
        (withDensity_absolutelyContinuous _ _) _
    have := hac.ae_le (compl_mem_ae_iff.mpr hnull)
    filter_upwards [this] with θ hθ
    simpa using hθ
  have := isProbabilityMeasure_villainLaw L β hβ
  rw [integral_congr_ae (g := fun _ => (1 : ℝ))
    (by filter_upwards [hae] with θ hθ; simp [hθ])]
  simp

end FroehlichSpencer.BKT

end
