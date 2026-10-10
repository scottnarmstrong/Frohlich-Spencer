/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.VillainMeasure
public import FroehlichSpencer.BKT.Surface.VillainLaw
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The wired-root Villain observable

The wired angle is pinned to zero under the Villain law, so its cosine expectation is one
(KP (1.4), p. 4).
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT

private instance villainRootCoordinate_isFiniteMeasure (L : ℕ)
    (j : Option (Fin L × Fin L)) :
    IsFiniteMeasure (if j = none then Measure.dirac (0 : ℝ)
      else volume.restrict (Set.Ico (-Real.pi) Real.pi)) := by
  classical
  split_ifs with hj
  · subst j
    infer_instance
  · refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top

/-- The normalized Villain law gives full measure to configurations whose wired angle is zero. -/
theorem ae_villain_root_angle_eq_zero (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ θ ∂villainLaw L β hβ, θ none = 0 := by
  classical
  have hbase : ∀ᵐ θ ∂villainBaseMeasure L, θ none = 0 := by
    rw [ae_iff]
    rw [villainBaseMeasure]
    change Measure.pi (fun j : Option (Fin L × Fin L) =>
      if j = none then Measure.dirac (0 : ℝ)
      else volume.restrict (Set.Ico (-Real.pi) Real.pi))
        (Function.eval none ⁻¹' ({0}ᶜ : Set ℝ)) = 0
    rw [← Measure.map_apply (measurable_pi_apply none)
      (measurableSet_singleton (0 : ℝ)).compl]
    rw [Measure.pi_map_eval]
    simp
  have hdensity : ∀ᵐ θ ∂villainDensityMeasure L β, θ none = 0 :=
    (withDensity_absolutelyContinuous _ _).ae_le hbase
  rw [ae_iff] at hdensity ⊢
  rw [villainLaw_eq_normalizedDensityMeasure L β hβ, Measure.smul_apply, smul_eq_mul]
  simp [hdensity]

/-- The cosine expectation at the wired vertex is exactly one. -/
theorem villainLaw_root_cos_integral (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    (∫ θ, Real.cos (θ none) ∂villainLaw L β hβ) = 1 := by
  have hu : (villainLaw L β hβ) Set.univ = 1 := by
    rw [villainLaw_eq_normalizedDensityMeasure L β hβ, Measure.smul_apply, smul_eq_mul]
    have hpart := villainDensityMeasure_univ_pos_lt_top L β hβ
    exact ENNReal.inv_mul_cancel (ne_of_gt hpart.1) (ne_of_lt hpart.2)
  have hcos : ∀ᵐ θ ∂villainLaw L β hβ, Real.cos (θ none) = 1 := by
    filter_upwards [ae_villain_root_angle_eq_zero L β hβ] with θ hθ
    simp [hθ]
  rw [integral_congr_ae hcos, integral_const, measureReal_def, hu]
  norm_num

/-- The wired root has graph distance zero from itself. -/
@[simp]
theorem squareZero_dist_wiredRoot_self (L : ℕ) :
    (squareZero L).toSimpleGraph.dist none none = 0 := by
  simp

/-- The wired-root instance of KP's power-law lower bound is automatic for every positive
exponent parameter. -/
theorem villainLaw_powerLaw_at_wiredRoot (L : ℕ) (β C : ℝ) (hβ : 0 < β) :
    ((squareZero L).toSimpleGraph.dist none none + 1 : ℝ) ^ (-C / β) ≤
      ∫ θ, Real.cos (θ none) ∂villainLaw L β hβ := by
  rw [squareZero_dist_wiredRoot_self, villainLaw_root_cos_integral]
  norm_num

end FroehlichSpencer.BKT

end
