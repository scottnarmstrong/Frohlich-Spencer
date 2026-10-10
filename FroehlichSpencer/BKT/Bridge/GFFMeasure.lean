/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.Normalization
public import FroehlichSpencer.BKT.Surface.GFFLaw

/-!
# The GFF law is the internal normalized rooted Gaussian free field

The `gffLaw` (KP (1.3), p. 2) and the internal `gffMeasure` are built from the same density
with respect to Lebesgue measure on `V → ℝ`, and both are normalized by their total mass.

This
module identifies them, so that the internal normalization results apply to the law.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open MeasureTheory
open Multigraph

universe u v

variable {V : Type u} {E : Type v}

/--
The density of KP (1.3), `exp (-(β / 2) ∑_e (φ (src e) - φ (tgt e))²) · 𝟙_{[-π, π)} (φ v)`,
is the internal rooted density `gffDensity`.
-/
theorem gffLaw_density_eq_gffDensity [Fintype E] [DecidableEq V] (G : Multigraph V E) (β : ℝ)
    (v : V) (φ : V → ℝ) :
    ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2) *
        (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v)) =
      ENNReal.ofReal (gffDensity G β v φ) := by
  by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi
  · rw [gffDensity_of_root_mem G β v φ h, Set.indicator_of_mem h]
    simp [Multigraph.energy, Multigraph.grad]
  · rw [gffDensity_of_root_not_mem G β v φ h, Set.indicator_of_notMem h]
    simp

/--
The unnormalized measure inside the `gffLaw` is the internal `gffDensityMeasure`.
-/
theorem gffLaw_densityMeasure_eq [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E)
    (β : ℝ) (v : V) :
    (Measure.pi fun _ : V => (volume : Measure ℝ)).withDensity
        (fun φ => ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2) *
          (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v))) =
      gffDensityMeasure G β v := by
  rw [gffDensityMeasure, ← volume_pi]
  congr 1
  funext φ
  exact gffLaw_density_eq_gffDensity G β v φ

/--
The GFF law of KP (1.3) is the internal normalized rooted Gaussian free field.
-/
theorem gffLaw_eq_gffMeasure [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) :
    gffLaw G hG β hβ v = gffMeasure G hG β hβ v := by
  dsimp only [gffLaw, gffMeasure]
  rw [gffLaw_densityMeasure_eq G β v, gffDensityMeasure_univ G hG β hβ v]

end FroehlichSpencer.BKT

end
