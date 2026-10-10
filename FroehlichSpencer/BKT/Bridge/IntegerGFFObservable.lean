/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.IntegerGFFMeasure
public import FroehlichSpencer.BKT.Surface.IntegerGFFLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Nonnegative observables under the integer GFF law

This module identifies the law's `∫⁻` of an `ENNReal.ofReal`
observable with the normalized pinned lattice sum, extending the partition
function characterization on KP p. 3.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open MeasureTheory
open Multigraph

universe u v

/--
The integer GFF law integrates any nonnegative observable as the
normalized pinned lattice sum, provided that weighted sum is summable.
-/
theorem integerGFFLaw_lintegral_ofReal_eq_igffExpectation
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (F : (V → ℤ) → ℝ)
    (hF : ∀ m, 0 ≤ F m)
    (hFs : Summable (fun m : pinnedIntegerField V root =>
      F m.1 * igffWeight G β m)) :
    (∫⁻ m, ENNReal.ofReal (F m) ∂integerGFFLaw G hG β hβ root) =
      ENNReal.ofReal (igffExpectation G hG β hβ root (fun m => F m.1)) := by
  classical
  change G.Connected at hG
  let base : Measure (V → ℤ) :=
    Measure.pi fun j => if j = root then Measure.dirac (0 : ℤ) else Measure.count
  let density : (V → ℤ) → ENNReal := fun m =>
    ENNReal.ofReal (Real.exp (-(β / 2) *
      ∑ e, ((m (G.src e) : ℝ) - (m (G.tgt e) : ℝ)) ^ 2))
  let ν : Measure (V → ℤ) := base.withDensity density
  have htotal : ν Set.univ = ENNReal.ofReal (igffPartitionFunction G β root) := by
    simpa [ν, base, density] using integerGFFDensityMeasure_univ G hG β hβ root
  have hFmeas : Measurable (fun m : V → ℤ => ENNReal.ofReal (F m)) :=
    measurable_of_countable _
  have hdensity : Measurable density := measurable_of_countable _
  have hbaseAtom (m : V → ℤ) : base {m} = if m root = 0 then 1 else 0 := by
    exact integerGFFBase_singleton root m
  have hsum : (∑' m : V → ℤ,
      density m * ENNReal.ofReal (F m) * base {m}) =
      ENNReal.ofReal (∑' m : pinnedIntegerField V root,
        F m.1 * igffWeight G β m) := by
    have hsub :
        (∑' m : V → ℤ, if hm : m root = 0 then
          ENNReal.ofReal (F m) *
            ENNReal.ofReal (igffWeight G β ⟨m, hm⟩) else 0) =
        ∑' m : pinnedIntegerField V root,
          ENNReal.ofReal (F m.1) * ENNReal.ofReal (igffWeight G β m) := by
      let e : {m : V → ℤ // m ∈ ({m | m root = 0} : Set (V → ℤ))} ≃
          pinnedIntegerField V root := {
        toFun := fun m => ⟨m.1, by
          simpa only [Set.mem_ofPred_eq] using m.2⟩
        invFun := fun m => ⟨m.1, by
          simpa only [Set.mem_ofPred_eq] using m.2⟩
        left_inv := by intro m; apply Subtype.ext; rfl
        right_inv := by intro m; apply Subtype.ext; rfl }
      let g (m : V → ℤ) := if hm : m root = 0 then
        ENNReal.ofReal (F m) * ENNReal.ofReal (igffWeight G β ⟨m, hm⟩)
        else 0
      let f (m : pinnedIntegerField V root) :=
        ENNReal.ofReal (F m.1) * ENNReal.ofReal (igffWeight G β m)
      calc
        (∑' m : V → ℤ, if hm : m root = 0 then
            ENNReal.ofReal (F m) *
              ENNReal.ofReal (igffWeight G β ⟨m, hm⟩) else 0) =
            ∑' a : {m : V → ℤ // m ∈ ({m | m root = 0} : Set (V → ℤ))}, g a.1 := by
          calc
            (∑' m : V → ℤ, if hm : m root = 0 then
                ENNReal.ofReal (F m) *
                  ENNReal.ofReal (igffWeight G β ⟨m, hm⟩) else 0) =
                ∑' m : V → ℤ, if hm : m root = 0 then g m else 0 := by
              apply tsum_congr
              intro m
              by_cases hm : m root = 0 <;> simp [g, hm]
            _ = ∑' m : V → ℤ,
                if m ∈ ({m | m root = 0} : Set (V → ℤ)) then g m else 0 := by
              apply tsum_congr
              intro m
              by_cases hm : m root = 0 <;> simp [Set.mem_ofPred_eq, hm]
            _ = ∑' a : {m : V → ℤ //
                m ∈ ({m | m root = 0} : Set (V → ℤ))}, g a.1 :=
              by
                simpa only [Set.indicator_apply] using
                  (tsum_subtype ({m | m root = 0} : Set (V → ℤ)) g).symm
        _ = ∑' m : pinnedIntegerField V root, f m := by
          calc
            (∑' a : {m : V → ℤ // m ∈ ({m | m root = 0} : Set (V → ℤ))},
                g a.1) =
              ∑' a : {m : V → ℤ // m ∈ ({m | m root = 0} : Set (V → ℤ))},
                f (e a) := by
              apply tsum_congr
              intro a
              have ha : a.1 root = 0 := by
                simpa only [Set.mem_ofPred_eq] using a.2
              have he : e a = ⟨a.1, ha⟩ := by
                apply Subtype.ext
                rfl
              rw [he]
              simp [f, g, ha]
            _ = ∑' m : pinnedIntegerField V root, f m := Equiv.tsum_eq e f
    calc
      (∑' m : V → ℤ, density m * ENNReal.ofReal (F m) * base {m}) =
          ∑' m : V → ℤ, if hm : m root = 0 then
            ENNReal.ofReal (F m) *
              ENNReal.ofReal (igffWeight G β ⟨m, hm⟩) else 0 := by
        apply tsum_congr
        intro m
        rw [hbaseAtom m]
        by_cases hm : m root = 0
        · have hweight : density m = ENNReal.ofReal
              (igffWeight G β (⟨m, hm⟩ : pinnedIntegerField V root)) := by
            change ENNReal.ofReal (Real.exp (-(β / 2) *
              ∑ e, ((m (G.src e) : ℝ) - (m (G.tgt e) : ℝ)) ^ 2)) = _
            rw [← igffWeight_eq_kp G β (⟨m, hm⟩ : pinnedIntegerField V root)]
          simp [hm, hweight, mul_comm]
        · simp [hm]
      _ = ∑' m : pinnedIntegerField V root,
          ENNReal.ofReal (F m.1) * ENNReal.ofReal (igffWeight G β m) := hsub
      _ = ∑' m : pinnedIntegerField V root,
          ENNReal.ofReal (F m.1 * igffWeight G β m) := by
        apply tsum_congr
        intro m
        exact (ENNReal.ofReal_mul (hF m.1)).symm
      _ = ENNReal.ofReal (∑' m : pinnedIntegerField V root,
          F m.1 * igffWeight G β m) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (f := fun m : pinnedIntegerField V root => F m.1 * igffWeight G β m)
          (fun m => mul_nonneg (hF m.1) (Real.exp_pos _).le) hFs]
  change (∫⁻ m, ENNReal.ofReal (F m) ∂((ν Set.univ)⁻¹ • ν)) = _
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul base hdensity hFmeas,
    lintegral_countable']
  simp only [Pi.mul_apply]
  rw [htotal, hsum]
  simp only [smul_eq_mul, igffExpectation]
  rw [ENNReal.ofReal_div_of_pos (igffPartitionFunction_pos G hG β hβ root)]
  simp [div_eq_mul_inv, mul_comm]

end FroehlichSpencer.BKT

end
