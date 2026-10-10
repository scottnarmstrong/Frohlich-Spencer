/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.HarmonicField

/-!
# Periodic harmonic correction

The real Hodge decomposition of a torus cycle has a dual-gradient part and two constant harmonic
currents. This file separates those parts and gives the periodic height correction with the root
pinned to zero.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open Multigraph

namespace FroehlichSpencer.BKT.Rotator.Periodic

noncomputable section

variable {L : ℕ} [NeZero L]

/-- The constant horizontal and vertical harmonic currents with prescribed cut periods. -/
def torusRealUniformHarmonicCurrent (p q : ℝ) : TorusEdge L → ℝ := fun e =>
  if e.2 then q / (L : ℝ) else p / (L : ℝ)

private theorem sum_const_zmod_div (c : ℝ) :
    (∑ _ : ZMod L, c / (L : ℝ)) = c := by
  calc
    (∑ _ : ZMod L, c / (L : ℝ)) = ∑ i : Fin L, c / (L : ℝ) := by
      exact (Equiv.sum_comp (ZMod.finEquiv L).toEquiv
        (fun _ : ZMod L => c / (L : ℝ))).symm
    _ = c := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
      simp only [Finset.card_univ, Fintype.card_fin]
      field_simp [hL]

omit [NeZero L] in
theorem torusRealUniformHarmonicCurrent_divergence (p q : ℝ) (v : TorusVertex L) :
    torusRealDivergence (torusRealUniformHarmonicCurrent (L := L) p q) v = 0 := by
  simp [torusRealDivergence, torusRealUniformHarmonicCurrent]

theorem torusRealUniformHarmonicCurrent_horizontalPeriod (p q : ℝ) (x : ZMod L) :
    torusRealHorizontalPeriod (torusRealUniformHarmonicCurrent (L := L) p q) x = p := by
  change (∑ y : ZMod L, p / (L : ℝ)) = p
  exact sum_const_zmod_div p

theorem torusRealUniformHarmonicCurrent_verticalPeriod (p q : ℝ) (y : ZMod L) :
    torusRealVerticalPeriod (torusRealUniformHarmonicCurrent (L := L) p q) y = q := by
  change (∑ x : ZMod L, q / (L : ℝ)) = q
  exact sum_const_zmod_div q

private theorem torusGraph_grad_sum_horizontal (hL : 2 < L)
    (u : TorusVertex L → ℝ) (y : ZMod L) :
    (∑ x : ZMod L, (torusGraph L hL).grad u ((x, y), false)) = 0 := by
  change (∑ x : ZMod L, (u (x, y) - u (x + 1, y))) = 0
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ x : ZMod L, u (x + 1, y)) = ∑ x : ZMod L, u (x, y) := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : ZMod L))
      (fun x : ZMod L => u (x, y)))
  rw [hshift, sub_self]

private theorem torusGraph_grad_sum_vertical (hL : 2 < L)
    (u : TorusVertex L → ℝ) (x : ZMod L) :
    (∑ y : ZMod L, (torusGraph L hL).grad u ((x, y), true)) = 0 := by
  change (∑ y : ZMod L, (u (x, y) - u (x, y + 1))) = 0
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ y : ZMod L, u (x, y + 1)) = ∑ y : ZMod L, u (x, y) := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : ZMod L))
      (fun y : ZMod L => u (x, y)))
  rw [hshift, sub_self]

private theorem torusRealUniformHarmonicCurrent_cross_grad_zero
    (hL : 2 < L) (u : TorusVertex L → ℝ) (p q : ℝ) :
    (∑ e : TorusEdge L,
      (torusGraph L hL).grad u e * torusRealUniformHarmonicCurrent p q e) = 0 := by
  have hx : (∑ v : TorusVertex L,
      (torusGraph L hL).grad u (v, false)) = 0 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [torusGraph_grad_sum_horizontal hL u]
    simp
  have hy : (∑ v : TorusVertex L,
      (torusGraph L hL).grad u (v, true)) = 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [torusGraph_grad_sum_vertical hL u]
    simp
  have hsplit :
      (∑ e : TorusEdge L,
        (torusGraph L hL).grad u e * torusRealUniformHarmonicCurrent p q e) =
        (∑ v : TorusVertex L, (torusGraph L hL).grad u (v, false) * (p / (L : ℝ))) +
        (∑ v : TorusVertex L, (torusGraph L hL).grad u (v, true) * (q / (L : ℝ))) := by
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [show (∑ d : Bool, (torusGraph L hL).grad u (v, d) *
        torusRealUniformHarmonicCurrent p q (v, d)) =
        (torusGraph L hL).grad u (v, false) * (p / (L : ℝ)) +
          (torusGraph L hL).grad u (v, true) * (q / (L : ℝ)) by
      rw [Fintype.sum_bool]
      simp [torusRealUniformHarmonicCurrent]; ring]
  rw [hsplit, ← Finset.sum_mul, ← Finset.sum_mul, hx, hy]
  ring

private theorem torusRealUniformHarmonicCurrent_energy (p q : ℝ) :
    (∑ e : TorusEdge L, torusRealUniformHarmonicCurrent p q e ^ 2) = p ^ 2 + q ^ 2 := by
  have hconst (c : ℝ) :
      (∑ v : TorusVertex L, (c / (L : ℝ)) ^ 2) = c ^ 2 := by
    rw [Fintype.sum_prod_type]
    have hterm : (c / (L : ℝ)) ^ 2 = (c ^ 2 / (L : ℝ)) / (L : ℝ) := by
      field_simp
    simp_rw [hterm, sum_const_zmod_div]
  have hsplit :
      (∑ e : TorusEdge L, torusRealUniformHarmonicCurrent p q e ^ 2) =
        (∑ v : TorusVertex L, (p / (L : ℝ)) ^ 2) +
        (∑ v : TorusVertex L, (q / (L : ℝ)) ^ 2) := by
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [show (∑ d : Bool, torusRealUniformHarmonicCurrent p q (v, d) ^ 2) =
        (p / (L : ℝ)) ^ 2 + (q / (L : ℝ)) ^ 2 by
      rw [Fintype.sum_bool]
      simp [torusRealUniformHarmonicCurrent]; ring]
  rw [hsplit, hconst p, hconst q]

/-- A source current and a potential with matching divergence differ by a cycle. Removing its
constant harmonic periods leaves a dual gradient, which is canceled by a pinned periodic height.
The corrected source-plus-gradient field is the primal gradient plus the two harmonic currents. -/
theorem exists_periodicHarmonicCorrection (hL : 2 < L)
    (j : TorusEdge L → ℝ) (u : TorusVertex L → ℝ)
    (hdiv : ∀ v,
      torusRealDivergence j v =
        torusRealDivergence (fun e => (torusGraph L hL).grad u e) v) :
    ∃ (σ : TorusVertex L → ℝ) (p q : ℝ),
      σ (0, 0) = 0 ∧
      (∀ e, j e + (torusDualGraph hL).grad σ e =
        (torusGraph L hL).grad u e + torusRealUniformHarmonicCurrent p q e) ∧
      p = torusRealHorizontalPeriod
        (j - fun e => (torusGraph L hL).grad u e) 0 ∧
      q = torusRealVerticalPeriod
        (j - fun e => (torusGraph L hL).grad u e) 0 := by
  let cyc : TorusEdge L → ℝ := j - fun e => (torusGraph L hL).grad u e
  let p := torusRealHorizontalPeriod cyc 0
  let q := torusRealVerticalPeriod cyc 0
  let H := torusRealUniformHarmonicCurrent (L := L) p q
  let c : TorusEdge L → ℝ := cyc - H
  have hdivCyc : ∀ v, torusRealDivergence cyc v = 0 := by
    intro v
    have hsub : torusRealDivergence
        (j - fun e => (torusGraph L hL).grad u e) v =
        torusRealDivergence j v -
          torusRealDivergence (fun e => (torusGraph L hL).grad u e) v := by
      simp [torusRealDivergence, Pi.sub_apply]
      ring
    rw [show cyc = j - fun e => (torusGraph L hL).grad u e by rfl, hsub, hdiv v]
    ring
  have hdivC : ∀ v, torusRealDivergence c v = 0 := by
    intro v
    have hsub : torusRealDivergence (cyc - H) v =
        torusRealDivergence cyc v - torusRealDivergence H v := by
      simp [torusRealDivergence, Pi.sub_apply]
      ring
    rw [show c = cyc - H by rfl, hsub, hdivCyc v,
      torusRealUniformHarmonicCurrent_divergence]
    ring
  have hwindX : torusRealHorizontalPeriod c 0 = 0 := by
    calc
      torusRealHorizontalPeriod c 0 =
          torusRealHorizontalPeriod cyc 0 - torusRealHorizontalPeriod H 0 := by
        simp only [c, H, torusRealHorizontalPeriod, Pi.sub_apply, Finset.sum_sub_distrib]
      _ = p - p := by
        rw [show p = torusRealHorizontalPeriod cyc 0 by rfl,
          torusRealUniformHarmonicCurrent_horizontalPeriod]
      _ = 0 := sub_self _
  have hwindY : torusRealVerticalPeriod c 0 = 0 := by
    calc
      torusRealVerticalPeriod c 0 =
          torusRealVerticalPeriod cyc 0 - torusRealVerticalPeriod H 0 := by
        simp only [c, H, torusRealVerticalPeriod, Pi.sub_apply, Finset.sum_sub_distrib]
      _ = q - q := by
        rw [show q = torusRealVerticalPeriod cyc 0 by rfl,
          torusRealUniformHarmonicCurrent_verticalPeriod]
      _ = 0 := sub_self _
  let h := torusRealPathHeight c
  let σ := -h
  have hroot : σ (0, 0) = 0 := by
    simp [σ, h, torusRealPathHeight_root]
  have hcycle : c = torusDualGradientReal h :=
    torusRealCycle_eq_dualGradient hL c hdivC hwindX hwindY
  have hcorr : ∀ e, j e + (torusDualGraph hL).grad σ e =
      (torusGraph L hL).grad u e + H e := by
    intro e
    have hsigma : (torusDualGraph hL).grad σ e = -torusDualGradientReal h e := by
      rw [torusDualGraph_grad_eq_torusDualGradientReal]
      cases e with
      | mk z d => cases d <;> simp [σ, torusDualGradientReal] <;> ring
    have he := congrFun hcycle e
    calc
      j e + (torusDualGraph hL).grad σ e = j e - torusDualGradientReal h e := by
        rw [hsigma]
        ring
      _ = j e - c e := by rw [he]
      _ = (torusGraph L hL).grad u e + H e := by
        simp [c, cyc, H, torusRealUniformHarmonicCurrent]
        ring
  refine ⟨σ, p, q, hroot, ?_, ?_, ?_⟩
  · intro e
    exact hcorr e
  · rfl
  · rfl

/-- The corrected source energy splits into the Green-flow energy and the squared harmonic
periods. The two terms are orthogonal on the periodic torus. -/
theorem exists_periodicHarmonicCorrection_energy (hL : 2 < L)
    (j : TorusEdge L → ℝ) (u : TorusVertex L → ℝ)
    (hdiv : ∀ v,
      torusRealDivergence j v =
        torusRealDivergence (fun e => (torusGraph L hL).grad u e) v) :
    ∃ (σ : TorusVertex L → ℝ) (p q : ℝ),
      σ (0, 0) = 0 ∧
      (∀ e, j e + (torusDualGraph hL).grad σ e =
        (torusGraph L hL).grad u e + torusRealUniformHarmonicCurrent p q e) ∧
      (∑ e : TorusEdge L,
        (j e + (torusDualGraph hL).grad σ e) ^ 2) =
        (torusGraph L hL).energy u + p ^ 2 + q ^ 2 := by
  obtain ⟨σ, p, q, hroot, hdecomp, -, -⟩ :=
    exists_periodicHarmonicCorrection hL j u hdiv
  refine ⟨σ, p, q, hroot, hdecomp, ?_⟩
  calc
    (∑ e : TorusEdge L, (j e + (torusDualGraph hL).grad σ e) ^ 2) =
        ∑ e : TorusEdge L,
          ((torusGraph L hL).grad u e + torusRealUniformHarmonicCurrent p q e) ^ 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hdecomp e]
    _ = (torusGraph L hL).energy u + p ^ 2 + q ^ 2 := by
      unfold Multigraph.energy
      rw [show (fun e : TorusEdge L =>
          ((torusGraph L hL).grad u e + torusRealUniformHarmonicCurrent p q e) ^ 2) =
          (fun e => ((torusGraph L hL).grad u e) ^ 2 +
            2 * (torusGraph L hL).grad u e * torusRealUniformHarmonicCurrent p q e +
            (torusRealUniformHarmonicCurrent p q e) ^ 2) by
        funext e; ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcross :
          (∑ e : TorusEdge L, 2 * (torusGraph L hL).grad u e *
            torusRealUniformHarmonicCurrent p q e) = 0 := by
        calc
          _ = 2 * (∑ e : TorusEdge L, (torusGraph L hL).grad u e *
              torusRealUniformHarmonicCurrent p q e) := by
            have hpoint : (fun e : TorusEdge L => 2 * (torusGraph L hL).grad u e *
                torusRealUniformHarmonicCurrent p q e) =
                (fun e => 2 * ((torusGraph L hL).grad u e *
                  torusRealUniformHarmonicCurrent p q e)) := by
              funext e
              ring
            rw [hpoint, ← Finset.mul_sum]
          _ = 0 := by rw [torusRealUniformHarmonicCurrent_cross_grad_zero hL u p q]; ring
      rw [hcross, torusRealUniformHarmonicCurrent_energy p q]
      ring

end

end FroehlichSpencer.BKT.Rotator.Periodic

end
