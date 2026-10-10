/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Infra.Green.PathExpansion
public import FroehlichSpencer.IDS.Green
public import FroehlichSpencer.Multiscale.Singular
public import FroehlichSpencer.Surface.FiniteGreen

/-!
# The base clause of the determinism estimate
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


theorem norm_finiteGreen_le_pathExpansion {ν : ℕ} (P : Multiscale.Params)
    (hN : 2 * (ν : ℝ) < P.Nthr) {B : Finset (Site ν)} {v : Site ν → ℝ}
    (hB : ∀ x ∈ B, x ∉ Multiscale.singular0 P v) {ε : ℝ} (hε : ε ≠ 0) (x y : {x // x ∈ B}) :
    ‖finiteGreen ν B v P.E ε hε x y‖ ≤
      (2 * ν / P.Nthr) ^ ⌈Multiscale.siteDist ν x y⌉₊ / (P.Nthr - 2 * ν) := by
  have h := Infra.norm_resolventColumn_le_of_diag_dominant (a := hoppingKernel ν)
    (K := 2 * (ν : ℝ)) (sum_norm_hoppingKernel_le ν)
    (d := siteDist ν) (siteDist_triangle ν) (siteDist_self ν)
    (fun x y h => by
      rw [siteDist_eq_norm]; exact IDS.norm_latticeCast_sub_le_one_of_hoppingKernel_ne_zero h)
    (fun w => v w + 2 * (ν : ℝ)) B (z := (P.E : ℂ) + (ε : ℂ) * Complex.I) (N := P.Nthr)
    hN (fun w hw => by
      have h1 := not_le.1 (mt (mem_singular0 P v w).2 (hB w hw))
      refine le_trans (le_of_lt h1) (le_trans ?_ (Complex.abs_re_le_norm _))
      have : (((v w + 2 * (ν : ℝ) : ℝ) : ℂ) - ((P.E : ℂ) + (ε : ℂ) * Complex.I)).re =
          v w - P.E + 2 * (ν : ℝ) := by simp; ring
      push_cast at this ⊢
      rw [this])
    x.1 y.1
  rw [Infra.resolventColumn_of_mem _ _ _ x.2 y.2] at h
  unfold finiteGreen
  rw [hamiltonian_eq_restrictedOp]
  exact h


theorem norm_finiteGreen_le_one {ν : ℕ} (P : Multiscale.Params)
    (hN : 2 * (ν : ℝ) + 1 ≤ P.Nthr) {B : Finset (Site ν)} {v : Site ν → ℝ}
    (hB : ∀ x ∈ B, x ∉ Multiscale.singular0 P v) {ε : ℝ} (hε : ε ≠ 0) (x y : {x // x ∈ B}) :
    ‖finiteGreen ν B v P.E ε hε x y‖ ≤ 1 := by
  have hN' : 2 * (ν : ℝ) < P.Nthr := by linarith
  have h := norm_finiteGreen_le_pathExpansion P hN' hB hε x y
  have hν : (0 : ℝ) ≤ 2 * ν := by positivity
  have hpos : 0 < P.Nthr := by linarith
  refine h.trans ?_
  have h1 : (2 * (ν : ℝ) / P.Nthr) ^ ⌈siteDist ν x y⌉₊ ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hpos).2 hN'.le)
  rw [div_le_one (by linarith)]
  linarith


theorem norm_finiteGreen_le_exp_base {ν : ℕ} (P : Multiscale.Params)
    (hN : 2 * (ν : ℝ) + 1 ≤ P.Nthr) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {B : Finset (Site ν)}
    {v : Site ν → ℝ} (hB : ∀ x ∈ B, x ∉ Multiscale.singular0 P v) {ε : ℝ} (hε : ε ≠ 0)
    (x y : {x // x ∈ B}) :
    ‖finiteGreen ν B v P.E ε hε x y‖ ≤
      Real.exp (-(Real.log (P.Nthr / (2 * ν)) -
        C₀ * Multiscale.scaleD P.K₀ 0 ^ (-(1 / 4 : ℝ))) * Multiscale.siteDist ν x y) := by
  have hN' : 2 * (ν : ℝ) < P.Nthr := by linarith
  have hpos : 0 < P.Nthr := by linarith
  have ht : 0 ≤ siteDist ν x y := siteDist_nonneg ν x y
  have hc : 0 ≤ C₀ * scaleD P.K₀ 0 ^ (-(1 / 4 : ℝ)) := by
    rw [scaleD_zero]; positivity
  set c := C₀ * scaleD P.K₀ 0 ^ (-(1 / 4 : ℝ))
  rcases Nat.eq_zero_or_pos ν with h0 | hν
  · subst h0
    refine (norm_finiteGreen_le_one P hN hB hε x y).trans ?_
    rw [Real.one_le_exp_iff]
    simp only [Nat.cast_zero, mul_zero, div_zero, Real.log_zero, zero_sub, neg_neg]
    positivity
  · have hν' : (0 : ℝ) < ν := by exact_mod_cast hν
    have hq0 : 0 < 2 * (ν : ℝ) / P.Nthr := by positivity
    have hq1 : 2 * (ν : ℝ) / P.Nthr ≤ 1 := (div_le_one hpos).2 hN'.le
    have h := norm_finiteGreen_le_pathExpansion P hN' hB hε x y
    have hd : 1 / (P.Nthr - 2 * ν) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h1 : (2 * (ν : ℝ) / P.Nthr) ^ ⌈siteDist ν x y⌉₊ ≤
        (2 * (ν : ℝ) / P.Nthr) ^ (siteDist ν x y) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Nat.le_ceil _)
    have h2 : (2 * (ν : ℝ) / P.Nthr) ^ (siteDist ν x y) =
        Real.exp (-Real.log (P.Nthr / (2 * ν)) * siteDist ν x y) := by
      rw [Real.rpow_def_of_pos hq0, ← Real.log_inv, inv_div]
    have h3 : Real.exp (-Real.log (P.Nthr / (2 * ν)) * siteDist ν x y) ≤
        Real.exp (-(Real.log (P.Nthr / (2 * ν)) - c) * siteDist ν x y) := by
      apply Real.exp_le_exp.2
      nlinarith
    calc _ ≤ _ := h
      _ = (2 * (ν : ℝ) / P.Nthr) ^ ⌈siteDist ν x y⌉₊ * (1 / (P.Nthr - 2 * ν)) := by ring
      _ ≤ (2 * (ν : ℝ) / P.Nthr) ^ ⌈siteDist ν x y⌉₊ * 1 :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := by rw [mul_one]; exact h1.trans (h2.le.trans h3)


theorem norm_finiteGreen_le_exp_base_restricted {ν : ℕ} (P : Multiscale.Params)
    (hN : 2 * (ν : ℝ) + 1 ≤ P.Nthr) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {Λ A : Finset (Site ν)}
    {v : Site ν → ℝ} (hA : ∀ x ∈ A ∩ Λ, x ∉ Multiscale.singularSetsIn P Λ v 0) {ε : ℝ}
    (hε : ε ≠ 0) (x y : {x // x ∈ A ∩ Λ}) :
    ‖finiteGreen ν (A ∩ Λ) v P.E ε hε x y‖ ≤ 1 ∧
      ‖finiteGreen ν (A ∩ Λ) v P.E ε hε x y‖ ≤
        Real.exp (-(Real.log (P.Nthr / (2 * ν)) -
          C₀ * Multiscale.scaleD P.K₀ 0 ^ (-(1 / 4 : ℝ))) * Multiscale.siteDist ν x y) := by
  have hB : ∀ x ∈ A ∩ Λ, x ∉ singular0 P v := fun x hx h =>
    hA x hx (show x ∈ singularSetsIn P Λ v 0 from ⟨h, (Finset.mem_inter.1 hx).2⟩)
  exact ⟨norm_finiteGreen_le_one P hN hB hε x y,
    norm_finiteGreen_le_exp_base P hN hC₀ hB hε x y⟩

end FroehlichSpencer.T12
