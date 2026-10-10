/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.IDS.Green
public import FroehlichSpencer.Infra.Green.APriori
public import FroehlichSpencer.Infra.Lattice.Decay
public import FroehlichSpencer.Infra.Ergodic.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Boundary comparison of finite- and infinite-volume Green functions

For fixed `z` with `Im z ≠ 0` and any potential `v`, the average over the cube `Q_L` of
`|G_{Q_L}(z; x, x) - G(z; x, x)|` tends to `0` as `L → ∞`.

Method: the `ℓ²` comparison of the
finite-volume resolvent column with the infinite-volume column (error controlled by the tail of
the latter outside the cube), Combes–Thomas decay for the tail at interior points, and the a priori
bound `2 / |Im z|` on the boundary layer, whose relative size tends to `0`.

Motivation: Fröhlich–Spencer (1983), (1.28)–(1.29), Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace FroehlichSpencer.IDS

/-- The tail profile: `exp (-c ‖u‖)` for lattice points at Euclidean distance more than `r`. -/
private noncomputable def tailProfile (ν : ℕ) (c r : ℝ) (u : Site ν) : ℝ :=
  if r < ‖Infra.Lattice.latticeCast u‖ then Real.exp (-c * ‖Infra.Lattice.latticeCast u‖) else 0

private theorem tailProfile_nonneg (ν : ℕ) (c r : ℝ) (u : Site ν) : 0 ≤ tailProfile ν c r u := by
  unfold tailProfile; split_ifs <;> positivity

private theorem summable_tailProfile {ν : ℕ} {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Summable (tailProfile ν c r) := by
  refine (Infra.Lattice.summable_exp_neg_norm_latticeCast (ν := ν) hc).of_nonneg_of_le
    (tailProfile_nonneg ν c r) fun u => ?_
  unfold tailProfile; split_ifs
  · exact le_rfl
  · positivity

private theorem tendsto_tsum_tailProfile {ν : ℕ} {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℕ => ∑' u, tailProfile ν c (r : ℝ) u) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun (r : ℕ) (u : Site ν) => tailProfile ν c (r : ℝ) u) (g := fun _ => 0)
    (bound := fun u => Real.exp (-c * ‖Infra.Lattice.latticeCast u‖))
    (Infra.Lattice.summable_exp_neg_norm_latticeCast (ν := ν) hc) (fun u => ?_)
    (Eventually.of_forall fun r u => ?_)
  · simpa using h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖Infra.Lattice.latticeCast u‖⌉₊] with r hr
    have : ¬ ((r : ℝ) < ‖Infra.Lattice.latticeCast u‖) :=
      not_lt.2 ((Nat.le_ceil _).trans (by exact_mod_cast hr))
    simp [tailProfile, this]
  · rw [Real.norm_of_nonneg (tailProfile_nonneg ν c _ u)]
    unfold tailProfile; split_ifs
    · exact le_rfl
    · positivity

/-- A point outside the cube of radius `L` is at distance more than `r` from the cube of radius
`L - r`. -/
private theorem lt_norm_latticeCast_sub_of_mem_cube {ν L r : ℕ} (hrL : r ≤ L) {x w : Site ν}
    (hx : x ∈ Infra.cube ν (L - r)) (hw : w ∉ Infra.cube ν L) :
    (r : ℝ) < ‖Infra.Lattice.latticeCast (w - x)‖ := by
  rw [Infra.mem_cube] at hx hw
  push Not at hw
  obtain ⟨i, hi⟩ := hw
  have hxi := hx i
  have hcast : (((L - r : ℕ) : ℤ)) = (L : ℤ) - r := by omega
  rw [hcast] at hxi
  have h1 : (r : ℤ) < |(w - x) i| := by
    rw [lt_abs, Pi.sub_apply]
    by_cases h : -(L : ℤ) ≤ w i
    · have := hi h; omega
    · omega
  have h2 : (r : ℝ) < |(((w - x) i : ℤ) : ℝ)| := by exact_mod_cast h1
  exact h2.trans_le (Infra.Lattice.abs_latticeCast_apply_le_norm _ i)

private theorem tail_le {ν L r : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ) (hrL : r ≤ L)
    {x : Site ν} (hx : x ∈ Infra.cube ν (L - r)) :
    ∑' w, (if w ∈ Infra.cube ν L then 0 else ‖latticeGreen ν z v x w‖ ^ 2) ≤
      (2 / |z.im|) ^ 2 * ∑' u, tailProfile ν
        (2 * Real.log (1 + |z.im| / (2 * (2 * (ν : ℝ) + 1)))) (r : ℝ) u := by
  have hη : 0 < |z.im| := abs_pos.2 hz
  set μ := Real.log (1 + |z.im| / (2 * (2 * (ν : ℝ) + 1))) with hμ
  have hμpos : 0 < μ := Real.log_pos (by
    have : 0 < |z.im| / (2 * (2 * (ν : ℝ) + 1)) := by positivity
    linarith)
  have hsum : Summable fun u => tailProfile ν (2 * μ) (r : ℝ) u :=
    summable_tailProfile (by positivity) _
  have hshift : Summable fun w : Site ν => (2 / |z.im|) ^ 2 *
      tailProfile ν (2 * μ) (r : ℝ) (w - x) :=
    (((Equiv.subRight x).summable_iff (f := fun u => tailProfile ν (2 * μ) (r : ℝ) u)).2
      hsum).mul_left _
  have hpt : ∀ w : Site ν, (if w ∈ Infra.cube ν L then 0 else ‖latticeGreen ν z v x w‖ ^ 2) ≤
      (2 / |z.im|) ^ 2 * tailProfile ν (2 * μ) (r : ℝ) (w - x) := by
    intro w
    by_cases hw : w ∈ Infra.cube ν L
    · simp only [hw, ite_true]
      exact mul_nonneg (by positivity) (tailProfile_nonneg _ _ _ _)
    · simp only [hw, ite_false]
      have hd := lt_norm_latticeCast_sub_of_mem_cube hrL hx hw
      have hg := norm_latticeGreen_le_exp hz v x w
      rw [← hμ, ← Infra.Lattice.latticeCast_sub] at hg
      have h0 : 0 ≤ ‖latticeGreen ν z v x w‖ := norm_nonneg _
      have hsq := pow_le_pow_left₀ h0 hg 2
      refine hsq.trans (le_of_eq ?_)
      unfold tailProfile
      simp only [hd, ite_true]
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
  have hlsum : Summable fun w : Site ν =>
      (if w ∈ Infra.cube ν L then 0 else ‖latticeGreen ν z v x w‖ ^ 2) :=
    hshift.of_nonneg_of_le (fun w => by split_ifs <;> positivity) hpt
  calc _ ≤ ∑' w : Site ν, (2 / |z.im|) ^ 2 * tailProfile ν (2 * μ) (r : ℝ) (w - x) :=
        hlsum.tsum_le_tsum hpt hshift
    _ = (2 / |z.im|) ^ 2 * ∑' w : Site ν, tailProfile ν (2 * μ) (r : ℝ) (w - x) :=
        tsum_mul_left
    _ = _ := by
        congr 1
        exact (Equiv.subRight x).tsum_eq (fun u => tailProfile ν (2 * μ) (r : ℝ) u)

/-- Pointwise comparison of the finite-volume diagonal Green function with the infinite-volume one
in terms of the tail of the infinite-volume column outside the cube. -/
private theorem norm_sub_le_sqrt_tail {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ)
    (Λ : Finset (Site ν)) {x : Site ν} (hx : x ∈ Λ) :
    ‖Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) Λ z x x -
        latticeGreen ν z v x x‖ ≤
      Real.sqrt ((1 + (2 * (ν : ℝ)) ^ 2 / z.im ^ 2) *
        ∑' w, (if w ∈ Λ then 0 else ‖latticeGreen ν z v x w‖ ^ 2)) := by
  classical
  set G := Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) Λ z x with hG
  set g := latticeGreen ν z v x with hg
  have hmem := (latticeGreen_spec hz v x).1
  have hgs : Summable fun w => ‖g w‖ ^ 2 := by
    have := (memℓp_gen_iff (by simp)).1 hmem
    simpa using this
  have hGs : Summable fun w => ‖G w‖ ^ 2 :=
    summable_of_ne_finset_zero (s := Λ) fun w hw => by
      simp [hG, Infra.resolventColumn_of_notMem_left _ _ z x hw]
  have hds : Summable fun w => ‖G w - g w‖ ^ 2 := by
    refine ((hGs.mul_left 2).add (hgs.mul_left 2)).of_nonneg_of_le (fun w => by positivity)
      fun w => ?_
    have h := norm_sub_le (G w) (g w)
    have h0 := norm_nonneg (G w - g w)
    nlinarith [sq_nonneg (‖G w‖ - ‖g w‖), norm_nonneg (G w), norm_nonneg (g w)]
  have h1 : ‖G x - g x‖ ^ 2 ≤ ∑' w, ‖G w - g w‖ ^ 2 :=
    hds.le_tsum x fun j _ => by positivity
  have h2 := Infra.tsum_norm_sq_resolventColumn_sub_le (hoppingKernel_symm ν)
    (hoppingKernel_finite ν) (sum_norm_hoppingKernel_le ν) (fun w => v w + 2 * (ν : ℝ)) hz hx
    hmem (latticeGreen_spec hz v x).2
  have h3 := h1.trans h2
  have h4 := Real.abs_le_sqrt h3
  rwa [abs_of_nonneg (norm_nonneg _)] at h4

/-- The finite-volume diagonal Green function and the infinite-volume one differ by at most
`2 / |Im z|`. -/
private theorem norm_sub_le_two_div {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ)
    (Λ : Finset (Site ν)) (x : Site ν) :
    ‖Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) Λ z x x -
        latticeGreen ν z v x x‖ ≤ 2 / |z.im| := by
  classical
  have hη : 0 < |z.im| := abs_pos.2 hz
  set G := Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) Λ z x with hG
  have hGs : Summable fun w => ‖G w‖ ^ 2 := by
    by_cases hxΛ : x ∈ Λ
    · exact summable_of_ne_finset_zero (s := Λ) fun w hw => by
        simp [hG, Infra.resolventColumn_of_notMem_left _ _ z x hw]
    · exact summable_of_ne_finset_zero (s := ∅) fun w _ => by
        simp [hG, Infra.resolventColumn_of_notMem_right _ _ z w hxΛ]
  have h1 : ‖G x‖ ^ 2 ≤ ∑' w, ‖G w‖ ^ 2 := hGs.le_tsum x fun j _ => by positivity
  have h2 := Infra.tsum_norm_sq_resolventColumn_le (hoppingKernel_symm ν)
    (fun w => v w + 2 * (ν : ℝ)) Λ hz x
  have h3 : (1 / |z.im|) ^ 2 = 1 / z.im ^ 2 := by rw [div_pow, sq_abs, one_pow]
  have hGb : ‖G x‖ ≤ 1 / |z.im| :=
    le_of_sq_le_sq (h1.trans (h2.trans_eq h3.symm)) (by positivity)
  have hgb := norm_latticeGreen_le hz v x x
  calc _ ≤ ‖G x‖ + ‖latticeGreen ν z v x x‖ := norm_sub_le _ _
    _ ≤ 1 / |z.im| + 1 / |z.im| := add_le_add hGb hgb
    _ = 2 / |z.im| := by ring

/-- The relative size of the boundary layer of width `r` in the cube tends to `0`. -/
private theorem tendsto_card_layer_div (ν r : ℕ) :
    Tendsto (fun L : ℕ => ((Infra.cube ν L \ Infra.cube ν (L - r)).card : ℝ) /
      (Infra.cube ν L).card) atTop (𝓝 0) := by
  have hden : Tendsto (fun L : ℕ => 2 * (L : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have h1 : Tendsto (fun L : ℕ => (2 * (r : ℝ)) / (2 * (L : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h2 : Tendsto (fun L : ℕ => (1 - (2 * (r : ℝ)) / (2 * (L : ℝ) + 1)) ^ ν) atTop
      (𝓝 ((1 - 0) ^ ν)) := (tendsto_const_nhds.sub h1).pow ν
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  simp only [sub_zero, one_pow, sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop r] with L hrL
  have hsub := Finset.card_sdiff_add_card_eq_card (Infra.cube_mono (ν := ν) (Nat.sub_le L r))
  have hc : ((Infra.cube ν L \ Infra.cube ν (L - r)).card : ℝ) =
      (Infra.cube ν L).card - (Infra.cube ν (L - r)).card := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast hsub
  rw [hc, sub_div, div_self (by exact_mod_cast (Infra.card_cube_pos ν L).ne'),
    Infra.card_cube, Infra.card_cube]
  congr 1
  push_cast
  rw [← div_pow]
  congr 1
  have hcast : ((L - r : ℕ) : ℝ) = (L : ℝ) - r := Nat.cast_sub hrL
  rw [hcast]
  have : (2 * (L : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_average_norm_resolventColumn_sub_latticeGreen {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    (v : Site ν → ℝ) :
    Tendsto (fun L : ℕ => ((Infra.cube ν L).card : ℝ)⁻¹ * ∑ x ∈ Infra.cube ν L,
      ‖Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) (Infra.cube ν L) z x x -
        latticeGreen ν z v x x‖) atTop (𝓝 0) := by
  classical
  have hη : 0 < |z.im| := abs_pos.2 hz
  set μ := Real.log (1 + |z.im| / (2 * (2 * (ν : ℝ) + 1))) with hμ
  have hμpos : 0 < μ := Real.log_pos (by
    have : 0 < |z.im| / (2 * (2 * (ν : ℝ) + 1)) := by positivity
    linarith)
  set C : ℝ := 1 + (2 * (ν : ℝ)) ^ 2 / z.im ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  set B : ℕ → ℝ := fun r => Real.sqrt (C * ((2 / |z.im|) ^ 2 *
    ∑' u, tailProfile ν (2 * μ) (r : ℝ) u)) with hB
  have hBt : Tendsto B atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (C * ((2 / |z.im|) ^ 2 * 0))).comp
      (((tendsto_tsum_tailProfile (ν := ν) (c := 2 * μ) (by positivity)).const_mul
        ((2 / |z.im|) ^ 2)).const_mul C)
    simpa [Function.comp_def, hB] using h
  -- the bound for large `L`
  have hbound : ∀ r L : ℕ, r ≤ L →
      ((Infra.cube ν L).card : ℝ)⁻¹ * ∑ x ∈ Infra.cube ν L,
        ‖Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) (Infra.cube ν L)
          z x x - latticeGreen ν z v x x‖ ≤
      B r + 2 / |z.im| * (((Infra.cube ν L \ Infra.cube ν (L - r)).card : ℝ) /
        (Infra.cube ν L).card) := by
    intro r L hrL
    set Λ := Infra.cube ν L with hΛ
    set I := Infra.cube ν (L - r) with hI
    have hsub : I ⊆ Λ := Infra.cube_mono (Nat.sub_le L r)
    have hcard : (0 : ℝ) < Λ.card := by exact_mod_cast Infra.card_cube_pos ν L
    set f : Site ν → ℝ := fun x =>
      ‖Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) Λ z x x -
        latticeGreen ν z v x x‖ with hf
    have hin : ∀ x ∈ I, f x ≤ B r := by
      intro x hx
      refine (norm_sub_le_sqrt_tail hz v Λ (hsub hx)).trans (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_left (tail_le hz v hrL hx) hC0
    have hlay : ∀ x ∈ Λ \ I, f x ≤ 2 / |z.im| := fun x _ => norm_sub_le_two_div hz v Λ x
    have hsum : ∑ x ∈ Λ, f x ≤ I.card * B r + (Λ \ I).card * (2 / |z.im|) := by
      rw [← Finset.sum_sdiff hsub, add_comm]
      refine add_le_add ?_ ?_
      · exact (Finset.sum_le_card_nsmul _ _ _ hin).trans_eq (by simp)
      · exact (Finset.sum_le_card_nsmul _ _ _ hlay).trans_eq (by simp)
    have hB0 : 0 ≤ B r := Real.sqrt_nonneg _
    have hIΛ : (I.card : ℝ) ≤ Λ.card := by exact_mod_cast Finset.card_le_card hsub
    calc (Λ.card : ℝ)⁻¹ * ∑ x ∈ Λ, f x
        ≤ (Λ.card : ℝ)⁻¹ * (I.card * B r + (Λ \ I).card * (2 / |z.im|)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (Λ.card : ℝ)⁻¹ * (Λ.card * B r + (Λ \ I).card * (2 / |z.im|)) := by
          gcongr
      _ = B r + 2 / |z.im| * (((Λ \ I).card : ℝ) / Λ.card) := by
          field_simp
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine Eventually.of_forall fun L => lt_of_lt_of_le ha ?_
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => norm_nonneg _)
  · obtain ⟨r, hr⟩ := (hBt.eventually (gt_mem_nhds (show (0 : ℝ) < a / 2 by linarith))).exists
    have hq := (tendsto_card_layer_div ν r).const_mul (2 / |z.im|)
    rw [mul_zero] at hq
    filter_upwards [hq.eventually (gt_mem_nhds (show (0 : ℝ) < a / 2 by linarith)),
      eventually_ge_atTop r] with L hL hrL
    have := hbound r L hrL
    linarith
