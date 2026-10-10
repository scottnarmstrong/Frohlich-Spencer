/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Infra.Green.Existence
public import FroehlichSpencer.Infra.Green.InfiniteVolumeRegularity
public import FroehlichSpencer.Infra.Ergodic.Basic
public import FroehlichSpencer.Infra.Lattice.Basic

/-!
# The lattice Green function

The infinite-volume Green function `G(z; x, y)(v)` on `ℤ^ν`, the unique square-summable solution of
`(-Δ + v - z) ψ = δ_y`, obtained from the generic theorem for `hoppingKernel ν` with potential
`v + 2ν`.

We prove the characterization, the bound `|G| ≤ 1/|Im z|`, shift covariance,
measurability in `v`, Combes–Thomas decay and the large-`t` asymptotics `it · G(it; y, y) → -1`.

Motivation: Fröhlich–Spencer (1983), (1.4), Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology

namespace FroehlichSpencer.IDS

/-- The lattice Green function `G(z; x, y)(v)` (source `y`, point `x`): the unique
square-summable solution of `(−Δ + v − z) ψ = δ_y` for `Im z ≠ 0` (junk value `0` if `Im z = 0`).
Internal helper of the IDS provider. -/
noncomputable def latticeGreen (ν : ℕ) (z : ℂ) (v : Site ν → ℝ) (y x : Site ν) : ℂ :=
  if hz : z.im ≠ 0 then
    (Infra.existsUnique_memℓp_eq_single (hoppingKernel_symm ν) (hoppingKernel_finite ν)
      (sum_norm_hoppingKernel_le ν) (fun w => v w + 2 * (ν : ℝ)) hz y).exists.choose x
  else 0

theorem latticeGreen_spec {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ) (y : Site ν) :
    Memℓp (latticeGreen ν z v y) 2 ∧ ∀ x, ∑' w, hoppingKernel ν x w * latticeGreen ν z v y w +
      (((v x + 2 * (ν : ℝ) : ℝ) : ℂ) - z) * latticeGreen ν z v y x =
        (Pi.single y 1 : Site ν → ℂ) x := by
  have h : latticeGreen ν z v y =
      (Infra.existsUnique_memℓp_eq_single (hoppingKernel_symm ν) (hoppingKernel_finite ν)
      (sum_norm_hoppingKernel_le ν) (fun w => v w + 2 * (ν : ℝ)) hz y).exists.choose := by
    funext x
    simp [latticeGreen, hz]
  rw [h]
  exact (Infra.existsUnique_memℓp_eq_single (hoppingKernel_symm ν) (hoppingKernel_finite ν)
      (sum_norm_hoppingKernel_le ν) (fun w => v w + 2 * (ν : ℝ)) hz y).exists.choose_spec

theorem eq_latticeGreen {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ) (y : Site ν)
    {ψ : Site ν → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, hoppingKernel ν x w * ψ w + (((v x + 2 * (ν : ℝ) : ℝ) : ℂ) - z) * ψ x =
      (Pi.single y 1 : Site ν → ℂ) x) :
    ψ = latticeGreen ν z v y :=
  (Infra.existsUnique_memℓp_eq_single (hoppingKernel_symm ν) (hoppingKernel_finite ν)
    (sum_norm_hoppingKernel_le ν) (fun w => v w + 2 * (ν : ℝ)) hz y).unique ⟨hψ, h⟩
    (latticeGreen_spec hz v y)

theorem norm_latticeGreen_le {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ) (y x : Site ν) :
    ‖latticeGreen ν z v y x‖ ≤ 1 / |z.im| :=
  Infra.norm_le_one_div_of_eq_single (hoppingKernel_symm ν) (hoppingKernel_finite ν)
    (sum_norm_hoppingKernel_le ν) (fun w => v w + 2 * (ν : ℝ)) hz (latticeGreen_spec hz v y).1
    (latticeGreen_spec hz v y).2 x

private theorem hoppingKernel_add_add {ν : ℕ} (x w a : Site ν) :
    hoppingKernel ν (x + a) (w + a) = hoppingKernel ν x w := by
  unfold hoppingKernel
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (w + a = x + a + Pi.single k (1 : ℤ)) ↔ (w = x + Pi.single k (1 : ℤ)) := by
    rw [add_right_comm, add_left_inj]
  have h2 : (w + a = x + a - Pi.single k (1 : ℤ)) ↔ (w = x - Pi.single k (1 : ℤ)) := by
    rw [add_sub_right_comm, add_left_inj]
  simp only [h1, h2]

theorem latticeGreen_shift {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ) (a y x : Site ν) :
    latticeGreen ν z v (y + a) (x + a) = latticeGreen ν z (Infra.latticeShift a v) y x := by
  have hmem : Memℓp (fun x => latticeGreen ν z v (y + a) (x + a)) 2 := by
    have h := (latticeGreen_spec hz v (y + a)).1
    rw [memℓp_gen_iff (by simp)] at h ⊢
    exact ((Equiv.addRight a).summable_iff (f := fun x => ‖latticeGreen ν z v (y + a) x‖ ^
      ENNReal.toReal 2)).2 h
  have heq := eq_latticeGreen hz (Infra.latticeShift a v) y
    (ψ := fun x => latticeGreen ν z v (y + a) (x + a)) hmem (fun x => by
      have h := (latticeGreen_spec hz v (y + a)).2 (x + a)
      have hs : ∑' w, hoppingKernel ν (x + a) w * latticeGreen ν z v (y + a) w =
          ∑' w, hoppingKernel ν x w * latticeGreen ν z v (y + a) (w + a) := by
        rw [← (Equiv.addRight a).tsum_eq]
        exact tsum_congr fun w => by simp [hoppingKernel_add_add]
      rw [hs] at h
      have hp : (Pi.single (y + a) 1 : Site ν → ℂ) (x + a) = (Pi.single y 1 : Site ν → ℂ) x := by
        simp [Pi.single_apply]
      rw [hp] at h
      simpa [Infra.latticeShift_apply] using h)
  exact congrFun heq x

theorem measurable_latticeGreen {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (y x : Site ν) :
    Measurable fun v : Site ν → ℝ => latticeGreen ν z v y x := by
  have hm := Infra.measurable_of_forall_eq_single (hoppingKernel_symm ν) (hoppingKernel_finite ν)
    (sum_norm_hoppingKernel_le ν) hz y x
    (Ψ := fun u => latticeGreen ν z (fun w => u w - 2 * (ν : ℝ)) y) (fun u => by
      refine ⟨(latticeGreen_spec hz _ y).1, fun x' => ?_⟩
      simpa using (latticeGreen_spec hz (fun w => u w - 2 * (ν : ℝ)) y).2 x')
  have hc : Measurable fun v : Site ν → ℝ => fun w => v w + 2 * (ν : ℝ) :=
    Measurable.of_eval fun w => (measurable_pi_apply w).add_const _
  have := hm.comp hc
  simpa [Function.comp_def] using this

theorem norm_latticeCast_sub_le_one_of_hoppingKernel_ne_zero {ν : ℕ} {x w : Site ν}
    (h : hoppingKernel ν x w ≠ 0) :
    ‖Infra.Lattice.latticeCast x - Infra.Lattice.latticeCast w‖ ≤ 1 := by
  obtain ⟨k, rfl | rfl⟩ := hoppingKernel_ne_zero_exists h
  · refine ((Infra.Lattice.norm_latticeCast_sub_eq_one_iff _ _).2 ⟨k, Or.inr ?_, ?_⟩).le
    · simp
    · intro j hj; simp [hj]
  · refine ((Infra.Lattice.norm_latticeCast_sub_eq_one_iff _ _).2 ⟨k, Or.inl ?_, ?_⟩).le
    · simp
    · intro j hj; simp [hj]

theorem norm_latticeGreen_le_exp {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ)
    (y x : Site ν) :
    ‖latticeGreen ν z v y x‖ ≤ 2 / |z.im| *
      Real.exp (-Real.log (1 + |z.im| / (2 * (2 * (ν : ℝ) + 1))) *
        ‖Infra.Lattice.latticeCast x - Infra.Lattice.latticeCast y‖) :=
  Infra.norm_le_exp_of_eq_single (hoppingKernel_symm ν) (hoppingKernel_finite ν)
    (sum_norm_hoppingKernel_le ν)
    (d := fun x y => ‖Infra.Lattice.latticeCast x - Infra.Lattice.latticeCast y‖)
    (fun x y w => Infra.Lattice.norm_latticeCast_sub_le_add x w y)
    (fun x => by simp) (fun x y h => norm_latticeCast_sub_le_one_of_hoppingKernel_ne_zero h)
    (fun w => v w + 2 * (ν : ℝ)) hz (latticeGreen_spec hz v y).1 (latticeGreen_spec hz v y).2 x

theorem tendsto_mul_latticeGreen (ν : ℕ) (v : Site ν → ℝ) (y : Site ν) :
    Tendsto (fun t : ℝ => (t : ℂ) * I * latticeGreen ν ((t : ℂ) * I) v y y) atTop (𝓝 (-1)) := by
  set C : ℝ := |v y + 2 * (ν : ℝ)| + 2 * (ν : ℝ) with hC
  have hbound : ∀ t : ℝ, 0 < t →
      ‖(t : ℂ) * I * latticeGreen ν ((t : ℂ) * I) v y y - (-1)‖ ≤ C / t := by
    intro t ht
    have hz : ((t : ℂ) * I).im ≠ 0 := by simpa using ht.ne'
    have hG : ∀ w, ‖latticeGreen ν ((t : ℂ) * I) v y w‖ ≤ 1 / t := fun w => by
      simpa [abs_of_pos ht] using norm_latticeGreen_le hz v y w
    have h := (latticeGreen_spec hz v y).2 y
    simp only [Pi.single_eq_same] at h
    set G := latticeGreen ν ((t : ℂ) * I) v y with hGdef
    have hS : ‖∑' w, hoppingKernel ν y w * G w‖ ≤ 2 * (ν : ℝ) / t := by
      rw [tsum_eq_sum (s := (hoppingKernel_finite ν y).toFinset) fun w hw => by
        have : hoppingKernel ν y w = 0 := by simpa using hw
        simp [this]]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ w ∈ (hoppingKernel_finite ν y).toFinset, ‖hoppingKernel ν y w * G w‖
          ≤ ∑ w ∈ (hoppingKernel_finite ν y).toFinset, ‖hoppingKernel ν y w‖ * (1 / t) :=
            Finset.sum_le_sum fun w _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hG w) (norm_nonneg _)
        _ = (∑ w ∈ (hoppingKernel_finite ν y).toFinset, ‖hoppingKernel ν y w‖) * (1 / t) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ 2 * (ν : ℝ) * (1 / t) :=
            mul_le_mul_of_nonneg_right (sum_norm_hoppingKernel_le ν y _) (by positivity)
        _ = 2 * (ν : ℝ) / t := by ring
    have heq : (t : ℂ) * I * G y - (-1) =
        (((v y + 2 * (ν : ℝ) : ℝ) : ℂ)) * G y + ∑' w, hoppingKernel ν y w * G w := by
      linear_combination -h
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(((v y + 2 * (ν : ℝ) : ℝ) : ℂ)) * G y‖ ≤ |v y + 2 * (ν : ℝ)| / t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc _ ≤ |v y + 2 * (ν : ℝ)| * (1 / t) :=
            mul_le_mul_of_nonneg_left (hG y) (abs_nonneg _)
        _ = _ := by ring
    calc _ ≤ |v y + 2 * (ν : ℝ)| / t + 2 * (ν : ℝ) / t := add_le_add h1 hS
      _ = C / t := by rw [hC]; ring
  have hlim : Tendsto (fun t : ℝ => C / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_gt_atTop 0).mono fun t ht => hbound t ht) hlim

end FroehlichSpencer.IDS
