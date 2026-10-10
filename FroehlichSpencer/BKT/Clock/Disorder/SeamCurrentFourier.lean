/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-!
# Clock Fourier coefficients and the current bound

For a function `f` sampled at the clock angles `2π l/N`, `clockAngleFourier N f m` is its discrete
Fourier coefficient. For `2π`-periodic `f`, `f(2πa/N − 2πb/N) = ∑_m f̂(m) χ(m(a − b))`
(`clockAngleFourier_inversion`).

The **current bound** (`norm_sum_prod_clock_le`) compares two clock partition sums
`Z(f) = ∑_k ∏_e f_e(θ_{src e} − θ_{tgt e})` with `θ = 2πk/N`. Expanding every edge weight in clock
characters and summing over the spins leaves only the currents `m : E → ℤ_N` with zero divergence
mod `N`, each counted `N^{|V|}` times:
`Z(f) = ∑_m (∏_e f̂_e(m_e)) Ω(m)`, with `Ω(m) ≥ 0`. Hence if `ĝ_e ≥ 0` and `‖f̂_e‖ ≤ λ_e ĝ_e`,
then `‖Z(f)‖ ≤ (∏_e λ_e) Z(g)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Complex Finset

/-! ### Clock characters -/

/-- The clock character `exp(2πi d/N)` of an integer `d`. -/
def clockChar (N : ℕ) (d : ℤ) : ℂ := Complex.exp (2 * Real.pi * I * d / N)

theorem clockChar_add (N : ℕ) (d d' : ℤ) : clockChar N (d + d') = clockChar N d * clockChar N d' := by
  unfold clockChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem clockChar_zero (N : ℕ) : clockChar N 0 = 1 := by
  simp [clockChar]

theorem clockChar_sum {ι : Type*} (s : Finset ι) (N : ℕ) (d : ι → ℤ) :
    clockChar N (∑ i ∈ s, d i) = ∏ i ∈ s, clockChar N (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [clockChar_zero]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, clockChar_add, ih]

theorem clockChar_mul_nat (N : ℕ) (d : ℤ) (m : ℕ) : clockChar N (m * d) = clockChar N d ^ m := by
  unfold clockChar
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem clockChar_eq_one_of_dvd {N : ℕ} (hN : 0 < N) {d : ℤ} (h : (N : ℤ) ∣ d) :
    clockChar N d = 1 := by
  obtain ⟨q, rfl⟩ := h
  unfold clockChar
  rw [Complex.exp_eq_one_iff]
  refine ⟨q, ?_⟩
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem clockChar_ne_one_of_not_dvd {N : ℕ} (hN : 0 < N) {d : ℤ} (h : ¬ (N : ℤ) ∣ d) :
    clockChar N d ≠ 1 := by
  intro h1
  unfold clockChar at h1
  rw [Complex.exp_eq_one_iff] at h1
  obtain ⟨q, hq⟩ := h1
  apply h
  refine ⟨q, ?_⟩
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (d : ℂ) = N * q := by
    field_simp at hq
    linear_combination hq
  exact_mod_cast h2

/-- **Orthogonality of the clock characters**: `∑_{m < N} χ(m d) = N` if `N ∣ d`, and `0`
otherwise. -/
theorem sum_clockChar_mul {N : ℕ} (hN : 0 < N) (d : ℤ) :
    ∑ m : Fin N, clockChar N ((m : ℕ) * d) = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  simp_rw [clockChar_mul_nat]
  rw [Fin.sum_univ_eq_sum_range (fun m => clockChar N d ^ m)]
  split_ifs with h
  · rw [clockChar_eq_one_of_dvd hN h]
    simp
  · have hne := clockChar_ne_one_of_not_dvd hN h
    rw [geom_sum_eq hne]
    have hpow : clockChar N d ^ N = 1 := by
      rw [← clockChar_mul_nat]
      exact clockChar_eq_one_of_dvd hN (dvd_mul_right _ _)
    rw [hpow, sub_self, zero_div]

/-! ### Clock Fourier coefficients -/

/-- The clock Fourier coefficient `f̂(m) = N⁻¹ ∑_l f(2πl/N) χ(−m l)`. -/
def clockAngleFourier (N : ℕ) (f : ℝ → ℝ) (m : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ l : Fin N, (f (2 * Real.pi * (l : ℕ) / N) : ℂ) * clockChar N (-((m : ℕ) * (l : ℕ)))

/-- **Clock Fourier inversion** at a difference of clock angles, for a `2π`-periodic function. -/
theorem clockAngleFourier_inversion {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ)
    (hper : Function.Periodic f (2 * Real.pi)) (a b : Fin N) :
    (f (2 * Real.pi * (a : ℕ) / N - 2 * Real.pi * (b : ℕ) / N) : ℂ) =
      ∑ m : Fin N, clockAngleFourier N f m * clockChar N ((m : ℕ) * ((a : ℕ) - (b : ℕ) : ℤ)) := by
  classical
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  -- the representative of `a − b`
  set d : ℤ := (a : ℕ) - (b : ℕ) with hd
  set l₀ : Fin N := ⟨(d % N).toNat, by
    have h1 : 0 ≤ d % N := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have h2 : d % N < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    omega⟩ with hl₀
  have hl₀val : ((l₀ : ℕ) : ℤ) = d % N := by
    have h1 : 0 ≤ d % N := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    simp only [hl₀]
    exact Int.toNat_of_nonneg h1
  -- the right side collapses to `l₀`
  have hrhs : ∑ m : Fin N, clockAngleFourier N f m * clockChar N ((m : ℕ) * d) =
      (N : ℂ)⁻¹ * ∑ l : Fin N, (f (2 * Real.pi * (l : ℕ) / N) : ℂ) *
        ∑ m : Fin N, clockChar N ((m : ℕ) * (d - (l : ℕ))) := by
    unfold clockAngleFourier
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    have : clockChar N ((m : ℕ) * (d - (l : ℕ))) =
        clockChar N (-((m : ℕ) * (l : ℕ))) * clockChar N ((m : ℕ) * d) := by
      rw [← clockChar_add]
      congr 1
      ring
    rw [this]
    ring
  rw [hrhs]
  simp_rw [sum_clockChar_mul hN]
  rw [Finset.sum_eq_single l₀]
  · have hdiv : (N : ℤ) ∣ d - (l₀ : ℕ) := by
      rw [hl₀val]
      exact ⟨d / N, by rw [Int.emod_def]; ring⟩
    have hite : (if (N : ℤ) ∣ d - (l₀ : ℕ) then (N : ℂ) else 0) = N := by simp [hdiv]
    rw [hite, mul_comm (f _ : ℂ) (N : ℂ), ← mul_assoc, inv_mul_cancel₀ hN', one_mul]
    congr 1
    obtain ⟨q, hq⟩ := hdiv
    rw [hd] at hq
    have hq' : ((a : ℕ) : ℝ) - (b : ℕ) - (l₀ : ℕ) = N * q := by exact_mod_cast hq
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hval : 2 * Real.pi * (a : ℕ) / N - 2 * Real.pi * (b : ℕ) / N =
        2 * Real.pi * (l₀ : ℕ) / N + q * (2 * Real.pi) := by
      have e1 : (2 * Real.pi * (a : ℕ) / N - 2 * Real.pi * (b : ℕ) / N) -
          (2 * Real.pi * (l₀ : ℕ) / N + q * (2 * Real.pi)) =
          2 * Real.pi / N * (((a : ℕ) : ℝ) - (b : ℕ) - (l₀ : ℕ) - N * q) := by
        field_simp
        ring
      rw [hq', sub_self, mul_zero] at e1
      linarith
    rw [hval, hper.int_mul q]
  · intro l _ hl
    have hndiv : ¬ (N : ℤ) ∣ d - (l : ℕ) := by
      intro h
      apply hl
      apply Fin.ext
      have h1 : d % N = ((l : ℕ) : ℤ) % N :=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)
      have hlt : ((l : ℕ) : ℤ) < N := by exact_mod_cast l.isLt
      have h2 : ((l : ℕ) : ℤ) % N = (l : ℕ) := Int.emod_eq_of_lt (by positivity) hlt
      have : ((l₀ : ℕ) : ℤ) = ((l : ℕ) : ℤ) := by rw [hl₀val, h1, h2]
      exact_mod_cast this.symm
    simp only [hndiv, ite_false, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The current bound -/

section Current

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The angle difference along an edge. -/
def clockEdgeAngle (N : ℕ) (src tgt : E → V) (k : V → Fin N) (e : E) : ℝ :=
  2 * Real.pi * (k (src e) : ℕ) / N - 2 * Real.pi * (k (tgt e) : ℕ) / N

/-- The clock partition sum of edge weights `f_e`. -/
def clockEdgeSum (N : ℕ) (src tgt : E → V) (f : E → ℝ → ℝ) : ℝ :=
  ∑ k : V → Fin N, ∏ e, f e (clockEdgeAngle N src tgt k e)

/-- The spin sum of the characters of a current. -/
def clockCurrentCount (N : ℕ) (src tgt : E → V) (m : E → Fin N) : ℂ :=
  ∑ k : V → Fin N, ∏ e, clockChar N ((m e : ℕ) * ((k (src e) : ℕ) - (k (tgt e) : ℕ) : ℤ))

/-- The current expansion `Z(f) = ∑_m (∏_e f̂_e(m_e)) Ω(m)`. -/
theorem clockEdgeSum_eq_currents {N : ℕ} (hN : 0 < N) (src tgt : E → V) (f : E → ℝ → ℝ)
    (hper : ∀ e, Function.Periodic (f e) (2 * Real.pi)) :
    (clockEdgeSum N src tgt f : ℂ) =
      ∑ m : E → Fin N, (∏ e, clockAngleFourier N (f e) (m e)) * clockCurrentCount N src tgt m := by
  classical
  unfold clockEdgeSum clockCurrentCount
  push_cast
  have hinv : ∀ (k : V → Fin N) (e : E),
      ((f e (clockEdgeAngle N src tgt k e) : ℝ) : ℂ) =
        ∑ μ : Fin N, clockAngleFourier N (f e) μ *
          clockChar N ((μ : ℕ) * ((k (src e) : ℕ) - (k (tgt e) : ℕ) : ℤ)) :=
    fun k e => clockAngleFourier_inversion hN (f e) (hper e) (k (src e)) (k (tgt e))
  simp_rw [hinv, Finset.prod_univ_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]

/-- The divergence of a current at a site. -/
def clockDivergence {N : ℕ} (src tgt : E → V) (m : E → Fin N) (v : V) : ℤ :=
  ∑ e, (if src e = v then ((m e : ℕ) : ℤ) else 0) - ∑ e, (if tgt e = v then ((m e : ℕ) : ℤ) else 0)

omit [Fintype V] [DecidableEq E] in
/-- Rearranging a sum over the edges by an endpoint. -/
theorem sum_edge_eq_sum_vertex [Fintype V] (s : E → V) (F : V → ℤ) (G : E → ℤ) :
    ∑ e, G e * F (s e) = ∑ v, F v * ∑ e, (if s e = v then G e else 0) := by
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

omit [DecidableEq E] in
theorem clockCurrentCount_eq {N : ℕ} (hN : 0 < N) (src tgt : E → V) (m : E → Fin N) :
    clockCurrentCount N src tgt m =
      ∏ v, (if (N : ℤ) ∣ clockDivergence src tgt m v then (N : ℂ) else 0) := by
  classical
  unfold clockCurrentCount
  have hrearr : ∀ k : V → Fin N,
      ∏ e, clockChar N ((m e : ℕ) * ((k (src e) : ℕ) - (k (tgt e) : ℕ) : ℤ)) =
        ∏ v, clockChar N ((k v : ℕ) * clockDivergence src tgt m v) := by
    intro k
    rw [← clockChar_sum, ← clockChar_sum]
    congr 1
    unfold clockDivergence
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [sum_edge_eq_sum_vertex src (fun v => ((k v : ℕ) : ℤ)) (fun e => ((m e : ℕ) : ℤ)),
      sum_edge_eq_sum_vertex tgt (fun v => ((k v : ℕ) : ℤ)) (fun e => ((m e : ℕ) : ℤ))]
  simp_rw [hrearr]
  rw [← Fintype.prod_sum (fun v (j : Fin N) => clockChar N ((j : ℕ) * clockDivergence src tgt m v))]
  exact Finset.prod_congr rfl fun v _ => sum_clockChar_mul hN _

omit [DecidableEq E] in
/-- `Ω(m)` is a nonnegative real number. -/
theorem clockCurrentCount_eq_ofReal {N : ℕ} (hN : 0 < N) (src tgt : E → V) (m : E → Fin N) :
    ∃ ω : ℝ, 0 ≤ ω ∧ clockCurrentCount N src tgt m = (ω : ℂ) := by
  classical
  refine ⟨∏ v, (if (N : ℤ) ∣ clockDivergence src tgt m v then (N : ℝ) else 0),
    Finset.prod_nonneg fun v _ => by split_ifs <;> positivity, ?_⟩
  rw [clockCurrentCount_eq hN]
  push_cast
  refine Finset.prod_congr rfl fun v _ => ?_
  split_ifs <;> simp

/-- **The current bound.** If the clock Fourier coefficients of `g_e` are real numbers `c_e` and
those of `f_e` satisfy `‖f̂_e‖ ≤ λ_e c_e`, then `‖Z(f)‖ ≤ (∏_e λ_e) Z(g)`. -/
theorem norm_clockEdgeSum_le {N : ℕ} (hN : 0 < N) (src tgt : E → V) (f g : E → ℝ → ℝ)
    (hfper : ∀ e, Function.Periodic (f e) (2 * Real.pi))
    (hgper : ∀ e, Function.Periodic (g e) (2 * Real.pi))
    (c : E → Fin N → ℝ) (hgc : ∀ e μ, clockAngleFourier N (g e) μ = c e μ)
    (lam : E → ℝ) (hf : ∀ e μ, ‖clockAngleFourier N (f e) μ‖ ≤ lam e * c e μ) :
    |clockEdgeSum N src tgt f| ≤ (∏ e, lam e) * clockEdgeSum N src tgt g := by
  classical
  choose ω hω0 hω using fun m : E → Fin N => clockCurrentCount_eq_ofReal hN src tgt m
  have hg : clockEdgeSum N src tgt g = ∑ m : E → Fin N, (∏ e, c e (m e)) * ω m := by
    have h := clockEdgeSum_eq_currents hN src tgt g hgper
    simp_rw [hgc, hω] at h
    exact_mod_cast h
  have hf' := clockEdgeSum_eq_currents hN src tgt f hfper
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hf', hg, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, hω, Complex.norm_real, Real.norm_of_nonneg (hω0 m), norm_prod, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod₀ (fun e _ => norm_nonneg _) fun e _ => hf e (m e)) (hω0 m)

end Current

end FroehlichSpencer.BKT.Clock.Disorder

end
