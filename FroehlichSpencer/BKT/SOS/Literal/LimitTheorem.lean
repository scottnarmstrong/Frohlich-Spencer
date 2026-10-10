/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitPoints

/-!
# FS81 Theorem 7.3 as `Ω ↗ ℤ²` (the comb-inserted SOS construction)

FS81's state (7.16) is the comb on a finite `A` inside the vague limit `dμ_{I_β}` of the
zero-exterior measures as `Ω ↗ ℤ²` (FS81). The observables of (7.17)/(7.18) are the
differences `φ(0) − φ(x)`, `0, x ∈ A`.

`literal_theorem73_limit`: for `0 < β ≤ β₀`, every finite `A ⊂ ℤ²` and `w ∈ A`:

* **existence**: along every sequence of centred boxes `L_j → ∞` the laws `diffLaw β A w L_j` of the
  differences `d(z) = n(z) − n(w)` have a vague limit point (a subsequence converging pointwise
  on `ℤ^A`);
* **every limit point `ν`** is a probability measure. For all `v, v' ∈ A` it satisfies (7.17) for
  every `ε`, `⟨e^{ε[d(v)−d(v')]}⟩_ν ≥ e^{(ε²/(8β')) log(1+|v−v'|)}` in `[0, ∞]`, and (7.18),
  `⟨[d(v)−d(v')]²⟩_ν ≥ log(1+|v−v'|)/β'`, with a finite variance.

The input that makes lower bounds pass to the limit is the uniform exponential bound (*)
(`literal_exp_abs_plane`). Uniqueness of the limit is not claimed.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **FS81 Theorem 7.3 at every vague limit point as `Ω ↗ ℤ²`.** See the module docstring. -/
theorem literal_theorem73_limit :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), 0 < β₀ ∧ β₀ ≤ 1 ∧ Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ), w ∈ A →
        (∀ Ls : ℕ → ℕ, Tendsto Ls atTop atTop → ∃ (φs : ℕ → ℕ) (ν : Measure (DiffConfig A)),
          StrictMono φs ∧ ∀ d, Tendsto (fun j => diffLaw β A w (Ls (φs j)) {d}) atTop
            (𝓝 (ν {d}))) ∧
        ∀ (Ls : ℕ → ℕ) (ν : Measure (DiffConfig A)), Tendsto Ls atTop atTop →
          (∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d}))) →
          IsProbabilityMeasure ν ∧ ∀ (v v' : ℤ × ℤ) (hv : v ∈ A) (hv' : v' ∈ A),
            (∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε ^ 2 / (8 * β' β) *
                Real.log (1 + (planeLinf v v' : ℝ)))) ≤
              ∫⁻ d, ENNReal.ofReal (Real.exp (ε * ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ))) ∂ν) ∧
            ENNReal.ofReal (Real.log (1 + (planeLinf v v' : ℝ)) / β' β) ≤
              ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂ν ∧
            ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂ν < ⊤ := by
  obtain ⟨β₀, β', hβ₀, hβ₀1, hlim, h⟩ := literal_theorem73_plane
  refine ⟨β₀, β', hβ₀, hβ₀1, hlim, fun β hβ hββ₀ => ⟨(h β hβ hββ₀).1, fun A w hw =>
    ⟨fun Ls hLs => exists_limitPoint_diffLaw hβ (hββ₀.trans hβ₀1) A w hLs,
      fun Ls ν hLs hν => ?_⟩⟩⟩
  have hβ1 : β ≤ 1 := hββ₀.trans hβ₀1
  have hβ' : 0 < β' β := (h β hβ hββ₀).1
  have hprob := isProbabilityMeasure_limitPoint hβ hβ1 hw hLs hν
  refine ⟨hprob, fun v v' hv hv' => ?_⟩
  obtain ⟨L_A, hA⟩ := (h β hβ hββ₀).2 A v v' hv hv'
  set ℓ := Real.log (1 + (planeLinf v v' : ℝ)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (planeLinf v v'); linarith)
  set X : DiffConfig A → ℝ := fun d => ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) with hX
  have hev : ∀ᶠ j in atTop, L_A ≤ Ls j ∧ 1 ≤ Ls j := by
    filter_upwards [hLs.eventually_ge_atTop L_A, hLs.eventually_ge_atTop 1] with j h1 h2
    exact ⟨h1, h2⟩
  -- the window at the limit
  have hwin : ∀ ε : ℝ, |ε| ≤ β / 2 →
      ENNReal.ofReal (Real.exp (ℓ / β' β * ε ^ 2)) ≤ mgfExt ν X ε := by
    intro ε hε
    refine le_lintegral_exp_limitPoint hβ hβ1 hw hv hv' hLs hν hε ?_
    filter_upwards [hev] with j hj
    rw [lintegral_diffLaw_pair hβ.le hw hv hv' (Ls j)
      (F := fun t => ENNReal.ofReal (Real.exp (ε * t))) (ENNReal.measurable_ofReal.comp
        (by fun_prop))]
    have := (hA (Ls j) hj.1).1 ε hε
    rw [show ℓ / β' β * ε ^ 2 = ε ^ 2 / β' β * ℓ by ring]
    exact this
  refine ⟨fun ε => ?_, ?_, ?_⟩
  · -- (7.17) for every `ε`
    by_cases hvv : v = v'
    · subst hvv
      have hℓz : ℓ = 0 := by rw [hℓ]; simp [planeLinf]
      rw [hℓz, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
      have : ∀ d : DiffConfig A, ENNReal.ofReal (Real.exp
          (ε * ((d ⟨v, hv⟩ - d ⟨v, hv'⟩ : ℤ) : ℝ))) = 1 := fun d => by simp
      simp_rw [this, lintegral_const, measure_univ, one_mul, le_refl]
    · have h := le_mgfExt_of_window ν (X := X) (measurable_of_countable X)
        (div_nonneg hℓ0 hβ'.le) (by positivity : (0 : ℝ) < β / 2)
        (mgfExt_limitPoint_neg hβ.le hw hv hv' hν) hwin
        (fun ε hε => mgfExt_limitPoint_eq_top hβ.le hw hv hv' hvv hLs hν (by linarith)) ε
      rw [show ℓ / β' β / 8 * ε ^ 2 = ε ^ 2 / (8 * β' β) * ℓ by ring] at h
      exact h
  · -- (7.18)
    refine le_lintegral_sq_limitPoint hβ hβ1 hw hv hv' hLs hν ?_
    filter_upwards [hev] with j hj
    rw [lintegral_diffLaw_pair hβ.le hw hv hv' (Ls j)
      (F := fun t => ENNReal.ofReal (t ^ 2)) (ENNReal.measurable_ofReal.comp (by fun_prop)),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_literal_sq (by omega) hβ hβ1
        (centeredSite_mem hv) (centeredSite_mem hv')) (Eventually.of_forall fun φ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hA (Ls j) hj.1).2
  · -- a finite variance
    obtain ⟨C, CX, hC, hCX, -, hXb⟩ := eventually_diffLaw_bounds hβ hβ1 hw hLs hv hv'
    obtain ⟨B, hB⟩ := exists_sq_le_add (b := 3 * β / 4) (η := 1) (by positivity) one_pos
    refine (lintegral_le_of_tendsto_singleton hν _ (fun _ => ENNReal.ofReal_ne_top)
      (B := ENNReal.ofReal (max B 0) + ENNReal.ofReal CX) ?_).trans_lt
      (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
    filter_upwards [hXb, hLs.eventually_ge_atTop 1] with j hj hj1
    have hp := isProbabilityMeasure_diffLaw hβ hβ1 A w hj1
    calc ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂diffLaw β A w (Ls j)
        ≤ ∫⁻ d, (ENNReal.ofReal (max B 0) + ENNReal.ofReal (Real.exp
            (3 * β / 4 * |((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)|))) ∂diffLaw β A w (Ls j) := by
          refine lintegral_mono fun d => ?_
          rw [← ENNReal.ofReal_add (le_max_right _ _) (Real.exp_pos _).le]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := hB |((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)| (abs_nonneg _)
          rw [sq_abs, one_mul] at h1
          linarith [le_max_left B 0]
      _ ≤ ENNReal.ofReal (max B 0) + ENNReal.ofReal CX := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          exact add_le_add le_rfl hj

end FroehlichSpencer.BKT.SOS.Literal

end
