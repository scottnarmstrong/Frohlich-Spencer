/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Moment
public import FroehlichSpencer.BKT.SOS.Roughening.Theorem73

/-!
# FS81 Theorem 7.3 in FS81's literal state (7.16) (the finite comb construction)

FS81 §7.2, Theorem 7.3 and Remark 1 (FS81): in the state (7.16), the comb on a
finite region `A` inside the zero-mass `I_β`-field, for small `β`,

`⟨e^{ε[φ(0)−φ(x)]}⟩⁰_A ≥ e^{(ε²/β') ln(1+|x|)}` (7.17), `⟨[φ(0)−φ(x)]²⟩⁰_A ≥ (1/β') ln(1+|x|)` (7.18).

Here the zero-mass field is the finite-volume `dμ_{I_β,Ω}` on a box `Ω ⊇ A` with zero exterior, and
the state is the genuine probability measure `literalState L β A` (`Literal/State.lean`); the
moment is the extended (`ℝ≥0∞`) lintegral and the variance a Bochner integral of an integrable
function.

* `literal_theorem73`: there are `β₀ ∈ (0, 1]`, `β' → 0` and `L₀` such that for `0 < β ≤ β₀`, every
  box of side `L ≥ L₀`, **every** region `A ⊆ Ω` and all `u, v ∈ A`, (7.17) for `|ε| ≤ β/2` and
  (7.18) hold with `ℓ = log(1 + min(‖u − v‖_∞, depth_Ω(u)))`. The cap is the distance of `u` to
  the outside of `Ω`, not of `A`: the field off `A` is the continuous field of the whole box.
* `literal_theorem73_deep`: for `‖u − v‖_∞ ≤ depth_Ω(u)` (every large `Ω` around `A`) the bound is
  FS81's `log(1 + |x|)`, uniformly over `A` and `Ω`.

The constants are those of the Dirichlet-box theorem (`Roughening.sos_theorem73`): the comb layer on
`A` has the constants of the Appendix D layer (`exists_combOnWitness`), and the numbers are
`exists_sosNumbers`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site siteBoundaryDepth)
open FroehlichSpencer.BKT.SOS.Tilt
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

theorem heightField_neg (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ)
    (y : {x // x ∉ A} → ℝ) : heightField A (-n) (-y) = -heightField A n y := by
  funext x
  simp only [heightField, mergePi, Pi.neg_apply]
  split_ifs <;> simp

/-- The marginal weight is even. -/
theorem literalWeight_neg {β : ℝ} (hβ : 0 ≤ β) (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) :
    literalWeight L β A (-n) = literalWeight L β A n := by
  unfold literalWeight
  rw [← Generic.integral_comp_neg_pi (fun y => boxWeight L β (heightField A (-n) y))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [heightField_neg, boxWeight_neg hβ]

/-- **FS81 Theorem 7.3 in the literal state (7.16)**, for every region `A` of every large box. -/
theorem literal_theorem73 :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧ β₀ ≤ 1 ∧ 1 < L₀ ∧
      Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ L, L₀ ≤ L → ∀ (A : Finset (Site L)) (u v : Site L),
        u ∈ A → v ∈ A →
        (∀ ε : ℝ, |ε| ≤ β / 2 →
          ENNReal.ofReal (Real.exp (ε ^ 2 / β' β *
            Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)))) ≤
            literalMomentExt L β A u v ε) ∧
        Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) / β' β ≤
          literalVariance L β A u v := by
  obtain ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₁, hα, hK₀, hK₁, hD₁, hKv, hwit⟩ :=
    exists_combOnWitness
  obtain ⟨T₀, C₁, hT₀, hC₁lim, hnum⟩ := exists_sosNumbers (D₂ := D₂) (a₁ := a₁) (a₂ := a₂) Kov
    hα hK₀ hK₁ hD₁ hKv
  refine ⟨Real.exp (-T₀), fun β => 1024 * Real.pi ^ 2 * C₁ (-Real.log β), max L₁ 2,
    Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), lt_of_lt_of_le (by norm_num)
      (le_max_right _ _), ?_, fun β hβ hβ₀ => ?_⟩
  · have hlog : Tendsto (fun β : ℝ => -Real.log β) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    simpa using (hC₁lim.comp hlog).const_mul (1024 * Real.pi ^ 2)
  set T := -Real.log β with hTdef
  have hT : T₀ ≤ T := by
    have h := Real.log_le_log hβ hβ₀
    rw [Real.log_exp] at h
    linarith
  have hβT : Real.exp (-T) = β := by rw [hTdef, neg_neg, Real.exp_log hβ]
  have hβ1 : β ≤ 1 := hβ₀.trans (Real.exp_le_one_iff.mpr (by linarith))
  obtain ⟨hC₁pos, M, κc, amp, b, εp, εe, k₀, hlog', hcurv, hamp, hampW, hk₀, hexp, hquad₁, hquad₂,
    hM, hb8, hb₁, hb₂, hthr, hthrE, hC₁eq, hsmall⟩ := hnum T hT
  rw [hβT] at hlog' hcurv hampW hexp hquad₁
  have hπ : 0 < Real.pi := Real.pi_pos
  refine ⟨by positivity, fun L hL A u v hu hv => ?_⟩
  have hL1 : 1 < L := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hL)
  have hwitL := fun N hN => hwit L (le_trans (le_max_left _ _) hL) A N hN
  set ℓ := Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) with hℓdef
  have hR := log_le_dipoleResistance_squareZero hL1 u v
  rw [Nat.cast_add, Nat.cast_one, add_comm] at hR
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (min (linfDist u v) (siteBoundaryDepth u)); linarith)
  have hC : 0 < κc + 4 * εp := by rw [hC₁eq]; exact hC₁pos
  -- (7.17)
  have hmom : ∀ ε : ℝ, |ε| ≤ β / 2 →
      ENNReal.ofReal (Real.exp (ε ^ 2 / (1024 * Real.pi ^ 2 * C₁ T) * ℓ)) ≤
        literalMomentExt L β A u v ε := by
    intro ε hε
    have h := literalMoment_ge_of_layer hK₀ hK₁ hD₁ hKv hβ hβ1 hlog' hcurv hamp hampW hk₀ hexp
      hquad₁ hquad₂ hM hb8 hb₁ hb₂ hthr hthrE hC hL1 hwitL hu hv ε hε
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) h
    rw [hC₁eq]
    exact theorem73_exponent_le hC₁pos hR hℓ0 (by rw [← hC₁eq] at hsmall ⊢; exact hsmall)
  refine ⟨hmom, ?_⟩
  -- (7.18)
  have hZpos := tsum_literalWeight_pos hL1 hβ hβ1 A
  have key := le_tsum_sq_mul_of_exp_le (Equiv.neg ({x // x ∈ A} → ℤ))
    (X := fun n => (n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩) (w := literalWeight L β A)
    (fun n => by simp only [Equiv.neg_apply, Pi.neg_apply, Int.cast_neg]; ring)
    (fun n => literalWeight_neg hβ.le A n) (fun n => (literalWeight_pos hL1 hβ hβ1 A n).le)
    (δ := β / 2) (a := ℓ / (1024 * Real.pi ^ 2 * C₁ T)) (by positivity)
    (fun c hc => summable_exp_mul_literalWeight hL1 hβ hβ1 hu hv hc) (fun ε hε0 hεδ => by
      have h := hmom ε (by rw [abs_of_pos hε0]; exact hεδ)
      rw [literalMomentExt_eq hL1 hβ hβ1 hu hv (by rw [abs_of_pos hε0]; exact hεδ),
        ENNReal.ofReal_le_ofReal_iff (div_nonneg (tsum_nonneg fun n => mul_nonneg
          (Real.exp_pos _).le (literalWeight_pos hL1 hβ hβ1 A n).le) hZpos.le),
        le_div_iff₀ hZpos] at h
      have heq : ℓ / (1024 * Real.pi ^ 2 * C₁ T) * ε ^ 2 =
          ε ^ 2 / (1024 * Real.pi ^ 2 * C₁ T) * ℓ := by ring
      rw [heq]
      exact h)
  rw [literalVariance_eq hL1 hβ hβ1 hu hv, le_div_iff₀ hZpos]
  exact key

/-- **FS81 Theorem 7.3 in the literal state, at points away from the outside of `Ω`**: with
`|x| = ‖u − v‖_∞ ≤ depth_Ω(u)` the bounds carry FS81's `log(1 + |x|)`, uniformly over the region
`A ∋ u, v` and the box. -/
theorem literal_theorem73_deep :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧ β₀ ≤ 1 ∧ 1 < L₀ ∧
      Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ L, L₀ ≤ L → ∀ (A : Finset (Site L)) (u v : Site L),
        u ∈ A → v ∈ A → linfDist u v ≤ siteBoundaryDepth u →
        (∀ ε : ℝ, |ε| ≤ β / 2 →
          ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + (linfDist u v : ℝ)))) ≤
            literalMomentExt L β A u v ε) ∧
        Real.log (1 + (linfDist u v : ℝ)) / β' β ≤ literalVariance L β A u v := by
  obtain ⟨β₀, β', L₀, hβ₀, hβ₀1, hL₀, hlim, h⟩ := literal_theorem73
  refine ⟨β₀, β', L₀, hβ₀, hβ₀1, hL₀, hlim, fun β hβ hββ₀ =>
    ⟨(h β hβ hββ₀).1, fun L hL A u v hu hv huv => ?_⟩⟩
  have h' := (h β hβ hββ₀).2 L hL A u v hu hv
  rw [min_eq_left huv] at h'
  exact h'

end FroehlichSpencer.BKT.SOS.Literal

end
