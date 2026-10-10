/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Domain
public import FroehlichSpencer.BKT.Coulomb.SineGordon
public import FroehlichSpencer.BKT.Charges.Theorem22
public import FroehlichSpencer.BKT.Charges.P21
public import FroehlichSpencer.BKT.SpinWaves.BoundaryShellPacking
public import FroehlichSpencer.BKT.SpinWaves.SquareGeometry
import FroehlichSpencer.BKT.Gaussian.ComplexCharacteristic
import Mathlib.Tactic

/-!
# FS81 Theorem B on the square domains

It follows from
the marked renormalization of `Generic/Marked/`  and the KP T2.2, P2.1 and
L4.6/P2.4.

* `markedThresholds`, **`markedSquareBound_exists`**: explicit constants.
  - `cB = 1/(16384 max(D₁, 1))`, with `D₁` the constant of KP P2.1.
  - For every activity bound `z̄` and `η > 0`, a threshold `β₁(z̄, η)` collects KP's damping
    threshold and the smallness conditions (H1)–(H4).

It is of order `η²`, so
    `κ₀ = 1/β₁ = O(η⁻²)`, as in FS81 (`β > O(η⁻²)`).
  - The marked bound `MarkedSquareBoundInternal` then holds on every free square and every even
    periodic square, uniformly in the side, the root and the weights.
* `integral_cos_neutral_gffLaw`, `integral_cos_mul_cos_charge_nonneg`,
  `integral_cos_mul_prod_sineGordonWeight_nonneg`: positivity `0 ≤ G_ξ`, from the charge
  expansion.
* `fracCorrInternal`: FS81 (1.22) in the sine-Gordon representation,
  `G_ξ(o, x) = ⟨cos(ξ(φ_o − φ_x))⟩`, for the hard-core weights `1 + z cos φ` on a charge region
  `A` at Coulomb inverse temperature `κ` (the GFF at `κ⁻¹`).
* **`coulombB_squares`**: there is an absolute `c = cB / log 2 > 0` such that for every `z ≥ 0`
  and `η > 0` there is `κ₀` with `0 ≤ G_ξ(o, x) ≤ 2 (|o − x| + 1)^{-c η² κ}`.

This holds for
  `κ > κ₀` and `min(ξ, 1 − ξ) ≥ η`, on every free square and every even periodic square.

**Reading of the source.**
- The threshold `κ₀ = O(η⁻²)` depends on `η` (FS81: `β > O(η⁻²)`, CG.s5).

No uniformity as
  `ξ → 0, 1` is claimed.
- The power law is stated with `|o − x| + 1`; it implies FS81's `|x|^{-β'}` for `|x| ≥ 1`.
- The activity `z = 0` needs no separate argument.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory FroehlichSpencer.BKT.Generic.Marked Reduction

/-! ### The thresholds -/

section Threshold

theorem exp_neg_four_le : Real.exp (-4) ≤ 1 / 32 := by
  have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have := Real.quadratic_le_exp_of_nonneg (zero_le_one' ℝ)
    norm_num at this ⊢
    linarith
  have h2 : (5 / 2 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he 4
  have h3 : (32 : ℝ) ≤ Real.exp 4 := by
    rw [h1]
    nlinarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 4) (by norm_num)]
  linarith

theorem exp_neg_twenty_le : Real.exp (-20) ≤ 1 / 2 ^ 25 := by
  have h4 : Real.exp (-4) ≤ 1 / 32 := exp_neg_four_le
  have h : Real.exp (-20) = Real.exp (-4) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  calc Real.exp (-4) ^ 5 ≤ (1 / 32) ^ 5 := pow_le_pow_left₀ (Real.exp_pos _).le h4 5
    _ = 1 / 2 ^ 25 := by norm_num

/-- The smallness conditions (H1)–(H4) of `markedDomain_bound` from explicit thresholds on `c`
and `β`, all of order `η²`: `c ≤ η²/(2·289·16384 D₁)`, `β ≤ η²/(64 (h + 1))`,
`β ≤ η²/(2·16384·289 D₁ max(D₂, 1))` and `β ≤ c/20`. -/
theorem markedThresholds {D₁ D₂ h c β η : ℝ} (hD₁ : 1 ≤ D₁) (hh : 0 ≤ h)
    (hη : 0 < η) (hc : 0 < c) (hcη : c ≤ η ^ 2 / (2 * 289 * 16384 * D₁)) (hβ : 0 < β)
    (hb1 : β ≤ η ^ 2 / (64 * (h + 1))) (hb2 : β ≤ η ^ 2 / (2 * 16384 * 289 * D₁ * max D₂ 1))
    (hb3 : β ≤ c / 20) :
    β * (h + 1) + c ≤ η ^ 2 / 32 ∧
      4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ η ^ 2 / (64 * β) ∧
      289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁) ∧
      Real.exp (-(c / β)) ≤ 1 / 32 := by
  have hD₁pos : 0 < D₁ := by linarith
  have hη2 : 0 < η ^ 2 := by positivity
  have hcb : 20 ≤ c / β := by rw [le_div_iff₀ hβ]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : β * (h + 1) ≤ η ^ 2 / 64 := by
      rw [le_div_iff₀ (by positivity)] at hb1
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have h2 : c ≤ η ^ 2 / 64 := by
      refine hcη.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  · have hexp : Real.exp (-(c / β)) ≤ 1 / 2 ^ 25 :=
      (Real.exp_le_exp.2 (by linarith)).trans exp_neg_twenty_le
    have hM : (chargeCoverScale : ℝ) ^ 2 = 2 ^ 32 := by norm_num [chargeCoverScale]
    have hL : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ 147456 := by
      rw [hM]
      have := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 4 * 288 * 2 ^ 32)
      norm_num at this ⊢
      linarith
    refine hL.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have hcη' : c * (2 * 289 * 16384 * D₁) ≤ η ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hcη
    have hβc : 20 * β ≤ c := by linarith
    nlinarith
  · have hmax : D₂ ≤ max D₂ 1 := le_max_left _ _
    have hmax1 : 0 < max D₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h1 : 289 * D₂ * β ≤ η ^ 2 / (2 * 16384 * D₁) := by
      rw [le_div_iff₀ (by positivity)] at hb2
      rw [le_div_iff₀ (by positivity)]
      have : D₂ * β ≤ max D₂ 1 * β := mul_le_mul_of_nonneg_right hmax hβ.le
      nlinarith
    have h2 : 289 * c ≤ η ^ 2 / (2 * 16384 * D₁) := by
      rw [le_div_iff₀ (by positivity)] at hcη
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h3 : η ^ 2 / (2 * 16384 * D₁) + η ^ 2 / (2 * 16384 * D₁) = η ^ 2 / (16384 * D₁) := by
      field_simp
      ring
    linarith
  · refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_four_le
    linarith

end Threshold

/-! ### FS81 Theorem B on the square domains -/

section Squares

/-- **FS81 Theorem B on one square domain** with constant `cB` and threshold `β₁` (KP inverse
temperature `β = κ⁻¹ < β₁`): for hard-core weights `1 + 2z_j cos φ_j`, `|z_j| ≤ z̄`, the dipole
mark at `o ≠ x` and `η ≤ min(ξ, 1 − ξ)`, the normalizer is positive and
`|∫ cos(ξ(φ_o − φ_x)) ∏ (1 + 2z_j cos φ_j) dμ| ≤ 2 e^{-(cB η²/β) log₂(|o − x| + 1)} 𝒵`. -/
def MarkedSquareBoundInternal (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected) (cB zbar η β₁ : ℝ) :
    Prop :=
  ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₁ → ∀ zs : Fin L × Fin L → ℝ,
    (∀ j, |zs j| ≤ zbar) → ∀ o x : Fin L × Fin L, o ≠ x → ∀ ξ : ℝ, 0 < ξ → ξ < 1 →
      η ≤ dipoleGap ξ →
      0 < ∫ φ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂gffLaw Λ hΛ β hβ v ∧
      |∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, (1 + 2 * zs j * Real.cos (φ j))
          ∂gffLaw Λ hΛ β hβ v| ≤
        2 * Real.exp (-(cB * η ^ 2 / β) * Real.logb 2 (latticeDistance boundary L o x + 1)) *
          ∫ φ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂gffLaw Λ hΛ β hβ v

/--
**FS81 Theorem B on the square domains** (hard-core gas, unit dipole marks).

There is an
absolute constant `cB > 0` such that for every activity bound `z̄ ≥ 0` and every `η > 0` there is
a threshold `β₁ > 0` with `MarkedSquareBoundInternal` on every free square and every even periodic
square.

The constants come from the KP T2.2, P2.1 and L4.6 (via P2.4):
`cB = 1/(16384 max(D₁, 1))`, and `β₁` collects KP's damping threshold and (H1)–(H4).
-/
theorem markedSquareBound_exists :
    ∃ cB : ℝ, 0 < cB ∧ ∀ zbar : ℝ, 0 ≤ zbar → ∀ η : ℝ, 0 < η → ∃ β₁ : ℝ, 0 < β₁ ∧
      ∀ L : ℕ, ∀ hL : 1 < L,
        MarkedSquareBoundInternal .free (squareFree L) (squareFree_connected L hL) cB zbar η β₁ ∧
        (Even L → MarkedSquareBoundInternal .periodic (squarePeriodic L)
          (squarePeriodic_connected L hL) cB zbar η β₁) := by
  obtain ⟨D₂, hD₂, h22⟩ := t22Statement_of_repairedBasicLemma
  obtain ⟨D₃, hD₃, h24⟩ := p24_of_l46 SpinWaves.BoundaryShellPacking.l46Statement_holds
  obtain ⟨D₁, hD₁, h21⟩ := kp_p21Statement
  obtain ⟨D₁', hD₁'⟩ : ∃ D₁' : ℝ, D₁' = max D₁ 1 := ⟨_, rfl⟩
  have hD₁'1 : 1 ≤ D₁' := hD₁' ▸ le_max_right _ _
  have hmono : ∀ {boundary : SquareBoundary} {L : ℕ}, P21Step boundary L D₁ →
      P21Step boundary L D₁' := by
    intro boundary L h cover ϱ hϱ
    obtain ⟨h1, h2⟩ := h cover ϱ hϱ
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (hD₁' ▸ le_max_left _ _) ?_)⟩
    positivity
  refine ⟨1 / (16384 * D₁'), by positivity, fun zbar hzbar η hη => ?_⟩
  obtain ⟨β₀, c₁, hβ₀, hc₁, hdamp⟩ := exists_damping_constants zbar 0 0 D₁' D₂ D₃
    (by norm_num) (by linarith) hD₂ hD₃
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = Real.log (max 1 zbar) + 1 + 0 := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := by
    rw [hh]
    have := Real.log_nonneg (le_max_left 1 zbar)
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min c₁ (η ^ 2 / (2 * 289 * 16384 * D₁')) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact lt_min hc₁ (by positivity)
  have hcc₁ : c ≤ c₁ := hc ▸ min_le_left _ _
  have hcη : c ≤ η ^ 2 / (2 * 289 * 16384 * D₁') := hc ▸ min_le_right _ _
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : ℝ, β₁ = min β₀ (min (η ^ 2 / (64 * (h + 1)))
      (min (η ^ 2 / (2 * 16384 * 289 * D₁' * max D₂ 1)) (c / 20))) := ⟨_, rfl⟩
  have hmaxD₂ : 0 < max D₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hβ₁pos : 0 < β₁ := by
    rw [hβ₁]
    exact lt_min hβ₀ (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hH : ∀ β : ℝ, 0 < β → β < β₁ → β < β₀ ∧
      β * (Real.log (max 1 zbar) + 1 + 0 + 1) + c ≤ η ^ 2 / 32 ∧
      4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ η ^ 2 / (64 * β) ∧
      289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁') ∧
      Real.exp (-(c / β)) ≤ 1 / 32 := by
    intro β hβ hββ₁
    rw [hβ₁] at hββ₁
    have k0 := hββ₁.trans_le (min_le_left _ _)
    have k1 := hββ₁.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have k2 := hββ₁.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
    have k3 := hββ₁.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
    obtain ⟨H1, H2, H3, H4⟩ := markedThresholds hD₁'1 hh0 hη hcpos hcη hβ k1 k2 k3
    rw [hh] at H1
    exact ⟨k0, H1, H2, H3, H4⟩
  have hexpo : ∀ β : ℝ, η ^ 2 / (16384 * D₁' * β) = 1 / (16384 * D₁') * η ^ 2 / β := by
    intro β
    rw [div_mul_eq_mul_div, one_mul, div_div]
  refine ⟨β₁, hβ₁pos, fun L hL => ⟨?_, fun hE => ?_⟩⟩
  · intro v β hβ hββ₁ zs hzs o x hox ξ hξ0 hξ1 hηξ
    obtain ⟨hββ₀, H1, H2, H3, H4⟩ := hH β hβ hββ₁
    have hb := markedDomain_bound hL (squareFree L) (squareFree_connected L hL) (fun _ _ => rfl)
      (SpinWaves.squareFreeBipartiteDegreeFour L hL)
      (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).1 hD₁'1 hD₂.le (h22 L hL).1
      (hmono (h21 L hL).1) (h24 L hL).1 hzbar hdamp hη hcpos hcc₁ hβ hββ₀ H1 H2 H3 H4 v zs hzs
      hox hξ0 hξ1 hηξ
    rw [hexpo] at hb
    exact hb
  · intro v β hβ hββ₁ zs hzs o x hox ξ hξ0 hξ1 hηξ
    obtain ⟨hββ₀, H1, H2, H3, H4⟩ := hH β hβ hββ₁
    have hb := markedDomain_bound hL (squarePeriodic L) (squarePeriodic_connected L hL)
      (fun _ _ => rfl) (SpinWaves.squarePeriodicBipartiteDegreeFour L hE hL)
      ((SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).2 hE) hD₁'1 hD₂.le
      ((h22 L hL).2 hE) (hmono ((h21 L hL).2 hE)) ((h24 L hL).2 hE) hzbar hdamp hη hcpos hcc₁
      hβ hββ₀ H1 H2 H3 H4 v zs hzs hox hξ0 hξ1 hηξ
    rw [hexpo] at hb
    exact hb

end Squares

/-! ### Positivity of the fractional correlation -/

section Positivity

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

/-- The Gaussian characteristic function of a real neutral density:
`∫ cos⟨φ, τ⟩ dμ = e^{-⟨τ, C τ⟩/(2β)}`. -/
theorem integral_cos_neutral_gffLaw (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (β : ℝ) (hβ : 0 < β) (v : V) (τ : V → ℝ) (hτ : ∑ j, τ j = 0) :
    ∫ φ, Real.cos (∑ j, φ j * τ j) ∂gffLaw G hG β hβ v =
      Real.exp (-(Multigraph.pairing τ (-G.greenOp hG τ)) / (2 * β)) := by
  have hchar := gff_characteristic_function G hG β hβ v τ hτ
  rw [← gffLaw_eq_gffMeasure] at hchar
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  have hint : Integrable (fun φ : V → ℝ => Complex.exp (Complex.I *
      ((Multigraph.pairing φ τ : ℝ) : ℂ))) (gffLaw G hG β hβ v) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) 1
      (ae_of_all _ fun φ => ?_)
    · unfold Multigraph.pairing
      fun_prop
    · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hpt : ∀ φ : V → ℝ, Real.cos (∑ j, φ j * τ j) =
      RCLike.re (Complex.exp (Complex.I * ((Multigraph.pairing φ τ : ℝ) : ℂ))) := by
    intro φ
    rw [mul_comm Complex.I, RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re]
    rfl
  simp_rw [hpt]
  rw [integral_re hint, hchar]
  set Q := Multigraph.pairing τ (-(G.greenOp hG) τ)
  have hcast : Complex.exp (-(Q : ℂ) / (2 * (β : ℂ))) = ((Real.exp (-Q / (2 * β)) : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [hcast, RCLike.re_to_complex, Complex.ofReal_re]

/-- `∫ cos(ξ⟨φ, f⟩) cos⟨φ, q⟩ dμ ≥ 0` for a real neutral `f` and an integer `q`: half the sum of the
characteristic functions of `q ± ξf`, which vanish when `q` is charged. -/
theorem integral_cos_mul_cos_charge_nonneg (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (f : V → ℝ)
    (hf : ∑ j, f j = 0) (ξ : ℝ) (q : V → ℤ) :
    0 ≤ ∫ φ, Real.cos (ξ * ∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ))
      ∂gffLaw G hG β hβ v := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  have hpt : ∀ φ : V → ℝ, Real.cos (ξ * ∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ)) =
      (Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * (ξ * f j)) +
        Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * (-(ξ * f j)))) / 2 := by
    intro φ
    have e1 : ∑ j, φ j * (ξ * f j) = ξ * ∑ j, φ j * f j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, φ j * (-(ξ * f j)) = -(ξ * ∑ j, φ j * f j) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2, ← sub_eq_add_neg, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hpt]
  have hτ1 : ∑ j, ξ * f j = 0 := by rw [← Finset.mul_sum, hf, mul_zero]
  have hτ2 : ∑ j, -(ξ * f j) = 0 := by rw [Finset.sum_neg_distrib, hτ1, neg_zero]
  have hint : ∀ τ : V → ℝ, Integrable (fun φ : V → ℝ =>
      Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * τ j)) (gffLaw G hG β hβ v) := fun τ =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [integral_div, integral_add (hint _) (hint _)]
  refine div_nonneg ?_ (by norm_num)
  by_cases hq : ∑ j, q j = 0
  · have hqR : ∑ j, (q j : ℝ) = 0 := by exact_mod_cast hq
    have hval : ∀ τ : V → ℝ, ∑ j, τ j = 0 →
        0 ≤ ∫ φ, Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * τ j) ∂gffLaw G hG β hβ v := by
      intro τ hτ
      have hcomb : ∀ φ : V → ℝ, ∑ j, φ j * (q j : ℝ) + ∑ j, φ j * τ j =
          ∑ j, φ j * ((q j : ℝ) + τ j) := fun φ => by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hcomb]
      rw [integral_cos_neutral_gffLaw G hG β hβ v _ (by rw [Finset.sum_add_distrib, hqR, hτ,
        add_zero])]
      exact (Real.exp_pos _).le
    exact add_nonneg (hval _ hτ1) (hval _ hτ2)
  · have hzero : ∀ τ : V → ℝ, ∑ j, τ j = 0 →
        ∫ φ, Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * τ j) ∂gffLaw G hG β hβ v = 0 := by
      intro τ hτ
      have h := gffLaw_integral_cos_charged_mul_eq_zero G hG β hβ v q hq τ hτ (fun _ => 1)
        (fun _ _ => rfl) continuous_const 1 (fun _ => by simp)
      simpa using h
    rw [hzero _ hτ1, hzero _ hτ2, add_zero]

/-- **Positivity of the fractional correlation** (FS81 Theorem B, `0 ≤ G_ξ`): for even
nonnegative charge weights, `∫ cos(ξ⟨φ, f⟩) ∏_j λ̂_j(φ_j) dμ ≥ 0` for every real neutral `f`
(the charge expansion `prod_sineGordonWeight_eq_sum`). -/
theorem integral_cos_mul_prod_sineGordonWeight_nonneg (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n) (hlam0 : ∀ j n, 0 ≤ lam j n)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (ξ : ℝ) :
    0 ≤ ∫ φ, Real.cos (ξ * ∑ j, φ j * f j) * ∏ j, sineGordonWeightInternal N (lam j) (φ j)
      ∂gffLaw G hG β hβ v := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  have hexp : ∀ φ : V → ℝ, Real.cos (ξ * ∑ j, φ j * f j) *
      ∏ j, sineGordonWeightInternal N (lam j) (φ j) =
      ∑ q ∈ chargeConfigsInternal V N, Real.cos (ξ * ∑ j, φ j * f j) *
        ((∏ j, lam j (q j)) * Real.cos (∑ j, φ j * (q j : ℝ))) := fun φ => by
    rw [prod_sineGordonWeight_eq_sum N lam hlam, Finset.mul_sum]
  rw [integral_congr_ae (ae_of_all _ hexp)]
  have hint : ∀ q : V → ℤ, Integrable (fun φ : V → ℝ => Real.cos (ξ * ∑ j, φ j * f j) *
      ((∏ j, lam j (q j)) * Real.cos (∑ j, φ j * (q j : ℝ)))) (gffLaw G hG β hβ v) := fun q =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) |∏ j, lam j (q j)|
      (ae_of_all _ fun φ => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        calc |Real.cos (ξ * ∑ j, φ j * f j)| * (|∏ j, lam j (q j)| *
              |Real.cos (∑ j, φ j * (q j : ℝ))|)
            ≤ 1 * (|∏ j, lam j (q j)| * 1) := by
              gcongr
              · exact Real.abs_cos_le_one _
              · exact Real.abs_cos_le_one _
          _ = |∏ j, lam j (q j)| := by ring)
  rw [integral_finsetSum _ fun q _ => hint q]
  refine Finset.sum_nonneg fun q _ => ?_
  have hpt : ∀ φ : V → ℝ, Real.cos (ξ * ∑ j, φ j * f j) *
      ((∏ j, lam j (q j)) * Real.cos (∑ j, φ j * (q j : ℝ))) = (∏ j, lam j (q j)) *
        (Real.cos (ξ * ∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ))) := fun φ => by ring
  simp_rw [hpt]
  rw [integral_const_mul]
  exact mul_nonneg (Finset.prod_nonneg fun j _ => hlam0 j _)
    (integral_cos_mul_cos_charge_nonneg G hG β hβ v f hf ξ q)

end Positivity

/-! ### FS81 Theorem B in the sine-Gordon representation on the squares -/

section SineGordon

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- FS81 (1.22) in the sine-Gordon representation (FS81 §5.1), in cosine form: the
fractional-charge correlation `G_ξ(o, x) = ⟨cos(ξ(φ_o − φ_x))⟩` of the hard-core gas with charges
in `A`, at Coulomb inverse temperature `κ` (the Gaussian field at KP inverse temperature `κ⁻¹`).
The sine part of `⟨e^{iξ(φ_o − φ_x)}⟩` vanishes by `φ ↦ −φ`; it is not used here. -/
def fracCorrInternal {E : Type*} [Fintype E] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ)
    (hκ : 0 < κ) (v : V) (A : Finset V) (z ξ : ℝ) (o x : V) : ℝ :=
  weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v (hardCoreSineGordonInternal A z)
    (fun φ => Real.cos (ξ * (φ o - φ x)))

omit [Fintype V] in
/-- The hard-core region weights are `1 + 2 z_j cos φ` with `z_j = z/2` on `A`, zero off `A`. -/
theorem hardCoreSineGordon_eq (A : Finset V) (z : ℝ) (j : V) (φ : ℝ) :
    hardCoreSineGordonInternal A z j φ = 1 + 2 * (if j ∈ A then z / 2 else 0) * Real.cos φ := by
  rw [sineGordonWeight_regionHardCore]
  split_ifs <;> ring

omit [Fintype V] in
theorem regionHardCoreWeight_nonneg (A : Finset V) {z : ℝ} (hz : 0 ≤ z) (j : V) (n : ℤ) :
    0 ≤ regionWeightInternal A (hardCoreWeightInternal z) j n := by
  unfold regionWeightInternal hardCoreWeightInternal
  split_ifs <;> positivity

/-- **Theorem B on one domain from the marked bound**: `0 ≤ G_ξ(o, x)` for `z ≥ 0`, and
`G_ξ(o, x) ≤ 2 (|o − x| + 1)^{-(cB/log 2) η² κ}` when `κ⁻¹` is below the threshold of the marked
bound with activity bound `z/2`. -/
theorem fracCorr_le_of_markedSquareBound (boundary : SquareBoundary) {L : ℕ} {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected) {cB z η β₁ : ℝ}
    (hz : 0 ≤ z) (hB : MarkedSquareBoundInternal boundary Λ hΛ cB (z / 2) η β₁) {κ : ℝ} (hκ : 0 < κ)
    (hκβ : κ⁻¹ < β₁) (v : Fin L × Fin L) (A : Finset (Fin L × Fin L)) {o x : Fin L × Fin L}
    (hox : o ≠ x) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hηξ : η ≤ dipoleGap ξ) :
    0 ≤ fracCorrInternal Λ hΛ κ hκ v A z ξ o x ∧
      fracCorrInternal Λ hΛ κ hκ v A z ξ o x ≤
        2 * ((latticeDistance boundary L o x : ℝ) + 1) ^ (-(cB / Real.log 2 * η ^ 2 * κ)) := by
  set zs : Fin L × Fin L → ℝ := fun j => if j ∈ A then z / 2 else 0 with hzs
  have hzsb : ∀ j, |zs j| ≤ z / 2 := fun j => by
    simp only [hzs]
    split_ifs
    · rw [abs_of_nonneg (by linarith)]
    · simp; linarith
  obtain ⟨hZ, hI⟩ := hB v κ⁻¹ (inv_pos.2 hκ) hκβ zs hzsb o x hox ξ hξ0 hξ1 hηξ
  have hw : ∀ φ : Fin L × Fin L → ℝ, ∏ j, hardCoreSineGordonInternal A z j (φ j) =
      ∏ j, (1 + 2 * zs j * Real.cos (φ j)) := fun φ =>
    Finset.prod_congr rfl fun j _ => hardCoreSineGordon_eq A z j (φ j)
  have hnorm : weightedGFFNormalizer Λ hΛ κ⁻¹ (inv_pos.2 hκ) v (hardCoreSineGordonInternal A z) =
      ∫ φ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v := by
    unfold weightedGFFNormalizer
    simp_rw [hw]
  have hnum : ∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, hardCoreSineGordonInternal A z j (φ j)
      ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v =
      ∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, (1 + 2 * zs j * Real.cos (φ j))
        ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v := by
    simp_rw [hw]
  have hG : fracCorrInternal Λ hΛ κ hκ v A z ξ o x =
      (∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, (1 + 2 * zs j * Real.cos (φ j))
        ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v) /
      ∫ φ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v := by
    unfold fracCorrInternal weightedGFFExpectation
    rw [hnorm, hnum]
  -- positivity of the numerator
  have hpos : 0 ≤ ∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, hardCoreSineGordonInternal A z j (φ j)
      ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v := by
    have h := integral_cos_mul_prod_sineGordonWeight_nonneg Λ hΛ κ⁻¹ (inv_pos.2 hκ) v 1
      (fun j => regionWeightInternal A (hardCoreWeightInternal z) j)
      (fun j n => regionWeight_neg A (hardCoreWeight_neg z) j n)
      (fun j n => regionHardCoreWeight_nonneg A hz j n) (fun j => (dipoleMark o x j : ℝ))
      (by exact_mod_cast sum_univ_dipoleMark o x) ξ
    simp_rw [sum_mul_dipoleMark] at h
    exact h
  rw [hnum] at hpos
  rw [hG]
  refine ⟨div_nonneg hpos hZ.le, ?_⟩
  rw [div_le_iff₀ hZ]
  refine (le_abs_self _).trans (hI.trans (le_of_eq ?_))
  congr 2
  have hd : (0 : ℝ) < (latticeDistance boundary L o x : ℝ) + 1 := by positivity
  rw [Real.rpow_def_of_pos hd, Real.logb, div_inv_eq_mul]
  congr 1
  ring

/-- The bound of FS81 Theorem B on one square domain, in the sine-Gordon form. -/
def FracCorrSquareBoundInternal (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected) (c z η κ₀ : ℝ) :
    Prop :=
  ∀ (κ : ℝ) (hκ : 0 < κ), κ₀ < κ → ∀ (v : Fin L × Fin L) (A : Finset (Fin L × Fin L))
    (o x : Fin L × Fin L), o ≠ x → ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
      0 ≤ fracCorrInternal Λ hΛ κ hκ v A z ξ o x ∧
        fracCorrInternal Λ hΛ κ hκ v A z ξ o x ≤
          2 * ((latticeDistance boundary L o x : ℝ) + 1) ^ (-(c * η ^ 2 * κ))

/-- **FS81 Theorem B on the square domains** (hard-core gas, unit dipole marks, sine-Gordon
form). There is an absolute `c > 0` such that for every activity `z ≥ 0` and every `η > 0` there
is `κ₀` with: for `κ > κ₀`, every free square and every even periodic square, every charge
region `A`, root `v`, `o ≠ x` and `ξ` with `min(ξ, 1 − ξ) ≥ η`,
`0 ≤ G_ξ(o, x) ≤ 2 (|o − x| + 1)^{-c η² κ}`. -/
theorem coulombB_squares :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, 0 ≤ z → ∀ η : ℝ, 0 < η → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ L : ℕ, ∀ hL : 1 < L,
        FracCorrSquareBoundInternal .free (squareFree L) (squareFree_connected L hL) c z η κ₀ ∧
        (Even L → FracCorrSquareBoundInternal .periodic (squarePeriodic L)
          (squarePeriodic_connected L hL) c z η κ₀) := by
  obtain ⟨cB, hcB, hB⟩ := markedSquareBound_exists
  refine ⟨cB / Real.log 2, div_pos hcB (Real.log_pos (by norm_num)), fun z hz η hη => ?_⟩
  obtain ⟨β₁, hβ₁, hB'⟩ := hB (z / 2) (by linarith) η hη
  refine ⟨1 / β₁, by positivity, fun L hL => ⟨?_, fun hE => ?_⟩⟩
  · intro κ hκ hκ₀ v A o x hox ξ hξ0 hξ1 hηξ
    have hκβ : κ⁻¹ < β₁ := by
      rw [inv_lt_comm₀ hκ hβ₁, ← one_div]
      exact hκ₀
    exact fracCorr_le_of_markedSquareBound .free _ _ hz (hB' L hL).1 hκ hκβ v A hox hξ0 hξ1 hηξ
  · intro κ hκ hκ₀ v A o x hox ξ hξ0 hξ1 hηξ
    have hκβ : κ⁻¹ < β₁ := by
      rw [inv_lt_comm₀ hκ hβ₁, ← one_div]
      exact hκ₀
    exact fracCorr_le_of_markedSquareBound .periodic _ _ hz ((hB' L hL).2 hE) hκ hκβ v A hox
      hξ0 hξ1 hηξ

end SineGordon

end FroehlichSpencer.BKT.Coulomb
