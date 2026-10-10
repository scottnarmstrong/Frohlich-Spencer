/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Moment
public import FroehlichSpencer.BKT.SOS.Tilt.Endpoint
public import FroehlichSpencer.BKT.SOS.Tilt.Potential

/-!
# The tilted ratio bound along the dipole potential (the dipole tilt construction: FS81 (7.20)–(7.40), generic form)

For a rooted charge layer, the tilted moment bound (`integral_tilt_ge_of_rootedLayerD`) at the edge
field `θ = ∇σ` becomes, after the translation `φ ↦ φ − σ` (`integral_tiltDensity_grad_shift`), a
lower bound on the tilted rooted integral by the untilted one:

`exp(⟨∇σ, b⟩ − κ‖∇σ‖² − 2ε ∑_e ([∇σ]²_{2π} + (∇σ)²) − 16Λ) ∫ ρ₀ O ≤ ∫ e^{⟨∇φ, b⟩} ρ₀ O`

(`integral_tilt_ratio_ge`). Along the dipole potential `g` of two vertices `p, q`
(`dipolePotential`), with the tilt `b = τ∇g` (so `⟨∇φ, b⟩ = τ(φ(p) − φ(q))`), the shift
`σ = s(g − g(root))` of FS81 (7.22) and the packed endpoint sum (`sum_abs_mul_tiltExponent_sq_le`),
the optimal `s = τ/(2C₁)` gives (`integral_tilt_dipole_ge`)

`exp(τ² R(p, q) (1/(4C₁) − 16 ε_end)) ∫ ρ₀ O ≤ ∫ e^{τ(φ(p) − φ(q))} ρ₀ O`,

with `C₁ = κ + 4ε`, `R(p, q)` the effective resistance and `ε_end` the endpoint threshold. This is
FS81's (7.17) in generic form, with prefactor one; (★) is the requirement `C₁ ε_end → 0`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open MeasureTheory Finset
open FroehlichSpencer.BKT.Generic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
  {G : Multigraph V E} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

omit [DecidableEq V] in
/-- **The translation by a rooted shift**: `φ ↦ φ − σ` with `σ(v) = 0` removes the edge offset
`∇σ` and the shift of the root-relative observable, at the price `e^{−⟨∇σ, b⟩}` of the tilt. -/
theorem integral_tiltDensity_grad_shift (G : Multigraph V E) (w : ℂ → ℂ) (bt : E → ℝ) (v : V)
    (lam : V → ℝ → ℝ) (σ : V → ℝ) (hσ : σ v = 0) :
    ∫ φ, tiltDensity G w (fun e => G.grad σ e) bt v φ * ∏ j, lam j (φ j + σ j - (φ v + σ v)) =
      Real.exp (-tiltExponent (gradLinear G) bt σ) *
        ∫ φ, tiltDensity G w 0 bt v φ * ∏ j, lam j (φ j - φ v) := by
  rw [← integral_sub_right_eq_self _ σ, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  have hprod : ∏ j, lam j ((φ - σ) j + σ j - ((φ - σ) v + σ v)) = ∏ j, lam j (φ j - φ v) :=
    Finset.prod_congr rfl fun j _ => by simp only [Pi.sub_apply, sub_add_cancel]
  have htilt : tiltExponent (gradLinear G) bt (φ - σ) =
      tiltExponent (gradLinear G) bt φ - tiltExponent (gradLinear G) bt σ := by
    rw [sub_eq_add_neg, tiltExponent_add, tiltExponent_neg, ← sub_eq_add_neg]
  have hgrad : ∀ e, G.grad (φ - σ) e + G.grad σ e = G.grad φ e + (0 : E → ℝ) e := fun e => by
    simp only [Multigraph.grad, Pi.sub_apply, Pi.zero_apply]
    ring
  simp only [hprod]
  unfold tiltDensity offsetEdgeDensity
  simp only [hgrad, htilt, Pi.sub_apply, hσ, sub_zero, Real.exp_sub]
  rw [Real.exp_neg]
  field_simp

/-- **The tilted ratio bound for a rooted charge layer.** For every rooted shift `σ`, the
untilted rooted integral times `exp(⟨∇σ, b⟩ − loss)` is at most the tilted one. -/
theorem integral_tilt_ratio_ge (hG : G.toSimpleGraph.Connected) (v : V)
    (CL : RootedChargeLayerD G v lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {dsc : (V → ℤ) → ℕ} {Kv : ℝ} {Kov : ℕ} (hloc : CL.IsLocal dsc Kv Kov) (hKv : 0 ≤ Kv)
    (hw : IsStripWeight w W c) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) {M : ℝ → ℝ}
    (hlog : HasLogDerivBounds w W M) {κc : ℝ} (hcurv : HasCurvatureBound w κc)
    {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hM : ∀ u : ℝ, |u| ≤ max (amp * K₁) 1 → M u ≤ m)
    {a₁ a₂ b : ℝ} (hZ : ∀ ϱ : V → ℤ, Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    {ε : ℝ} (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    {η K : ℝ} (hη : 0 < η) (hwexp : HasExpMajorant w W η K) (bt : E → ℝ)
    (hbt : ∀ e, |bt e| ≤ η / 2) {Λ : ℝ}
    (hΛ : ∀ i, ∑ ϱ ∈ CL.N i, |rootedActivityD CL c κ amp k₀ i ϱ| *
      tiltExponent (gradLinear G) bt (rootedSpinWaveD CL κ amp k₀ i ϱ) ^ 2 ≤ Λ)
    (σ : V → ℝ) (hσ : σ v = 0) :
    Real.exp (tiltExponent (gradLinear G) bt σ - κc * ∑ e, G.grad σ e ^ 2 -
        2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + G.grad σ e ^ 2) -
        16 * Λ) *
        ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) ≤
      ∫ φ, tiltDensity G w 0 bt v φ * ∏ j, lam j (φ j - φ v) := by
  have h := integral_tilt_ge_of_rootedLayerD hG v CL hloc hKv hw hnzero hlog hcurv hc hκ hK₀ hK₁
    hD₁ hamp hampW hW1 hk₀ hexp hquad₁ hquad₂ hm0 hm1 hM hZ hb8 hb₁ hb₂ hthr hη hwexp bt hbt hΛ σ
    (fun e => G.grad σ e)
  rw [integral_tiltDensity_grad_shift G w bt v lam σ hσ] at h
  set T := tiltExponent (gradLinear G) bt σ
  set X := κc * ∑ e, G.grad σ e ^ 2 +
    2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + G.grad σ e ^ 2) +
    16 * Λ with hX
  have hL : Real.exp (T - κc * ∑ e, G.grad σ e ^ 2 -
      2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + G.grad σ e ^ 2) -
      16 * Λ) = Real.exp T * Real.exp (-X) := by
    rw [← Real.exp_add]; congr 1; rw [hX]; ring
  have hR : Real.exp (-(κc * ∑ e, G.grad σ e ^ 2) -
      2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + G.grad σ e ^ 2) -
      16 * Λ) = Real.exp (-X) := by
    congr 1; rw [hX]; ring
  rw [hR] at h
  rw [hL, mul_assoc]
  calc Real.exp T * (Real.exp (-X) * ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v))
      ≤ Real.exp T * (Real.exp (-T) *
          ∫ φ, tiltDensity G w 0 bt v φ * ∏ j, lam j (φ j - φ v)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = ∫ φ, tiltDensity G w 0 bt v φ * ∏ j, lam j (φ j - φ v) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The algebra of the optimal shift: with `s = τ/(2C₁)`,
`τsR − C₁s²R − 16Λ = τ²R(1/(4C₁)) − 16Λ`. -/
lemma dipole_exponent_eq {τ R C₁ : ℝ} (hC₁ : 0 < C₁) :
    τ * (τ / (2 * C₁)) * R - C₁ * ((τ / (2 * C₁)) ^ 2 * R) = τ ^ 2 * R * (1 / (4 * C₁)) := by
  field_simp
  ring

/-- **The tilted ratio bound along the dipole potential** (FS81 (7.17), generic form). With the
tilt `b = τ∇g` of the unit dipole potential of `p, q` and the shift `σ = s(g − g(v))`,
`s = τ/(2C₁)`, `C₁ = κ_c + 4ε`:

`exp(τ² R(p, q) (1/(4C₁) − 16 ε_end)) ∫ ρ₀ O ≤ ∫ e^{⟨∇φ, τ∇g⟩} ρ₀ O`,

where `⟨∇φ, τ∇g⟩ = τ(φ(p) − φ(q))` (`sum_grad_mul_grad_dipolePotential`). The hypotheses are those
of `integral_tilt_ratio_ge`, `|τ| ≤ η/2`, and the endpoint threshold `hthrE` (the packing of
`sum_abs_mul_tiltExponent_sq_le` with `M = max(amp K₁, 1)`). -/
theorem integral_tilt_dipole_ge (hG : G.toSimpleGraph.Connected) (v : V)
    (CL : RootedChargeLayerD G v lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {dsc : (V → ℤ) → ℕ} {Kv : ℝ} {Kov : ℕ} (hloc : CL.IsLocal dsc Kv Kov) (hKv : 0 ≤ Kv)
    (hw : IsStripWeight w W c) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) {M : ℝ → ℝ}
    (hlog : HasLogDerivBounds w W M) {κc : ℝ} (hcurv : HasCurvatureBound w κc)
    {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hM : ∀ u : ℝ, |u| ≤ max (amp * K₁) 1 → M u ≤ m)
    {a₁ a₂ b : ℝ} (hZ : ∀ ϱ : V → ℤ, Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    {ε : ℝ} (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    {εe : ℝ} (hthrE : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (Kv * max (amp * K₁) 1 ^ 2) * (d + 1) ^ (2 + 1) * u ^ 0 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ εe)
    (hC₁ : 0 < κc + 4 * ε)
    {η K : ℝ} (hη : 0 < η) (hwexp : HasExpMajorant w W η K) (p q : V) (τ : ℝ)
    (hτ : |τ| ≤ η / 2) :
    Real.exp (τ ^ 2 * dipoleResistance G hG p q * (1 / (4 * (κc + 4 * ε)) - 16 * εe)) *
        ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) ≤
      ∫ φ, tiltDensity G w 0 (fun e => τ * G.grad (dipolePotential G hG p q) e) v φ *
        ∏ j, lam j (φ j - φ v) := by
  classical
  set g := dipolePotential G hG p q with hg
  set R := dipoleResistance G hG p q with hR
  set bt : E → ℝ := fun e => τ * G.grad g e with hbt
  set C₁ := κc + 4 * ε with hC₁def
  set s := τ / (2 * C₁) with hs
  set σ : V → ℝ := fun x => s * (g x - g v) with hσ
  have hε : 0 ≤ ε := le_trans (by positivity) (hthr 1 2 le_rfl (by norm_num))
  have hεe : 0 ≤ εe := le_trans (by positivity) (hthrE 1 2 le_rfl (by norm_num))
  have hR0 : 0 ≤ R := dipoleResistance_nonneg G hG p q
  -- the tilt is admissible
  have hbtη : ∀ e, |bt e| ≤ η / 2 := fun e => by
    rw [hbt, abs_mul]
    calc |τ| * |G.grad g e| ≤ |τ| * 1 :=
          mul_le_mul_of_nonneg_left (abs_grad_dipolePotential_le_one G hG p q e) (abs_nonneg _)
      _ ≤ η / 2 := by rw [mul_one]; exact hτ
  -- the endpoint sums
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  have hlogb : ∀ i, ∀ ϱ ∈ CL.N i, 0 ≤ Real.logb 2 (dsc ϱ + 1) := fun i ϱ _ =>
    Real.logb_nonneg (by norm_num) (by
      have := Nat.cast_nonneg (α := ℝ) (dsc ϱ); linarith)
  have hdecay : ∀ i, ∀ ϱ ∈ CL.N i, |rootedActivityD CL c κ amp k₀ i ϱ| ≤
      Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + Real.logb 2 (dsc ϱ + 1))) :=
    fun i ϱ hϱ => abs_rootedActivityD_le CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂
      hZ hb0 hb₁ hb₂ i ϱ hϱ (hlogb i ϱ hϱ) (hloc.cover i ϱ hϱ)
  have hbtsq : ∑ e, bt e ^ 2 = τ ^ 2 * R := by
    rw [hR, ← sum_grad_sq_dipolePotential G hG p q, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [hbt]; ring
  have hΛ : ∀ i, ∑ ϱ ∈ CL.N i, |rootedActivityD CL c κ amp k₀ i ϱ| *
      tiltExponent (gradLinear G) bt (rootedSpinWaveD CL κ amp k₀ i ϱ) ^ 2 ≤
      εe * (τ ^ 2 * R) := fun i => by
    rw [← hbtsq]
    exact sum_abs_mul_tiltExponent_sq_le CL hloc hKv κ amp k₀
      (fun i ϱ hϱ e => abs_grad_rootedSpinWaveD_le CL hκ hK₀ hK₁ hamp k₀ i ϱ hϱ e)
      (rootedActivityD CL c κ amp k₀) b εe hdecay hthrE bt i
  -- the ratio bound at the shift `σ`
  have hσv : σ v = 0 := by rw [hσ]; simp
  have hmain := integral_tilt_ratio_ge hG v CL hloc hKv hw hnzero hlog hcurv hc hκ hK₀ hK₁ hD₁
    hamp hampW hW1 hk₀ hexp hquad₁ hquad₂ hm0 hm1 hM hZ hb8 hb₁ hb₂ hthr hη hwexp bt hbtη hΛ σ hσv
  -- the exponent
  have hgradσ : ∀ e, G.grad σ e = s * G.grad g e := fun e => by
    simp only [hσ, Multigraph.grad]
    ring
  have hT : tiltExponent (gradLinear G) bt σ = τ * s * R := by
    unfold tiltExponent
    simp only [gradLinear_apply, hgradσ]
    rw [hR, ← sum_grad_sq_dipolePotential G hG p q, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [hbt]; ring
  have hE : ∑ e, G.grad σ e ^ 2 = s ^ 2 * R := by
    rw [hR, ← sum_grad_sq_dipolePotential G hG p q, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [hgradσ]; ring
  have hmod : ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + G.grad σ e ^ 2) ≤
      2 * (s ^ 2 * R) := by
    calc ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + G.grad σ e ^ 2)
        = ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + ∑ e, G.grad σ e ^ 2 :=
          Finset.sum_add_distrib
      _ ≤ ∑ e, G.grad σ e ^ 2 + ∑ e, G.grad σ e ^ 2 := by
          refine add_le_add (Finset.sum_le_sum fun e _ => ?_) le_rfl
          rw [← sq_abs (toIcoMod _ _ _), ← sq_abs (G.grad σ e)]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_toIcoMod_le_abs _) 2
      _ = 2 * (s ^ 2 * R) := by rw [hE]; ring
  have hexpo : τ ^ 2 * R * (1 / (4 * C₁) - 16 * εe) ≤
      tiltExponent (gradLinear G) bt σ - κc * ∑ e, G.grad σ e ^ 2 -
        2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 +
          G.grad σ e ^ 2) - 16 * (εe * (τ ^ 2 * R)) := by
    rw [hT, hE]
    have h1 := dipole_exponent_eq (τ := τ) (R := R) hC₁
    have h2 : 2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 +
        G.grad σ e ^ 2) ≤ 2 * ε * (2 * (s ^ 2 * R)) := mul_le_mul_of_nonneg_left hmod (by
      positivity)
    rw [← hs] at h1
    have h3 : τ * s * R - κc * (s ^ 2 * R) - 2 * ε * (2 * (s ^ 2 * R)) =
        τ * s * R - C₁ * (s ^ 2 * R) := by rw [hC₁def]; ring
    nlinarith [h1, h2, h3]
  calc Real.exp (τ ^ 2 * R * (1 / (4 * C₁) - 16 * εe)) *
        ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v)
      ≤ Real.exp (tiltExponent (gradLinear G) bt σ - κc * ∑ e, G.grad σ e ^ 2 -
          2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 +
            G.grad σ e ^ 2) - 16 * (εe * (τ ^ 2 * R))) *
          ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) := by
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexpo)
          (integral_edgeDensity_rootedLayerD_nonneg hG v CL hloc hw hc hκ hK₀ hK₁ hD₁ hamp hampW
            hW1 hk₀ hexp hquad₁ hquad₂ hZ hb8 hb₁ hb₂)
    _ ≤ _ := hmain

end FroehlichSpencer.BKT.SOS.Tilt

end
