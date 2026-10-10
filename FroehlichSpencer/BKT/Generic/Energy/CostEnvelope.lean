/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.SpinWave.Base
public import FroehlichSpencer.BKT.Generic.SpinWave.Graded
public import FroehlichSpencer.BKT.Generic.GaussianInstance
public import FroehlichSpencer.BKT.Rotator.Contour.Factor

/-!
# The cost-envelope energy lemma

The translation energy `E_c(a, ϱ) = ⟨a, ϱ⟩ − Σ_e c(∇a(e))` of `Generic/LocalFactor.lean` for a
non-quadratic edge cost `c` ().

The cost is assumed to have the two-branch envelope of
FS81 Theorem 6.1 (c), J p. 576 (`Rotator.Contour.cEnvelope`):

* `c(u) ≤ κ u²` for `|u| ≤ 1` (quadratic branch),
* `c(u) ≤ κ' e^{2π|u|}` for `1 ≤ |u| ≤ W` (exponential branch).

By
gradient disjointness the energy splits over the pieces, which gives

`E_c(a, ϱ) ≥ Σ_{s < k₀} (λ |q_t| − N B(λK₁)) + Σ_{s ≥ k₀} μ_s / 2`, and `|∇a| ≤ max(λK₁, 1)`,

where `B(x) = κx² + κ'e^{2πx}` and `N` bounds the number of edges on which a piece below `k₀` has
nonzero gradient (the energy envelope count §4 count; an explicit hypothesis here).

For the Bessel cost
`c(u) = cEnvelope C u / β` and `λ = log β/(4πK₁)` the exponential-branch pieces contribute at least
`(log β/(8πK₁)) |q_t|` as soon as `β ≥ max(e, (16πK₁CN)²)`.
-/

@[expose] public section

open FroehlichSpencer.BKT.Generic.SpinWave
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Generic

/-! ### The cost envelope -/

/-- The majorant `B(x) = κ x² + κ' e^{2πx}` of the cost on `|u| ≤ x`. -/
def costMajorant (κ κ' x : ℝ) : ℝ :=
  κ * x ^ 2 + κ' * Real.exp (2 * π * x)

/-- A cost with the two-branch envelope of FS81 Theorem 6.1 (c) up to the width `W`. -/
structure IsCostEnvelope (c : ℝ → ℝ) (κ κ' W : ℝ) : Prop where
  even : ∀ u, c (-u) = c u
  zero : c 0 = 0
  nonneg_κ : 0 ≤ κ
  nonneg_κ' : 0 ≤ κ'
  quad : ∀ u, |u| ≤ 1 → c u ≤ κ * u ^ 2
  expo : ∀ u, 1 ≤ |u| → |u| ≤ W → c u ≤ κ' * Real.exp (2 * π * |u|)

theorem costMajorant_nonneg {κ κ' : ℝ} (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (x : ℝ) :
    0 ≤ costMajorant κ κ' x := by
  unfold costMajorant
  positivity

theorem costMajorant_mono {κ κ' : ℝ} (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : costMajorant κ κ' x ≤ costMajorant κ κ' y := by
  unfold costMajorant
  have h1 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  have h2 : Real.exp (2 * π * x) ≤ Real.exp (2 * π * y) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  nlinarith [mul_le_mul_of_nonneg_left h1 hκ, mul_le_mul_of_nonneg_left h2 hκ']

theorem IsCostEnvelope.le_costMajorant {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W)
    {u x : ℝ} (hux : |u| ≤ x) (hxW : x ≤ W) : c u ≤ costMajorant κ κ' x := by
  have hx : 0 ≤ x := (abs_nonneg u).trans hux
  have hexp : 0 ≤ κ' * Real.exp (2 * π * x) := mul_nonneg hc.nonneg_κ' (Real.exp_pos _).le
  unfold costMajorant
  by_cases h : |u| ≤ 1
  · have hu2 : u ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg u) hux 2
    nlinarith [hc.quad u h, mul_le_mul_of_nonneg_left hu2 hc.nonneg_κ]
  · push Not at h
    have h1 := hc.expo u h.le (hux.trans hxW)
    have h2 : Real.exp (2 * π * |u|) ≤ Real.exp (2 * π * x) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.nonneg_κ', mul_nonneg hc.nonneg_κ (sq_nonneg x)]

/-! ### One piece -/

variable {V E : Type*} [Fintype V] [Fintype E]

theorem translationEnergy_smul (c : ℝ → ℝ) (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (r : ℝ) (ψ ϱ : V → ℝ) :
    translationEnergy c D (r • ψ) ϱ = r * ∑ j, ψ j * ϱ j - ∑ e, c (r * D ψ e) := by
  simp only [translationEnergy, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Quadratic branch.** If `|r| g ≤ 1` for a gradient bound `g`, then
`E_c(r ψ, ϱ) ≥ r⟨ψ, ϱ⟩ − κ r² Σ_e (∇ψ)²`. -/
theorem translationEnergy_smul_ge_quad {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) {ψ ϱ : V → ℝ} {g r : ℝ} (hgrad : ∀ e, |D ψ e| ≤ g)
    (hr : |r| * g ≤ 1) :
    r * ∑ j, ψ j * ϱ j - κ * r ^ 2 * ∑ e, D ψ e ^ 2 ≤ translationEnergy c D (r • ψ) ϱ := by
  rw [translationEnergy_smul]
  have hcost : ∑ e, c (r * D ψ e) ≤ κ * r ^ 2 * ∑ e, D ψ e ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have hu : |r * D ψ e| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hgrad e) (abs_nonneg r)).trans hr
    calc c (r * D ψ e) ≤ κ * (r * D ψ e) ^ 2 := hc.quad _ hu
      _ = κ * r ^ 2 * D ψ e ^ 2 := by ring
  linarith

/-- **Exponential branch.** If `|r| g ≤ W` and `∇ψ` vanishes off a finite set `S` of at most `N`
edges, then `E_c(r ψ, ϱ) ≥ r⟨ψ, ϱ⟩ − N B(|r| g)`. -/
theorem translationEnergy_smul_ge_expo {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) {ψ ϱ : V → ℝ} {g r N : ℝ} (hgrad : ∀ e, |D ψ e| ≤ g)
    (hrW : |r| * g ≤ W) {S : Finset E} (hS : ∀ e, D ψ e ≠ 0 → e ∈ S) (hcount : (S.card : ℝ) ≤ N) :
    r * ∑ j, ψ j * ϱ j - N * costMajorant κ κ' (|r| * g) ≤ translationEnergy c D (r • ψ) ϱ := by
  classical
  rw [translationEnergy_smul]
  have hB := costMajorant_nonneg hc.nonneg_κ hc.nonneg_κ' (|r| * g)
  have hcost : ∑ e, c (r * D ψ e) ≤ N * costMajorant κ κ' (|r| * g) := by
    rw [← Finset.sum_add_sum_compl S]
    have h0 : ∑ e ∈ Sᶜ, c (r * D ψ e) = 0 :=
      Finset.sum_eq_zero fun e he => by
        have : D ψ e = 0 := by
          by_contra h
          exact (Finset.mem_compl.mp he) (hS e h)
        rw [this, mul_zero, hc.zero]
    rw [h0, add_zero]
    calc ∑ e ∈ S, c (r * D ψ e)
        ≤ ∑ _e ∈ S, costMajorant κ κ' (|r| * g) :=
          Finset.sum_le_sum fun e _ => hc.le_costMajorant (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hgrad e) (abs_nonneg r)) hrW
      _ = S.card * costMajorant κ κ' (|r| * g) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * costMajorant κ κ' (|r| * g) := mul_le_mul_of_nonneg_right hcount hB
  linarith

/-! ### The amplitude rule -/

/-- The quadratic-branch amplitude scale `μ_s = min(1/(2κK₀), 2^{γ s}/K₁)`. -/
def quadAmplitude (κ K₀ K₁ γ : ℝ) (s : ℕ) : ℝ :=
  min (1 / (2 * κ * K₀)) ((2 : ℝ) ^ (γ * s) / K₁)

/-- The amplitude of a piece of scale `s` and charge `q`: `λ q/|q|` below `k₀`, `μ_s/q` from `k₀`
on. Both have the sign of `q`. -/
def costEnvelopeAmplitude (κ K₀ K₁ γ lam : ℝ) (k₀ : ℕ) (s : ℕ) (q : ℝ) : ℝ :=
  if s < k₀ then lam * q / |q| else quadAmplitude κ K₀ K₁ γ s / q

theorem quadAmplitude_pos {κ K₀ K₁ γ : ℝ} (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (s : ℕ) :
    0 < quadAmplitude κ K₀ K₁ γ s := by
  unfold quadAmplitude
  exact lt_min (by positivity) (by positivity)

/-! ### Assembly over graded spin-wave data -/

section Graded

variable [DecidableEq V] {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {centerOf : (V → ℤ) → V}
  {ρ : V → ℤ}

/-- The exponent `γ = 1 − 1/α` of the gradient bound. -/
def gradExponent (α : ℝ) : ℝ :=
  1 - 1 / α

theorem gradExponent_pos {α : ℝ} (hα : 1 < α) : 0 < gradExponent α := by
  unfold gradExponent
  have : 1 / α < 1 := by rw [div_lt_one (by linarith)]; exact hα
  linarith

/-- The amplitude of piece `t` under the cost-envelope rule. -/
def envelopeAmplitude (Wv : GradedSpinWave G N₀ centerOf ρ) (κ lam : ℝ) (k₀ : ℕ) (t : Wv.ι) : ℝ :=
  costEnvelopeAmplitude κ Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) lam k₀ (Wv.scale t) (Wv.charge t)

/-- The spin wave `a = Σ_t r_t ψ_t` with the per-scale amplitudes. -/
def envelopeWave (Wv : GradedSpinWave G N₀ centerOf ρ) (κ lam : ℝ) (k₀ : ℕ) : V → ℝ :=
  letI := Wv.finite
  fun j => ∑ t, envelopeAmplitude Wv κ lam k₀ t * Wv.piece t j

theorem rpow_neg_gradExponent_le_one {α : ℝ} (hα : 1 < α) (s : ℕ) :
    (2 : ℝ) ^ (-gradExponent α * s) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (by have := gradExponent_pos hα; nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])

theorem charge_ne_zero (Wv : GradedSpinWave G N₀ centerOf ρ) (t : Wv.ι) : Wv.charge t ≠ 0 := by
  intro h
  have := Wv.charge_ge_one t
  rw [h, abs_zero] at this
  norm_num at this

/-- **The cost-envelope energy lemma.** For a cost with the two-branch envelope and graded
spin-wave data, the per-scale amplitudes give
`E_c(a, ϱ) ≥ Σ_{s < k₀} (λ|q_t| − N B(λK₁)) + Σ_{s ≥ k₀} μ_s/2`. -/
theorem translationEnergy_envelopeWave_ge (Wv : GradedSpinWave G N₀ centerOf ρ) {c : ℝ → ℝ}
    {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < Wv.K₀)
    (hK₁ : 0 < Wv.K₁) {lam : ℝ} (hlam : 0 ≤ lam) (hlamW : lam * Wv.K₁ ≤ W) (k₀ : ℕ) {N : ℝ}
    (hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ N) :
    letI := Wv.finite
    (∑ t ∈ Finset.univ.filter (fun t => Wv.scale t < k₀),
        (lam * |Wv.charge t| - N * costMajorant κ κ' (lam * Wv.K₁))) +
      ∑ t ∈ Finset.univ.filter (fun t => ¬Wv.scale t < k₀),
        quadAmplitude κ Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) (Wv.scale t) / 2 ≤
      translationEnergy c (gradLinear G) (envelopeWave Wv κ lam k₀) (fun j => (ρ j : ℝ)) := by
  let _ : Fintype Wv.ι := Wv.finite
  set γ := gradExponent Wv.alpha
  set D := gradLinear G
  let a : Wv.ι → V → ℝ := fun t => envelopeAmplitude Wv κ lam k₀ t • Wv.piece t
  have hsplit : translationEnergy c D (envelopeWave Wv κ lam k₀) (fun j => (ρ j : ℝ)) =
      ∑ t, translationEnergy c D (a t) (fun j => (ρ j : ℝ)) := by
    classical
    have h := translationEnergy_sum_of_grad_disjoint Finset.univ c hc.zero D a
      (fun j => (ρ j : ℝ)) (fun t _ t' _ htt' e => ?_)
    · rw [← h]
      rfl
    · have hsm : ∀ t, D (a t) e = envelopeAmplitude Wv κ lam k₀ t * G.grad (Wv.piece t) e :=
        fun t => by
          simp only [a]
          rw [map_smul]
          rfl
      rcases Wv.grad_disjoint t t' htt' e with h | h
      · left
        rw [hsm, h, mul_zero]
      · right
        rw [hsm, h, mul_zero]
  have hpair : ∀ t, ∑ j, Wv.piece t j * (ρ j : ℝ) = Wv.charge t := fun t => Wv.pairing t
  have henergy : ∀ t, ∑ e, D (Wv.piece t) e ^ 2 ≤ Wv.K₀ * Wv.charge t ^ 2 := fun t => by
    simpa only [D, gradLinear_apply, Multigraph.energy] using Wv.energy_le t
  have hgrad : ∀ t e, |D (Wv.piece t) e| ≤ Wv.K₁ * (2 : ℝ) ^ (-γ * (Wv.scale t : ℝ)) :=
    fun t e => by
      simpa only [D, gradLinear_apply, γ, gradExponent, neg_sub] using Wv.grad_le t e
  rw [hsplit, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => Wv.scale t < k₀)]
  refine add_le_add (Finset.sum_le_sum fun t ht => ?_) (Finset.sum_le_sum fun t ht => ?_)
  · -- exponential branch
    have hs := (Finset.mem_filter.mp ht).2
    have hq := charge_ne_zero Wv t
    have hqa : 0 < |Wv.charge t| := abs_pos.mpr hq
    have hr : envelopeAmplitude Wv κ lam k₀ t = lam * Wv.charge t / |Wv.charge t| := by
      simp only [envelopeAmplitude, costEnvelopeAmplitude, ite_eq_left hs]
    have hrabs : |envelopeAmplitude Wv κ lam k₀ t| = lam := by
      rw [hr, abs_div, abs_mul, abs_abs, abs_of_nonneg hlam, mul_div_assoc,
        div_self hqa.ne', mul_one]
    have hg : ∀ e, |D (Wv.piece t) e| ≤ Wv.K₁ := fun e =>
      (hgrad t e).trans (mul_le_of_le_one_right hK₁.le
        (by simpa [γ] using rpow_neg_gradExponent_le_one Wv.alpha_gt_one (Wv.scale t)))
    have h := translationEnergy_smul_ge_expo hc D (ϱ := fun j => (ρ j : ℝ)) hg
      (r := envelopeAmplitude Wv κ lam k₀ t) (by rw [hrabs]; exact hlamW)
      (S := Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0)
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩) (hcount t hs)
    rw [hrabs, hpair] at h
    have hgain : envelopeAmplitude Wv κ lam k₀ t * Wv.charge t = lam * |Wv.charge t| := by
      rw [hr, div_mul_eq_mul_div, mul_assoc, ← sq, ← sq_abs, sq, ← mul_assoc,
        mul_div_assoc, div_self hqa.ne']
      ring
    rw [hgain] at h
    exact h
  · -- quadratic branch
    have hs := (Finset.mem_filter.mp ht).2
    have hq := charge_ne_zero Wv t
    have hqa : 0 < |Wv.charge t| := abs_pos.mpr hq
    set μ := quadAmplitude κ Wv.K₀ Wv.K₁ γ (Wv.scale t)
    have hμ : 0 < μ := quadAmplitude_pos hκ hK₀ hK₁ _
    have hr : envelopeAmplitude Wv κ lam k₀ t = μ / Wv.charge t := by
      simp only [envelopeAmplitude, costEnvelopeAmplitude, ite_eq_right hs, μ, γ]
    have hpow : (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) * (2 : ℝ) ^ (-γ * (Wv.scale t : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num), neg_mul, add_neg_cancel, Real.rpow_zero]
    have hrg : |envelopeAmplitude Wv κ lam k₀ t| * (Wv.K₁ * (2 : ℝ) ^ (-γ * (Wv.scale t : ℝ)))
        ≤ 1 := by
      rw [hr, abs_div, abs_of_pos hμ]
      have hμ2 : μ ≤ (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) / Wv.K₁ := min_le_right _ _
      have hq1 := Wv.charge_ge_one t
      rw [div_mul_eq_mul_div, div_le_one hqa]
      calc μ * (Wv.K₁ * (2 : ℝ) ^ (-γ * (Wv.scale t : ℝ)))
          ≤ (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) / Wv.K₁ *
              (Wv.K₁ * (2 : ℝ) ^ (-γ * (Wv.scale t : ℝ))) :=
            mul_le_mul_of_nonneg_right hμ2 (by positivity)
        _ = (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) * (2 : ℝ) ^ (-γ * (Wv.scale t : ℝ)) := by
          field_simp
        _ = 1 := hpow
        _ ≤ |Wv.charge t| := hq1
    have h := translationEnergy_smul_ge_quad hc D (ϱ := fun j => (ρ j : ℝ)) (hgrad t) hrg
    rw [hpair] at h
    have hμ1 : μ ≤ 1 / (2 * κ * Wv.K₀) := min_le_left _ _
    have hκK : κ * Wv.K₀ * μ ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * κ * Wv.K₀)] at hμ1
      nlinarith
    have hgain : envelopeAmplitude Wv κ lam k₀ t * Wv.charge t = μ := by
      rw [hr, div_mul_cancel₀ _ hq]
    have hcost : κ * envelopeAmplitude Wv κ lam k₀ t ^ 2 * ∑ e, D (Wv.piece t) e ^ 2 ≤
        κ * Wv.K₀ * μ ^ 2 := by
      have h1 : κ * envelopeAmplitude Wv κ lam k₀ t ^ 2 * ∑ e, D (Wv.piece t) e ^ 2 ≤
          κ * envelopeAmplitude Wv κ lam k₀ t ^ 2 * (Wv.K₀ * Wv.charge t ^ 2) :=
        mul_le_mul_of_nonneg_left (henergy t) (by positivity)
      have h2 : κ * envelopeAmplitude Wv κ lam k₀ t ^ 2 * (Wv.K₀ * Wv.charge t ^ 2) =
          κ * Wv.K₀ * μ ^ 2 := by
        rw [hr, div_pow]
        field_simp
      linarith
    nlinarith [hgain, hcost, h]

/-- The gradient of the assembled wave is at most `max(λK₁, 1)`. -/
theorem abs_grad_envelopeWave_le (Wv : GradedSpinWave G N₀ centerOf ρ) {κ : ℝ} (hκ : 0 < κ)
    (hK₀ : 0 < Wv.K₀) (hK₁ : 0 < Wv.K₁) {lam : ℝ} (hlam : 0 ≤ lam) (k₀ : ℕ) (e : E) :
    |G.grad (envelopeWave Wv κ lam k₀) e| ≤ max (lam * Wv.K₁) 1 := by
  classical
  let _ : Fintype Wv.ι := Wv.finite
  set γ := gradExponent Wv.alpha
  have hlin : G.grad (envelopeWave Wv κ lam k₀) e =
      ∑ t, envelopeAmplitude Wv κ lam k₀ t * G.grad (Wv.piece t) e := by
    simp only [envelopeWave, Multigraph.grad, Finset.sum_sub_distrib, mul_sub]
  have hterm : ∀ t, |envelopeAmplitude Wv κ lam k₀ t * G.grad (Wv.piece t) e| ≤
      max (lam * Wv.K₁) 1 := fun t => by
    have hq := charge_ne_zero Wv t
    have hqa : 0 < |Wv.charge t| := abs_pos.mpr hq
    have hg := Wv.grad_le t e
    have hle1 := rpow_neg_gradExponent_le_one Wv.alpha_gt_one (Wv.scale t)
    rw [abs_mul]
    by_cases hs : Wv.scale t < k₀
    · have hrabs : |envelopeAmplitude Wv κ lam k₀ t| = lam := by
        simp only [envelopeAmplitude, costEnvelopeAmplitude, ite_eq_left hs]
        rw [abs_div, abs_mul, abs_abs, abs_of_nonneg hlam, mul_div_assoc, div_self hqa.ne',
          mul_one]
      rw [hrabs]
      refine le_trans ?_ (le_max_left _ _)
      refine mul_le_mul_of_nonneg_left (hg.trans ?_) hlam
      refine mul_le_of_le_one_right hK₁.le ?_
      simpa [gradExponent] using hle1
    · set μ := quadAmplitude κ Wv.K₀ Wv.K₁ γ (Wv.scale t)
      have hμ : 0 < μ := quadAmplitude_pos hκ hK₀ hK₁ _
      have hr : |envelopeAmplitude Wv κ lam k₀ t| = μ / |Wv.charge t| := by
        simp only [envelopeAmplitude, costEnvelopeAmplitude, ite_eq_right hs]
        rw [abs_div, abs_of_pos hμ]
      have hμ2 : μ ≤ (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) / Wv.K₁ := min_le_right _ _
      have hpow : (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) * (2 : ℝ) ^ (-(1 - 1 / Wv.alpha) *
          (Wv.scale t : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num), show γ = 1 - 1 / Wv.alpha from rfl, neg_mul,
          add_neg_cancel, Real.rpow_zero]
      refine le_trans ?_ (le_max_right _ _)
      rw [hr, div_mul_eq_mul_div, div_le_one hqa]
      calc μ * |G.grad (Wv.piece t) e|
          ≤ (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) / Wv.K₁ *
              (Wv.K₁ * (2 : ℝ) ^ (-(1 - 1 / Wv.alpha) * (Wv.scale t : ℝ))) :=
            mul_le_mul hμ2 hg (abs_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (γ * (Wv.scale t : ℝ)) *
            (2 : ℝ) ^ (-(1 - 1 / Wv.alpha) * (Wv.scale t : ℝ)) := by
          field_simp
        _ = 1 := hpow
        _ ≤ |Wv.charge t| := Wv.charge_ge_one t
  -- at most one term is nonzero
  rw [hlin]
  by_cases h : ∃ t, envelopeAmplitude Wv κ lam k₀ t * G.grad (Wv.piece t) e ≠ 0
  · obtain ⟨t₀, ht₀⟩ := h
    rw [Finset.sum_eq_single t₀ (fun t _ htt₀ => ?_) (fun h => absurd (Finset.mem_univ t₀) h)]
    · exact hterm t₀
    · rcases Wv.grad_disjoint t t₀ htt₀ e with h' | h'
      · rw [h', mul_zero]
      · exact absurd (by rw [h', mul_zero]) ht₀
  · push Not at h
    rw [Finset.sum_eq_zero fun t _ => h t, abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)

end Graded

/-! ### The Bessel cost -/

/-- The Bessel translation cost `c(u) = cEnvelope C u / β` (FS81 Theorem 6.1 (c), J p. 576) has
the two-branch envelope with `κ = κ' = C/β`, at every width. -/
theorem isCostEnvelope_cEnvelope {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) (W : ℝ) :
    IsCostEnvelope (fun u => Rotator.Contour.cEnvelope C u / β) (C / β) (C / β) W where
  even u := by simp only [Rotator.Contour.cEnvelope_neg]
  zero := by simp [Rotator.Contour.cEnvelope]
  nonneg_κ := div_nonneg hC hβ.le
  nonneg_κ' := div_nonneg hC hβ.le
  quad u hu := by
    simp only [Rotator.Contour.cEnvelope, ite_eq_left hu]
    rw [div_mul_eq_mul_div]
  expo u hu _ := by
    simp only [Rotator.Contour.cEnvelope]
    split_ifs with h
    · have hu1 : |u| = 1 := le_antisymm h hu
      have hsq : u ^ 2 = 1 := by rw [← sq_abs, hu1, one_pow]
      rw [hsq, mul_one, hu1]
      have he : 1 ≤ Real.exp (2 * π * 1) := Real.one_le_exp (by positivity)
      calc C / β = C / β * 1 := (mul_one _).symm
        _ ≤ C / β * Real.exp (2 * π * 1) := mul_le_mul_of_nonneg_left he (div_nonneg hC hβ.le)
    · rw [div_mul_eq_mul_div]

/-- The exponential-branch amplitude `λ_β = log β / (4πK₁)` for the Bessel cost. -/
def besselAmplitude (K₁ β : ℝ) : ℝ :=
  Real.log β / (4 * π * K₁)

theorem costMajorant_bessel_le {C β K₁ : ℝ} (hC : 0 ≤ C) (hβ : 1 ≤ β) (hK₁ : 0 < K₁) :
    costMajorant (C / β) (C / β) (besselAmplitude K₁ β * K₁) ≤ 2 * C / Real.sqrt β := by
  have hβ0 : 0 < β := by linarith
  have hlog0 : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hx : besselAmplitude K₁ β * K₁ = Real.log β / (4 * π) := by
    unfold besselAmplitude
    field_simp
  have hsqrt : Real.exp (2 * π * (Real.log β / (4 * π))) = Real.sqrt β := by
    rw [show 2 * π * (Real.log β / (4 * π)) = Real.log β * (1 / 2) by field_simp; ring,
      ← Real.rpow_def_of_pos hβ0, Real.sqrt_eq_rpow]
  have hlog : Real.log β ≤ 4 * β ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hβ0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rwa [div_eq_mul_inv, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num, mul_comm] at this
  have hquart : (β ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le, Real.sqrt_eq_rpow]
    norm_num
  have hlog2 : Real.log β ^ 2 ≤ 16 * Real.sqrt β := by
    rw [← hquart]
    nlinarith [pow_le_pow_left₀ hlog0 hlog 2]
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hss : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.two_le_pi]
  rw [hx, costMajorant, hsqrt]
  have hbound : (Real.log β / (4 * π)) ^ 2 ≤ Real.sqrt β := by
    rw [div_pow]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.two_le_pi]
  calc C / β * (Real.log β / (4 * π)) ^ 2 + C / β * Real.sqrt β
      ≤ C / β * Real.sqrt β + C / β * Real.sqrt β := by
        gcongr
    _ = 2 * C / Real.sqrt β := by
        have h1 : C / β * Real.sqrt β = C / Real.sqrt β := by
          rw [div_mul_eq_mul_div, div_eq_div_iff hβ0.ne' hs.ne', mul_assoc, hss]
        rw [h1]
        ring

/-- For `β ≥ max(e, (16πK₁CN)²)`, the exponential-branch cost of `N` edges is at most half the
gain: `N · B(λ_β K₁) ≤ λ_β / 2`. -/
theorem bessel_expBranch_le {C β K₁ N : ℝ} (hC : 0 ≤ C) (hK₁ : 0 < K₁) (hN : 0 ≤ N)
    (hβe : Real.exp 1 ≤ β) (hβN : (16 * π * K₁ * C * N) ^ 2 ≤ β) :
    N * costMajorant (C / β) (C / β) (besselAmplitude K₁ β * K₁) ≤ besselAmplitude K₁ β / 2 := by
  have hβ1 : 1 ≤ β := le_trans (Real.one_le_exp (by norm_num)) hβe
  have hβ0 : 0 < β := by linarith
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hlog1 : 1 ≤ Real.log β := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hβe
  have hsN : 16 * π * K₁ * C * N ≤ Real.sqrt β := by
    have h0 : 0 ≤ 16 * π * K₁ * C * N := by positivity
    calc 16 * π * K₁ * C * N = Real.sqrt ((16 * π * K₁ * C * N) ^ 2) := by
          rw [Real.sqrt_sq h0]
      _ ≤ Real.sqrt β := Real.sqrt_le_sqrt hβN
  calc N * costMajorant (C / β) (C / β) (besselAmplitude K₁ β * K₁)
      ≤ N * (2 * C / Real.sqrt β) := mul_le_mul_of_nonneg_left (costMajorant_bessel_le hC hβ1 hK₁) hN
    _ ≤ 1 / (8 * π * K₁) := by
        rw [mul_div_assoc', div_le_div_iff₀ hs (by positivity)]
        nlinarith [hsN]
    _ ≤ besselAmplitude K₁ β / 2 := by
        unfold besselAmplitude
        rw [div_div, show 4 * π * K₁ * 2 = 8 * π * K₁ by ring]
        gcongr

/-- **The Bessel cost-envelope energy bound.** For the Bessel cost `cEnvelope C u / β`, the
amplitude `λ_β = log β/(4πK₁)` below the threshold scale `k₀` and `μ_s` from `k₀` on, if every
piece below `k₀` has nonzero gradient on at most `N` edges and `β ≥ max(e, (16πK₁CN)², 2)`:
`E_c(a, ϱ) ≥ (log β/(8πK₁)) Σ_{s < k₀} |q_t| + ½ Σ_{s ≥ k₀} min(β/(2CK₀), 2^{γ s}/K₁)`, and
`|∇a| ≤ max(log β/(4π), 1) ≤ β/2`, inside the strip where the Bessel envelope holds. -/
theorem translationEnergy_envelopeWave_bessel_ge [DecidableEq V] {G : Multigraph V E}
    {N₀ : Finset (V → ℤ)} {centerOf : (V → ℤ) → V} {ρ : V → ℤ}
    (Wv : GradedSpinWave G N₀ centerOf ρ) {C β : ℝ} (hC : 0 < C) (hK₀ : 0 < Wv.K₀)
    (hK₁ : 0 < Wv.K₁) (k₀ : ℕ) {N : ℝ} (hN : 0 ≤ N)
    (hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ N)
    (hβe : Real.exp 1 ≤ β) (hβN : (16 * π * Wv.K₁ * C * N) ^ 2 ≤ β) (hβ2 : 2 ≤ β) :
    letI := Wv.finite
    (Real.log β / (8 * π * Wv.K₁) *
        ∑ t ∈ Finset.univ.filter (fun t => Wv.scale t < k₀), |Wv.charge t|) +
      ∑ t ∈ Finset.univ.filter (fun t => ¬Wv.scale t < k₀),
        quadAmplitude (C / β) Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) (Wv.scale t) / 2 ≤
      translationEnergy (fun u => Rotator.Contour.cEnvelope C u / β) (gradLinear G)
        (envelopeWave Wv (C / β) (besselAmplitude Wv.K₁ β) k₀) (fun j => (ρ j : ℝ)) ∧
    ∀ e, |G.grad (envelopeWave Wv (C / β) (besselAmplitude Wv.K₁ β) k₀) e| ≤ β / 2 := by
  classical
  let _ : Fintype Wv.ι := Wv.finite
  have hβ0 : 0 < β := by linarith
  have hlam0 : 0 ≤ besselAmplitude Wv.K₁ β := by
    unfold besselAmplitude
    exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  have hlamK : besselAmplitude Wv.K₁ β * Wv.K₁ = Real.log β / (4 * π) := by
    unfold besselAmplitude
    field_simp
  have hlamW : besselAmplitude Wv.K₁ β * Wv.K₁ ≤ β / 2 := by
    rw [hlamK, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := Real.log_le_sub_one_of_pos hβ0
    nlinarith [Real.two_le_pi]
  have hκ : 0 < C / β := div_pos hC hβ0
  refine ⟨?_, fun e => ?_⟩
  · refine le_trans ?_ (translationEnergy_envelopeWave_ge Wv (isCostEnvelope_cEnvelope hC.le hβ0
      (β / 2)) hκ hK₀ hK₁ hlam0 hlamW k₀ hcount)
    have hexp := bessel_expBranch_le hC.le hK₁ hN hβe hβN
    refine add_le_add ?_ le_rfl
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    have hq := Wv.charge_ge_one t
    have hhalf : Real.log β / (8 * π * Wv.K₁) = besselAmplitude Wv.K₁ β / 2 := by
      unfold besselAmplitude
      field_simp
      ring
    rw [hhalf]
    nlinarith [hexp, mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ besselAmplitude Wv.K₁ β / 2)]
  · refine (abs_grad_envelopeWave_le Wv hκ hK₀ hK₁ hlam0 k₀ e).trans (max_le hlamW ?_)
    linarith

end FroehlichSpencer.BKT.Generic

end
