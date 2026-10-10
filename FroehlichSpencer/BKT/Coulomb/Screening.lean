/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.SecondMoment
public import FroehlichSpencer.BKT.Coulomb.SineGordon
import FroehlichSpencer.BKT.Coulomb.MomentCalculus
import Mathlib.Tactic

/-!
# The finite-volume obstruction to Debye screening

With `b(q) = κ ⟨q, C f⟩`, the representation (`Coulomb/SineGordon.lean`) reads
`M(u) = ⟨e^{u φ(f)}⟩_Λ = e^{κ ⟨f, C f⟩ u²/2} Ψ(u)`, `Ψ(u) = ⟨cos (u b(q))⟩_Λ`, a finite sum.

* `gasExpectation_sq_le_of_expMoment`: `M(u) ≥ e^{u² κ (1-δ) ⟨f,Cf⟩/2}` gives
  `Ψ(u) ≥ e^{-δ κ ⟨f,Cf⟩ u²/2}`, hence `⟨b(q)²⟩_Λ ≤ δ κ ⟨f, C f⟩` (the finite-volume
  `S_q(k) ≤ δ κ⁻¹ Ĉ(k)⁻¹`).
* `weightedGFFExpectation_sq_sineGordon`: **(1.17) in finite volume**,
  `⟨φ(f)²⟩_Λ = κ ⟨f, C f⟩ - κ² ⟨⟨q, C f⟩²⟩_Λ` (the right side's Fourier form at
  `f = e^{i k ·}` is `κ Ĉ(k) - κ² Ĉ(k)² ⟨|q̂(k)|²⟩`), proved by computing `M''(0)` twice: as a
  field moment (differentiation under the integral) and from the finite charge sum.

FS81 obtains (1.17) "by integration by parts in a periodic box"; no integration by parts is
  used here.
* `gasExpectation_cos_eq_sineGordon`: the representation read in the other direction, the
  charge characteristic functional as a sine-Gordon GFF expectation,
  `⟨cos ⟨q, g⟩⟩_Λ = e^{-‖∇g‖²/(2κ)} ⟨e^{φ(-Δ g)/κ}⟩^φ_Λ` for every test function `g`.
* `gasExpectation_pairing_sq_le_energy`: the same bound in Dirichlet-energy form,
  `⟨⟨q, g⟩²⟩_Λ ≤ (δ/κ) ∑_{edges} (g_j - g_ℓ)²` for every `g` (take `f = -Δ g`).
* `hardCore_chargeFluctuation_bound`: **the finite-volume screening obstruction** for the
  hard-core gas on free and even periodic squares, uniform in the volume (from  KP
  Theorem 1.5).

For `0 ≤ z`, the hard-core gas weights are nonnegative (`gasPartition_pos`), so
  the left side is a genuine variance of the charge pairing (its mean vanishes by `q ↦ -q`).

Debye screening (Stillinger–Lovett, (1.18): `M(κ) = 2/κ`) would give
  `⟨|q̂(k)|²⟩ ≈ κ⁻¹ |k|²` near `k = 0`, i.e. charge fluctuations `≈ κ⁻¹` times the Dirichlet
  energy of slowly varying `g`; the bound with `δ < 1` contradicts this uniformly in the volume.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Filter Topology

variable {W : Type*} [Fintype W] [DecidableEq W] {E : Type*} [Fintype E]

/-! ### The gas side: charge characteristic function and charge fluctuations -/

section Gas

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem gasExpectation_const_mul (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) (c : ℝ) (F : (V → ℤ) → ℝ) :
    gasExpectationInternal N T κ lam (fun q => c * F q) =
      c * gasExpectationInternal N T κ lam F := by
  unfold gasExpectationInternal
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

theorem gasExpectation_one (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (hZ : gasPartitionInternal N T κ lam ≠ 0) :
    gasExpectationInternal N T κ lam (fun _ => 1) = 1 := by
  unfold gasExpectationInternal
  simp only [mul_one]
  exact div_self hZ

/-- Differentiation of a gas expectation in a parameter (a finite sum). -/
theorem hasDerivAt_gasExpectation (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) {F F' : ℝ → (V → ℤ) → ℝ} {u₀ : ℝ}
    (h : ∀ q, HasDerivAt (fun u => F u q) (F' u₀ q) u₀) :
    HasDerivAt (fun u => gasExpectationInternal N T κ lam (F u))
      (gasExpectationInternal N T κ lam (F' u₀)) u₀ := by
  unfold gasExpectationInternal
  exact (HasDerivAt.fun_sum fun q _ => (h q).const_mul _).div_const _

/-- The scaled form of the representation: `M(u) = e^{κ ⟨f,Cf⟩ u²/2} Ψ(u)` with
`Ψ(u) = ⟨cos (u κ ⟨q, C f⟩)⟩_Λ`. -/
theorem weightedGFFExpectation_exp_mul_sineGordon {E : Type*} [Fintype E] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (u : ℝ) :
    weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j))
        (fun φ => Real.exp (u * ∑ j, φ j * f j)) =
      Real.exp (κ * (∑ j, f j * -(T f j)) / 2 * u ^ 2) *
        gasExpectationInternal N T κ lam
          (fun q => Real.cos (u * (κ * ∑ j, (q j : ℝ) * -(T f j)))) := by
  have huf : ∑ j, (u • f) j = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hf, mul_zero]
  have h := weightedGFFExpectation_exp_sineGordon G hG κ hκ v N lam hlam T hT (u • f) huf
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h
  have e1 : (fun φ : V → ℝ => Real.exp (u * ∑ j, φ j * f j)) =
      fun φ => Real.exp (∑ j, φ j * (u * f j)) := by
    funext φ
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : κ * (∑ j, f j * -(T f j)) / 2 * u ^ 2 =
      (κ * ∑ j, u * f j * -(u * T f j)) / 2 := by
    simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e3 : (fun q : V → ℤ => Real.cos (u * (κ * ∑ j, (q j : ℝ) * -(T f j)))) =
      fun q => Real.cos (κ * ∑ j, (q j : ℝ) * -(u * T f j)) := by
    funext q
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, e2, e3]
  exact h

theorem hasDerivAt_gasExpectation_cos (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) (b : (V → ℤ) → ℝ) (u : ℝ) :
    HasDerivAt (fun u => gasExpectationInternal N T κ lam (fun q => Real.cos (u * b q)))
      (gasExpectationInternal N T κ lam (fun q => -Real.sin (u * b q) * b q)) u := by
  refine hasDerivAt_gasExpectation N T κ lam (F := fun u q => Real.cos (u * b q))
    (F' := fun u q => -Real.sin (u * b q) * b q) (fun q => ?_)
  convert ((hasDerivAt_id' u).mul_const (b q)).cos using 1
  ring

theorem hasDerivAt_gasExpectation_sin (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) (b : (V → ℤ) → ℝ) :
    HasDerivAt (fun u => gasExpectationInternal N T κ lam (fun q => -Real.sin (u * b q) * b q))
      (-gasExpectationInternal N T κ lam (fun q => b q ^ 2)) 0 := by
  have h := hasDerivAt_gasExpectation N T κ lam (u₀ := 0)
    (F := fun u q => -Real.sin (u * b q) * b q)
    (F' := fun u q => -1 * (Real.cos (u * b q) * b q * b q)) (fun q => by
      convert (((hasDerivAt_id' (0 : ℝ)).mul_const (b q)).sin.neg.mul_const (b q)) using 1
      ring)
  convert h using 1
  rw [gasExpectation_const_mul]
  simp only [zero_mul, Real.cos_zero, one_mul, neg_one_mul]
  congr 2
  funext q
  ring

theorem gasExpectation_cos_zero (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) (b : (V → ℤ) → ℝ) (hZ : gasPartitionInternal N T κ lam ≠ 0) :
    gasExpectationInternal N T κ lam (fun q => Real.cos (0 * b q)) = 1 := by
  simp only [zero_mul, Real.cos_zero]
  exact gasExpectation_one N T κ lam hZ

/-- The gas side of FS81 Theorem 5.1: an exponential-moment lower bound
`⟨e^{u φ(f)}⟩ ≥ e^{u² κ (1-δ) ⟨f,Cf⟩/2}` for the sine-Gordon field bounds the charge
fluctuations, `⟨(κ ⟨q, C f⟩)²⟩_Λ ≤ δ κ ⟨f, C f⟩`. This is the finite-volume form of
`S_q(k) ≤ δ κ⁻¹ Ĉ(k)⁻¹` (J (1.17), p. 531, with p. 567). -/
theorem gasExpectation_sq_le_of_expMoment {E : Type*} [Fintype E] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (δ : ℝ) (hZ : gasPartitionInternal N T κ lam ≠ 0)
    (hlow : ∀ u : ℝ, Real.exp (u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2) ≤
      weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j))
        (fun φ => Real.exp (u * ∑ j, φ j * f j))) :
    gasExpectationInternal N T κ lam (fun q => (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2) ≤
      δ * κ * ∑ j, f j * -(T f j) := by
  set Q := ∑ j, f j * -(T f j) with hQ
  set b : (V → ℤ) → ℝ := fun q => κ * ∑ j, (q j : ℝ) * -(T f j) with hb
  have hΨ : ∀ u : ℝ, Real.exp (-(δ * κ * Q / 2) * u ^ 2) ≤
      gasExpectationInternal N T κ lam (fun q => Real.cos (u * b q)) := by
    intro u
    have h1 := hlow u
    rw [weightedGFFExpectation_exp_mul_sineGordon G hG κ hκ v N lam hlam T hT f hf u] at h1
    have hpos := Real.exp_pos (κ * Q / 2 * u ^ 2)
    rw [show -(δ * κ * Q / 2) * u ^ 2 = u ^ 2 * κ * (1 - δ) * Q / 2 - κ * Q / 2 * u ^ 2 by ring,
      Real.exp_sub, div_le_iff₀ hpos]
    exact h1.trans_eq (mul_comm _ _)
  have h := two_mul_le_of_exp_sq_le (gasExpectation_cos_zero N T κ lam b hZ)
    (Eventually.of_forall fun u => hasDerivAt_gasExpectation_cos N T κ lam b u)
    (hasDerivAt_gasExpectation_sin N T κ lam b) (Eventually.of_forall hΨ)
  linarith

/-- **FS81 (1.17) in finite volume**, in real space: for even charge weights with `Z_Λ ≠ 0`,
`⟨φ(f)²⟩_Λ = κ ⟨f, C f⟩ - κ² ⟨⟨q, C f⟩²⟩_Λ` for zero-sum `f`, the left side being the (signed)
sine-Gordon second moment and the right side the gas charge fluctuation (J p. 531). -/
theorem weightedGFFExpectation_sq_sineGordon {E : Type*} [Fintype E] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (hZ : gasPartitionInternal N T κ lam ≠ 0) :
    weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j)) (fun φ => (∑ j, φ j * f j) ^ 2) =
      κ * (∑ j, f j * -(T f j)) -
        gasExpectationInternal N T κ lam (fun q => (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2) := by
  set Q := ∑ j, f j * -(T f j) with hQ
  set a := κ * Q / 2 with ha
  set b : (V → ℤ) → ℝ := fun q => κ * ∑ j, (q j : ℝ) * -(T f j) with hb
  set lamSG : V → ℝ → ℝ := fun j => sineGordonWeightInternal N (lam j)
  set Ψ : ℝ → ℝ := fun u => gasExpectationInternal N T κ lam (fun q => Real.cos (u * b q))
  set Ψ₁ : ℝ → ℝ := fun u => gasExpectationInternal N T κ lam
    (fun q => -Real.sin (u * b q) * b q)
  have hΨ0 : Ψ 0 = 1 := gasExpectation_cos_zero N T κ lam b hZ
  have hWc : Continuous fun φ : V → ℝ => ∏ j, lamSG j (φ j) :=
    continuous_finsetProd _ fun j _ => (continuous_sineGordonWeight N _).comp (continuous_apply j)
  have hWB : ∀ φ : V → ℝ, |∏ j, lamSG j (φ j)| ≤
      ∏ j, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, |lam j n| := fun φ => by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => abs_sineGordonWeight_le _ _ _
  have hd := hasDerivAt_weightedGFFExpectation_pow_mul_exp G hG κ⁻¹ (inv_pos.2 hκ) v lamSG
    hWc hWB f hf
  set M₁ : ℝ → ℝ := fun u => weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v lamSG
    (fun φ => (∑ j, φ j * f j) ^ (0 + 1) * Real.exp (u * ∑ j, φ j * f j))
  have hrep : (fun u => weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v lamSG
      (fun φ => (∑ j, φ j * f j) ^ 0 * Real.exp (u * ∑ j, φ j * f j))) =
      fun u => Real.exp (a * u ^ 2) * Ψ u := by
    funext u
    simp only [pow_zero, one_mul]
    exact weightedGFFExpectation_exp_mul_sineGordon G hG κ hκ v N lam hlam T hT f hf u
  have hE : ∀ u : ℝ, HasDerivAt (fun u => Real.exp (a * u ^ 2))
      (2 * a * u * Real.exp (a * u ^ 2)) u := by
    intro u
    convert ((hasDerivAt_pow 2 u).const_mul a).exp using 1
    push_cast
    ring
  have hM₁ : ∀ u, M₁ u = 2 * a * u * Real.exp (a * u ^ 2) * Ψ u +
      Real.exp (a * u ^ 2) * Ψ₁ u := by
    intro u
    have h1 := hd 0 u
    rw [hrep] at h1
    exact h1.unique ((hE u).mul (hasDerivAt_gasExpectation_cos N T κ lam b u))
  have hM₁fun : M₁ = fun u => 2 * a * u * Real.exp (a * u ^ 2) * Ψ u +
      Real.exp (a * u ^ 2) * Ψ₁ u := funext hM₁
  have hfield := hd 1 0
  change HasDerivAt M₁ _ 0 at hfield
  rw [hM₁fun] at hfield
  have hexpl : HasDerivAt (fun u => 2 * a * u * Real.exp (a * u ^ 2) * Ψ u +
      Real.exp (a * u ^ 2) * Ψ₁ u)
      (2 * a - gasExpectationInternal N T κ lam (fun q => b q ^ 2)) 0 := by
    have h1 := ((((hasDerivAt_id' (0 : ℝ)).const_mul (2 * a)).mul (hE 0)).mul
      (hasDerivAt_gasExpectation_cos N T κ lam b 0)).add
      ((hE 0).mul (hasDerivAt_gasExpectation_sin N T κ lam b))
    convert h1 using 1
    change 2 * a - gasExpectationInternal N T κ lam (fun q => b q ^ 2) =
      (2 * a * 1 * Real.exp (a * 0 ^ 2) + 2 * a * 0 * (2 * a * 0 * Real.exp (a * 0 ^ 2))) * Ψ 0 +
        2 * a * 0 * Real.exp (a * 0 ^ 2) * Ψ₁ 0 +
        (2 * a * 0 * Real.exp (a * 0 ^ 2) * Ψ₁ 0 +
          Real.exp (a * 0 ^ 2) * -gasExpectationInternal N T κ lam (fun q => b q ^ 2))
    rw [hΨ0]
    simp
    ring
  have huniq := hfield.unique hexpl
  simp only [zero_mul, Real.exp_zero, mul_one] at huniq
  rw [ha] at huniq
  convert huniq using 1
  ring

/-- Gas expectations only see neutral configurations. -/
theorem gasExpectation_congr_neutral (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) {F F' : (V → ℤ) → ℝ} (h : ∀ q : V → ℤ, ∑ j, q j = 0 → F q = F' q) :
    gasExpectationInternal N T κ lam F = gasExpectationInternal N T κ lam F' := by
  unfold gasExpectationInternal
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold gasWeightInternal
  split_ifs with hq
  · rw [h q hq]
  · simp

/-- The potential of `f = -Δ g` is `g` up to a constant, and `⟨f, C f⟩` is the Dirichlet
energy of `g`. -/
theorem neg_pseudoinverse_neg_laplacian {E : Type*} [Fintype E] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (T : (V → ℝ) →ₗ[ℝ] V → ℝ)
    (hT : G.IsLaplacianPseudoinverse T) (g : V → ℝ) :
    ∃ m : ℝ, (∀ j, -(T (-G.laplacian g) j) = g j - m) ∧
      ∑ j, -G.laplacian g j * -(T (-G.laplacian g) j) = ∑ e, (g (G.src e) - g (G.tgt e)) ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.mpr hG.nonempty
  set m : ℝ := (∑ j, g j) / Fintype.card V with hm
  set g₀ : V → ℝ := fun j => g j - m with hg₀
  have hsum : ∑ j, g₀ j = 0 := by
    simp only [hg₀, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
    field_simp
    ring
  have hlap : G.laplacian g₀ = G.laplacian g := by
    have h := (G.laplacianₗ ℝ).map_sub g (fun _ => m)
    simp only [Multigraph.laplacianₗ] at h
    have h' : G.laplacian (g - fun _ => m) = G.laplacian g - G.laplacian (fun _ : V => m) := h
    rw [Multigraph.laplacian_const, sub_zero] at h'
    exact h'
  have hTg : ∀ j, -(T (-G.laplacian g) j) = g₀ j := by
    intro j
    have h1 := ((hT.1 g₀ hsum).2)
    rw [hlap] at h1
    have : T (-G.laplacian g) = -T (G.laplacian g) := T.map_neg _
    rw [this, h1]
    simp
  refine ⟨m, hTg, ?_⟩
  simp_rw [hTg]
  have hpair := Multigraph.energy_eq_neg_pairing_laplacian G g₀
  rw [hlap] at hpair
  have hen : G.energy g₀ = ∑ e, (g (G.src e) - g (G.tgt e)) ^ 2 := by
    unfold Multigraph.energy Multigraph.grad
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hg₀]
    ring
  rw [← hen, hpair]
  unfold Multigraph.pairing
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- FS81 (1.15)–(1.16) read in the other direction: the charge characteristic functional of the
neutral gas is a sine-Gordon GFF expectation,
`⟨cos ⟨q, g⟩⟩_Λ = e^{-‖∇g‖²/(2κ)} ⟨e^{φ(-Δ g)/κ}⟩^φ_Λ` for every test function `g`. -/
theorem gasExpectation_cos_eq_sineGordon {E : Type*} [Fintype E] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T) (g : V → ℝ) :
    gasExpectationInternal N T κ lam (fun q => Real.cos (∑ j, (q j : ℝ) * g j)) =
      Real.exp (-(∑ e, (g (G.src e) - g (G.tgt e)) ^ 2) / (2 * κ)) *
        weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v
          (fun j => sineGordonWeightInternal N (lam j))
          (fun φ => Real.exp (∑ j, φ j * (-G.laplacian g j / κ))) := by
  obtain ⟨m, hpot, hQ⟩ := neg_pseudoinverse_neg_laplacian G hG T hT g
  set f : V → ℝ := fun j => -G.laplacian g j / κ with hfdef
  have hf : ∑ j, f j = 0 := by
    simp only [hfdef, ← Finset.sum_div, Finset.sum_neg_distrib, G.sum_laplacian_eq_zero,
      neg_zero, zero_div]
  have hfκ : f = κ⁻¹ • -G.laplacian g := by
    funext j; simp [hfdef, div_eq_inv_mul]
  have hTf : ∀ j, -(T f j) = (g j - m) / κ := by
    intro j
    rw [hfκ, T.map_smul, Pi.smul_apply, smul_eq_mul, ← hpot j]
    ring
  have hrep := weightedGFFExpectation_exp_sineGordon G hG κ hκ v N lam hlam T hT f hf
  have hQf : κ * (∑ j, f j * -(T f j)) / 2 =
      (∑ e, (g (G.src e) - g (G.tgt e)) ^ 2) / (2 * κ) := by
    rw [← hQ]
    simp_rw [hTf, hpot]
    simp only [hfdef, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have hcos : gasExpectationInternal N T κ lam
      (fun q => Real.cos (κ * ∑ j, (q j : ℝ) * -(T f j))) =
      gasExpectationInternal N T κ lam (fun q => Real.cos (∑ j, (q j : ℝ) * g j)) := by
    refine gasExpectation_congr_neutral N T κ lam fun q hq => ?_
    have hqR : ∑ j, (q j : ℝ) = 0 := by exact_mod_cast hq
    congr 1
    simp_rw [hTf]
    rw [Finset.mul_sum]
    have : ∑ j, κ * ((q j : ℝ) * ((g j - m) / κ)) = ∑ j, (q j : ℝ) * g j - m * ∑ j, (q j : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [this, hqR, mul_zero, sub_zero]
  rw [hQf, hcos] at hrep
  rw [hrep, ← mul_assoc, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, one_mul]

/-- The charge-fluctuation bound in Dirichlet-energy form: if
`⟨(κ ⟨q, C f⟩)²⟩_Λ ≤ δ κ ⟨f, C f⟩` for every zero-sum `f`, then
`⟨⟨q, g⟩²⟩_Λ ≤ (δ/κ) ∑_{edges} (g_j - g_ℓ)²` for every `g`. -/
theorem gasExpectation_pairing_sq_le_energy {E : Type*} [Fintype E] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ)
    (hT : G.IsLaplacianPseudoinverse T) (κ : ℝ) (hκ : 0 < κ) (lam : V → ℤ → ℝ) (δ : ℝ)
    (hf : ∀ f : V → ℝ, ∑ j, f j = 0 →
      gasExpectationInternal N T κ lam (fun q => (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2) ≤
        δ * κ * ∑ j, f j * -(T f j))
    (g : V → ℝ) :
    gasExpectationInternal N T κ lam (fun q => (∑ j, (q j : ℝ) * g j) ^ 2) ≤
      δ / κ * ∑ e, (g (G.src e) - g (G.tgt e)) ^ 2 := by
  obtain ⟨m, hpot, hQ⟩ := neg_pseudoinverse_neg_laplacian G hG T hT g
  have hsum : ∑ j, -G.laplacian g j = 0 := by
    rw [Finset.sum_neg_distrib, G.sum_laplacian_eq_zero, neg_zero]
  have h := hf (fun j => -G.laplacian g j) hsum
  have hfun : (fun j => -G.laplacian g j) = -G.laplacian g := rfl
  have hscale : gasExpectationInternal N T κ lam
      (fun q => (κ * ∑ j, (q j : ℝ) * -(T (-G.laplacian g) j)) ^ 2) =
      κ ^ 2 * gasExpectationInternal N T κ lam
        (fun q => (∑ j, (q j : ℝ) * -(T (-G.laplacian g) j)) ^ 2) := by
    rw [← gasExpectation_const_mul]
    congr 1
    funext q
    ring
  rw [hfun, hQ, hscale] at h
  have hcongr := gasExpectation_congr_neutral N T κ lam
    (F := fun q => (∑ j, (q j : ℝ) * -(T (-G.laplacian g) j)) ^ 2)
    (F' := fun q => (∑ j, (q j : ℝ) * g j) ^ 2) (fun q hq => by
      have hqR : ∑ j, (q j : ℝ) = 0 := by exact_mod_cast hq
      congr 1
      simp_rw [hpot, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hqR, zero_mul,
        sub_zero])
  rw [hcongr] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  nlinarith

/-- `Z_Λ > 0` for nonnegative charge weights with a positive vacancy weight (FS81 p. 530: the
physical gas has a positive a priori measure). -/
theorem gasPartition_pos (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (hnn : ∀ j n, 0 ≤ lam j n) (h0 : ∀ j, 0 < lam j 0) : 0 < gasPartitionInternal N T κ lam := by
  unfold gasPartitionInternal
  refine Finset.sum_pos' (fun q _ => ?_) ⟨0, ?_, ?_⟩
  · unfold gasWeightInternal
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg fun j _ => hnn j _) (Real.exp_pos _).le
    · exact le_rfl
  · simp [chargeConfigsInternal, Fintype.mem_piFinset]
  · unfold gasWeightInternal
    simp only [Pi.zero_apply, Finset.sum_const_zero, ite_true]
    exact mul_pos (Finset.prod_pos fun j _ => h0 j) (Real.exp_pos _)

end Gas

/-! ### The hard-core gas: the finite-volume screening obstruction -/

omit [Fintype W] in
theorem regionHardCoreWeight_nonneg (A : Finset W) {z : ℝ} (hz : 0 ≤ z) (j : W) (n : ℤ) :
    0 ≤ regionWeightInternal A (hardCoreWeightInternal z) j n := by
  unfold regionWeightInternal hardCoreWeightInternal
  split_ifs <;> positivity

/-- FS81 (1.17) for the hard-core gas with `z ≥ 0`, any `κ > 0`, any finite connected domain:
`⟨φ(f)²⟩_Λ = κ ⟨f, C f⟩ - κ² ⟨⟨q, C f⟩²⟩_Λ`. -/
theorem hardCore_secondMoment_eq (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected)
    (κ : ℝ) (hκ : 0 < κ) (v : W) (A : Finset W) (z : ℝ) (hz : 0 ≤ z)
    (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (hT : Λ.IsLaplacianPseudoinverse T)
    (f : W → ℝ) (hf : ∑ j, f j = 0) :
    weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v (hardCoreSineGordonInternal A z)
        (fun φ => (∑ j, φ j * f j) ^ 2) =
      κ * (∑ j, f j * -(T f j)) -
        κ ^ 2 * gasExpectationInternal 1 T κ (regionWeightInternal A (hardCoreWeightInternal z))
          (fun q => (∑ j, (q j : ℝ) * -(T f j)) ^ 2) := by
  have hZ := gasPartition_pos 1 T κ (regionWeightInternal A (hardCoreWeightInternal z))
    (regionHardCoreWeight_nonneg A hz) (fun j => by
      simp [regionWeightInternal, hardCoreWeightInternal])
  rw [weightedGFFExpectation_sq_sineGordon Λ hΛ κ hκ v 1 _
    (regionWeight_neg A (hardCoreWeight_neg z)) T hT f hf hZ.ne', ← gasExpectation_const_mul]
  congr 2
  funext q
  ring

/-- The finite-volume screening obstruction on one domain: the charge fluctuations of the
hard-core gas are at most `δ/κ` times the Dirichlet energy of the test function. -/
def HardCoreChargeFluctuationBoundInternal (Λ : Multigraph W E) (δ α κ₀ : ℝ) : Prop :=
  ∀ (A : Finset W) (κ : ℝ), 0 < κ → κ₀ < κ →
    ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      ∀ T : (W → ℝ) →ₗ[ℝ] W → ℝ, Λ.IsLaplacianPseudoinverse T → ∀ g : W → ℝ,
        gasExpectationInternal 1 T κ (regionWeightInternal A (hardCoreWeightInternal z))
            (fun q => (∑ j, (q j : ℝ) * g j) ^ 2) ≤
          δ / κ * ∑ e, (g (Λ.src e) - g (Λ.tgt e)) ^ 2

theorem hardCoreChargeFluctuationBound_of_expMomentBound (Λ : Multigraph W E)
    (hΛ : Λ.toSimpleGraph.Connected) (δ α κ₀ : ℝ)
    (h : HardCoreExpMomentBoundInternal Λ hΛ δ α κ₀) :
    HardCoreChargeFluctuationBoundInternal Λ δ α κ₀ := by
  intro A κ hκ hκ₀ z hz hzκ T hT g
  obtain ⟨v⟩ := hΛ.nonempty
  obtain ⟨hZ, hbd⟩ := h v A κ hκ hκ₀ z hz hzκ
  have hlam := regionWeight_neg A (hardCoreWeight_neg z)
  have hZgas : gasPartitionInternal 1 T κ (regionWeightInternal A (hardCoreWeightInternal z)) ≠ 0 := by
    rw [← weightedGFFNormalizer_sineGordon Λ hΛ κ hκ v 1 _ hlam T hT]
    exact hZ.ne'
  exact gasExpectation_pairing_sq_le_energy Λ hΛ 1 T hT κ hκ _ δ
    (fun f hf => gasExpectation_sq_le_of_expMoment Λ hΛ κ hκ v 1 _ hlam T hT f hf δ hZgas
      (hbd T hT f hf)) g

/-- **The finite-volume obstruction to Debye screening** (FS81 Theorem A with (1.17), J
pp. 531–532 and 567): for each `δ > 0` and `α` there is `κ₀`, independent of the volume, such
that for the hard-core gas on free and even periodic squares, `κ > κ₀`, `0 ≤ z ≤ e^{κ/17 + α}`
and every test function `g`, `⟨⟨q, g⟩²⟩_Λ ≤ (δ/κ) ∑_{edges} (g_j - g_ℓ)²`. Debye screening (the
Stillinger–Lovett sum rule (1.18)) would make the left side `≈ κ⁻¹ ∑ (g_j - g_ℓ)²` for slowly
varying `g`. -/
theorem hardCore_chargeFluctuation_bound (δ : ℝ) (hδ : 0 < δ) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ L : ℕ, 1 < L →
      HardCoreChargeFluctuationBoundInternal (squareFree L) δ α κ₀ ∧
        (Even L → HardCoreChargeFluctuationBoundInternal (squarePeriodic L) δ α κ₀) := by
  obtain ⟨κ₀, hκ₀, h⟩ := hardCore_expMoment_lower_bound δ hδ α
  exact ⟨κ₀, hκ₀, fun L hL =>
    ⟨hardCoreChargeFluctuationBound_of_expMomentBound _ _ δ α κ₀ (h L hL).1,
      fun he => hardCoreChargeFluctuationBound_of_expMomentBound _ _ δ α κ₀ ((h L hL).2 he)⟩⟩

end FroehlichSpencer.BKT.Coulomb
