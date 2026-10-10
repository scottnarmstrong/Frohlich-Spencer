/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.JensenIntegral

/-!
# the lower bound for one ensemble, and for a countable mixture

`ensemble_lower_bound` chains, for one ensemble of currents on an abstract finite gauge complex:

1. the real translation `θ → θ + τ` (FS82 (3.24)–(3.30)), with `c τ + φ = ε`;
2. neutrality (3.20): the non-neutral currents drop out;
3. the renormalization identity (3.38);
4. the Jensen bound (3.49);
5. steps 3 and 2 backwards at `ε = 0`.

The result is `∫ ∏ (1 + K_i cos 2π(ρ_i, θ)) W_φ ≥ e^{−Err} ∫ ∏ (1 + K_i cos 2π(ρ_i, θ)) W_0`, which is
`𝒥_γ(ε) ≥ e^{−Err} 𝒥_γ(0)` in the notation of (3.49).

`mixture_lower_bound` passes the bound through an absolutely summable expansion
`pin = Σ_γ F_γ` with nonnegative-weight terms (FS82 (3.51)).
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN.Torus

noncomputable section

local instance ensembleBound_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance ensembleBound_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance ensembleBound_isProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem coe_int_eq_zero (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
  have h : ((n : ℝ) : UnitAddCircle) = n • ((1 : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_one]
  rw [h, AddCircle.coe_period, smul_zero]

variable {E P ι : Type*} [Fintype E] [Fintype P] [Fintype ι]

/-- The Wilson weight is invariant along an integer direction annihilated by every plaquette. -/
theorem wilsonWeight_add_dir (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (g : E → ℤ)
    (hg : ∀ p, ∑ e, c p e * g e = 0) (θ : E → UnitAddCircle) (u : UnitAddCircle) :
    wilsonWeight β c ε (θ + fun e => g e • u) = wilsonWeight β c ε θ := by
  unfold wilsonWeight
  refine Finset.prod_congr rfl fun p _ => ?_
  unfold flux
  rw [pair_add, pair_zsmul_dir, hg p, zero_smul, add_zero]

/-- The real translation: `W_φ(θ + τ) = W_{φ + cτ}(θ)`. -/
theorem wilsonWeight_translate (β : ℝ) (c : P → E → ℤ) (φ ε : P → ℝ) (τ : E → ℝ)
    (hτ : ∀ p, ∑ e, (c p e : ℝ) * τ e + φ p = ε p) (θ : E → UnitAddCircle) :
    wilsonWeight β c φ (θ + fun e => (τ e : UnitAddCircle)) = wilsonWeight β c ε θ := by
  unfold wilsonWeight
  refine Finset.prod_congr rfl fun p _ => ?_
  unfold flux
  rw [pair_add, pair_coe, add_assoc, ← AddCircle.coe_add, hτ p]

theorem cosFactor_translate (K : ℝ) (ρ : E → ℤ) (τ : E → ℝ) (θ : E → UnitAddCircle) :
    cosFactor K ρ 0 (θ + fun e => (τ e : UnitAddCircle)) =
      cosFactor K ρ (∑ e, (ρ e : ℝ) * τ e) θ := by
  unfold cosFactor
  rw [pair_add, pair_coe, AddCircle.coe_zero, add_zero]

theorem cosFactor_congr_int (K : ℝ) (ρ : E → ℤ) {δ δ' : ℝ} (h : ∃ n : ℤ, δ = δ' + n)
    (θ : E → UnitAddCircle) : cosFactor K ρ δ θ = cosFactor K ρ δ' θ := by
  obtain ⟨n, rfl⟩ := h
  unfold cosFactor
  rw [AddCircle.coe_add, coe_int_eq_zero, add_zero]

theorem abs_cosFactor_le {K : ℝ} (hK : 0 ≤ K) (ρ : E → ℤ) (δ : ℝ) (θ : E → UnitAddCircle) :
    |cosFactor K ρ δ θ| ≤ 1 + K := by
  unfold cosFactor
  have h := abs_le.mp (abs_cosC_le_one (pair ρ θ + (δ : UnitAddCircle)))
  rw [abs_le]
  constructor <;> nlinarith [h.1, h.2]

/-- **The lower bound for one ensemble** (FS82 (3.28)–(3.49)). -/
theorem ensemble_lower_bound [DecidableEq ι] {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ)
    (φ ε : P → ℝ) (τ : E → ℝ) (hτ : ∀ p, ∑ e, (c p e : ℝ) * τ e + φ p = ε p)
    (K : ι → ℝ) (ρ : ι → E → ℤ)
    (neutral : ι → Prop) [DecidablePred neutral] (g : ι → E → ℤ)
    (hgauge : ∀ i, ¬ neutral i → ∀ p, ∑ e, c p e * g i e = 0)
    (hne : ∀ i, ¬ neutral i → ∑ e, ρ i e * g i e ≠ 0)
    (hzero : ∀ i j, ¬ neutral i → j ≠ i → ∑ e, ρ j e * g i e = 0)
    (a : ι → E → ℝ)
    (hcross : ∀ i j, neutral i → neutral j → i ≠ j → ∑ x, (ρ i x : ℝ) * a j x = 0)
    (hplaq : ∀ p i j, neutral i → neutral j → i ≠ j →
      plaqShift c (a i) p = 0 ∨ plaqShift c (a j) p = 0)
    (hK0 : ∀ i, neutral i → 0 ≤ K i)
    (hz : ∀ i, neutral i → K i * attenuation β c (ρ i) (a i) ≤ 1 / 2)
    (d : ι → ℝ) (hd : ∀ i, neutral i → ∃ n : ℤ, ∑ e, (ρ i e : ℝ) * τ e = d i + n)
    (Err : ℝ)
    (hErr : ∑ i ∈ Finset.univ.filter neutral, 3 * (K i * attenuation β c (ρ i) (a i)) *
          (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (d i) ^ 2) +
        β / 2 * ∑ p, (2 * Real.pi * ε p) ^ 2 ≤ Err) :
    Real.exp (-Err) * ∫ θ, (∏ i, cosFactor (K i) (ρ i) 0 θ) * wilsonWeight β c (fun _ => 0) θ ≤
      ∫ θ, (∏ i, cosFactor (K i) (ρ i) 0 θ) * wilsonWeight β c φ θ := by
  classical
  -- step 1: translation
  have h1 : ∫ θ, (∏ i, cosFactor (K i) (ρ i) 0 θ) * wilsonWeight β c φ θ =
      ∫ θ, (∏ i, cosFactor (K i) (ρ i) (∑ e, (ρ i e : ℝ) * τ e) θ) * wilsonWeight β c ε θ := by
    rw [← integral_translate (fun θ : E → UnitAddCircle =>
      (∏ i, cosFactor (K i) (ρ i) 0 θ) * wilsonWeight β c φ θ) (fun e => (τ e : UnitAddCircle))]
    congr 1
    funext θ
    rw [wilsonWeight_translate β c φ ε τ hτ]
    congr 1
    exact Finset.prod_congr rfl fun i _ => cosFactor_translate _ _ _ _
  -- step 2: neutrality, for both fields
  have h2 : ∀ (ε' : P → ℝ) (δ' : ι → ℝ),
      ∫ θ, (∏ i, cosFactor (K i) (ρ i) (δ' i) θ) * wilsonWeight β c ε' θ =
        ∫ θ, (∏ i ∈ Finset.univ.filter neutral, cosFactor (K i) (ρ i) (δ' i) θ) *
          wilsonWeight β c ε' θ := fun ε' δ' =>
    integral_prod_cosFactor_neutral K ρ δ' _ (continuous_wilsonWeight β c ε') neutral g
      (fun i hi θ u => wilsonWeight_add_dir β c ε' (g i) (hgauge i hi) θ u) hne hzero
  -- the neutral currents as a family
  have hsub : ∀ (f : ι → ℝ), ∏ i ∈ Finset.univ.filter neutral, f i =
      ∏ i : {i // neutral i}, f i.1 := fun f =>
    Finset.prod_subtype (Finset.univ.filter neutral) (fun i => by simp) f
  have hsubsum : ∀ (f : ι → ℝ), ∑ i ∈ Finset.univ.filter neutral, f i =
      ∑ i : {i // neutral i}, f i.1 := fun f =>
    Finset.sum_subtype (Finset.univ.filter neutral) (fun i => by simp) f
  -- step 3: the renormalization identity on the neutral family
  have h3 : ∀ (ε' : P → ℝ) (δ' : ι → ℝ),
      ∫ θ, (∏ i ∈ Finset.univ.filter neutral, cosFactor (K i) (ρ i) (δ' i) θ) *
          wilsonWeight β c ε' θ =
        ∫ θ, (∏ i : {i // neutral i}, (1 + K i.1 * attenuation β c (ρ i.1) (a i.1) *
          renormF β c ε' (ρ i.1) (δ' i.1) (a i.1) θ)) * wilsonWeight β c ε' θ := by
    intro ε' δ'
    simp_rw [hsub]
    exact integral_cosFactor_eq_renorm β c ε' (fun i : {i // neutral i} => K i.1)
      (fun i => ρ i.1) (fun i => δ' i.1) (fun i => a i.1)
      (fun i j hij => hcross i.1 j.1 i.2 j.2 (fun h => hij (Subtype.ext h)))
      (fun p i j hij => hplaq p i.1 j.1 i.2 j.2 (fun h => hij (Subtype.ext h)))
  -- the phases of the neutral currents
  have hphase : ∫ θ, (∏ i ∈ Finset.univ.filter neutral,
        cosFactor (K i) (ρ i) (∑ e, (ρ i e : ℝ) * τ e) θ) * wilsonWeight β c ε θ =
      ∫ θ, (∏ i ∈ Finset.univ.filter neutral, cosFactor (K i) (ρ i) (d i) θ) *
        wilsonWeight β c ε θ := by
    congr 1
    funext θ
    congr 1
    exact Finset.prod_congr rfl fun i hi =>
      cosFactor_congr_int _ _ (hd i (Finset.mem_filter.mp hi).2) θ
  -- step 4: Jensen
  have hz0 : ∀ i : {i // neutral i}, 0 ≤ K i.1 * attenuation β c (ρ i.1) (a i.1) := fun i =>
    mul_nonneg (hK0 i.1 i.2) (attenuation_pos β c _ _).le
  have h4 := integral_renorm_jensen hβ c ε
    (fun i : {i // neutral i} => K i.1 * attenuation β c (ρ i.1) (a i.1)) hz0
    (fun i => hz i.1 i.2) (fun i => ρ i.1) (fun i => d i.1) (fun i => a i.1)
  have hErr' : ∑ i : {i // neutral i}, 3 * (K i.1 * attenuation β c (ρ i.1) (a i.1)) *
          (2 * shiftK2 β c (a i.1) ε + 12 * shiftK1 β c (a i.1) ε (d i.1) ^ 2) +
        β / 2 * ∑ p, (2 * Real.pi * ε p) ^ 2 ≤ Err := by
    rw [← hsubsum (fun i => 3 * (K i * attenuation β c (ρ i) (a i)) *
      (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (d i) ^ 2))]
    exact hErr
  have hnonneg : 0 ≤ ∫ θ, (∏ i : {i // neutral i},
      (1 + K i.1 * attenuation β c (ρ i.1) (a i.1) *
        renormF β c (fun _ => 0) (ρ i.1) 0 (a i.1) θ)) * wilsonWeight β c (fun _ => 0) θ := by
    refine integral_nonneg fun θ => mul_nonneg (Finset.prod_nonneg fun i _ => ?_)
      (wilsonWeight_pos β c _ θ).le
    exact (renormFactor_pos hβ c _ (ρ i.1) 0 (a i.1) θ (hz0 i) (hz i.1 i.2)).le
  rw [h1, h2 ε, hphase, h3 ε d, h2 (fun _ => 0) (fun _ => 0), h3 (fun _ => 0) (fun _ => 0)]
  refine le_trans ?_ h4
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hErr')) hnonneg

/-! ### Countable mixtures -/

/-- **A termwise lower bound passes to an absolutely summable expansion** (FS82 (3.51)). -/
theorem mixture_lower_bound {Γ : Type*} [Countable Γ]
    (F : Γ → (E → UnitAddCircle) → ℝ) (hF : ∀ γ, Continuous (F γ))
    (bound : Γ → ℝ) (hbound : ∀ γ θ, |F γ θ| ≤ bound γ) (hsum : Summable bound)
    (pin : (E → UnitAddCircle) → ℝ) (hpin : ∀ θ, HasSum (fun γ => F γ θ) (pin θ))
    (W W0 : (E → UnitAddCircle) → ℝ) (hW : Continuous W) (hW0 : Continuous W0) (C : ℝ)
    (hterm : ∀ γ, C * ∫ θ, F γ θ * W0 θ ≤ ∫ θ, F γ θ * W θ) :
    C * ∫ θ, pin θ * W0 θ ≤ ∫ θ, pin θ * W θ := by
  have key : ∀ V : (E → UnitAddCircle) → ℝ, Continuous V →
      HasSum (fun γ => ∫ θ, F γ θ * V θ) (∫ θ, pin θ * V θ) := by
    intro V hV
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hV.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (fun _ => 0) (Set.mem_univ _))
    have hint : ∀ γ, Integrable fun θ => F γ θ * V θ := fun γ =>
      integrable_of_continuous _ ((hF γ).mul hV)
    have hnorm : Summable fun γ => ∫ θ, ‖F γ θ * V θ‖ := by
      refine Summable.of_nonneg_of_le (fun γ => integral_nonneg fun θ => norm_nonneg _)
        (fun γ => ?_) (hsum.mul_right B)
      have hle : ∀ θ : E → UnitAddCircle, ‖F γ θ * V θ‖ ≤ bound γ * B := by
        intro θ
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hbound γ θ) (hB θ (Set.mem_univ _)) (norm_nonneg _)
          ((abs_nonneg _).trans (hbound γ θ))
      calc ∫ θ, ‖F γ θ * V θ‖ ≤ ∫ _θ : E → UnitAddCircle, bound γ * B :=
            integral_mono (hint γ).norm (integrable_const _) hle
        _ = bound γ * B := by simp
    have h := hasSum_integral_of_summable_integral_norm hint hnorm
    have heq : (fun θ => ∑' γ, F γ θ * V θ) = fun θ => pin θ * V θ := by
      funext θ
      rw [tsum_mul_right, (hpin θ).tsum_eq]
    rwa [heq] at h
  have h0 := (key W0 hW0).mul_left C
  have h1 := key W hW
  exact hasSum_le hterm h0 h1

end

end FroehlichSpencer.FS82.ZN.Torus

end
