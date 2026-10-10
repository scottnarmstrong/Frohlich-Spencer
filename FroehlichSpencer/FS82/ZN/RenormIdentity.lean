/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.WilsonShift

/-!
# neutrality and the renormalization identity (3.38)

For an abstract finite gauge complex (links `E`, plaquettes `P`, incidence `c`) and a finite family
of currents `ρ_i : E → ℤ` with coefficients `K_i` and phase offsets `δ_i`:

* `integral_prod_cosFactor_neutral` (FS82 (3.20)).

A factor `1 + K_i cos(2π((ρ_i, θ) + δ_i))` can
  be dropped from the integral against a function `G` when there is an integer direction `g` with
  `G(θ + g u) = G(θ)`, `(ρ_i, g) ≠ 0` and `(ρ_j, g) = 0` for the other currents.

For the Wilson
  weight the directions are the gauge transformations at vertices.
* `integral_cosFactor_eq_renorm` (FS82 (3.38)).

Given real shift vectors `a_i` on the links with
  `(ρ_i, a_j) = 0` for `i ≠ j`, and such that no plaquette is shifted by two different currents,
  `∫ ∏_i [1 + K_i cos(…)] W = ∫ ∏_i [1 + K_i A_i F_i] W`, where `A_i = attenuation` is
  `e^{−(ρ_i, a_i)} ∏_p e^{β(cosh η_{i,p} − 1)}`, `η_{i,p} = Σ_x c_p(x) a_i(x)`, and
  `F_i = renormF` is the real part of `e^{2πi((ρ_i,θ)+δ_i)} ∏_p i_β(η_{i,p}; ·)`, the function
  `F` of (3.36).
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN.Torus

noncomputable section

local instance renormIdentity_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance renormIdentity_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance renormIdentity_isAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance renormIdentity_isProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### The unit character -/

/-- `e^{2πi x}` as a function on `ℝ/ℤ`. -/
def eC (z : UnitAddCircle) : ℂ := fourier (T := (1 : ℝ)) 1 z

theorem eC_coe (x : ℝ) :
    eC (x : UnitAddCircle) = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) :=
  fourier_one_coe x

theorem continuous_eC : Continuous eC := (fourier (T := (1 : ℝ)) 1).continuous

@[simp] theorem eC_zero : eC 0 = 1 := by
  have h := eC_coe 0
  simpa using h

theorem eC_add (x y : UnitAddCircle) : eC (x + y) = eC x * eC y := by
  obtain ⟨a, rfl⟩ := exists_real_lift x
  obtain ⟨b, rfl⟩ := exists_real_lift y
  rw [← AddCircle.coe_add, eC_coe, eC_coe, eC_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eC_neg (x : UnitAddCircle) : eC (-x) = (starRingEnd ℂ) (eC x) := by
  obtain ⟨a, rfl⟩ := exists_real_lift x
  rw [← AddCircle.coe_neg, eC_coe, eC_coe, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem eC_sum {κ : Type*} (s : Finset κ) (x : κ → UnitAddCircle) :
    eC (∑ i ∈ s, x i) = ∏ i ∈ s, eC (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, eC_add, ih]

theorem cosC_eq_re_eC (z : UnitAddCircle) : cosC z = (eC z).re := rfl

theorem ofReal_cosC (z : UnitAddCircle) :
    ((cosC z : ℝ) : ℂ) = (eC z + (starRingEnd ℂ) (eC z)) / 2 := by
  rw [cosC_eq_re_eC, Complex.re_eq_add_conj]

variable {E P ι : Type*} [Fintype E] [Fintype P] [Fintype ι]

theorem chi_eq_eC (m : E → ℤ) (θ : E → UnitAddCircle) : chi m θ = eC (pair m θ) := rfl

/-! ### Neutrality -/

/-- The factor `1 + K cos(2π((ρ, θ) + δ))` of one current. -/
def cosFactor (K : ℝ) (ρ : E → ℤ) (δ : ℝ) (θ : E → UnitAddCircle) : ℝ :=
  1 + K * cosC (pair ρ θ + (δ : UnitAddCircle))

theorem continuous_cosFactor (K : ℝ) (ρ : E → ℤ) (δ : ℝ) :
    Continuous (cosFactor K ρ δ) := by
  unfold cosFactor
  exact continuous_const.add (continuous_const.mul
    (continuous_cosC.comp ((continuous_pair ρ).add continuous_const)))

theorem integral_one_add_cosC (K : ℝ) (z : UnitAddCircle) {n : ℤ} (hn : n ≠ 0) :
    ∫ u : UnitAddCircle, (1 + K * cosC (z + n • u)) = 1 := by
  have hc : Continuous fun u : UnitAddCircle => K * cosC (z + n • u) :=
    continuous_const.mul (continuous_cosC.comp (continuous_const.add (continuous_id.zsmul n)))
  have hint : Integrable fun u : UnitAddCircle => K * cosC (z + n • u) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add (integrable_const _) hint, integral_const_mul, integral_cosC_add_zsmul z hn]
  simp

omit [Fintype ι] in
/-- One non-neutral current is removed by averaging along its direction. -/
theorem integral_prod_cosFactor_insert [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∉ s)
    (K : ι → ℝ) (ρ : ι → E → ℤ) (δ : ι → ℝ)
    (G : (E → UnitAddCircle) → ℝ) (hG : Continuous G) (g : E → ℤ)
    (hGinv : ∀ (θ : E → UnitAddCircle) (u : UnitAddCircle), G (θ + fun e => g e • u) = G θ)
    (hne : ∑ e, ρ i e * g e ≠ 0) (hzero : ∀ j ∈ s, ∑ e, ρ j e * g e = 0) :
    ∫ θ, (∏ j ∈ insert i s, cosFactor (K j) (ρ j) (δ j) θ) * G θ =
      ∫ θ, (∏ j ∈ s, cosFactor (K j) (ρ j) (δ j) θ) * G θ := by
  have hD : Continuous (fun u : UnitAddCircle => (fun e => g e • u : E → UnitAddCircle)) :=
    continuous_pi fun e => continuous_id.zsmul (g e)
  have hcont : Continuous fun θ : E → UnitAddCircle =>
      (∏ j ∈ insert i s, cosFactor (K j) (ρ j) (δ j) θ) * G θ :=
    (continuous_finsetProd _ fun j _ => continuous_cosFactor _ _ _).mul hG
  rw [integral_average _ hcont _ hD]
  congr 1
  funext θ
  have hstep : ∀ u : UnitAddCircle,
      (∏ j ∈ insert i s, cosFactor (K j) (ρ j) (δ j) (θ + fun e => g e • u)) *
          G (θ + fun e => g e • u) =
        (1 + K i * cosC ((pair (ρ i) θ + (δ i : UnitAddCircle)) + (∑ e, ρ i e * g e) • u)) *
          ((∏ j ∈ s, cosFactor (K j) (ρ j) (δ j) θ) * G θ) := by
    intro u
    rw [Finset.prod_insert hi, hGinv, mul_assoc]
    congr 1
    · unfold cosFactor
      rw [pair_add, pair_zsmul_dir, add_right_comm]
    · congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      unfold cosFactor
      rw [pair_add, pair_zsmul_dir, hzero j hj, zero_smul, add_zero]
  simp_rw [hstep]
  rw [integral_mul_const, integral_one_add_cosC _ _ hne, one_mul]

/-- **Neutrality (FS82 (3.20)).** Every current that has a symmetry direction of `G` seen by it
alone drops out of the integral. -/
theorem integral_prod_cosFactor_neutral [DecidableEq ι] (K : ι → ℝ) (ρ : ι → E → ℤ) (δ : ι → ℝ)
    (G : (E → UnitAddCircle) → ℝ) (hG : Continuous G)
    (neutral : ι → Prop) [DecidablePred neutral] (g : ι → E → ℤ)
    (hGinv : ∀ i, ¬ neutral i → ∀ (θ : E → UnitAddCircle) (u : UnitAddCircle),
      G (θ + fun e => g i e • u) = G θ)
    (hne : ∀ i, ¬ neutral i → ∑ e, ρ i e * g i e ≠ 0)
    (hzero : ∀ i j, ¬ neutral i → j ≠ i → ∑ e, ρ j e * g i e = 0) :
    ∫ θ, (∏ j, cosFactor (K j) (ρ j) (δ j) θ) * G θ =
      ∫ θ, (∏ j ∈ Finset.univ.filter neutral, cosFactor (K j) (ρ j) (δ j) θ) * G θ := by
  have key : ∀ t : Finset ι, (∀ i ∈ t, ¬ neutral i) →
      ∫ θ, (∏ j ∈ Finset.univ.filter neutral ∪ t, cosFactor (K j) (ρ j) (δ j) θ) * G θ =
        ∫ θ, (∏ j ∈ Finset.univ.filter neutral, cosFactor (K j) (ρ j) (δ j) θ) * G θ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        simp
    | insert i t hi ih =>
        intro ht
        have hin : ¬ neutral i := ht i (Finset.mem_insert_self i t)
        have hnot : i ∉ Finset.univ.filter neutral ∪ t := by
          simp [hin, hi]
        rw [Finset.union_insert, integral_prod_cosFactor_insert _ i hnot K ρ δ G hG (g i)
          (hGinv i hin) (hne i hin)
          (fun j hj => hzero i j hin (by rintro rfl; exact hnot hj))]
        exact ih fun j hj => ht j (Finset.mem_insert_of_mem hj)
  have h := key (Finset.univ.filter fun i => ¬ neutral i)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hu : Finset.univ.filter neutral ∪ (Finset.univ.filter fun i => ¬ neutral i) =
      (Finset.univ : Finset ι) := by
    ext i
    simp [em]
  rw [hu] at h
  exact h

/-! ### The renormalized factor -/

/-- The imaginary shift of the plaquette `p` generated by the link shifts `a`. -/
def plaqShift (c : P → E → ℤ) (a : E → ℝ) (p : P) : ℝ :=
  ∑ x, (c p x : ℝ) * a x

/-- The attenuation of a current shifted with multiplicity `s`:
`e^{−s²(ρ, a)} ∏_p e^{β(cosh(s η_p) − 1)}`. -/
def attenuationAt (β : ℝ) (c : P → E → ℤ) (ρ : E → ℤ) (a : E → ℝ) (s : ℤ) : ℝ :=
  Real.exp (-((s : ℝ) ^ 2 * ∑ x, (ρ x : ℝ) * a x)) *
    ∏ p, Real.exp (β * (Real.cosh ((s : ℝ) * plaqShift c a p) - 1))

/-- The attenuation `e^{−(ρ, a)} ∏_p e^{β(cosh η_p − 1)}` of FS82 (3.35), (3.37). -/
def attenuation (β : ℝ) (c : P → E → ℤ) (ρ : E → ℤ) (a : E → ℝ) : ℝ :=
  Real.exp (-(∑ x, (ρ x : ℝ) * a x)) * ∏ p, Real.exp (β * (Real.cosh (plaqShift c a p) - 1))

theorem attenuation_pos (β : ℝ) (c : P → E → ℤ) (ρ : E → ℤ) (a : E → ℝ) :
    0 < attenuation β c ρ a :=
  mul_pos (Real.exp_pos _) (Finset.prod_pos fun _ _ => Real.exp_pos _)

theorem attenuationAt_zero (β : ℝ) (c : P → E → ℤ) (ρ : E → ℤ) (a : E → ℝ) :
    attenuationAt β c ρ a 0 = 1 := by
  simp [attenuationAt]

theorem attenuationAt_one (β : ℝ) (c : P → E → ℤ) (ρ : E → ℤ) (a : E → ℝ) :
    attenuationAt β c ρ a 1 = attenuation β c ρ a := by
  simp [attenuationAt, attenuation]

theorem attenuationAt_neg_one (β : ℝ) (c : P → E → ℤ) (ρ : E → ℤ) (a : E → ℝ) :
    attenuationAt β c ρ a (-1) = attenuation β c ρ a := by
  simp [attenuationAt, attenuation, Real.cosh_neg]

/-- The complex factor `e^{2πi((ρ,θ)+δ)} ∏_p i_β(η_p; flux_p θ + ε_p)`. -/
def renormU (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ) (δ : ℝ) (a : E → ℝ)
    (θ : E → UnitAddCircle) : ℂ :=
  eC (pair ρ θ + (δ : UnitAddCircle)) *
    ∏ p, shiftFactor β (plaqShift c a p) (flux c p θ + (ε p : UnitAddCircle))

/-- The real function `F(ρ; dθ + ε)` of FS82 (3.36). -/
def renormF (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ) (δ : ℝ) (a : E → ℝ)
    (θ : E → UnitAddCircle) : ℝ :=
  (renormU β c ε ρ δ a θ).re

theorem continuous_renormU (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ) (δ : ℝ)
    (a : E → ℝ) : Continuous (renormU β c ε ρ δ a) := by
  unfold renormU
  refine (continuous_eC.comp ((continuous_pair ρ).add continuous_const)).mul ?_
  exact continuous_finsetProd _ fun p _ =>
    (continuous_shiftFactor β _).comp ((continuous_flux c p).add continuous_const)

theorem continuous_renormF (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ) (δ : ℝ)
    (a : E → ℝ) : Continuous (renormF β c ε ρ δ a) :=
  Complex.continuous_re.comp (continuous_renormU β c ε ρ δ a)

theorem norm_eC (z : UnitAddCircle) : ‖eC z‖ = 1 := by
  obtain ⟨x, rfl⟩ := exists_real_lift z
  rw [eC_coe, Complex.norm_exp_ofReal_mul_I]

/-- FS82 after (3.36): `|F| ≤ 1`. -/
theorem norm_renormU_le_one {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ)
    (δ : ℝ) (a : E → ℝ) (θ : E → UnitAddCircle) : ‖renormU β c ε ρ δ a θ‖ ≤ 1 := by
  unfold renormU
  rw [norm_mul, norm_eC, one_mul, norm_prod]
  exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p _ => norm_shiftFactor_le_one hβ _ _)).trans_eq (by simp)

theorem abs_renormF_le_one {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ)
    (δ : ℝ) (a : E → ℝ) (θ : E → UnitAddCircle) : |renormF β c ε ρ δ a θ| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_renormU_le_one hβ c ε ρ δ a θ)

/-! ### One term of the expansion -/

omit [Fintype ι] in
theorem apply_sum_eq_prod_of_pairwise_zero {M : Type*} [CommMonoid M] (s : Finset ι)
    (g : ℝ → M) (hg : g 0 = 1) (t : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i = 0 ∨ t j = 0) :
    g (∑ i ∈ s, t i) = ∏ i ∈ s, g (t i) := by
  classical
  by_cases hall : ∀ i ∈ s, t i = 0
  · rw [Finset.sum_eq_zero hall, hg]
    exact (Finset.prod_eq_one fun i hi => by rw [hall i hi, hg]).symm
  · push Not at hall
    obtain ⟨i₀, hi₀, hne⟩ := hall
    have hothers : ∀ j ∈ s, j ≠ i₀ → t j = 0 := fun j hj hji =>
      (h j hj i₀ hi₀ hji).resolve_right hne
    rw [Finset.sum_eq_single_of_mem i₀ hi₀ hothers,
      Finset.prod_eq_single_of_mem i₀ hi₀ (fun j hj hji => by rw [hothers j hj hji, hg])]

theorem pair_sum_zsmul (s : ι → ℤ) (ρ : ι → E → ℤ) (θ : E → UnitAddCircle) :
    pair (fun x => ∑ i, s i * ρ i x) θ = ∑ i, s i • pair (ρ i) θ := by
  unfold pair
  simp_rw [Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

/-- **One term.** For integer multiplicities `s_i`, the product of the characters of the currents
against the Wilson weight equals the product of the attenuated, shifted characters. -/
theorem integral_character_term (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ)
    (ρ : ι → E → ℤ) (δ : ι → ℝ) (a : ι → E → ℝ)
    (hcross : ∀ i j, i ≠ j → ∑ x, (ρ i x : ℝ) * a j x = 0)
    (hplaq : ∀ p i j, i ≠ j → plaqShift c (a i) p = 0 ∨ plaqShift c (a j) p = 0)
    (s : ι → ℤ) :
    ∫ θ, (∏ i, eC (s i • (pair (ρ i) θ + (δ i : UnitAddCircle)))) *
        ((wilsonWeight β c ε θ : ℝ) : ℂ) =
      ∫ θ, (∏ i, ((attenuationAt β c (ρ i) (a i) (s i) : ℝ) : ℂ) *
          eC (s i • (pair (ρ i) θ + (δ i : UnitAddCircle))) *
          ∏ p, shiftFactor β ((s i : ℝ) * plaqShift c (a i) p)
            (flux c p θ + (ε p : UnitAddCircle))) * ((wilsonWeight β c ε θ : ℝ) : ℂ) := by
  classical
  set m : E → ℤ := fun x => ∑ i, s i * ρ i x with hm
  set A : E → ℝ := fun x => ∑ i, (s i : ℝ) * a i x with hA
  set D : ℝ := ∑ i, (s i : ℝ) * δ i with hD
  have hchar : ∀ θ : E → UnitAddCircle,
      (∏ i, eC (s i • (pair (ρ i) θ + (δ i : UnitAddCircle)))) =
        eC (D : UnitAddCircle) * chi m θ := by
    intro θ
    rw [← eC_sum, chi_eq_eC, ← eC_add]
    congr 1
    rw [hm, pair_sum_zsmul, hD]
    have hcoe : ((∑ i, (s i : ℝ) * δ i : ℝ) : UnitAddCircle) =
        ∑ i, s i • (δ i : UnitAddCircle) := by
      have h : ∀ i, s i • ((δ i : ℝ) : UnitAddCircle) = (((s i : ℝ) * δ i : ℝ) : UnitAddCircle) := by
        intro i
        rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
      simp_rw [h]
      exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        (fun i => (s i : ℝ) * δ i) Finset.univ
    rw [hcoe, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_add, add_comm]
  have hpair : ∑ x, (m x : ℝ) * A x = ∑ i, (s i : ℝ) ^ 2 * ∑ x, (ρ i x : ℝ) * a i x := by
    have h1 : ∀ x, (m x : ℝ) * A x =
        ∑ i, ∑ j, (s i : ℝ) * (s j : ℝ) * ((ρ i x : ℝ) * a j x) := by
      intro x
      rw [hm, hA]
      push_cast
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i]
    · rw [← Finset.mul_sum]
      ring
    · intro j _ hji
      rw [← Finset.mul_sum, hcross i j (Ne.symm hji), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hshift : ∀ p, (0 : ℝ) + ∑ x, (c p x : ℝ) * A x = ∑ i, (s i : ℝ) * plaqShift c (a i) p := by
    intro p
    rw [zero_add, hA]
    unfold plaqShift
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have hweight : ∀ θ : E → UnitAddCircle,
      (∏ i, ((attenuationAt β c (ρ i) (a i) (s i) : ℝ) : ℂ)) *
          (∏ i, ∏ p, shiftFactor β ((s i : ℝ) * plaqShift c (a i) p)
            (flux c p θ + (ε p : UnitAddCircle))) * ((wilsonWeight β c ε θ : ℝ) : ℂ) =
        ((Real.exp (-(∑ x, (m x : ℝ) * A x)) : ℝ) : ℂ) *
          shiftedWeight β c ε (fun p => 0 + ∑ x, (c p x : ℝ) * A x) θ := by
    intro θ
    have hSW : shiftedWeight β c ε (fun p => 0 + ∑ x, (c p x : ℝ) * A x) θ =
        ((wilsonWeight β c ε θ : ℝ) : ℂ) *
          ∏ p, ∏ i, (((Real.exp (β * (Real.cosh ((s i : ℝ) * plaqShift c (a i) p) - 1)) : ℝ) : ℂ) *
            shiftFactor β ((s i : ℝ) * plaqShift c (a i) p)
              (flux c p θ + (ε p : UnitAddCircle))) := by
      unfold shiftedWeight wilsonWeight
      rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      beta_reduce
      rw [hshift p, exp_cosShift, mul_assoc]
      congr 1
      exact apply_sum_eq_prod_of_pairwise_zero Finset.univ
        (fun t : ℝ => ((Real.exp (β * (Real.cosh t - 1)) : ℝ) : ℂ) *
          shiftFactor β t (flux c p θ + (ε p : UnitAddCircle)))
        (by simp) (fun i => (s i : ℝ) * plaqShift c (a i) p)
        (fun i _ j _ hij => by
          rcases hplaq p i j hij with h | h
          · exact Or.inl (by rw [h, mul_zero])
          · exact Or.inr (by rw [h, mul_zero]))
    have hatt : (∏ i, ((attenuationAt β c (ρ i) (a i) (s i) : ℝ) : ℂ)) =
        ((Real.exp (-(∑ x, (m x : ℝ) * A x)) : ℝ) : ℂ) *
          ∏ p, ∏ i, ((Real.exp (β * (Real.cosh ((s i : ℝ) * plaqShift c (a i) p) - 1)) : ℝ) : ℂ) := by
      rw [hpair, ← Finset.sum_neg_distrib, Real.exp_sum, Finset.prod_comm, Complex.ofReal_prod,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold attenuationAt
      push_cast
      rfl
    rw [hSW, hatt]
    simp_rw [Finset.prod_mul_distrib]
    rw [Finset.prod_comm (f := fun p i => shiftFactor β ((s i : ℝ) * plaqShift c (a i) p)
      (flux c p θ + (ε p : UnitAddCircle)))]
    ring
  have hL : ∀ θ : E → UnitAddCircle,
      (∏ i, eC (s i • (pair (ρ i) θ + (δ i : UnitAddCircle)))) *
          ((wilsonWeight β c ε θ : ℝ) : ℂ) =
        eC (D : UnitAddCircle) * (chi m θ * shiftedWeight β c ε (fun _ => 0) θ) := by
    intro θ
    rw [hchar θ, shiftedWeight_zero]
    ring
  have hR : ∀ θ : E → UnitAddCircle,
      (∏ i, ((attenuationAt β c (ρ i) (a i) (s i) : ℝ) : ℂ) *
          eC (s i • (pair (ρ i) θ + (δ i : UnitAddCircle))) *
          ∏ p, shiftFactor β ((s i : ℝ) * plaqShift c (a i) p)
            (flux c p θ + (ε p : UnitAddCircle))) * ((wilsonWeight β c ε θ : ℝ) : ℂ) =
        eC (D : UnitAddCircle) * (((Real.exp (-(∑ x, (m x : ℝ) * A x)) : ℝ) : ℂ) *
          (chi m θ * shiftedWeight β c ε (fun p => 0 + ∑ x, (c p x : ℝ) * A x) θ)) := by
    intro θ
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hchar θ]
    have h := hweight θ
    calc (∏ i, ((attenuationAt β c (ρ i) (a i) (s i) : ℝ) : ℂ)) * (eC (D : UnitAddCircle) * chi m θ) *
          (∏ i, ∏ p, shiftFactor β ((s i : ℝ) * plaqShift c (a i) p)
            (flux c p θ + (ε p : UnitAddCircle))) * ((wilsonWeight β c ε θ : ℝ) : ℂ)
        = eC (D : UnitAddCircle) * chi m θ *
            ((∏ i, ((attenuationAt β c (ρ i) (a i) (s i) : ℝ) : ℂ)) *
              (∏ i, ∏ p, shiftFactor β ((s i : ℝ) * plaqShift c (a i) p)
                (flux c p θ + (ε p : UnitAddCircle))) * ((wilsonWeight β c ε θ : ℝ) : ℂ)) := by
          ring
      _ = _ := by
          rw [h]
          ring
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_chi_shiftedWeight β c ε (fun _ => 0) m A]

/-! ### The identity (3.38) -/

/-- The multiplicity of the three terms of `1 + K cos`: `0`, `1`, `−1`. -/
def sgn3 (s : Fin 3) : ℤ := if s = 0 then 0 else if s = 1 then 1 else -1

/-- The coefficient of the three terms of `1 + K cos`: `1`, `K/2`, `K/2`. -/
def coef3 (K : ℝ) (s : Fin 3) : ℂ := if s = 0 then 1 else ((K / 2 : ℝ) : ℂ)

theorem cosFactor_eq_sum (K : ℝ) (ρ : E → ℤ) (δ : ℝ) (θ : E → UnitAddCircle) :
    ((cosFactor K ρ δ θ : ℝ) : ℂ) =
      ∑ s : Fin 3, coef3 K s * eC (sgn3 s • (pair ρ θ + (δ : UnitAddCircle))) := by
  have h0 : sgn3 0 = 0 := by simp [sgn3]
  have h1 : sgn3 1 = 1 := by simp [sgn3]
  have h2 : sgn3 2 = -1 := by simp [sgn3]
  have c0 : coef3 K 0 = 1 := by simp [coef3]
  have c1 : coef3 K 1 = ((K / 2 : ℝ) : ℂ) := by simp [coef3]
  have c2 : coef3 K 2 = ((K / 2 : ℝ) : ℂ) := by simp [coef3]
  rw [Fin.sum_univ_three, h0, h1, h2, c0, c1, c2, zero_smul, one_smul, neg_smul, one_smul,
    eC_zero, eC_neg]
  unfold cosFactor
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, ofReal_cosC]
  push_cast
  ring

/-- The three attenuated, shifted terms of one current add up to `1 + K A F`. -/
theorem sum_three_renorm (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (K : ℝ) (ρ : E → ℤ) (δ : ℝ)
    (a : E → ℝ) (θ : E → UnitAddCircle) :
    ∑ s : Fin 3, coef3 K s * (((attenuationAt β c ρ a (sgn3 s) : ℝ) : ℂ) *
        eC (sgn3 s • (pair ρ θ + (δ : UnitAddCircle))) *
        ∏ p, shiftFactor β ((sgn3 s : ℝ) * plaqShift c a p)
          (flux c p θ + (ε p : UnitAddCircle))) =
      ((1 + K * attenuation β c ρ a * renormF β c ε ρ δ a θ : ℝ) : ℂ) := by
  have h0 : sgn3 0 = 0 := by simp [sgn3]
  have h1 : sgn3 1 = 1 := by simp [sgn3]
  have h2 : sgn3 2 = -1 := by simp [sgn3]
  have c0 : coef3 K 0 = 1 := by simp [coef3]
  have c1 : coef3 K 1 = ((K / 2 : ℝ) : ℂ) := by simp [coef3]
  have c2 : coef3 K 2 = ((K / 2 : ℝ) : ℂ) := by simp [coef3]
  have hconj : (starRingEnd ℂ) (renormU β c ε ρ δ a θ) =
      eC (-(pair ρ θ + (δ : UnitAddCircle))) *
        ∏ p, shiftFactor β (-plaqShift c a p) (flux c p θ + (ε p : UnitAddCircle)) := by
    unfold renormU
    rw [map_mul, map_prod, eC_neg]
    congr 1
    exact Finset.prod_congr rfl fun p _ => (shiftFactor_neg_eta β _ _).symm
  have hre : ((renormF β c ε ρ δ a θ : ℝ) : ℂ) =
      (renormU β c ε ρ δ a θ + (starRingEnd ℂ) (renormU β c ε ρ δ a θ)) / 2 := by
    unfold renormF
    rw [Complex.re_eq_add_conj]
  rw [Fin.sum_univ_three, h0, h1, h2, c0, c1, c2, attenuationAt_zero, attenuationAt_one,
    attenuationAt_neg_one, zero_smul, one_smul, neg_smul, one_smul, eC_zero]
  simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, neg_mul,
    shiftFactor_zero, Finset.prod_const_one, mul_one, Complex.ofReal_one]
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_mul, hre, hconj]
  unfold renormU
  push_cast
  ring

theorem continuous_eC_zsmul (s : ℤ) (ρ : E → ℤ) (δ : ℝ) :
    Continuous fun θ : E → UnitAddCircle => eC (s • (pair ρ θ + (δ : UnitAddCircle))) :=
  continuous_eC.comp (((continuous_pair ρ).add continuous_const).zsmul s)

/-- **FS82 (3.38) for an abstract ensemble.** If the shift vectors of different currents do not
see each other's currents (`hcross`) and no plaquette is shifted by two of them (`hplaq`), the
factors `1 + K_i cos` may be replaced by `1 + K_i A_i F_i` under the integral against the Wilson
weight. -/
theorem integral_cosFactor_eq_renorm [DecidableEq ι] (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ)
    (K : ι → ℝ) (ρ : ι → E → ℤ) (δ : ι → ℝ) (a : ι → E → ℝ)
    (hcross : ∀ i j, i ≠ j → ∑ x, (ρ i x : ℝ) * a j x = 0)
    (hplaq : ∀ p i j, i ≠ j → plaqShift c (a i) p = 0 ∨ plaqShift c (a j) p = 0) :
    ∫ θ, (∏ i, cosFactor (K i) (ρ i) (δ i) θ) * wilsonWeight β c ε θ =
      ∫ θ, (∏ i, (1 + K i * attenuation β c (ρ i) (a i) *
        renormF β c ε (ρ i) (δ i) (a i) θ)) * wilsonWeight β c ε θ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  have hL : ∀ θ : E → UnitAddCircle,
      (((∏ i, cosFactor (K i) (ρ i) (δ i) θ) * wilsonWeight β c ε θ : ℝ) : ℂ) =
        ∑ σ : ι → Fin 3, (∏ i, coef3 (K i) (σ i)) *
          ((∏ i, eC (sgn3 (σ i) • (pair (ρ i) θ + (δ i : UnitAddCircle)))) *
            ((wilsonWeight β c ε θ : ℝ) : ℂ)) := by
    intro θ
    rw [Complex.ofReal_mul, Complex.ofReal_prod]
    simp_rw [cosFactor_eq_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  have hR : ∀ θ : E → UnitAddCircle,
      (((∏ i, (1 + K i * attenuation β c (ρ i) (a i) *
          renormF β c ε (ρ i) (δ i) (a i) θ)) * wilsonWeight β c ε θ : ℝ) : ℂ) =
        ∑ σ : ι → Fin 3, (∏ i, coef3 (K i) (σ i)) *
          ((∏ i, ((attenuationAt β c (ρ i) (a i) (sgn3 (σ i)) : ℝ) : ℂ) *
            eC (sgn3 (σ i) • (pair (ρ i) θ + (δ i : UnitAddCircle))) *
            ∏ p, shiftFactor β ((sgn3 (σ i) : ℝ) * plaqShift c (a i) p)
              (flux c p θ + (ε p : UnitAddCircle))) * ((wilsonWeight β c ε θ : ℝ) : ℂ)) := by
    intro θ
    rw [Complex.ofReal_mul, Complex.ofReal_prod]
    simp_rw [← sum_three_renorm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hL, hR]
  have hw : Continuous fun θ : E → UnitAddCircle => ((wilsonWeight β c ε θ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_wilsonWeight β c ε)
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_const_mul, integral_const_mul,
      integral_character_term β c ε ρ δ a hcross hplaq (fun i => sgn3 (σ i))]
  · intro σ _
    refine integrable_of_continuous _ (continuous_const.mul (Continuous.mul ?_ hw))
    exact continuous_finsetProd _ fun i _ =>
      (continuous_const.mul (continuous_eC_zsmul _ _ _)).mul
        (continuous_finsetProd _ fun p _ =>
          (continuous_shiftFactor β _).comp ((continuous_flux c p).add continuous_const))
  · intro σ _
    refine integrable_of_continuous _ (continuous_const.mul (Continuous.mul ?_ hw))
    exact continuous_finsetProd _ fun i _ => continuous_eC_zsmul _ _ _

end

end FroehlichSpencer.FS82.ZN.Torus

end
