/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.SchwartzFourierLattice
public import FroehlichSpencer.BKT.Rotator.PoissonMultiSchwartz
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Partial Poisson summation (the finite comb construction: the comb on a sub-region)

FS81's state (7.16) inserts the comb `∏_{j∈A}[1 + 2Σ_q cos(2πqφ(j))]` only on the sites of `A`; the
other sites keep the continuous field. For a Schwartz density `f` on `ℝ^ι` and a set of coordinates
`p`, the comb pairings therefore converge to the Fourier coefficients `f̂(q ⊕ 0)` at frequencies
vanishing off `p`, and these sum to the lattice sum of the **marginal**
`G(x) = ∫ f(x ⊕ y) dy` over the coordinates off `p`:

`Σ_{q ∈ ℤ^p} f̂(q ⊕ 0) = Σ_{n ∈ ℤ^p} ∫_{ℝ^{¬p}} f(n ⊕ y) dy` (`tsum_fourier_extZero_eq_tsum_marginal`).

The marginal is Schwartz (`exists_schwartz_marginalPi`): its coordinate Fourier transform is
`f̂(· ⊕ 0)` (Fubini along `MeasurableEquiv.piEquivPiSubtypeProd`), the restriction of the Schwartz
`f̂` along the isometric embedding `ξ ↦ ξ ⊕ 0` is Schwartz, and by Fourier inversion (Mathlib's
`Continuous.fourierInv_fourier_eq`, transported to coordinates in `eq_of_fourierPi_eq`) the marginal
is the inverse transform of that Schwartz function. The multidimensional Poisson formula
(`poissonSummation_schwartz_pi_unconditional`) for the marginal then gives the identity.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Complex
open scoped FourierTransform SchwartzMap
open FroehlichSpencer.BKT.Rotator

/-! ## The coordinate Fourier transform -/

/-- The coordinate Fourier transform `ĝ(ξ) = ∫ e^{−2πi⟨x, ξ⟩} g(x) dx`. -/
def fourierPi {κ : Type*} [Fintype κ] (g : (κ → ℝ) → ℂ) (ξ : κ → ℝ) : ℂ :=
  ∫ x, cexp (((-2 * Real.pi * ∑ i, x i * ξ i : ℝ) : ℂ) * I) * g x

theorem multiEuclideanFourierCoefficient_eq_fourierPi {κ : Type*} [Fintype κ]
    (g : (κ → ℝ) → ℂ) (q : κ → ℤ) :
    multiEuclideanFourierCoefficient g q = fourierPi g (fun i => (q i : ℝ)) := rfl

theorem measurePreserving_euclideanEquiv_symm (κ : Type*) [Fintype κ] :
    MeasurePreserving (fun x : κ → ℝ => (EuclideanSpace.equiv κ ℝ).symm x) volume volume := by
  convert PiLp.volume_preserving_toLp κ using 1
  funext x
  rfl

theorem measurePreserving_euclideanEquiv (κ : Type*) [Fintype κ] :
    MeasurePreserving (fun v : EuclideanSpace ℝ κ => EuclideanSpace.equiv κ ℝ v) volume volume := by
  convert PiLp.volume_preserving_ofLp κ using 1
  funext x
  rfl

theorem inner_euclideanEquiv_symm {κ : Type*} [Fintype κ] (x : κ → ℝ) (w : EuclideanSpace ℝ κ) :
    inner ℝ ((EuclideanSpace.equiv κ ℝ).symm x) w = ∑ i, x i * EuclideanSpace.equiv κ ℝ w i := by
  rw [show (EuclideanSpace.equiv κ ℝ).symm x = (WithLp.toLp 2 x : EuclideanSpace ℝ κ) by rfl,
    PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.inner_apply]
  rfl

/-- The Euclidean Fourier transform of a function read in coordinates is its coordinate Fourier
transform. -/
theorem fourier_comp_euclideanEquiv {κ : Type*} [Fintype κ] (g : (κ → ℝ) → ℂ)
    (w : EuclideanSpace ℝ κ) :
    𝓕 (fun v : EuclideanSpace ℝ κ => g (EuclideanSpace.equiv κ ℝ v)) w =
      fourierPi g (EuclideanSpace.equiv κ ℝ w) := by
  rw [Real.fourier_eq']
  unfold fourierPi
  rw [← (measurePreserving_euclideanEquiv_symm κ).integral_comp
    (MeasurableEquiv.toLp 2 (κ → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_euclideanEquiv_symm, ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul]

/-- For a Schwartz function the repository's Fourier transform is the coordinate one. -/
theorem schwartzFourierOnPi_eq_fourierPi {κ : Type*} [Fintype κ] (f : 𝓢(κ → ℝ, ℂ))
    (ξ : κ → ℝ) : schwartzFourierOnPi f ξ = fourierPi f ξ := by
  have h := fourier_comp_euclideanEquiv (fun x => f x) ((EuclideanSpace.equiv κ ℝ).symm ξ)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

/-- **Uniqueness**: two continuous integrable functions with the same integrable coordinate Fourier
transform coincide (Fourier inversion). -/
theorem eq_of_fourierPi_eq {κ : Type*} [Fintype κ] {H₁ H₂ : (κ → ℝ) → ℂ}
    (hc₁ : Continuous H₁) (hc₂ : Continuous H₂) (hi₁ : Integrable H₁) (hi₂ : Integrable H₂)
    (hF : fourierPi H₁ = fourierPi H₂) (hFi : Integrable (fourierPi H₁)) : H₁ = H₂ := by
  have hmp := measurePreserving_euclideanEquiv κ
  set e : EuclideanSpace ℝ κ ≃ᵐ (κ → ℝ) := (MeasurableEquiv.toLp 2 (κ → ℝ)).symm
  have hFE : ∀ H : (κ → ℝ) → ℂ,
      𝓕 (fun v : EuclideanSpace ℝ κ => H (EuclideanSpace.equiv κ ℝ v)) =
        fun w => fourierPi H (EuclideanSpace.equiv κ ℝ w) :=
    fun H => funext fun w => fourier_comp_euclideanEquiv H w
  have hE : ∀ H : (κ → ℝ) → ℂ, Continuous H → Integrable H → Integrable (fourierPi H) →
      (fun v : EuclideanSpace ℝ κ => H (EuclideanSpace.equiv κ ℝ v)) =
        𝓕⁻ (𝓕 (fun v : EuclideanSpace ℝ κ => H (EuclideanSpace.equiv κ ℝ v))) := by
    intro H hc hi hfi
    have hcE : Continuous fun v : EuclideanSpace ℝ κ => H (EuclideanSpace.equiv κ ℝ v) :=
      hc.comp (EuclideanSpace.equiv κ ℝ).continuous
    have hiE : Integrable fun v : EuclideanSpace ℝ κ => H (EuclideanSpace.equiv κ ℝ v) :=
      (hmp.integrable_comp_emb e.measurableEmbedding).mpr hi
    refine (hcE.fourierInv_fourier_eq hiE ?_).symm
    rw [hFE]
    exact (hmp.integrable_comp_emb e.measurableEmbedding).mpr hfi
  have h1 := hE H₁ hc₁ hi₁ hFi
  have h2 := hE H₂ hc₂ hi₂ (hF ▸ hFi)
  have h12 : 𝓕 (fun v : EuclideanSpace ℝ κ => H₁ (EuclideanSpace.equiv κ ℝ v)) =
      𝓕 (fun v : EuclideanSpace ℝ κ => H₂ (EuclideanSpace.equiv κ ℝ v)) := by
    rw [hFE, hFE, hF]
  funext x
  have hx := congrFun h1 ((EuclideanSpace.equiv κ ℝ).symm x)
  have hy := congrFun h2 ((EuclideanSpace.equiv κ ℝ).symm x)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hx hy
  rw [hx, hy, h12]

/-! ## The marginal over the coordinates off `p` -/

section Marginal

variable {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]

/-- Merging the coordinates on `p` and off `p`. -/
def mergePi (x : {i // p i} → ℝ) (y : {i // ¬p i} → ℝ) : ι → ℝ :=
  fun i => if h : p i then x ⟨i, h⟩ else y ⟨i, h⟩

omit [Fintype ι] in
theorem mergePi_eq_symm (z : ({i // p i} → ℝ) × ({i // ¬p i} → ℝ)) :
    mergePi p z.1 z.2 = (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p).symm z := rfl

theorem measurePreserving_mergePi :
    MeasurePreserving (fun z : ({i // p i} → ℝ) × ({i // ¬p i} → ℝ) => mergePi p z.1 z.2)
      volume volume :=
  (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) p).symm

omit [Fintype ι] in
theorem continuous_mergePi_right (x : {i // p i} → ℝ) : Continuous fun y => mergePi p x y := by
  refine continuous_pi fun i => ?_
  unfold mergePi
  by_cases h : p i
  · simp only [h, ↓reduceDIte]; exact continuous_const
  · simp only [h, ↓reduceDIte]; exact continuous_apply _

omit [Fintype ι] in
theorem continuous_mergePi_left (y : {i // ¬p i} → ℝ) : Continuous fun x => mergePi p x y := by
  refine continuous_pi fun i => ?_
  unfold mergePi
  by_cases h : p i
  · simp only [h, ↓reduceDIte]; exact continuous_apply _
  · simp only [h, ↓reduceDIte]; exact continuous_const

theorem norm_le_norm_mergePi (x : {i // p i} → ℝ) (y : {i // ¬p i} → ℝ) :
    ‖y‖ ≤ ‖mergePi p x y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  have h : mergePi p x y j.1 = y j := by
    unfold mergePi; rw [dite_eq_right j.2]
  rw [← h]
  exact norm_le_pi_norm (mergePi p x y) j.1

/-- Extension by zero off `p`. -/
def extZero : ({i // p i} → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => mergePi p ξ 0
      map_add' := fun ξ η => by
        funext i; unfold mergePi; by_cases h : p i <;> simp [h]
      map_smul' := fun a ξ => by
        funext i; unfold mergePi; by_cases h : p i <;> simp [h] }

theorem extZero_apply (ξ : {i // p i} → ℝ) (i : ι) :
    extZero p ξ i = if h : p i then ξ ⟨i, h⟩ else 0 := rfl

theorem norm_le_norm_extZero (ξ : {i // p i} → ℝ) : ‖ξ‖ ≤ ‖extZero p ξ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  have h : extZero p ξ j.1 = ξ j := by rw [extZero_apply, dite_eq_left j.2]
  rw [← h]
  exact norm_le_pi_norm (extZero p ξ) j.1

theorem sum_mul_extZero (w : ι → ℝ) (ξ : {i // p i} → ℝ) :
    ∑ i, w i * extZero p ξ i = ∑ i : {i // p i}, w i * ξ i := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h2 : ∑ i : {i // ¬p i}, w i * extZero p ξ i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [extZero_apply, dite_eq_right i.2, mul_zero]
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [extZero_apply, dite_eq_left i.2]

/-- The marginal `G(x) = ∫ g(x ⊕ y) dy` over the coordinates off `p`. -/
def marginalPi (g : (ι → ℝ) → ℂ) (x : {i // p i} → ℝ) : ℂ := ∫ y, g (mergePi p x y)

theorem integrable_comp_mergePi {g : (ι → ℝ) → ℂ} (hg : Integrable g) :
    Integrable (fun z : ({i // p i} → ℝ) × ({i // ¬p i} → ℝ) => g (mergePi p z.1 z.2)) :=
  ((measurePreserving_mergePi p).integrable_comp_emb
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p).symm.measurableEmbedding).mpr hg

theorem integrable_marginalPi {g : (ι → ℝ) → ℂ} (hg : Integrable g) :
    Integrable (marginalPi p g) :=
  (integrable_comp_mergePi p hg).integral_prod_left

/-- **The Fourier transform of the marginal** is the Fourier transform at frequencies vanishing
off `p`. -/
theorem fourierPi_marginalPi {g : (ι → ℝ) → ℂ} (hg : Integrable g) (ξ : {i // p i} → ℝ) :
    fourierPi (marginalPi p g) ξ = fourierPi g (extZero p ξ) := by
  set c : ({i // p i} → ℝ) → ℂ := fun x => cexp (((-2 * Real.pi * ∑ i, x i * ξ i : ℝ) : ℂ) * I)
    with hc
  have hc1 : ∀ x, ‖c x‖ = 1 := fun x => by
    rw [hc, Complex.norm_exp]; simp
  have hint : Integrable (fun z : ({i // p i} → ℝ) × ({i // ¬p i} → ℝ) =>
      c z.1 * g (mergePi p z.1 z.2)) := by
    refine (integrable_comp_mergePi p hg).bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact Filter.Eventually.of_forall fun z => (hc1 z.1).le
  unfold fourierPi marginalPi
  calc ∫ x, cexp (((-2 * Real.pi * ∑ i, x i * ξ i : ℝ) : ℂ) * I) * ∫ y, g (mergePi p x y)
      = ∫ x, ∫ y, c x * g (mergePi p x y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [← integral_const_mul]
    _ = ∫ z : ({i // p i} → ℝ) × ({i // ¬p i} → ℝ), c z.1 * g (mergePi p z.1 z.2) :=
        (integral_prod _ hint).symm
    _ = ∫ w, cexp (((-2 * Real.pi * ∑ i, w i * extZero p ξ i : ℝ) : ℂ) * I) * g w := by
        rw [← (measurePreserving_mergePi p).integral_comp
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p).symm.measurableEmbedding]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hsum : ∑ i : {i // p i}, mergePi p z.1 z.2 i * ξ i = ∑ i, z.1 i * ξ i :=
          Finset.sum_congr rfl fun i _ => by unfold mergePi; rw [dite_eq_left i.2]
        simp only [hc]
        rw [sum_mul_extZero, hsum]

/-- The decay of a Schwartz function along the slices `y ↦ f(x ⊕ y)`, uniformly in `x`. -/
theorem exists_slice_decay (f : 𝓢(ι → ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f (mergePi p x y)‖ ≤
      C * (1 + ‖y‖) ^ (-((Fintype.card {i // ¬p i} + 1 : ℕ) : ℝ)) := by
  set k : ℕ := Fintype.card {i // ¬p i} + 1 with hk
  set C : ℝ := 2 ^ k * (Finset.Iic (k, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hC
  have hdecay : ∀ z : ι → ℝ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ (-(k : ℝ)) := by
    intro z
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl f z
    rw [norm_iteratedFDeriv_zero] at h
    have hpos : 0 < (1 + ‖z‖) ^ k := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos,
      mul_comm]
    exact h
  have hC0 : 0 ≤ C := by
    have := hdecay 0
    have h0 : 0 ≤ ‖f 0‖ := norm_nonneg _
    have h1 : 0 < (1 + ‖(0 : ι → ℝ)‖) ^ (-(k : ℝ)) := by positivity
    nlinarith
  refine ⟨C, hC0, fun x y => (hdecay _).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC0
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by linarith [norm_le_norm_mergePi p x y]) (by simp)

theorem integrable_slice_decay_bound :
    Integrable fun y : {i // ¬p i} → ℝ =>
      (1 + ‖y‖) ^ (-((Fintype.card {i // ¬p i} + 1 : ℕ) : ℝ)) := by
  refine integrable_one_add_norm ?_
  rw [Module.finrank_fintype_fun_eq_card]
  simp

/-- The slices of a Schwartz function are integrable. -/
theorem integrable_slice (f : 𝓢(ι → ℝ, ℂ)) (x : {i // p i} → ℝ) :
    Integrable fun y => f (mergePi p x y) := by
  obtain ⟨C, -, hC⟩ := exists_slice_decay p f
  exact ((integrable_slice_decay_bound p).const_mul C).mono'
    (f.continuous.comp (continuous_mergePi_right p x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hC x y)

/-- The marginal of a Schwartz function is continuous. -/
theorem continuous_marginalPi (f : 𝓢(ι → ℝ, ℂ)) : Continuous (marginalPi p f) := by
  obtain ⟨C, -, hC⟩ := exists_slice_decay p f
  exact continuous_of_dominated
    (fun x => (f.continuous.comp (continuous_mergePi_right p x)).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun y => hC x y)
    ((integrable_slice_decay_bound p).const_mul C)
    (Filter.Eventually.of_forall fun y => f.continuous.comp (continuous_mergePi_left p y))

end Marginal

/-! ## The marginal is Schwartz; partial Poisson summation -/

section Poisson

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]

omit [DecidableEq ι] in
/-- **The marginal of a Schwartz function is Schwartz**, with coordinate Fourier transform
`f̂(· ⊕ 0)`. -/
theorem exists_schwartz_marginalPi (f : 𝓢(ι → ℝ, ℂ)) :
    ∃ F : 𝓢({i // p i} → ℝ, ℂ), (∀ x, F x = marginalPi p f x) ∧
      ∀ ξ, fourierPi F ξ = fourierPi f (extZero p ξ) := by
  classical
  have hanti : AntilipschitzWith 1 (extZero p) :=
    (extZero p).antilipschitz_of_bound fun ξ => by
      rw [NNReal.coe_one, one_mul]; exact norm_le_norm_extZero p ξ
  set gA : 𝓢({i // p i} → ℝ, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ
    (extZero p).hasTemperateGrowth hanti (schwartzFourierOnPi f) with hgA
  have hgA_apply : ∀ ξ, gA ξ = fourierPi f (extZero p ξ) := fun ξ => by
    rw [hgA, SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply,
      schwartzFourierOnPi_eq_fourierPi]
  set FE : 𝓢(EuclideanSpace ℝ {i // p i}, ℂ) := 𝓕⁻ (schwartzToEuclidean gA) with hFE
  set F : 𝓢({i // p i} → ℝ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (EuclideanSpace.equiv {i // p i} ℝ).symm FE with hF
  have hFtoE : schwartzToEuclidean F = FE := by
    ext v
    simp [schwartzToEuclidean, hF, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hFfour : ∀ ξ, fourierPi F ξ = gA ξ := fun ξ => by
    rw [← schwartzFourierOnPi_eq_fourierPi]
    have h : schwartzFourierOnPi F ξ =
        (𝓕 (schwartzToEuclidean F)) ((EuclideanSpace.equiv {i // p i} ℝ).symm ξ) := rfl
    rw [h, hFtoE, hFE, FourierTransform.fourier_fourierInv_eq]
    simp only [schwartzToEuclidean, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨F, fun x => ?_, fun ξ => by rw [hFfour, hgA_apply]⟩
  have heq := eq_of_fourierPi_eq (H₁ := fun x => F x) (H₂ := marginalPi p f) F.continuous
    (continuous_marginalPi p f) F.integrable (integrable_marginalPi p f.integrable)
    (funext fun ξ => by
      show fourierPi F ξ = _
      rw [hFfour, hgA_apply, fourierPi_marginalPi p f.integrable])
    (by
      have : fourierPi (fun x => F x) = fun ξ => gA ξ := funext hFfour
      rw [this]; exact gA.integrable)
  exact congrFun heq x

/-- The integer frequency vanishing off `p`. -/
def extZeroInt (q : {i // p i} → ℤ) : ι → ℤ := fun i => if h : p i then q ⟨i, h⟩ else 0

omit [DecidableEq ι] in
theorem extZero_intCast (q : {i // p i} → ℤ) :
    extZero p (fun i => (q i : ℝ)) = fun i => ((extZeroInt p q i : ℤ) : ℝ) := by
  funext i
  rw [extZero_apply, extZeroInt]
  by_cases h : p i <;> simp [h]

/-- **Partial Poisson summation**: `Σ_{q ∈ ℤ^p} f̂(q ⊕ 0) = Σ_{n ∈ ℤ^p} ∫ f(n ⊕ y) dy`, both
sides absolutely summable. -/
theorem tsum_fourier_extZero_eq_tsum_marginal (f : 𝓢(ι → ℝ, ℂ)) :
    (∑' q : {i // p i} → ℤ, multiEuclideanFourierCoefficient f (extZeroInt p q) =
      ∑' n : {i // p i} → ℤ, marginalPi p f (fun i => (n i : ℝ))) ∧
    Summable (fun q : {i // p i} → ℤ => multiEuclideanFourierCoefficient f (extZeroInt p q)) ∧
    Summable (fun n : {i // p i} → ℤ => marginalPi p f (fun i => (n i : ℝ))) := by
  classical
  obtain ⟨F, hF, hFf⟩ := exists_schwartz_marginalPi p f
  have hcoef : ∀ q : {i // p i} → ℤ, multiEuclideanFourierCoefficient F q =
      multiEuclideanFourierCoefficient f (extZeroInt p q) := fun q => by
    rw [multiEuclideanFourierCoefficient_eq_fourierPi, hFf, extZero_intCast,
      ← multiEuclideanFourierCoefficient_eq_fourierPi]
  have hpois := poissonSummation_schwartz_pi_unconditional F
  refine ⟨?_, ?_, ?_⟩
  · rw [← tsum_congr hcoef, hpois]
    exact tsum_congr fun n => hF _
  · exact (summable_multiEuclideanFourierCoefficient_of_schwartz F).congr hcoef
  · exact (schwartz_pi_lattice_samples_summable F).congr fun n => hF _

end Poisson

end FroehlichSpencer.BKT.SOS.Literal

end
