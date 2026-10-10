/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaFree
public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
import Mathlib.Tactic

/-!
# FS81 Theorem A in infinite volume for physical Condition-λ gases

The corrected decay rate/ argument of `Coulomb/ThermodynamicLimit.lean`, run for the free-b.c. Condition-λ gas
of `Coulomb/ConditionLambdaFree.lean` (no frequency cutoff, expectations are absolutely
convergent sums over all of `ℤ^Λ`).

* `fullGasExpectation_sum`, `fullGasExpectation_const_mul`: linearity of the cutoff-free
  expectation on summable observables; `summable_mul_freeChargePairing` supplies summability of
  the charge-pairing products from the gate.
* `lambdaFieldFormInternal`: the polarized field second moment; `lambdaFieldForm_sum_smul`
  (bilinear expansion) and `lambdaFieldForm_eq_quarter` (polarization).
* `lambdaFieldCorrelationInternal κ λ n x y`: `⟨(φ(x) - φ(0))(φ(y) - φ(0))⟩_{Λ_n}` on the boxes
  `Λ_n = [-n, n]²`; it is bounded uniformly in `n` (`abs_lambdaFieldCorrelation_le`), using
  FS81 Theorem A in finite volume and the positivity of physical weights.
* `lambda_thermodynamic_limit_exists`: limit points exist along a subsequence (compactness).
* **`lambda_infinite_theoremA`**, packaged in **`conditionLambda_thermodynamic_limit`**: for
  every limit point and every finitely supported zero-sum `f`,
  `(1 - δ) κ ⟨f, C f⟩ ≤ ⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩` with FS81's whole-plane potential (J p. 532,
  (1.19), for the gases of J pp. 570–572).

Only physical weights (`λ ≥ 0`, `λ(0) = 1`) are treated here: the uniform correlation bound
uses `⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩`, which needs a positive charge measure.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology

/-! ### Linearity of the full expectation -/

section Linear

variable {V : Type*} [Fintype V]

theorem fullGasExpectation_sum {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ} {ι : Type*}
    (s : Finset ι) (F : ι → (V → ℤ) → ℝ)
    (hs : ∀ i ∈ s, Summable fun q => gasWeightInternal T κ lam q * F i q) :
    fullGasExpectationInternal T κ lam (fun q => ∑ i ∈ s, F i q) =
      ∑ i ∈ s, fullGasExpectationInternal T κ lam (F i) := by
  unfold fullGasExpectationInternal
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum hs, Finset.sum_div]

theorem fullGasExpectation_const_mul (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (c : ℝ) (F : (V → ℤ) → ℝ) :
    fullGasExpectationInternal T κ lam (fun q => c * F q) =
      c * fullGasExpectationInternal T κ lam F := by
  unfold fullGasExpectationInternal
  simp_rw [mul_left_comm _ c, tsum_mul_left]
  rw [mul_div_assoc]

theorem abs_mul_pairing_le_quadratic (κ : ℝ) (h h' : V → ℝ) (q : V → ℤ) :
    |(κ * ∑ j, (q j : ℝ) * h j) * (κ * ∑ j, (q j : ℝ) * h' j)| ≤
      κ ^ 2 * (∑ j, h j ^ 2 + ∑ j, h' j ^ 2) / 2 * (1 + ∑ j, (q j : ℝ) ^ 2) := by
  have h1 := mul_le_mul_of_nonneg_left (sq_pairing_le h q) (sq_nonneg κ)
  have h2 := mul_le_mul_of_nonneg_left (sq_pairing_le h' q) (sq_nonneg κ)
  have hxy : ∀ X Y : ℝ, |X * Y| ≤ (X ^ 2 + Y ^ 2) / 2 := fun X Y =>
    abs_le.2 ⟨by nlinarith [sq_nonneg (X + Y)], by nlinarith [sq_nonneg (X - Y)]⟩
  refine (hxy _ _).trans ?_
  rw [mul_pow, mul_pow]
  nlinarith

end Linear

/-! ### The field bilinear form of the free Condition-λ gas -/

section FieldForm

variable {V : Type*} [Fintype V] [DecidableEq V] (pos : V → ℤ × ℤ) (κ : ℝ) (lam : ℤ → ℝ)

/-- The polarized field second moment of the free Condition-λ gas,
`⟨φ(f) φ(g)⟩_Λ = κ ⟨f, C g⟩ - ⟨(κ ⟨q, C f⟩)(κ ⟨q, C g⟩)⟩_Λ`, without frequency cutoff. -/
def lambdaFieldFormInternal (f g : V → ℝ) : ℝ :=
  κ * ∑ v, f v * -(freePotentialOpInternal pos g v) -
    fullGasExpectationInternal (freePotentialOpInternal pos) κ (fun _ => lam)
      (fun p => (κ * freeChargePairingInternal pos f p) * (κ * freeChargePairingInternal pos g p))

omit [DecidableEq V] in
theorem lambdaFieldForm_self (f : V → ℝ) :
    lambdaFieldFormInternal pos κ lam f f =
      fullSecondMomentInternal (freePotentialOpInternal pos) κ (fun _ => lam) f := by
  unfold lambdaFieldFormInternal fullSecondMomentInternal
  congr 2
  funext p
  unfold freeChargePairingInternal
  ring

omit [DecidableEq V] in
theorem lambdaFieldForm_comm (f g : V → ℝ) :
    lambdaFieldFormInternal pos κ lam f g = lambdaFieldFormInternal pos κ lam g f := by
  unfold lambdaFieldFormInternal
  rw [sum_mul_neg_freePotentialOp_symm]
  congr 2
  funext p
  ring

omit [DecidableEq V] in
theorem summable_mul_freeChargePairing
    (h : GateInternal (freePotentialOpInternal pos) κ (fun _ => lam)) (c : ℝ) (f g : V → ℝ) :
    Summable fun p => gasWeightInternal (freePotentialOpInternal pos) κ (fun _ => lam) p *
      (c * ((κ * freeChargePairingInternal pos f p) * (κ * freeChargePairingInternal pos g p))) := by
  refine h.summable_mul _ (|c| * (κ ^ 2 * (∑ j, (-(freePotentialOpInternal pos f j)) ^ 2 +
    ∑ j, (-(freePotentialOpInternal pos g j)) ^ 2) / 2)) fun p => ?_
  have := mul_le_mul_of_nonneg_left (abs_mul_pairing_le_quadratic κ
    (fun j => -(freePotentialOpInternal pos f j)) (fun j => -(freePotentialOpInternal pos g j)) p)
    (abs_nonneg c)
  rw [abs_mul]
  unfold freeChargePairingInternal
  exact this.trans_eq (by ring)

omit [DecidableEq V] in
/-- Bilinear expansion of the field form along finite linear combinations (needs the gate for
the summability of the charge-pairing products). -/
theorem lambdaFieldForm_sum_smul (h : GateInternal (freePotentialOpInternal pos) κ (fun _ => lam))
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → V → ℝ) :
    lambdaFieldFormInternal pos κ lam (∑ i ∈ s, c i • F i) (∑ j ∈ s, c j • F j) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * lambdaFieldFormInternal pos κ lam (F i) (F j) := by
  unfold lambdaFieldFormInternal
  simp_rw [freeChargePairing_sum_smul]
  have h1 : ∑ v, (∑ i ∈ s, c i • F i) v * -(freePotentialOpInternal pos (∑ j ∈ s, c j • F j) v) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * ∑ v, F i v * -(freePotentialOpInternal pos (F j) v) := by
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have h2 : fullGasExpectationInternal (freePotentialOpInternal pos) κ (fun _ => lam) (fun p =>
      (κ * ∑ i ∈ s, c i * freeChargePairingInternal pos (F i) p) *
        (κ * ∑ j ∈ s, c j * freeChargePairingInternal pos (F j) p)) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * fullGasExpectationInternal (freePotentialOpInternal pos) κ
        (fun _ => lam) (fun p =>
          (κ * freeChargePairingInternal pos (F i) p) * (κ * freeChargePairingInternal pos (F j) p)) := by
    have hexp : ∀ p : V → ℤ, (κ * ∑ i ∈ s, c i * freeChargePairingInternal pos (F i) p) *
        (κ * ∑ j ∈ s, c j * freeChargePairingInternal pos (F j) p) =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * ((κ * freeChargePairingInternal pos (F i) p) *
          (κ * freeChargePairingInternal pos (F j) p)) := by
      intro p
      rw [show ∀ A B : ℝ, (κ * A) * (κ * B) = (A * B) * κ ^ 2 from fun A B => by ring,
        Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hexp]
    rw [fullGasExpectation_sum _ _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [fullGasExpectation_sum _ _ fun j _ => summable_mul_freeChargePairing pos κ lam h _ _ _]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact fullGasExpectation_const_mul _ _ _ _ _
    · simp_rw [Finset.mul_sum]
      exact summable_sum fun j _ => summable_mul_freeChargePairing pos κ lam h _ _ _
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq V] in
/-- Polarization: `4 ⟨φ(F) φ(G)⟩ = ⟨φ(F + G)²⟩ - ⟨φ(F - G)²⟩`. -/
theorem lambdaFieldForm_eq_quarter
    (h : GateInternal (freePotentialOpInternal pos) κ (fun _ => lam)) (F G : V → ℝ) :
    4 * lambdaFieldFormInternal pos κ lam F G =
      fullSecondMomentInternal (freePotentialOpInternal pos) κ (fun _ => lam) (F + G) -
        fullSecondMomentInternal (freePotentialOpInternal pos) κ (fun _ => lam) (F - G) := by
  have hp := lambdaFieldForm_sum_smul pos κ lam h (Finset.univ : Finset (Fin 2)) ![1, 1] ![F, G]
  have hm := lambdaFieldForm_sum_smul pos κ lam h (Finset.univ : Finset (Fin 2)) ![1, -1] ![F, G]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    neg_smul, one_mul, mul_one, neg_mul, mul_neg, neg_neg] at hp hm
  rw [← lambdaFieldForm_self, ← lambdaFieldForm_self, ← sub_eq_add_neg] at *
  rw [hp, hm, lambdaFieldForm_comm pos κ lam G F]
  ring

end FieldForm

/-! ### Boxes `Λ_n = [-n, n]²` -/

section Boxes

/-- The field two-point function `⟨(φ(x) - φ(0)) (φ(y) - φ(0))⟩_{Λ_n}` of the free Condition-λ gas
(set to `0` when `x` or `y` lies outside the box). -/
def lambdaFieldCorrelationInternal (κ : ℝ) (lam : ℤ → ℝ) (n : ℕ) (x y : ℤ × ℤ) : ℝ :=
  if x ∈ boxInternal n ∧ y ∈ boxInternal n then
    lambdaFieldFormInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ lam
      (fun v => dipoleTestInternal x v.1) (fun v => dipoleTestInternal y v.1)
  else 0

theorem lambdaSecondMoment_box_eq_sum (κ : ℝ) (lam : ℤ → ℝ) {n R : ℕ}
    (h : GateInternal (freePotentialOpInternal (Subtype.val : boxInternal n → ℤ × ℤ)) κ
      (fun _ => lam))
    (hRn : R ≤ n) {f : ℤ × ℤ → ℝ} (hf : SupportedInBox R f)
    (hf0 : ∑ x ∈ boxInternal R, f x = 0) :
    fullSecondMomentInternal (freePotentialOpInternal (Subtype.val : boxInternal n → ℤ × ℤ)) κ
        (fun _ => lam) (fun v => f v.1) =
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
        f x * f y * lambdaFieldCorrelationInternal κ lam n x y := by
  rw [← lambdaFieldForm_self, restrict_eq_sum_dipole (n := n) hf hf0,
    lambdaFieldForm_sum_smul _ _ _ h]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [lambdaFieldCorrelationInternal, ite_eq_left ⟨box_mono hRn hx, box_mono hRn hy⟩]

/-- The volume-independent bound `|Γ_n(x, y)| ≤ fieldCorrelationBoundInternal κ x y` for
physical Condition-λ weights above the threshold. -/
theorem abs_lambdaFieldCorrelation_le {δ C α ε κ₀ : ℝ}
    (h : FreeConditionLambdaBoundInternal δ C α ε κ₀) (hδ1 : δ ≤ 1) (κ : ℝ) (hκ : 0 < κ)
    (hκκ₀ : κ₀ < κ) (lam : ℤ → ℝ) (hlam : ConditionLambdaInternal C α ε κ lam)
    (hphys : PhysicalWeightInternal lam) (n : ℕ) (x y : ℤ × ℤ) :
    |lambdaFieldCorrelationInternal κ lam n x y| ≤ fieldCorrelationBoundInternal κ x y := by
  set R := pairRadiusInternal x y
  have hxR := mem_box_pairRadius_left x y
  have hyR := mem_box_pairRadius_right x y
  have hsP : SupportedInBox R (fun u => dipoleTestInternal x u + dipoleTestInternal y u) :=
    (dipoleTest_supported hxR).add (dipoleTest_supported hyR)
  have hsM : SupportedInBox R (fun u => dipoleTestInternal x u - dipoleTestInternal y u) := by
    intro u hu
    simp [dipoleTest_supported hxR u hu, dipoleTest_supported hyR u hu]
  have hzP : ∑ u ∈ boxInternal R, (dipoleTestInternal x u + dipoleTestInternal y u) = 0 := by
    rw [Finset.sum_add_distrib, sum_dipoleTest_box hxR, sum_dipoleTest_box hyR, add_zero]
  have hzM : ∑ u ∈ boxInternal R, (dipoleTestInternal x u - dipoleTestInternal y u) = 0 := by
    rw [Finset.sum_sub_distrib, sum_dipoleTest_box hxR, sum_dipoleTest_box hyR, sub_zero]
  have hQP := wholePlaneQuad_nonneg hsP hzP
  have hQM := wholePlaneQuad_nonneg hsM hzM
  unfold lambdaFieldCorrelationInternal
  split_ifs with hxy
  · have hRn := pairRadius_le hxy.1 hxy.2
    set F : boxInternal n → ℝ := fun v => dipoleTestInternal x v.1
    set G : boxInternal n → ℝ := fun v => dipoleTestInternal y v.1
    have hsum : ∀ {g : ℤ × ℤ → ℝ}, SupportedInBox R g → ∑ u ∈ boxInternal R, g u = 0 →
        ∑ v : boxInternal n, g v.1 = 0 := by
      intro g hg hg0
      rw [Finset.sum_coe_sort (boxInternal n) g, sum_box_eq_of_supported hRn hg, hg0]
    have hP0 := hsum hsP hzP
    have hM0 := hsum hsM hzM
    obtain ⟨hZP, -, hlowP, hupP⟩ :=
      free_conditionLambda_physical h (boxInternal n) κ hκκ₀ lam hlam hphys (F + G) hP0
    obtain ⟨-, -, hlowM, hupM⟩ :=
      free_conditionLambda_physical h (boxInternal n) κ hκκ₀ lam hlam hphys (F - G) hM0
    have hgate := ((h (boxInternal n) κ hκκ₀ lam hlam hphys.1).2).1
    have eP : freeQuadInternal (Subtype.val : boxInternal n → ℤ × ℤ) (F + G) =
        wholePlaneQuadInternal R (fun u => dipoleTestInternal x u + dipoleTestInternal y u) :=
      freeQuad_box_eq hRn hsP
    have eM : freeQuadInternal (Subtype.val : boxInternal n → ℤ × ℤ) (F - G) =
        wholePlaneQuadInternal R (fun u => dipoleTestInternal x u - dipoleTestInternal y u) :=
      freeQuad_box_eq hRn hsM
    rw [eP] at hlowP hupP
    rw [eM] at hlowM hupM
    have h4 := lambdaFieldForm_eq_quarter (Subtype.val : boxInternal n → ℤ × ℤ) κ lam hgate F G
    have hδ' : 0 ≤ 1 - δ := by linarith
    have l1 : 0 ≤ (1 - δ) * κ * wholePlaneQuadInternal R
        (fun u => dipoleTestInternal x u + dipoleTestInternal y u) := by positivity
    have l2 : 0 ≤ (1 - δ) * κ * wholePlaneQuadInternal R
        (fun u => dipoleTestInternal x u - dipoleTestInternal y u) := by positivity
    unfold fieldCorrelationBoundInternal
    rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_zero]
    unfold fieldCorrelationBoundInternal
    positivity

end Boxes

/-! ### FS81 Theorem A in infinite volume for physical Condition-λ gases -/

section Limits

/-- **Existence of thermodynamic limit points** for the free Condition-λ gas on the boxes
`Λ_n = [-n, n]²`: along some subsequence the field two-point functions converge for every
`x, y ∈ ℤ²`. -/
theorem lambda_thermodynamic_limit_exists {δ C α ε κ₀ : ℝ}
    (h : FreeConditionLambdaBoundInternal δ C α ε κ₀) (hδ1 : δ ≤ 1) (κ : ℝ) (hκ : 0 < κ)
    (hκκ₀ : κ₀ < κ) (lam : ℤ → ℝ) (hlam : ConditionLambdaInternal C α ε κ lam)
    (hphys : PhysicalWeightInternal lam) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : ℤ × ℤ → ℤ × ℤ → ℝ,
      ∀ x y, Tendsto (fun k => lambdaFieldCorrelationInternal κ lam (φ k) x y) atTop
        (𝓝 (Γ x y)) := by
  obtain ⟨φ, hφ, l, hl⟩ := exists_subseq_tendsto_pointwise (ι := (ℤ × ℤ) × (ℤ × ℤ))
    (fun n i => lambdaFieldCorrelationInternal κ lam n i.1 i.2)
    (fun i => fieldCorrelationBoundInternal κ i.1 i.2)
    (fun n i => abs_lambdaFieldCorrelation_le h hδ1 κ hκ hκκ₀ lam hlam hphys n i.1 i.2)
  exact ⟨φ, hφ, fun x y => l (x, y), fun x y => hl (x, y)⟩

/-- **FS81 Theorem A in infinite volume for physical Condition-λ gases** (J p. 532, (1.19), with
J pp. 570–572): along any thermodynamic limit `Γ` of the field two-point functions, for every
finitely supported zero-sum `f`, `⟨φ(f)²⟩ = ∑_{x,y} f(x) f(y) Γ(x,y)` is the limit of the
finite-volume second moments and `(1 - δ) κ ⟨f, C f⟩ ≤ ⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩`. -/
theorem lambda_infinite_theoremA {δ C α ε κ₀ : ℝ}
    (h : FreeConditionLambdaBoundInternal δ C α ε κ₀) (κ : ℝ) (hκκ₀ : κ₀ < κ) (lam : ℤ → ℝ)
    (hlam : ConditionLambdaInternal C α ε κ lam) (hphys : PhysicalWeightInternal lam)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {Γ : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hΓ : ∀ x y, Tendsto (fun k => lambdaFieldCorrelationInternal κ lam (φ k) x y) atTop
      (𝓝 (Γ x y)))
    {R : ℕ} {f : ℤ × ℤ → ℝ} (hf : SupportedInBox R f) (hf0 : ∑ x ∈ boxInternal R, f x = 0) :
    Tendsto (fun k => fullSecondMomentInternal
        (freePotentialOpInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ)) κ (fun _ => lam)
        (fun v => f v.1)) atTop
      (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y)) ∧
    (1 - δ) * κ * wholePlaneQuadInternal R f ≤
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ∧
    ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ≤
      κ * wholePlaneQuadInternal R f := by
  have hev : ∀ᶠ k in atTop, R ≤ φ k := hφ.tendsto_atTop.eventually_ge_atTop R
  have hlim : Tendsto (fun k => fullSecondMomentInternal
      (freePotentialOpInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ)) κ (fun _ => lam)
      (fun v => f v.1)) atTop
      (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y)) := by
    refine Tendsto.congr' ?_ (tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ =>
      (hΓ x y).const_mul (f x * f y))
    filter_upwards [hev] with k hk
    exact (lambdaSecondMoment_box_eq_sum κ lam
      ((h (boxInternal (φ k)) κ hκκ₀ lam hlam hphys.1).2).1 hk hf hf0).symm
  have hsum : ∀ k, R ≤ φ k → ∑ v : boxInternal (φ k), f v.1 = 0 := fun k hk => by
    rw [Finset.sum_coe_sort (boxInternal (φ k)) f, sum_box_eq_of_supported hk hf, hf0]
  refine ⟨hlim, ge_of_tendsto hlim ?_, le_of_tendsto hlim ?_⟩
  · filter_upwards [hev] with k hk
    have := (free_conditionLambda_physical h (boxInternal (φ k)) κ hκκ₀ lam hlam hphys
      (fun v => f v.1) (hsum k hk)).2.2.1
    rwa [freeQuad_box_eq hk hf] at this
  · filter_upwards [hev] with k hk
    have := (free_conditionLambda_physical h (boxInternal (φ k)) κ hκκ₀ lam hlam hphys
      (fun v => f v.1) (hsum k hk)).2.2.2
    rwa [freeQuad_box_eq hk hf] at this

/-- ** packaged: FS81 Theorem A in infinite volume for physical Condition-λ gases** (free b.c.,
boxes `Λ_n = [-n, n]²`): for `0 < δ ≤ 1` and `(C, α, ε)` with `ε < 1/16` there is `κ₀` such that
for `κ > κ₀` and every physical Condition-λ weight, thermodynamic limit points exist and every
one of them satisfies `(1 - δ) κ ⟨f, C f⟩ ≤ ⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩`. -/
theorem conditionLambda_thermodynamic_limit (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (C α ε : ℝ)
    (hε : ε < 1 / 16) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
      ConditionLambdaInternal C α ε κ lam → PhysicalWeightInternal lam →
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : ℤ × ℤ → ℤ × ℤ → ℝ,
        ∀ x y, Tendsto (fun k => lambdaFieldCorrelationInternal κ lam (φ k) x y) atTop
          (𝓝 (Γ x y))) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ Γ : ℤ × ℤ → ℤ × ℤ → ℝ,
        (∀ x y, Tendsto (fun k => lambdaFieldCorrelationInternal κ lam (φ k) x y) atTop
          (𝓝 (Γ x y))) →
        ∀ (R : ℕ) (f : ℤ × ℤ → ℝ), SupportedInBox R f → ∑ x ∈ boxInternal R, f x = 0 →
          (1 - δ) * κ * wholePlaneQuadInternal R f ≤
            ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ∧
          ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ≤
            κ * wholePlaneQuadInternal R f) := by
  obtain ⟨κ₀, hκ₀, h⟩ := free_conditionLambda_bound δ hδ C α ε hε
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ lam hlam hphys => ⟨lambda_thermodynamic_limit_exists h hδ1 κ
    (hκ₀.trans hκκ₀) hκκ₀ lam hlam hphys, fun φ hφ Γ hΓ R f hf hf0 => ?_⟩⟩
  have := lambda_infinite_theoremA h κ hκκ₀ lam hlam hphys hφ hΓ hf hf0
  exact ⟨this.2.1, this.2.2⟩

end Limits

end FroehlichSpencer.BKT.Coulomb
