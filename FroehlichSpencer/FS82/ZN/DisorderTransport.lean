/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.PinExpansion
public import FroehlichSpencer.FS82.ZN.PiTransport
public import FroehlichSpencer.FS82.ZN.CubeEmbedding
public import FroehlichSpencer.FS82.ZN.Disorder

/-!
* the primal link `e` carries the variable of the dual link `D e`, with the C2 orientation sign;
* the dual links outside the image carry only their pinning factor, which integrates to one;
* the Wilson weight sits on the dual plaquettes `cubeQ M`, the images of the primal plaquettes,
  with the curl coefficient as incidence;
* a twist `ψ_p` on the primal plaquette `p` becomes `σ_{D p} ψ_p` on `D p`.
-/

open scoped BigOperators
open MeasureTheory
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.ZN.Torus

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

local instance disorderTransport_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance disorderTransport_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem circleCosCharacter_one (z : UnitAddCircle) : circleCosCharacter 1 z = cosC z := by
  unfold circleCosCharacter cosC
  simp

/-- The primal plaquette flux as a sum over the primal links. -/
theorem primalPlaquetteFlux_eq_sum {B : Box 4} (θ : PrimalAngleConfig B)
    (p : PrimalPlaquettes B) :
    primalPlaquetteFlux θ p = ∑ e : PrimalLinks B, boundaryBasis p.1 e.1 • θ e := by
  classical
  unfold primalPlaquetteFlux circleChainPairing
  have hb : boundary (Finsupp.single p.1 (1 : ℤ)) = boundaryBasis p.1 := boundary_basis p.1
  rw [hb, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype (boundaryBasis p.1) (fun c a => a • primalCircleCochain θ c)
      (fun c => zero_smul ℤ _)]
  rw [← Finset.sum_filter_of_ne (p := fun c : Cell 4 B => cellDegree c = 1)]
  · rw [Finset.sum_subtype (p := fun c : Cell 4 B => cellDegree c = 1)
      (Finset.univ.filter fun c : Cell 4 B => cellDegree c = 1)
      (fun c => by simp) (fun c => boundaryBasis p.1 c • primalCircleCochain θ c)]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold primalCircleCochain
    rw [dite_eq_left e.2]
  · intro c _ hne
    by_contra hdeg
    apply hne
    unfold primalCircleCochain
    rw [dite_eq_right hdeg, smul_zero]

/-- The images of the primal plaquettes of `cube M` among the dual plaquettes of
`cube (M+1)`. -/
def cubeQ (M : ℕ) : Finset (SourceDualTwoCells (cube (M + 1))) :=
  Finset.univ.image (cubeD₂ M)

/-- The primal configuration read off a configuration on the dual links: the variable of the
image link, with the C2 orientation sign. -/
def cubeR (M : ℕ) (θ' : Link (cube (M + 1)) → UnitAddCircle) : PrimalAngleConfig (cube M) :=
  fun e => sourceDualT (cubeD₁ M e) • θ' (cubeD₁ M e)

/-- The primal flux of the restricted configuration is the signed dual flux. -/
theorem primalPlaquetteFlux_cubeR (M : ℕ) (θ' : Link (cube (M + 1)) → UnitAddCircle)
    (p : PrimalPlaquettes (cube M)) :
    primalPlaquetteFlux (cubeR M θ') p =
      sourceDualSigma (cubeD₂ M p) •
        ∑ e' : Link (cube (M + 1)), curlInt (cubeD₂ M p) e' • θ' e' := by
  classical
  have hR : ∑ e' : Link (cube (M + 1)), curlInt (cubeD₂ M p) e' • θ' e' =
      ∑ e : PrimalLinks (cube M), curlInt (cubeD₂ M p) (cubeD₁ M e) • θ' (cubeD₁ M e) := by
    rw [← Finset.sum_image (f := fun e' => curlInt (cubeD₂ M p) e' • θ' e')
      (fun e _ e₂ _ h => cubeD₁_injective M h)]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun e' _ he' => ?_
    rw [curlInt_cubeD₂_eq_zero M p e' fun e hh =>
      he' (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, hh⟩), zero_smul]
  rw [primalPlaquetteFlux_eq_sum, hR, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold cubeR
  rw [boundaryBasis_cube_eq M p e, smul_smul, smul_smul]
  congr 1
  have hT : sourceDualT (cubeD₁ M e) * sourceDualT (cubeD₁ M e) = 1 := by
    rcases sourceDualT_is_pm_one (cubeD₁ M e) with h | h <;> rw [h] <;> norm_num
  calc sourceDualSigma (cubeD₂ M p) * sourceDualT (cubeD₁ M e) *
        curlInt (cubeD₂ M p) (cubeD₁ M e) * sourceDualT (cubeD₁ M e)
      = sourceDualSigma (cubeD₂ M p) * curlInt (cubeD₂ M p) (cubeD₁ M e) *
          (sourceDualT (cubeD₁ M e) * sourceDualT (cubeD₁ M e)) := by ring
    _ = _ := by rw [hT, mul_one]

theorem cosC_zsmul_sign_add {s : ℤ} (hs : s = 1 ∨ s = -1) (X : UnitAddCircle) (ψ : ℝ) :
    cosC (s • X + (ψ : UnitAddCircle)) = cosC (X + (((s : ℝ) * ψ : ℝ) : UnitAddCircle)) := by
  rcases hs with rfl | rfl
  · simp
  · rw [← cosC_neg]
    congr 1
    simp only [neg_smul, one_smul, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
      AddCircle.coe_neg]
    abel

/-- **Transport of a Wilson-type density.** A twist `ψ_p` on the primal plaquettes of `cube M`
becomes the twist `Φ` on the dual plaquettes of `cube (M+1)` when `Φ(D p) = σ_{D p} ψ_p`. -/
theorem integral_primal_eq_dual (M N : ℕ) (h : NNReal) (β : ℝ)
    (ψ : PrimalPlaquettes (cube M) → ℝ) (Φ : SourceDualTwoCells (cube (M + 1)) → ℝ)
    (hΦ : ∀ p, Φ (cubeD₂ M p) = ((sourceDualSigma (cubeD₂ M p) : ℤ) : ℝ) * ψ p) :
    ∫ θ : PrimalAngleConfig (cube M),
        (∏ p : PrimalPlaquettes (cube M), Real.exp (β *
          circleCosCharacter 1 (primalPlaquetteFlux θ p + (ψ p : UnitAddCircle)))) *
          znPinningDensity N h θ =
      ∫ θ' : Link (cube (M + 1)) → UnitAddCircle,
        (∏ e', znPinningFactor N h (θ' e')) *
          wilsonWeight β (modelInc (cubeQ M)) (fun p' => Φ p'.1) θ' := by
  classical
  set Wp : PrimalAngleConfig (cube M) → ℝ := fun θ =>
    ∏ p : PrimalPlaquettes (cube M), Real.exp (β *
      circleCosCharacter 1 (primalPlaquetteFlux θ p + (ψ p : UnitAddCircle))) with hWp
  have hWpc : Continuous Wp := by
    refine continuous_finsetProd _ fun p _ => ?_
    exact Real.continuous_exp.comp (continuous_const.mul ((continuous_circleCosCharacter 1).comp
      ((continuous_primalPlaquetteFlux p).add continuous_const)))
  set s : PrimalLinks (cube M) → ℤ := fun e => sourceDualT (cubeD₁ M e) with hs
  have hspm : ∀ e, s e = 1 ∨ s e = -1 := fun e => sourceDualT_is_pm_one _
  have hflipc : Continuous fun θ : PrimalAngleConfig (cube M) => fun e => s e • θ e :=
    continuous_pi fun e => (continuous_apply e).zsmul (s e)
  -- step 1: the sign flips
  have h1 : ∫ θ : PrimalAngleConfig (cube M), Wp θ * znPinningDensity N h θ =
      ∫ θ : PrimalAngleConfig (cube M), (∏ e, znPinningFactor N h (θ e)) *
        Wp (fun e => s e • θ e) := by
    rw [← integral_flip s hspm (fun θ => Wp θ * znPinningDensity N h θ)
      (hWpc.mul (continuous_znPinningDensity N h))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    change Wp (fun e => s e • θ e) * znPinningDensity N h (fun e => s e • θ e) = _
    unfold znPinningDensity
    simp_rw [znPinningFactor_zsmul N h (hspm _)]
    ring
  -- step 2: restriction to the image links
  have h2 := integral_pin_restrict N h (cubeD₁ M) (cubeD₁_injective M)
    (fun θ : PrimalAngleConfig (cube M) => Wp (fun e => s e • θ e)) (hWpc.comp hflipc)
  rw [h1, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ' => ?_)
  change (∏ e', znPinningFactor N h (θ' e')) * Wp (cubeR M θ') = _
  congr 1
  -- step 3: the Wilson weights agree
  have hprod : wilsonWeight β (modelInc (cubeQ M)) (fun p' => Φ p'.1) θ' =
      ∏ p' ∈ cubeQ M, Real.exp (β *
        cosC (pair (fun e => curlInt p' e) θ' + (Φ p' : UnitAddCircle))) :=
    Finset.prod_coe_sort (cubeQ M) (fun p' : SourceDualTwoCells (cube (M + 1)) =>
      Real.exp (β * cosC (pair (fun e => curlInt p' e) θ' + (Φ p' : UnitAddCircle))))
  rw [hprod]
  unfold cubeQ
  rw [Finset.prod_image fun p _ p₂ _ hh => cubeD₂_injective M hh]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [circleCosCharacter_one, primalPlaquetteFlux_cubeR,
    cosC_zsmul_sign_add (sourceDualSigma_is_pm_one _), hΦ p]
  rfl

/-! ### The sheet -/

theorem cubeD_inl (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) (v : Fin (cube M i + 1))
    (h : c i = Sum.inl v) : ∃ w, cubeD M c i = Sum.inl w ∧ w.val = v.val := by
  simp only [cubeD, h]
  exact ⟨_, rfl, rfl⟩

theorem cubeD_inr (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) (t : Fin (cube M i))
    (h : c i = Sum.inr t) : ∃ e, cubeD M c i = Sum.inr e ∧ e.val = t.val + 1 := by
  simp only [cubeD, h]
  exact ⟨_, rfl, rfl⟩

/-- The coordinates of a centred disorder plaquette: positions `M+1+i`, `M+1+j` on the axes `0`,
`1` and the interval `M` on the axes `2`, `3`. -/
theorem centeredRectangularTwistPlaquette_coords {L T M : ℕ} (hL : L ≤ M) (hT : T ≤ M)
    (hbox : 0 < M) (i : Fin L) (j : Fin T) :
    (∃ v, centeredRectangularTwistPlaquette hL hT hbox i j 0 = Sum.inl v ∧
        v.val = M + 1 + i.val) ∧
      (∃ v, centeredRectangularTwistPlaquette hL hT hbox i j 1 = Sum.inl v ∧
        v.val = M + 1 + j.val) ∧
      (∃ e, centeredRectangularTwistPlaquette hL hT hbox i j 2 = Sum.inr e ∧ e.val = M) ∧
      (∃ e, centeredRectangularTwistPlaquette hL hT hbox i j 3 = Sum.inr e ∧ e.val = M) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-- A dual plaquette with vertex coordinates on the axes `0`, `1` and interval coordinates on the
axes `2`, `3` has C2 orientation sign `−1`. -/
theorem sourceDualSigma_eq_neg_one {B : Box 4} (f : SourceDualTwoCells B)
    (h0 : ∃ v, f.1 0 = Sum.inl v) (h1 : ∃ v, f.1 1 = Sum.inl v)
    (h2 : ∃ e, f.1 2 = Sum.inr e) (h3 : ∃ e, f.1 3 = Sum.inr e) :
    sourceDualSigma f = -1 := by
  obtain ⟨v0, h0⟩ := h0
  obtain ⟨v1, h1⟩ := h1
  obtain ⟨e2, h2⟩ := h2
  obtain ⟨e3, h3⟩ := h3
  have haxes : dualCellAxes f.1 = {2, 3} := by
    ext k
    fin_cases k <;> simp [dualCellAxes, h0, h1, h2, h3]
  unfold sourceDualSigma dualAxisSum
  rw [haxes]
  decide


theorem centered_sheet_transport {L T M : ℕ} (hL : L ≤ M) (hT : T ≤ M) (hbox : 0 < M)
    (N ξ : ℕ) (p : PrimalPlaquettes (cube M)) :
    -((ξ : ℝ) / (N : ℝ) * cubeSheet L T (M + 1) (cubeD₂ M p)) =
      ((sourceDualSigma (cubeD₂ M p) : ℤ) : ℝ) *
        ((centeredRectangularTwistSheet hL hT hbox p.1 : ℝ) * (ξ : ℝ) / (N : ℝ)) := by
  classical
  rw [centeredRectangularTwistSheet_apply, cubeSheet_apply]
  by_cases hs : rectangularTwistSheetSupport (centeredRectangularTwistPlaquette hL hT hbox) p.1
  · obtain ⟨i, j, hij⟩ := hs
    obtain ⟨⟨v0, h0, hv0⟩, ⟨v1, h1, hv1⟩, ⟨e2, h2, he2⟩, ⟨e3, h3, he3⟩⟩ :=
      centeredRectangularTwistPlaquette_coords hL hT hbox i j
    rw [hij] at h0 h1 h2 h3
    have hcond : (∃ v, (cubeD₂ M p).1 0 = Sum.inl v ∧ M + 1 ≤ v.val ∧ v.val < M + 1 + L) ∧
        (∃ v, (cubeD₂ M p).1 1 = Sum.inl v ∧ M + 1 ≤ v.val ∧ v.val < M + 1 + T) ∧
        (∃ e, (cubeD₂ M p).1 2 = Sum.inr e ∧ e.val = M + 1) ∧
        (∃ e, (cubeD₂ M p).1 3 = Sum.inr e ∧ e.val = M + 1) := by
      obtain ⟨w0, hw0, hw0v⟩ := cubeD_inl M p.1 0 v0 h0
      obtain ⟨w1, hw1, hw1v⟩ := cubeD_inl M p.1 1 v1 h1
      obtain ⟨f2, hf2, hf2v⟩ := cubeD_inr M p.1 2 e2 h2
      obtain ⟨f3, hf3, hf3v⟩ := cubeD_inr M p.1 3 e3 h3
      have hi := i.isLt
      have hj := j.isLt
      exact ⟨⟨w0, hw0, by omega, by omega⟩, ⟨w1, hw1, by omega, by omega⟩,
        ⟨f2, hf2, by omega⟩, ⟨f3, hf3, by omega⟩⟩
    have hsig : sourceDualSigma (cubeD₂ M p) = -1 :=
      sourceDualSigma_eq_neg_one _ ⟨_, hcond.1.choose_spec.1⟩ ⟨_, hcond.2.1.choose_spec.1⟩
        ⟨_, hcond.2.2.1.choose_spec.1⟩ ⟨_, hcond.2.2.2.choose_spec.1⟩
    have hsupp : rectangularTwistSheetSupport (centeredRectangularTwistPlaquette hL hT hbox) p.1 :=
      ⟨i, j, hij⟩
    rw [ite_eq_left hcond, ite_eq_left hsupp, hsig]
    push_cast
    ring
  · have hncond : ¬ ((∃ v, (cubeD₂ M p).1 0 = Sum.inl v ∧ M + 1 ≤ v.val ∧ v.val < M + 1 + L) ∧
        (∃ v, (cubeD₂ M p).1 1 = Sum.inl v ∧ M + 1 ≤ v.val ∧ v.val < M + 1 + T) ∧
        (∃ e, (cubeD₂ M p).1 2 = Sum.inr e ∧ e.val = M + 1) ∧
        (∃ e, (cubeD₂ M p).1 3 = Sum.inr e ∧ e.val = M + 1)) := by
      rintro ⟨⟨v0, h0, hv0l, hv0u⟩, ⟨v1, h1, hv1l, hv1u⟩, ⟨e2, h2, he2⟩, ⟨e3, h3, he3⟩⟩
      apply hs
      -- read the coordinates of `p`
      have hp0 : ∃ w, p.1 0 = Sum.inl w ∧ w.val = v0.val := by
        cases hc : p.1 0 with
        | inl w =>
            refine ⟨w, rfl, ?_⟩
            have := h0
            simp only [cubeD₂, cubeD, hc] at this
            exact congrArg Fin.val (Sum.inl.inj this)
        | inr t =>
            have := h0
            simp only [cubeD₂, cubeD, hc] at this
            cases this
      have hp1 : ∃ w, p.1 1 = Sum.inl w ∧ w.val = v1.val := by
        cases hc : p.1 1 with
        | inl w =>
            refine ⟨w, rfl, ?_⟩
            have := h1
            simp only [cubeD₂, cubeD, hc] at this
            exact congrArg Fin.val (Sum.inl.inj this)
        | inr t =>
            have := h1
            simp only [cubeD₂, cubeD, hc] at this
            cases this
      have hp2 : ∃ t, p.1 2 = Sum.inr t ∧ t.val + 1 = e2.val := by
        cases hc : p.1 2 with
        | inl w =>
            have := h2
            simp only [cubeD₂, cubeD, hc] at this
            cases this
        | inr t =>
            refine ⟨t, rfl, ?_⟩
            have := h2
            simp only [cubeD₂, cubeD, hc] at this
            exact congrArg Fin.val (Sum.inr.inj this)
      have hp3 : ∃ t, p.1 3 = Sum.inr t ∧ t.val + 1 = e3.val := by
        cases hc : p.1 3 with
        | inl w =>
            have := h3
            simp only [cubeD₂, cubeD, hc] at this
            cases this
        | inr t =>
            refine ⟨t, rfl, ?_⟩
            have := h3
            simp only [cubeD₂, cubeD, hc] at this
            exact congrArg Fin.val (Sum.inr.inj this)
      obtain ⟨w0, hw0, hw0v⟩ := hp0
      obtain ⟨w1, hw1, hw1v⟩ := hp1
      obtain ⟨t2, ht2, ht2v⟩ := hp2
      obtain ⟨t3, ht3, ht3v⟩ := hp3
      refine ⟨⟨w0.val - (M + 1), by omega⟩, ⟨w1.val - (M + 1), by omega⟩, ?_⟩
      obtain ⟨⟨u0, g0, hu0⟩, ⟨u1, g1, hu1⟩, ⟨f2, g2, hf2⟩, ⟨f3, g3, hf3⟩⟩ :=
        centeredRectangularTwistPlaquette_coords hL hT hbox
          (⟨w0.val - (M + 1), by omega⟩ : Fin L) (⟨w1.val - (M + 1), by omega⟩ : Fin T)
      funext k
      fin_cases k
      · change centeredRectangularTwistPlaquette hL hT hbox _ _ 0 = p.1 0
        rw [g0, hw0]
        exact congrArg Sum.inl (Fin.ext (by simp only at hu0; omega))
      · change centeredRectangularTwistPlaquette hL hT hbox _ _ 1 = p.1 1
        rw [g1, hw1]
        exact congrArg Sum.inl (Fin.ext (by simp only at hu1; omega))
      · change centeredRectangularTwistPlaquette hL hT hbox _ _ 2 = p.1 2
        rw [g2, ht2]
        exact congrArg Sum.inr (Fin.ext (by omega))
      · change centeredRectangularTwistPlaquette hL hT hbox _ _ 3 = p.1 3
        rw [g3, ht3]
        exact congrArg Sum.inr (Fin.ext (by omega))
    rw [ite_eq_right hncond, ite_eq_right hs]
    simp

/-! ### The bound at finite `h` -/

/-- The global reflection `θ ↦ −θ` exchanges the twists `φ` and `−φ`. -/
theorem integral_pin_wilsonWeight_neg {K P : Type*} [Fintype K] [Fintype P] (N : ℕ) (h : NNReal)
    (β : ℝ) (c : P → K → ℤ) (φ : P → ℝ) :
    ∫ θ : K → UnitAddCircle, (∏ k, znPinningFactor N h (θ k)) *
        wilsonWeight β c (fun p => -φ p) θ =
      ∫ θ : K → UnitAddCircle, (∏ k, znPinningFactor N h (θ k)) * wilsonWeight β c φ θ := by
  rw [← integral_neg_config (fun θ : K → UnitAddCircle =>
    (∏ k, znPinningFactor N h (θ k)) * wilsonWeight β c φ θ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Pi.neg_apply, znPinningFactor_neg, wilsonWeight_neg]


theorem finiteCenteredDisorderExpectation_ge {L T M N ξ : ℕ} (hL1 : 1 ≤ L) (hT1 : 1 ≤ T)
    (hL : L ≤ M) (hT : T ≤ M) (hbox : 0 < M) (hN : 0 < N) (hξ : 1 ≤ ξ) {β : ℝ} (hβ : 0 ≤ β)
    (ha : 11 ≤ znActivityRate β N) (h : NNReal) :
    Real.exp (-(znStateError β N * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
      finiteCenteredDisorderExpectation β N ξ L T M h hL hT hbox := by
  have hnum : finiteDisorderNumerator β N ξ h (centeredRectangularTwistSheet hL hT hbox) =
      ∫ θ' : Link (cube (M + 1)) → UnitAddCircle, (∏ e', znPinningFactor N h (θ' e')) *
        wilsonWeight β (modelInc (cubeQ M))
          (fun p' => -((ξ : ℝ) / (N : ℝ) * cubeSheet L T (M + 1) p'.1)) θ' :=
    integral_primal_eq_dual M N h β
      (fun p => (centeredRectangularTwistSheet hL hT hbox p.1 : ℝ) * (ξ : ℝ) / (N : ℝ))
      (fun p' => -((ξ : ℝ) / (N : ℝ) * cubeSheet L T (M + 1) p'))
      (fun p => centered_sheet_transport hL hT hbox N ξ p)
  have hden : finiteZNPartitionFunction (B := cube M) β N h =
      ∫ θ' : Link (cube (M + 1)) → UnitAddCircle, (∏ e', znPinningFactor N h (θ' e')) *
        wilsonWeight β (modelInc (cubeQ M)) (fun _ => 0) θ' := by
    have h0 := integral_primal_eq_dual M N h β (fun _ => 0) (fun _ => 0) (fun p => by simp)
    rw [← h0]
    unfold finiteZNPartitionFunction finiteZNWeight wilsonActionDensity wilsonPlaquetteFactor
    simp
  have hmain := sourceModel_lower_bound (L := L) (T := T) (M := M + 1) (N := N) (ξ := ξ) hL1 hT1
    (by omega) hN hξ hβ ha (cubeQ M) h
  have hneg := integral_pin_wilsonWeight_neg N h β (modelInc (cubeQ M))
    (fun p' : {p' : SourceDualTwoCells (cube (M + 1)) // p' ∈ cubeQ M} =>
      (ξ : ℝ) / (N : ℝ) * cubeSheet L T (M + 1) p'.1)
  rw [← hneg, ← hnum, ← hden] at hmain
  unfold finiteCenteredDisorderExpectation finiteDisorderExpectation
  rw [le_div_iff₀ (finiteZNPartitionFunction_pos β N h)]
  exact hmain

end

end FroehlichSpencer.FS82.ZN

end
