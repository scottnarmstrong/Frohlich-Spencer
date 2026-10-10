/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.SourceJensen
public import FroehlichSpencer.FS82.Moment.PositivePacking

/-!
# the Jensen/packing estimate with windows of any polynomial growth

`XY/Jensen3.lean` proves the packing estimate behind FS82 (4.38) with the window count
`4 (6 L)⁴` of the four-dimensional proof, which also covers `D = 3`.

In dimension `d` a window of
side `L` has of the order of `L ^ d` cells, so the estimate is restated here with a window count
`Cbox · L ^ n` and a filling mass `Cfill · E · L ^ n`, for any `n`.

* `polyActivity n a C L = (20 C² / a²) L^{2n} e^{−aL}`: the activity of a current of length `L`
  after its squared norm is absorbed by the Gaussian tail.
* `jensen_per_current_poly`: the Jensen term of one current.
* `polyPackingConstant n Cbox a C = (20 Cbox C² / a²) ∑_L L^{3n} e^{−aL}`.
* `relativePhase_packing_poly`: `∑_i γ(z_i) θ_i² ≤ polyPackingConstant · ∑_p field(p)²`, for
  currents with pairwise disjoint supports, each localized in a window around a cell where the
  field is maximal on the filling.
* `polyPackingConstant_le_exponential_tail`: the constant is at most a multiple of `e^{1−a}`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.Moment.Packing

/-- The activity of a current of length `L` after absorbing its squared norm, for windows of
polynomial degree `n`. -/
noncomputable def polyActivity (n : ℕ) (a C : ℝ) (L : ℕ) : ℝ :=
  (20 * C ^ 2 / a ^ 2) * (L : ℝ) ^ (2 * n) * Real.exp (-(a * (L : ℝ)))

theorem polyActivity_nonneg (n : ℕ) (a C : ℝ) (L : ℕ) : 0 ≤ polyActivity n a C L := by
  unfold polyActivity
  positivity

/-- **The Jensen term of one current.** -/
theorem jensen_per_current_poly (n : ℕ) (a C x M z θ : ℝ) (L : ℕ) (ha : 0 < a) (ha1 : 1 ≤ a)
    (hx : 0 ≤ x) (hz0 : 0 ≤ z)
    (hz : z ≤ Real.exp (-(a * (x + (L : ℝ))))) (hL : 1 ≤ L)
    (hθ : |θ| ≤ C * M * x * (L : ℝ) ^ n) :
    sourceJensenGamma z * θ ^ 2 ≤ polyActivity n a C L * M ^ 2 := by
  have hsmall : z ≤ 1 / 2 :=
    activity_z_le_half_positive a x (L : ℝ) z ha1 hx (by exact_mod_cast hL) hz
  have hγ := sourceJensenGamma_le_five_mul hz0 hsmall
  have hθsq : θ ^ 2 ≤ (C * M * x * (L : ℝ) ^ n) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  have hsplit : Real.exp (-(a * (x + (L : ℝ)))) =
      Real.exp (-(a * x)) * Real.exp (-(a * (L : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hx2 := square_mul_exp_neg_le a x ha hx
  have hpow : (L : ℝ) ^ (2 * n) = ((L : ℝ) ^ n) ^ 2 := pow_mul' _ _ _
  have hL0 : 0 ≤ (L : ℝ) ^ (2 * n) * Real.exp (-(a * (L : ℝ))) := by positivity
  calc sourceJensenGamma z * θ ^ 2
      ≤ (5 * z) * (C * M * x * (L : ℝ) ^ n) ^ 2 :=
        mul_le_mul hγ hθsq (sq_nonneg _) (by positivity)
    _ ≤ (5 * (Real.exp (-(a * x)) * Real.exp (-(a * (L : ℝ))))) *
          (C * M * x * (L : ℝ) ^ n) ^ 2 := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = 5 * C ^ 2 * M ^ 2 * ((L : ℝ) ^ (2 * n) * Real.exp (-(a * (L : ℝ)))) *
          (x ^ 2 * Real.exp (-(a * x))) := by
        rw [hpow]
        ring
    _ ≤ 5 * C ^ 2 * M ^ 2 * ((L : ℝ) ^ (2 * n) * Real.exp (-(a * (L : ℝ)))) * (4 / a ^ 2) :=
        mul_le_mul_of_nonneg_left hx2 (by positivity)
    _ = polyActivity n a C L * M ^ 2 := by
        unfold polyActivity
        ring

/-- The packing constant for windows of polynomial degree `n` with `Cbox · L ^ n` cells. -/
noncomputable def polyPackingConstant (n Cbox : ℕ) (a C : ℝ) : ℝ :=
  (20 * (Cbox : ℝ) * C ^ 2 / a ^ 2) * ∑' L : ℕ, (L : ℝ) ^ (3 * n) * Real.exp (-(a * (L : ℝ)))

theorem summable_pow_mul_exp (m : ℕ) (a : ℝ) (ha : 0 < a) :
    Summable (fun L : ℕ => (L : ℝ) ^ m * Real.exp (-(a * (L : ℝ)))) := by
  simpa only [neg_mul] using (Real.summable_pow_mul_exp_neg_nat_mul m (r := a) ha)

theorem polyPackingConstant_nonneg (n Cbox : ℕ) (a C : ℝ) : 0 ≤ polyPackingConstant n Cbox a C := by
  unfold polyPackingConstant
  exact mul_nonneg (by positivity) (tsum_nonneg fun L => by positivity)

/-- The finite budget of the buckets is at most the packing constant. -/
theorem polyActivity_budget_le (n Cbox : ℕ) (a C : ℝ) (ha : 0 < a) (K : Finset ℕ) :
    (∑ L ∈ K, ((Cbox : ℝ) * (L : ℝ) ^ n) * polyActivity n a C L) ≤
      polyPackingConstant n Cbox a C := by
  have hsum := (summable_pow_mul_exp (3 * n) a ha).sum_le_tsum K (by intro L _; positivity)
  have hcoef : 0 ≤ 20 * (Cbox : ℝ) * C ^ 2 / a ^ 2 := by positivity
  have hfinite : (∑ L ∈ K, ((Cbox : ℝ) * (L : ℝ) ^ n) * polyActivity n a C L) =
      (20 * (Cbox : ℝ) * C ^ 2 / a ^ 2) *
        ∑ L ∈ K, (L : ℝ) ^ (3 * n) * Real.exp (-(a * (L : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun L _ => ?_
    have hpow : (L : ℝ) ^ (3 * n) = (L : ℝ) ^ n * (L : ℝ) ^ (2 * n) := by
      rw [← pow_add]
      congr 1
      ring
    unfold polyActivity
    rw [hpow]
    ring
  rw [hfinite]
  exact mul_le_mul_of_nonneg_left hsum hcoef

/-- A filling with controlled mass gives a controlled phase. -/
theorem twoPi_fillPairing_abs_le {P : Type*} [Fintype P] (fill field : P → ℝ) (M A : ℝ)
    (hM : 0 ≤ M) (hfield : ∀ p, fill p ≠ 0 → |field p| ≤ M) (hmass : (∑ p, |fill p|) ≤ A) :
    |(2 * Real.pi) * (∑ p, field p * fill p)| ≤ (2 * Real.pi) * (M * A) := by
  have hterm : ∀ p, |field p * fill p| ≤ M * |fill p| := by
    intro p
    by_cases hp : fill p = 0
    · simp [hp]
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hfield p hp) (abs_nonneg _)
  have hsum : (∑ p, |field p * fill p|) ≤ M * (∑ p, |fill p|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hterm p
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  rw [abs_mul, abs_of_nonneg hpi]
  refine mul_le_mul_of_nonneg_left ?_ hpi
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hsum.trans (mul_le_mul_of_nonneg_left hmass hM))

/-- **The Jensen/packing estimate with polynomial windows.** For each current `i` the phase is
`2π ⟨field, fill_i⟩`, the filling has mass at most `Cfill · E_i · L_i ^ n`, and the field is
maximal, on the filling, at the cell `statement i`. The supports are pairwise disjoint, have `L_i`
elements, and lie in the window `box (statement i) L_i`, which has at most `Cbox · L ^ n` elements. -/
theorem relativePhase_packing_poly
    {I P α : Type*} [DecidableEq I] [DecidableEq α] [Fintype P] [DecidableEq P]
    (n Cbox : ℕ) (T : Finset I) (K : Finset ℕ)
    (support : I → Finset α) (box : P → ℕ → Finset α)
    (anchor : I → P) (length : I → ℕ)
    (z energy θ : I → ℝ) (field : P → ℝ) (fill : I → P → ℝ)
    (a Cfill : ℝ) (ha : 0 < a) (ha1 : 1 ≤ a)
    (hlength_mem : ∀ i ∈ T, length i ∈ K)
    (hKpos : ∀ L ∈ K, 1 ≤ L)
    (henergy : ∀ i ∈ T, 0 ≤ energy i)
    (hz0 : ∀ i ∈ T, 0 ≤ z i)
    (hz : ∀ i ∈ T, z i ≤ Real.exp (-(a * (energy i + (length i : ℝ)))))
    (hθ : ∀ i ∈ T, θ i = (2 * Real.pi) * (∑ p, field p * fill i p))
    (hfillMass : ∀ i ∈ T, (∑ p, |fill i p|) ≤ Cfill * energy i * (length i : ℝ) ^ n)
    (hfieldMax : ∀ i ∈ T, ∀ p, fill i p ≠ 0 → |field p| ≤ |field (anchor i)|)
    (hdisj : (↑T : Set I).PairwiseDisjoint support)
    (hsize : ∀ i ∈ T, (support i).card = length i)
    (hlocal : ∀ i ∈ T, support i ⊆ box (anchor i) (length i))
    (hbox : ∀ p L, (box p L).card ≤ Cbox * L ^ n) :
    (∑ i ∈ T, sourceJensenGamma (z i) * θ i ^ 2) ≤
      polyPackingConstant n Cbox a (2 * Real.pi * Cfill) * (∑ p, (field p) ^ 2) := by
  classical
  set C := 2 * Real.pi * Cfill with hC
  let error : I → ℝ := fun i => sourceJensenGamma (z i) * θ i ^ 2
  have herror : ∀ i ∈ T, error i ≤ polyActivity n a C (length i) * (field (anchor i)) ^ 2 := by
    intro i hi
    have hL : 1 ≤ length i := hKpos (length i) (hlength_mem i hi)
    have hphase : |θ i| ≤ C * |field (anchor i)| * energy i * (length i : ℝ) ^ n := by
      rw [hθ i hi]
      have h := twoPi_fillPairing_abs_le (fill i) field |field (anchor i)|
        (Cfill * energy i * (length i : ℝ) ^ n) (abs_nonneg _) (hfieldMax i hi) (hfillMass i hi)
      refine h.trans (le_of_eq ?_)
      rw [hC]
      ring
    have h := jensen_per_current_poly n a C (energy i) |field (anchor i)| (z i) (θ i) (length i)
      ha ha1 (henergy i hi) (hz0 i hi) (hz i hi) hL hphase
    rwa [sq_abs] at h
  let key : I → P × ℕ := fun i => (anchor i, length i)
  let keys : Finset (P × ℕ) := Finset.univ ×ˢ K
  have hkeys : ∀ i ∈ T, key i ∈ keys := by
    intro i hi
    simp only [keys, Finset.mem_product, Finset.mem_univ, true_and]
    exact hlength_mem i hi
  have hsplit := Finset.sum_fiberwise_of_maps_to hkeys error
  change (∑ i ∈ T, error i) ≤ _
  rw [← hsplit, Finset.sum_product]
  calc (∑ p, ∑ L ∈ K, ∑ i ∈ T with key i = (p, L), error i)
      ≤ ∑ p, ∑ L ∈ K, (((Cbox : ℝ) * (L : ℝ) ^ n) * polyActivity n a C L) * (field p) ^ 2 := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun L hL => ?_
        let U : Finset I := T.filter (fun i => key i = (p, L))
        have hdisjU : (↑U : Set I).PairwiseDisjoint support := by
          intro i hi j hj hij
          exact hdisj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
        have hsubU : ∀ i ∈ U, support i ⊆ box p L := by
          intro i hi
          obtain ⟨hiT, hiKey⟩ := Finset.mem_filter.mp hi
          have hpEq : anchor i = p := congrArg Prod.fst hiKey
          have hLEq : length i = L := congrArg Prod.snd hiKey
          simpa [hpEq, hLEq] using hlocal i hiT
        have hsizeU : ∀ i ∈ U, (support i).card = L := by
          intro i hi
          obtain ⟨hiT, hiKey⟩ := Finset.mem_filter.mp hi
          have hLEq : length i = L := congrArg Prod.snd hiKey
          simpa [hLEq] using hsize i hiT
        have hmul := card_mul_le_of_disjoint_supports U support (box p L) L hdisjU hsubU hsizeU
        have hL1 : 1 ≤ L := hKpos L hL
        have hUCard : U.card ≤ Cbox * L ^ n :=
          (Nat.le_mul_of_pos_right _ hL1).trans (hmul.trans (hbox p L))
        have hUCardR : (U.card : ℝ) ≤ (Cbox : ℝ) * (L : ℝ) ^ n := by exact_mod_cast hUCard
        have hact : 0 ≤ polyActivity n a C L * (field p) ^ 2 :=
          mul_nonneg (polyActivity_nonneg n a C L) (sq_nonneg _)
        calc (∑ i ∈ U, error i) ≤ ∑ i ∈ U, polyActivity n a C L * (field p) ^ 2 := by
              refine Finset.sum_le_sum fun i hi => ?_
              obtain ⟨hiT, hiKey⟩ := Finset.mem_filter.mp hi
              have hpEq : anchor i = p := congrArg Prod.fst hiKey
              have hLEq : length i = L := congrArg Prod.snd hiKey
              simpa [hpEq, hLEq] using herror i hiT
          _ = (U.card : ℝ) * (polyActivity n a C L * (field p) ^ 2) := by simp
          _ ≤ ((Cbox : ℝ) * (L : ℝ) ^ n) * (polyActivity n a C L * (field p) ^ 2) :=
              mul_le_mul_of_nonneg_right hUCardR hact
          _ = (((Cbox : ℝ) * (L : ℝ) ^ n) * polyActivity n a C L) * (field p) ^ 2 := by ring
    _ ≤ polyPackingConstant n Cbox a C * (∑ p, (field p) ^ 2) :=
        sum_l2_with_length_budget K field
          (fun L => ((Cbox : ℝ) * (L : ℝ) ^ n) * polyActivity n a C L)
          (polyPackingConstant n Cbox a C) (polyActivity_budget_le n Cbox a C ha K)

/-- The polynomial-geometric tail at unit rate. -/
noncomputable def polyTail (m : ℕ) : ℝ := ∑' L : ℕ, (L : ℝ) ^ m * Real.exp (-(1 * (L : ℝ)))

theorem polyTail_nonneg (m : ℕ) : 0 ≤ polyTail m :=
  tsum_nonneg fun L => by positivity

/-- **The packing constant is exponentially small in the rate.** -/
theorem polyPackingConstant_le_exponential_tail (n Cbox : ℕ) (hn : 0 < n) (a C : ℝ)
    (ha : 0 < a) (ha1 : 1 ≤ a) :
    polyPackingConstant n Cbox a C ≤
      (20 * (Cbox : ℝ) * C ^ 2 / a ^ 2) * Real.exp (1 - a) * polyTail (3 * n) := by
  let fA : ℕ → ℝ := fun L => (L : ℝ) ^ (3 * n) * Real.exp (-(a * (L : ℝ)))
  let f1 : ℕ → ℝ := fun L => (L : ℝ) ^ (3 * n) * Real.exp (-(1 * (L : ℝ)))
  have hsA : Summable fA := summable_pow_mul_exp (3 * n) a ha
  have hs1 : Summable f1 := summable_pow_mul_exp (3 * n) 1 (by norm_num)
  have hpoint : ∀ L, fA L ≤ Real.exp (1 - a) * f1 L := by
    intro L
    by_cases hL : L = 0
    · subst hL
      have h3 : 3 * n ≠ 0 := by omega
      simp [fA, f1, h3]
    · have hLpos : 1 ≤ (L : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hL)
      have hexp : Real.exp (-(a * (L : ℝ))) ≤ Real.exp (1 - a) * Real.exp (-(1 * (L : ℝ))) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc fA L = (L : ℝ) ^ (3 * n) * Real.exp (-(a * (L : ℝ))) := rfl
        _ ≤ (L : ℝ) ^ (3 * n) * (Real.exp (1 - a) * Real.exp (-(1 * (L : ℝ)))) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Real.exp (1 - a) * f1 L := by
            simp only [f1]
            ring
  have hscaled : Summable (fun L => Real.exp (1 - a) * f1 L) := hs1.mul_left _
  have htsum := Summable.tsum_le_tsum hpoint hsA hscaled
  have hscale : (∑' L : ℕ, Real.exp (1 - a) * f1 L) = Real.exp (1 - a) * polyTail (3 * n) :=
    hs1.tsum_mul_left (Real.exp (1 - a))
  have hcoef : 0 ≤ 20 * (Cbox : ℝ) * C ^ 2 / a ^ 2 := by positivity
  calc polyPackingConstant n Cbox a C = (20 * (Cbox : ℝ) * C ^ 2 / a ^ 2) * ∑' L : ℕ, fA L := rfl
    _ ≤ (20 * (Cbox : ℝ) * C ^ 2 / a ^ 2) * (Real.exp (1 - a) * polyTail (3 * n)) := by
        rw [← hscale]
        exact mul_le_mul_of_nonneg_left htsum hcoef
    _ = (20 * (Cbox : ℝ) * C ^ 2 / a ^ 2) * Real.exp (1 - a) * polyTail (3 * n) := by ring

end FroehlichSpencer.FS82.XY.DualD

end
