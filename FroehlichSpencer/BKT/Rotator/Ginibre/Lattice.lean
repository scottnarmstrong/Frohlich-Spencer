/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.System
public import FroehlichSpencer.BKT.Rotator.Ginibre.LatticeStep

/-!
# The free-boundary plane rotator on finite domains of `ℤ²`

For a finite set `Λ ⊆ ℤ²` the free-boundary plane rotator state of FS81 (1.26), J p. 533, is
`Z_Λ⁻¹ ∏_{(ij) ⊂ Λ} exp(β cos(θ_i - θ_j)) ∏_{j ∈ Λ} dθ_j`, the product running over the
nearest-neighbour pairs of `Λ`. It is the cosine Gibbs measure with one coupling `β` on every
ordered pair of sites of `Λ` that is a positive nearest-neighbour step, and coupling `0` on all other
ordered pairs. The two-point function `⟨cos(ξ(θ_u - θ_v))⟩_Λ(β)` is nonnegative (Ginibre I),
increases with the domain (FS81, J pp. 535, 585: a consequence of Ginibre's inequalities) and with
`β`, and is invariant under translating the domain together with the two sites.
-/

@[expose] public section

open MeasureTheory
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

/-- The frequency `δ_x - δ_y` of an ordered pair of sites. -/
def bondFrequency (Λ : Finset (ℤ × ℤ)) (b : Λ × Λ) : Frequency Λ :=
  fun x => (if x = b.1 then 1 else 0) - (if x = b.2 then 1 else 0)

/-- Free-boundary couplings: `β` on the positive nearest-neighbour steps of `Λ`, `0` otherwise. -/
def freeCoupling (β : ℝ) (Λ : Finset (ℤ × ℤ)) (b : Λ × Λ) : ℝ :=
  if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then β else 0

/-- The free-boundary plane rotator state on the finite domain `Λ ⊆ ℤ²`, FS81 (1.26). -/
def freeRotatorMeasure (β : ℝ) (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  cosineGibbs (bondFrequency Λ) (freeCoupling β Λ)

/-- The angle at a point of `ℤ²`, extended by zero outside `Λ`. -/
def latticeAngle {Λ : Finset (ℤ × ℤ)} (θ : Λ → ℝ) (z : ℤ × ℤ) : ℝ :=
  if h : z ∈ Λ then θ ⟨z, h⟩ else 0

/-- The finite-volume free-boundary two-point function `⟨cos(ξ(θ_u - θ_v))⟩_Λ(β)`. -/
def freeTwoPoint (β : ℝ) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : ℝ :=
  ∫ θ, Real.cos (ξ * (latticeAngle θ u - latticeAngle θ v)) ∂freeRotatorMeasure β Λ

/-- The frequency `ξ (δ_u - δ_v)` of the two-point observable on `Λ`. -/
def twoPointFrequency (Λ : Finset (ℤ × ℤ)) (ξ : ℤ) (u v : ℤ × ℤ) : Frequency Λ :=
  fun x => ξ * ((if (x : ℤ × ℤ) = u then 1 else 0) - (if (x : ℤ × ℤ) = v then 1 else 0))

/-- The domain `Λ + w`. -/
def translateDomain (Λ : Finset (ℤ × ℤ)) (w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Λ.map (addRightEmbedding w)

variable {Λ : Finset (ℤ × ℤ)}

theorem mem_translateDomain {w z : ℤ × ℤ} : z ∈ translateDomain Λ w ↔ z - w ∈ Λ := by
  simp only [translateDomain, Finset.mem_map, addRightEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨z - w, h, sub_add_cancel z w⟩

theorem sum_ite_coe_eq (θ : Λ → ℝ) (u : ℤ × ℤ) :
    ∑ x : Λ, (if (x : ℤ × ℤ) = u then θ x else 0) = latticeAngle θ u := by
  classical
  unfold latticeAngle
  split_ifs with hu
  · rw [Fintype.sum_eq_single ⟨u, hu⟩ fun x hx => ite_eq_right fun h => hx (Subtype.ext h)]
    simp
  · exact Finset.sum_eq_zero fun x _ =>
      ite_eq_right fun h : (x : ℤ × ℤ) = u => hu (h ▸ x.2)

theorem phase_bondFrequency (b : Λ × Λ) (θ : Λ → ℝ) :
    phase (bondFrequency Λ b) θ = θ b.1 - θ b.2 := by
  classical
  simp only [phase, bondFrequency, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem phase_twoPointFrequency (ξ : ℤ) (u v : ℤ × ℤ) (θ : Λ → ℝ) :
    phase (twoPointFrequency Λ ξ u v) θ = ξ * (latticeAngle θ u - latticeAngle θ v) := by
  simp only [phase, twoPointFrequency, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero, mul_assoc, sub_mul, ite_mul, one_mul, zero_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, sum_ite_coe_eq]

theorem continuous_latticeAngle (u : ℤ × ℤ) :
    Continuous fun θ : Λ → ℝ => latticeAngle θ u := by
  unfold latticeAngle
  split_ifs
  exacts [continuous_apply _, continuous_const]

theorem freeCoupling_nonneg {β : ℝ} (hβ : 0 ≤ β) (b : Λ × Λ) : 0 ≤ freeCoupling β Λ b := by
  unfold freeCoupling
  split_ifs
  exacts [hβ, le_rfl]

theorem freeTwoPoint_eq_integral_cos (β : ℝ) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    freeTwoPoint β ξ Λ u v =
      ∫ θ, Real.cos (phase (twoPointFrequency Λ ξ u v) θ) ∂freeRotatorMeasure β Λ := by
  simp only [freeTwoPoint, phase_twoPointFrequency]

instance isProbabilityMeasure_freeRotatorMeasure (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    IsProbabilityMeasure (freeRotatorMeasure β Λ) := by
  unfold freeRotatorMeasure
  infer_instance

/-- Ginibre I for the two-point function. -/
theorem freeTwoPoint_nonneg {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    0 ≤ freeTwoPoint β ξ Λ u v := by
  rw [freeTwoPoint_eq_integral_cos]
  exact integral_cos_cosineGibbs_nonneg _ (freeCoupling_nonneg hβ) _

theorem freeTwoPoint_le_one (β : ℝ) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    freeTwoPoint β ξ Λ u v ≤ 1 := by
  rw [freeTwoPoint_eq_integral_cos]
  exact integral_cos_cosineGibbs_le_one _ _ _

theorem freeTwoPoint_comm (β : ℝ) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    freeTwoPoint β ξ Λ u v = freeTwoPoint β ξ Λ v u := by
  unfold freeTwoPoint
  congr 1
  funext θ
  rw [← Real.cos_neg]
  congr 1
  ring

theorem freeTwoPoint_self (β : ℝ) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    freeTwoPoint β ξ Λ u u = 1 := by
  simp [freeTwoPoint]

/-- Monotonicity in the inverse temperature. -/
theorem freeTwoPoint_mono_beta {β β' : ℝ} (hβ : 0 ≤ β) (hββ' : β ≤ β') (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    freeTwoPoint β ξ Λ u v ≤ freeTwoPoint β' ξ Λ u v := by
  rw [freeTwoPoint_eq_integral_cos, freeTwoPoint_eq_integral_cos]
  refine integral_cos_cosineGibbs_mono _ (freeCoupling_nonneg hβ) (fun b => ?_) _
  unfold freeCoupling
  split_ifs
  exacts [hββ', le_rfl]

/-- **Domain monotonicity** (free boundary conditions): enlarging the domain increases the
two-point function of two sites of the smaller domain. -/
theorem freeTwoPoint_mono_domain {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) {Λ Λ' : Finset (ℤ × ℤ)}
    (hΛ : Λ ⊆ Λ') {u v : ℤ × ℤ} (hu : u ∈ Λ) (hv : v ∈ Λ) :
    freeTwoPoint β ξ Λ u v ≤ freeTwoPoint β ξ Λ' u v := by
  classical
  rw [freeTwoPoint_eq_integral_cos, freeTwoPoint_eq_integral_cos]
  let ι : Λ → Λ' := fun x => ⟨x.1, hΛ x.2⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  let J'' : Λ' × Λ' → ℝ := fun b =>
    if (b.1 : ℤ × ℤ) ∈ Λ ∧ (b.2 : ℤ × ℤ) ∈ Λ then freeCoupling β Λ' b else 0
  refine integral_cos_cosineGibbs_le_of_embedding (J'' := J'') _ _ _ (fun b => ?_)
    (fun b => ?_) hι (fun θ' => ?_) _ _ (fun θ' => ?_)
  · simp only [J'']
    split_ifs
    exacts [freeCoupling_nonneg hβ b, le_rfl]
  · simp only [J'']
    split_ifs
    exacts [le_rfl, freeCoupling_nonneg hβ b]
  · simp only [cosineEnergy, phase_bondFrequency]
    symm
    refine Fintype.sum_of_injective (Prod.map ι ι) (hι.prodMap hι) _ _ (fun b hb => ?_)
      (fun a => ?_)
    · simp only [J'']
      rw [ite_eq_right, zero_mul]
      rintro ⟨h₁, h₂⟩
      exact hb ⟨(⟨b.1, h₁⟩, ⟨b.2, h₂⟩), rfl⟩
    · simp only [J'', Prod.map_fst, Prod.map_snd, ι, Finset.coe_mem, and_self, ite_true]
      rfl
  · rw [phase_twoPointFrequency, phase_twoPointFrequency]
    simp only [latticeAngle, dite_eq_left hu, dite_eq_left hv, dite_eq_left (hΛ hu),
      dite_eq_left (hΛ hv), Function.comp_apply, ι]

/-- The translation `x ↦ x + w` from `Λ` onto `Λ + w`. -/
def translateEquiv (Λ : Finset (ℤ × ℤ)) (w : ℤ × ℤ) : Λ ≃ translateDomain Λ w where
  toFun x := ⟨x.1 + w, mem_translateDomain.mpr (by simp)⟩
  invFun y := ⟨y.1 - w, mem_translateDomain.mp y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

theorem latticeAngle_translate (w : ℤ × ℤ) (θ' : translateDomain Λ w → ℝ) (u : ℤ × ℤ) :
    latticeAngle (θ' ∘ translateEquiv Λ w) u = latticeAngle θ' (u + w) := by
  unfold latticeAngle
  by_cases hu : u ∈ Λ
  · rw [dite_eq_left hu, dite_eq_left (mem_translateDomain.mpr (by simpa using hu))]
    rfl
  · rw [dite_eq_right hu, dite_eq_right (fun h => hu (by simpa using mem_translateDomain.mp h))]

/-- **Translation invariance** of the finite-volume two-point function. -/
theorem freeTwoPoint_translate (β : ℝ) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v w : ℤ × ℤ) :
    freeTwoPoint β ξ (translateDomain Λ w) (u + w) (v + w) = freeTwoPoint β ξ Λ u v := by
  classical
  unfold freeTwoPoint freeRotatorMeasure
  have h := integral_comp_cosineGibbs (bondFrequency Λ) (freeCoupling β Λ)
    (bondFrequency (translateDomain Λ w)) (freeCoupling β (translateDomain Λ w))
    (translateEquiv Λ w).injective (fun θ' => ?_)
    (f := fun θ => Real.cos (ξ * (latticeAngle θ u - latticeAngle θ v))) ?_
  · simpa only [latticeAngle_translate] using h
  · simp only [cosineEnergy, phase_bondFrequency]
    symm
    refine Fintype.sum_equiv ((translateEquiv Λ w).prodCongr (translateEquiv Λ w)) _ _
      (fun a => ?_)
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Function.comp_apply,
      freeCoupling, LatticeStep, translateEquiv, Equiv.coe_fn_mk]
    have hshift (x y e : ℤ × ℤ) : y + w = x + w + e ↔ y = x + e := by
      rw [add_right_comm, add_left_inj]
    congr 1
    exact if_congr (by simp only [hshift]) rfl rfl
  · exact (Real.continuous_cos.comp (continuous_const.mul
      ((continuous_latticeAngle u).sub (continuous_latticeAngle v)))).measurable

end FroehlichSpencer.BKT.Rotator.Ginibre

end
