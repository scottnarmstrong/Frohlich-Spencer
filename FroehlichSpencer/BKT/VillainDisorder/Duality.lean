/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.ShiftedVillain
public import FroehlichSpencer.BKT.Duality.Expectation
public import FroehlichSpencer.BKT.Bridge.WiredVillainModel
import Mathlib.Tactic

/-!
# The exact disorder duality on the wired box

FS81's disorder operator (1.32) for the Villain model (`f_β = v_β`), J p. 534, with `x = (n, 0)`:
`D^ξ_{0x} = ∏_{m=1}^n v_β(θ_{(m,1)} − θ_{(m,0)} + 2πξ)/v_β(θ_{(m,1)} − θ_{(m,0)})`.

It is taken on the wired box `Λ_L^zero` (`villainLaw`), with the string translated to start
at a site `o` of the box.

Its dual is FS81 (1.38) (J p. 535, proved in FS81 Appendix A):
`⟨D^ξ_{0x}⟩ = ⟨e^{2πiξ(φ_0 − φ_x)}⟩^*`.

Here it is exact in finite volume.

* The disorder operator is the `ShiftedVillain` shift ratio for the shift `2πξ` on the `n` string
  bonds (`villainShiftRatio_stringShift`).
* `neutralCurrentHeightEquiv` identifies the neutral wired currents with the pinned integer
  heights on the dual free square of side `L + 1`.

Along the dual faces `stringFace`, the string
  phase telescopes to `2πξ(h(x*) − h(0*))` (`sum_dualHeightGradient_stringShift`).
* **`villainLaw_disorder_eq_igff`**: `⟨D^ξ⟩_{Λ_L^zero}(β)` is the IGFF expectation of
  `cos(2πξ(h(x*) − h(0*)))`, at inverse temperature `1/β`, on the dual free square rooted at
  `dualBoxRoot L`.

**Boundary condition.** The primal box is wired (`Λ_L^zero`, the KP setting), so the dual
integer field has free boundary condition.

FS81 (1.35) instead sets the dual field to `0` outside
`Λ`, which is dual to a free primal box.

That case is not treated here.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FroehlichSpencer.BKT.VillainDisorder

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Duality FroehlichSpencer.BKT.Lattice2D

variable {L : ℕ}

/-! ### FS81's disorder operator on the wired box -/

/-- The upper end `(o₁ + m + 1, o₂ + 1)` of the `m`-th bond of the disorder string. -/
def stringUpper (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L)
    (m : Fin n) : Fin L × Fin L :=
  (⟨o.1.val + m.val + 1, by omega⟩, ⟨o.2.val + 1, hfit.2⟩)

/-- The lower end `(o₁ + m + 1, o₂)` of the `m`-th bond of the disorder string. -/
def stringLower (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L)
    (m : Fin n) : Fin L × Fin L :=
  (⟨o.1.val + m.val + 1, by omega⟩, o.2)

/--
**FS81's disorder operator (1.32)** for the Villain model on the wired box `Λ_L^zero`
( carrier, `θ none` the wired angle): with `0 = o` and `x = o + (n, 0)`,
`D^ξ_{0x} = ∏_{m=1}^{n} v_β(θ_{(o₁+m, o₂+1)} − θ_{(o₁+m, o₂)} + 2πξ) /
v_β(θ_{(o₁+m, o₂+1)} − θ_{(o₁+m, o₂)})`.

The string must fit in the box (`o₁ + n < L`, `o₂ + 1 < L`).
-/
def villainDisorderInternal (β ξ : ℝ) (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (θ : Option (Fin L × Fin L) → ℝ) : ℝ :=
  ∏ m : Fin n,
    villainWeight β (θ (some (stringUpper o n hfit m)) - θ (some (stringLower o n hfit m)) +
        2 * Real.pi * ξ) /
      villainWeight β (θ (some (stringUpper o n hfit m)) - θ (some (stringLower o n hfit m)))

/-- The wired edge of the `m`-th bond: the dual horizontal edge from the dual face
`(o₁ + m + 1, o₂ + 1)` to `(o₁ + m + 2, o₂ + 1)`. -/
def stringEdge (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L)
    (m : Fin n) : WiredEdge L :=
  .inl (horizontalDualEdgeData (stringUpper o n hfit m).1 (lowIndex (stringUpper o n hfit m).2))

theorem stringEdge_injective (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) : Function.Injective (stringEdge o n hfit) := by
  intro m m' h
  simp only [stringEdge, horizontalDualEdgeData, lowIndex, Sum.inl.injEq, Prod.mk.injEq,
    Subtype.mk.injEq, Fin.ext_iff, Fin.val_castLE, stringUpper] at h
  exact Fin.ext (by omega)

theorem wiredBox_src_stringEdge (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (m : Fin n) :
    (wiredBoxGraph L).src (stringEdge o n hfit m) = some (stringUpper o n hfit m) := by
  change horizontalPrimalSrc _ = _
  rw [horizontalPrimalSrc_eq_some_iff]

theorem wiredBox_tgt_stringEdge (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (m : Fin n) :
    (wiredBoxGraph L).tgt (stringEdge o n hfit m) = some (stringLower o n hfit m) := by
  show horizontalPrimalTgt (horizontalDualEdgeData (stringUpper o n hfit m).1
    (lowIndex (stringUpper o n hfit m).2)) = _
  have h0 : (horizontalDualEdgeData (stringUpper o n hfit m).1
      (lowIndex (stringUpper o n hfit m).2)).2.val ≠ 0 := by
    simp [horizontalDualEdgeData, lowIndex, stringUpper]
  unfold horizontalPrimalTgt
  rw [dite_eq_right h0]
  simp only [Option.some.injEq]
  ext <;> simp [horizontalFaceX, horizontalDualEdgeData, lowIndex, stringUpper, stringLower]

/-- The bond shifts of the disorder string: `2πξ` on the string edges, zero elsewhere. -/
def stringShift (ξ : ℝ) (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L)
    (e : WiredEdge L) : ℝ :=
  if e ∈ Finset.univ.image (stringEdge o n hfit) then 2 * Real.pi * ξ else 0

theorem villainShiftRatio_stringShift (β ξ : ℝ) (hβ : 0 < β) (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (θ : Villain.FreeAngles (WiredVertex L) none) :
    Villain.villainShiftRatio (wiredBoxGraph L) none β (stringShift ξ o n hfit) θ =
      villainDisorderInternal β ξ o n hfit (sourcePinnedAngle L θ) := by
  classical
  unfold Villain.villainShiftRatio villainDisorderInternal sourcePinnedAngle
  set S := Finset.univ.image (stringEdge o n hfit) with hS
  rw [← Finset.prod_subset (Finset.subset_univ S) fun e _ he => ?_]
  · rw [hS, Finset.prod_image fun m _ m' _ h => stringEdge_injective o n hfit h]
    refine Finset.prod_congr rfl fun m _ => ?_
    have hmem : stringEdge o n hfit m ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (by simp)
    rw [wiredBox_src_stringEdge, wiredBox_tgt_stringEdge]
    simp only [stringShift, ← hS, hmem, ↓reduceIte]
  · simp only [stringShift, ← hS, he, ↓reduceIte, add_zero]
    exact div_self (VillainWeight.villainWeight_pos hβ _).ne'

/-! ### The dual heights along the string -/

/-- The dual face `(o₁ + k + 1, o₂ + 1)` of the free dual square of side `L + 1`, `k ≤ n`. -/
def stringFace (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L)
    (k : ℕ) : SquareFreeVertex (L + 1) :=
  (⟨min (o.1.val + k + 1) L, by omega⟩, ⟨o.2.val + 1, by omega⟩)

theorem dualHeightGradient_stringEdge (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (h : SquareFreeVertex (L + 1) → ℤ) (m : Fin n) :
    dualHeightGradient h (stringEdge o n hfit m) =
      h (stringFace o n hfit (m.val + 1)) - h (stringFace o n hfit m.val) := by
  unfold dualHeightGradient
  have hsrc : (dualBoxGraph L).src (stringEdge o n hfit m) = stringFace o n hfit m.val := by
    simp only [dualBoxGraph, squareFreeGraph, stringEdge, horizontalDualEdgeData, stringFace,
      lowIndex, stringUpper]
    ext <;> (simp; try omega)
  have htgt : (dualBoxGraph L).tgt (stringEdge o n hfit m) = stringFace o n hfit (m.val + 1) := by
    simp only [dualBoxGraph, squareFreeGraph, stringEdge, horizontalDualEdgeData, stringFace,
      lowIndex, stringUpper]
    ext <;> (simp; try omega)
  rw [hsrc, htgt]

/-- Telescoping along the string: `∑_e q_e s_e = 2πξ (h(x') − h(0'))` for `q = ∇h`. -/
theorem sum_dualHeightGradient_stringShift (ξ : ℝ) (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (h : SquareFreeVertex (L + 1) → ℤ) :
    ∑ e, (dualHeightGradient h e : ℝ) * stringShift ξ o n hfit e =
      2 * Real.pi * ξ * ((h (stringFace o n hfit n) : ℝ) - h (stringFace o n hfit 0)) := by
  classical
  have h1 : ∑ e, (dualHeightGradient h e : ℝ) * stringShift ξ o n hfit e =
      ∑ e ∈ Finset.univ.image (stringEdge o n hfit),
        (dualHeightGradient h e : ℝ) * (2 * Real.pi * ξ) := by
    rw [← Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_]
    · refine Finset.sum_congr rfl fun e he => ?_
      simp only [stringShift, he, ↓reduceIte]
    · simp only [stringShift, he, ↓reduceIte, mul_zero]
  rw [h1, Finset.sum_image fun m _ m' _ hm => stringEdge_injective o n hfit hm,
    ← Finset.sum_mul]
  have htel : ∑ m : Fin n, (dualHeightGradient h (stringEdge o n hfit m) : ℝ) =
      (h (stringFace o n hfit n) : ℝ) - h (stringFace o n hfit 0) := by
    simp_rw [dualHeightGradient_stringEdge]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun k => (h (stringFace o n hfit (k + 1)) : ℝ) -
      h (stringFace o n hfit k)) n]
    exact Finset.sum_range_sub (fun k => (h (stringFace o n hfit k) : ℝ)) n
  rw [htel]
  ring

/-! ### The disorder duality -/

private theorem tsum_if_subtype {α : Type*} (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    (∑' a, if P a then f a else 0) = ∑' a : {a // P a}, f a.1 := by
  calc (∑' a, if P a then f a else 0) = ∑' a, ({a | P a} : Set α).indicator f a := by
        refine tsum_congr fun a => ?_
        by_cases ha : P a <;> simp [Set.indicator, ha]
    _ = ∑' a : {a // P a}, f a.1 := (tsum_subtype {a | P a} f).symm

/-- The neutral current sum with the string phase is the IGFF sum of the dual height cosine. -/
theorem neutralCurrent_tsum_cos_eq (β ξ : ℝ) (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) :
    (∑' q : WiredEdge L → ℤ, Villain.neutralCurrentGaussianWeight (wiredBoxGraph L) none β q *
        Real.cos (∑ e, (q e : ℝ) * stringShift ξ o n hfit e)) =
      ∑' h : PinnedDualHeight L, Real.cos (2 * Real.pi * ξ *
          ((h.1 (stringFace o n hfit n) : ℝ) - h.1 (stringFace o n hfit 0))) *
        igffWeight (dualBoxGraph L) (1 / β) h := by
  classical
  have hrw : ∀ q : WiredEdge L → ℤ,
      Villain.neutralCurrentGaussianWeight (wiredBoxGraph L) none β q *
        Real.cos (∑ e, (q e : ℝ) * stringShift ξ o n hfit e) =
      if Villain.neutralAwayFrom (wiredBoxGraph L) none q then
        Villain.currentGaussianWeight β q * Real.cos (∑ e, (q e : ℝ) * stringShift ξ o n hfit e)
      else 0 := fun q => by
    unfold Villain.neutralCurrentGaussianWeight
    split_ifs <;> simp
  rw [tsum_congr hrw, tsum_if_subtype]
  let eq := neutralCurrentHeightEquiv (L := L)
  change (∑' q : NeutralWiredCurrent L, Villain.currentGaussianWeight β q.1 *
    Real.cos (∑ e, (q.1 e : ℝ) * stringShift ξ o n hfit e)) = _
  rw [← Equiv.tsum_eq eq]
  refine tsum_congr fun h => ?_
  change Villain.currentGaussianWeight β (dualHeightGradient h.1) *
      Real.cos (∑ e, (dualHeightGradient h.1 e : ℝ) * stringShift ξ o n hfit e) = _
  rw [currentGaussianWeight_dualHeightGradient_eq_igffWeight,
    sum_dualHeightGradient_stringShift, mul_comm]

/-- **The exact finite disorder duality** (FS81 (1.38), Appendix A, on the wired box): the
Villain disorder expectation on `Λ_L^zero` equals the rooted dual IGFF expectation, at inverse
temperature `1/β` on the free dual square of side `L + 1`, of `cos(2πξ (h(x') − h(0')))`, where
`0' = (o₁ + 1, o₂ + 1)` and `x' = (o₁ + n + 1, o₂ + 1)` are the dual faces at the two ends of
the string. -/
theorem villainLaw_disorder_eq_igff (hL : 0 < L) (β : ℝ) (hβ : 0 < β) (ξ : ℝ)
    (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) :
    (∫ θ, villainDisorderInternal β ξ o n hfit θ ∂villainLaw L β hβ) =
      igffExpectation (dualBoxGraph L) (dualBoxGraph_connected hL) (1 / β)
        (one_div_pos.mpr hβ) (dualBoxRoot L)
        (fun h => Real.cos (2 * Real.pi * ξ *
          ((h.1 (stringFace o n hfit n) : ℝ) - h.1 (stringFace o n hfit 0)))) := by
  have hmeas : Measurable (villainDisorderInternal (L := L) β ξ o n hfit) := by
    unfold villainDisorderInternal
    refine Finset.measurable_prod _ fun m _ => ?_
    have hv := (Villain.continuous_villainWeight β hβ).measurable
    exact (hv.comp (by fun_prop)).div (hv.comp (by fun_prop))
  rw [← villainLaw_map_sourcePinnedAngle L β hβ,
    integral_map (sourcePinnedAngle_measurable L).aemeasurable hmeas.aestronglyMeasurable]
  simp_rw [← villainShiftRatio_stringShift β ξ hβ o n hfit]
  rw [Villain.integral_villainShiftRatio, neutralCurrent_tsum_cos_eq,
    neutralCurrent_tsum_eq_igffPartitionFunction]
  rfl

end FroehlichSpencer.BKT.VillainDisorder
