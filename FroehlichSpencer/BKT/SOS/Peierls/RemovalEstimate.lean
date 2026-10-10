/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Peierls.RemovalWeight
public import FroehlichSpencer.BKT.SOS.Peierls.Removal
public import FroehlichSpencer.BKT.SOS.Roughening.Moment
public import FroehlichSpencer.BKT.SOS.Roughening.Weight
import Mathlib.Tactic

/-! # Countable fixed-contour SOS removal estimate -/

@[expose] public section

noncomputable section

open Classical
open scoped BigOperators
open FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

namespace FroehlichSpencer.BKT.SOS.Peierls

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight sosPartition)

/-- Zero-outer integer fields on the expanded box. -/
abbrev ZeroOuterSOSHeight (L : ℕ) :=
  {n : Lattice2D.SquareFreeVertex (L + 2) → ℤ // zeroOnOuterLayer n}

/-- The zero-outer fields carrying a specified nonzero saturated contour on inner-touching edges. -/
def sosContourEvent {L : ℕ} (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :
    Set (ZeroOuterSOSHeight L) := {c |
      (∀ e ∈ Γ, isInnerVertex L ((squareFreeGraph (L + 2)).src e) ∨
        isInnerVertex L ((squareFreeGraph (L + 2)).tgt e)) ∧
      squareFreePlaquetteSaturated ((squareFreeGraph (L + 2)).grad c.1) Γ ∧
      ∀ e ∈ Γ, (squareFreeGraph (L + 2)).grad c.1 e ≠ 0}

/-- The event carrier is just the removable-height carrier with its zero-outer proof factored out. -/
def sosContourEventEquiv {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :
    RemovableSOSHeight Γ ≃ {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ} where
  toFun n := ⟨⟨n.1, n.2.1⟩, by simpa [sosContourEvent] using n.2.2⟩
  invFun c := ⟨c.1.1, c.1.2, by simpa [sosContourEvent] using c.2⟩
  left_inv n := rfl
  right_inv c := rfl

/-- The removed height and its nonzero contour labels, now with the zero-outer condition retained
in the configuration carrier. -/
def sosContourRemovalEncoding {L : ℕ} (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (n : RemovableSOSHeight Γ) : ZeroOuterSOSHeight L × IntegerContourLabel Γ :=
  (⟨contourRemovedHeight Γ n, (contourRemovedHeight_spec Γ n).1⟩,
    (integerContourRemovalEncoding Γ n).2)

theorem sosContourRemovalEncoding_injective {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :
    Function.Injective (sosContourRemovalEncoding Γ) := by
  intro n m h
  apply integerContourRemovalEncoding_injective Γ
  have h' :
      (contourRemovedHeight Γ n,
        (integerContourRemovalEncoding Γ n).2) =
      (contourRemovedHeight Γ m,
        (integerContourRemovalEncoding Γ m).2) := by
    exact congrArg (fun p : ZeroOuterSOSHeight L × IntegerContourLabel Γ =>
      (p.1.1, p.2)) h
  simpa [sosContourRemovalEncoding, integerContourRemovalEncoding] using h'

/-- Countable weighted contour removal for an SOS height contour. The activity at one edge
includes a nonnegative observable factor `g(d)`. -/
theorem sosContourRemoval_tsum {L : ℕ}
    (β : ℝ) (_hβ : 0 ≤ β) (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (g : ℤ → ℝ) (hg : ∀ d, 0 ≤ g d) :
    (∑' n : RemovableSOSHeight Γ,
      ENNReal.ofReal (expandedSOSWeight L β n.1 *
        ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad n.1 e))) ≤
      (∑' c : ZeroOuterSOSHeight L, ENNReal.ofReal (expandedSOSWeight L β c.1)) *
        (∑' d : {d : ℤ // d ≠ 0},
          ENNReal.ofReal (g d.1 * Real.exp (-(β * |(d.1 : ℝ)|)))) ^ Γ.card := by
  classical
  let inst : Fintype {e : Lattice2D.SquareFreeEdge (L + 2) // e ∈ Γ} := inferInstance
  let a : {d : ℤ // d ≠ 0} → ENNReal := fun d =>
    ENNReal.ofReal (g d.1 * Real.exp (-(β * |(d.1 : ℝ)|)))
  let remove : RemovableSOSHeight Γ → ZeroOuterSOSHeight L × IntegerContourLabel Γ :=
    sosContourRemovalEncoding Γ
  let term (n : RemovableSOSHeight Γ) : ENNReal :=
    ENNReal.ofReal (expandedSOSWeight L β n.1 *
      ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad n.1 e))
  have hfactor (n : RemovableSOSHeight Γ) :
      term n =
        ENNReal.ofReal (expandedSOSWeight L β (remove n).1.1) *
          integerContourLabelActivity Γ inst a (remove n).2 := by
    dsimp [term, remove, sosContourRemovalEncoding, a]
    let label := (integerContourRemovalEncoding Γ n).2
    have hweight := expandedSOSWeight_eq_contourRemoved_mul_labels β Γ n
    have hreal :
        expandedSOSWeight L β n.1 *
            ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad n.1 e) =
          expandedSOSWeight L β (contourRemovedHeight Γ n) *
            ∏ e ∈ Γ,
              (g ((squareFreeGraph (L + 2)).grad n.1 e) *
                Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|))) := by
      calc
        _ = (expandedSOSWeight L β (contourRemovedHeight Γ n) *
              ∏ e ∈ Γ, Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|))) *
              ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad n.1 e) := by rw [hweight]
        _ = _ := by
          have hprod :
              (∏ e ∈ Γ,
                (g ((squareFreeGraph (L + 2)).grad n.1 e) *
                  Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)))) =
                (∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad n.1 e)) *
                  ∏ e ∈ Γ, Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)) := by
            rw [Finset.prod_mul_distrib]
          calc
            _ = expandedSOSWeight L β (contourRemovedHeight Γ n) *
                  ((∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad n.1 e)) *
                    ∏ e ∈ Γ, Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|))) := by
              ring
            _ = _ := congrArg (fun x => expandedSOSWeight L β (contourRemovedHeight Γ n) * x)
              hprod.symm
    have hprodRealNonneg (e : Lattice2D.SquareFreeEdge (L + 2)) (he : e ∈ Γ) :
        0 ≤ g ((squareFreeGraph (L + 2)).grad n.1 e) *
          Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)) :=
      mul_nonneg (hg _) (Real.exp_nonneg _)
    have hprodENN :
        ENNReal.ofReal (∏ e ∈ Γ,
            (g ((squareFreeGraph (L + 2)).grad n.1 e) *
              Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)))) =
          integerContourLabelActivity Γ inst a label := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun e he => hprodRealNonneg e he)]
      rw [Finset.prod_subtype (F := inst) Γ (fun _ => Iff.rfl)]
      simp [integerContourLabelActivity, a, label]
      apply Finset.prod_congr rfl
      intro edge hedge
      simp [integerContourRemovalEncoding]
    have hWpos : 0 < expandedSOSWeight L β (contourRemovedHeight Γ n) := by
      unfold expandedSOSWeight
      exact Finset.prod_pos fun _ _ => Real.exp_pos _
    rw [hreal, ENNReal.ofReal_mul hWpos.le]
    exact congrArg (fun x => ENNReal.ofReal
      (expandedSOSWeight L β (contourRemovedHeight Γ n)) * x) hprodENN
  have hremove : Function.Injective remove :=
    sosContourRemovalEncoding_injective Γ
  let A : Set (ZeroOuterSOSHeight L) := sosContourEvent Γ
  let decode : A → RemovableSOSHeight Γ := (sosContourEventEquiv Γ).symm
  let removeA : A → ZeroOuterSOSHeight L × IntegerContourLabel Γ := fun n => remove (decode n)
  let termA : A → ENNReal := fun n => term (decode n)
  have hremoveA : Function.Injective removeA := by
    intro n m h
    apply (sosContourEventEquiv Γ).symm.injective
    apply hremove
    exact h
  have hfactorA (n : A) :
      termA n = ENNReal.ofReal (expandedSOSWeight L β (removeA n).1.1) *
        integerContourLabelActivity Γ inst a (removeA n).2 := by
    exact hfactor (decode n)
  have hsumA : (∑' n : A, termA n) = ∑' n : RemovableSOSHeight Γ, term n := by
    simpa [termA, decode] using (sosContourEventEquiv Γ).symm.tsum_eq term
  rw [← hsumA]
  exact integerContourRemoval_tsum_pow Γ inst A
    (fun c : ZeroOuterSOSHeight L => ENNReal.ofReal (expandedSOSWeight L β c.1))
    a removeA hremoveA termA hfactorA

/-- Extending a pinned height by zero gives an equivalence with expanded fields that vanish on
the outer frame. -/
def sosExtensionEquiv (L : ℕ) :
    (Site L → ℤ) ≃ ZeroOuterSOSHeight L where
  toFun n := ⟨extendHeight L n, by
    intro x hx
    exact extendHeight_zero_of_not_inner n x hx⟩
  invFun n := restrictHeight n.1
  left_inv n := restrictHeight_extendHeight n
  right_inv n := by
    apply Subtype.ext
    exact extendHeight_restrictHeight n.1 n.2

/-- The pinned partition sum is exactly the expanded zero-outer partition sum. -/
theorem sosPartition_eq_expanded_tsum {L : ℕ} (β : ℝ) :
    sosPartition L β =
      ∑' c : ZeroOuterSOSHeight L, expandedSOSWeight L β c.1 := by
  unfold sosPartition
  calc
    (∑' n : Site L → ℤ, sosHeightWeight L β n) =
        ∑' n : Site L → ℤ, expandedSOSWeight L β (extendHeight L n) := by
      apply tsum_congr
      intro n
      rw [sosHeightWeight_eq_prod_expandedEdges β n]
      rfl
    _ = ∑' c : ZeroOuterSOSHeight L, expandedSOSWeight L β c.1 := by
      simpa [sosExtensionEquiv] using
        (sosExtensionEquiv L).tsum_eq
          (fun c : ZeroOuterSOSHeight L => expandedSOSWeight L β c.1)

/-- The fixed-contour estimate on the full zero-outer field carrier, written as a sum over its
specified contour event. -/
theorem sosContourEvent_tsum {L : ℕ} (β : ℝ) (hβ : 0 ≤ β)
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (g : ℤ → ℝ) (hg : ∀ d, 0 ≤ g d) :
    (∑' c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ},
      ENNReal.ofReal (expandedSOSWeight L β c.1.1 *
        ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad c.1.1 e))) ≤
      (∑' c : ZeroOuterSOSHeight L, ENNReal.ofReal (expandedSOSWeight L β c.1)) *
        (∑' d : {d : ℤ // d ≠ 0},
          ENNReal.ofReal (g d.1 * Real.exp (-(β * |(d.1 : ℝ)|)))) ^ Γ.card := by
  let E := sosContourEventEquiv Γ
  have hsum :
      (∑' c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ},
        ENNReal.ofReal (expandedSOSWeight L β c.1.1 *
          ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad c.1.1 e))) =
      (∑' n : RemovableSOSHeight Γ,
        ENNReal.ofReal (expandedSOSWeight L β n.1 *
          ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad n.1 e))) := by
    symm
    exact E.tsum_eq (fun c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ} =>
      ENNReal.ofReal (expandedSOSWeight L β c.1.1 *
        ∏ e ∈ Γ, g ((squareFreeGraph (L + 2)).grad c.1.1 e)))
  rw [hsum]
  exact sosContourRemoval_tsum β hβ Γ g hg

end FroehlichSpencer.BKT.SOS.Peierls

end
