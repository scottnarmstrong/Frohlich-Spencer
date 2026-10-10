/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Roughening.Comb
public import FroehlichSpencer.BKT.Clock.Peierls.GenericGradient
public import FroehlichSpencer.BKT.Clock.Peierls.GenericContours
public import FroehlichSpencer.BKT.Bridge.WiredBoxCarrier
import Mathlib.Tactic

/-! # Extension of a pinned SOS height to a free square

The pinned box is placed one lattice unit inside a larger free square.  Its four possible
missing-neighbour directions at each site index the bonds to the outer layer.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Peierls

open Classical
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site SquareZeroBond)
open FroehlichSpencer.BKT.SOS.Roughening
open FroehlichSpencer.BKT.Duality

/-- The square of side `L` inside the side-`L+2` free square. -/
def innerSite {L : ℕ} (x : Site L) : Lattice2D.SquareFreeVertex (L + 2) :=
  (⟨x.1.val + 1, by omega⟩, ⟨x.2.val + 1, by omega⟩)

/-- A free-square vertex is in the pinned inner square. -/
def isInnerVertex (L : ℕ) (x : Lattice2D.SquareFreeVertex (L + 2)) : Prop :=
  1 ≤ x.1.val ∧ x.1.val ≤ L ∧ 1 ≤ x.2.val ∧ x.2.val ≤ L

/-- Read an inner free-square vertex in the original box. -/
def innerSiteOfVertex {L : ℕ} (x : Lattice2D.SquareFreeVertex (L + 2))
    (hx : isInnerVertex L x) : Site L :=
  (⟨x.1.val - 1, by
      rcases hx with ⟨hx₁, hx₂, -, -⟩
      omega⟩,
    ⟨x.2.val - 1, by
      rcases hx with ⟨-, -, hy₁, hy₂⟩
      omega⟩)

/-- Extend a pinned height by zero to the outer layer. -/
def extendHeight (L : ℕ) (n : Site L → ℤ) : Lattice2D.SquareFreeVertex (L + 2) → ℤ :=
  by
    classical
    exact fun x => if hx : isInnerVertex L x then n (innerSiteOfVertex x hx) else 0

@[simp] theorem isInnerVertex_innerSite {L : ℕ} (x : Site L) :
isInnerVertex L (innerSite x) := by
  simp [isInnerVertex, innerSite]

@[simp] theorem innerSiteOfVertex_innerSite {L : ℕ} (x : Site L) :
    innerSiteOfVertex (innerSite x) (isInnerVertex_innerSite x) = x := by
  apply Prod.ext <;> apply Fin.ext <;> simp [innerSiteOfVertex, innerSite]

@[simp] theorem extendHeight_innerSite {L : ℕ} (n : Site L → ℤ) (x : Site L) :
    extendHeight L n (innerSite x) = n x := by
  simp [extendHeight]

theorem extendHeight_zero_of_not_inner {L : ℕ} (n : Site L → ℤ)
    (x : Lattice2D.SquareFreeVertex (L + 2)) (hx : ¬ isInnerVertex L x) :
    extendHeight L n x = 0 := by
  simp [extendHeight, hx]

/-- Restrict an expanded height field to its inner sites. -/
def restrictHeight {L : ℕ} (f : Lattice2D.SquareFreeVertex (L + 2) → ℤ) : Site L → ℤ :=
  fun p => f (innerSite p)

/-- A field vanishes on the one-site outer layer. -/
def zeroOnOuterLayer {L : ℕ} (f : Lattice2D.SquareFreeVertex (L + 2) → ℤ) : Prop :=
  ∀ x, ¬ isInnerVertex L x → f x = 0

theorem innerSite_innerSiteOfVertex {L : ℕ} (x : Lattice2D.SquareFreeVertex (L + 2))
    (hx : isInnerVertex L x) : innerSite (innerSiteOfVertex x hx) = x := by
  rcases hx with ⟨hx₁, hx₂, hy₁, hy₂⟩
  apply Prod.ext
  · apply Fin.ext
    simp [innerSite, innerSiteOfVertex]
    omega
  · apply Fin.ext
    simp [innerSite, innerSiteOfVertex]
    omega

theorem extendHeight_restrictHeight {L : ℕ}
    (f : Lattice2D.SquareFreeVertex (L + 2) → ℤ) (hf : zeroOnOuterLayer f) :
    extendHeight L (restrictHeight f) = f := by
  funext x
  by_cases hx : isInnerVertex L x
  · simp [extendHeight, restrictHeight, hx]
    exact congrArg f (innerSite_innerSiteOfVertex x hx)
  · simp [extendHeight, hx, hf x hx]

theorem restrictHeight_extendHeight {L : ℕ} (n : Site L → ℤ) :
    restrictHeight (extendHeight L n) = n := by
  funext p
  simp [restrictHeight]

theorem extendHeight_unique_of_zeroOnOuter {L : ℕ}
    (f : Lattice2D.SquareFreeVertex (L + 2) → ℤ) (_hf : zeroOnOuterLayer f)
    (n : Site L → ℤ) (hn : extendHeight L n = f) : n = restrictHeight f := by
  funext p
  have h := congrFun hn (innerSite p)
  simpa [restrictHeight] using h

theorem extendHeight_existsUnique_of_zeroOnOuter {L : ℕ}
    (f : Lattice2D.SquareFreeVertex (L + 2) → ℤ) (hf : zeroOnOuterLayer f) :
    ∃! n : Site L → ℤ, extendHeight L n = f := by
  refine ⟨restrictHeight f, extendHeight_restrictHeight f hf, ?_⟩
  intro n hn
  exact extendHeight_unique_of_zeroOnOuter f hf n hn

/-- The four local directions, ordered left, right, bottom, top. -/
def missingFaceDirection {L : ℕ} (p : Site L) (d : Fin 4) : Prop :=
  match d.val with
  | 0 => p.1.val = 0
  | 1 => p.1.val + 1 = L
  | 2 => p.2.val = 0
  | _ => p.2.val + 1 = L

theorem wiredBoxIncidentEdge_boundary_iff_missing (L : ℕ) (p : Site L) (d : Fin 4) :
    ((wiredBoxGraph L).src (wiredBoxIncidentEdge L p d) = none ∨
      (wiredBoxGraph L).tgt (wiredBoxIncidentEdge L p d) = none) ↔
      missingFaceDirection p d := by
  fin_cases d <;>
    simp [missingFaceDirection, wiredBoxIncidentEdge, wiredBoxFinCastSucc,
      wiredBoxFinSuccCast, wiredBoxSrc_verticalDualEdge, wiredBoxTgt_verticalDualEdge,
      wiredBoxSrc_horizontalDualEdge, wiredBoxTgt_horizontalDualEdge] <;> omega

private theorem wiredBoxIncidentEdge_inner_card (L : ℕ) (p : Site L) :
    Fintype.card {d : Fin 4 // ¬ missingFaceDirection p d} = squareZeroFreeDegree L p := by
  classical
  let e : Fin 4 ≃ WiredIncidentEdge L p := wiredBoxIncidentEdgeEquiv L p
  have hcard : Fintype.card (WiredInteriorIncidentEdge L p) = squareZeroFreeDegree L p :=
    wiredInteriorIncidentEdge_card L p
  -- The local direction equivalence restricts to the interior incidences.
  let f : {d : Fin 4 // ¬ missingFaceDirection p d} ≃ WiredInteriorIncidentEdge L p := by
    classical
    refine
      { toFun := fun d =>
          ⟨⟨wiredBoxIncidentEdge L p d.1,
            (not_or.mp (by
              intro h
              exact d.2 ((wiredBoxIncidentEdge_boundary_iff_missing L p d.1).mp h)))⟩,
            wiredBoxIncidentEdge_incident L p d.1⟩
        invFun := fun z =>
          ⟨e.symm ⟨z.1.1, z.2⟩, by
            intro hm
            have hb := (wiredBoxIncidentEdge_boundary_iff_missing L p
              (e.symm ⟨z.1.1, z.2⟩)).mpr hm
            have heq : wiredBoxIncidentEdge L p (e.symm ⟨z.1.1, z.2⟩) = z.1.1 :=
              congrArg Subtype.val (e.apply_symm_apply ⟨z.1.1, z.2⟩)
            rw [heq] at hb
            rcases hb with hs | ht
            · exact z.1.2.1 hs
            · exact z.1.2.2 ht⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro d
      apply Subtype.ext
      exact e.left_inv d.1
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      change wiredBoxIncidentEdge L p (e.symm ⟨z.1.1, z.2⟩) = z.1.1
      exact congrArg Subtype.val (e.right_inv ⟨z.1.1, z.2⟩)
  calc
    Fintype.card {d : Fin 4 // ¬ missingFaceDirection p d} =
        Fintype.card (WiredInteriorIncidentEdge L p) := Fintype.card_congr f
    _ = squareZeroFreeDegree L p := hcard

theorem missingFaceDirection_card (L : ℕ) (p : Site L) :
    Fintype.card {d : Fin 4 // missingFaceDirection p d} = 4 - squareZeroFreeDegree L p := by
  classical
  have htotal : Fintype.card (Fin 4) = 4 := by simp
  rw [← wiredBoxIncidentEdge_inner_card L p]
  have h := Fintype.card_subtype_compl
    (p := fun d : Fin 4 => ¬ missingFaceDirection p d)
  simpa [htotal, Nat.sub_sub_self] using h

noncomputable def missingFaceDirectionEquiv (L : ℕ) (p : Site L) :
    Fin (4 - squareZeroFreeDegree L p) ≃ {d : Fin 4 // missingFaceDirection p d} :=
  (Fintype.equivFinOfCardEq (missingFaceDirection_card L p)).symm

/-- Choose the missing face direction represented by a wired boundary multiplicity. -/
def boundaryDirection {L : ℕ} (b : SquareZeroBoundaryIndex L) : Fin 4 :=
  (missingFaceDirectionEquiv L b.1 b.2).1

@[simp] theorem boundaryDirection_missing {L : ℕ} (b : SquareZeroBoundaryIndex L) :
    missingFaceDirection b.1 (boundaryDirection b) :=
  (missingFaceDirectionEquiv L b.1 b.2).2

/-- Shift an internal free-square bond one step into the larger free square. -/
def innerCoord {L : ℕ} (i : Fin L) : Fin (L + 2) :=
  ⟨i.val + 1, by have hi := i.isLt; omega⟩

def boundaryCoord {L : ℕ} (i : Fin L) : Fin (L + 2) :=
  ⟨i.val, by have hi := i.isLt; omega⟩

def outerCoord {L : ℕ} (i : Fin L) : Fin (L + 2) :=
  ⟨i.val + 2, by have hi := i.isLt; omega⟩

def innerEdge {L : ℕ} : Lattice2D.SquareFreeEdge L → Lattice2D.SquareFreeEdge (L + 2)
  | .inl e => .inl
      (⟨innerCoord e.1.1, by
        have h := e.1.2
        have hi := e.1.1.isLt
        simp only [innerCoord]
        omega⟩, innerCoord e.2)
  | .inr e => .inr
      (innerCoord e.1, ⟨innerCoord e.2.1, by
        have h := e.2.2
        have hi := e.2.1.isLt
        simp only [innerCoord]
        omega⟩)

theorem innerEdge_injective {L : ℕ} :
    Function.Injective (@innerEdge L) := by
  intro e f h
  cases e <;> cases f <;>
    simp_all [innerEdge, innerCoord, Fin.ext_iff, Prod.ext_iff, Subtype.ext_iff]

/-- The expanded free-square edge leaving an inner site in a specified coordinate direction. -/
def faceBoundaryEdge {L : ℕ} (p : Site L) (d : Fin 4) : Lattice2D.SquareFreeEdge (L + 2) :=
  match d.val with
  | 0 => .inl (⟨⟨boundaryCoord p.1, by
        have hp := p.1.isLt
        simp only [boundaryCoord]
        omega⟩, by
      have hp := p.1.isLt
      simp only [boundaryCoord]
      omega⟩, innerCoord p.2)
  | 1 => .inl (⟨⟨innerCoord p.1, by
        have hp := p.1.isLt
        simp only [innerCoord]
        omega⟩, by
      have hp := p.1.isLt
      simp only [innerCoord]
      omega⟩, innerCoord p.2)
  | 2 => .inr (innerCoord p.1, ⟨⟨boundaryCoord p.2, by
        have hp := p.2.isLt
        simp only [boundaryCoord]
        omega⟩, by
      have hp := p.2.isLt
      simp only [boundaryCoord]
      omega⟩)
  | _ => .inr (innerCoord p.1, ⟨⟨innerCoord p.2, by
        have hp := p.2.isLt
        simp only [innerCoord]
        omega⟩, by
      have hp := p.2.isLt
      simp only [innerCoord]
      omega⟩)

/-- The outer endpoint opposite a missing face of `p`. -/
def outerFaceVertex {L : ℕ} (p : Site L) (d : Fin 4) : Lattice2D.SquareFreeVertex (L + 2) :=
  match d.val with
  | 0 => (boundaryCoord p.1, innerCoord p.2)
  | 1 => (outerCoord p.1, innerCoord p.2)
  | 2 => (innerCoord p.1, boundaryCoord p.2)
  | _ => (innerCoord p.1, outerCoord p.2)

theorem outerFaceVertex_not_inner {L : ℕ} (p : Site L) (d : Fin 4)
    (hd : missingFaceDirection p d) : ¬ isInnerVertex L (outerFaceVertex p d) := by
  fin_cases d <;> simp_all [missingFaceDirection, outerFaceVertex, isInnerVertex,
    innerCoord, boundaryCoord, outerCoord] <;> omega

theorem faceBoundaryEdge_endpoints {L : ℕ} (p : Site L) (d : Fin 4)
    (hd : missingFaceDirection p d) :
    ((squareFreeGraph (L + 2)).src (faceBoundaryEdge p d) = innerSite p ∧
        (squareFreeGraph (L + 2)).tgt (faceBoundaryEdge p d) = outerFaceVertex p d) ∨
      ((squareFreeGraph (L + 2)).tgt (faceBoundaryEdge p d) = innerSite p ∧
        (squareFreeGraph (L + 2)).src (faceBoundaryEdge p d) = outerFaceVertex p d) := by
  fin_cases d <;> simp_all [faceBoundaryEdge, outerFaceVertex, innerSite,
    missingFaceDirection, squareFreeGraph, innerCoord, boundaryCoord, outerCoord]

theorem innerEdge_endpoints_inner {L : ℕ} (e : Lattice2D.SquareFreeEdge L) :
    isInnerVertex L ((squareFreeGraph (L + 2)).src (innerEdge e)) ∧
      isInnerVertex L ((squareFreeGraph (L + 2)).tgt (innerEdge e)) := by
  cases e with
  | inl e =>
      have hi := e.1.1.isLt
      have hstep := e.1.2
      have hj := e.2.isLt
      simp [isInnerVertex, innerEdge, squareFreeGraph, innerCoord]
      omega
  | inr e =>
      have hi := e.1.isLt
      have hj := e.2.1.isLt
      have hstep := e.2.2
      simp [isInnerVertex, innerEdge, squareFreeGraph, innerCoord]
      omega

theorem faceBoundaryEdge_innerEndpoint {L : ℕ} (p : Site L) (d : Fin 4)
    (hd : missingFaceDirection p d) :
    isInnerVertex L ((squareFreeGraph (L + 2)).src (faceBoundaryEdge p d)) ∨
      isInnerVertex L ((squareFreeGraph (L + 2)).tgt (faceBoundaryEdge p d)) := by
  rcases faceBoundaryEdge_endpoints p d hd with ⟨hs, _⟩ | ⟨ht, _⟩
  · rw [hs]
    exact Or.inl (isInnerVertex_innerSite p)
  · rw [ht]
    exact Or.inr (isInnerVertex_innerSite p)

theorem faceBoundaryEdge_injective {L : ℕ} {p q : Site L} {d e : Fin 4}
    (hd : missingFaceDirection p d) (he : missingFaceDirection q e)
    (h : faceBoundaryEdge p d = faceBoundaryEdge q e) : p = q ∧ d = e := by
  fin_cases d <;> fin_cases e <;>
    simp_all [faceBoundaryEdge, missingFaceDirection, innerCoord, boundaryCoord,
      Fin.ext_iff, Prod.ext_iff] <;> omega

private theorem innerEdge_ne_faceBoundaryEdge {L : ℕ} (e : Lattice2D.SquareFreeEdge L)
    (p : Site L) (d : Fin 4) (hd : missingFaceDirection p d) :
    innerEdge e ≠ faceBoundaryEdge p d := by
  intro h
  rcases faceBoundaryEdge_endpoints p d hd with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · have hi := (innerEdge_endpoints_inner e).2
    rw [h, ht] at hi
    exact outerFaceVertex_not_inner p d hd hi
  · have hi := (innerEdge_endpoints_inner e).1
    rw [h, hs] at hi
    exact outerFaceVertex_not_inner p d hd hi


theorem faceBoundaryEdge_gradient_abs {L : ℕ} (n : Site L → ℤ) (p : Site L) (d : Fin 4)
    (hd : missingFaceDirection p d) :
    |(squareFreeGraph (L + 2)).grad (extendHeight L n) (faceBoundaryEdge p d)| =
      |pinnedGrad L (fun x => (n x : ℝ)) (Sum.inr ⟨p, (missingFaceDirectionEquiv L p).symm ⟨d, hd⟩⟩)| := by
  let b : SquareZeroBoundaryIndex L :=
    ⟨p, (missingFaceDirectionEquiv L p).symm ⟨d, hd⟩⟩
  have hout : extendHeight L n (outerFaceVertex p d) = 0 :=
    extendHeight_zero_of_not_inner n (outerFaceVertex p d) (outerFaceVertex_not_inner p d hd)
  have hright : pinnedGrad L (fun x => (n x : ℝ)) (Sum.inr b) = (n p : ℝ) := by
    simp [pinnedGrad, pinnedField, Multigraph.grad, squareZero, b]
  rcases faceBoundaryEdge_endpoints p d hd with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · simp [Multigraph.grad, hs, ht, extendHeight_innerSite, hout, hright, b]
  · simp [Multigraph.grad, hs, ht, extendHeight_innerSite, hout, hright, b, abs_neg]

theorem outerOuterGradient_zero {L : ℕ} (n : Site L → ℤ)
    (e : Lattice2D.SquareFreeEdge (L + 2))
    (hs : ¬ isInnerVertex L ((squareFreeGraph (L + 2)).src e))
    (ht : ¬ isInnerVertex L ((squareFreeGraph (L + 2)).tgt e)) :
    (squareFreeGraph (L + 2)).grad (extendHeight L n) e = 0 := by
  rw [Multigraph.grad,
    extendHeight_zero_of_not_inner n _ hs,
    extendHeight_zero_of_not_inner n _ ht]
  simp

theorem innerEdge_endpoints {L : ℕ} (e : Lattice2D.SquareFreeEdge L) :
    (squareFreeGraph (L + 2)).src (innerEdge e) = innerSite ((squareFreeGraph L).src e) ∧
      (squareFreeGraph (L + 2)).tgt (innerEdge e) = innerSite ((squareFreeGraph L).tgt e) := by
  cases e with
  | inl e => simp [innerEdge, innerSite, innerCoord, squareFreeGraph]
  | inr e => simp [innerEdge, innerSite, innerCoord, squareFreeGraph]

theorem innerEdge_gradient_abs {L : ℕ} (n : Site L → ℤ) (e : FroehlichSpencer.BKT.SquareFreeEdge L) :
    |(squareFreeGraph (L + 2)).grad (extendHeight L n)
        (innerEdge ((FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism L).edges e))| =
      |pinnedGrad L (fun x => (n x : ℝ)) (Sum.inl e)| := by
  let I := FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism L
  rcases I.endpoints e with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · have hs' : (squareFreeGraph L).src (I.edges e) = (FroehlichSpencer.BKT.squareFree L).src e := by
      simpa [I, FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism,
        FroehlichSpencer.BKT.squareFreeGraphIsomorphism] using hs
    have ht' : (squareFreeGraph L).tgt (I.edges e) = (FroehlichSpencer.BKT.squareFree L).tgt e := by
      simpa [I, FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism,
        FroehlichSpencer.BKT.squareFreeGraphIsomorphism] using ht
    have hi := innerEdge_endpoints (I.edges e)
    rw [Multigraph.grad, hi.1, hi.2, extendHeight_innerSite, extendHeight_innerSite,
      hs', ht']
    simp [pinnedGrad, pinnedField, Multigraph.grad, squareZero]
  · have hs' : (squareFreeGraph L).tgt (I.edges e) = (FroehlichSpencer.BKT.squareFree L).src e := by
      simpa [I, FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism,
        FroehlichSpencer.BKT.squareFreeGraphIsomorphism] using hs
    have ht' : (squareFreeGraph L).src (I.edges e) = (FroehlichSpencer.BKT.squareFree L).tgt e := by
      simpa [I, FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism,
        FroehlichSpencer.BKT.squareFreeGraphIsomorphism] using ht
    have hi := innerEdge_endpoints (I.edges e)
    rw [Multigraph.grad, hi.1, hi.2, extendHeight_innerSite, extendHeight_innerSite,
      hs', ht']
    simp [pinnedGrad, pinnedField, Multigraph.grad, squareZero, abs_sub_comm]

/-- A free-square bond touching the inner SOS box. -/
abbrev ExpandedInnerEdge (L : ℕ) :=
  {e : Lattice2D.SquareFreeEdge (L + 2) //
    isInnerVertex L ((squareFreeGraph (L + 2)).src e) ∨
      isInnerVertex L ((squareFreeGraph (L + 2)).tgt e)}

/-- Map each pinned SOS bond to the unique expanded free edge it represents. -/
def squareZeroBondToExpandedInnerEdge {L : ℕ} (b : SquareZeroBond L) : ExpandedInnerEdge L := by
  cases b with
  | inl e =>
      exact ⟨innerEdge ((FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism L).edges e),
        Or.inl (innerEdge_endpoints_inner _).1⟩
  | inr b =>
      exact ⟨faceBoundaryEdge b.1 (boundaryDirection b),
        faceBoundaryEdge_innerEndpoint b.1 (boundaryDirection b) (boundaryDirection_missing b)⟩

/-- The facewise construction sends distinct wired bonds to distinct expanded edges. -/
theorem squareZeroBondToExpandedInnerEdge_injective {L : ℕ} :
    Function.Injective (@squareZeroBondToExpandedInnerEdge L) := by
  intro b c h
  cases b with
  | inl e =>
    cases c with
    | inl f =>
      apply congrArg Sum.inl
      apply (FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism L).edges.injective
      apply innerEdge_injective
      exact congrArg Subtype.val h
    | inr c =>
      exfalso
      apply innerEdge_ne_faceBoundaryEdge
        ((FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism L).edges e)
        c.1 (boundaryDirection c) (boundaryDirection_missing c)
      exact congrArg Subtype.val h
  | inr b =>
    cases c with
    | inl e =>
      exfalso
      apply innerEdge_ne_faceBoundaryEdge
        ((FroehlichSpencer.BKT.squareFreeSourceGraphIsomorphism L).edges e)
        b.1 (boundaryDirection b) (boundaryDirection_missing b)
      exact (congrArg Subtype.val h).symm
    | inr c =>
      rcases b with ⟨p, ib⟩
      rcases c with ⟨q, ic⟩
      have hedge := congrArg Subtype.val h
      obtain ⟨hp, hd⟩ := faceBoundaryEdge_injective
        (boundaryDirection_missing (⟨p, ib⟩ : SquareZeroBoundaryIndex L))
        (boundaryDirection_missing (⟨q, ic⟩ : SquareZeroBoundaryIndex L)) hedge
      cases hp
      change ((missingFaceDirectionEquiv L p) ib).1 =
        ((missingFaceDirectionEquiv L p) ic).1 at hd
      have hidx := (missingFaceDirectionEquiv L p).injective (Subtype.ext hd)
      apply congrArg Sum.inr
      exact congrArg (fun i => (⟨p, i⟩ : SquareZeroBoundaryIndex L)) hidx

/-- Every pinned bond gradient is the same as the expanded free-edge gradient, up to the
orientation convention already removed by absolute values. -/
theorem squareZeroBond_gradient_abs {L : ℕ} (n : Site L → ℤ) (b : SquareZeroBond L) :
    |(squareFreeGraph (L + 2)).grad (extendHeight L n)
        (squareZeroBondToExpandedInnerEdge b).1| =
      |pinnedGrad L (fun x => (n x : ℝ)) b| := by
  cases b with
  | inl e =>
      simpa [squareZeroBondToExpandedInnerEdge] using innerEdge_gradient_abs n e
  | inr b =>
      let E := missingFaceDirectionEquiv L b.1
      have hsub : (⟨boundaryDirection b, boundaryDirection_missing b⟩ :
          {d : Fin 4 // missingFaceDirection b.1 d}) = E b.2 := by
        apply Subtype.ext
        rfl
      have hidx : E.symm ⟨boundaryDirection b, boundaryDirection_missing b⟩ = b.2 := by
        have h := congrArg E.symm hsub
        have h' : E.symm (E b.2) = b.2 := E.symm_apply_apply _
        exact h.trans h'
      have h := faceBoundaryEdge_gradient_abs n b.1 (boundaryDirection b)
        (boundaryDirection_missing b)
      rw [hidx] at h
      simpa [squareZeroBondToExpandedInnerEdge] using h

/-- The SOS weight is the product of the expanded gradients over precisely the mapped bonds. -/
theorem sosHeightWeight_eq_prod_mappedEdges {L : ℕ} (β : ℝ) (n : Site L → ℤ) :
    sosHeightWeight L β n =
      ∏ b : SquareZeroBond L,
        Real.exp (-(β * |(squareFreeGraph (L + 2)).grad (extendHeight L n)
          (squareZeroBondToExpandedInnerEdge b).1|)) := by
  unfold sosHeightWeight
  apply Finset.prod_congr rfl
  intro b hb
  rw [squareZeroBond_gradient_abs]


end FroehlichSpencer.BKT.SOS.Peierls

end
