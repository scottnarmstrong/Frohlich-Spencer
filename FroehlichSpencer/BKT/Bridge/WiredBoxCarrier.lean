/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.WiredBoxSymmetry
public import FroehlichSpencer.BKT.Villain.GraphIsomorphism
public import FroehlichSpencer.BKT.Villain.RootObservable

/-!
# The and internal wired-square carriers

The dual-square edges incident to a primal square vertex are its four coordinate-side
incidences.

This is the local count used to match the wired boundary fibers (KP p. 2, §6.1).
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Duality

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D

/-- Include a coordinate in the side-`L+1` dual square. -/
def wiredBoxFinCastSucc {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  ⟨i.val, by omega⟩

/-- The coordinate immediately to the right or above a free coordinate. -/
def wiredBoxFinSuccCast {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The four dual edges around a free primal vertex, ordered left, right, bottom, top. -/
def wiredBoxIncidentEdge (L : ℕ) (p : SquareFreeVertex L) : Fin 4 → WiredEdge L :=
  fun d => match d.val with
    | 0 => verticalDualEdge (wiredBoxFinCastSucc p.1) p.2
    | 1 => verticalDualEdge (wiredBoxFinSuccCast p.1) p.2
    | 2 => horizontalDualEdge p.1 (wiredBoxFinCastSucc p.2)
    | _ => horizontalDualEdge p.1 (wiredBoxFinSuccCast p.2)

/-- Each of the four coordinate-side dual edges is incident to its free primal vertex. -/
theorem wiredBoxIncidentEdge_incident (L : ℕ) (p : SquareFreeVertex L)
    (d : Fin 4) :
    (wiredBoxGraph L).src (wiredBoxIncidentEdge L p d) = some p ∨
      (wiredBoxGraph L).tgt (wiredBoxIncidentEdge L p d) = some p := by
  fin_cases d <;>
    simp [wiredBoxIncidentEdge, wiredBoxFinCastSucc, wiredBoxFinSuccCast,
      wiredBoxSrc_verticalDualEdge, wiredBoxTgt_verticalDualEdge,
      wiredBoxSrc_horizontalDualEdge, wiredBoxTgt_horizontalDualEdge]

/-- The four coordinate-side edges around a free wired-square vertex are distinct. -/
theorem wiredBoxIncidentEdge_injective (L : ℕ) (p : SquareFreeVertex L) :
    Function.Injective (wiredBoxIncidentEdge L p) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [wiredBoxIncidentEdge, wiredBoxFinCastSucc, wiredBoxFinSuccCast,
      verticalDualEdge, horizontalDualEdge, verticalDualEdgeData,
      horizontalDualEdgeData, Fin.ext_iff] at hab ⊢

/-- Internal wired edges incident to a fixed free vertex. -/
abbrev WiredIncidentEdge (L : ℕ) (p : SquareFreeVertex L) :=
  {e : WiredEdge L //
    (wiredBoxGraph L).src e = some p ∨ (wiredBoxGraph L).tgt e = some p}

/-- Every internal wired edge incident to a free vertex is one of its four coordinate-side
edges. -/
theorem wiredBoxIncidentEdge_surjective (L : ℕ) (p : SquareFreeVertex L) :
    Function.Surjective (fun d : Fin 4 =>
      (⟨wiredBoxIncidentEdge L p d, wiredBoxIncidentEdge_incident L p d⟩ :
        WiredIncidentEdge L p)) := by
  intro e
  rcases e with ⟨e, he⟩
  cases e with
  | inl e =>
      rcases he with hs | ht
      · have hj : e.2.val < L := by
          by_contra hj
          simp [wiredBoxGraph, wiredBoxSrc, horizontalPrimalSrc, hj] at hs
        have hp : (horizontalFaceX e, ⟨e.2.val, hj⟩) = p := by
          simpa [wiredBoxGraph, wiredBoxSrc, horizontalPrimalSrc, horizontalFaceX, hj] using hs
        refine ⟨⟨2, by omega⟩, ?_⟩
        apply Subtype.ext
        simp only [wiredBoxIncidentEdge, horizontalDualEdge]
        apply congrArg Sum.inl
        rw [← horizontalDualEdgeData_face e]
        have hxv : p.1.val = e.1.1.val := by
          have hv := congrArg (fun q : Fin L × Fin L => q.1.val) hp
          simpa [horizontalFaceX] using hv.symm
        have hyv : e.2.val = p.2.val := by
          have hv := congrArg (fun q : Fin L × Fin L => q.2.val) hp
          simpa using hv
        apply Prod.ext
        · apply Subtype.ext
          apply Fin.ext
          simp [horizontalDualEdgeData, horizontalFaceX, wiredBoxFinCastSucc, hxv]
        · apply Fin.ext
          simp [horizontalDualEdgeData, wiredBoxFinCastSucc, hyv]
      · have hj0 : e.2.val ≠ 0 := by
          intro hzero
          simp [wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt, hzero] at ht
        have hp : (horizontalFaceX e,
            ⟨e.2.val - 1, by have h := e.2.isLt; omega⟩) = p := by
          simpa [wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt, horizontalFaceX,
            hj0] using ht
        refine ⟨⟨3, by omega⟩, ?_⟩
        apply Subtype.ext
        simp only [wiredBoxIncidentEdge, horizontalDualEdge]
        apply congrArg Sum.inl
        rw [← horizontalDualEdgeData_face e]
        have hxv : p.1.val = e.1.1.val := by
          have hv := congrArg (fun q : Fin L × Fin L => q.1.val) hp
          simpa [horizontalFaceX] using hv.symm
        have hyv : e.2.val = p.2.val + 1 := by
          have hv : e.2.val - 1 = p.2.val := by
            simpa using congrArg (fun q : Fin L × Fin L => q.2.val) hp
          omega
        apply Prod.ext
        · apply Subtype.ext
          apply Fin.ext
          simp [horizontalDualEdgeData, horizontalFaceX, wiredBoxFinSuccCast, hxv]
        · apply Fin.ext
          simp [horizontalDualEdgeData, wiredBoxFinSuccCast, hyv]
  | inr e =>
      rcases he with hs | ht
      · have hi0 : e.1.val ≠ 0 := by
          intro hzero
          simp [wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, hzero] at hs
        have hp : (⟨e.1.val - 1, by have h := e.1.isLt; omega⟩, verticalFaceY e) = p := by
          simpa [wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, verticalFaceY,
            hi0] using hs
        refine ⟨⟨1, by omega⟩, ?_⟩
        apply Subtype.ext
        simp only [wiredBoxIncidentEdge, verticalDualEdge]
        apply congrArg Sum.inr
        rw [← verticalDualEdgeData_face e]
        have hxv : e.1.val = p.1.val + 1 := by
          have hv : e.1.val - 1 = p.1.val := by
            simpa using congrArg (fun q : Fin L × Fin L => q.1.val) hp
          omega
        have hyv : p.2.val = e.2.1.val := by
          have hv := congrArg (fun q : Fin L × Fin L => q.2.val) hp
          simpa [verticalFaceY] using hv.symm
        apply Prod.ext
        · apply Fin.ext
          simp [verticalDualEdgeData, wiredBoxFinSuccCast, hxv]
        · apply Subtype.ext
          apply Fin.ext
          simp [verticalDualEdgeData, verticalFaceY, hyv]
      · have hi : e.1.val < L := by
          by_contra hi
          simp [wiredBoxGraph, wiredBoxTgt, verticalPrimalTgt, hi] at ht
        have hp : (⟨e.1.val, hi⟩, verticalFaceY e) = p := by
          simpa [wiredBoxGraph, wiredBoxTgt, verticalPrimalTgt, verticalFaceY, hi] using ht
        refine ⟨⟨0, by omega⟩, ?_⟩
        apply Subtype.ext
        simp only [wiredBoxIncidentEdge, verticalDualEdge]
        apply congrArg Sum.inr
        rw [← verticalDualEdgeData_face e]
        have hxv : p.1.val = e.1.val := by
          have hv := congrArg (fun q : Fin L × Fin L => q.1.val) hp
          simpa using hv.symm
        have hyv : p.2.val = e.2.1.val := by
          have hv := congrArg (fun q : Fin L × Fin L => q.2.val) hp
          simpa [verticalFaceY] using hv.symm
        apply Prod.ext
        · apply Fin.ext
          simp [verticalDualEdgeData, wiredBoxFinCastSucc, hxv]
        · apply Subtype.ext
          apply Fin.ext
          simp [verticalDualEdgeData, verticalFaceY, hyv]

/-- The four edges incident to a free internal wired vertex form its exact local incidence
fiber. -/
noncomputable def wiredBoxIncidentEdgeEquiv (L : ℕ) (p : SquareFreeVertex L) :
    Fin 4 ≃ WiredIncidentEdge L p :=
  Equiv.ofBijective (fun d : Fin 4 =>
    (⟨wiredBoxIncidentEdge L p d, wiredBoxIncidentEdge_incident L p d⟩ :
      WiredIncidentEdge L p))
    ⟨fun _ _ hab => wiredBoxIncidentEdge_injective L p (congrArg Subtype.val hab),
      wiredBoxIncidentEdge_surjective L p⟩

/-- Dual edges whose two primal endpoints are both free. -/
abbrev WiredInteriorEdge (L : ℕ) :=
  {e : WiredEdge L //
    (wiredBoxGraph L).src e ≠ none ∧ (wiredBoxGraph L).tgt e ≠ none}

/-- Cross an internal free-square edge by rotating it through a right angle into the dual square. -/
def crossInternalFreeEdge (L : ℕ) : Lattice2D.SquareFreeEdge L → WiredEdge L
  | .inl e => verticalDualEdge (wiredBoxFinSuccCast e.1.1) e.2
  | .inr e => horizontalDualEdge e.1 (wiredBoxFinSuccCast e.2.1)

/-- A crossed free-square edge has both primal endpoints in the free square. -/
theorem crossInternalFreeEdge_interior (L : ℕ) (e : Lattice2D.SquareFreeEdge L) :
    (wiredBoxGraph L).src (crossInternalFreeEdge L e) ≠ none ∧
      (wiredBoxGraph L).tgt (crossInternalFreeEdge L e) ≠ none := by
  cases e with
  | inl e =>
      constructor
      · simp [crossInternalFreeEdge, wiredBoxFinSuccCast, wiredBoxGraph,
          wiredBoxSrc, verticalPrimalSrc, verticalFaceY, verticalDualEdge]
      · have hL : e.1.1.val + 1 < L := e.1.2
        simp [crossInternalFreeEdge, wiredBoxFinSuccCast, wiredBoxGraph,
          wiredBoxTgt, verticalPrimalTgt, verticalFaceY, verticalDualEdge, hL]
  | inr e =>
      constructor
      · have hL : e.2.1.val + 1 < L := e.2.2
        simp [crossInternalFreeEdge, wiredBoxFinSuccCast, wiredBoxGraph,
          wiredBoxSrc, horizontalPrimalSrc, horizontalFaceX, horizontalDualEdge, hL]
      · simp [crossInternalFreeEdge, wiredBoxFinSuccCast, wiredBoxGraph,
          wiredBoxTgt, horizontalPrimalTgt, horizontalFaceX, horizontalDualEdge]

/-- Read an interior dual edge as the unique internal free-square edge that it crosses. -/
def uncrossInternalFreeEdge (L : ℕ) (edge : WiredEdge L)
    (he : (wiredBoxGraph L).src edge ≠ none ∧
      (wiredBoxGraph L).tgt edge ≠ none) : Lattice2D.SquareFreeEdge L := by
  classical
  cases edge with
  | inl h =>
      have hrow : h.2.val < L := by
        by_contra hh
        have hs := he.1
        simp [wiredBoxGraph, wiredBoxSrc, horizontalPrimalSrc, hh] at hs
      have hrow0 : h.2.val ≠ 0 := by
        intro hh
        have ht := he.2
        simp [wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt, hh] at ht
      let j : Fin L := ⟨h.2.val - 1, by omega⟩
      have hj : j.val + 1 < L := by dsimp [j]; omega
      exact .inr (horizontalFaceX h, ⟨j, hj⟩)
  | inr h =>
      have hcol0 : h.1.val ≠ 0 := by
        intro hh
        have hs := he.1
        simp [wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, hh] at hs
      have hcol : h.1.val < L := by
        by_contra hh
        have ht := he.2
        simp [wiredBoxGraph, wiredBoxTgt, verticalPrimalTgt, hh] at ht
      let i : Fin L := ⟨h.1.val - 1, by omega⟩
      have hi : i.val + 1 < L := by dsimp [i]; omega
      exact .inl (⟨i, hi⟩, verticalFaceY h)

/-- Internal free-square edges correspond bijectively to dual edges with two free endpoints. -/
noncomputable def crossInternalFreeEdgeEquiv (L : ℕ) :
    Lattice2D.SquareFreeEdge L ≃ WiredInteriorEdge L where
  toFun e := ⟨crossInternalFreeEdge L e, crossInternalFreeEdge_interior L e⟩
  invFun e := uncrossInternalFreeEdge L e.1 e.2
  left_inv e := by
    cases e with
    | inl e =>
        simp [uncrossInternalFreeEdge, crossInternalFreeEdge, wiredBoxFinSuccCast,
          verticalDualEdge, horizontalDualEdge, verticalDualEdgeData,
          horizontalDualEdgeData, verticalFaceY, horizontalFaceX]
    | inr e =>
        simp [uncrossInternalFreeEdge, crossInternalFreeEdge, wiredBoxFinSuccCast,
          verticalDualEdge, horizontalDualEdge, verticalDualEdgeData,
          horizontalDualEdgeData, verticalFaceY, horizontalFaceX]
  right_inv e := by
    rcases e with ⟨e, he⟩
    cases e with
    | inl e =>
        apply Subtype.ext
        have hrow0 : e.2.val ≠ 0 := by
          intro hzero
          have ht := he.2
          simp [wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt, hzero] at ht
        change horizontalDualEdge (horizontalFaceX e)
          ⟨e.2.val - 1 + 1, by have h := e.2.isLt; omega⟩ = Sum.inl e
        simp only [horizontalDualEdge]
        apply congrArg Sum.inl
        have hrow :
            (⟨e.2.val - 1 + 1, by have h := e.2.isLt; omega⟩ : Fin (L + 1)) = e.2 := by
          apply Fin.ext
          change e.2.val - 1 + 1 = e.2.val
          omega
        rw [hrow]
        exact horizontalDualEdgeData_face e
    | inr e =>
        apply Subtype.ext
        have hcol0 : e.1.val ≠ 0 := by
          intro hzero
          have hs := he.1
          simp [wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, hzero] at hs
        change verticalDualEdge ⟨e.1.val - 1 + 1,
          by have h := e.1.isLt; omega⟩ (verticalFaceY e) = Sum.inr e
        simp only [verticalDualEdge]
        apply congrArg Sum.inr
        have hcol :
            (⟨e.1.val - 1 + 1, by have h := e.1.isLt; omega⟩ : Fin (L + 1)) = e.1 := by
          apply Fin.ext
          change e.1.val - 1 + 1 = e.1.val
          omega
        rw [hcol]
        exact verticalDualEdgeData_face e

/--
free edges identify with the interior dual edges, via the reusable sorted-pair
classification and the free-square carrier isomorphism (KP pp. 2, 32).
-/
noncomputable def sourceFreeEdgeCrossingEquiv (L : ℕ) :
    SquareFreeEdge L ≃ WiredInteriorEdge L :=
  (squareFreeSourceGraphIsomorphism L).edges.trans (crossInternalFreeEdgeEquiv L)

/--
The internal crossing of the canonical positive-step representative is the reusable
free-edge crossing map.
-/
theorem crossInternalFreeEdge_squareFreeSourceGraphIsomorphism (L : ℕ)
    (e : SquareFreeEdge L) :
    crossInternalFreeEdge L ((squareFreeSourceGraphIsomorphism L).edges e) =
      wiredBoxCrossesFreeEdge L e := by
  rcases squareFreeEdge_classification e with hh | hv
  · have hstep : wiredBoxFinSuccCast e.1.1.1 = e.1.1.1.succ := by
      apply Fin.ext
      simp [wiredBoxFinSuccCast, Fin.val_succ]
    simp [squareFreeSourceGraphIsomorphism, squareFreeGraphIsomorphism,
      squareFreeEdgeEquiv, squareFreeEdgeToInternal, crossInternalFreeEdge,
      wiredBoxCrossesFreeEdge, hh.1, hstep]
  · have hrow : e.1.1.2 ≠ e.1.2.2 := by
      intro h
      have hvv := congrArg Fin.val h
      omega
    have hstep : wiredBoxFinSuccCast e.1.1.2 = e.1.1.2.succ := by
      apply Fin.ext
      simp [wiredBoxFinSuccCast, Fin.val_succ]
    simp [squareFreeSourceGraphIsomorphism, squareFreeGraphIsomorphism,
      squareFreeEdgeEquiv, squareFreeEdgeToInternal, crossInternalFreeEdge,
      wiredBoxCrossesFreeEdge, hv.1, hrow, hstep]

/--
The crossing map preserves the unordered pair of primal endpoints.
-/
theorem sourceFreeEdgeCrossing_endpoints (L : ℕ) (e : SquareFreeEdge L) :
    ((wiredBoxGraph L).src (sourceFreeEdgeCrossingEquiv L e).1 =
        some ((squareFree L).src e) ∧
      (wiredBoxGraph L).tgt (sourceFreeEdgeCrossingEquiv L e).1 =
        some ((squareFree L).tgt e)) ∨
    ((wiredBoxGraph L).src (sourceFreeEdgeCrossingEquiv L e).1 =
        some ((squareFree L).tgt e) ∧
      (wiredBoxGraph L).tgt (sourceFreeEdgeCrossingEquiv L e).1 =
        some ((squareFree L).src e)) := by
  change ((wiredBoxGraph L).src
      (crossInternalFreeEdge L ((squareFreeSourceGraphIsomorphism L).edges e)) =
        some ((squareFree L).src e) ∧
      (wiredBoxGraph L).tgt
      (crossInternalFreeEdge L ((squareFreeSourceGraphIsomorphism L).edges e)) =
        some ((squareFree L).tgt e)) ∨
    ((wiredBoxGraph L).src
      (crossInternalFreeEdge L ((squareFreeSourceGraphIsomorphism L).edges e)) =
        some ((squareFree L).tgt e) ∧
      (wiredBoxGraph L).tgt
      (crossInternalFreeEdge L ((squareFreeSourceGraphIsomorphism L).edges e)) =
        some ((squareFree L).src e))
  simp_rw [crossInternalFreeEdge_squareFreeSourceGraphIsomorphism]
  exact wiredBoxCrossesFreeEdge_endpoints L e

/-- Incidence at a free vertex is preserved and reflected by the free-edge crossing
equivalence. -/
theorem sourceFreeEdgeCrossing_incident_iff (L : ℕ) (e : SquareFreeEdge L)
    (p : SquareFreeVertex L) :
    ((squareFree L).src e = p ∨ (squareFree L).tgt e = p) ↔
      ((wiredBoxGraph L).src (sourceFreeEdgeCrossingEquiv L e).1 = some p ∨
        (wiredBoxGraph L).tgt (sourceFreeEdgeCrossingEquiv L e).1 = some p) := by
  rcases sourceFreeEdgeCrossing_endpoints L e with h | h
  · constructor
    · rintro (hs | ht)
      · exact Or.inl (h.1.trans (congrArg some hs))
      · exact Or.inr (h.2.trans (congrArg some ht))
    · rintro (hs | ht)
      · exact Or.inl (Option.some.inj (h.1.symm.trans hs))
      · exact Or.inr (Option.some.inj (h.2.symm.trans ht))
  · constructor
    · rintro (hs | ht)
      · exact Or.inr (h.2.trans (congrArg some hs))
      · exact Or.inl (h.1.trans (congrArg some ht))
    · rintro (hs | ht)
      · exact Or.inr (Option.some.inj (h.1.symm.trans hs))
      · exact Or.inl (Option.some.inj (h.2.symm.trans ht))

/--
free edges incident to a fixed vertex correspond exactly to interior dual edges
incident to that vertex.
-/
abbrev SourceFreeIncidentEdge (L : ℕ) (p : SquareFreeVertex L) :=
  {e : SquareFreeEdge L //
    (squareFree L).src e = p ∨ (squareFree L).tgt e = p}

/-- The interior wired incidence fiber at a fixed free vertex. -/
abbrev WiredInteriorIncidentEdge (L : ℕ) (p : SquareFreeVertex L) :=
  {e : WiredInteriorEdge L //
    (wiredBoxGraph L).src e.1 = some p ∨ (wiredBoxGraph L).tgt e.1 = some p}

/-- The free-edge crossing equivalence restricts to each endpoint incidence fiber. -/
noncomputable def sourceFreeIncidentEdgeEquiv (L : ℕ) (p : SquareFreeVertex L) :
    SourceFreeIncidentEdge L p ≃ WiredInteriorIncidentEdge L p where
  toFun e := ⟨sourceFreeEdgeCrossingEquiv L e.1,
    (sourceFreeEdgeCrossing_incident_iff L e.1 p).mp e.2⟩
  invFun e := ⟨(sourceFreeEdgeCrossingEquiv L).symm e.1,
    (sourceFreeEdgeCrossing_incident_iff L
      ((sourceFreeEdgeCrossingEquiv L).symm e.1) p).mpr (by
        simpa using e.2)⟩
  left_inv e := Subtype.ext ((sourceFreeEdgeCrossingEquiv L).left_inv e.1)
  right_inv e := Subtype.ext ((sourceFreeEdgeCrossingEquiv L).right_inv e.1)

/--
The degree of a vertex in the free square, using the inline definition in
`squareZero` (KP p. 2).
-/
def squareZeroFreeDegree (L : ℕ) (p : SquareFreeVertex L) : ℕ :=
  (Finset.univ.filter fun e : SquareFreeEdge L =>
    (squareFree L).src e = p ∨ (squareFree L).tgt e = p).card

/-- Interior incidences represented as a subfiber of all four internal incidences. -/
abbrev WiredInteriorIncidentWithin (L : ℕ) (p : SquareFreeVertex L) :=
  {e : WiredIncidentEdge L p //
    (wiredBoxGraph L).src e.1 ≠ none ∧ (wiredBoxGraph L).tgt e.1 ≠ none}

/-- The internal boundary incidence fiber at a free vertex, as the complement of its interior
incidences in the exact four-edge local fiber. -/
abbrev WiredBoundaryFiber (L : ℕ) (p : SquareFreeVertex L) :=
  {e : WiredIncidentEdge L p //
    ¬((wiredBoxGraph L).src e.1 ≠ none ∧ (wiredBoxGraph L).tgt e.1 ≠ none)}

/-- Internal wired edges with at least one wired endpoint. -/
abbrev WiredBoundaryEdge (L : ℕ) :=
  {e : WiredEdge L //
    ¬((wiredBoxGraph L).src e ≠ none ∧ (wiredBoxGraph L).tgt e ≠ none)}

/-- Reorder the two incidence predicates on an interior edge. -/
noncomputable def wiredInteriorIncidentEquiv (L : ℕ) (p : SquareFreeVertex L) :
    WiredInteriorIncidentEdge L p ≃ WiredInteriorIncidentWithin L p where
  toFun e := ⟨⟨e.1.1, e.2⟩, e.1.2⟩
  invFun e := ⟨⟨e.1.1, e.2⟩, e.1.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/--
The free degree is the cardinality of its free-edge incidence fiber.
-/
theorem sourceFreeIncidentEdge_card (L : ℕ) (p : SquareFreeVertex L) :
    Fintype.card (SourceFreeIncidentEdge L p) = squareZeroFreeDegree L p := by
  classical
  exact Fintype.card_subtype _

/--
The internal free-edge incidence fiber has the same cardinality as the degree.
-/
theorem wiredInteriorIncidentEdge_card (L : ℕ) (p : SquareFreeVertex L) :
    Fintype.card (WiredInteriorIncidentEdge L p) = squareZeroFreeDegree L p := by
  calc
    Fintype.card (WiredInteriorIncidentEdge L p) =
        Fintype.card (SourceFreeIncidentEdge L p) :=
      Fintype.card_congr (sourceFreeIncidentEdgeEquiv L p).symm
    _ = squareZeroFreeDegree L p := sourceFreeIncidentEdge_card L p

/--
At a free vertex, the internal boundary-edge fiber has exactly the multiplicity
`4 - degree`.
-/
theorem wiredBoundaryFiber_card (L : ℕ) (p : SquareFreeVertex L) :
    Fintype.card (WiredBoundaryFiber L p) = 4 - squareZeroFreeDegree L p := by
  classical
  have htotal : Fintype.card (WiredIncidentEdge L p) = 4 :=
    Fintype.card_congr (wiredBoxIncidentEdgeEquiv L p).symm
  have hinterior : Fintype.card (WiredInteriorIncidentWithin L p) =
      squareZeroFreeDegree L p := by
    calc
      Fintype.card (WiredInteriorIncidentWithin L p) =
          Fintype.card (WiredInteriorIncidentEdge L p) :=
        Fintype.card_congr (wiredInteriorIncidentEquiv L p).symm
      _ = squareZeroFreeDegree L p := wiredInteriorIncidentEdge_card L p
  rw [Fintype.card_subtype_compl
    (p := fun e : WiredIncidentEdge L p =>
      (wiredBoxGraph L).src e.1 ≠ none ∧ (wiredBoxGraph L).tgt e.1 ≠ none)]
  rw [htotal, hinterior]

/-- An internal wired edge outside the free-free interior has exactly one free endpoint.
The other endpoint is the wired vertex (KP p. 2). -/
theorem wiredBoundary_endpoints (L : ℕ) (e : WiredEdge L)
    (he : ¬((wiredBoxGraph L).src e ≠ none ∧ (wiredBoxGraph L).tgt e ≠ none)) :
    (∃ p, (wiredBoxGraph L).src e = some p ∧ (wiredBoxGraph L).tgt e = none) ∨
      (∃ p, (wiredBoxGraph L).src e = none ∧ (wiredBoxGraph L).tgt e = some p) := by
  classical
  cases hs : (wiredBoxGraph L).src e with
  | none =>
      cases ht : (wiredBoxGraph L).tgt e with
      | none => exact False.elim ((wiredBoxGraph L).src_ne_tgt e (by simp [hs, ht]))
      | some p => exact Or.inr ⟨p, rfl, rfl⟩
  | some p =>
      cases ht : (wiredBoxGraph L).tgt e with
      | none => exact Or.inl ⟨p, rfl, rfl⟩
      | some q => exact False.elim (he ⟨by simp [hs], by simp [ht]⟩)

/-- A boundary edge has at most one free endpoint value. -/
theorem wiredBoundary_incident_unique (L : ℕ) (e : WiredEdge L)
    (he : ¬((wiredBoxGraph L).src e ≠ none ∧ (wiredBoxGraph L).tgt e ≠ none))
    {p q : SquareFreeVertex L}
    (hp : (wiredBoxGraph L).src e = some p ∨ (wiredBoxGraph L).tgt e = some p)
    (hq : (wiredBoxGraph L).src e = some q ∨ (wiredBoxGraph L).tgt e = some q) : p = q := by
  rcases wiredBoundary_endpoints L e he with ⟨r, hs, ht⟩ | ⟨r, hs, ht⟩
  · have hp' : p = r := by
      rcases hp with hp | hp
      · exact Option.some.inj (hs.symm.trans hp).symm
      · simp [ht] at hp
    have hq' : q = r := by
      rcases hq with hq | hq
      · exact Option.some.inj (hs.symm.trans hq).symm
      · simp [ht] at hq
    exact hp'.trans hq'.symm
  · have hp' : p = r := by
      rcases hp with hp | hp
      · simp [hs] at hp
      · exact Option.some.inj (ht.symm.trans hp).symm
    have hq' : q = r := by
      rcases hq with hq | hq
      · simp [hs] at hq
      · exact Option.some.inj (ht.symm.trans hq).symm
    exact hp'.trans hq'.symm

/-- A boundary incidence identifies the unique free endpoint of an internal boundary edge. -/
theorem wiredBoundaryFiber_endpoints (L : ℕ) (p : SquareFreeVertex L)
    (e : WiredBoundaryFiber L p) :
    ((wiredBoxGraph L).src e.1.1 = some p ∧ (wiredBoxGraph L).tgt e.1.1 = none) ∨
      ((wiredBoxGraph L).src e.1.1 = none ∧ (wiredBoxGraph L).tgt e.1.1 = some p) := by
  rcases wiredBoundary_endpoints L e.1.1 e.2 with ⟨q, hs, ht⟩ | ⟨q, hs, ht⟩
  · rcases e.1.2 with hp | hp
    · have hqp : q = p := Option.some.inj (hs.symm.trans hp)
      subst q
      exact Or.inl ⟨hs, ht⟩
    · simp [ht] at hp
  · rcases e.1.2 with hp | hp
    · simp [hs] at hp
    · have hqp : q = p := Option.some.inj (ht.symm.trans hp)
      subst q
      exact Or.inr ⟨hs, ht⟩

/-- The forgetful map from the disjoint union of local fibers to the boundary edge carrier. -/
def wiredBoundarySigmaToEdge (L : ℕ) :
    (Σ p : SquareFreeVertex L, WiredBoundaryFiber L p) → WiredBoundaryEdge L :=
  fun e => ⟨e.2.1.1, e.2.2⟩

/-- The local boundary-fiber map is injective because a wired boundary edge has one free endpoint. -/
theorem wiredBoundarySigmaToEdge_injective (L : ℕ) :
    Function.Injective (wiredBoundarySigmaToEdge L) := by
  intro a b hab
  cases a with
  | mk p ae =>
    cases b with
    | mk q be =>
      have he : ae.1.1 = be.1.1 := congrArg Subtype.val hab
      have hbi : (wiredBoxGraph L).src ae.1.1 = some q ∨
          (wiredBoxGraph L).tgt ae.1.1 = some q := by
        simpa only [he] using be.1.2
      have hp := wiredBoundary_incident_unique L ae.1.1 ae.2
        (p := p) (q := q) ae.1.2 hbi
      apply Sigma.ext hp
      cases hp
      apply heq_of_eq
      apply Subtype.ext
      apply Subtype.ext
      exact he

/-- Every internal wired boundary edge appears in exactly one local boundary fiber. -/
theorem wiredBoundarySigmaToEdge_surjective (L : ℕ) :
    Function.Surjective (wiredBoundarySigmaToEdge L) := by
  intro e
  rcases wiredBoundary_endpoints L e.1 e.2 with ⟨p, hs, ht⟩ | ⟨p, hs, ht⟩
  · refine ⟨⟨p, ⟨⟨e.1, Or.inl hs⟩, e.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨⟨p, ⟨⟨e.1, Or.inr ht⟩, e.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- The local boundary-fiber map is bijective. -/
theorem wiredBoundarySigmaToEdge_bijective (L : ℕ) :
    Function.Bijective (wiredBoundarySigmaToEdge L) :=
  ⟨wiredBoundarySigmaToEdge_injective L, wiredBoundarySigmaToEdge_surjective L⟩

/-- Internal boundary incidence fibers enumerate every internal wired boundary edge exactly once. -/
noncomputable def wiredBoundarySigmaEquiv (L : ℕ) :
    (Σ p : SquareFreeVertex L, WiredBoundaryFiber L p) ≃ WiredBoundaryEdge L :=
  Equiv.ofBijective (wiredBoundarySigmaToEdge L) (wiredBoundarySigmaToEdge_bijective L)

@[simp] theorem wiredBoundarySigmaEquiv_val (L : ℕ)
    (e : Σ p : SquareFreeVertex L, WiredBoundaryFiber L p) :
    (wiredBoundarySigmaEquiv L e).1 = e.2.1.1 := by
  change (Equiv.ofBijective (wiredBoundarySigmaToEdge L)
    (wiredBoundarySigmaToEdge_bijective L) e).1 = e.2.1.1
  rw [Equiv.ofBijective_apply]
  rfl

/--
Each  boundary multiplicity `Fin (4 - deg p)` is matched with the internal wired
boundary incidences at `p`; the cardinality calculation is the degree equality.
-/
noncomputable def sourceBoundaryFiberEquiv (L : ℕ) (p : SquareFreeVertex L) :
    Fin (4 - squareZeroFreeDegree L p) ≃ WiredBoundaryFiber L p :=
  (Fintype.equivFinOfCardEq (wiredBoundaryFiber_card L p)).symm

/--
The total  boundary edge fiber is equivalent to the internal wired boundary edges.
-/
noncomputable def sourceBoundarySigmaEquiv (L : ℕ) :
    (Σ p : SquareFreeVertex L, Fin (4 - squareZeroFreeDegree L p)) ≃
      WiredBoundaryEdge L :=
  (Equiv.sigmaCongrRight fun p => sourceBoundaryFiberEquiv L p).trans
    (wiredBoundarySigmaEquiv L)

/--
The exact inline boundary index used in the `squareZero` declaration.
-/
abbrev SquareZeroBoundaryIndex (L : ℕ) :=
  Σ p : Fin L × Fin L, Fin (4 - (Finset.univ.filter fun e : SquareFreeEdge L =>
    (squareFree L).src e = p ∨ (squareFree L).tgt e = p).card)

/--
The inline  degree is definitionally the named degree used by the local fiber API.
-/
theorem squareZeroFreeDegree_eq_inline (L : ℕ) (p : SquareFreeVertex L) :
    squareZeroFreeDegree L p =
      (Finset.univ.filter fun e : SquareFreeEdge L =>
        (squareFree L).src e = p ∨ (squareFree L).tgt e = p).card := rfl

/--
Cast the `Fin (4 - deg p)` fiber to the local degree notation.

This is the explicit
per-vertex cast used in the carrier equivalence.
-/
noncomputable def squareZeroBoundaryIndexCast (L : ℕ) :
    SquareZeroBoundaryIndex L ≃
      (Σ p : SquareFreeVertex L, Fin (4 - squareZeroFreeDegree L p)) := by
  classical
  refine Equiv.sigmaCongrRight fun p => ?_
  let h := congrArg (fun n : ℕ => 4 - n) (squareZeroFreeDegree_eq_inline L p).symm
  refine {
    toFun := fun i => Fin.cast h i
    invFun := fun i => Fin.cast h.symm i
    left_inv := ?_
    right_inv := ?_
  }
  · intro i
    simp
  · intro i
    simp

/-- Split the internal wired edge carrier into its free-free and wired-boundary edges. -/
noncomputable def wiredBoxEdgePartitionEquiv (L : ℕ) :
    WiredInteriorEdge L ⊕ WiredBoundaryEdge L ≃ WiredEdge L := by
  classical
  exact Equiv.sumCompl (fun e : WiredEdge L =>
    (wiredBoxGraph L).src e ≠ none ∧ (wiredBoxGraph L).tgt e ≠ none)

/--
The wired-square edge carrier is bijective with the internal dual-edge carrier.

Free edges cross to interior dual edges; each boundary multiplicity is identified by its local
`Fin (4 - deg p)` incidence fiber (KP pp. 2, 32).
-/
noncomputable def squareZeroWiredBoxEdgeEquivNormalized (L : ℕ) :
    (SquareFreeEdge L ⊕ Σ p : SquareFreeVertex L,
      Fin (4 - squareZeroFreeDegree L p)) ≃ WiredEdge L :=
  (Equiv.sumCongr (sourceFreeEdgeCrossingEquiv L) (sourceBoundarySigmaEquiv L)).trans
    (wiredBoxEdgePartitionEquiv L)

noncomputable def squareZeroWiredBoxEdgeEquiv (L : ℕ) :
    SquareFreeEdge L ⊕ SquareZeroBoundaryIndex L ≃ WiredEdge L :=
  (Equiv.sumCongr (Equiv.refl _) (squareZeroBoundaryIndexCast L)).trans
    (squareZeroWiredBoxEdgeEquivNormalized L)

@[simp] theorem squareZeroWiredBoxEdgeEquiv_inr (L : ℕ)
    (b : SquareZeroBoundaryIndex L) :
    squareZeroWiredBoxEdgeEquiv L (Sum.inr b) =
      (sourceBoundarySigmaEquiv L (squareZeroBoundaryIndexCast L b)).1 := by
  rfl

/--
The boundary multiplicity selects an internal edge with endpoints the indexed free
vertex and the wired root.
-/
theorem sourceBoundarySigmaEquiv_endpoints (L : ℕ) (p : SquareFreeVertex L)
    (i : Fin (4 - squareZeroFreeDegree L p)) :
    ((wiredBoxGraph L).src (sourceBoundarySigmaEquiv L ⟨p, i⟩).1 = some p ∧
      (wiredBoxGraph L).tgt (sourceBoundarySigmaEquiv L ⟨p, i⟩).1 = none) ∨
    ((wiredBoxGraph L).src (sourceBoundarySigmaEquiv L ⟨p, i⟩).1 = none ∧
      (wiredBoxGraph L).tgt (sourceBoundarySigmaEquiv L ⟨p, i⟩).1 = some p) := by
  simpa only [sourceBoundarySigmaEquiv, Equiv.trans_apply,
    Equiv.sigmaCongrRight_apply, wiredBoundarySigmaEquiv_val] using
    wiredBoundaryFiber_endpoints L p (sourceBoundaryFiberEquiv L p i)

/--
The wired square and the internal face-dual wired box have the same multigraph
carrier, including each parallel boundary edge (KP p. 2 and §6.1, p. 32).
-/
noncomputable def squareZeroWiredBoxGraphIsomorphism (L : ℕ) :
    Multigraph.Isomorphism (squareZero L) (wiredBoxGraph L) where
  vertices := Equiv.refl _
  edges := squareZeroWiredBoxEdgeEquiv L
  endpoints := by
    intro e
    cases e with
    | inl e =>
        change ((wiredBoxGraph L).src (sourceFreeEdgeCrossingEquiv L e).1 =
            some ((squareFree L).src e) ∧
          (wiredBoxGraph L).tgt (sourceFreeEdgeCrossingEquiv L e).1 =
            some ((squareFree L).tgt e)) ∨
          ((wiredBoxGraph L).src (sourceFreeEdgeCrossingEquiv L e).1 =
            some ((squareFree L).tgt e) ∧
          (wiredBoxGraph L).tgt (sourceFreeEdgeCrossingEquiv L e).1 =
            some ((squareFree L).src e))
        exact sourceFreeEdgeCrossing_endpoints L e
    | inr b =>
        change ((wiredBoxGraph L).src (squareZeroWiredBoxEdgeEquiv L (Sum.inr b)) =
            some b.1 ∧
          (wiredBoxGraph L).tgt (squareZeroWiredBoxEdgeEquiv L (Sum.inr b)) = none) ∨
          ((wiredBoxGraph L).src (squareZeroWiredBoxEdgeEquiv L (Sum.inr b)) = none ∧
          (wiredBoxGraph L).tgt (squareZeroWiredBoxEdgeEquiv L (Sum.inr b)) = some b.1)
        let b' := squareZeroBoundaryIndexCast L b
        rw [squareZeroWiredBoxEdgeEquiv_inr]
        have hb := sourceBoundarySigmaEquiv_endpoints L b'.1 b'.2
        simpa [squareZero, b', squareZeroBoundaryIndexCast,
          Equiv.sigmaCongrRight_apply] using hb

end FroehlichSpencer.BKT.Duality

end
