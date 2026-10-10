/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Peierls.Extension
public import FroehlichSpencer.BKT.SOS.Peierls.Removal
public import FroehlichSpencer.BKT.Clock.Peierls.FieldSplittingSquare
import Mathlib.Tactic

/-! # Integer contour removal on an expanded SOS square

For a zero-outer height, the gradient outside a saturated contour is again a gradient.  Its
potential is normalized by proving directly that it is constant on the outer frame.  The missing
gradient on the contour is retained as the integer contour label.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Peierls

open Classical
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Clock.Peierls
open FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

def squareFreeVertexAt (N i j : ℕ) (hi : i < N) (hj : j < N) :
    SquareFreeVertex N := (⟨i, hi⟩, ⟨j, hj⟩)

private theorem squareFreePlaquetteClosed_grad {L : ℕ}
    (f : SquareFreeVertex L → ℤ) :
    squareFreePlaquetteClosed ((squareFreeGraph L).grad f) := by
  intro i j hi hj
  have hb : squareFreeHorizontalValue ((squareFreeGraph L).grad f) i j =
      f (squareFreeVertexAt L i j (by omega) (by omega)) -
        f (squareFreeVertexAt L (i + 1) j hi (by omega)) := by
    simp [squareFreeHorizontalValue, squareFreeHorizontalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, hi, show j < L by omega]
  have hr : squareFreeVerticalValue ((squareFreeGraph L).grad f) (i + 1) j =
      f (squareFreeVertexAt L (i + 1) j (by omega) (by omega)) -
        f (squareFreeVertexAt L (i + 1) (j + 1) (by omega) hj) := by
    simp [squareFreeVerticalValue, squareFreeVerticalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, show i + 1 < L by omega, hj]
  have hl : squareFreeVerticalValue ((squareFreeGraph L).grad f) i j =
      f (squareFreeVertexAt L i j (by omega) (by omega)) -
        f (squareFreeVertexAt L i (j + 1) (by omega) hj) := by
    simp [squareFreeVerticalValue, squareFreeVerticalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, show i < L by omega, hj]
  have ht : squareFreeHorizontalValue ((squareFreeGraph L).grad f) i (j + 1) =
      f (squareFreeVertexAt L i (j + 1) (by omega) (by omega)) -
        f (squareFreeVertexAt L (i + 1) (j + 1) hi hj) := by
    simp [squareFreeHorizontalValue, squareFreeHorizontalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, hi, show j + 1 < L by omega]
  rw [hb, hr, hl, ht]
  abel

private theorem horizontal_gradient_zero_eq {L : ℕ}
    (f : SquareFreeVertex L → ℤ) (i j : ℕ)
    (hi : i + 1 < L) (hj : j < L)
    (hzero : (squareFreeGraph L).grad f (squareFreeHorizontalEdgeAt i j hi hj) = 0) :
    f (squareFreeVertexAt L i j (by omega) hj) = f (squareFreeVertexAt L (i + 1) j hi hj) := by
  have h : f (squareFreeVertexAt L i j (by omega) hj) -
      f (squareFreeVertexAt L (i + 1) j hi hj) = 0 := by
    simpa [Multigraph.grad, squareFreeGraph, squareFreeHorizontalEdgeAt, squareFreeVertexAt] using hzero
  exact sub_eq_zero.mp h

private theorem vertical_gradient_zero_eq {L : ℕ}
    (f : SquareFreeVertex L → ℤ) (i j : ℕ)
    (hi : i < L) (hj : j + 1 < L)
    (hzero : (squareFreeGraph L).grad f (squareFreeVerticalEdgeAt i j hi hj) = 0) :
    f (squareFreeVertexAt L i j hi (by omega)) = f (squareFreeVertexAt L i (j + 1) hi hj) := by
  have h : f (squareFreeVertexAt L i j hi (by omega)) -
      f (squareFreeVertexAt L i (j + 1) hi hj) = 0 := by
    simpa [Multigraph.grad, squareFreeGraph, squareFreeVerticalEdgeAt, squareFreeVertexAt] using hzero
  exact sub_eq_zero.mp h

private theorem horizontal_constant_of_zero_gradient {L : ℕ}
    (f : SquareFreeVertex L → ℤ) (j : ℕ) (hj : j < L)
    (hzero : ∀ i (hi : i + 1 < L),
      (squareFreeGraph L).grad f (squareFreeHorizontalEdgeAt i j hi hj) = 0) :
    ∀ i (hi : i < L), f (squareFreeVertexAt L i j hi hj) = f (squareFreeVertexAt L 0 j (by omega) hj) := by
  intro i
  induction i with
  | zero =>
      intro hi
      rfl
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hstep := horizontal_gradient_zero_eq f i j (by omega) hj (hzero i (by omega))
      calc
        f (squareFreeVertexAt L (i + 1) j hi hj) = f (squareFreeVertexAt L i j (by omega) hj) := hstep.symm
        _ = f (squareFreeVertexAt L 0 j (by omega) hj) := hprev

private theorem vertical_constant_of_zero_gradient {L : ℕ}
    (f : SquareFreeVertex L → ℤ) (i : ℕ) (hi : i < L)
    (hzero : ∀ j (hj : j + 1 < L),
      (squareFreeGraph L).grad f (squareFreeVerticalEdgeAt i j hi hj) = 0) :
    ∀ j (hj : j < L), f (squareFreeVertexAt L i j hi hj) = f (squareFreeVertexAt L i 0 hi (by omega)) := by
  intro j
  induction j with
  | zero =>
      intro hj
      rfl
  | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hstep := vertical_gradient_zero_eq f i j hi (by omega) (hzero j (by omega))
      calc
        f (squareFreeVertexAt L i (j + 1) hi hj) = f (squareFreeVertexAt L i j hi (by omega)) := hstep.symm
        _ = f (squareFreeVertexAt L i 0 hi (by omega)) := hprev

/-- A function whose gradient vanishes on outer-frame edges is constant on the outer frame.
The proof follows the bottom, right, top, and left sides in coordinates. -/
theorem outerFrame_constant {L : ℕ} (f : SquareFreeVertex (L + 2) → ℤ)
    (hzero : ∀ e : Lattice2D.SquareFreeEdge (L + 2),
      ¬ isInnerVertex L ((squareFreeGraph (L + 2)).src e) →
      ¬ isInnerVertex L ((squareFreeGraph (L + 2)).tgt e) →
      (squareFreeGraph (L + 2)).grad f e = 0) :
    ∀ x, ¬ isInnerVertex L x →
      f x = f (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega)) := by
  intro x hx
  rcases x with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hframe : i = 0 ∨ i = L + 1 ∨ j = 0 ∨ j = L + 1 := by
    by_contra h
    push Not at h
    apply hx
    simp [isInnerVertex]
    omega
  have hBottom : ∀ k (hk : k + 1 < L + 2),
      (squareFreeGraph (L + 2)).grad f
        (squareFreeHorizontalEdgeAt k 0 hk (by omega)) = 0 := by
    intro k hk
    apply hzero
    · simp [isInnerVertex, squareFreeGraph, squareFreeHorizontalEdgeAt]
    · simp [isInnerVertex, squareFreeGraph, squareFreeHorizontalEdgeAt]
  have hLeft : ∀ k (hk : k + 1 < L + 2),
      (squareFreeGraph (L + 2)).grad f
        (squareFreeVerticalEdgeAt 0 k (by omega) hk) = 0 := by
    intro k hk
    apply hzero
    · simp [isInnerVertex, squareFreeGraph, squareFreeVerticalEdgeAt]
    · simp [isInnerVertex, squareFreeGraph, squareFreeVerticalEdgeAt]
  have hRight : ∀ k (hk : k + 1 < L + 2),
      (squareFreeGraph (L + 2)).grad f
        (squareFreeVerticalEdgeAt (L + 1) k (by omega) hk) = 0 := by
    intro k hk
    apply hzero
    · simp [isInnerVertex, squareFreeGraph, squareFreeVerticalEdgeAt]
    · simp [isInnerVertex, squareFreeGraph, squareFreeVerticalEdgeAt]
  have hTop : ∀ k (hk : k + 1 < L + 2),
      (squareFreeGraph (L + 2)).grad f
        (squareFreeHorizontalEdgeAt k (L + 1) hk (by omega)) = 0 := by
    intro k hk
    apply hzero
    · simp [isInnerVertex, squareFreeGraph, squareFreeHorizontalEdgeAt]
    · simp [isInnerVertex, squareFreeGraph, squareFreeHorizontalEdgeAt]
  rcases hframe with hi0 | hiR | hj0 | hjT
  · subst i
    have hcol := vertical_constant_of_zero_gradient f 0 (by omega) hLeft j hj
    simpa [squareFreeVertexAt] using hcol
  · subst i
    have hcol := vertical_constant_of_zero_gradient f (L + 1) (by omega) hRight j hj
    have hbottom := horizontal_constant_of_zero_gradient f 0 (by omega) hBottom (L + 1) (by omega)
    calc
      f (squareFreeVertexAt (L + 2) (L + 1) j (by omega) hj) =
        f (squareFreeVertexAt (L + 2) (L + 1) 0 (by omega) (by omega)) := hcol
      _ = f (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega)) := hbottom
  · subst j
    have hrow := horizontal_constant_of_zero_gradient f 0 (by omega) hBottom i hi
    simpa [squareFreeVertexAt] using hrow
  · subst j
    have hrow := horizontal_constant_of_zero_gradient f (L + 1) (by omega) hTop i hi
    have hleft := vertical_constant_of_zero_gradient f 0 (by omega) hLeft (L + 1) (by omega)
    calc
      f (squareFreeVertexAt (L + 2) i (L + 1) hi (by omega)) =
        f (squareFreeVertexAt (L + 2) 0 (L + 1) (by omega) (by omega)) := hrow
      _ = f (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega)) := hleft

/-- On a free square, a vertex function is determined by its gradient and its value at the
lower-left corner. -/
theorem squareFreeHeight_eq_of_grad_eq_atOrigin {N : ℕ}
    (f g : SquareFreeVertex N → ℤ)
    (hN : 0 < N)
    (hgrad : ∀ e : Lattice2D.SquareFreeEdge N,
      (squareFreeGraph N).grad f e = (squareFreeGraph N).grad g e)
    (hroot : f (squareFreeVertexAt N 0 0 hN hN) =
      g (squareFreeVertexAt N 0 0 hN hN)) :
    f = g := by
  let d : SquareFreeVertex N → ℤ := fun x => f x - g x
  have hdgrad : ∀ e : Lattice2D.SquareFreeEdge N, (squareFreeGraph N).grad d e = 0 := by
    intro e
    change (f ((squareFreeGraph N).src e) - g ((squareFreeGraph N).src e)) -
        (f ((squareFreeGraph N).tgt e) - g ((squareFreeGraph N).tgt e)) = 0
    have h := hgrad e
    simp only [Multigraph.grad] at h
    linarith
  have hdroot : d (squareFreeVertexAt N 0 0 hN hN) = 0 := by
    simp [d, hroot]
  funext x
  rcases x with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hrow := horizontal_constant_of_zero_gradient d j hj (fun k hk => by
    exact hdgrad (squareFreeHorizontalEdgeAt k j hk hj))
  have hcol := vertical_constant_of_zero_gradient d 0 (by omega) (fun k hk => by
    exact hdgrad (squareFreeVerticalEdgeAt 0 k (by omega) hk)) j hj
  have hx : d (squareFreeVertexAt N i j hi hj) =
      d (squareFreeVertexAt N 0 0 hN hN) := by
    calc
      d (squareFreeVertexAt N i j hi hj) =
          d (squareFreeVertexAt N 0 j (by omega) hj) := hrow i hi
      _ = d (squareFreeVertexAt N 0 0 hN hN) := hcol
  have hx0 : d (squareFreeVertexAt N i j hi hj) = 0 := by rw [hx, hdroot]
  change f (squareFreeVertexAt N i j hi hj) = g (squareFreeVertexAt N i j hi hj)
  dsimp [d] at hx0
  exact sub_eq_zero.mp hx0

/-- Remove the contour part of an integer gradient and normalize the resulting potential to be
zero on the outer frame.  The assumption that every selected edge touches the pinned inner square
ensures that the outside gradient vanishes along every outer-frame edge. -/
theorem zeroOuterContourRemoval_existsUnique {L : ℕ}
    (n : SquareFreeVertex (L + 2) → ℤ) (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (hn : zeroOnOuterLayer n)
    (hinner : ∀ e ∈ Γ,
      isInnerVertex L ((squareFreeGraph (L + 2)).src e) ∨
        isInnerVertex L ((squareFreeGraph (L + 2)).tgt e))
    (hsaturated : squareFreePlaquetteSaturated ((squareFreeGraph (L + 2)).grad n) Γ) :
    ∃! n' : SquareFreeVertex (L + 2) → ℤ,
      zeroOnOuterLayer n' ∧
        ∀ e, (squareFreeGraph (L + 2)).grad n' e =
          restrictEdgeFieldOutside Γ ((squareFreeGraph (L + 2)).grad n) e := by
  let η : Lattice2D.SquareFreeEdge (L + 2) → ℤ := (squareFreeGraph (L + 2)).grad n
  let ηout := restrictEdgeFieldOutside Γ η
  have hclosed : squareFreePlaquetteClosed η := by
    exact squareFreePlaquetteClosed_grad n
  have hsplit := squareFreePlaquetteClosed_restrict_split η Γ hclosed (by
    simpa [η] using hsaturated)
  obtain ⟨f, hf⟩ := squareFreeEdgeField_isGradient ηout hsplit.2
  have hframeGrad : ∀ e : Lattice2D.SquareFreeEdge (L + 2),
      ¬ isInnerVertex L ((squareFreeGraph (L + 2)).src e) →
      ¬ isInnerVertex L ((squareFreeGraph (L + 2)).tgt e) →
      (squareFreeGraph (L + 2)).grad f e = 0 := by
    intro e hs ht
    have hnot : e ∉ Γ := by
      intro he
      exact (hinner e he).elim hs ht
    have hηzero : η e = 0 := by
      dsimp [η, Multigraph.grad]
      rw [hn _ hs, hn _ ht]
      simp
    have houtzero : ηout e = 0 := by
      simp [ηout, restrictEdgeFieldOutside, hnot, hηzero]
    rw [hf e, houtzero]
  let n' : SquareFreeVertex (L + 2) → ℤ := fun x =>
    f x - f (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega))
  have hn'outer : zeroOnOuterLayer n' := by
    intro x hx
    have hconst := outerFrame_constant f hframeGrad x hx
    simp [n', hconst]
  have hn'grad : ∀ e, (squareFreeGraph (L + 2)).grad n' e = ηout e := by
    intro e
    calc
      (squareFreeGraph (L + 2)).grad n' e = (squareFreeGraph (L + 2)).grad f e := by
        simp only [Multigraph.grad]
        dsimp [n']
        ring
      _ = ηout e := hf e
  refine ⟨n', ⟨hn'outer, ?_⟩, ?_⟩
  · intro e
    simpa [ηout, η] using hn'grad e
  · intro m hm
    apply squareFreeHeight_eq_of_grad_eq_atOrigin m n' (by omega)
    · intro e
      rw [hm.2 e]
      exact (hn'grad e).symm
    · have hmo := hm.1 (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega)) (by
        simp [isInnerVertex, squareFreeVertexAt])
      have hno := hn'outer (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega)) (by
        simp [isInnerVertex, squareFreeVertexAt])
      rw [hmo, hno]

/-- Integer heights eligible for removal of a fixed saturated contour. -/
abbrev RemovableSOSHeight {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :=
  {n : SquareFreeVertex (L + 2) → ℤ //
    zeroOnOuterLayer n ∧
      (∀ e ∈ Γ, isInnerVertex L ((squareFreeGraph (L + 2)).src e) ∨
        isInnerVertex L ((squareFreeGraph (L + 2)).tgt e)) ∧
      squareFreePlaquetteSaturated ((squareFreeGraph (L + 2)).grad n) Γ ∧
      ∀ e ∈ Γ, (squareFreeGraph (L + 2)).grad n e ≠ 0}

/-- The canonically chosen normalized height after deleting a saturated contour. -/
noncomputable def contourRemovedHeight {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (n : RemovableSOSHeight Γ) : SquareFreeVertex (L + 2) → ℤ :=
  Classical.choose (zeroOuterContourRemoval_existsUnique n.1 Γ n.2.1 n.2.2.1 n.2.2.2.1).exists

theorem contourRemovedHeight_spec {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (n : RemovableSOSHeight Γ) :
    zeroOnOuterLayer (contourRemovedHeight Γ n) ∧
      ∀ e, (squareFreeGraph (L + 2)).grad (contourRemovedHeight Γ n) e =
        restrictEdgeFieldOutside Γ ((squareFreeGraph (L + 2)).grad n.1) e := by
  exact Classical.choose_spec
    (zeroOuterContourRemoval_existsUnique n.1 Γ n.2.1 n.2.2.1 n.2.2.2.1).exists

/-- The removed configuration together with its nonzero integer contour gradient. -/
noncomputable def integerContourRemovalEncoding {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (n : RemovableSOSHeight Γ) :
    (SquareFreeVertex (L + 2) → ℤ) × IntegerContourLabel Γ :=
  (contourRemovedHeight Γ n, fun e =>
    ⟨(squareFreeGraph (L + 2)).grad n.1 e.1, n.2.2.2.2 e.1 e.2⟩)

/-- The removal encoding is injective: the removed gradient determines the outside part, while
the integer contour label records the inside part. -/
theorem integerContourRemovalEncoding_injective {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :
    Function.Injective (integerContourRemovalEncoding Γ) := by
  intro n m h
  have hremoved : contourRemovedHeight Γ n = contourRemovedHeight Γ m :=
    congrArg Prod.fst h
  have hlabel := congrArg Prod.snd h
  apply Subtype.ext
  apply squareFreeHeight_eq_of_grad_eq_atOrigin n.1 m.1 (by omega)
  · intro e
    by_cases he : e ∈ Γ
    · have hval := congrFun hlabel ⟨e, he⟩
      have hval' :
          (⟨(squareFreeGraph (L + 2)).grad n.1 e, n.2.2.2.2 e he⟩ :
            {d : ℤ // d ≠ 0}) =
          ⟨(squareFreeGraph (L + 2)).grad m.1 e, m.2.2.2.2 e he⟩ := by
        simpa [integerContourRemovalEncoding] using hval
      exact congrArg Subtype.val hval'
    · have hnSpec := contourRemovedHeight_spec Γ n
      have hmSpec := contourRemovedHeight_spec Γ m
      calc
        (squareFreeGraph (L + 2)).grad n.1 e =
            restrictEdgeFieldOutside Γ ((squareFreeGraph (L + 2)).grad n.1) e := by
          simp [restrictEdgeFieldOutside, he]
        _ = (squareFreeGraph (L + 2)).grad (contourRemovedHeight Γ n) e :=
          (hnSpec.2 e).symm
        _ = (squareFreeGraph (L + 2)).grad (contourRemovedHeight Γ m) e := by
          rw [hremoved]
        _ = restrictEdgeFieldOutside Γ ((squareFreeGraph (L + 2)).grad m.1) e :=
          hmSpec.2 e
        _ = (squareFreeGraph (L + 2)).grad m.1 e := by
          simp [restrictEdgeFieldOutside, he]
  · have horiginN := n.2.1 (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega)) (by
      simp [isInnerVertex, squareFreeVertexAt])
    have horiginM := m.2.1 (squareFreeVertexAt (L + 2) 0 0 (by omega) (by omega)) (by
      simp [isInnerVertex, squareFreeVertexAt])
    rw [horiginN, horiginM]

end FroehlichSpencer.BKT.SOS.Peierls

end
