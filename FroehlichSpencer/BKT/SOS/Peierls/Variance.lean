/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Peierls.ActiveSOS
public import FroehlichSpencer.BKT.SOS.Peierls.RemovalEstimate
public import FroehlichSpencer.BKT.SOS.Peierls.Summability
public import FroehlichSpencer.BKT.SOS.Peierls.RougheningTransition
import Mathlib.Tactic

/-! # Low-temperature SOS variance: component-flux reduction -/

@[expose] public section

noncomputable section

open Classical
open scoped BigOperators
open Filter Topology

namespace FroehlichSpencer.BKT.SOS.Peierls

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight sosPartition sosVariance
  sosHeightWeight_pos linfDist)
open FroehlichSpencer.BKT.Clock.Peierls
open FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

/-- A prefix of the horizontal row from the left outer frame to a pinned site. -/
def sosPrefixLength {L : ℕ} (u : Site L) : ℕ := u.1.val + 1

/-- The horizontal path from the left outer frame to the horizontal coordinate of `u`. -/
def sosPrefixPath {L : ℕ} (u : Site L)
    (i : Fin (sosPrefixLength u)) : Lattice2D.SquareFreeEdge (L + 2) :=
  @FroehlichSpencer.BKT.SOS.Peierls.sosHorizontalPathEdge
    (L + 2) (u.1.val + 1) (u.2.val + 1) (by omega) (by omega) i

private theorem sosHorizontalPathFlux_eq_segmentSum {N R y : ℕ}
    (η : Lattice2D.SquareFreeEdge N → ℤ) (hR : R < N) (hy : y < N) :
    clockPeierlsPathFlux η (sosHorizontalPathEdge hR hy) =
      squareFreeHorizontalSegmentSum η y 0 R := by
  classical
  unfold clockPeierlsPathFlux
  let f : ℕ → ℤ := fun i =>
    if hi : i + 1 < N then
      η (GenericGradient.squareFreeHorizontalEdgeAt i y hi hy) else 0
  have hpath : (∑ i : Fin R, η (sosHorizontalPathEdge hR hy i)) =
      ∑ i : Fin R, f i.val := by
    apply Finset.sum_congr rfl
    intro i _
    have hiN : i.val + 1 < N := by omega
    simp [f, sosHorizontalPathEdge, hiN]
  rw [hpath, Fin.sum_univ_eq_sum_range f R]
  have hseg (r : ℕ) : squareFreeHorizontalSegmentSum η y 0 r =
      ∑ i ∈ Finset.range r, GenericGradient.squareFreeHorizontalValue η i y := by
    induction r with
    | zero => simp [squareFreeHorizontalSegmentSum]
    | succ r ih =>
        rw [squareFreeHorizontalSegmentSum, Finset.sum_range_succ, ih]
        simp
  rw [hseg]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i + 1 < N := by have := Finset.mem_range.mp hi; omega
  simp [f, GenericGradient.squareFreeHorizontalValue, hiN, hy]

private theorem sum_pathAbs_le_support {P E : Type*} [Fintype P] [DecidableEq E]
    (p : P → E) (hp : Function.Injective p) (η : E → ℤ) (S : Finset E) :
    (∑ i : P, if p i ∈ S then |η (p i)| else 0) ≤ ∑ e ∈ S, |η e| := by
  classical
  let I : Finset P := Finset.univ.filter fun i => p i ∈ S
  have hfilter :
      (∑ i : P, if p i ∈ S then |η (p i)| else 0) =
        ∑ i ∈ I, |η (p i)| := by
    simp [I, Finset.sum_ite]
  have himage : I.image p ⊆ S := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  have hsumImage :
      (∑ e ∈ I.image p, |η e|) = ∑ i ∈ I, |η (p i)| := by
    apply Finset.sum_image
    intro i hi j hj hij
    exact hp hij
  calc
    _ = ∑ i ∈ I, |η (p i)| := hfilter
    _ = ∑ e ∈ I.image p, |η e| := hsumImage.symm
    _ ≤ ∑ e ∈ S, |η e| := Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun e _ _ => abs_nonneg _)

private theorem componentFlux_abs_le_support {N R y : ℕ}
    (hR : R < N) (hy : y < N) (η : Lattice2D.SquareFreeEdge N → ℤ)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph N) η).ConnectedComponent) :
    |clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph N) η
        (sosHorizontalPathEdge hR hy) c| ≤
      ∑ e ∈ clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph N) η c, |η e| := by
  classical
  let p := sosHorizontalPathEdge hR hy
  let S := clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph N) η c
  have hp : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    have hanchor := congrArg clockPeierlsEdgeAnchor hij
    have hval : i.val = j.val := by
      simpa [p, sosHorizontalPathEdge, clockPeierlsEdgeAnchor,
        GenericGradient.squareFreeHorizontalEdgeAt] using congrArg Prod.fst hanchor
    exact hval
  unfold clockPeierlsComponentFlux
  change |∑ i : Fin R, if p i ∈ S then η (p i) else 0| ≤ ∑ e ∈ S, |η e|
  calc
    _ ≤ ∑ i : Fin R, |if p i ∈ S then η (p i) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin R, if p i ∈ S then |η (p i)| else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    _ ≤ _ := sum_pathAbs_le_support p hp η S

private theorem sosGradient_closed {L : ℕ} (f : SquareFreeVertex L → ℤ) :
    squareFreePlaquetteClosed ((squareFreeGraph L).grad f) := by
  intro i j hi hj
  have hb : GenericGradient.squareFreeHorizontalValue ((squareFreeGraph L).grad f) i j =
      f (squareFreeVertexAt L i j (by omega) (by omega)) -
        f (squareFreeVertexAt L (i + 1) j hi (by omega)) := by
    simp [GenericGradient.squareFreeHorizontalValue, GenericGradient.squareFreeHorizontalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, hi, show j < L by omega]
  have hr : GenericGradient.squareFreeVerticalValue ((squareFreeGraph L).grad f) (i + 1) j =
      f (squareFreeVertexAt L (i + 1) j (by omega) (by omega)) -
        f (squareFreeVertexAt L (i + 1) (j + 1) (by omega) hj) := by
    simp [GenericGradient.squareFreeVerticalValue, GenericGradient.squareFreeVerticalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, show i + 1 < L by omega, hj]
  have hl : GenericGradient.squareFreeVerticalValue ((squareFreeGraph L).grad f) i j =
      f (squareFreeVertexAt L i j (by omega) (by omega)) -
        f (squareFreeVertexAt L i (j + 1) (by omega) hj) := by
    simp [GenericGradient.squareFreeVerticalValue, GenericGradient.squareFreeVerticalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, show i < L by omega, hj]
  have ht : GenericGradient.squareFreeHorizontalValue ((squareFreeGraph L).grad f) i (j + 1) =
      f (squareFreeVertexAt L i (j + 1) (by omega) (by omega)) -
        f (squareFreeVertexAt L (i + 1) (j + 1) hi hj) := by
    simp [GenericGradient.squareFreeHorizontalValue, GenericGradient.squareFreeHorizontalEdgeAt,
      Multigraph.grad, squareFreeGraph, squareFreeVertexAt, hi, show j + 1 < L by omega]
  rw [hb, hr, hl, ht]
  abel

private theorem sosGenericPlaquetteEdges_mem_clock {N : ℕ}
    (i j : ℕ) (hi : i + 1 < N) (hj : j + 1 < N)
    {e : Lattice2D.SquareFreeEdge N}
    (he : e ∈ GenericGradient.squareFreePlaquetteEdges i j hi hj) :
    e ∈ clockPeierlsPlaquetteEdges (L := N) ⟨i, by omega⟩ ⟨j, by omega⟩
      (by omega) (by omega) := by
  simp [GenericGradient.squareFreePlaquetteEdges, clockPeierlsPlaquetteEdges,
    GenericGradient.squareFreeHorizontalEdgeAt, clockPeierlsHorizontalEdgeAt,
    GenericGradient.squareFreeVerticalEdgeAt, clockPeierlsVerticalEdgeAt] at he ⊢
  aesop

/-- Plaquette components of a nonzero edge field are saturated, independently of the coefficient
group. -/
private theorem sosComponentSupport_saturated {N : ℕ}
    (η : Lattice2D.SquareFreeEdge N → ℤ)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph N) η).ConnectedComponent) :
    squareFreePlaquetteSaturated η
      (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph N) η c) := by
  intro i j hi hj hmeet f hf
  rcases hmeet with ⟨e, hePlaquette, heS⟩
  by_cases hfzero : η f = 0
  · exact Or.inl hfzero
  · have ⟨heBad, heComp⟩ :=
      (mem_clockPeierlsComponentSupport_iff (clockPeierlsAdjacencyGraph N) η c e).mp heS
    have he' := sosGenericPlaquetteEdges_mem_clock i j hi hj hePlaquette
    have hf' := sosGenericPlaquetteEdges_mem_clock i j hi hj hf
    have hshare : clockPeierlsSharesPlaquette e f :=
      ⟨⟨i, by omega⟩, ⟨j, by omega⟩, by omega, by omega, he', hf'⟩
    by_cases hef : e = f
    · subst f
      exact Or.inr heS
    · have hadj : (clockPeierlsAdjacencyGraph N).Adj e f := ⟨hef, hshare⟩
      have hbadAdj :
          (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph N) η).Adj
            ⟨e, heBad⟩ ⟨f, hfzero⟩ := SimpleGraph.induce_adj.mpr hadj
      have hfComp :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hbadAdj).symm.trans heComp
      exact Or.inr ((mem_clockPeierlsComponentSupport_iff
        (clockPeierlsAdjacencyGraph N) η c f).2 ⟨hfzero, hfComp⟩)

/-- The gradient flux along the prefix from the left outer frame to `u` is the negative pinned
height, since the field is zero on the outer frame. -/
theorem sosPrefixFlux_eq_neg_height {L : ℕ}
    (u : Site L) (n : Site L → ℤ) :
    clockPeierlsPathFlux ((squareFreeGraph (L + 2)).grad (extendHeight L n))
      (sosPrefixPath u) = -(n u) := by
  let R := sosPrefixLength u
  have hR : R < L + 2 := by dsimp [R, sosPrefixLength]; omega
  have hy : u.2.val + 1 < L + 2 := by omega
  have hsegment :
      clockPeierlsPathFlux ((squareFreeGraph (L + 2)).grad (extendHeight L n))
          (sosPrefixPath u) =
        squareFreeHorizontalSegmentSum ((squareFreeGraph (L + 2)).grad (extendHeight L n))
          (u.2.val + 1) 0 R := by
    have hpath : sosPrefixPath u = sosHorizontalPathEdge hR hy := by
      funext i
      simp [sosPrefixPath, R, sosPrefixLength, sosHorizontalPathEdge]
    rw [hpath]
    exact sosHorizontalPathFlux_eq_segmentSum
      ((squareFreeGraph (L + 2)).grad (extendHeight L n)) hR hy
  rw [hsegment]
  rw [squareFreeHorizontalSegmentSum_grad (extendHeight L n)
    (u.2.val + 1) 0 R hy (by dsimp [R, sosPrefixLength]; omega)]
  have hleft : extendHeight L n
      (⟨⟨0, by omega⟩, ⟨u.2.val + 1, by omega⟩⟩ : SquareFreeVertex (L + 2)) = 0 := by
    apply extendHeight_zero_of_not_inner
    simp [isInnerVertex]
  have hend : extendHeight L n
      (⟨⟨0 + R, by omega⟩, ⟨u.2.val + 1, hy⟩⟩ : SquareFreeVertex (L + 2)) = n u := by
    dsimp [R, sosPrefixLength]
    simp only [Nat.zero_add]
    change extendHeight L n (innerSite u) = n u
    exact extendHeight_innerSite n u
  rw [hleft, hend]
  simp

/-- The pinned height is the sum of the fluxes of its nonzero-gradient components, up to the
orientation of the path from the outer frame. -/
theorem sosHeight_eq_neg_sum_componentFlux {L : ℕ}
    (u : Site L) (n : Site L → ℤ) :
    n u = - ∑ c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent,
      clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath u) c := by
  have hsum := clockPeierlsPathFlux_eq_sum_componentFlux
    (clockPeierlsAdjacencyGraph (L + 2))
    ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath u)
  rw [sosPrefixFlux_eq_neg_height u n] at hsum
  linarith

/-- The absolute pinned height is bounded by the sum of absolute gradients in its active contour
components. The estimate is pointwise in the configuration. -/
theorem sosHeight_abs_le_componentObservable {L : ℕ} (u : Site L) (n : Site L → ℤ) :
    |n u| ≤ ∑ c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent,
      ∑ e ∈ clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c,
        |(squareFreeGraph (L + 2)).grad (extendHeight L n) e| := by
  classical
  let η := (squareFreeGraph (L + 2)).grad (extendHeight L n)
  let G := clockPeierlsAdjacencyGraph (L + 2)
  let R := sosPrefixLength u
  have hR : R < L + 2 := by dsimp [R, sosPrefixLength]; omega
  have hy : u.2.val + 1 < L + 2 := by omega
  have hpath : sosPrefixPath u = sosHorizontalPathEdge hR hy := by
    funext i
    simp [sosPrefixPath, R, sosPrefixLength, sosHorizontalPathEdge]
  have hsum := sosHeight_eq_neg_sum_componentFlux u n
  calc
    |n u| = |∑ c : (clockPeierlsBadGraph G η).ConnectedComponent,
        clockPeierlsComponentFlux G η (sosPrefixPath u) c| := by
          rw [hsum]
          simp [G, η]
    _ ≤ ∑ c : (clockPeierlsBadGraph G η).ConnectedComponent,
        |clockPeierlsComponentFlux G η (sosPrefixPath u) c| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : (clockPeierlsBadGraph G η).ConnectedComponent,
        ∑ e ∈ clockPeierlsComponentSupport G η c, |η e| := by
          apply Finset.sum_le_sum
          intro c hc
          rw [hpath]
          exact componentFlux_abs_le_support hR hy η c
    _ = _ := by rfl

/-- A component with nonzero flux across the pinned prefix has a path edge in its support, and the
row-detour estimate forces its size at every such edge. -/
theorem sosActiveComponent_has_largeSupport {L : ℕ} (u : Site L) (n : Site L → ℤ)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent)
    (hflux : clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath u) c ≠ 0) :
    ∃ i : Fin (sosPrefixLength u),
      sosPrefixPath u i ∈ clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c ∧
      clockPeierlsMinContourSize (sosPrefixLength u)
          (max (u.2.val + 1) (L + 1 - (u.2.val + 1))) (i.val + 1) ≤
        (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
          ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c).card := by
  classical
  let η := (squareFreeGraph (L + 2)).grad (extendHeight L n)
  let R := sosPrefixLength u
  let y := u.2.val + 1
  let G := clockPeierlsAdjacencyGraph (L + 2)
  have hR : R < L + 2 := by dsimp [R, sosPrefixLength]; omega
  have hy : y < L + 2 := by dsimp [y]; omega
  have hpath : sosPrefixPath u = sosHorizontalPathEdge hR hy := by
    funext i
    simp [sosPrefixPath, R, y, sosPrefixLength, sosHorizontalPathEdge]
  have hroot : ∃ i : Fin R,
      sosHorizontalPathEdge hR hy i ∈ clockPeierlsComponentSupport G η c := by
    by_contra h
    have hnot : ∀ i : Fin R,
        sosHorizontalPathEdge hR hy i ∉ clockPeierlsComponentSupport G η c := by
      intro i hi
      exact h ⟨i, hi⟩
    have hzero : clockPeierlsComponentFlux G η (sosHorizontalPathEdge hR hy) c = 0 := by
      unfold clockPeierlsComponentFlux
      simp [hnot]
    exact hflux (by simpa [G, η, hpath] using hzero)
  rcases hroot with ⟨i, hi⟩
  refine ⟨i, ?_, ?_⟩
  · simpa [hpath] using hi
  · have hsize := sosComponent_minContourSize_row_le hR hy η
      (sosGradient_closed (extendHeight L n)) c (sosComponentSupport_saturated η c)
      i (by simpa [hpath] using hflux) hi
    simpa [R, y, G, η] using hsize

/-- For a horizontal prefix whose length is at most twice the available vertical margin, a contour
of size `k + 1` can cross only `O(k)` path positions. -/
theorem sosActivePositions_card_le (R M k : ℕ) (hRM : R ≤ 2 * M) :
    ((Finset.Icc 1 R).filter fun j =>
      clockPeierlsMinContourSize R M j ≤ k + 1).card ≤ 4 * (k + 5) := by
  classical
  let active := (Finset.Icc 1 R).filter fun j =>
    clockPeierlsMinContourSize R M j ≤ k + 1
  let left := Finset.Icc 1 (k + 4)
  let right := Finset.Icc (R - (k + 4)) R
  by_cases hM : M ≤ k + 4
  · have hsub : active ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
    have hcard : active.card ≤ R := by
      calc
        active.card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsub
        _ = R := by simp
    calc
      active.card ≤ R := hcard
      _ ≤ 2 * M := hRM
      _ ≤ 2 * (k + 4) := Nat.mul_le_mul_left 2 hM
      _ ≤ 4 * (k + 5) := by omega
  · have hM' : k + 4 < M := by omega
    have hsubset : active ⊆ left ∪ right := by
      intro j hj
      have hjmem : j ∈ Finset.Icc 1 R := (Finset.mem_filter.mp hj).1
      have hjact : clockPeierlsMinContourSize R M j ≤ k + 1 :=
        (Finset.mem_filter.mp hj).2
      have hjbounds : 1 ≤ j ∧ j ≤ R := by simpa only [Finset.mem_Icc] using hjmem
      change max 1 (min j (min (R - j) M) - 3) ≤ k + 1 at hjact
      have hmin : min j (min (R - j) M) ≤ k + 4 := by omega
      have hmin' : min j (R - j) ≤ k + 4 := by
        by_contra hn
        have hgt : k + 4 < min j (R - j) := by omega
        have hj' : k + 4 < j := lt_of_lt_of_le hgt (Nat.min_le_left _ _)
        have hr' : k + 4 < R - j := lt_of_lt_of_le hgt (Nat.min_le_right _ _)
        have hrest : k + 4 < min (R - j) M := lt_min_iff.mpr ⟨hr', hM'⟩
        have hwhole : k + 4 < min j (min (R - j) M) :=
          lt_min_iff.mpr ⟨hj', hrest⟩
        omega
      rcases min_le_iff.mp hmin' with hjleft | hjright
      · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨by omega, hjleft⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_Icc.mpr ⟨by omega, hjbounds.2⟩)
    have hleft : left.card ≤ k + 4 := by simp [left]
    have hright : right.card ≤ k + 5 := by simp [right]; omega
    calc
      active.card ≤ (left ∪ right).card := Finset.card_le_card hsubset
      _ ≤ left.card + right.card := Finset.card_union_le _ _
      _ ≤ (k + 4) + (k + 5) := Nat.add_le_add hleft hright
      _ ≤ 4 * (k + 5) := by omega

/-- The one-contour second-moment activity for integer edge labels. -/
def sosContourSecondActivity (β : ℝ) : ℝ :=
  ∑' d : {d : ℤ // d ≠ 0}, (d.1 : ℝ) ^ 2 * Real.exp (-(β * |(d.1 : ℝ)|))

private def sosNatSecondActivityTerm (β : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.exp (-β * (n : ℝ))

private def sosIntSecondActivityTerm (β : ℝ) (d : ℤ) : ℝ :=
  (d : ℝ) ^ 2 * Real.exp (-(β * |(d : ℝ)|))

private theorem sosIntSecondActivity_positive (β : ℝ) (n : ℕ) :
    sosIntSecondActivityTerm β (n : ℤ) = sosNatSecondActivityTerm β n := by
  simp [sosIntSecondActivityTerm, sosNatSecondActivityTerm, abs_of_nonneg]

private theorem sosIntSecondActivity_negative (β : ℝ) (n : ℕ) :
    sosIntSecondActivityTerm β (-(↑n + 1)) = sosNatSecondActivityTerm β (n + 1) := by
  have hcast : ((-(↑n + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
  unfold sosIntSecondActivityTerm
  rw [hcast, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
  simp only [sosNatSecondActivityTerm]
  push_cast
  rw [show -(β * ((n : ℝ) + 1)) = -β * ((n : ℝ) + 1) by ring]
  ring

private theorem sosIntSecondActivity_summable {β : ℝ} (hβ : 0 < β) :
    Summable (sosIntSecondActivityTerm β) := by
  have hnat : Summable (sosNatSecondActivityTerm β) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 2 hβ using 1
    ext n
    rfl
  have htail : Summable fun n : ℕ => sosNatSecondActivityTerm β (n + 1) :=
    Summable.comp_injective (i := fun n : ℕ => n + 1) hnat
      (fun a b h => Nat.add_right_cancel h)
  have hpos : Summable fun n : ℕ => sosIntSecondActivityTerm β n := by
    convert hnat using 1
    ext n
    exact sosIntSecondActivity_positive β n
  have hneg : Summable fun n : ℕ =>
      sosIntSecondActivityTerm β (-(↑n + 1)) := by
    convert htail using 1
    ext n
    exact sosIntSecondActivity_negative β n
  exact Summable.of_nat_of_neg_add_one hpos hneg

private theorem sosContourSecondActivity_eq_int_sum {β : ℝ} (hβ : 0 < β) :
    sosContourSecondActivity β = ∑' d : ℤ, sosIntSecondActivityTerm β d := by
  have hsum := sosIntSecondActivity_summable hβ
  have hzero : sosIntSecondActivityTerm β 0 = 0 := by simp [sosIntSecondActivityTerm]
  calc
    sosContourSecondActivity β =
        ∑' d : {d : ℤ // d ≠ 0}, sosIntSecondActivityTerm β d.1 := rfl
    _ = ∑' d : ℤ,
          ({d : ℤ | d ≠ 0}.indicator (sosIntSecondActivityTerm β)) d := by
        exact tsum_subtype {d : ℤ | d ≠ 0} (sosIntSecondActivityTerm β)
    _ = ∑' d : ℤ, sosIntSecondActivityTerm β d := by
        apply tsum_congr
        intro d
        by_cases hd : d ≠ 0
        · simp [hd]
        · have : d = 0 := by simpa using hd
          subst d
          simp [hzero]

private theorem sosNatSecondActivity_tsum_eq {β : ℝ} (hβ : 0 < β) :
    (∑' n : ℕ, sosNatSecondActivityTerm β n) =
      Real.exp (-β) * (1 + Real.exp (-β)) / (1 - Real.exp (-β)) ^ 3 := by
  let r : ℝ := Real.exp (-β)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hexp (n : ℕ) : Real.exp (-β * (n : ℝ)) = r ^ n := by
    rw [show -β * (n : ℝ) = (n : ℝ) * (-β) by ring, Real.exp_nat_mul]
  calc
    _ = ∑' n : ℕ, (n : ℝ) ^ 2 * r ^ n := by
      apply tsum_congr
      intro n
      change (n : ℝ) ^ 2 * Real.exp (-β * (n : ℝ)) = (n : ℝ) ^ 2 * r ^ n
      rw [hexp]
    _ = r * (1 + r) / (1 - r) ^ 3 := by
      have hrnorm : ‖r‖ < 1 := by
        rw [Real.norm_of_nonneg hr0]
        exact hrlt
      exact tsum_sq_mul_geometric_of_norm_lt_one hrnorm
    _ = _ := by rfl

/-- At sufficiently large inverse temperature, the label activity including the quadratic
observable is uniformly small. -/
theorem sosContourSecondActivity_le_small {β : ℝ} (hβ : 10000000 ≤ β) :
    sosContourSecondActivity β ≤ 1 / 100000 := by
  have hβpos : 0 < β := by linarith
  let r : ℝ := Real.exp (-β)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hExpLower : 1 + β ≤ Real.exp β := by
    simpa [add_comm] using Real.add_one_le_exp β
  have hrle : r ≤ 1 / 10000000 := by
    dsimp [r]
    calc
      Real.exp (-β) = 1 / Real.exp β := by simpa [one_div] using Real.exp_neg β
      _ ≤ 1 / (1 + β) := one_div_le_one_div_of_le (by positivity) hExpLower
      _ ≤ 1 / 10000000 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hrlt : r < 1 := by linarith
  have hden : 0 < 1 - r := by linarith
  have hdenhalf : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    have hdiv : (1 : ℝ) / (1 - r) ≤ 2 := (div_le_iff₀ hden).2 (by linarith)
    simpa [one_div] using hdiv
  have hinv0 : 0 ≤ (1 - r)⁻¹ := by positivity
  have hinv3 : (1 - r)⁻¹ ^ 3 ≤ 8 := by
    calc
      (1 - r)⁻¹ ^ 3 ≤ (2 : ℝ) ^ 3 := by gcongr
      _ = 8 := by norm_num
  have hnat := sosNatSecondActivity_tsum_eq hβpos
  have hnatBound :
      (∑' n : ℕ, sosNatSecondActivityTerm β n) ≤ 16 / 10000000 := by
    rw [hnat]
    have hnum : r * (1 + r) ≤ (2 : ℝ) / 10000000 := by
      have hfactor : 1 + r ≤ 2 := by linarith
      have hfactor0 : 0 ≤ 1 + r := by linarith
      calc
        r * (1 + r) ≤ (1 / 10000000) * 2 :=
          mul_le_mul hrle hfactor hfactor0 (by norm_num)
        _ = (2 : ℝ) / 10000000 := by norm_num
    calc
      r * (1 + r) / (1 - r) ^ 3 = r * (1 + r) * (1 - r)⁻¹ ^ 3 := by
        rw [div_eq_mul_inv, inv_pow]
      _ ≤ (2 / 10000000) * 8 :=
        mul_le_mul hnum hinv3 (by positivity) (by positivity)
      _ = 16 / 10000000 := by norm_num
  have htailSummable : Summable fun n : ℕ => sosNatSecondActivityTerm β (n + 1) := by
    have hs' : Summable fun n : ℕ => sosNatSecondActivityTerm β n := by
      simpa [sosNatSecondActivityTerm] using Real.summable_pow_mul_exp_neg_nat_mul 2 hβpos
    exact Summable.comp_injective (i := fun n : ℕ => n + 1) hs'
      (fun a b h => Nat.add_right_cancel h)
  have hnatSummable : Summable (sosNatSecondActivityTerm β) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 2 hβpos using 1
    ext n
    rfl
  have htailEq :
      (∑' n : ℕ, sosNatSecondActivityTerm β (n + 1)) =
        ∑' n : ℕ, sosNatSecondActivityTerm β n := by
    have hzero : sosNatSecondActivityTerm β 0 = 0 := by simp [sosNatSecondActivityTerm]
    calc
      _ = sosNatSecondActivityTerm β 0 + _ := by rw [hzero, zero_add]
      _ = _ := hnatSummable.tsum_eq_zero_add.symm
  have hIntTsum :
      (∑' d : ℤ, sosIntSecondActivityTerm β d) =
        (∑' n : ℕ, sosNatSecondActivityTerm β n) +
          (∑' n : ℕ, sosNatSecondActivityTerm β (n + 1)) := by
    have hpos : Summable fun n : ℕ => sosIntSecondActivityTerm β n := by
      convert (Real.summable_pow_mul_exp_neg_nat_mul 2 hβpos) using 1
      ext n
      rw [sosIntSecondActivity_positive]
      rfl
    have hneg : Summable fun n : ℕ => sosIntSecondActivityTerm β (-(↑n + 1)) := by
      convert htailSummable using 1
      ext n
      exact sosIntSecondActivity_negative β n
    rw [tsum_of_nat_of_neg_add_one hpos hneg]
    congr 1
    · apply tsum_congr
      intro n
      exact sosIntSecondActivity_positive β n
    · apply tsum_congr
      intro n
      exact sosIntSecondActivity_negative β n
  rw [sosContourSecondActivity_eq_int_sum hβpos, hIntTsum]
  rw [htailEq]
  calc
    (∑' n : ℕ, sosNatSecondActivityTerm β n) +
        (∑' n : ℕ, sosNatSecondActivityTerm β n) =
        (∑' n : ℕ, sosNatSecondActivityTerm β n) * 2 := by ring
    _ ≤ (16 / 10000000) * 2 :=
      mul_le_mul_of_nonneg_right hnatBound (by norm_num)
    _ ≤ 1 / 100000 := by norm_num

private def sosContourSquareTerm {L : ℕ} (β : ℝ)
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ}) : ℝ :=
  expandedSOSWeight L β c.1.1 *
    ∏ e ∈ Γ, |(((squareFreeGraph (L + 2)).grad c.1.1 e : ℤ) : ℝ)| ^ 2

private theorem sosContourSquareTerm_nonneg {L : ℕ} (β : ℝ)
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ}) :
    0 ≤ sosContourSquareTerm β Γ c := by
  unfold sosContourSquareTerm expandedSOSWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg fun e _ => Real.exp_nonneg _
  · exact Finset.prod_nonneg fun e _ => sq_nonneg _

/-- The fixed-contour square-label observable has a genuine finite real expectation, bounded by
the partition function times the one-edge quadratic activity to the contour size. -/
private theorem sosContourSquareMoment_le {L : ℕ} (hL : 1 < L) {β : ℝ}
    (hβ : 0 < β) (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :
    Summable (sosContourSquareTerm β Γ) ∧
      (∑' c, sosContourSquareTerm β Γ c) ≤
        sosPartition L β * sosContourSecondActivity β ^ Γ.card := by
  classical
  let g : ℤ → ℝ := fun d => |(d : ℝ)| ^ 2
  have hg : ∀ d, 0 ≤ g d := fun _ => sq_nonneg _
  have hactNonneg : 0 ≤ sosContourSecondActivity β := by
    unfold sosContourSecondActivity
    exact tsum_nonneg fun d => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hsAct : Summable fun d : {d : ℤ // d ≠ 0} =>
      g d.1 * Real.exp (-(β * |(d.1 : ℝ)|)) := by
    have hs := Summable.comp_injective (i := fun d : {d : ℤ // d ≠ 0} => d.1)
      (sosIntSecondActivity_summable hβ) Subtype.val_injective
    exact hs.congr fun d => by
      simp [g, sosIntSecondActivityTerm, sq_abs]
  have hactEq : (∑' d : {d : ℤ // d ≠ 0},
      g d.1 * Real.exp (-(β * |(d.1 : ℝ)|))) = sosContourSecondActivity β := by
    unfold sosContourSecondActivity
    apply tsum_congr
    intro d
    simp [g, sq_abs]
  have hactENN : (∑' d : {d : ℤ // d ≠ 0}, ENNReal.ofReal
      (g d.1 * Real.exp (-(β * |(d.1 : ℝ)|)))) =
        ENNReal.ofReal (sosContourSecondActivity β) := by
    calc
      _ = ENNReal.ofReal (∑' d : {d : ℤ // d ≠ 0},
          g d.1 * Real.exp (-(β * |(d.1 : ℝ)|))) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun d => mul_nonneg (hg _) (Real.exp_nonneg _)) hsAct).symm
      _ = ENNReal.ofReal (sosContourSecondActivity β) := congrArg ENNReal.ofReal hactEq
  have hsWeight : Summable fun n : Site L → ℤ => sosHeightWeight L β n :=
    summable_sosPartition hL hβ
  have hsExpanded : Summable fun c : ZeroOuterSOSHeight L =>
      expandedSOSWeight L β c.1 := by
    apply (sosExtensionEquiv L).summable_iff.mp
    refine hsWeight.congr ?_
    intro n
    symm
    rw [sosHeightWeight_eq_prod_expandedEdges β n]
    rfl
  have hZENN : (∑' c : ZeroOuterSOSHeight L,
      ENNReal.ofReal (expandedSOSWeight L β c.1)) = ENNReal.ofReal (sosPartition L β) := by
    calc
      _ = ENNReal.ofReal (∑' c : ZeroOuterSOSHeight L, expandedSOSWeight L β c.1) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun c => Finset.prod_nonneg fun e _ => Real.exp_nonneg _) hsExpanded).symm
      _ = ENNReal.ofReal (sosPartition L β) := by
        rw [sosPartition_eq_expanded_tsum]
  have hZnonneg : 0 ≤ sosPartition L β := by
    unfold sosPartition
    exact tsum_nonneg fun n => (sosHeightWeight_pos L β n).le
  have hactivityBound := sosContourEvent_tsum β hβ.le Γ g hg
  have hENN : (∑' c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ},
      ENNReal.ofReal (sosContourSquareTerm β Γ c)) ≤
        ENNReal.ofReal (sosPartition L β * sosContourSecondActivity β ^ Γ.card) := by
    have hrealNonneg : 0 ≤ sosContourSecondActivity β ^ Γ.card := pow_nonneg hactNonneg _
    have hfactor := hactivityBound
    simp only [sosContourSquareTerm, g] at hfactor ⊢
    rw [hZENN, hactENN] at hfactor
    have hrewrite : ENNReal.ofReal (sosPartition L β) *
        ENNReal.ofReal (sosContourSecondActivity β) ^ Γ.card =
        ENNReal.ofReal (sosPartition L β * sosContourSecondActivity β ^ Γ.card) := by
      rw [← ENNReal.ofReal_pow hactNonneg, ← ENNReal.ofReal_mul hZnonneg]
    rw [hrewrite] at hfactor
    exact hfactor
  have hrealTotalNonneg : 0 ≤ sosPartition L β * sosContourSecondActivity β ^ Γ.card :=
    mul_nonneg hZnonneg (pow_nonneg hactNonneg _)
  have hENNneTop :
      (∑' c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ},
        ENNReal.ofReal (sosContourSquareTerm β Γ c)) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hENN ENNReal.ofReal_lt_top
  have htermToReal (c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ}) :
      (ENNReal.ofReal (sosContourSquareTerm β Γ c)).toReal = sosContourSquareTerm β Γ c :=
    ENNReal.toReal_ofReal (sosContourSquareTerm_nonneg β Γ c)
  have hsTerm : Summable (sosContourSquareTerm β Γ) := by
    have h := ENNReal.summable_toReal hENNneTop
    exact h.congr htermToReal
  have hsumToReal :
      (∑' c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ},
        ENNReal.ofReal (sosContourSquareTerm β Γ c)).toReal =
      ∑' c, sosContourSquareTerm β Γ c := by
    rw [ENNReal.tsum_toReal_eq (fun c => ENNReal.ofReal_ne_top)]
    apply tsum_congr
    exact htermToReal
  have hleReal := (ENNReal.toReal_le_toReal hENNneTop ENNReal.ofReal_ne_top).2 hENN
  rw [hsumToReal, ENNReal.toReal_ofReal hrealTotalNonneg] at hleReal
  exact ⟨hsTerm, hleReal⟩

private def sosContourSupportObservable {L : ℕ} (n : Site L → ℤ)
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) : ℝ :=
  ∑ e ∈ Γ, |(((squareFreeGraph (L + 2)).grad (extendHeight L n) e : ℤ) : ℝ)|

private theorem sosContourSupportObservable_sq_le {L : ℕ} (n : Site L → ℤ)
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (hΓ : ∀ e ∈ Γ, (squareFreeGraph (L + 2)).grad (extendHeight L n) e ≠ 0) :
    sosContourSupportObservable n Γ ^ 2 ≤
      (Γ.card : ℝ) ^ 2 *
        ∏ e ∈ Γ, |(((squareFreeGraph (L + 2)).grad (extendHeight L n) e : ℤ) : ℝ)| ^ 2 := by
  classical
  let a (e : Lattice2D.SquareFreeEdge (L + 2)) : ℝ :=
    |(((squareFreeGraph (L + 2)).grad (extendHeight L n) e : ℤ) : ℝ)|
  let P := ∏ e ∈ Γ, a e
  have haOne (e : Lattice2D.SquareFreeEdge (L + 2)) (he : e ∈ Γ) : 1 ≤ a e := by
    dsimp [a]
    have h := Int.one_le_abs (hΓ e he)
    exact_mod_cast h
  have hfactor (e : Lattice2D.SquareFreeEdge (L + 2)) (he : e ∈ Γ) : a e ≤ P := by
    have hrest : 1 ≤ ∏ f ∈ Γ.erase e, a f := by
      calc
        1 = ∏ f ∈ Γ.erase e, (1 : ℝ) := by simp
        _ ≤ ∏ f ∈ Γ.erase e, a f := by
          apply Finset.prod_le_prod₀
          · intro f hf
            norm_num
          · intro f hf
            exact haOne f (Finset.mem_of_mem_erase hf)
    have hprod := Finset.prod_erase_mul Γ a he
    dsimp [P]
    calc
      a e = 1 * a e := by ring
      _ ≤ (∏ f ∈ Γ.erase e, a f) * a e :=
        mul_le_mul_of_nonneg_right hrest (abs_nonneg _)
      _ = ∏ f ∈ Γ, a f := hprod
  have hsum : sosContourSupportObservable n Γ ≤ (Γ.card : ℝ) * P := by
    dsimp [sosContourSupportObservable, a, P]
    calc
      _ ≤ ∑ e ∈ Γ, P := Finset.sum_le_sum fun e he => hfactor e he
      _ = (Γ.card : ℝ) * P := by simp [nsmul_eq_mul]
  have hnonneg : 0 ≤ sosContourSupportObservable n Γ := by
    dsimp [sosContourSupportObservable]
    exact Finset.sum_nonneg fun e he => abs_nonneg _
  have hPnonneg : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro e he
    exact abs_nonneg _
  have hcardnonneg : 0 ≤ (Γ.card : ℝ) := Nat.cast_nonneg _
  calc
    sosContourSupportObservable n Γ ^ 2 ≤ ((Γ.card : ℝ) * P) ^ 2 :=
      (sq_le_sq₀ hnonneg (mul_nonneg hcardnonneg hPnonneg)).2 hsum
    _ = (Γ.card : ℝ) ^ 2 *
        ∏ e ∈ Γ, |(((squareFreeGraph (L + 2)).grad (extendHeight L n) e : ℤ) : ℝ)| ^ 2 := by
      rw [mul_pow, Finset.prod_pow]

private def sosPinnedContourEvent {L : ℕ} (n : Site L → ℤ)
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) : Prop :=
  (∀ e ∈ Γ, isInnerVertex L ((squareFreeGraph (L + 2)).src e) ∨
    isInnerVertex L ((squareFreeGraph (L + 2)).tgt e)) ∧
  squareFreePlaquetteSaturated ((squareFreeGraph (L + 2)).grad (extendHeight L n)) Γ ∧
  ∀ e ∈ Γ, (squareFreeGraph (L + 2)).grad (extendHeight L n) e ≠ 0

private theorem sosComponentSupport_pinnedContourEvent {L : ℕ}
    (n : Site L → ℤ)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent) :
    sosPinnedContourEvent n
      (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c) := by
  classical
  let η := (squareFreeGraph (L + 2)).grad (extendHeight L n)
  let Γ := clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2)) η c
  refine ⟨?_, sosComponentSupport_saturated η c, ?_⟩
  · intro e he
    by_contra hout
    push Not at hout
    have hmem := (mem_clockPeierlsComponentSupport_iff
      (clockPeierlsAdjacencyGraph (L + 2)) η c e).mp he
    have hzero := outerOuterGradient_zero n e hout.1 hout.2
    exact hmem.1 (by simpa [η] using hzero)
  · intro e he
    have hmem := (mem_clockPeierlsComponentSupport_iff
      (clockPeierlsAdjacencyGraph (L + 2)) η c e).mp he
    exact hmem.1

private def sosPinnedContourEventEquiv {L : ℕ}
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :
    {n : Site L → ℤ // sosPinnedContourEvent n Γ} ≃
      {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ} where
  toFun n := ⟨sosExtensionEquiv L n.1, by
    simpa [sosPinnedContourEvent, sosContourEvent, sosExtensionEquiv] using n.2⟩
  invFun c := by
    refine ⟨(sosExtensionEquiv L).symm c.1, ?_⟩
    change (∀ e ∈ Γ, isInnerVertex L ((squareFreeGraph (L + 2)).src e) ∨
        isInnerVertex L ((squareFreeGraph (L + 2)).tgt e)) ∧
      squareFreePlaquetteSaturated
        ((squareFreeGraph (L + 2)).grad
          (extendHeight L (restrictHeight c.1.1))) Γ ∧
      ∀ e ∈ Γ, (squareFreeGraph (L + 2)).grad
        (extendHeight L (restrictHeight c.1.1)) e ≠ 0
    rw [extendHeight_restrictHeight c.1.1 c.1.2]
    exact c.2
  left_inv n := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

private def sosPinnedContourSquareTerm {L : ℕ} (β : ℝ)
    (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) (n : Site L → ℤ) : ℝ :=
  if sosPinnedContourEvent n Γ then
    sosHeightWeight L β n * sosContourSupportObservable n Γ ^ 2
  else 0

private theorem sosPinnedContourSquareMoment_le {L : ℕ} (hL : 1 < L) {β : ℝ}
    (hβ : 0 < β) (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) :
    Summable (sosPinnedContourSquareTerm β Γ) ∧
      (∑' n, sosPinnedContourSquareTerm β Γ n) ≤
        sosPartition L β * (Γ.card : ℝ) ^ 2 *
          sosContourSecondActivity β ^ Γ.card := by
  classical
  let E := sosPinnedContourEventEquiv Γ
  have hfixed := sosContourSquareMoment_le hL hβ Γ
  let p : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ} → ℝ :=
    sosContourSquareTerm β Γ
  let o : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ} → ℝ := fun c =>
    expandedSOSWeight L β c.1.1 * sosContourSupportObservable
      (restrictHeight c.1.1) Γ ^ 2
  have hp : Summable p := by
    exact hfixed.1
  have hple : ∀ c, 0 ≤ o c ∧ o c ≤ (Γ.card : ℝ) ^ 2 * p c := by
    intro c
    let n : Site L → ℤ := restrictHeight c.1.1
    have hext : extendHeight L n = c.1.1 := by
      exact extendHeight_restrictHeight c.1.1 c.1.2
    have hΓ : ∀ e ∈ Γ, (squareFreeGraph (L + 2)).grad c.1.1 e ≠ 0 := c.2.2.2
    have hsquare := sosContourSupportObservable_sq_le n Γ (by simpa [hext] using hΓ)
    have hw : 0 ≤ expandedSOSWeight L β c.1.1 :=
      Finset.prod_nonneg fun e _ => Real.exp_nonneg _
    constructor
    · exact mul_nonneg hw (sq_nonneg _)
    · dsimp [o, p, n, sosContourSquareTerm]
      rw [hext] at hsquare
      have h := mul_le_mul_of_nonneg_left hsquare hw
      calc
        expandedSOSWeight L β c.1.1 * sosContourSupportObservable n Γ ^ 2 ≤
            expandedSOSWeight L β c.1.1 *
              ((Γ.card : ℝ) ^ 2 *
                ∏ e ∈ Γ, |(((squareFreeGraph (L + 2)).grad c.1.1 e : ℤ) : ℝ)| ^ 2) := h
        _ = (Γ.card : ℝ) ^ 2 *
            (expandedSOSWeight L β c.1.1 *
              ∏ e ∈ Γ, |(((squareFreeGraph (L + 2)).grad c.1.1 e : ℤ) : ℝ)| ^ 2) := by ring
  have ho : Summable o := by
    apply (hp.mul_left ((Γ.card : ℝ) ^ 2)).of_nonneg_of_le
    · intro c
      exact (hple c).1
    · intro c
      exact (hple c).2
  have hoBound : (∑' c, o c) ≤
      (Γ.card : ℝ) ^ 2 *
        (sosPartition L β * sosContourSecondActivity β ^ Γ.card) := by
    calc
      _ ≤ ∑' c, (Γ.card : ℝ) ^ 2 * p c :=
        ho.tsum_le_tsum (fun c => (hple c).2)
          ((hp.mul_left ((Γ.card : ℝ) ^ 2)))
      _ = (Γ.card : ℝ) ^ 2 * ∑' c, p c := by rw [tsum_mul_left]
      _ ≤ _ := by
        have hfixed' : (∑' c, p c) ≤
            sosPartition L β * sosContourSecondActivity β ^ Γ.card := by
          exact hfixed.2
        exact mul_le_mul_of_nonneg_left hfixed' (sq_nonneg _)
  have hsource : Summable fun n : {n : Site L → ℤ // sosPinnedContourEvent n Γ} =>
      sosHeightWeight L β n.1 * sosContourSupportObservable n.1 Γ ^ 2 := by
    have h := E.summable_iff.mpr ho
    refine h.congr ?_
    intro n
    change expandedSOSWeight L β (extendHeight L n.1) *
        sosContourSupportObservable (restrictHeight (extendHeight L n.1)) Γ ^ 2 =
      sosHeightWeight L β n.1 * sosContourSupportObservable n.1 Γ ^ 2
    rw [restrictHeight_extendHeight]
    unfold expandedSOSWeight
    rw [← sosHeightWeight_eq_prod_expandedEdges β n.1]
  have hsourceBound :
      (∑' n : {n : Site L → ℤ // sosPinnedContourEvent n Γ},
        sosHeightWeight L β n.1 * sosContourSupportObservable n.1 Γ ^ 2) ≤
        sosPartition L β * (Γ.card : ℝ) ^ 2 *
          sosContourSecondActivity β ^ Γ.card := by
    calc
      _ = ∑' n : {n : Site L → ℤ // sosPinnedContourEvent n Γ}, o (E n) := by
        apply tsum_congr
        intro n
        change sosHeightWeight L β n.1 * sosContourSupportObservable n.1 Γ ^ 2 =
          expandedSOSWeight L β (extendHeight L n.1) *
            sosContourSupportObservable (restrictHeight (extendHeight L n.1)) Γ ^ 2
        rw [restrictHeight_extendHeight]
        unfold expandedSOSWeight
        rw [sosHeightWeight_eq_prod_expandedEdges β n.1]
      _ = ∑' c : {c : ZeroOuterSOSHeight L // c ∈ sosContourEvent Γ}, o c := E.tsum_eq o
      _ ≤ _ := by
        calc
          _ ≤ (Γ.card : ℝ) ^ 2 *
              (sosPartition L β * sosContourSecondActivity β ^ Γ.card) := hoBound
          _ = _ := by ring_nf
  let S : Set (Site L → ℤ) := {n | sosPinnedContourEvent n Γ}
  let f : (Site L → ℤ) → ℝ := fun n =>
    sosHeightWeight L β n * sosContourSupportObservable n Γ ^ 2
  have hsubtype : Summable fun n : S => f n.1 := by
    change Summable (fun n : S => f n.1) at hsource
    exact hsource
  have hindicator : Summable (S.indicator f) :=
    (summable_subtype_iff_indicator (s := S) (f := f)).mp hsubtype
  have hterm : sosPinnedContourSquareTerm β Γ = S.indicator f := by
    funext n
    by_cases hn : sosPinnedContourEvent n Γ
    · simp [sosPinnedContourSquareTerm, S, f, hn, Set.indicator]
    · simp [sosPinnedContourSquareTerm, S, f, hn, Set.indicator]
  rw [hterm]
  have hsum : (∑' n, sosPinnedContourSquareTerm β Γ n) =
      ∑' n : {n : Site L → ℤ // sosPinnedContourEvent n Γ},
        sosHeightWeight L β n.1 * sosContourSupportObservable n.1 Γ ^ 2 := by
    calc
      _ = ∑' n, S.indicator f n := by rw [hterm]
      _ = ∑' n : S, f n.1 := (tsum_subtype S f).symm
  exact ⟨hindicator, by rw [← hterm, hsum]; exact hsourceBound⟩

/-- Connected edge animals of size `k` meeting the pinned prefix from `u` at a position allowed
by the frame-detour bound. -/
private def sosPathAnimalFamily {L : ℕ} (u : Site L) (k : ℕ) :
    Finset (Finset (Lattice2D.SquareFreeEdge (L + 2))) := by
  let R := sosPrefixLength u
  let y := u.2.val + 1
  let M := max y (L + 1 - y)
  exact ((Finset.univ : Finset (Fin R)).filter fun i =>
    clockPeierlsMinContourSize R M (i.val + 1) ≤ k).biUnion fun i =>
      FroehlichSpencer.Infra.animals (clockPeierlsAdjacencyGraph (L + 2))
        (sosPrefixPath u i) k

/-- The path-animal family at size `k` is bounded by the active-position count times the
degree-six lattice-animal count. -/
private theorem sosPathAnimalFamily_card_le {L : ℕ} (u : Site L) {k : ℕ} (hk : 1 ≤ k) :
    (sosPathAnimalFamily u k).card ≤ 4 * (k + 5) * 36 ^ k := by
  classical
  let R := sosPrefixLength u
  let y := u.2.val + 1
  let M := max y (L + 1 - y)
  let activeRoots := (Finset.univ : Finset (Fin R)).filter fun i =>
    clockPeierlsMinContourSize R M (i.val + 1) ≤ k
  let activePositions := (Finset.Icc 1 R).filter fun j =>
    clockPeierlsMinContourSize R M j ≤ k
  have hRM : R ≤ 2 * M := by
    have hy : y ≤ L := by dsimp [y]; omega
    have hleft : y ≤ M := Nat.le_max_left _ _
    have hright : L + 1 - y ≤ M := Nat.le_max_right _ _
    dsimp [R, sosPrefixLength]
    omega
  have hactivePositions : activePositions.card ≤ 4 * (k + 5) := by
    have h := sosActivePositions_card_le R M (k - 1) hRM
    have hmin : ∀ j, clockPeierlsMinContourSize R M j ≤ k ↔
        clockPeierlsMinContourSize R M j ≤ (k - 1) + 1 := by
      intro j
      rw [Nat.sub_add_cancel hk]
    have heq : activePositions = (Finset.Icc 1 R).filter fun j =>
        clockPeierlsMinContourSize R M j ≤ (k - 1) + 1 := by
      ext j
      simp only [activePositions, Finset.mem_filter]
      constructor
      · rintro ⟨hmem, hact⟩
        exact ⟨hmem, (hmin j).mp hact⟩
      · rintro ⟨hmem, hact⟩
        exact ⟨hmem, (hmin j).mpr hact⟩
    have hbase : activePositions.card ≤ 4 * ((k - 1) + 5) := by
      simpa [heq] using h
    calc
      activePositions.card ≤ 4 * ((k - 1) + 5) := hbase
      _ ≤ 4 * (k + 5) := by omega
  have hactiveRootsCard : activeRoots.card = activePositions.card := by
    have himage : activeRoots.image (fun i : Fin R => i.val + 1) = activePositions := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        activeRoots, activePositions, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨by omega, by omega⟩, hi⟩
      · rintro ⟨⟨hj1, hjR⟩, hjact⟩
        let i : Fin R := ⟨j - 1, by omega⟩
        have hji : i.val + 1 = j := by dsimp [i]; omega
        refine ⟨i, ⟨?_, ?_⟩⟩
        · rw [hji]
          exact hjact
        · exact hji
    calc
      activeRoots.card = (activeRoots.image (fun i : Fin R => i.val + 1)).card :=
        (Finset.card_image_of_injective activeRoots (fun a b h => Fin.ext (by simpa using h))).symm
      _ = activePositions.card := congrArg Finset.card himage
  have hactive : activeRoots.card ≤ 4 * (k + 5) := by
    rw [hactiveRootsCard]
    exact hactivePositions
  have hanimal (i : Fin R) (hi : i ∈ activeRoots) :
      (FroehlichSpencer.Infra.animals (clockPeierlsAdjacencyGraph (L + 2))
        (sosPrefixPath u i) k).card ≤ 36 ^ k := by
    have hbound := clockPeierlsAdjacencyGraph_card_animals_le (L + 2)
      (sosPrefixPath u i) k
    have hpow : 6 ^ (2 * (k - 1)) ≤ 36 ^ k := by
      calc
        6 ^ (2 * (k - 1)) ≤ 6 ^ (2 * k) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 36 ^ k := by rw [pow_mul]; norm_num
    exact hbound.trans hpow
  have hsum : (sosPathAnimalFamily u k).card ≤
      activeRoots.card * 36 ^ k := by
    calc
      _ ≤ ∑ i ∈ activeRoots,
          (FroehlichSpencer.Infra.animals (clockPeierlsAdjacencyGraph (L + 2))
            (sosPrefixPath u i) k).card := by
          change (activeRoots.biUnion fun i =>
            FroehlichSpencer.Infra.animals (clockPeierlsAdjacencyGraph (L + 2))
              (sosPrefixPath u i) k).card ≤ _
          exact Finset.card_biUnion_le
      _ ≤ ∑ i ∈ activeRoots, 36 ^ k := by
        apply Finset.sum_le_sum
        intro i hi
        exact hanimal i hi
      _ = activeRoots.card * 36 ^ k := by simp
  calc
    _ ≤ activeRoots.card * 36 ^ k := hsum
    _ ≤ 4 * (k + 5) * 36 ^ k := Nat.mul_le_mul_right _ hactive

/-- Two pinned prefixes have at most twice the number of possible active contour animals. -/
private theorem sosTwoPathAnimalFamily_card_le {L : ℕ} (u v : Site L) {k : ℕ}
    (hk : 1 ≤ k) :
    ((sosPathAnimalFamily u k) ∪ (sosPathAnimalFamily v k)).card ≤
      8 * (k + 5) * 36 ^ k := by
  calc
    _ ≤ (sosPathAnimalFamily u k).card + (sosPathAnimalFamily v k).card :=
      Finset.card_union_le _ _
    _ ≤ 4 * (k + 5) * 36 ^ k + 4 * (k + 5) * 36 ^ k :=
      Nat.add_le_add (sosPathAnimalFamily_card_le u hk)
        (sosPathAnimalFamily_card_le v hk)
    _ = 8 * (k + 5) * 36 ^ k := by ring

private theorem sosPathAnimalFamily_mem_card {L : ℕ} (u : Site L) {k : ℕ}
    {Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))}
    (hΓ : Γ ∈ sosPathAnimalFamily u k) : Γ.card = k := by
  classical
  unfold sosPathAnimalFamily at hΓ
  rcases Finset.mem_biUnion.mp hΓ with ⟨i, hi, hani⟩
  exact (FroehlichSpencer.Infra.mem_animals
    (clockPeierlsAdjacencyGraph (L + 2))).mp hani |>.2.1

private theorem sosComponentSupport_injective {L : ℕ}
    (η : Lattice2D.SquareFreeEdge (L + 2) → ℤ) :
    Function.Injective (clockPeierlsComponentSupport
      (clockPeierlsAdjacencyGraph (L + 2)) η) := by
  intro c d hcd
  let H := clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2)) η
  obtain ⟨x, hx⟩ := SimpleGraph.ConnectedComponent.nonempty_supp c
  have hxcomp : H.connectedComponentMk x = c := by
    simpa [H, SimpleGraph.ConnectedComponent.mem_supp_iff] using hx
  have hxmem : x.1 ∈ clockPeierlsComponentSupport
      (clockPeierlsAdjacencyGraph (L + 2)) η c := by
    rw [mem_clockPeierlsComponentSupport_iff_componentMk]
    exact hxcomp
  have hdmem : x.1 ∈ clockPeierlsComponentSupport
      (clockPeierlsAdjacencyGraph (L + 2)) η d := by
    rw [← hcd]
    exact hxmem
  have hdcomp := (mem_clockPeierlsComponentSupport_iff_componentMk
    (clockPeierlsAdjacencyGraph (L + 2)) η x.1 x.2 d).mp hdmem
  exact hxcomp.symm.trans hdcomp

private theorem sosComponentSupport_mem_pathAnimalFamily {L : ℕ} (u : Site L)
    (n : Site L → ℤ)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent)
    (hflux : clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath u) c ≠ 0) :
    clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c ∈
      sosPathAnimalFamily u
        (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
          ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c).card := by
  classical
  let η := (squareFreeGraph (L + 2)).grad (extendHeight L n)
  let G := clockPeierlsAdjacencyGraph (L + 2)
  let Γ := clockPeierlsComponentSupport G η c
  obtain ⟨i, hroot, hsize⟩ := sosActiveComponent_has_largeSupport u n c hflux
  have hanimal : Γ ∈ FroehlichSpencer.Infra.animals G (sosPrefixPath u i) Γ.card := by
    exact clockPeierlsComponentSupport_mem_animals G η c hroot
  have hrootIndex : i ∈ (Finset.univ : Finset (Fin (sosPrefixLength u))).filter
      (fun i => clockPeierlsMinContourSize (sosPrefixLength u)
        (max (u.2.val + 1) (L + 1 - (u.2.val + 1))) (i.val + 1) ≤ Γ.card) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsize
  unfold sosPathAnimalFamily
  exact Finset.mem_biUnion.mpr ⟨i, hrootIndex, hanimal⟩

/-- Finite index of all rooted connected contour candidates meeting either pinned prefix. -/
private def sosTwoPathAnimalPairs {L : ℕ} (u v : Site L) :
    Finset (ℕ × Finset (Lattice2D.SquareFreeEdge (L + 2))) :=
  (Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2)))).biUnion fun k =>
    ((sosPathAnimalFamily u k) ∪ (sosPathAnimalFamily v k)).image fun Γ => (k, Γ)

private theorem sosTwoPathAnimalPairs_sum {L : ℕ} (u v : Site L)
    (f : ℕ → Finset (Lattice2D.SquareFreeEdge (L + 2)) → ℝ) :
    (∑ p ∈ sosTwoPathAnimalPairs u v, f p.1 p.2) =
      ∑ k ∈ Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))),
        ∑ Γ ∈ (sosPathAnimalFamily u k ∪ sosPathAnimalFamily v k), f k Γ := by
  classical
  let I := Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2)))
  let A (k : ℕ) := sosPathAnimalFamily u k ∪ sosPathAnimalFamily v k
  let F (k : ℕ) := (A k).image fun Γ => (k, Γ)
  have hdisj : (↑I : Set ℕ).PairwiseDisjoint F := by
    intro k hk l hl hkl
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    rcases Finset.mem_image.mp hp with ⟨Γ, hΓ, rfl⟩
    rcases Finset.mem_image.mp hp' with ⟨Δ, hΔ, hEq⟩
    exact hkl (congrArg Prod.fst hEq.symm)
  change (∑ p ∈ I.biUnion F, f p.1 p.2) =
    ∑ k ∈ I, ∑ Γ ∈ A k, f k Γ
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro k hk
  have hinj : Set.InjOn (fun Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)) => (k, Γ))
      ↑(A k) := by
    intro Γ hΓ Δ hΔ hEq
    exact congrArg Prod.snd hEq
  change (∑ p ∈ (A k).image (fun Γ => (k, Γ)), f p.1 p.2) = _
  rw [Finset.sum_image hinj]

private def sosFirstAnimalSeriesTerm (k : ℕ) : ℝ :=
  8 * ((k : ℝ) + 5) * (9 / 25) ^ k

private theorem sosFirstAnimalSeries_summable :
    Summable sosFirstAnimalSeriesTerm := by
  have h0 : Summable fun k : ℕ => (9 / 25 : ℝ) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : Summable fun k : ℕ => (k : ℝ) * (9 / 25 : ℝ) ^ k := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1
      (by norm_num : ‖(9 / 25 : ℝ)‖ < 1))
  have h := (h1.add (h0.mul_left 5)).mul_left 8
  convert h using 1
  ext k
  simp [sosFirstAnimalSeriesTerm]
  ring

private def sosFirstAnimalConstant : ℝ := ∑' k : ℕ, sosFirstAnimalSeriesTerm k

private theorem sosFirstAnimalConstant_nonneg : 0 ≤ sosFirstAnimalConstant := by
  unfold sosFirstAnimalConstant
  exact tsum_nonneg fun k => by
    unfold sosFirstAnimalSeriesTerm
    positivity

private def sosSecondAnimalSeriesTerm (k : ℕ) : ℝ :=
  8 * ((k : ℝ) + 5) * (k : ℝ) ^ 2 * (9 / 250) ^ k

private theorem sosSecondAnimalSeries_summable :
    Summable sosSecondAnimalSeriesTerm := by
  have h2 : Summable fun k : ℕ => (k : ℝ) ^ 2 * (9 / 250 : ℝ) ^ k := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 2
      (by norm_num : ‖(9 / 250 : ℝ)‖ < 1))
  have h3 : Summable fun k : ℕ => (k : ℝ) ^ 3 * (9 / 250 : ℝ) ^ k := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 3
      (by norm_num : ‖(9 / 250 : ℝ)‖ < 1))
  have h := (h3.add (h2.mul_left 5)).mul_left 8
  convert h using 1
  ext k
  simp [sosSecondAnimalSeriesTerm]
  ring

private def sosSecondAnimalConstant : ℝ := ∑' k : ℕ, sosSecondAnimalSeriesTerm k

private theorem sosSecondAnimalConstant_nonneg : 0 ≤ sosSecondAnimalConstant := by
  unfold sosSecondAnimalConstant
  exact tsum_nonneg fun k => by
    unfold sosSecondAnimalSeriesTerm
    positivity

private theorem sosTwoPathAnimalPairs_secondMomentSum_le {L : ℕ} (hL : 1 < L)
    (u v : Site L) {β : ℝ} (hβ : 10000000 ≤ β) :
    (∑ p ∈ sosTwoPathAnimalPairs u v,
      (100 : ℝ) ^ p.1 * ∑' n, sosPinnedContourSquareTerm β p.2 n) ≤
      sosPartition L β * sosSecondAnimalConstant := by
  classical
  have hβpos : 0 < β := by linarith
  have hq := sosContourSecondActivity_le_small hβ
  have hq0 : 0 ≤ sosContourSecondActivity β := by
    unfold sosContourSecondActivity
    exact tsum_nonneg fun d => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hratio : 36 * 100 * sosContourSecondActivity β ≤ 9 / 250 := by
    nlinarith
  have hratioPow (k : ℕ) :
      (36 : ℝ) ^ k * (100 : ℝ) ^ k * sosContourSecondActivity β ^ k ≤
        (9 / 250 : ℝ) ^ k := by
    have heq : (36 : ℝ) ^ k * (100 : ℝ) ^ k * sosContourSecondActivity β ^ k =
        (36 * 100 * sosContourSecondActivity β) ^ k := by
      rw [← mul_pow, ← mul_pow]
    rw [heq]
    exact pow_le_pow_left₀ (by positivity) hratio k
  have hZnonneg : 0 ≤ sosPartition L β :=
    (sosPartition_pos_of_summable L β (summable_sosPartition hL hβpos)).le
  have hs := sosSecondAnimalSeries_summable
  have hfinite :
      (∑ k ∈ Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))),
        ∑ Γ ∈ (sosPathAnimalFamily u k ∪ sosPathAnimalFamily v k),
          (100 : ℝ) ^ k * ∑' n, sosPinnedContourSquareTerm β Γ n) ≤
        sosPartition L β *
          ∑ k ∈ Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))),
            sosSecondAnimalSeriesTerm k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    let A := sosPathAnimalFamily u k ∪ sosPathAnimalFamily v k
    have hkpos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hcard := sosTwoPathAnimalFamily_card_le u v hkpos
    have hcardReal : (A.card : ℝ) ≤ (8 * (k + 5) * 36 ^ k : ℕ) := by
      exact_mod_cast hcard
    have hterm (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) (hΓ : Γ ∈ A) :
        (100 : ℝ) ^ k * ∑' n, sosPinnedContourSquareTerm β Γ n ≤
          (100 : ℝ) ^ k *
            (sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k) := by
      have hsize : Γ.card = k := by
        rcases Finset.mem_union.mp hΓ with hU | hV
        · exact sosPathAnimalFamily_mem_card u hU
        · exact sosPathAnimalFamily_mem_card v hV
      have hmom := sosPinnedContourSquareMoment_le hL hβpos Γ
      have hbound : (∑' n, sosPinnedContourSquareTerm β Γ n) ≤
          sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k := by
        simpa [hsize] using hmom.2
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    have hsumTerm := Finset.sum_le_sum fun Γ hΓ => hterm Γ hΓ
    rw [Finset.sum_const, nsmul_eq_mul] at hsumTerm
    have hfacNonneg : 0 ≤
        (100 : ℝ) ^ k *
          (sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k) := by
      positivity
    have hcount : (A.card : ℝ) *
        ((100 : ℝ) ^ k *
          (sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k)) ≤
        (8 * (k + 5) * 36 ^ k : ℕ) *
          ((100 : ℝ) ^ k *
            (sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k)) :=
      mul_le_mul_of_nonneg_right hcardReal hfacNonneg
    have hconstantBound :
        (8 * (k + 5) * 36 ^ k : ℕ) *
          ((100 : ℝ) ^ k *
            (sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k)) ≤
        sosPartition L β * sosSecondAnimalSeriesTerm k := by
      push_cast
      have hpoly : 0 ≤ 8 * ((k : ℝ) + 5) * (k : ℝ) ^ 2 := by positivity
      calc
        8 * ((k : ℝ) + 5) * (36 : ℝ) ^ k *
            ((100 : ℝ) ^ k *
              (sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k)) =
            sosPartition L β *
              (8 * ((k : ℝ) + 5) * (k : ℝ) ^ 2) *
                ((36 : ℝ) ^ k * (100 : ℝ) ^ k * sosContourSecondActivity β ^ k) := by ring
        _ ≤ sosPartition L β *
            (8 * ((k : ℝ) + 5) * (k : ℝ) ^ 2) * (9 / 250 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (hratioPow k)
            (mul_nonneg hZnonneg hpoly)
        _ = sosPartition L β * sosSecondAnimalSeriesTerm k := by
          rw [sosSecondAnimalSeriesTerm]
          ring
    have hfinal :
        (∑ Γ ∈ A, (100 : ℝ) ^ k * ∑' n, sosPinnedContourSquareTerm β Γ n) ≤
          sosPartition L β * sosSecondAnimalSeriesTerm k := by
      calc
        _ ≤ (A.card : ℝ) *
            ((100 : ℝ) ^ k *
              (sosPartition L β * (k : ℝ) ^ 2 * sosContourSecondActivity β ^ k)) := by
              simpa [A] using hsumTerm
        _ ≤ _ := hcount.trans hconstantBound
    exact hfinal
  rw [sosTwoPathAnimalPairs_sum u v
    (fun k Γ => (100 : ℝ) ^ k * ∑' n, sosPinnedContourSquareTerm β Γ n)]
  calc
    _ ≤ sosPartition L β *
        ∑ k ∈ Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))),
          sosSecondAnimalSeriesTerm k := hfinite
    _ ≤ sosPartition L β * ∑' k : ℕ, sosSecondAnimalSeriesTerm k := by
      apply mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum
          (Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))))
          (fun k _ => by unfold sosSecondAnimalSeriesTerm; positivity))
      exact hZnonneg
    _ = sosPartition L β * sosSecondAnimalConstant := by rfl

private theorem sosTwoPathAnimalPairs_firstWeight_le {L : ℕ} (u v : Site L) :
    (∑ p ∈ sosTwoPathAnimalPairs u v, (1 / 100 : ℝ) ^ p.1) ≤
      sosFirstAnimalConstant := by
  classical
  have hs := sosFirstAnimalSeries_summable
  rw [sosTwoPathAnimalPairs_sum u v (fun k _ => (1 / 100 : ℝ) ^ k)]
  have hfinite :
      (∑ k ∈ Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))),
        ∑ Γ ∈ (sosPathAnimalFamily u k ∪ sosPathAnimalFamily v k),
          (1 / 100 : ℝ) ^ k) ≤
        ∑ k ∈ Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))),
          sosFirstAnimalSeriesTerm k := by
    apply Finset.sum_le_sum
    intro k hk
    have hkpos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hcard := sosTwoPathAnimalFamily_card_le u v hkpos
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcast : ((sosPathAnimalFamily u k ∪ sosPathAnimalFamily v k).card : ℝ) ≤
        (8 * (k + 5) * 36 ^ k : ℕ) := by exact_mod_cast hcard
    have hpow : (36 : ℝ) ^ k * (1 / 100 : ℝ) ^ k = (9 / 25 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num
    have hnonneg : 0 ≤ (1 / 100 : ℝ) ^ k := by positivity
    calc
      ((sosPathAnimalFamily u k ∪ sosPathAnimalFamily v k).card : ℝ) *
          (1 / 100 : ℝ) ^ k ≤
        (8 * (k + 5) * 36 ^ k : ℕ) * (1 / 100 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hcast hnonneg
      _ = sosFirstAnimalSeriesTerm k := by
        push_cast
        dsimp [sosFirstAnimalSeriesTerm]
        calc
          8 * ((k : ℝ) + 5) * (36 : ℝ) ^ k * (1 / 100 : ℝ) ^ k =
              8 * ((k : ℝ) + 5) * ((36 : ℝ) ^ k * (1 / 100 : ℝ) ^ k) := by ring
          _ = 8 * ((k : ℝ) + 5) * (9 / 25 : ℝ) ^ k := by rw [hpow]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))),
        sosFirstAnimalSeriesTerm k := hfinite
    _ ≤ ∑' k : ℕ, sosFirstAnimalSeriesTerm k :=
      hs.sum_le_tsum (Finset.Icc 1 (Fintype.card (Lattice2D.SquareFreeEdge (L + 2))))
        (fun k hk => by
          unfold sosFirstAnimalSeriesTerm
          positivity)
    _ = sosFirstAnimalConstant := rfl

private theorem sosComponentSupport_mem_twoPathAnimalPairs {L : ℕ} (u v : Site L)
    (n : Site L → ℤ)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent)
    (hflux : clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath u) c -
      clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath v) c ≠ 0) :
    ((clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c).card,
      clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
        ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c) ∈
        sosTwoPathAnimalPairs u v := by
  classical
  let η := (squareFreeGraph (L + 2)).grad (extendHeight L n)
  let G := clockPeierlsAdjacencyGraph (L + 2)
  let Γ := clockPeierlsComponentSupport G η c
  let Fu := clockPeierlsComponentFlux G η (sosPrefixPath u) c
  let Fv := clockPeierlsComponentFlux G η (sosPrefixPath v) c
  have hactive : Fu ≠ 0 ∨ Fv ≠ 0 := by
    by_contra h
    push Not at h
    change Fu - Fv ≠ 0 at hflux
    exact hflux (by rw [h.1, h.2]; rfl)
  have hfamily : Γ ∈ sosPathAnimalFamily u Γ.card ∪ sosPathAnimalFamily v Γ.card := by
    rcases hactive with hU | hV
    · exact Finset.mem_union_left _ (sosComponentSupport_mem_pathAnimalFamily u n c hU)
    · exact Finset.mem_union_right _ (sosComponentSupport_mem_pathAnimalFamily v n c hV)
  have hcard : Γ.card ≤ Fintype.card (Lattice2D.SquareFreeEdge (L + 2)) := by
    exact Finset.card_le_univ Γ
  have hcardpos : 1 ≤ Γ.card := by
    rcases hactive with hU | hV
    · obtain ⟨i, hi, hsize⟩ := sosActiveComponent_has_largeSupport u n c hU
      exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨sosPrefixPath u i, hi⟩)
    · obtain ⟨i, hi, hsize⟩ := sosActiveComponent_has_largeSupport v n c hV
      exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨sosPrefixPath v i, hi⟩)
  have hsizeRange := Finset.mem_Icc.mpr ⟨hcardpos, hcard⟩
  unfold sosTwoPathAnimalPairs
  exact Finset.mem_biUnion.mpr ⟨Γ.card,
    hsizeRange,
    Finset.mem_image.mpr ⟨Γ, hfamily, rfl⟩⟩

private def sosComponentFluxDifference {L : ℕ} (u v : Site L) (n : Site L → ℤ)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent) : ℤ :=
  clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath u) c -
    clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n)) (sosPrefixPath v) c

private def sosActiveComponents {L : ℕ} (u v : Site L) (n : Site L → ℤ) :
    Finset (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2))
      ((squareFreeGraph (L + 2)).grad (extendHeight L n))).ConnectedComponent :=
  Finset.univ.filter fun c => sosComponentFluxDifference u v n c ≠ 0

private theorem sosActiveComponentSum_le_twoPathCandidates {L : ℕ}
    (u v : Site L) (n : Site L → ℤ)
    (f : ℕ → Finset (Lattice2D.SquareFreeEdge (L + 2)) → ℝ)
    (hf : ∀ k Γ, 0 ≤ f k Γ) :
    (∑ c ∈ sosActiveComponents u v n,
      f (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
          ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c).card
        (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
          ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c)) ≤
      ∑ p ∈ sosTwoPathAnimalPairs u v, f p.1 p.2 := by
  classical
  let η := (squareFreeGraph (L + 2)).grad (extendHeight L n)
  let C := (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2)) η).ConnectedComponent
  let I := sosActiveComponents u v n
  let support (c : C) := clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2)) η c
  let pair (c : C) := ((support c).card, support c)
  have hinj : Function.Injective pair := by
    intro c d h
    apply sosComponentSupport_injective η
    exact congrArg Prod.snd h
  have himage : I.image pair ⊆ sosTwoPathAnimalPairs u v := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨c, hc, rfl⟩
    apply sosComponentSupport_mem_twoPathAnimalPairs u v n c
    exact (Finset.mem_filter.mp hc).2
  have hsumImage :
      (∑ c ∈ I, f (pair c).1 (pair c).2) =
        ∑ p ∈ I.image pair, f p.1 p.2 := by
    symm
    exact Finset.sum_image (fun c hc d hd h => hinj h)
  calc
    _ = ∑ c ∈ I, f (pair c).1 (pair c).2 := by rfl
    _ = ∑ p ∈ I.image pair, f p.1 p.2 := hsumImage
    _ ≤ ∑ p ∈ sosTwoPathAnimalPairs u v, f p.1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro p hp hnot
        exact hf p.1 p.2)

private def sosTwoPathContourObservableSum {L : ℕ} (u v : Site L)
    (n : Site L → ℤ) : ℝ :=
  ∑ p ∈ sosTwoPathAnimalPairs u v,
    (100 : ℝ) ^ p.1 *
      if sosPinnedContourEvent n p.2 then sosContourSupportObservable n p.2 ^ 2 else 0

private theorem sosActiveComponentSquareSum_le_candidates {L : ℕ}
    (u v : Site L) (n : Site L → ℤ) :
    (∑ c ∈ sosActiveComponents u v n,
      (100 : ℝ) ^ (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
          ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c).card *
        sosContourSupportObservable n
          (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
            ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c) ^ 2) ≤
      sosTwoPathContourObservableSum u v n := by
  classical
  let f (k : ℕ) (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2))) : ℝ :=
    (100 : ℝ) ^ k *
      if sosPinnedContourEvent n Γ then sosContourSupportObservable n Γ ^ 2 else 0
  have hf : ∀ k Γ, 0 ≤ f k Γ := by
    intro k Γ
    dsimp [f]
    split_ifs <;> positivity
  have hbase := sosActiveComponentSum_le_twoPathCandidates u v n f hf
  have hleft :
      (∑ c ∈ sosActiveComponents u v n,
        (100 : ℝ) ^ (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
            ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c).card *
          sosContourSupportObservable n
            (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
              ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c) ^ 2) =
        ∑ c ∈ sosActiveComponents u v n,
          f (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
              ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c).card
            (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2))
              ((squareFreeGraph (L + 2)).grad (extendHeight L n)) c) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hEvent := sosComponentSupport_pinnedContourEvent n c
    simp [f, hEvent]
  simpa [sosTwoPathContourObservableSum, f] using hleft.trans_le hbase

private theorem sosHeightDifference_sq_le_twoPathCandidates {L : ℕ}
    (u v : Site L) (n : Site L → ℤ) :
    ((n u : ℝ) - n v) ^ 2 ≤
      4 * sosFirstAnimalConstant * sosTwoPathContourObservableSum u v n := by
  classical
  let η := (squareFreeGraph (L + 2)).grad (extendHeight L n)
  let C := (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (L + 2)) η).ConnectedComponent
  let support (c : C) := clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (L + 2)) η c
  let fluxU (c : C) := clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
    η (sosPrefixPath u) c
  let fluxV (c : C) := clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (L + 2))
    η (sosPrefixPath v) c
  let fluxDiff (c : C) : ℤ := fluxU c - fluxV c
  let I := sosActiveComponents u v n
  let a (c : C) : ℝ := (1 / 10 : ℝ) ^ (support c).card
  let b (c : C) : ℝ := (10 : ℝ) ^ (support c).card *
    (2 * sosContourSupportObservable n (support c))
  have hprod (c : C) : a c * b c =
      2 * sosContourSupportObservable n (support c) := by
    dsimp [a, b]
    calc
      (1 / 10 : ℝ) ^ (support c).card *
          ((10 : ℝ) ^ (support c).card *
            (2 * sosContourSupportObservable n (support c))) =
          ((1 / 10 : ℝ) ^ (support c).card * (10 : ℝ) ^ (support c).card) *
            (2 * sosContourSupportObservable n (support c)) := by ring
      _ = (((1 / 10 : ℝ) * 10) ^ (support c).card) *
            (2 * sosContourSupportObservable n (support c)) := by rw [← mul_pow]
      _ = _ := by norm_num
  have hu := sosHeight_eq_neg_sum_componentFlux u n
  have hv := sosHeight_eq_neg_sum_componentFlux v n
  have huReal : (n u : ℝ) = -(∑ c : C, (fluxU c : ℝ)) := by
    exact_mod_cast hu
  have hvReal : (n v : ℝ) = -(∑ c : C, (fluxV c : ℝ)) := by
    exact_mod_cast hv
  have hdiff : (n u : ℝ) - n v = -(∑ c : C, ((fluxU c : ℝ) - (fluxV c : ℝ))) := by
    rw [huReal, hvReal, Finset.sum_sub_distrib]
    ring
  have hfilter : (∑ c : C, fluxDiff c) = ∑ c ∈ I, fluxDiff c := by
    change (∑ c : C, fluxDiff c) =
      ∑ c ∈ Finset.univ.filter (fun c : C => fluxDiff c ≠ 0), fluxDiff c
    exact (Finset.sum_filter_of_ne (s := Finset.univ) (f := fluxDiff)
      (p := fun c => fluxDiff c ≠ 0) (by intro c hc hne; exact hne)
      ).symm
  have hfilterReal :
      (∑ c : C, ((fluxU c : ℝ) - (fluxV c : ℝ))) =
        ∑ c ∈ I, ((fluxU c : ℝ) - (fluxV c : ℝ)) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hfilter
    simpa only [Int.cast_sum, Int.cast_sub, fluxDiff] using h
  have hdiffFiltered : (n u : ℝ) - n v =
      -(∑ c ∈ I, ((fluxU c : ℝ) - (fluxV c : ℝ))) := by
    rw [hdiff]
    rw [hfilterReal]
  have hR_u : sosPrefixLength u < L + 2 := by
    dsimp [sosPrefixLength]
    omega
  have hy_u : u.2.val + 1 < L + 2 := by omega
  have hR_v : sosPrefixLength v < L + 2 := by
    dsimp [sosPrefixLength]
    omega
  have hy_v : v.2.val + 1 < L + 2 := by omega
  have hfluxU (c : C) : |(fluxU c : ℝ)| ≤
      sosContourSupportObservable n (support c) := by
    have hi := componentFlux_abs_le_support hR_u hy_u η c
    have hiCast : ((|fluxU c| : ℤ) : ℝ) ≤
        ((∑ e ∈ support c, |η e| : ℤ) : ℝ) := by
      exact_mod_cast hi
    simpa [sosContourSupportObservable, support, η, Int.cast_abs, Int.cast_sum] using hiCast
  have hfluxV (c : C) : |(fluxV c : ℝ)| ≤
      sosContourSupportObservable n (support c) := by
    have hi := componentFlux_abs_le_support hR_v hy_v η c
    have hiCast : ((|fluxV c| : ℤ) : ℝ) ≤
        ((∑ e ∈ support c, |η e| : ℤ) : ℝ) := by
      exact_mod_cast hi
    simpa [sosContourSupportObservable, support, η, Int.cast_abs, Int.cast_sum] using hiCast
  have hfluxDiff (c : C) : |((fluxU c : ℝ) - (fluxV c : ℝ))| ≤
      2 * sosContourSupportObservable n (support c) := by
    calc
      _ ≤ |(fluxU c : ℝ)| + |(fluxV c : ℝ)| := abs_sub _ _
      _ ≤ sosContourSupportObservable n (support c) +
            sosContourSupportObservable n (support c) := add_le_add (hfluxU c) (hfluxV c)
      _ = _ := by ring
  have hsumBound : |(n u : ℝ) - n v| ≤
      ∑ c ∈ I, 2 * sosContourSupportObservable n (support c) := by
    rw [hdiffFiltered, abs_neg]
    calc
      |∑ c ∈ I, ((fluxU c : ℝ) - (fluxV c : ℝ))| ≤
          ∑ c ∈ I, |((fluxU c : ℝ) - (fluxV c : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun c hc => hfluxDiff c
  have hsumNonneg : 0 ≤ ∑ c ∈ I, 2 * sosContourSupportObservable n (support c) :=
    Finset.sum_nonneg fun c hc => mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun e he => abs_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I a b
  have hcs' :
      (∑ c ∈ I, 2 * sosContourSupportObservable n (support c)) ^ 2 ≤
        (∑ c ∈ I, a c ^ 2) * ∑ c ∈ I, b c ^ 2 := by
    simpa only [hprod] using hcs
  have hfirst : (∑ c ∈ I, a c ^ 2) ≤ sosFirstAnimalConstant := by
    have hsum := sosActiveComponentSum_le_twoPathCandidates u v n
      (fun k _ => (1 / 100 : ℝ) ^ k) (by intro k Γ; positivity)
    have htermEq : (∑ c ∈ I, a c ^ 2) =
        ∑ c ∈ I, (1 / 100 : ℝ) ^ (support c).card := by
      apply Finset.sum_congr rfl
      intro c hc
      dsimp [a]
      calc
        ((1 / 10 : ℝ) ^ (support c).card) ^ 2 =
            (1 / 10 : ℝ) ^ ((support c).card * 2) := by rw [← pow_mul]
        _ = ((1 / 10 : ℝ) ^ 2) ^ (support c).card := by
          rw [Nat.mul_comm, pow_mul]
        _ = (1 / 100 : ℝ) ^ (support c).card := by norm_num
    have hcandidate :
        (∑ c ∈ I, (1 / 100 : ℝ) ^ (support c).card) ≤
          ∑ p ∈ sosTwoPathAnimalPairs u v, (1 / 100 : ℝ) ^ p.1 := by
      simpa [I, support, sosActiveComponents, sosComponentFluxDifference] using hsum
    calc
      _ = ∑ c ∈ I, (1 / 100 : ℝ) ^ (support c).card := htermEq
      _ ≤ _ := hcandidate
      _ ≤ sosFirstAnimalConstant := sosTwoPathAnimalPairs_firstWeight_le u v
  have hsecond : (∑ c ∈ I, b c ^ 2) ≤
      4 * sosTwoPathContourObservableSum u v n := by
    have htermEq : (∑ c ∈ I, b c ^ 2) =
        4 * ∑ c ∈ I, (100 : ℝ) ^ (support c).card *
          sosContourSupportObservable n (support c) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      dsimp [b]
      have h10 : ((10 : ℝ) ^ (support c).card) ^ 2 = (100 : ℝ) ^ (support c).card := by
        calc
          ((10 : ℝ) ^ (support c).card) ^ 2 =
              (10 : ℝ) ^ ((support c).card * 2) := by rw [← pow_mul]
          _ = ((10 : ℝ) ^ 2) ^ (support c).card := by
            rw [Nat.mul_comm, pow_mul]
          _ = (100 : ℝ) ^ (support c).card := by norm_num
      rw [mul_pow, h10]
      ring
    calc
      _ = 4 * ∑ c ∈ I, (100 : ℝ) ^ (support c).card *
            sosContourSupportObservable n (support c) ^ 2 := htermEq
      _ ≤ 4 * sosTwoPathContourObservableSum u v n := by
        apply mul_le_mul_of_nonneg_left
          (sosActiveComponentSquareSum_le_candidates u v n)
        norm_num
  have hXnonneg : 0 ≤ |(n u : ℝ) - n v| := abs_nonneg _
  have hXsq : ((n u : ℝ) - n v) ^ 2 ≤
      (∑ c ∈ I, 2 * sosContourSupportObservable n (support c)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hXnonneg hsumNonneg).2 hsumBound
  have hprodBound :
      (∑ c ∈ I, a c ^ 2) * ∑ c ∈ I, b c ^ 2 ≤
        sosFirstAnimalConstant * (4 * sosTwoPathContourObservableSum u v n) :=
    mul_le_mul hfirst hsecond (Finset.sum_nonneg fun c hc => sq_nonneg _)
      (sosFirstAnimalConstant_nonneg)
  calc
    ((n u : ℝ) - n v) ^ 2 ≤
        (∑ c ∈ I, 2 * sosContourSupportObservable n (support c)) ^ 2 := hXsq
    _ ≤ (∑ c ∈ I, a c ^ 2) * ∑ c ∈ I, b c ^ 2 := hcs'
    _ ≤ sosFirstAnimalConstant * (4 * sosTwoPathContourObservableSum u v n) := hprodBound
    _ = 4 * sosFirstAnimalConstant * sosTwoPathContourObservableSum u v n := by ring

private def sosTwoPathCandidateWeightedTerm {L : ℕ} (β : ℝ)
    (p : ℕ × Finset (Lattice2D.SquareFreeEdge (L + 2))) (n : Site L → ℤ) : ℝ :=
  (100 : ℝ) ^ p.1 * sosPinnedContourSquareTerm β p.2 n

/-- The SOS variance is bounded uniformly in the pinned box and both sites at sufficiently large
inverse temperature. The numerator is the genuine summable expectation established above. -/
theorem sos_lowTemperature_variance_bounded :
    ∃ β₁ C : ℝ, 0 < β₁ ∧ 0 < C ∧
      ∀ β : ℝ, β₁ ≤ β → ∀ L : ℕ, ∀ u v : Site L,
        sosVariance L β u v ≤ C := by
  let β₁ : ℝ := 10000000
  let C : ℝ := 4 * sosFirstAnimalConstant * sosSecondAnimalConstant + 1
  have hA0 := sosFirstAnimalConstant_nonneg
  have hB0 := sosSecondAnimalConstant_nonneg
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨β₁, C, by norm_num [β₁], hC, ?_⟩
  intro β hβ L u v
  have hβpos : 0 < β := by dsimp [β₁] at hβ; linarith
  by_cases hL : 1 < L
  · classical
    let P := sosTwoPathAnimalPairs u v
    let t (p : ℕ × Finset (Lattice2D.SquareFreeEdge (L + 2)))
        (n : Site L → ℤ) := sosTwoPathCandidateWeightedTerm β p n
    have hterms (p : ℕ × Finset (Lattice2D.SquareFreeEdge (L + 2))) :
        Summable (fun n : Site L → ℤ => t p n) := by
      have h := sosPinnedContourSquareMoment_le hL hβpos p.2
      simpa [t, sosTwoPathCandidateWeightedTerm] using
        h.1.mul_left ((100 : ℝ) ^ p.1)
    have hCandidateSummable : Summable fun n : Site L → ℤ => ∑ p ∈ P, t p n := by
      induction P using Finset.induction_on with
      | empty => simp
      | @insert p P hp ih =>
        simp only [Finset.sum_insert hp]
        exact (hterms p).add ih
    have hExchange :
      (∑' n : Site L → ℤ, ∑ p ∈ P, t p n) =
        ∑ p ∈ P, ∑' n : Site L → ℤ, t p n :=
      Summable.tsum_finsetSum (fun p hp => hterms p)
    have hCandidateBound :
        (∑' n : Site L → ℤ, ∑ p ∈ P, t p n) ≤
          sosPartition L β * sosSecondAnimalConstant := by
      calc
        _ = ∑ p ∈ P, ∑' n : Site L → ℤ, t p n := hExchange
        _ = ∑ p ∈ P,
              (100 : ℝ) ^ p.1 * ∑' n : Site L → ℤ,
                sosPinnedContourSquareTerm β p.2 n := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [t, sosTwoPathCandidateWeightedTerm, tsum_mul_left]
        _ ≤ sosPartition L β * sosSecondAnimalConstant := by
          simpa [P, t, sosTwoPathCandidateWeightedTerm] using
            sosTwoPathAnimalPairs_secondMomentSum_le hL u v hβ
    have hobsEq (n : Site L → ℤ) :
        sosHeightWeight L β n * sosTwoPathContourObservableSum u v n =
          ∑ p ∈ P, t p n := by
      unfold sosTwoPathContourObservableSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases he : sosPinnedContourEvent n p.2
      · simp [t, sosTwoPathCandidateWeightedTerm, sosPinnedContourSquareTerm, he]
        ring
      · simp [t, sosTwoPathCandidateWeightedTerm, sosPinnedContourSquareTerm, he]
    have hnum := summable_sosSecondMoment hL hβpos u v
    have hcoeff : 0 ≤ 4 * sosFirstAnimalConstant := by positivity
    have hpoint (n : Site L → ℤ) :
        (((n u : ℝ) - n v) ^ 2) * sosHeightWeight L β n ≤
          4 * sosFirstAnimalConstant * ∑ p ∈ P, t p n := by
      have h := sosHeightDifference_sq_le_twoPathCandidates u v n
      have hw := (sosHeightWeight_pos L β n).le
      calc
        _ ≤ (4 * sosFirstAnimalConstant *
              sosTwoPathContourObservableSum u v n) * sosHeightWeight L β n :=
            mul_le_mul_of_nonneg_right h hw
        _ = 4 * sosFirstAnimalConstant *
              (sosHeightWeight L β n * sosTwoPathContourObservableSum u v n) := by ring
        _ = _ := by rw [hobsEq n]
    have hnumBound :
        (∑' n : Site L → ℤ, (((n u : ℝ) - n v) ^ 2) * sosHeightWeight L β n) ≤
          4 * sosFirstAnimalConstant *
            (sosPartition L β * sosSecondAnimalConstant) := by
      calc
        _ ≤ ∑' n : Site L → ℤ,
              4 * sosFirstAnimalConstant * (∑ p ∈ P, t p n) :=
            hnum.tsum_le_tsum hpoint (hCandidateSummable.mul_left _)
        _ = 4 * sosFirstAnimalConstant *
              (∑' n : Site L → ℤ, ∑ p ∈ P, t p n) := by rw [tsum_mul_left]
        _ ≤ 4 * sosFirstAnimalConstant *
              (sosPartition L β * sosSecondAnimalConstant) :=
            mul_le_mul_of_nonneg_left hCandidateBound hcoeff
    have hZsum := summable_sosPartition hL hβpos
    have hZpos := sosPartition_pos_of_summable L β hZsum
    have hZnonneg : 0 ≤ sosPartition L β := hZpos.le
    have hnumOverZ : sosVariance L β u v ≤ C := by
      unfold sosVariance
      apply (div_le_iff₀ hZpos).2
      calc
        _ ≤ (4 * sosFirstAnimalConstant * sosSecondAnimalConstant) *
              sosPartition L β := by
                calc
                  _ ≤ 4 * sosFirstAnimalConstant *
                      (sosPartition L β * sosSecondAnimalConstant) := hnumBound
                  _ = _ := by ring
        _ ≤ C * sosPartition L β := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [C]
            linarith
          · exact hZnonneg
    exact hnumOverZ
  · have hLpos : 0 < L := by
      have huL := u.1.isLt
      omega
    have hLone : L = 1 := by omega
    subst L
    have huv : u = v := Subsingleton.elim _ _
    simp [sosVariance, huv, hC.le]

/-- The small-temperature divergence from Theorem 7.3 and the high-temperature uniform Peierls
bound together give both sides of the SOS roughening transition. -/
theorem sos_roughening_transition :
    (∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧ Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β ≤ β₀ → 0 < β' β ∧
        ∀ K : ℝ, ∃ L : ℕ, ∃ u v : Site L,
          L₀ ≤ L ∧ linfDist u v ≤ siteBoundaryDepth u ∧ K < sosVariance L β u v) ∧
    (∃ β₁ C : ℝ, 0 < β₁ ∧ 0 < C ∧
      ∀ β : ℝ, β₁ ≤ β → ∀ L : ℕ, ∀ u v : Site L,
        sosVariance L β u v ≤ C) := by
  exact ⟨sos_smallTemperature_variance_unbounded, sos_lowTemperature_variance_bounded⟩

end FroehlichSpencer.BKT.SOS.Peierls

end
