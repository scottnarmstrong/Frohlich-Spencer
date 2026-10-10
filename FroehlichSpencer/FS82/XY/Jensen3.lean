/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Renormalization3
public import FroehlichSpencer.FS82.XY.Poisson3
public import FroehlichSpencer.FS82.Moment.SourceJensen
public import FroehlichSpencer.FS82.Moment.PositivePacking

/-!
# FS82 three-dimensional Jensen estimates

The source Jensen curvature is exponentially small when the renormalized
activity has an exponential envelope. This is the scalar estimate used by
the three-dimensional packing argument.
-/

public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.Expansion3
open FroehlichSpencer.FS82.XY.Renormalization3

theorem xy3_lineage_currentNear_separated {B : Dual3Box}
    {q : Dual3Links B → ℤ} {s : CurrentState B}
    (hs : IsSeparatedCurrentState q s)
    {t u : ExpansionLineage B} (ht : t ∈ s) (hu : u ∈ s) (htu : t ≠ u)
    (e f : Dual3Links B)
    (he : lineageCurrent q t e ≠ 0)
    (hf : lineageCurrent q u f ≠ 0) :
    ¬ Expansion3.currentNear e f := by
  apply hs t ht u hu htu e ?_ f ?_
  · simp [currentSupport, he]
  · simp [currentSupport, hf]

/-- An exponentially small activity is in the range of the corrected source
bound `γ(z) ≤ 5z`, once its exponential rate clears `log 2`. -/
theorem sourceJensenGamma_le_five_exp_of_logEnvelope
    {a : ℝ} {L : ℕ} {z : ℝ}
    (hlog : Real.log 2 ≤ a * (L : ℝ))
    (hz0 : 0 ≤ z)
    (hz : z ≤ Real.exp (-(a * (L : ℝ)))) :
    sourceJensenGamma z ≤ 5 * Real.exp (-(a * (L : ℝ))) := by
  have hhalf : Real.exp (-(a * (L : ℝ))) ≤ 1 / 2 := by
    calc
      Real.exp (-(a * (L : ℝ))) ≤ Real.exp (-(Real.log 2)) :=
        Real.exp_le_exp.mpr (neg_le_neg hlog)
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hgamma := sourceJensenGamma_le_five_mul hz0 (hz.trans hhalf)
  calc
    sourceJensenGamma z ≤ 5 * z := hgamma
    _ ≤ 5 * Real.exp (-(a * (L : ℝ))) :=
      mul_le_mul_of_nonneg_left hz (by norm_num)


/-! ### Closedness of separated components

If the vertex coboundary stencil at each vertex meets the support of at most
one of two summands, closedness of their sum forces closedness of each
summand. The premise is stated directly on the stencil.
-/

private theorem xy3_inner_zero_of_local_support {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u v : EuclideanSpace ℝ ι)
    (h : ∀ i, u i = 0 ∨ v i = 0) : inner ℝ u v = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rcases h i with hu | hv
  · simp [RCLike.inner_apply, hu]
  · simp [RCLike.inner_apply, hv]

/-- If two link currents have disjoint incidence at each vertex, and their sum
is co-closed, then each summand is co-closed. This is the valid closure rule
for a terminal separated family; it does not apply to arbitrary intermediate
lineages. -/
theorem xy3_coClosed_split_of_vertexStencil_separation {B : Dual3Box}
    (q r : EuclideanSpace ℝ (Dual3Links B))
    (hsum : q + r ∈ coClosed (dual3ExactOneComplex B))
    (hlocal : ∀ v : Dual3Vertices B,
      (∀ e, ((dual3ExactOneComplex B).d₀
        (EuclideanSpace.single v (1 : ℝ))) e ≠ 0 → q e = 0) ∨
      (∀ e, ((dual3ExactOneComplex B).d₀
        (EuclideanSpace.single v (1 : ℝ))) e ≠ 0 → r e = 0)) :
    q ∈ coClosed (dual3ExactOneComplex B) ∧
      r ∈ coClosed (dual3ExactOneComplex B) := by
  have hsum' : (dual3ExactOneComplex B).d₀.adjoint (q + r) = 0 := hsum
  constructor
  · change (dual3ExactOneComplex B).d₀.adjoint q = 0
    ext v
    have htest : inner ℝ
        ((dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ)))
        (q + r) = 0 := by
      calc
        _ = inner ℝ (EuclideanSpace.single v (1 : ℝ))
            ((dual3ExactOneComplex B).d₀.adjoint (q + r)) :=
          (LinearMap.adjoint_inner_right (dual3ExactOneComplex B).d₀
            (EuclideanSpace.single v (1 : ℝ)) (q + r)).symm
        _ = 0 := by rw [hsum']; simp
    rcases hlocal v with hq | hr
    · have hqinner := xy3_inner_zero_of_local_support
        ((dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ))) q
        (fun e => by
          by_cases he : (dual3ExactOneComplex B).d₀
              (EuclideanSpace.single v (1 : ℝ)) e = 0
          · exact Or.inl he
          · exact Or.inr (hq e he))
      have hcoord := LinearMap.adjoint_inner_right
        (dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ)) q
      have hsingle : inner ℝ (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint q) =
          ((dual3ExactOneComplex B).d₀.adjoint q) v := by
        rw [EuclideanSpace.inner_single_left]
        simp
      have hzero : inner ℝ
          (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint q) = 0 := by
        rw [hcoord]
        exact hqinner
      rw [hsingle] at hzero
      simpa using hzero
    · have hrinner := xy3_inner_zero_of_local_support
        ((dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ))) r
        (fun e => by
          by_cases he : (dual3ExactOneComplex B).d₀
              (EuclideanSpace.single v (1 : ℝ)) e = 0
          · exact Or.inl he
          · exact Or.inr (hr e he))
      have hsumInner := htest
      rw [inner_add_right] at hsumInner
      rw [hrinner, add_zero] at hsumInner
      have hcoord := LinearMap.adjoint_inner_right
        (dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ)) q
      have hsingle : inner ℝ (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint q) =
          ((dual3ExactOneComplex B).d₀.adjoint q) v := by
        rw [EuclideanSpace.inner_single_left]
        simp
      have hzero : inner ℝ
          (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint q) = 0 := by
        rw [hcoord]
        exact hsumInner
      rw [hsingle] at hzero
      simpa using hzero
  · change (dual3ExactOneComplex B).d₀.adjoint r = 0
    ext v
    have htest : inner ℝ
        ((dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ)))
        (q + r) = 0 := by
      calc
        _ = inner ℝ (EuclideanSpace.single v (1 : ℝ))
            ((dual3ExactOneComplex B).d₀.adjoint (q + r)) :=
          (LinearMap.adjoint_inner_right (dual3ExactOneComplex B).d₀
            (EuclideanSpace.single v (1 : ℝ)) (q + r)).symm
        _ = 0 := by rw [hsum']; simp
    rcases hlocal v with hq | hr
    · have hqinner := xy3_inner_zero_of_local_support
        ((dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ))) q
        (fun e => by
          by_cases he : (dual3ExactOneComplex B).d₀
              (EuclideanSpace.single v (1 : ℝ)) e = 0
          · exact Or.inl he
          · exact Or.inr (hq e he))
      have hsumInner := htest
      rw [inner_add_right] at hsumInner
      rw [hqinner, zero_add] at hsumInner
      have hcoord := LinearMap.adjoint_inner_right
        (dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ)) r
      have hsingle : inner ℝ (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint r) =
          ((dual3ExactOneComplex B).d₀.adjoint r) v := by
        rw [EuclideanSpace.inner_single_left]
        simp
      have hzero : inner ℝ
          (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint r) = 0 := by
        rw [hcoord]
        exact hsumInner
      rw [hsingle] at hzero
      simpa using hzero
    · have hrinner := xy3_inner_zero_of_local_support
        ((dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ))) r
        (fun e => by
          by_cases he : (dual3ExactOneComplex B).d₀
              (EuclideanSpace.single v (1 : ℝ)) e = 0
          · exact Or.inl he
          · exact Or.inr (hr e he))
      have hcoord := LinearMap.adjoint_inner_right
        (dual3ExactOneComplex B).d₀ (EuclideanSpace.single v (1 : ℝ)) r
      have hsingle : inner ℝ (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint r) =
          ((dual3ExactOneComplex B).d₀.adjoint r) v := by
        rw [EuclideanSpace.inner_single_left]
        simp
      have hzero : inner ℝ
          (EuclideanSpace.single v (1 : ℝ))
          ((dual3ExactOneComplex B).d₀.adjoint r) = 0 := by
        rw [hcoord]
        exact hrinner
      rw [hsingle] at hzero
      simpa using hzero

/-- A finite separated sum of currents can be filtered componentwise by
co-closedness, provided the supports are separated on each vertex stencil. -/
theorem xy3_each_coClosed_of_pairwiseStencilSeparated {B : Dual3Box}
    {I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) (q : I → EuclideanSpace ℝ (Dual3Links B))
    (hsum : (∑ i ∈ T, q i) ∈ coClosed (dual3ExactOneComplex B))
    (hsep : ∀ v : Dual3Vertices B, ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      (∀ e, ((dual3ExactOneComplex B).d₀
        (EuclideanSpace.single v (1 : ℝ))) e ≠ 0 → q i e = 0) ∨
      (∀ e, ((dual3ExactOneComplex B).d₀
        (EuclideanSpace.single v (1 : ℝ))) e ≠ 0 → q j e = 0)) :
    ∀ i ∈ T, q i ∈ coClosed (dual3ExactOneComplex B) := by
  intro i hi
  let r : EuclideanSpace ℝ (Dual3Links B) := ∑ j ∈ T.erase i, q j
  have hsumErase := Finset.sum_erase_add T q hi
  have hsumEq : q i + r = ∑ j ∈ T, q j := by
    dsimp [r]
    rw [add_comm]
    exact hsumErase
  have hclosed : q i + r ∈ coClosed (dual3ExactOneComplex B) := by
    rw [hsumEq]
    exact hsum
  have hlocal : ∀ v : Dual3Vertices B,
      (∀ e, ((dual3ExactOneComplex B).d₀
        (EuclideanSpace.single v (1 : ℝ))) e ≠ 0 → q i e = 0) ∨
      (∀ e, ((dual3ExactOneComplex B).d₀
        (EuclideanSpace.single v (1 : ℝ))) e ≠ 0 → r e = 0) := by
    intro v
    by_cases hiZero : ∀ e, ((dual3ExactOneComplex B).d₀
        (EuclideanSpace.single v (1 : ℝ))) e ≠ 0 → q i e = 0
    · exact Or.inl hiZero
    · push Not at hiZero
      obtain ⟨e₀, he₀, hiNe⟩ := hiZero
      right
      intro e he
      change (∑ j ∈ T.erase i, q j) e = 0
      rw [WithLp.ofLp_sum, Finset.sum_apply e]
      apply Finset.sum_eq_zero
      intro j hj
      obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
      have hsepij := hsep v i hi j hjT hji.symm
      rcases hsepij with hqi | hqj
      · exact (hiNe (hqi e₀ he₀)).elim
      · exact hqj e he
  exact (xy3_coClosed_split_of_vertexStencil_separation
    (q i) r hclosed hlocal).1

/-!
`currentNear` is defined by neighboring link base points (or a shared
plaquette).

A vertex coboundary stencil consists of the six links incident
to that vertex.

The coordinate argument below proves that any two links in
one such stencil are `currentNear`; hence a separated family has at most one
member meeting each stencil.
-/

private theorem xy3_vertexCoordinate_left {B : Dual3Box}
    (v : Dual3Vertices B) (i : Fin 3) :
    ∃ x : Fin (B i), v.1 i = Sum.inl x := by
  cases hc : v.1 i with
  | inl x => exact ⟨x, rfl⟩
  | inr x =>
    have hi : i ∈ dualCellAxes v.1 := by simp [dualCellAxes, hc]
    have hcard : (dualCellAxes v.1).card = 0 := by
      simpa [dualCellDegree] using v.2
    have hpos : 0 < (dualCellAxes v.1).card := Finset.card_pos.mpr ⟨i, hi⟩
    omega

private noncomputable def xy3_vertexCoordinate
    {B : Dual3Box} (v : Dual3Vertices B) (i : Fin 3) : ℕ :=
  (Classical.choose (xy3_vertexCoordinate_left v i)).val + 1

private theorem xy3_vertexCoordinate_eq {B : Dual3Box}
    (v : Dual3Vertices B) (i : Fin 3) (x : Fin (B i))
    (hx : v.1 i = Sum.inl x) :
    xy3_vertexCoordinate v i = x.val + 1 := by
  have hchoose : v.1 i = Sum.inl (Classical.choose (xy3_vertexCoordinate_left v i)) :=
    Classical.choose_spec (xy3_vertexCoordinate_left v i)
  have hxval : Classical.choose (xy3_vertexCoordinate_left v i) = x := by
    have h := congrArg (fun c : DualCoord B i => match c with
      | Sum.inl y => y.val
      | Sum.inr _ => 0) (hchoose.symm.trans hx)
    exact Fin.ext (by simpa using h)
  simp [xy3_vertexCoordinate, hxval]

theorem xy3_d0_single_stencil {B : Dual3Box}
    (v : Dual3Vertices B) (e : Dual3Links B) :
    dual3D₀ (EuclideanSpace.single v 1) e =
      dualExteriorDifferenceStencilBasis v.1 (dual3LinksEmbedding e) := by
  have hv : dual3VerticesToChain (EuclideanSpace.single v (1 : ℝ)) =
      Finsupp.single v.1 1 := by
    change dual3EmbedSubtype dual3VerticesEmbedding
      (euclideanToFinsupp (EuclideanSpace.single v (1 : ℝ))) = _
    rw [euclideanToFinsupp_single, dual3EmbedSubtype_apply_single]
    rfl
  have heval := congrArg (fun c : DualRealChain 3 B =>
      c (dual3LinksEmbedding e))
    (dual3D₀_embed_eq_derivative (EuclideanSpace.single v (1 : ℝ)))
  rw [hv, dualExteriorDifference_basis_eq_coordinateStencil] at heval
  have hleft : dual3LinksToChain
      (dual3D₀ (EuclideanSpace.single v (1 : ℝ)))
      (dual3LinksEmbedding e) = dual3D₀ (EuclideanSpace.single v (1 : ℝ)) e := by
    change dual3EmbedSubtype dual3LinksEmbedding
      (euclideanToFinsupp (dual3D₀ (EuclideanSpace.single v (1 : ℝ))))
      (dual3LinksEmbedding e) = _
    rw [dual3EmbedSubtype_apply_at_image]
    rfl
  rw [hleft] at heval
  exact heval

private theorem xy3_stencil_nonzero_has_face {B : Dual3Box}
    (v : Dual3Vertices B) (e : Dual3Links B)
    (h : dual3D₀ (EuclideanSpace.single v 1) e ≠ 0) :
    ∃ i : Fin 3, ∃ x : Fin (B i), v.1 i = Sum.inl x ∧
      (dualUpperFace v.1 i x = e.1 ∨ dualLowerFace v.1 i x = e.1) := by
  by_contra hfaces
  apply h
  have hs := xy3_d0_single_stencil v e
  rw [dualExteriorDifferenceStencilBasis] at hs
  rw [← Finsupp.lapply_apply (M := ℝ) (R := ℝ) (a := dual3LinksEmbedding e)] at hs
  rw [map_sum (Finsupp.lapply (R := ℝ) (dual3LinksEmbedding e))] at hs
  rw [hs]
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨x, hx⟩ := xy3_vertexCoordinate_left v i
  have hu : dualUpperFace v.1 i x ≠ e.1 := by
    intro heq
    apply hfaces
    exact ⟨i, x, hx, Or.inl heq⟩
  have hl : dualLowerFace v.1 i x ≠ e.1 := by
    intro heq
    apply hfaces
    exact ⟨i, x, hx, Or.inr heq⟩
  simp [Finsupp.lapply_apply, hx, hu, hl, dual3LinksEmbedding]

private theorem xy3_incidentLink_baseCoordinate {B : Dual3Box}
    (v : Dual3Vertices B) (e : Dual3Links B) (i : Fin 3)
    (x : Fin (B i)) (hx : v.1 i = Sum.inl x)
    (hface : dualUpperFace v.1 i x = e.1 ∨
      dualLowerFace v.1 i x = e.1) (k : Fin 3) :
    Renormalization3.linkBaseCoordinate e k = xy3_vertexCoordinate v k ∨
      Renormalization3.linkBaseCoordinate e k + 1 = xy3_vertexCoordinate v k := by
  obtain ⟨xk, hxk⟩ := xy3_vertexCoordinate_left v k
  have hvcoord := xy3_vertexCoordinate_eq v k xk hxk
  rw [hvcoord]
  by_cases hki : k = i
  · subst k
    have hxxk : x = xk := by
      have h := hx.symm.trans hxk
      injection h
    subst xk
    rcases hface with hu | hl
    · unfold Renormalization3.linkBaseCoordinate
      have hui := congrFun hu i
      rw [← hui]
      simp [dualUpperFace]
    · unfold Renormalization3.linkBaseCoordinate
      have hli := congrFun hl i
      rw [← hli]
      simp [dualLowerFace]
  · rcases hface with hu | hl
    · have heq : e.1 k = v.1 k := by
        have huk := congrFun hu k
        simpa [dualUpperFace, hki] using huk.symm
      unfold Renormalization3.linkBaseCoordinate
      rw [heq, hxk]
      simp
    · have heq : e.1 k = v.1 k := by
        have hlk := congrFun hl k
        simpa [dualLowerFace, hki] using hlk.symm
      unfold Renormalization3.linkBaseCoordinate
      rw [heq, hxk]
      simp


theorem xy3_currentNear_of_commonVertexStencil {B : Dual3Box}
    (v : Dual3Vertices B) (e f : Dual3Links B)
    (he : dual3D₀ (EuclideanSpace.single v 1) e ≠ 0)
    (hf : dual3D₀ (EuclideanSpace.single v 1) f ≠ 0) :
    Expansion3.currentNear e f := by
  obtain ⟨i, x, hx, hfaceE⟩ := xy3_stencil_nonzero_has_face v e he
  obtain ⟨j, y, hy, hfaceF⟩ := xy3_stencil_nonzero_has_face v f hf
  apply Or.inl
  intro k
  change Renormalization3.linkBaseCoordinate e k ≤
      Renormalization3.linkBaseCoordinate f k + 1 ∧
    Renormalization3.linkBaseCoordinate f k ≤
      Renormalization3.linkBaseCoordinate e k + 1
  have hleft := xy3_incidentLink_baseCoordinate v e i x hx hfaceE k
  have hright := xy3_incidentLink_baseCoordinate v f j y hy hfaceF k
  rcases hleft with hleft | hleft
  · rcases hright with hright | hright
    · constructor <;> omega
    · constructor <;> omega
  · rcases hright with hright | hright
    · constructor <;> omega
    · constructor <;> omega

/--
The premise is coordinatewise and works for real link fields.
-/
theorem xy3_vertexStencilSeparated_of_currentNearSeparated {B : Dual3Box}
    {I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) (q : I → EuclideanSpace ℝ (Dual3Links B))
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      ∀ e f, q i e ≠ 0 → q j f ≠ 0 → ¬ Expansion3.currentNear e f) :
    ∀ v : Dual3Vertices B, ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      (∀ e, dual3D₀ (EuclideanSpace.single v (1 : ℝ)) e ≠ 0 → q i e = 0) ∨
      (∀ e, dual3D₀ (EuclideanSpace.single v (1 : ℝ)) e ≠ 0 → q j e = 0) := by
  intro v i hi j hj hij
  by_cases hqi : ∀ e, dual3D₀ (EuclideanSpace.single v (1 : ℝ)) e ≠ 0 → q i e = 0
  · exact Or.inl hqi
  · right
    intro f hf
    by_contra hqjf
    push Not at hqi
    obtain ⟨e, he, hqie⟩ := hqi
    have hnear : Expansion3.currentNear e f :=
      xy3_currentNear_of_commonVertexStencil v e f he hf
    exact hsep i hi j hj hij e f hqie hqjf hnear

/-- A co-closed sum of mutually `currentNear`-separated real link fields has
co-closed components. This is the closure rule for the surviving separated
family; it is not asserted for intermediate raw lineages. -/
theorem xy3_each_coClosed_of_currentNearSeparated {B : Dual3Box}
    {I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) (q : I → EuclideanSpace ℝ (Dual3Links B))
    (hsum : (∑ i ∈ T, q i) ∈ coClosed (dual3ExactOneComplex B))
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      ∀ e f, q i e ≠ 0 → q j f ≠ 0 → ¬ Expansion3.currentNear e f) :
    ∀ i ∈ T, q i ∈ coClosed (dual3ExactOneComplex B) := by
  apply xy3_each_coClosed_of_pairwiseStencilSeparated T q hsum
  exact xy3_vertexStencilSeparated_of_currentNearSeparated T q hsep


/-! ### Local relative-phase packing

The next theorem proves the aggregate budget from the local data used by a
controlled relative filling.  Its assumptions are per-current phase control,
support localization, and a box-volume bound; it does not assume an aggregate
Jensen budget. -/

/-- A relative filling with controlled coefficient mass gives a controlled
representative for the phase pairing. -/
theorem xy3_twoPi_fillPairing_abs_le
    {P : Type*} [Fintype P]
    (fill field : P → ℝ) (M A E : ℝ) (L : ℕ)
    (hM : 0 ≤ M)
    (hfield : ∀ p, fill p ≠ 0 → |field p| ≤ M)
    (hmass : (∑ p, |fill p|) ≤ A * E * (L : ℝ)^4) :
    |(2 * Real.pi) * (∑ p, field p * fill p)| ≤
      (2 * Real.pi) * A * M * E * (L : ℝ)^4 := by
  have hterm : ∀ p, |field p * fill p| ≤ M * |fill p| := by
    intro p
    by_cases hp : fill p = 0
    · simp [hp]
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hfield p hp) (abs_nonneg _)
  have hsum : (∑ p, |field p * fill p|) ≤ M * (∑ p, |fill p|) := by
    calc
      (∑ p, |field p * fill p|) ≤ ∑ p, M * |fill p| :=
        Finset.sum_le_sum fun p _ => hterm p
      _ = M * (∑ p, |fill p|) := by rw [Finset.mul_sum]
  have htriangle : |∑ p, field p * fill p| ≤ ∑ p, |field p * fill p| :=
    Finset.abs_sum_le_sum_abs _ _
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  calc
    |(2 * Real.pi) * (∑ p, field p * fill p)| =
        (2 * Real.pi) * |∑ p, field p * fill p| := by
          rw [abs_mul, abs_of_nonneg hpi]
    _ ≤ (2 * Real.pi) * ∑ p, |field p * fill p| :=
      mul_le_mul_of_nonneg_left htriangle hpi
    _ ≤ (2 * Real.pi) * (M * (∑ p, |fill p|)) :=
      mul_le_mul_of_nonneg_left hsum hpi
    _ ≤ (2 * Real.pi) * (M * (A * E * (L : ℝ)^4)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass hM) hpi
    _ = (2 * Real.pi) * A * M * E * (L : ℝ)^4 := by ring


/-- A finite-family Jensen/packing estimate from local phase representatives.
For each current, the representative is controlled by a local field maximum
times its squared current norm and the fourth power of its support length.
Disjoint supports localized in a side-six box give the dimension-three
packing count (the looser four-dimensional cardinality bound is sufficient).
-/
theorem xy3_relativePhase_packing
    {I P α : Type*} [DecidableEq I] [DecidableEq α]
    [Fintype P] [DecidableEq P]
    (T : Finset I) (K : Finset ℕ)
    (support : I → Finset α) (box : P → ℕ → Finset α)
    (plaquette : I → P) (length : I → ℕ)
    (z energy θ : I → ℝ) (field : P → ℝ) (fill : I → P → ℝ)
    (a Cfill : ℝ)
    (ha : 0 < a) (ha1 : 1 ≤ a) (hCfill : 0 ≤ Cfill)
    (hlength_mem : ∀ i ∈ T, length i ∈ K)
    (hKpos : ∀ L ∈ K, 1 ≤ L)
    (henergy : ∀ i ∈ T, 0 ≤ energy i)
    (hz0 : ∀ i ∈ T, 0 ≤ z i)
    (hz : ∀ i ∈ T,
      z i ≤ Real.exp (-((a) * (energy i + (length i : ℝ)))))
    (hθ : ∀ i ∈ T,
      θ i = (2 * Real.pi) * (∑ p, field p * fill i p))
    (hfillMass : ∀ i ∈ T,
      (∑ p, |fill i p|) ≤ Cfill * energy i * (length i : ℝ)^4)
    (hfieldMax : ∀ i ∈ T, ∀ p, fill i p ≠ 0 →
      |field p| ≤ |field (plaquette i)|)
    (hdisj : (↑T : Set I).PairwiseDisjoint support)
    (hsize : ∀ i ∈ T, (support i).card = length i)
    (hlocal : ∀ i ∈ T,
      support i ⊆ box (plaquette i) (length i))
    (hbox : ∀ p L, (box p L).card ≤ 4 * (6 * L)^4) :
    (∑ i ∈ T, sourceJensenGamma (z i) * θ i ^ 2) ≤
      (81 * cpack a (2 * Real.pi * Cfill)) *
        (∑ p, (field p)^2) := by
  have herror : ∀ i ∈ T,
      sourceJensenGamma (z i) * θ i ^ 2 ≤
        currentActivity a (2 * Real.pi * Cfill) (length i) *
          (field (plaquette i))^2 := by
    intro i hi
    have hL : 1 ≤ length i := hKpos (length i) (hlength_mem i hi)
    have hphase : |θ i| ≤ (2 * Real.pi * Cfill) *
        |field (plaquette i)| * energy i * (length i : ℝ)^4 := by
      rw [hθ i hi]
      apply xy3_twoPi_fillPairing_abs_le (fill i) field
        |field (plaquette i)| Cfill (energy i) (length i)
      · exact abs_nonneg _
      · exact fun p hp => hfieldMax i hi p hp
      · simpa [mul_assoc] using hfillMass i hi
    have hC : 0 ≤ 2 * Real.pi * Cfill := by positivity
    have h := jensen_per_current_activity_error_positive a (2 * Real.pi * Cfill)
      (energy i)
      |field (plaquette i)| (z i) (θ i) (length i)
      ha ha1 hC (henergy i hi) (abs_nonneg _)
      (hz0 i hi) (hz i hi) hL hphase
    simpa [Moment.Packing.jensenGamma, Moment.SourceJensen.sourceJensenGamma,
      pow_two] using h
  have hactivity : ∀ L ∈ K, 0 ≤ currentActivity a (2 * Real.pi * Cfill) L := by
    intro L hL
    unfold currentActivity
    positivity
  have hbudget : (∑ L ∈ K,
      5184 * (L : ℝ)^3 * currentActivity a (2 * Real.pi * Cfill) L) ≤
        81 * cpack a (2 * Real.pi * Cfill) := by
    exact side_six_activity_budget_le_81_cpack a (2 * Real.pi * Cfill) ha K
  exact finite_current_packing_l2_side_six_positive T K support box plaquette length
    (fun i => sourceJensenGamma (z i) * θ i ^ 2) field
    (currentActivity a (2 * Real.pi * Cfill))
    (81 * cpack a (2 * Real.pi * Cfill))
    hlength_mem hKpos
    hdisj hsize hlocal hbox
    (by
      intro i hi
      exact herror i hi)
    hactivity hbudget


/-- Countable outer mixtures preserve a uniform positive-branch lower bound.
This is the `HasSum` form needed when the branch label includes an integer
current assignment; it does not require the whole set of assignments to be
finite. -/
theorem xy3_countablePositiveBranchRatio_lower
    {I : Type*} [Countable I]
    (d Z J cost : I → ℝ) (rate energy denominator numerator : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hZ : ∀ i, 0 ≤ Z i)
    (hden : 0 < denominator)
    (hdenSum : HasSum (fun i => d i * Z i) denominator)
    (hnumSum : HasSum (fun i => d i * J i) numerator)
    (hbranch : ∀ i, Z i * Real.exp (-cost i) ≤ J i)
    (hcost : ∀ i, cost i ≤ rate * energy) :
    Real.exp (-(rate * energy)) ≤ numerator / denominator := by
  have hterm : ∀ i, Real.exp (-(rate * energy)) * (d i * Z i) ≤
      d i * J i := by
    intro i
    have hexp : Real.exp (-(rate * energy)) ≤ Real.exp (-cost i) :=
      Real.exp_le_exp.mpr (neg_le_neg (hcost i))
    calc
      Real.exp (-(rate * energy)) * (d i * Z i) =
          d i * (Z i * Real.exp (-(rate * energy))) := by ring
      _ ≤ d i * (Z i * Real.exp (-cost i)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (hZ i)) (hd i)
      _ ≤ d i * J i := mul_le_mul_of_nonneg_left (hbranch i) (hd i)
  have hscaled : HasSum
      (fun i => Real.exp (-(rate * energy)) * (d i * Z i))
      (Real.exp (-(rate * energy)) * denominator) :=
    hdenSum.mul_left (Real.exp (-(rate * energy)))
  have htotal := hasSum_le hterm hscaled hnumSum
  rw [le_div_iff₀ hden]
  exact htotal


end FroehlichSpencer.FS82.XY

end
