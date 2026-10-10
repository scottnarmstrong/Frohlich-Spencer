/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.IncidenceComponentPacking
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# FS82 PackingFamily component path and packing family
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents.PackingFamily

open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.ComponentPacking
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

noncomputable section
open Classical

theorem SourceVertexPath.trans {B : Box 4} (q : IntegerCurrent B)
    {p r s : Anchor 4 (bumpedBox B)} {n m : ℕ}
    (h₁ : SourceVertexPath q p r n) (h₂ : SourceVertexPath q r s m) :
    ∃ k, SourceVertexPath q p s k ∧ k = n + m := by
  induction h₁ with
  | refl p => exact ⟨m, by simpa using h₂, by simp⟩
  | @cons a b c n hab htail ih =>
      obtain ⟨k, hpath, hk⟩ := ih h₂
      refine ⟨k + 1, SourceVertexPath.cons hab hpath, ?_⟩
      omega

theorem SourceVertexPath.one_link {B : Box 4} (q : IntegerCurrent B)
    (e : Link B) (he : e ∈ q.support) :
    SourceVertexPath q (base e) (sourceLinkUpperAnchor e) 1 := by
  exact SourceVertexPath.cons
    (by exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
    (SourceVertexPath.refl _)

theorem SourceVertexPath.symm {B : Box 4} (q : IntegerCurrent B)
    {p r : Anchor 4 (bumpedBox B)} {n : ℕ}
    (h : SourceVertexPath q p r n) :
    SourceVertexPath q r p n := by
  induction h with
  | refl p => exact SourceVertexPath.refl _
  | @cons a b c n hab htail ih =>
      have hrev : SourceVertexPath q c b n := ih
      have hback : SourceVertexPath q b a 1 := by
        exact SourceVertexPath.cons (by
          rcases hab with ⟨e, he, h | h⟩
          · exact ⟨e, he, Or.inr ⟨h.2, h.1⟩⟩
          · exact ⟨e, he, Or.inl ⟨h.2, h.1⟩⟩)
          (SourceVertexPath.refl _)
      obtain ⟨k, hout, hk⟩ := SourceVertexPath.trans q hrev hback
      have hk' : k = n + 1 := by simpa using hk
      simpa [hk'] using hout

theorem boundaryBasis_link_support_subset {B : Box 4}
    (e : Link B) {c : Cell 4 (bumpedBox B)}
    (hc : c ∈ (boundaryBasis (lambdaCellToBumpedBox e.1)).support) :
    c = vertexCell (base e) ∨
      c = vertexCell (sourceLinkUpperAnchor e) := by
  have hdegree : cellDegree (lambdaCellToBumpedBox e.1) = 1 := by
    rw [lambdaCellToBumpedBox_degree]
    exact e.2
  have haxes : cellAxes (lambdaCellToBumpedBox e.1) = {axis e} := by
    rw [lambdaCellToBumpedBox_axes, axes_eq_singleton]
  let term : Fin 4 → Chain 4 (bumpedBox B) :=
    fun i => axisBoundaryBasis (lambdaCellToBumpedBox e.1) i
  have hsumEq : boundaryBasis (lambdaCellToBumpedBox e.1) =
      ∑ i : Fin 4, term i := by
    simp [term, boundaryBasis, axisBoundaryBasis]
  have hcval := Finsupp.mem_support_iff.mp hc
  rw [hsumEq] at hcval
  have hc' : c ∈ Function.support
      (fun x => ∑ i : Fin 4, term i x) := by
    change (∑ i : Fin 4, term i c) ≠ 0
    exact hcval
  have hmem := Finset.support_sum (Finset.univ : Finset (Fin 4))
    (fun i x => term i x) hc'
  rcases Set.mem_iUnion.mp hmem with ⟨i, hi⟩
  rcases Set.mem_iUnion.mp hi with ⟨hi, hterm⟩
  have hterm' : (term i) c ≠ 0 := by
    simpa only [Function.support, Set.mem_ofPred_eq] using hterm
  have hcoords : (lambdaCellToBumpedBox e.1 i).isRight := by
    cases hcoord : lambdaCellToBumpedBox e.1 i with
    | inl v => simp [term, axisBoundaryBasis, hcoord] at hterm'
    | inr v => rfl
  have hiAxis : i = axis e := by
    have hi' : i ∈ dualCellAxes e.1 := by
      rw [← lambdaCellToBumpedBox_axes]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcoords⟩
    rw [axes_eq_singleton] at hi'
    exact Finset.mem_singleton.mp hi'
  subst i
  obtain ⟨x, hx⟩ := axis_coord_exists e
  have htermVal : (axisBoundaryBasis (lambdaCellToBumpedBox e.1)
      (axis e)) c ≠ 0 := by
    simpa [term] using hterm'
  have hcoord : lambdaCellToBumpedBox e.1 (axis e) = Sum.inr x := by
    simp [lambdaCellToBumpedBox, hx]
    exact congrArg Sum.inr (Fin.ext rfl)
  have hend : c = upperFace (lambdaCellToBumpedBox e.1) (axis e)
        x ∨
      c = lowerFace (lambdaCellToBumpedBox e.1) (axis e)
        x := by
    by_contra hn
    push Not at hn
    have hz : (axisBoundaryBasis (lambdaCellToBumpedBox e.1)
        (axis e)) c = 0 := by
      rw [axisBoundaryBasis, hcoord]
      simp [basisChain, hn.1, hn.2]
    exact htermVal hz
  rcases hend with hupper | hlower
  · right
    rw [hupper]
    have hface : upperFace (lambdaCellToBumpedBox e.1) (axis e) x =
        vertexCell (sourceLinkUpperAnchor e) := by
      funext k
      by_cases hki : k = axis e
      · subst k
        simp [upperFace, vertexUpdate,
          hx, vertexCell, sourceLinkUpperAnchor, base, coordToBumpedAnchor]
      · rw [upperFace_apply_of_ne (c := lambdaCellToBumpedBox e.1)
          (i := axis e) (k := k) (e := x) hki]
        cases hcoord' : e.1 k with
        | inl v =>
          simp [vertexCell, base, coordToBumpedAnchor,
            lambdaCellToBumpedBox, hcoord', sourceLinkUpperAnchor,
            Function.update_of_ne hki]
          rfl
        | inr t =>
            have hkAxis : k ∈ dualCellAxes e.1 := by
              simp [dualCellAxes, hcoord']
            rw [axes_eq_singleton] at hkAxis
            exact (hki (Finset.mem_singleton.mp hkAxis)).elim
    exact hface
  · left
    rw [hlower]
    have hface : lowerFace (lambdaCellToBumpedBox e.1) (axis e) x =
        vertexCell (base e) := by
      funext k
      by_cases hki : k = axis e
      · subst k
        simp [lowerFace, vertexUpdate,
          hx, vertexCell, base, coordToBumpedAnchor]
        apply congrArg Sum.inl
        apply Fin.ext
        rfl
      · rw [lowerFace_apply_of_ne (c := lambdaCellToBumpedBox e.1)
          (i := axis e) (k := k) (e := x) hki]
        cases hcoord' : e.1 k with
        | inl v =>
          simp [vertexCell, base, coordToBumpedAnchor,
            lambdaCellToBumpedBox, hcoord']
          rfl
        | inr t =>
            have hkAxis : k ∈ dualCellAxes e.1 := by
              simp [dualCellAxes, hcoord']
            rw [axes_eq_singleton] at hkAxis
            exact (hki (Finset.mem_singleton.mp hkAxis)).elim
    exact hface

def sourceDualZeroAnchor {B : Box 4}
  (v : Gaussian.SourceDualZeroCells B) : Anchor 4 (bumpedBox B) :=
  zeroCellAnchor (lambdaCellToBumpedBox v.1)
    (by rw [lambdaCellToBumpedBox_degree]; exact v.2)

theorem sourceDualZeroAnchor_cell {B : Box 4}
    (v : Gaussian.SourceDualZeroCells B) :
    vertexCell (sourceDualZeroAnchor v) = lambdaCellToBumpedBox v.1 := by
  exact vertexCell_zeroCellAnchor _

theorem linkIncidentAt_sourceEndpoint {B : Box 4} (e : Link B)
    (v : Gaussian.SourceDualZeroCells B) (hinc : linkIncidentAt e v) :
    sourceDualZeroAnchor v = base e ∨
      sourceDualZeroAnchor v = sourceLinkUpperAnchor e := by
  have hcoeff : boundary (sourceCurrentLatticeChain
      (Finsupp.single e (1 : ℤ))) (lambdaCellToBumpedBox v.1) ≠ 0 := by
    intro hz
    apply hinc
    rw [← sourceCurrentLatticeChainDivergence_matches
      (Finsupp.single e (1 : ℤ)) v]
    simp [hz]
  have hboundary : boundary (sourceCurrentLatticeChain
      (Finsupp.single e (1 : ℤ))) =
      (sourceCurrentOrientationSign e * (1 : ℤ)) •
        boundaryBasis (lambdaCellToBumpedBox e.1) := by
    rw [sourceCurrentLatticeChain_single, map_smul, boundary_basis]
  have hbasis : (boundaryBasis (lambdaCellToBumpedBox e.1)
      (lambdaCellToBumpedBox v.1)) ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hboundary, Finsupp.smul_apply, hz]
    simp
  have hmem : lambdaCellToBumpedBox v.1 ∈
      (boundaryBasis (lambdaCellToBumpedBox e.1)).support :=
    Finsupp.mem_support_iff.mpr hbasis
  rcases boundaryBasis_link_support_subset e hmem with hbase | hupper
  · left
    have hcell : vertexCell (sourceDualZeroAnchor v) =
        vertexCell (base e) := by
      rw [sourceDualZeroAnchor_cell, hbase]
    funext i
    exact Sum.inl.inj (congrFun hcell i)
  · right
    have hcell : vertexCell (sourceDualZeroAnchor v) =
        vertexCell (sourceLinkUpperAnchor e) := by
      rw [sourceDualZeroAnchor_cell, hupper]
    funext i
    exact Sum.inl.inj (congrFun hcell i)

theorem linksShareFiniteVertex_sourceEndpoint {B : Box 4}
    {e f : Link B} (hshare : linksShareFiniteVertex e f) :
    ∃ v : Anchor 4 (bumpedBox B),
      (v = base e ∨ v = sourceLinkUpperAnchor e) ∧
      (v = base f ∨ v = sourceLinkUpperAnchor f) := by
  obtain ⟨w, he, hf⟩ := hshare
  let v := sourceDualZeroAnchor w
  have hve := linkIncidentAt_sourceEndpoint e w he
  have hvf := linkIncidentAt_sourceEndpoint f w hf
  exact ⟨v, hve, hvf⟩

theorem SourceVertexPath.between_link_endpoints {B : Box 4}
    (q : IntegerCurrent B) (e : Link B) (he : e ∈ q.support)
    {p r : Anchor 4 (bumpedBox B)}
    (hp : p = base e ∨ p = sourceLinkUpperAnchor e)
    (hr : r = base e ∨ r = sourceLinkUpperAnchor e) :
    ∃ n, n ≤ 1 ∧ SourceVertexPath q p r n := by
  rcases hp with hp | hp
  · subst p
    rcases hr with hr | hr
    · subst r
      exact ⟨0, by omega, SourceVertexPath.refl _⟩
    · subst r
      exact ⟨1, by omega, SourceVertexPath.one_link q e he⟩
  · subst p
    rcases hr with hr | hr
    · subst r
      exact ⟨1, by omega,
        SourceVertexPath.symm q (SourceVertexPath.one_link q e he)⟩
    · subst r
      exact ⟨0, by omega, SourceVertexPath.refl _⟩

theorem SourceVertexPath.of_linkWalk {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j)
    (q : IntegerCurrent B)
    (hsub : currentComponentSupport j c ⊆ q.support)
    {u v : currentComponentSupport j c}
    {a b : Anchor 4 (bumpedBox B)}
    (ha : a = base u.1 ∨ a = sourceLinkUpperAnchor u.1)
    (hb : b = base v.1 ∨ b = sourceLinkUpperAnchor v.1)
    (p : (ComponentPacking.componentLinkGraph j c).Walk u v) :
    ∃ n, n ≤ p.length + 1 ∧ SourceVertexPath q a b n := by
  induction p generalizing a b with
  | @nil x =>
      have hb' : b = base x.1 ∨ b = sourceLinkUpperAnchor x.1 := by
        simpa using hb
      exact SourceVertexPath.between_link_endpoints q x.1
        (hsub x.2) ha hb'
  | @cons x y z hxy tail ih =>
      obtain ⟨s, hsx, hsy⟩ := linksShareFiniteVertex_sourceEndpoint hxy.2
      obtain ⟨n₁, hn₁, hfirst⟩ :=
        SourceVertexPath.between_link_endpoints q x.1
          (hsub x.2) ha hsx
      obtain ⟨n₂, hn₂, htail⟩ := ih hsy hb
      obtain ⟨n, hpath, hn⟩ := SourceVertexPath.trans q hfirst htail
      refine ⟨n, ?_, hpath⟩
      rw [hn]
      change n₁ + n₂ ≤ tail.length + 1 + 1
      omega

theorem boundarySupport_has_boundaryBasis {B : Box 4}
    (μ : Chain 4 B) {c : Cell 4 B} (hc : c ∈ (boundary μ).support) :
    ∃ p ∈ μ.support, boundaryBasis p c ≠ 0 := by
  classical
  have hexp : boundary μ =
      ∑ p ∈ μ.support, μ p • boundaryBasis p := by
    calc
      boundary μ = boundary
          (∑ p ∈ μ.support, μ p • basisChain p) := by
            rw [chain_eq_support_basis]
      _ = ∑ p ∈ μ.support, μ p • boundaryBasis p := by
            rw [map_sum]
            simp_rw [map_smul, boundary_basis]
  have hcval := Finsupp.mem_support_iff.mp hc
  rw [hexp] at hcval
  by_contra hn
  push Not at hn
  have hterm : ∀ p ∈ μ.support, μ p * boundaryBasis p c = 0 := by
    intro p hp
    rw [hn p hp]
    simp
  apply hcval
  calc
    (∑ p ∈ μ.support, μ p • boundaryBasis p) c =
        ∑ p ∈ μ.support, μ p * boundaryBasis p c := by
          simp
    _ = 0 := Finset.sum_eq_zero fun p hp => hterm p hp

theorem sourceCurrentLatticeChain_support_link {B : Box 4}
    (q : IntegerCurrent B) {p : Cell 4 (bumpedBox B)}
    (hp : p ∈ (sourceCurrentLatticeChain q).support) :
    ∃ e ∈ q.support, p = lambdaCellToBumpedBox e.1 := by
  classical
  rw [sourceCurrentLatticeChain, sourceCurrentChain,
    Finsupp.support_embDomain, sourceCurrentOrientationTwist_support] at hp
  obtain ⟨e, he, hpeq⟩ := Finset.mem_map.mp hp
  refine ⟨e, he, ?_⟩
  exact hpeq.symm

theorem sourceBoundary_cell_has_link_endpoint {B : Box 4}
    (q : IntegerCurrent B) {c : Cell 4 (bumpedBox B)}
    (hc : c ∈ (sourceBoundaryChain q).support) :
    ∃ e ∈ q.support,
      c = vertexCell (base e) ∨ c = vertexCell (sourceLinkUpperAnchor e) := by
  obtain ⟨p, hp, hbasis⟩ :=
    boundarySupport_has_boundaryBasis (sourceCurrentLatticeChain q) hc
  obtain ⟨e, he, hpeq⟩ := sourceCurrentLatticeChain_support_link q hp
  rw [hpeq] at hbasis
  refine ⟨e, he, ?_⟩
  exact boundaryBasis_link_support_subset e
    (Finsupp.mem_support_iff.mpr hbasis)

theorem currentComponent_boundary_vertices_connected {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j)
    {u v : Cell 4 (bumpedBox B)}
    (hu : u ∈ (sourceBoundaryChain (currentComponentCurrent j c)).support)
    (hv : v ∈ (sourceBoundaryChain (currentComponentCurrent j c)).support) :
    ∃ n, n ≤ (currentComponentSupport j c).card ∧
      SourceVertexPath (currentComponentCurrent j c)
        (sourceBoundaryAnchor (currentComponentCurrent j c) u)
        (sourceBoundaryAnchor (currentComponentCurrent j c) v) n := by
  let q := currentComponentCurrent j c
  obtain ⟨e, he, heEndpoint⟩ := sourceBoundary_cell_has_link_endpoint q hu
  obtain ⟨f, hf, hfEndpoint⟩ := sourceBoundary_cell_has_link_endpoint q hv
  have heComp : e ∈ currentComponentSupport j c := by
    simpa [q, currentComponentCurrent_support] using he
  have hfComp : f ∈ currentComponentSupport j c := by
    simpa [q, currentComponentCurrent_support] using hf
  have hstart : sourceBoundaryAnchor q u = base e ∨
      sourceBoundaryAnchor q u = sourceLinkUpperAnchor e := by
    have hcell : vertexCell (sourceBoundaryAnchor q u) = vertexCell (base e) ∨
        vertexCell (sourceBoundaryAnchor q u) =
          vertexCell (sourceLinkUpperAnchor e) := by
      rw [sourceBoundaryAnchor_cell q hu]
      exact heEndpoint
    rcases hcell with h | h
    · exact Or.inl (by
        funext i
        exact Sum.inl.inj (congrFun h i))
    · exact Or.inr (by
        funext i
        exact Sum.inl.inj (congrFun h i))
  have hfinish : sourceBoundaryAnchor q v = base f ∨
      sourceBoundaryAnchor q v = sourceLinkUpperAnchor f := by
    have hcell : vertexCell (sourceBoundaryAnchor q v) = vertexCell (base f) ∨
        vertexCell (sourceBoundaryAnchor q v) =
          vertexCell (sourceLinkUpperAnchor f) := by
      rw [sourceBoundaryAnchor_cell q hv]
      exact hfEndpoint
    rcases hcell with h | h
    · exact Or.inl (by
        funext i
        exact Sum.inl.inj (congrFun h i))
    · exact Or.inr (by
        funext i
        exact Sum.inl.inj (congrFun h i))
  obtain ⟨p, hsimple, hwalkLength⟩ :=
    currentComponent_has_bounded_link_path j c heComp hfComp
  have hstrict : p.length < (currentComponentSupport j c).card := by
    simpa [ComponentPacking.componentLinkGraph] using hsimple.length_lt
  obtain ⟨n, hn, hpath⟩ :=
    SourceVertexPath.of_linkWalk j c q
      (by simp [q, currentComponentCurrent_support]) hstart hfinish p
  exact ⟨n, by omega, hpath⟩

end
end FroehlichSpencer.FS82.Currents.PackingFamily

end
