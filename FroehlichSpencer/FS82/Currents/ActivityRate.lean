/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.BranchEnvelope
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card

/-!
# FS82 (2.74): uniform local link-neighborhood count

The source's displayed sum in (2.74) is not itself the exponential activity
bound used later. This module starts with a box-uniform geometric count for
links at distance at most one.
-/

public section

namespace FroehlichSpencer.FS82.Currents

open Cubical

private theorem linkPointAt_coord_bounds {B : Box 4} (e : Link B) (t : ℝ)
    (ht₀ : (e.base e.axis).val ≤ t)
    (ht₁ : t ≤ (e.base e.axis).val + 1) (i : Fin 4) :
    ((e.base i).val : ℝ) ≤ linkPointAt e t i ∧
      linkPointAt e t i ≤ (e.base i).val + 1 := by
  by_cases hi : i = e.axis
  · subst i
    simpa [linkPointAt] using And.intro ht₀ ht₁
  · simp [linkPointAt, hi]

private theorem euclidean_coord_abs_le_norm (x : Point) (i : Fin 4) :
    |x i| ≤ ‖x‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq x]
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun j : Fin 4 => ‖x.ofLp j‖ ^ 2)
    (fun j hj => sq_nonneg _) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs] using h

private theorem point_coord_dist_le {x y : Point} (i : Fin 4) :
    |x i - y i| ≤ dist x y := by
  rw [dist_eq_norm]
  simpa using euclidean_coord_abs_le_norm (x - y) i

private theorem linkDistance_ge_two_of_baseCoordGap_four {B : Box 4}
    (e f : Link B) (i : Fin 4)
    (hgap : 4 ≤ ((e.base i).val : ℤ) - (f.base i).val) :
    2 ≤ linkDistance e f := by
  have hnonempty :
      {r : ℝ | ∃ x ∈ linkSegment e, ∃ y ∈ linkSegment f, r = dist x y}.Nonempty := by
    exact ⟨dist (vertexPoint e.base) (vertexPoint f.base),
      ⟨vertexPoint e.base, sourcePoint_mem_linkSegment e,
        vertexPoint f.base, sourcePoint_mem_linkSegment f, rfl⟩⟩
  apply le_csInf hnonempty
  rintro r ⟨x, hx, y, hy, rfl⟩
  rcases hx with ⟨t, ht₀, ht₁, rfl⟩
  rcases hy with ⟨s, hs₀, hs₁, rfl⟩
  have he := linkPointAt_coord_bounds e t ht₀ ht₁ i
  have hf := linkPointAt_coord_bounds f s hs₀ hs₁ i
  have hcoord := point_coord_dist_le (x := linkPointAt e t) (y := linkPointAt f s) i
  have hgapR : (4 : ℝ) ≤ (e.base i).val - (f.base i).val := by
    exact_mod_cast hgap
  have hsep : 2 ≤ linkPointAt e t i - linkPointAt f s i := by
    nlinarith [he.1, hf.2, hgapR]
  have hcoord' : linkPointAt e t i - linkPointAt f s i ≤
      dist (linkPointAt e t) (linkPointAt f s) := by
    have hsign : 0 ≤ linkPointAt e t i - linkPointAt f s i := by linarith
    rw [abs_of_nonneg hsign] at hcoord
    exact hcoord
  exact le_trans hsep hcoord'

theorem linkDistance_le_one_base_coordinate_gap {B : Box 4}
    (e f : Link B) (h : linkDistance e f ≤ 1) (i : Fin 4) :
    -3 ≤ ((e.base i).val : ℤ) - (f.base i).val ∧
      ((e.base i).val : ℤ) - (f.base i).val ≤ 3 := by
  constructor
  · by_contra hnot
    have hgap : 4 ≤ ((f.base i).val : ℤ) - (e.base i).val := by omega
    have := linkDistance_ge_two_of_baseCoordGap_four f e i hgap
    rw [linkDistance_symm] at this
    linarith
  · by_contra hnot
    have hgap : 4 ≤ ((e.base i).val : ℤ) - (f.base i).val := by omega
    have := linkDistance_ge_two_of_baseCoordGap_four e f i hgap
    linarith


/-- The bounded integer offset of a link base from a chosen center base. -/
@[expose] def linkBaseOffset {B : Box 4} (center e : Link B) (i : Fin 4) : ℤ :=
  (e.base i).val - (center.base i).val

/-- A finite code for a coordinate offset in `[-3,3]`; modulo keeps this
function total away from the local ball. -/
@[expose] def localCoordinateCode {B : Box 4} (center e : Link B) (i : Fin 4) : Fin 7 :=
  ⟨(Int.toNat (linkBaseOffset center e i + 3)) % 7, Nat.mod_lt _ (by norm_num)⟩

/-- Encode a link by its orientation and its four local base offsets. -/
@[expose] noncomputable def localLinkCode {B : Box 4} (center e : Link B) :
    Fin 4 × (Fin 4 → Fin 7) :=
  (e.axis, fun i => localCoordinateCode center e i)

@[expose] noncomputable def linkCoordinateBall {B : Box 4} (center : Link B) : Finset (Link B) :=
  Finset.univ.filter fun e => ∀ i, -3 ≤ linkBaseOffset center e i ∧
    linkBaseOffset center e i ≤ 3

theorem linkDistance_mem_linkCoordinateBall {B : Box 4} (center e : Link B)
    (h : linkDistance center e ≤ 1) : e ∈ linkCoordinateBall center := by
  simp only [linkCoordinateBall, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  rcases linkDistance_le_one_base_coordinate_gap center e h i with ⟨hlo, hhi⟩
  constructor
  · dsimp [linkBaseOffset]
    omega
  · dsimp [linkBaseOffset]
    omega

private theorem localCoordinateCode_val {B : Box 4} (center e : Link B) (i : Fin 4)
    (hlo : -3 ≤ linkBaseOffset center e i)
    (hhi : linkBaseOffset center e i ≤ 3) :
    (localCoordinateCode center e i).val = Int.toNat (linkBaseOffset center e i + 3) := by
  unfold localCoordinateCode
  have hnonneg : 0 ≤ linkBaseOffset center e i + 3 := by omega
  have hnatCast : ((Int.toNat (linkBaseOffset center e i + 3) : ℕ) : ℤ) =
      linkBaseOffset center e i + 3 := Int.toNat_of_nonneg hnonneg
  have hltZ : ((Int.toNat (linkBaseOffset center e i + 3) : ℕ) : ℤ) < 7 := by
    rw [hnatCast]
    omega
  have hlt : Int.toNat (linkBaseOffset center e i + 3) < 7 := by exact_mod_cast hltZ
  simp [Nat.mod_eq_of_lt hlt]

private theorem link_eq_of_axis_base_eq {B : Box 4} {e f : Link B}
    (haxis : e.axis = f.axis) (hbase : e.base = f.base) : e = f := by
  apply Subtype.ext
  funext i
  have haxesE : Cubical.dualCellAxes e.1 = {e.axis} := axes_eq_singleton e
  have haxesF : Cubical.dualCellAxes f.1 = {f.axis} := axes_eq_singleton f
  by_cases hi : i = e.axis
  · subst i
    have hmemE : e.axis ∈ Cubical.dualCellAxes e.1 := by simp [haxesE]
    have hmemF : e.axis ∈ Cubical.dualCellAxes f.1 := by
      rw [haxesF]
      simp [haxis]
    have heRight : (e.1 e.axis).isRight := (Finset.mem_filter.mp hmemE).2
    have hfRight : (f.1 e.axis).isRight := (Finset.mem_filter.mp hmemF).2
    cases he : e.1 e.axis with
    | inl v => simp [he] at heRight
    | inr v =>
      cases hf : f.1 e.axis with
      | inl w => simp [hf] at hfRight
      | inr w =>
        have hcoord : v.val = w.val := by
          have hcoord := congrArg (fun a : Cubical.Anchor 4 (bumpedBox B) => (a e.axis).val) hbase
          simpa [base, coordToBumpedAnchor, he, hf] using hcoord
        have hv : v = w := Fin.ext hcoord
        exact congrArg Sum.inr hv
  · have hiF : i ≠ f.axis := by simpa [haxis] using hi
    have hnotE : i ∉ Cubical.dualCellAxes e.1 := by
      rw [haxesE]
      simp [hi]
    have hnotF : i ∉ Cubical.dualCellAxes f.1 := by
      rw [haxesF]
      simp [hiF]
    have heLeft : ¬ (e.1 i).isRight := by
      intro hr
      exact hnotE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
    have hfLeft : ¬ (f.1 i).isRight := by
      intro hr
      exact hnotF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
    cases he : e.1 i with
    | inl v =>
      cases hf : f.1 i with
      | inl w =>
        have hcoord : v.val = w.val := by
          have hcoord := congrArg (fun a : Cubical.Anchor 4 (bumpedBox B) => (a i).val) hbase
          simpa [base, coordToBumpedAnchor, he, hf] using hcoord
        have hv : v = w := Fin.ext (by omega)
        exact congrArg Sum.inl hv
      | inr w => simp [hf] at hfLeft
    | inr v => simp [he] at heLeft

theorem localLinkCode_injective_on_linkCoordinateBall {B : Box 4}
    (center : Link B) :
    Set.InjOn (localLinkCode center) (↑(linkCoordinateBall center) : Set (Link B)) := by
  intro e he f hf hcode
  have heLocal : ∀ i, -3 ≤ linkBaseOffset center e i ∧ linkBaseOffset center e i ≤ 3 :=
    (Finset.mem_filter.mp he).2
  have hfLocal : ∀ i, -3 ≤ linkBaseOffset center f i ∧ linkBaseOffset center f i ≤ 3 :=
    (Finset.mem_filter.mp hf).2
  have haxis : e.axis = f.axis := by
    exact congrArg Prod.fst hcode
  have hbase : e.base = f.base := by
    funext i
    apply Fin.ext
    have hcoord := congrArg (fun c : Fin 4 × (Fin 4 → Fin 7) => (c.2 i).val) hcode
    change (localCoordinateCode center e i).val =
      (localCoordinateCode center f i).val at hcoord
    rw [localCoordinateCode_val center e i (heLocal i).1 (heLocal i).2,
      localCoordinateCode_val center f i (hfLocal i).1 (hfLocal i).2] at hcoord
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hcoord
    have hne : 0 ≤ linkBaseOffset center e i + 3 := by linarith [(heLocal i).1]
    have hnf : 0 ≤ linkBaseOffset center f i + 3 := by linarith [(hfLocal i).1]
    rw [Int.toNat_of_nonneg hne, Int.toNat_of_nonneg hnf] at hcast
    have hoffset : linkBaseOffset center e i = linkBaseOffset center f i := by
      linarith [hcast]
    dsimp [linkBaseOffset] at hoffset
    omega
  exact link_eq_of_axis_base_eq haxis hbase

theorem linkCoordinateBall_card_le {B : Box 4} (center : Link B) :
    (linkCoordinateBall center).card ≤ 4 * 7 ^ 4 := by
  let target : Finset (Fin 4 × (Fin 4 → Fin 7)) := Finset.univ
  have hcard := Finset.card_le_card_of_injOn
    (s := linkCoordinateBall center) (t := target) (localLinkCode center)
    (by intro e he; simp [target])
    (localLinkCode_injective_on_linkCoordinateBall center)
  calc
    (linkCoordinateBall center).card ≤ target.card := hcard
    _ = 4 * 7 ^ 4 := by simp [target]

noncomputable def oneNeighborUnion {B : Box 4} (S : Finset (Link B)) : Finset (Link B) :=
  S.biUnion fun e => linkCoordinateBall e

theorem oneNeighborSet_subset_oneNeighborUnion {B : Box 4} (S : Finset (Link B)) :
    oneNeighborSet S ⊆ oneNeighborUnion S := by
  intro e he
  rcases (Finset.mem_filter.mp he).2 with ⟨f, hf, hdist⟩
  simp only [oneNeighborUnion, Finset.mem_biUnion]
  have hdist' : linkDistance f e ≤ 1 := by rw [linkDistance_symm]; exact hdist
  exact ⟨f, hf, linkDistance_mem_linkCoordinateBall f e hdist'⟩

theorem oneNeighborSet_card_le_localConstant {B : Box 4} (S : Finset (Link B)) :
    (oneNeighborSet S).card ≤ (4 * 7 ^ 4) * S.card := by
  calc
    (oneNeighborSet S).card ≤ (oneNeighborUnion S).card :=
      Finset.card_le_card (oneNeighborSet_subset_oneNeighborUnion S)
    _ ≤ S.card * (4 * 7 ^ 4) := by
      unfold oneNeighborUnion
      exact Finset.card_biUnion_le_card_mul S (fun e => linkCoordinateBall e)
        (4 * 7 ^ 4) (by intro e he; exact linkCoordinateBall_card_le e)
    _ = (4 * 7 ^ 4) * S.card := by omega


/--
The squared norm of the integer-frequency current.
-/
@[expose] noncomputable def integerCurrentNormSq {B : Box 4} (q : Link B → ℤ) : ℝ :=
  ∑ e, (q e : ℝ) ^ 2


theorem currentSupport_card_le_integerCurrentNormSq {B : Box 4}
    (q : Link B → ℤ) :
    (currentSupport q).card ≤ integerCurrentNormSq q := by
  have hcard : (currentSupport q).card = ∑ e ∈ currentSupport q, (1 : ℝ) := by simp
  have hterm : ∀ e ∈ currentSupport q, (1 : ℝ) ≤ (q e : ℝ) ^ 2 := by
    intro e he
    have hne : q e ≠ 0 := by simpa [currentSupport] using he
    have hn : 1 ≤ (q e).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ((Int.natAbs_pos).mpr hne))
    have hnR : (1 : ℝ) ≤ ((q e).natAbs : ℝ) := by exact_mod_cast hn
    rcases Int.natAbs_eq (q e) with hq | hq
    · have hcast : (q e : ℝ) = ((q e).natAbs : ℝ) := by
        simpa using congrArg (fun z : ℤ => (z : ℝ)) hq
      rw [hcast]
      nlinarith
    · have hcast : (q e : ℝ) = -((q e).natAbs : ℝ) := by
        simpa using congrArg (fun z : ℤ => (z : ℝ)) hq
      rw [hcast]
      nlinarith
  have hsumSupport :
      (∑ e ∈ currentSupport q, (q e : ℝ) ^ 2) = integerCurrentNormSq q := by
    unfold integerCurrentNormSq
    apply Finset.sum_subset (Finset.subset_univ (currentSupport q))
    intro e he hnot
    have hzero : q e = 0 := by
      by_contra hne
      exact hnot (by simp [currentSupport, hne])
    simp [hzero]
  calc
    (currentSupport q).card = ∑ e ∈ currentSupport q, (1 : ℝ) := hcard
    _ ≤ ∑ e ∈ currentSupport q, (q e : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact hterm e he
    _ = integerCurrentNormSq q := hsumSupport


end FroehlichSpencer.FS82.Currents
end
