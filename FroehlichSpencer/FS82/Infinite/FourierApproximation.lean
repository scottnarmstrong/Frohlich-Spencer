/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.FourierGreen
public import FroehlichSpencer.FS82.Infinite.FourierVariational

import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

open MeasureTheory
open Algebra Submodule
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier

@[expose] public section


open MeasureTheory
open Algebra Submodule
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier

namespace FroehlichSpencer.FS82.Infinite.FourierApproximation

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


noncomputable section

@[fun_prop] private theorem continuous_fourier_char_local (n : ℤ) :
    Continuous (fun t : AddCircle (1 : ℝ) => fourier n t) :=
  map_continuous (fourier n)


theorem continuous_latticeCharacter (x : LatticePoint) :
    Continuous (latticeCharacter x) := by
  unfold latticeCharacter
  fun_prop [continuous_fourier_char_local]

theorem latticeCharacter_neg_conj (x : LatticePoint) (k : Torus4) :
    latticeCharacter (-x) k = conj (latticeCharacter x k) := by
  simp [latticeCharacter]

theorem latticeCharacter_mul (x y : LatticePoint) (k : Torus4) :
    latticeCharacter x k * latticeCharacter y k = latticeCharacter (x + y) k := by
  have h : conj (latticeCharacter (-y) k) = latticeCharacter y k := by
    simpa using (latticeCharacter_neg_conj (-y) k).symm
  rw [← h]
  simpa using latticeCharacter_mul_conj x (-y) k

def charMap (x : LatticePoint) : C(Torus4, ℂ) :=
  ⟨latticeCharacter x, continuous_latticeCharacter x⟩

def charSpan : Submodule ℂ C(Torus4, ℂ) :=
  Submodule.span ℂ (Set.range charMap)

def charSubalgebra : StarSubalgebra ℂ C(Torus4, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range charMap)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range charMap) ≤
      star (Algebra.adjoin ℂ (Set.range charMap))
    refine adjoin_le ?_
    rintro _ ⟨x, rfl⟩
    refine subset_adjoin ⟨-x, ?_⟩
    ext k
    exact latticeCharacter_neg_conj x k

theorem charSubalgebra_eq_span :
    charSubalgebra.toSubalgebra.toSubmodule = charSpan := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun f => Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_) subset_span
  · ext k
    simp [charMap, latticeCharacter]
  · rintro _ _ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    ext k
    exact (latticeCharacter_mul x y k).symm

def pointOfCoordinates (x : Fin 4 → ℤ) : LatticePoint :=
  (x 0, (x 1, (x 2, x 3)))


def unitFrequency (i : Fin 4) : LatticePoint :=
  pointOfCoordinates (fun j => if j = i then -1 else 0)

theorem charMap_unitFrequency_apply (i : Fin 4) (k : Torus4) :
    charMap (unitFrequency i) k = fourier 1 (torus4Coord k i) := by
  fin_cases i <;>
    simp [charMap, unitFrequency, pointOfCoordinates, latticeCharacter,
      torus4Coord]

theorem charSubalgebra_separatesPoints : charSubalgebra.SeparatesPoints := by
  classical
  intro k l hkl
  have hcoord : ∃ i : Fin 4, torus4Coord k i ≠ torus4Coord l i := by
    by_contra h
    push Not at h
    apply hkl
    cases k with
    | mk k0 k1 =>
      cases k1 with
      | mk k1 k2 =>
        cases k2 with
        | mk k2 k3 =>
          cases l with
          | mk l0 l1 =>
            cases l1 with
            | mk l1 l2 =>
              cases l2 with
              | mk l2 l3 =>
                apply Prod.ext
                · simpa [torus4Coord] using h 0
                · apply Prod.ext
                  · simpa [torus4Coord] using h 1
                  · apply Prod.ext
                    · simpa [torus4Coord] using h 2
                    · simpa [torus4Coord] using h 3
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨_, ⟨charMap (unitFrequency i), subset_adjoin ⟨unitFrequency i, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [charMap_unitFrequency_apply, charMap_unitFrequency_apply]
  rw [fourier_one, fourier_one]
  intro hcircleCoe
  have hcircle : AddCircle.toCircle (torus4Coord k i) =
      AddCircle.toCircle (torus4Coord l i) := Circle.coe_inj.mp hcircleCoe
  exact hi (AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hcircle)

theorem charSpan_dense : charSpan.topologicalClosure = ⊤ := by
  rw [← charSubalgebra_eq_span]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      charSubalgebra charSubalgebra_separatesPoints)


def linkCellAt (p : Fin 4 × LatticePoint) : LatticeCell 4 :=
  fun j => if j = p.1 then Sum.inr (latticePointCoordinate p.2 j)
    else Sum.inl (latticePointCoordinate p.2 j)

theorem latticeCellPoint_linkCellAt (p : Fin 4 × LatticePoint) :
    latticeCellPoint (linkCellAt p) = p.2 := by
  rcases p with ⟨i, ⟨a, ⟨b, ⟨c, d⟩⟩⟩⟩
  have hb (j : Fin 4) :
      latticeCellBaseCoordinate (linkCellAt (i, (a, (b, (c, d))))) j =
        latticePointCoordinate (a, (b, (c, d))) j := by
    by_cases hj : j = i <;> simp [linkCellAt, latticeCellBaseCoordinate, hj]
  simp only [latticeCellPoint]
  apply Prod.ext
  · simpa [latticePointCoordinate] using hb 0
  · apply Prod.ext
    · simpa [latticePointCoordinate] using hb 1
    · apply Prod.ext
      · simpa [latticePointCoordinate] using hb 2
      · simpa [latticePointCoordinate] using hb 3

theorem latticeCellAxes_linkCellAt (p : Fin 4 × LatticePoint) :
    latticeCellAxes (linkCellAt p) = {p.1} := by
  classical
  change Finset.univ.filter (fun j : Fin 4 =>
    latticeIsEdge (linkCellAt p j)) = {p.1}
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j = p.1 <;> simp [linkCellAt, latticeIsEdge, hj]

theorem latticeCellDegree_linkCellAt (p : Fin 4 × LatticePoint) :
    latticeCellDegree (linkCellAt p) = 1 := by
  have h := congrArg Finset.card (latticeCellAxes_linkCellAt p)
  simpa [latticeCellDegree, latticeCellAxes] using h

def linkCellEmbedding : (Fin 4 × LatticePoint) ↪ LatticeCell 4 where
  toFun := linkCellAt
  inj' := by
    intro p q hpq
    have haxes := congrArg latticeCellAxes hpq
    have hfirst : p.1 = q.1 := by
      rw [latticeCellAxes_linkCellAt, latticeCellAxes_linkCellAt] at haxes
      exact Finset.singleton_inj.mp haxes
    have hsecond : p.2 = q.2 := by
      have hpoint := congrArg latticeCellPoint hpq
      simpa [latticeCellPoint_linkCellAt] using hpoint
    exact Prod.ext hfirst hsecond

noncomputable def liftLinkCoefficients (c : (Fin 4 × LatticePoint) →₀ ℝ) :
    GlobalLinkField :=
  ⟨c.embDomain linkCellEmbedding, by
    intro cell hcell
    have hmem : cell ∈ c.support.map linkCellEmbedding := by
      simpa only [Finsupp.support_embDomain] using hcell
    rcases Finset.mem_map.mp hmem with ⟨p, hp, rfl⟩
    exact latticeCellDegree_linkCellAt p⟩

theorem linkCellAxis_iff (p : Fin 4 × LatticePoint) (i : Fin 4) :
    latticeLinkAxisCell (linkCellAt p) i ↔ p.1 = i := by
  constructor
  · intro hi
    have himem : i ∈ latticeCellAxes (linkCellAt p) := by
      simp [latticeCellAxes, hi.1]
    rw [latticeCellAxes_linkCellAt] at himem
    exact (Finset.mem_singleton.mp himem).symm
  · intro hpi
    subst i
    constructor
    · simp [linkCellAt, latticeIsEdge]
    · intro j hji hedge
      have hjmem : j ∈ latticeCellAxes (linkCellAt p) := by
        simp [latticeCellAxes, hedge]
      rw [latticeCellAxes_linkCellAt] at hjmem
      exact hji (Finset.mem_singleton.mp hjmem)

theorem liftLinkCoefficients_fourier (c : (Fin 4 × LatticePoint) →₀ ℝ)
    (i : Fin 4) (k : Torus4) :
    globalLinkFourierComponent (liftLinkCoefficients c) i k =
      ∑ p ∈ c.support.filter (fun p => p.1 = i),
        (c p : ℂ) * latticeCharacter p.2 k := by
  classical
  have hsupport : globalLinkAxisSupport (liftLinkCoefficients c) i =
      (c.support.filter (fun p => p.1 = i)).map linkCellEmbedding := by
    change (c.embDomain linkCellEmbedding).support.filter
      (fun cell => latticeLinkAxisCell cell i) = _
    rw [Finsupp.support_embDomain]
    ext cell
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, haxis⟩
      exact ⟨p, ⟨hp, (linkCellAxis_iff p i).mp haxis⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hpi⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, (linkCellAxis_iff p i).mpr hpi⟩
  unfold globalLinkFourierComponent
  rw [hsupport, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  have hcoef := Finsupp.embDomain_apply_self linkCellEmbedding c p
  have hpoint : latticeCellPoint (linkCellEmbedding p) = p.2 := by
    change latticeCellPoint (linkCellAt p) = p.2
    exact latticeCellPoint_linkCellAt p
  change (↑((c.embDomain linkCellEmbedding) (linkCellEmbedding p)) : ℂ) *
    latticeCharacter (latticeCellPoint (linkCellEmbedding p)) k = _
  rw [hcoef, hpoint]

private theorem finset_sum_finsupp_apply {α β γ : Type*} [DecidableEq β]
    [AddCommMonoid γ] (s : Finset α) (f : α → (β →₀ γ)) (x : β) :
    (∑ a ∈ s, f a) x = ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finsupp.add_apply]
      rw [ih]

noncomputable def realPartCoefficients (c : LatticePoint →₀ ℂ) :
    LatticePoint →₀ ℝ :=
  ∑ x ∈ c.support, Finsupp.single x (c x).re

theorem realPartCoefficients_apply (c : LatticePoint →₀ ℂ) (x : LatticePoint) :
    realPartCoefficients c x = (c x).re := by
  classical
  unfold realPartCoefficients
  rw [finset_sum_finsupp_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hne
    simp [hne.symm]
  · intro hnot
    have hzero : c x = 0 := by
      by_contra hne
      exact hnot (Finsupp.mem_support_iff.mpr hne)
    simp [hzero]

theorem realPartCoefficients_support_subset (c : LatticePoint →₀ ℂ) :
    (realPartCoefficients c).support ⊆ c.support := by
  intro x hx
  by_contra hnot
  have hzero : c x = 0 := Finsupp.notMem_support_iff.mp hnot
  simp [Finsupp.mem_support_iff, realPartCoefficients_apply, hzero] at hx

def complexFourierPoly (c : LatticePoint →₀ ℂ) : C(Torus4, ℂ) :=
  ∑ x ∈ c.support, c x • charMap x

def realFourierPoly (c : LatticePoint →₀ ℂ) : C(Torus4, ℂ) :=
  ∑ x ∈ c.support, (c x).re • charMap x

theorem latticeCharacter_torusNeg (x : LatticePoint) (k : Torus4) :
    latticeCharacter x (-k) = conj (latticeCharacter x k) := by
  unfold latticeCharacter
  simp

theorem realFourierPoly_symmetrization (c : LatticePoint →₀ ℂ) (k : Torus4) :
    realFourierPoly c k =
      (complexFourierPoly c k + conj (complexFourierPoly c (-k))) / 2 := by
  classical
  unfold realFourierPoly complexFourierPoly
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [map_sum]
  rw [add_div, Finset.sum_div, Finset.sum_div]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [map_mul]
  rw [Complex.real_smul]
  rw [Complex.re_eq_add_conj]
  simp [charMap, latticeCharacter_torusNeg]
  ring

theorem exists_complexFourierPoly_approx (f : C(Torus4, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : LatticePoint →₀ ℂ, ‖f - complexFourierPoly c‖ < ε := by
  have hf : f ∈ charSpan.topologicalClosure := by
    rw [charSpan_dense]
    exact Submodule.mem_top
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  refine ⟨c, ?_⟩
  rw [dist_eq_norm] at hdist
  have hpoly : complexFourierPoly c = g := by
    simpa [complexFourierPoly, Finsupp.sum] using hc
  rw [hpoly]
  exact hdist

theorem exists_realFourierPoly_approx (f : C(Torus4, ℂ))
    (hsym : ∀ k, f k = conj (f (-k))) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : LatticePoint →₀ ℂ, ‖f - realFourierPoly c‖ < ε := by
  obtain ⟨c, hc⟩ := exists_complexFourierPoly_approx f ε hε
  refine ⟨c, (f - realFourierPoly c).norm_lt_iff hε |>.2 ?_⟩
  intro k
  have hfirst : ‖complexFourierPoly c k - f k‖ < ε := by
    have hnorm := (f - complexFourierPoly c).norm_coe_le_norm k
    have hneg : ‖complexFourierPoly c k - f k‖ =
        ‖(f - complexFourierPoly c) k‖ := by
      calc
        _ = ‖-((f - complexFourierPoly c) k)‖ := by congr 1; simp
        _ = _ := norm_neg _
    rw [hneg]
    exact lt_of_le_of_lt hnorm hc
  have hsecond : ‖conj (complexFourierPoly c (-k)) - f k‖ < ε := by
    have hnorm := (f - complexFourierPoly c).norm_coe_le_norm (-k)
    have hconj : conj (complexFourierPoly c (-k)) - f k =
        conj (complexFourierPoly c (-k) - f (-k)) := by
      rw [hsym k, map_sub]
    rw [hconj, Complex.norm_conj]
    have hneg : ‖complexFourierPoly c (-k) - f (-k)‖ =
        ‖(f - complexFourierPoly c) (-k)‖ := by
      calc
        _ = ‖-((f - complexFourierPoly c) (-k))‖ := by congr 1; simp
        _ = _ := norm_neg _
    rw [hneg]
    exact lt_of_le_of_lt hnorm hc
  have hrepr : realFourierPoly c k - f k =
      ((complexFourierPoly c k - f k) +
        (conj (complexFourierPoly c (-k)) - f k)) / 2 := by
    rw [realFourierPoly_symmetrization, hsym k]
    ring
  have hnorm : ‖f k - realFourierPoly c k‖ =
      ‖realFourierPoly c k - f k‖ := by
    calc
      _ = ‖-(realFourierPoly c k - f k)‖ := by congr 1; ring
      _ = _ := norm_neg _
  have hreverse : ‖realFourierPoly c k - f k‖ < ε := by
    rw [hrepr]
    calc
      _ = ‖(complexFourierPoly c k - f k) +
          (conj (complexFourierPoly c (-k)) - f k)‖ / 2 := by
        rw [norm_div]
        norm_num
      _ ≤ (‖complexFourierPoly c k - f k‖ +
        ‖conj (complexFourierPoly c (-k)) - f k‖) / 2 := by
        gcongr
        exact norm_add_le _ _
      _ < ε := by linarith
  simpa only [ContinuousMap.sub_apply] using (hnorm ▸ hreverse)

noncomputable def pairAxisEmbedding (i : Fin 4) :
    LatticePoint ↪ Fin 4 × LatticePoint where
  toFun x := (i, x)
  inj' := by intro x y h; exact congrArg Prod.snd h


noncomputable def realFamilyPairCoefficients
    (c : Fin 4 → LatticePoint →₀ ℂ) : (Fin 4 × LatticePoint) →₀ ℝ :=
  ∑ i : Fin 4,
    (realPartCoefficients (c i)).embDomain (pairAxisEmbedding i)

theorem realFamilyPairCoefficients_apply
    (c : Fin 4 → LatticePoint →₀ ℂ) (i : Fin 4) (x : LatticePoint) :
    realFamilyPairCoefficients c (i, x) = (c i x).re := by
  classical
  unfold realFamilyPairCoefficients
  change (∑ j : Fin 4,
      (realPartCoefficients (c j)).embDomain (pairAxisEmbedding j))
      (pairAxisEmbedding i x) = _
  rw [finset_sum_finsupp_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finsupp.embDomain_apply_self, realPartCoefficients_apply]
  · intro j hj hji
    have hnot : pairAxisEmbedding i x ∉ Set.range (pairAxisEmbedding j) := by
      rintro ⟨y, hy⟩
      have hfst := congrArg Prod.fst hy
      exact hji hfst
    rw [Finsupp.embDomain_of_notMem_range _ _ _ hnot]
  · intro hnot
    simp at hnot

theorem realFamilyPairCoefficients_support_slice
    (c : Fin 4 → LatticePoint →₀ ℂ) (i : Fin 4) :
    (realFamilyPairCoefficients c).support.filter (fun p => p.1 = i) =
      ((realPartCoefficients (c i)).support.map (pairAxisEmbedding i)) := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨hp, hpi⟩
    refine ⟨p.2, ?_, ?_⟩
    · rw [Finsupp.mem_support_iff]
      have hp0 := Finsupp.mem_support_iff.mp hp
      rw [realFamilyPairCoefficients_apply] at hp0
      have hreal : (c i p.2).re ≠ 0 := by
        simpa [hpi] using hp0
      simpa [realPartCoefficients_apply] using hreal
    · exact Prod.ext hpi.symm rfl
  · rintro ⟨x, hx, rfl⟩
    constructor
    · rw [Finsupp.mem_support_iff]
      change realFamilyPairCoefficients c (i, x) ≠ 0
      rw [realFamilyPairCoefficients_apply]
      have hreal := Finsupp.mem_support_iff.mp hx
      rw [realPartCoefficients_apply] at hreal
      exact hreal
    · rfl

theorem liftRealFamily_fourier
    (c : Fin 4 → LatticePoint →₀ ℂ) (i : Fin 4) (k : Torus4) :
    globalLinkFourierComponent
      (liftLinkCoefficients (realFamilyPairCoefficients c)) i k =
        realFourierPoly (c i) k := by
  rw [liftLinkCoefficients_fourier, realFamilyPairCoefficients_support_slice]
  rw [Finset.sum_map]
  calc
    _ = ∑ x ∈ (realPartCoefficients (c i)).support,
        (↑((c i x).re) : ℂ) * latticeCharacter x k := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp only [pairAxisEmbedding, Function.Embedding.coeFn_mk]
      rw [realFamilyPairCoefficients_apply]
    _ = ∑ x ∈ (c i).support,
        (↑((c i x).re) : ℂ) * latticeCharacter x k := by
      apply Finset.sum_subset (realPartCoefficients_support_subset (c i))
      intro x hx hnot
      have hzero : (c i x).re = 0 := by
        have hz : realPartCoefficients (c i) x = 0 :=
          Finsupp.notMem_support_iff.mp hnot
        simpa [realPartCoefficients_apply] using hz
      simp [hzero]
    _ = realFourierPoly (c i) k := by
      simp [realFourierPoly, charMap]

end
end FourierApproximation
