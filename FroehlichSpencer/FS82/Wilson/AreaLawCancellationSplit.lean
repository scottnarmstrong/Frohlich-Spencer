/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawComponentSplit
public import FroehlichSpencer.FS82.Wilson.AreaLawCancellation
public import FroehlichSpencer.FS82.Wilson.AreaLawProjection
public import FroehlichSpencer.FS82.Wilson.AreaLawSource

/-!
# Source-component cancellation for a rectangular loop

Select one connected support component carrying the full loop. Its complement
has zero boundary, so the positive remainder sum is bounded by the vacuum
partition sum.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

private theorem areaLaw_exists_nonzero_sum_term {α : Type*}
    (s : Finset α) (f : α → ℤ) (h : (∑ x ∈ s, f x) ≠ 0) :
    ∃ x ∈ s, f x ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply Finset.sum_eq_zero
  intro x hx
  exact hn x hx

noncomputable def rectangleSourceComponent {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    (nonzeroPlaquetteGraph m).ConnectedComponent :=
  Classical.choose (exists_plaquetteModeComponent_with_source_boundary
    hL hT hLpos hTpos m hsource)

theorem rectangleSourceComponent_boundary {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    boundary (plaquetteModeChain
      (plaquetteModeComponentField m
        (rectangleSourceComponent hL hT hLpos hTpos m hsource))) =
      wilsonRectangleLoop L T hL hT :=
  Classical.choose_spec (exists_plaquetteModeComponent_with_source_boundary
    hL hT hLpos hTpos m hsource)

theorem rectangleSourceComponent_remainder_divergence_zero {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    plaquetteModeDivergence
      (plaquetteModeComponentRemainder m
        (rectangleSourceComponent hL hT hLpos hTpos m hsource)) = 0 := by
  let c := rectangleSourceComponent hL hT hLpos hTpos m hsource
  have htotal : boundary (plaquetteModeChain m) =
      wilsonRectangleLoop L T hL hT :=
    (plaquetteModeDivergence_eq_boundary m
      (wilsonRectangleSheet L T hL hT)
      (wilsonRectangleSheet_homogeneousSupport hL hT)).mp hsource
  have hsum :
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
        boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
        boundary (plaquetteModeChain m) := by
    rw [← map_add, ← plaquetteModeChain_eq_component_add_remainder]
  have hsplit :
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
        boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
    wilsonRectangleLoop L T hL hT := by
    calc
      _ = boundary (plaquetteModeChain m) := hsum
      _ = wilsonRectangleLoop L T hL hT := htotal
  rw [rectangleSourceComponent_boundary hL hT hLpos hTpos m hsource] at hsplit
  have hrem : boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) = 0 := by
    have hcancel :
        wilsonRectangleLoop L T hL hT +
            boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
          wilsonRectangleLoop L T hL hT + (0 : Chain 4 B) := by
      simpa using hsplit
    exact add_left_cancel hcancel
  have hdiv := (plaquetteModeDivergence_eq_boundary
    (plaquetteModeComponentRemainder m c) 0 (by
      intro x hx
      simp at hx)).2 (by simpa using hrem)
  have hdiv' :
      plaquetteModeDivergence (plaquetteModeComponentRemainder m c) =
        primalSheetLoopFrequency (0 : Chain 4 B) := by
    simpa [c] using hdiv
  have hfreqzero : primalSheetLoopFrequency (0 : Chain 4 B) = 0 := by
    funext l
    simp [primalSheetLoopFrequency]
  exact hdiv'.trans hfreqzero

theorem dualGaussianProduct_mul_of_disjoint_support {B : Box 4}
    (β : ℝ) (m n : PrimalPlaquettes B → ℤ)
    (hdisj : Disjoint (plaquetteFieldSupport m) (plaquetteFieldSupport n)) :
    dualGaussianProduct β (m + n) =
      dualGaussianProduct β m * dualGaussianProduct β n := by
  classical
  unfold dualGaussianProduct
  calc
    (∏ p : PrimalPlaquettes B,
        Real.exp (-(((m + n) p : ℤ) : ℝ) ^ 2 / (2 * β))) =
      ∏ p : PrimalPlaquettes B,
        (Real.exp (-(m p : ℝ) ^ 2 / (2 * β)) *
          Real.exp (-(n p : ℝ) ^ 2 / (2 * β))) := by
            apply Finset.prod_congr rfl
            intro p hp
            have hnot : ¬(m p ≠ 0 ∧ n p ≠ 0) := by
              intro hboth
              have hm : p ∈ plaquetteFieldSupport m := by
                simp [plaquetteFieldSupport, hboth.1]
              have hn : p ∈ plaquetteFieldSupport n := by
                simp [plaquetteFieldSupport, hboth.2]
              exact (Finset.disjoint_left.mp hdisj) hm hn
            change Real.exp (-(((m p + n p : ℤ) : ℝ) ^ 2) / (2 * β)) = _
            push_cast
            rw [← Real.exp_add]
            congr 1
            by_cases hm : m p = 0
            · simp [hm]
            · have hn : n p = 0 := by
                by_contra hne
                exact hnot ⟨hm, hne⟩
              simp [hn]
    _ = (∏ p : PrimalPlaquettes B,
          Real.exp (-(m p : ℝ) ^ 2 / (2 * β))) *
        (∏ p : PrimalPlaquettes B,
          Real.exp (-(n p : ℝ) ^ 2 / (2 * β))) := by
            rw [Finset.prod_mul_distrib]

theorem rectangleSourceComponent_support_has_rootedAnimal {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    ∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
      plaquetteModeComponentSupport m
        (rectangleSourceComponent hL hT hLpos hTpos m hsource) ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteModeComponentSupport m
              (rectangleSourceComponent hL hT hLpos hTpos m hsource)).card := by
  classical
  let c := rectangleSourceComponent hL hT hLpos hTpos m hsource
  let f := plaquetteModeComponentField m c
  let q := boundary (plaquetteModeChain f)
  have hq : q = wilsonRectangleLoop L T hL hT := by
    exact rectangleSourceComponent_boundary hL hT hLpos hTpos m hsource
  have hloopPair := areaTestPotential_pairing_wilsonRectangleLoop hL hT
  have hloopNe : wilsonRectangleLoop L T hL hT ≠ 0 := by
    intro hzero
    have hzeroPair : integerCellPairing areaTestPotential
        (wilsonRectangleLoop L T hL hT) = 0 := by simp [hzero]
    rw [hzeroPair] at hloopPair
    have harea : (L * T : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hLpos hTpos))
    exact harea hloopPair.symm
  obtain ⟨l, hl⟩ := Finsupp.support_nonempty_iff.mpr hloopNe
  have hloopCoeff : (wilsonRectangleLoop L T hL hT) l ≠ 0 :=
    Finsupp.mem_support_iff.mp hl
  have hqCoeff : q l ≠ 0 := by simpa [hq] using hloopCoeff
  have hdeg : cellDegree l = 1 :=
    integerBoundary_homogeneousSupport (plaquetteModeChain f) 2 (by omega)
      (plaquetteModeChain_homogeneousSupport f) l
      (Finsupp.mem_support_iff.mpr hqCoeff)
  let link : PrimalLinks B := ⟨l, hdeg⟩
  have hsheetLink : link ∈ rectangleBoundaryLinks L T hL hT := by
    simp only [rectangleBoundaryLinks, Finset.mem_filter, Finset.mem_univ, true_and]
    change (boundary (wilsonRectangleSheet L T hL hT)) l ≠ 0
    rw [← wilsonRectangleLoop]
    exact hloopCoeff
  have hchainEq : plaquetteModeChain f =
      plaquetteFieldChainOnSet m (plaquetteModeComponentSupport m c) := by
    simpa [f] using plaquetteModeComponentField_chain_eq_set m c
  have hcoeff :
      (boundary (plaquetteFieldChainOnSet m (plaquetteModeComponentSupport m c))) l ≠ 0 := by
    rw [← hchainEq]
    exact hqCoeff
  have hcoeffLink :
      (boundary (plaquetteFieldChainOnSet m
        (plaquetteModeComponentSupport m c))) link.1 ≠ 0 := by
    simpa [link] using hcoeff
  rw [plaquetteFieldChainOnSet_boundary_coeff] at hcoeffLink
  obtain ⟨p, hp, hpterm⟩ := areaLaw_exists_nonzero_sum_term
    (plaquetteModeComponentSupport m c)
    (fun p => m p * (boundary (Finsupp.single p.1 (1 : ℤ))) link.1) hcoeffLink
  have hpBoundary : (boundary (Finsupp.single p.1 (1 : ℤ))) link.1 ≠ 0 := by
    intro hz
    simp [hz] at hpterm
  have hroot : p ∈ rectangleSourceRootPlaquettes L T hL hT := by
    rw [rectangleSourceRootPlaquettes]
    apply Finset.mem_biUnion.mpr
    refine ⟨link, hsheetLink, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      plaquetteBoundaryLinks]
    exact hpBoundary
  refine ⟨p, hroot, ?_⟩
  simpa [c] using plaquetteModeComponentSupport_mem_animals m c hp

private theorem component_remainder_support_disjoint {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    Disjoint (plaquetteFieldSupport (plaquetteModeComponentField m c))
      (plaquetteFieldSupport (plaquetteModeComponentRemainder m c)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpcomp hprem
  have hcompval : plaquetteModeComponentField m c p ≠ 0 :=
    (Finset.mem_filter.mp hpcomp).2
  have hremval : plaquetteModeComponentRemainder m c p ≠ 0 :=
    (Finset.mem_filter.mp hprem).2
  have hcomp : p ∈ plaquetteModeComponentSupport m c := by
    by_contra hnot
    simp [plaquetteModeComponentField, hnot] at hcompval
  have hnot : p ∉ plaquetteModeComponentSupport m c := by
    intro hmem
    simp [plaquetteModeComponentRemainder, hmem] at hremval
  exact hnot hcomp

/-- The finite source partition sum is bounded by the sum over one rooted
connected source component times the unrestricted vacuum partition sum. -/
theorem dualWilsonPartition_le_rectangleSourceClusters_mul_vacuum
    {B : Box 4} {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T) (β : ℝ) (hβ : 0 < β) :
    dualWilsonPartition (B := B) β (wilsonRectangleSheet L T hL hT) ≤
      (∑' c : {a : PrimalPlaquettes B → ℤ //
        plaquetteModeDivergence a =
          primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT) ∧
        ∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
          plaquetteFieldSupport a ∈
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
              (plaquetteFieldSupport a).card},
        dualGaussianProduct β c.1) *
        dualWilsonPartition (B := B) β (0 : Chain 4 B) := by
  let X : Type := {m : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)}
  let C : (PrimalPlaquettes B → ℤ) → Prop := fun a =>
    ∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
      plaquetteFieldSupport a ∈
        FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
          (plaquetteFieldSupport a).card
  let pick (x : X) : (nonzeroPlaquetteGraph x.1).ConnectedComponent :=
    rectangleSourceComponent hL hT hLpos hTpos x.1 (by simpa [X] using x.2)
  let comp (x : X) : PrimalPlaquettes B → ℤ :=
    plaquetteModeComponentField x.1 (pick x)
  let rem (x : X) : PrimalPlaquettes B → ℤ :=
    plaquetteModeComponentRemainder x.1 (pick x)
  let P : Type := {a : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence a =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT) ∧ C a}
  let split : X → P × (PrimalPlaquettes B → ℤ) := fun x =>
    (⟨comp x, ⟨by
      apply (plaquetteModeDivergence_eq_boundary (comp x)
        (wilsonRectangleSheet L T hL hT)
        (wilsonRectangleSheet_homogeneousSupport hL hT)).2
      simpa [comp, pick, X, wilsonRectangleLoop] using
        rectangleSourceComponent_boundary hL hT hLpos hTpos x.1 x.2,
      by
        obtain ⟨p, hp, ha⟩ := rectangleSourceComponent_support_has_rootedAnimal
          hL hT hLpos hTpos x.1 x.2
        exact ⟨p, hp, by
          simpa [comp, pick, X, plaquetteModeComponentField_support] using ha⟩⟩⟩,
      rem x)
  have hinj : Function.Injective split := by
    intro x y hxy
    apply Subtype.ext
    have hcomp : comp x = comp y := congrArg (fun z : P × _ => z.1.1) hxy
    have hrem : rem x = rem y := congrArg Prod.snd hxy
    have hxadd : comp x + rem x = x.1 := by
      simpa [comp, rem, pick] using
        plaquetteModeComponentField_add_remainder x.1 (pick x)
    have hyadd : comp y + rem y = y.1 := by
      simpa [comp, rem, pick] using
        plaquetteModeComponentField_add_remainder y.1 (pick y)
    calc
      x.1 = comp x + rem x := hxadd.symm
      _ = comp y + rem y := by rw [hcomp, hrem]
      _ = y.1 := hyadd
  have hfactor (x : X) :
      dualGaussianProduct β x.1 =
        dualGaussianProduct β (split x).1.1 *
          dualWilsonTerm β (0 : Chain 4 B) (split x).2 := by
    have hadd : comp x + rem x = x.1 := by
      simpa [comp, rem, pick] using
        plaquetteModeComponentField_add_remainder x.1 (pick x)
    have hdivrem : plaquetteModeDivergence (rem x) = 0 := by
      simpa [rem, pick, X] using
        rectangleSourceComponent_remainder_divergence_zero
          hL hT hLpos hTpos x.1 x.2
    have hfreqzero : primalSheetLoopFrequency (0 : Chain 4 B) = 0 := by
      funext l
      simp [primalSheetLoopFrequency]
    have hterm0 :
        plaquetteModeDivergence (rem x) =
          primalSheetLoopFrequency (0 : Chain 4 B) := by
      rw [hdivrem, hfreqzero]
    have hprod := dualGaussianProduct_mul_of_disjoint_support β
      (comp x) (rem x) (by
        simpa [comp, rem, pick] using
          component_remainder_support_disjoint x.1 (pick x))
    rw [← hadd]
    simpa [split, dualWilsonTerm, hterm0] using hprod
  exact dualWilsonPartition_le_sourceCluster_mul_vacuum
    β hβ (wilsonRectangleSheet L T hL hT) C split hinj hfactor

end FroehlichSpencer.FS82.Wilson

end
