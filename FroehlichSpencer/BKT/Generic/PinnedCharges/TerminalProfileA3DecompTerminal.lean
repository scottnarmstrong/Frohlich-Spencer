/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3DecompInduction
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3CertTerminal

/-! # Terminal max-scale decomposition for collapsed profiles

The finite overlap-graph induction is specialized to the collapse family of every charged selected
square on a comb terminal.  A lattice neighborhood is internally connected by paths that remain
inside its Euclidean thickening.  Therefore overlap-graph components correspond exactly to the
zero-cost components of the collapsed lattice graph, and the induction gives the consumer's
`TerminalProfileA3UniqueMaxDecompositionLarge` statement.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

private theorem profileA3_ballReachable
    (𝓔 : Finset (Finset (Site L))) (E : Finset (Site L)) (hE : E ∈ 𝓔)
    (S : Finset (Site L)) (a : Site L) (ha : a ∈ S) (R : ℝ)
    {x : Site L} (hxd : euclideanSiteDistance x a ≤ R)
    (hEeq : E = boundaryEnergyNeighborhood R S) :
    (profileFreeGraph 𝓔).Reachable x a := by
  have aux : ∀ n, ∀ x : Site L, l1 x a = n →
      euclideanSiteDistance x a ≤ R → (profileFreeGraph 𝓔).Reachable x a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hlen hdist
      have hdist' : euclideanSiteDistance a x ≤ R := by
        rw [siteDist_comm]
        exact hdist
      by_cases hxa : x = a
      · subst x
        exact SimpleGraph.Reachable.rfl
      · obtain ⟨z, hxz, hzn, hzd⟩ := exists_step_toward hxa
        have hlt : l1 z a < n := by omega
        have hzd' : euclideanSiteDistance z a ≤ R := hzd.trans hdist
        have hxE : x ∈ E := by
          rw [hEeq, mem_boundaryEnergyNeighborhood_iff]
          exact ⟨a, ha, hdist'⟩
        have hzE : z ∈ E := by
          rw [hEeq, mem_boundaryEnergyNeighborhood_iff]
          have hzd'' : euclideanSiteDistance a z ≤ R := by
            rw [siteDist_comm]
            exact hzd'
          exact ⟨a, ha, hzd''⟩
        have hadj : (profileFreeGraph 𝓔).Adj x z := by
          exact ⟨hxz, ⟨E, hE, hxE, hzE⟩⟩
        exact (SimpleGraph.Adj.reachable hadj).trans (ih (l1 z a) hlt z rfl hzd')
  exact aux (l1 x a) x rfl hxd

private theorem profileA3_neutralNeighborhood_reachable
    (𝓔 : Finset (Finset (Site L))) (σ : ChargeDensity L)
    (hE : profileA3NeutralNeighborhood σ ∈ 𝓔) {x y : Site L}
    (hx : x ∈ profileA3NeutralNeighborhood σ)
    (hy : y ∈ profileA3NeutralNeighborhood σ) :
    (profileFreeGraph 𝓔).Reachable x y := by
  let R := 8 * boundaryAdjustedSize σ + 2
  obtain ⟨a, ha, hxa⟩ := (mem_boundaryEnergyNeighborhood_iff R
    (chargeSupport σ) x).mp (by simpa [R, profileA3NeutralNeighborhood] using hx)
  obtain ⟨b, hb, hyb⟩ := (mem_boundaryEnergyNeighborhood_iff R
    (chargeSupport σ) y).mp (by simpa [R, profileA3NeutralNeighborhood] using hy)
  have hab : euclideanSiteDistance a b ≤ boundaryAdjustedSize σ := by
    exact (siteDist_le_diam ha hb).trans (chargeEuclideanDiameter_le_boundaryAdjustedSize σ)
  have hbound : boundaryAdjustedSize σ ≤ R := by
    dsimp [R]
    linarith [boundaryAdjustedSize_nonneg σ]
  have hxa' := profileA3_ballReachable 𝓔 (profileA3NeutralNeighborhood σ) hE
    (chargeSupport σ) a ha R (by rw [siteDist_comm]; exact hxa) (by rfl)
  have hab' := profileA3_ballReachable 𝓔 (profileA3NeutralNeighborhood σ) hE
    (chargeSupport σ) a ha R (by rw [siteDist_comm]; exact hab.trans hbound) (by rfl)
  have hyb' := profileA3_ballReachable 𝓔 (profileA3NeutralNeighborhood σ) hE
    (chargeSupport σ) b hb R (by rw [siteDist_comm]; exact hyb) (by rfl)
  exact hxa'.trans (hab'.symm.trans hyb'.symm)

private theorem profileA3_collapsedComponent_eq_overlapUnion
    (F : Finset (ChargeDensity L)) (y : Site L)
    (σ : ChargeDensity L) (hσ : σ ∈ F)
    (hy : y ∈ profileA3NeutralNeighborhood σ) :
    collapsedComponent (F.image profileA3NeutralNeighborhood) y =
      profileA3LabelUnion (fun a : {τ : ChargeDensity L // τ ∈ F} => a.val)
        (profileA3GraphComponentVertices
          ((profileA3OverlapGraph F).connectedComponentMk ⟨σ, hσ⟩)) := by
  classical
  let 𝓔 := F.image profileA3NeutralNeighborhood
  let G := profileA3OverlapGraph F
  let a : {τ : ChargeDensity L // τ ∈ F} := ⟨σ, hσ⟩
  let c := G.connectedComponentMk a
  have hEσ : profileA3NeutralNeighborhood σ ∈ 𝓔 :=
    Finset.mem_image.mpr ⟨σ, hσ, rfl⟩
  have hforward : ∀ {x}, x ∈ collapsedComponent 𝓔 y →
      x ∈ profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F} => t.val)
        (profileA3GraphComponentVertices c) := by
    intro x hx
    have hreach := mem_collapsedComponent.mp hx
    let P : Site L → Prop := fun z =>
      ∃ t : {τ : ChargeDensity L // τ ∈ F},
        z ∈ profileA3NeutralNeighborhood t.val ∧ G.connectedComponentMk t = c
    have hstart : P y := ⟨a, hy, rfl⟩
    have hstep : ∀ ⦃u v⦄, P u → (profileFreeGraph 𝓔).Adj u v → P v := by
      intro u v hu huv
      rcases hu with ⟨t, hut, htc⟩
      obtain ⟨-, hc⟩ := huv
      obtain ⟨E, hE, huE, hvE⟩ := hc
      obtain ⟨τ, hτ, hEeq⟩ := Finset.mem_image.mp hE
      have huτ : u ∈ profileA3NeutralNeighborhood τ := by simpa [hEeq] using huE
      have hvτ : v ∈ profileA3NeutralNeighborhood τ := by simpa [hEeq] using hvE
      let t' : {τ : ChargeDensity L // τ ∈ F} := ⟨τ, hτ⟩
      have htc' : G.connectedComponentMk t' = c := by
        by_cases heq : t.val = τ
        · have hnodes : t = t' := Subtype.ext heq
          simpa [hnodes] using htc
        · have hadj : G.Adj t t' :=
            ⟨heq, ⟨u, Finset.mem_inter.mpr ⟨hut, huτ⟩⟩⟩
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans htc
      exact ⟨t', hvτ, htc'⟩
    have hxP := hreach.elim fun p => profileA3_walk_preserves hstep p hstart
    rcases hxP with ⟨t, hxt, htc⟩
    exact Finset.mem_biUnion.mpr ⟨t, (mem_profileA3GraphComponentVertices c t).mpr htc, hxt⟩
  have hbackward : ∀ {x},
      x ∈ profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F} => t.val)
        (profileA3GraphComponentVertices c) → x ∈ collapsedComponent 𝓔 y := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨t, htC, hxt⟩
    have hnodes : G.connectedComponentMk t = c :=
      (mem_profileA3GraphComponentVertices c t).mp htC
    have hpath : G.Reachable a t := by
      apply SimpleGraph.ConnectedComponent.eq.mp
      exact rfl.trans hnodes.symm
    let P : {τ : ChargeDensity L // τ ∈ F} → Prop := fun u =>
      ∀ z, z ∈ profileA3NeutralNeighborhood u.val →
        (profileFreeGraph 𝓔).Reachable y z
    have hstart : P a := by
      intro z hz
      exact profileA3_neutralNeighborhood_reachable 𝓔 σ hEσ hy hz
    have hstep : ∀ ⦃u v⦄, P u → G.Adj u v → P v := by
      intro u v hu huv z hz
      obtain ⟨q, hq⟩ := huv.2
      have hEv : profileA3NeutralNeighborhood v.val ∈ 𝓔 :=
        Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩
      have hyq := hu q (Finset.mem_inter.mp hq).1
      have hqz := profileA3_neutralNeighborhood_reachable 𝓔 v.val hEv
        (Finset.mem_inter.mp hq).2 hz
      exact hyq.trans hqz
    have htx := hpath.elim fun p => profileA3_walk_preserves hstep p hstart
    have hyx := htx x hxt
    exact mem_collapsedComponent.mpr hyx
  ext x
  constructor
  · exact hforward
  · exact hbackward

set_option linter.style.haveILetI false in
theorem terminalProfileA3UniqueMaxDecompositionLarge :
    TerminalProfileA3UniqueMaxDecompositionLarge := by
  classical
  intro L N T hT ρ hρ j hj s hs hq
  let K := chargeSupport (chargeRestriction ρ s)
  let F := profileCollapseFamily T.F ρ j K
  letI : Fintype {σ : ChargeDensity L // σ ∈ F} := profileA3FamilyFintype F
  intro y hy
  obtain ⟨E, hE, hyE⟩ := hy
  obtain ⟨σ, hσ, hEeq⟩ := Finset.mem_image.mp hE
  have hyσ : y ∈ profileA3NeutralNeighborhood σ := by simpa [hEeq] using hyE
  have hzero : ∀ t : {τ : ChargeDensity L // τ ∈ F}, t.val ≠ 0 := by
    intro t
    exact hT.geometry.ensemble.1 t.val (Finset.mem_filter.mp t.property).1
  have hAdj : ∀ ⦃u v : {τ : ChargeDensity L // τ ∈ F}⦄,
      (profileA3OverlapGraph F).Adj u v →
        (profileA3NeutralNeighborhood u.val ∩ profileA3NeutralNeighborhood v.val).Nonempty :=
    fun _ _ huv => huv.2
  have hsep : ∀ ⦃u v : {τ : ChargeDensity L // τ ∈ F}⦄, u ≠ v →
      (65536 : ℝ) * min (boundaryAdjustedSize u.val) (boundaryAdjustedSize v.val) ^
          (7 / 4 : ℝ) ≤
        euclideanSetDistance (chargeSupport u.val) (chargeSupport v.val) := by
    intro u v huv
    have hval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    have hpair := hT.geometry.separated u.val (Finset.mem_filter.mp u.property).1
      v.val (Finset.mem_filter.mp v.property).1 hval
    simpa [chargeCoverScale_eq,
      (show chargeCoverExponent = (7 / 4 : ℝ) from rfl)] using hpair
  let G := profileA3OverlapGraph F
  let a : {τ : ChargeDensity L // τ ∈ F} := ⟨σ, hσ⟩
  let c := G.connectedComponentMk a
  have hdecomp := profileA3_separated_component_decomposition_strong
    (profileA3GraphComponentVertices c).card (fun t : {τ : ChargeDensity L // τ ∈ F} => t.val)
    Subtype.val_injective G hAdj hzero hsep c rfl
  have hCeq : collapsedComponent (profileCollapsedSets T.F ρ j K) y =
      profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F} => t.val)
        (profileA3GraphComponentVertices c) := by
    have hgraph := profileA3_collapsedComponent_eq_overlapUnion F y σ hσ hyσ
    change collapsedComponent (F.image profileA3NeutralNeighborhood) y =
      profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F} => t.val)
        (profileA3GraphComponentVertices (G.connectedComponentMk a))
    exact hgraph
  obtain ⟨v, hv, hvmax, hvsmall, pieces, hcover, hpiecesdiam, hpiecesattach, hdiam⟩ := hdecomp
  rw [hCeq, hcover]
  exact ⟨v.val, v.property, pieces, rfl, hpiecesdiam, hpiecesattach⟩

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
