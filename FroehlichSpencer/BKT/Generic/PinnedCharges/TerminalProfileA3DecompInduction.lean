/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3DecompGeometry

/-! # Strong induction for separated neighborhood components -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The site union of a finite family of neighborhood labels. -/
def profileA3LabelUnion {V : Type*} [DecidableEq V] (label : V → ChargeDensity L)
    (S : Finset V) : Finset (Site L) :=
  S.biUnion fun v => profileA3NeutralNeighborhood (label v)

/-- Removing the vertices of scale at least `D/10` leaves the graph of low-only paths. -/
def profileA3TrimGraph {V : Type*} (G : SimpleGraph V) (label : V → ChargeDensity L)
    (D : ℝ) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ boundaryAdjustedSize (label v) < D / 10 ∧
    boundaryAdjustedSize (label w) < D / 10
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro v h
    exact G.loopless.irrefl v h.1⟩

theorem profileA3_trimGraph_le {V : Type*} (G : SimpleGraph V)
    (label : V → ChargeDensity L) (D : ℝ) : profileA3TrimGraph G label D ≤ G :=
  fun _ _ h => h.1

private theorem profileA3_trimWalk_low_end {V : Type*} (G : SimpleGraph V)
    (label : V → ChargeDensity L) (D : ℝ) {u v : V}
    (p : (profileA3TrimGraph G label D).Walk u v)
    (hu : boundaryAdjustedSize (label u) < D / 10) :
    boundaryAdjustedSize (label v) < D / 10 := by
  induction p with
  | nil => exact hu
  | @cons a b d hab q ih => exact ih hab.2.2

/-- Every vertex in a trimmed connected component is low once one vertex is low. -/
theorem profileA3_trimComponent_all_low {V : Type*} [Fintype V]
    (G : SimpleGraph V) (label : V → ChargeDensity L) (D : ℝ)
    (c : (profileA3TrimGraph G label D).ConnectedComponent)
    {u : V} (hu : u ∈ c.supp)
    {v : V} (hv : v ∈ c.supp)
    (huLow : boundaryAdjustedSize (label u) < D / 10) :
    boundaryAdjustedSize (label v) < D / 10 := by
  have huc : (profileA3TrimGraph G label D).connectedComponentMk u = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c u).mp hu
  have hvc : (profileA3TrimGraph G label D).connectedComponentMk v = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp hv
  have hreach : (profileA3TrimGraph G label D).Reachable u v :=
    (SimpleGraph.ConnectedComponent.eq).mp (huc.trans hvc.symm)
  exact hreach.elim fun p => profileA3_trimWalk_low_end G label D p huLow

/-- An invariant holding at the start of a walk and preserved by every edge holds at its end. -/
theorem profileA3_walk_preserves {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (hstep : ∀ ⦃u v⦄, P u → G.Adj u v → P v) {u v : V}
    (p : G.Walk u v) (hu : P u) : P v := by
  induction p with
  | nil => exact hu
  | @cons a b c hab q ih => exact ih (hstep hu hab)

/-- The decomposition data supplied for one connected component. -/
def ProfileA3ComponentDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (label : V → ChargeDensity L)
    (c : G.ConnectedComponent) : Prop :=
  ∃ v ∈ c.supp,
    (∀ w ∈ c.supp, boundaryAdjustedSize (label w) ≤ boundaryAdjustedSize (label v)) ∧
    (∀ w ∈ c.supp, w ≠ v →
      boundaryAdjustedSize (label w) < boundaryAdjustedSize (label v) / 10) ∧
    ∃ pieces : Finset (Finset (Site L)),
      profileA3LabelUnion label (profileA3GraphComponentVertices c) =
        profileA3NeutralNeighborhood (label v) ∪ pieces.biUnion id ∧
      (∀ S ∈ pieces, ∀ x ∈ S, ∀ y ∈ S,
        profileA3GraphLength x y ≤ 4 * boundaryAdjustedSize (label v)) ∧
      (∀ S ∈ pieces, ∃ z ∈ S, ∃ u ∈ profileA3NeutralNeighborhood (label v),
        profileA3GraphLength z u ≤ 1) ∧
      (∀ x ∈ profileA3LabelUnion label (profileA3GraphComponentVertices c),
        ∀ y ∈ profileA3LabelUnion label (profileA3GraphComponentVertices c),
          profileA3GraphLength x y ≤ 40 * boundaryAdjustedSize (label v))

theorem profileA3_separated_component_decomposition_strong
    (n : ℕ) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (label : V → ChargeDensity L) (_hinj : Function.Injective label)
      (G : SimpleGraph V)
      (_hAdj : ∀ ⦃u v⦄, G.Adj u v →
        (profileA3NeutralNeighborhood (label u) ∩
          profileA3NeutralNeighborhood (label v)).Nonempty)
      (_hzero : ∀ v, label v ≠ 0)
      (_hsep : ∀ ⦃u v⦄, u ≠ v →
        (65536 : ℝ) * min (boundaryAdjustedSize (label u))
          (boundaryAdjustedSize (label v)) ^ (7 / 4 : ℝ) ≤
          euclideanSetDistance (chargeSupport (label u)) (chargeSupport (label v)))
      (c : G.ConnectedComponent),
      (profileA3GraphComponentVertices c).card = n →
        ProfileA3ComponentDecomposition G label c := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V instV instDec label hinj G hAdj hzero hsep c hc
      classical
      let C := profileA3GraphComponentVertices c
      have hCne : C.Nonempty := by
        obtain ⟨v, hv⟩ := SimpleGraph.ConnectedComponent.nonempty_supp c
        refine ⟨v, ?_⟩
        apply (mem_profileA3GraphComponentVertices c v).2
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff c v).2 hv
      obtain ⟨v₀, hv₀, hmax⟩ := Finset.exists_max_image C
        (fun v => boundaryAdjustedSize (label v)) hCne
      let D := boundaryAdjustedSize (label v₀)
      have hv₀c : v₀ ∈ c.supp := by
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff c v₀).mpr
          ((mem_profileA3GraphComponentVertices c v₀).1 hv₀)
      have hD : 1 ≤ D := one_le_boundaryAdjustedSize (hzero v₀)
      let Glo := profileA3TrimGraph G label D
      have hGlo : Glo ≤ G := profileA3_trimGraph_le G label D
      have hlowResult : ∀ (c₀ : Glo.ConnectedComponent),
          (∃ u, u ∈ c₀.supp ∧ u ∈ c.supp ∧
            boundaryAdjustedSize (label u) < D / 10) →
          ProfileA3ComponentDecomposition Glo label c₀ := by
        intro c₀ hc₀
        obtain ⟨u, hu₀, huc, huLow⟩ := hc₀
        have hsub : profileA3GraphComponentVertices c₀ ⊆ C := by
          have hcc : Glo.connectedComponentMk u = c₀ :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ u).mp hu₀
          have hsup := SimpleGraph.ConnectedComponent.connectedComponentMk_supp_subset_supp
            hGlo c huc
          intro w hw
          have hwcc : Glo.connectedComponentMk w = c₀ :=
            (mem_profileA3GraphComponentVertices c₀ w).1 hw
          have hwSet : w ∈ c₀.supp :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ w).2 hwcc
          have hw' : w ∈ (Glo.connectedComponentMk u).supp := by
            rw [hcc]
            exact hwSet
          apply (mem_profileA3GraphComponentVertices c w).2
          exact (SimpleGraph.ConnectedComponent.mem_supp_iff c w).1 (hsup hw')
        have hv₀notLow : ¬ boundaryAdjustedSize (label v₀) < D / 10 := by
          dsimp [D]
          nlinarith
        have hstrict : profileA3GraphComponentVertices c₀ ⊂ C := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
          intro heq
          have hv₀fin : v₀ ∈ profileA3GraphComponentVertices c₀ := by
            rw [heq]
            exact hv₀
          have hv₀' : v₀ ∈ c₀.supp :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ v₀).2
              ((mem_profileA3GraphComponentVertices c₀ v₀).1 hv₀fin)
          have hLow := profileA3_trimComponent_all_low G label D c₀ hu₀ hv₀' huLow
          exact hv₀notLow hLow
        have hcard : (profileA3GraphComponentVertices c₀).card < n := by
          calc
            (profileA3GraphComponentVertices c₀).card < C.card := Finset.card_lt_card hstrict
            _ = n := hc
        exact ih (profileA3GraphComponentVertices c₀).card hcard label hinj Glo
          (fun {u v} (h : Glo.Adj u v) => hAdj h.1) hzero hsep c₀ rfl
      have hlowDiameter : ∀ (c₀ : Glo.ConnectedComponent),
          (∃ u, u ∈ c₀.supp ∧ u ∈ c.supp ∧
            boundaryAdjustedSize (label u) < D / 10) →
          ∀ x ∈ profileA3LabelUnion label (profileA3GraphComponentVertices c₀),
            ∀ y ∈ profileA3LabelUnion label (profileA3GraphComponentVertices c₀),
              profileA3GraphLength x y ≤ 4 * D := by
        intro c₀ hc₀ x hx y hy
        rcases hlowResult c₀ hc₀ with
          ⟨r, hr, hrmax, hrsmall, pieces, hcov, hpiecesdiam, hatt, hdiam⟩
        have hrScale : boundaryAdjustedSize (label r) < D / 10 := by
          obtain ⟨u, hu₀, huC, huLow⟩ := hc₀
          exact profileA3_trimComponent_all_low G label D c₀ hu₀ hr huLow
        have hdiam' := hdiam x hx y hy
        dsimp [D] at hrScale hdiam' ⊢
        nlinarith
      have hNoDirectHigh : ∀ {u v : V}, u ∈ c.supp → v ∈ c.supp →
          D / 10 ≤ boundaryAdjustedSize (label u) →
          D / 10 ≤ boundaryAdjustedSize (label v) → u ≠ v → ¬ G.Adj u v := by
        intro u v hu hv huhi hvhi huv hadj
        obtain ⟨hσ0, hτ0⟩ := And.intro (hzero u) (hzero v)
        have hsep' := hsep huv
        have huMax : boundaryAdjustedSize (label u) ≤ D :=
          hmax u ((mem_profileA3GraphComponentVertices c u).2
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c u).2 hu))
        have hvMax : boundaryAdjustedSize (label v) ≤ D :=
          hmax v ((mem_profileA3GraphComponentVertices c v).2
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c v).2 hv))
        exact profileA3_high_neighborhoods_not_overlap D (label u) (label v) hD
          hσ0 hτ0 huhi hvhi huMax hvMax hsep' (hAdj hadj)
      have hNoTwoHighThroughLow : ∀ (c₀ : Glo.ConnectedComponent),
          (∃ z, z ∈ c₀.supp ∧ z ∈ c.supp ∧
            boundaryAdjustedSize (label z) < D / 10) →
          ∀ {u v : V}, u ∈ c.supp → v ∈ c.supp →
            D / 10 ≤ boundaryAdjustedSize (label u) →
            D / 10 ≤ boundaryAdjustedSize (label v) → u ≠ v →
            (∃ a, a ∈ c₀.supp ∧ G.Adj u a) →
            (∃ b, b ∈ c₀.supp ∧ G.Adj v b) → False := by
        intro c₀ hc₀ u v hu hv huhi hvhi huv hleft hright
        obtain ⟨a, ha₀, hau⟩ := hleft
        obtain ⟨b, hb₀, hbv⟩ := hright
        obtain ⟨z, hz₀, hzC, hzLow⟩ := hc₀
        let S := profileA3LabelUnion label (profileA3GraphComponentVertices c₀)
        have hSdiam : ∀ x ∈ S, ∀ y ∈ S,
            profileA3GraphLength x y ≤ 4 * D :=
          hlowDiameter c₀ ⟨z, hz₀, hzC, hzLow⟩
        obtain ⟨x, hx⟩ := hAdj hau
        obtain ⟨y, hy⟩ := hAdj hbv
        have hxE : x ∈ profileA3NeutralNeighborhood (label u) :=
          (Finset.mem_inter.mp hx).1
        have hxA : x ∈ profileA3NeutralNeighborhood (label a) :=
          (Finset.mem_inter.mp hx).2
        have hyE : y ∈ profileA3NeutralNeighborhood (label v) :=
          (Finset.mem_inter.mp hy).1
        have hyB : y ∈ profileA3NeutralNeighborhood (label b) :=
          (Finset.mem_inter.mp hy).2
        have haS : x ∈ S := by
          apply Finset.mem_biUnion.mpr
          exact ⟨a, (mem_profileA3GraphComponentVertices c₀ a).2
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c₀ a).2 ha₀), hxA⟩
        have hbS : y ∈ S := by
          apply Finset.mem_biUnion.mpr
          exact ⟨b, (mem_profileA3GraphComponentVertices c₀ b).2
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c₀ b).2 hb₀), hyB⟩
        have hsep' : (65536 : ℝ) * min (boundaryAdjustedSize (label u))
            (boundaryAdjustedSize (label v)) ^ (7 / 4 : ℝ) ≤
            euclideanSetDistance (chargeSupport (label u)) (chargeSupport (label v)) :=
          hsep huv
        have huMax : boundaryAdjustedSize (label u) ≤ D :=
          hmax u ((mem_profileA3GraphComponentVertices c u).2
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c u).2 hu))
        have hvMax : boundaryAdjustedSize (label v) ≤ D :=
          hmax v ((mem_profileA3GraphComponentVertices c v).2
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c v).2 hv))
        exact profileA3_lowPiece_attaches_to_at_most_one_high D (label u) (label v) S
          hD (hzero u) (hzero v) (by
            intro heq
            exact huv (hinj heq)) huhi hvhi huMax hvMax hsep' hSdiam
          ⟨x, Finset.mem_inter.mpr ⟨hxE, haS⟩⟩
          ⟨y, Finset.mem_inter.mpr ⟨hyE, hbS⟩⟩
      let P : V → Prop := fun w => w = v₀ ∨
        ∃ c₀ : Glo.ConnectedComponent, w ∈ c₀.supp ∧
          c₀.supp ⊆ c.supp ∧ ∃ z, z ∈ c₀.supp ∧
            boundaryAdjustedSize (label z) < D / 10 ∧ G.Adj v₀ z
      have hStep : ∀ ⦃u v⦄, P u → G.Adj u v → P v := by
        intro u v hu hadj
        rcases hu with hroot | ⟨c₀, hu₀, hc₀sub, z, hz₀, hzLow, hzAttach⟩
        · subst u
          by_cases hvLow : boundaryAdjustedSize (label v) < D / 10
          · refine Or.inr ⟨Glo.connectedComponentMk v,
              SimpleGraph.ConnectedComponent.connectedComponentMk_mem, ?_, v,
              SimpleGraph.ConnectedComponent.connectedComponentMk_mem, hvLow, hadj⟩
            have hvC : v ∈ c.supp :=
              (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c hadj).mp hv₀c
            exact SimpleGraph.ConnectedComponent.connectedComponentMk_supp_subset_supp
              hGlo c hvC
          · have hvC : v ∈ c.supp := by
              exact (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c hadj).mp hv₀c
            by_cases heq : v = v₀
            · exact Or.inl heq
            · have hvHi : D / 10 ≤ boundaryAdjustedSize (label v) := le_of_not_gt hvLow
              exact False.elim (hNoDirectHigh hv₀c hvC
                (by dsimp [D]; nlinarith) hvHi (fun h => heq h.symm) hadj)
        · have hvC : v ∈ c.supp := by
            exact (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c hadj).mp
              (hc₀sub hu₀)
          by_cases hvLow : boundaryAdjustedSize (label v) < D / 10
          · have huLow : boundaryAdjustedSize (label u) < D / 10 :=
              profileA3_trimComponent_all_low G label D c₀ hz₀ hu₀ hzLow
            have hlowAdj : Glo.Adj u v := ⟨hadj, huLow, hvLow⟩
            have huc : Glo.connectedComponentMk u = c₀ :=
              (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ u).mp hu₀
            have hvc : Glo.connectedComponentMk v = c₀ :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hlowAdj).symm.trans huc
            exact Or.inr ⟨c₀,
              (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ v).mpr hvc,
              hc₀sub, z, hz₀, hzLow, hzAttach⟩
          · have hvHi : D / 10 ≤ boundaryAdjustedSize (label v) := le_of_not_gt hvLow
            by_cases heq : v = v₀
            · exact Or.inl heq
            · have hfalse := hNoTwoHighThroughLow c₀
                ⟨z, hz₀, hc₀sub hz₀, hzLow⟩
                hv₀c hvC (by dsimp [D]; nlinarith) hvHi (fun h => heq h.symm)
                ⟨z, hz₀, hzAttach⟩
                ⟨u, hu₀, hadj.symm⟩
              exact False.elim hfalse
      have hInv : ∀ w ∈ C, P w := by
        intro w hw
        have hwc : w ∈ c.supp := by
          exact (SimpleGraph.ConnectedComponent.mem_supp_iff c w).mpr
            ((mem_profileA3GraphComponentVertices c w).1 hw)
        have hrootComp : G.connectedComponentMk v₀ = c :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff c v₀).mp hv₀c
        have hwComp : G.connectedComponentMk w = c :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff c w).mp hwc
        have hreach : G.Reachable v₀ w :=
          (SimpleGraph.ConnectedComponent.eq).mp (hrootComp.trans hwComp.symm)
        rcases hreach with ⟨p⟩
        exact profileA3_walk_preserves hStep p (Or.inl rfl)
      have hnotOtherHigh : ∀ w ∈ C, w ≠ v₀ →
          boundaryAdjustedSize (label w) < D / 10 := by
        intro w hw hne
        rcases hInv w hw with heq | ⟨c₀, hw₀, _, z, hz₀, hzLow, _⟩
        · exact (hne heq).elim
        · exact profileA3_trimComponent_all_low G label D c₀ hz₀ hw₀ hzLow
      have hmaxD : ∀ w ∈ C, boundaryAdjustedSize (label w) ≤ D := by
        intro w hw
        rcases em (w = v₀) with heq | hne
        · subst w
          rfl
        · exact (hnotOtherHigh w hw hne).le.trans (by dsimp [D]; nlinarith)
      let lowVertices := C.filter fun w => boundaryAdjustedSize (label w) < D / 10
      let lowComps := lowVertices.image fun w => Glo.connectedComponentMk w
      let pieces := lowComps.image fun c₀ =>
        profileA3LabelUnion label (profileA3GraphComponentVertices c₀)
      have hlowCompsData : ∀ c₀ ∈ lowComps,
          ∃ w, w ∈ C ∧ boundaryAdjustedSize (label w) < D / 10 ∧
            Glo.connectedComponentMk w = c₀ := by
        intro c₀ hc₀
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hc₀
        have hw' := Finset.mem_filter.mp hw
        exact ⟨w, hw'.1, hw'.2, heq⟩
      have hlowCompSubset : ∀ c₀ ∈ lowComps,
          profileA3GraphComponentVertices c₀ ⊆ C := by
        intro c₀ hc₀ w hw
        obtain ⟨u, huC, -, huEq⟩ := hlowCompsData c₀ hc₀
        have huSupp : u ∈ c.supp := by
          exact (SimpleGraph.ConnectedComponent.mem_supp_iff c u).mpr
            ((mem_profileA3GraphComponentVertices c u).mp huC)
        have hsubSupp :=
          SimpleGraph.ConnectedComponent.connectedComponentMk_supp_subset_supp hGlo c huSupp
        have hwSupp : w ∈ c₀.supp :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ w).mpr
            ((mem_profileA3GraphComponentVertices c₀ w).mp hw)
        have hwSupp' : w ∈ (Glo.connectedComponentMk u).supp := by
          simpa [huEq] using hwSupp
        have hwC : w ∈ c.supp := hsubSupp hwSupp'
        exact (mem_profileA3GraphComponentVertices c w).mpr
          ((SimpleGraph.ConnectedComponent.mem_supp_iff c w).mp hwC)
      have hcover : profileA3LabelUnion label C =
          profileA3NeutralNeighborhood (label v₀) ∪ pieces.biUnion id := by
        classical
        ext x
        constructor
        · intro hx
          rcases Finset.mem_biUnion.mp hx with ⟨w, hwC, hxw⟩
          by_cases hwroot : w = v₀
          · subst w
            exact Finset.mem_union_left _ hxw
          · have hwLow := hnotOtherHigh w hwC hwroot
            have hwLowV : w ∈ lowVertices := Finset.mem_filter.mpr ⟨hwC, hwLow⟩
            have hc₀ : Glo.connectedComponentMk w ∈ lowComps :=
              Finset.mem_image.mpr ⟨w, hwLowV, rfl⟩
            have hxPiece : x ∈ profileA3LabelUnion label
                (profileA3GraphComponentVertices (Glo.connectedComponentMk w)) :=
              Finset.mem_biUnion.mpr ⟨w,
                (mem_profileA3GraphComponentVertices _ _).mpr rfl, hxw⟩
            have hpiece : profileA3LabelUnion label
                (profileA3GraphComponentVertices (Glo.connectedComponentMk w)) ∈ pieces :=
              Finset.mem_image.mpr ⟨Glo.connectedComponentMk w, hc₀, rfl⟩
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, hpiece, hxPiece⟩)
        · intro hx
          rcases Finset.mem_union.mp hx with hxH | hxP
          · exact Finset.mem_biUnion.mpr ⟨v₀, hv₀, hxH⟩
          · rcases Finset.mem_biUnion.mp hxP with ⟨S, hS, hxS⟩
            obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hS
            rcases Finset.mem_biUnion.mp hxS with ⟨w, hw₀, hxw⟩
            exact Finset.mem_biUnion.mpr ⟨w, hlowCompSubset c₀ hc₀ hw₀, hxw⟩
      have hpiecesdiam : ∀ S ∈ pieces, ∀ x ∈ S, ∀ y ∈ S,
          profileA3GraphLength x y ≤ 4 * D := by
        intro S hS x hx y hy
        obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hS
        obtain ⟨w, hwC, hwLow, hwEq⟩ := hlowCompsData c₀ hc₀
        have hw₀ : w ∈ c₀.supp :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ w).mpr hwEq
        exact hlowDiameter c₀ ⟨w, hw₀,
          (SimpleGraph.ConnectedComponent.mem_supp_iff c w).mpr
            ((mem_profileA3GraphComponentVertices c w).mp hwC), hwLow⟩ x hx y hy
      have hpiecesAttach : ∀ S ∈ pieces,
          ∃ z ∈ S, ∃ u ∈ profileA3NeutralNeighborhood (label v₀),
            profileA3GraphLength z u ≤ 1 := by
        intro S hS
        obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hS
        obtain ⟨w, hwC, hwLow, hwEq⟩ := hlowCompsData c₀ hc₀
        have hwNe : w ≠ v₀ := by
          have hv₀notLow : ¬ boundaryAdjustedSize (label v₀) < D / 10 := by
            dsimp [D]
            nlinarith
          intro heq
          subst w
          exact hv₀notLow hwLow
        rcases hInv w hwC with hroot | ⟨c₁, hw₁, hc₁sub, z, hz₁, hzLow, hzAttach⟩
        · exact (hwNe hroot).elim
        · have hc₁ : c₁ = c₀ := by
            have h₁ : Glo.connectedComponentMk w = c₁ :=
              (SimpleGraph.ConnectedComponent.mem_supp_iff c₁ w).mp hw₁
            exact h₁.symm.trans hwEq
          have hz₀ : z ∈ c₀.supp := by simpa [hc₁] using hz₁
          have hc₀sub : c₀.supp ⊆ c.supp := by simpa [hc₁] using hc₁sub
          have hzC : z ∈ c.supp := by
            exact hc₀sub hz₀
          obtain ⟨x, hx⟩ := hAdj hzAttach
          have hxS : x ∈ profileA3LabelUnion label
              (profileA3GraphComponentVertices c₀) := by
            apply Finset.mem_biUnion.mpr
            exact ⟨z, (mem_profileA3GraphComponentVertices c₀ z).mpr
              ((SimpleGraph.ConnectedComponent.mem_supp_iff c₀ z).mp hz₀),
              (Finset.mem_inter.mp hx).2⟩
          refine ⟨x, hxS, x, ?_, ?_⟩
          · exact (Finset.mem_inter.mp hx).1
          · simp [profileA3GraphLength]
      have hmaxSupp : ∀ w ∈ c.supp,
          boundaryAdjustedSize (label w) ≤ boundaryAdjustedSize (label v₀) := by
        intro w hw
        exact hmaxD w ((mem_profileA3GraphComponentVertices c w).mpr
          ((SimpleGraph.ConnectedComponent.mem_supp_iff c w).mp hw))
      have hnotOtherHighSupp : ∀ w ∈ c.supp, w ≠ v₀ →
          boundaryAdjustedSize (label w) < boundaryAdjustedSize (label v₀) / 10 := by
        intro w hw hne
        simpa [D] using hnotOtherHigh w
          ((mem_profileA3GraphComponentVertices c w).mpr
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c w).mp hw)) hne
      have hbounds := profileA3_component_bounds_of_uniqueMax_decomposition
        (label v₀) (hzero v₀) (profileA3LabelUnion label C)
        (profileA3NeutralNeighborhood (label v₀)) pieces rfl hcover hpiecesdiam hpiecesAttach
      refine ⟨v₀, hv₀c, hmaxSupp, hnotOtherHighSupp, pieces, hcover, hpiecesdiam,
        hpiecesAttach, ?_⟩
      simpa [D] using hbounds.2

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
