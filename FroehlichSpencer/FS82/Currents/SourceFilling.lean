/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.Expansion
public import FroehlichSpencer.FS82.Cubical.RealFilling
public import FroehlichSpencer.FS82.Moment.Comparison
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# FS82 source current fillings

The finite dual-link current is embedded by C1 into the bumped primal cubical
box. prism operator then fills closed currents, with its support and
coefficient bounds retained on that same carrier.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents

open Cubical
noncomputable section
open Classical

@[expose] def lambdaCellToBumpedBox {B : Box 4} (c : DualCell 4 B) :
    Cell 4 (bumpedBox B) := fun i =>
  match c i with
  | Sum.inl v => Sum.inl ⟨v.val + 1, by dsimp [bumpedBox]; omega⟩
  | Sum.inr e => Sum.inr ⟨e.val, by dsimp [bumpedBox]; omega⟩

theorem lambdaCellToBumpedBox_axes {B : Box 4} (c : DualCell 4 B) :
    cellAxes (lambdaCellToBumpedBox c) = dualCellAxes c := by
  ext i
  simp only [cellAxes, dualCellAxes, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases h : c i <;> simp [lambdaCellToBumpedBox, h, coordIsEdge]

theorem lambdaCellToBumpedBox_degree {B : Box 4} (c : DualCell 4 B) :
    cellDegree (lambdaCellToBumpedBox c) = dualCellDegree c := by
  simp [cellDegree, dualCellDegree, lambdaCellToBumpedBox_axes]

theorem lambdaCellToBumpedBox_injective {B : Box 4} :
    Function.Injective (@lambdaCellToBumpedBox B) := by
  intro c d h
  funext i
  have hi := congrFun h i
  cases hc : c i <;> cases hd : d i <;>
    simp [lambdaCellToBumpedBox, hc, hd] at hi ⊢ <;> omega

theorem axis_eq_of_interval {B : Box 4} (e : Link B) (k : Fin 4)
    (h : (e.1 k).isRight = true) : axis e = k := by
  have hk : k ∈ dualCellAxes e.1 := by
    simp [dualCellAxes, h]
  rw [axes_eq_singleton] at hk
  exact (Finset.mem_singleton.mp hk).symm

theorem lambdaCellToBumpedBox_eq_of_base_axis {B : Box 4}
    (e f : Link B) (hbase : base e = base f) (haxis : axis e = axis f) :
    lambdaCellToBumpedBox e.1 = lambdaCellToBumpedBox f.1 := by
  funext k
  by_cases hk : axis e = k
  · have hkf : axis f = k := by rw [← haxis]; exact hk
    cases hecoord : e.1 k with
    | inl v =>
        have hr := axis_coord_isRight e
        rw [hk] at hr
        simp [hecoord] at hr
    | inr t =>
        cases hfcoord : f.1 k with
        | inl w =>
            have hr := axis_coord_isRight f
            rw [hkf] at hr
            simp [hfcoord] at hr
        | inr u =>
            have hval : t.val = u.val := by
              have h := congrArg Fin.val (congrFun hbase k)
              simpa [base, hecoord, hfcoord, coordToBumpedAnchor] using h
            have htu : t = u := Fin.ext hval
            simp [lambdaCellToBumpedBox, hecoord, hfcoord, htu]
  · have hkf : axis f ≠ k := by
      intro hfk
      apply hk
      rw [haxis]
      exact hfk
    cases hecoord : e.1 k with
    | inl v =>
        cases hfcoord : f.1 k with
        | inl w =>
            have hval : v.val = w.val := by
              have h := congrArg Fin.val (congrFun hbase k)
              have hcast : v.val + 1 = w.val + 1 := by
                simpa [base, hecoord, hfcoord, coordToBumpedAnchor] using h
              omega
            have hvw : v = w := Fin.ext hval
            simp [lambdaCellToBumpedBox, hecoord, hfcoord, hvw]
        | inr u =>
            have hfk := axis_eq_of_interval f k (by simp [hfcoord])
            exact (hkf hfk).elim
    | inr t =>
        have heq := axis_eq_of_interval e k (by simp [hecoord])
        exact (hk heq).elim

abbrev SourceBoxLink (R : ℕ) := Fin 4 × (Fin 4 → Fin (2 * R))

theorem sourceBoxLink_card (R : ℕ) : Fintype.card (SourceBoxLink R) =
    4 * (2 * R)^4 := by
  simp [SourceBoxLink, Fintype.card_prod]

@[expose] def sourceCenteredLinkBox {B : Box 4}
    (p : Fin 4 → ℤ) (R : ℕ) : Finset (Link B) :=
  Finset.univ.filter fun e => ∀ k,
    p k - (R : ℤ) ≤ (base e k).val ∧
      (base e k).val < p k + (R : ℤ)

noncomputable def sourceCenteredBoxIndex {B : Box 4}
    (p : Fin 4 → ℤ) (R : ℕ) (e : Link B)
    (he : e ∈ sourceCenteredLinkBox p R) : SourceBoxLink R :=
  (axis e, fun k =>
    ⟨(((base e k).val : ℤ) - p k + (R : ℤ)).toNat, by
      have hrange := (Finset.mem_filter.mp he).2 k
      have hnonneg : 0 ≤ (base e k).val - p k + (R : ℤ) := by omega
      have hlt : (base e k).val - p k + (R : ℤ) < (2 * R : ℤ) := by omega
      have hltCast :
          (( (base e k).val - p k + (R : ℤ)).toNat : ℤ) < (2 * R : ℤ) := by
        simpa [Int.toNat_of_nonneg hnonneg] using hlt
      exact_mod_cast hltCast⟩)

noncomputable def sourceCenteredBoxCode {B : Box 4}
    (p : Fin 4 → ℤ) (R : ℕ) (hR : 0 < R)
    (e : Link B) : SourceBoxLink R :=
  if he : e ∈ sourceCenteredLinkBox p R then
    sourceCenteredBoxIndex p R e he
  else (0, fun _ => ⟨0, by omega⟩)

theorem sourceCenteredBoxCode_injOn {B : Box 4}
    (p : Fin 4 → ℤ) (R : ℕ) (hR : 0 < R) :
    Set.InjOn (sourceCenteredBoxCode p R hR)
      {e : Link B | e ∈ sourceCenteredLinkBox p R} := by
  intro e he f hf hcode
  have heFin : e ∈ sourceCenteredLinkBox p R := by simpa using he
  have hfFin : f ∈ sourceCenteredLinkBox p R := by simpa using hf
  have haxis : axis e = axis f := by
    have h := congrArg Prod.fst hcode
    simpa [sourceCenteredBoxCode, heFin, hfFin, sourceCenteredBoxIndex] using h
  have hbase : base e = base f := by
    funext k
    apply Fin.ext
    have hidx := congrArg (fun z : SourceBoxLink R => (z.2 k).val) hcode
    have hidx' :
        ((base e k).val - p k + (R : ℤ)).toNat =
          ((base f k).val - p k + (R : ℤ)).toNat := by
      simpa [sourceCenteredBoxCode, heFin, hfFin, sourceCenteredBoxIndex] using hidx
    have heNonneg : 0 ≤ (base e k).val - p k + (R : ℤ) := by
      have hrange := (Finset.mem_filter.mp heFin).2 k
      omega
    have hfNonneg : 0 ≤ (base f k).val - p k + (R : ℤ) := by
      have hrange := (Finset.mem_filter.mp hfFin).2 k
      omega
    have hcast :
        (((base e k).val - p k + (R : ℤ)).toNat : ℤ) =
          (((base f k).val - p k + (R : ℤ)).toNat : ℤ) := congrArg Int.ofNat hidx'
    rw [Int.toNat_of_nonneg heNonneg, Int.toNat_of_nonneg hfNonneg] at hcast
    have hcoord : ((base e k).val : ℤ) = (base f k).val := by omega
    exact_mod_cast hcoord
  have hcell := lambdaCellToBumpedBox_eq_of_base_axis e f hbase haxis
  have heq : e = f := by
    apply Subtype.ext
    exact lambdaCellToBumpedBox_injective hcell
  exact heq

theorem sourceCenteredLinkBox_card_le {B : Box 4}
    (p : Fin 4 → ℤ) (R : ℕ) :
    (sourceCenteredLinkBox (B := B) p R).card ≤ 4 * (2 * R)^4 := by
  classical
  by_cases hR : R = 0
  · subst R
    have hEmpty : sourceCenteredLinkBox (B := B) p 0 = ∅ := by
      ext e
      simp [sourceCenteredLinkBox]
    simp [hEmpty]
  · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
    have hcard := Finset.card_le_card_of_injOn
      (sourceCenteredBoxCode p R hRpos)
      (s := sourceCenteredLinkBox (B := B) p R)
      (t := Finset.univ)
      (by intro e he; simp)
      (sourceCenteredBoxCode_injOn (B := B) p R hRpos)
    calc
      (sourceCenteredLinkBox (B := B) p R).card ≤
          (Finset.univ : Finset (SourceBoxLink R)).card := hcard
      _ = 4 * (2 * R)^4 := sourceBoxLink_card R

theorem mem_sourceCenteredLinkBox_of_bounds {B : Box 4}
    {p : Fin 4 → ℤ} {R : ℕ} {e : Link B}
    (h : ∀ k, p k - (R : ℤ) ≤ (base e k).val ∧
      (base e k).val < p k + (R : ℤ)) :
    e ∈ sourceCenteredLinkBox p R := by
  simp only [sourceCenteredLinkBox, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact h

@[expose] def lambdaStarCellEmbedding {B : Box 4} :
    Link B ↪ Cell 4 (bumpedBox B) where
  toFun e := lambdaCellToBumpedBox e.1
  inj' e f h := by
    apply Subtype.ext
    exact lambdaCellToBumpedBox_injective h

@[expose] def sourceCurrentChain {B : Box 4} (q : IntegerCurrent B) :
    Chain 4 (bumpedBox B) :=
  Finsupp.embDomain (lambdaStarCellEmbedding (B := B)) q

@[simp] theorem sourceCurrentChain_apply {B : Box 4}
    (q : IntegerCurrent B) (e : Link B) :
    sourceCurrentChain q (lambdaCellToBumpedBox e.1) = q e := by
  classical
  rw [sourceCurrentChain, Finsupp.embDomain_apply]
  have hex : ∃ a : Link B,
      lambdaStarCellEmbedding a = lambdaCellToBumpedBox e.1 := ⟨e, rfl⟩
  rw [dite_eq_left hex]
  have hchoose : hex.choose = e := by
    have hspec := hex.choose_spec
    change lambdaCellToBumpedBox hex.choose.1 =
      lambdaCellToBumpedBox e.1 at hspec
    apply Subtype.ext
    exact lambdaCellToBumpedBox_injective hspec
  simp [hchoose]


@[expose] def supportInSourceCube {B : Box 4} (S : Finset (Link B))
    (lo : Fin 4 → ℕ) (D : ℕ) : Prop :=
  ∀ k, ∀ e ∈ S,
    lo k ≤ (base e k).val ∧
      (base e k).val + (if axis e = k then 1 else 0) ≤ lo k + D


theorem lambdaCellToBumpedBox_lower {B : Box 4} (e : Link B) (k : Fin 4) :
    cellCoordLower (lambdaCellToBumpedBox e.1) k = (base e k).val := by
  cases h : e.1 k <;>
    simp [lambdaCellToBumpedBox, cellCoordLower, coordBase, base,
      coordToBumpedAnchor, h]

theorem lambdaCellToBumpedBox_axis_iff {B : Box 4} (e : Link B) (k : Fin 4) :
    coordIsEdge (lambdaCellToBumpedBox e.1 k) = (axis e = k) := by
  by_cases hk : axis e = k
  · subst k
    have hr := axis_coord_isRight e
    cases h : e.1 (axis e) <;>
      simp [coordIsEdge, lambdaCellToBumpedBox, h] at hr ⊢
  · have hnot : k ∉ dualCellAxes e.1 := by
      rw [axes_eq_singleton]
      simpa using (Ne.symm hk)
    cases h : e.1 k with
    | inl v => simp [coordIsEdge, lambdaCellToBumpedBox, h, hk]
    | inr t =>
        have hmem : k ∈ dualCellAxes e.1 := by
          simp [dualCellAxes, h]
        exact (hnot hmem).elim

theorem lambdaCellToBumpedBox_upper {B : Box 4} (e : Link B) (k : Fin 4) :
    cellCoordUpper (lambdaCellToBumpedBox e.1) k =
      (base e k).val + if axis e = k then 1 else 0 := by
  have hbase : coordBase (lambdaCellToBumpedBox e.1 k) = (base e k).val :=
    lambdaCellToBumpedBox_lower e k
  simp only [cellCoordUpper, hbase, lambdaCellToBumpedBox_axis_iff]

theorem sourceCurrentChain_homogeneousSupport {B : Box 4}
    (q : IntegerCurrent B) : homogeneousSupport (sourceCurrentChain q) 1 := by
  intro c hc
  rw [sourceCurrentChain] at hc
  rw [Finsupp.support_embDomain] at hc
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hc
  change cellDegree (lambdaCellToBumpedBox e.1) = 1
  rw [lambdaCellToBumpedBox_degree]
  exact e.2

theorem sourceCurrentChain_supportedInRect {B : Box 4} (q : IntegerCurrent B)
    (lo : Fin 4 → ℕ) (D : ℕ)
    (hq : supportInSourceCube q.support lo D) :
    supportedInRect (sourceCurrentChain q) lo (fun k => lo k + D) := by
  intro c hc k
  rw [sourceCurrentChain] at hc
  rw [Finsupp.support_embDomain] at hc
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hc
  have h := hq k e he
  change lo k ≤ cellCoordLower (lambdaCellToBumpedBox e.1) k ∧
    cellCoordUpper (lambdaCellToBumpedBox e.1) k ≤ lo k + D
  simpa [lambdaCellToBumpedBox_lower, lambdaCellToBumpedBox_upper] using h

abbrev SourcePlaquette (B : Box 4) :=
  {c : Cell 4 (bumpedBox B) // cellDegree c = 2}

noncomputable instance sourcePlaquetteFintype {B : Box 4} :
    Fintype (SourcePlaquette B) := Fintype.ofFinite _

instance sourcePlaquetteDecidableEq {B : Box 4} : DecidableEq (SourcePlaquette B) :=
  inferInstance

@[expose] def sourceOmega {B : Box 4} (lo : Fin 4 → ℕ) (D : ℕ) :
    Finset (SourcePlaquette B) :=
  Finset.univ.filter fun p => ∀ k,
    lo k ≤ cellCoordLower p.1 k ∧ cellCoordUpper p.1 k ≤ lo k + D

@[expose] def sourcePlaquetteCoord {B : Box 4} (p : SourcePlaquette B) :
    Fin 4 → ℤ := fun k => (cellCoordLower p.1 k : ℤ)

theorem cellCoordLower_le_upper {B : Box 4} (c : Cell 4 B) (k : Fin 4) :
    cellCoordLower c k ≤ cellCoordUpper c k := by
  cases h : c k <;>
    simp [cellCoordLower, cellCoordUpper, coordBase, coordIsEdge, h]


abbrev SourceCubeCode (D : ℕ) :=
  (Fin 4 → Fin (D + 1)) × (Fin 4 → Bool)

private noncomputable def sourceCubeCode {B : Box 4} (lo : Fin 4 → ℕ) (D : ℕ)
    (p : SourcePlaquette B)
    (hp : ∀ k, lo k ≤ cellCoordLower p.1 k ∧ cellCoordUpper p.1 k ≤ lo k + D) :
    SourceCubeCode D :=
  (fun k => ⟨cellCoordLower p.1 k - lo k, by
    have hlow := hp k |>.1
    have hup := hp k |>.2
    have hbaseupper : cellCoordLower p.1 k ≤ cellCoordUpper p.1 k := by
      cases h : p.1 k <;> simp [cellCoordLower, cellCoordUpper, coordBase, coordIsEdge, h]
    omega⟩,
    fun k => decide (coordIsEdge (p.1 k)))

theorem sourceOmega_card_le_cubeCode {B : Box 4} (lo : Fin 4 → ℕ) (D : ℕ) :
    (sourceOmega (B := B) lo D).card ≤ 16 * (D + 1)^4 := by
  classical
  let code : SourcePlaquette B → SourceCubeCode D := fun p =>
    if hp : p ∈ sourceOmega (B := B) lo D then
      sourceCubeCode lo D p (Finset.mem_filter.mp hp |>.2)
    else default
  have hinj : Set.InjOn code
      (↑(sourceOmega (B := B) lo D) : Set (SourcePlaquette B)) := by
    intro p hp q hq hcode
    have hp' : p ∈ sourceOmega (B := B) lo D := by simpa using hp
    have hq' : q ∈ sourceOmega (B := B) lo D := by simpa using hq
    have hcode' : sourceCubeCode lo D p (Finset.mem_filter.mp hp |>.2) =
        sourceCubeCode lo D q (Finset.mem_filter.mp hq |>.2) := by
      change code p = code q at hcode
      dsimp [code] at hcode
      rw [dite_eq_left hp', dite_eq_left hq'] at hcode
      exact hcode
    apply Subtype.ext
    funext k
    have hlow : cellCoordLower p.1 k - lo k = cellCoordLower q.1 k - lo k := by
      have h := congrArg (fun z : SourceCubeCode D => (z.1 k).val) hcode'
      simpa [sourceCubeCode] using h
    have hedge : decide (coordIsEdge (p.1 k)) = decide (coordIsEdge (q.1 k)) := by
      have h := congrArg (fun z : SourceCubeCode D => z.2 k) hcode'
      simpa [sourceCubeCode] using h
    have hpinside := Finset.mem_filter.mp hp |>.2 k
    have hqinside := Finset.mem_filter.mp hq |>.2 k
    have hbase : cellCoordLower p.1 k = cellCoordLower q.1 k := by omega
    cases hpcoord : p.1 k with
    | inl vp =>
      cases hqcoord : q.1 k with
      | inl vq =>
        have hv : vp.val = vq.val := by
          simpa [cellCoordLower, coordBase, hpcoord, hqcoord] using hbase
        have hfin : vp = vq := Fin.ext hv
        simp [hfin]
      | inr eq => simp [coordIsEdge, hpcoord, hqcoord] at hedge
    | inr ep =>
      cases hqcoord : q.1 k with
      | inl vq => simp [coordIsEdge, hpcoord, hqcoord] at hedge
      | inr eq =>
        have hv : ep.val = eq.val := by
          simpa [cellCoordLower, coordBase, hpcoord, hqcoord] using hbase
        have hfin : ep = eq := Fin.ext hv
        simp [hfin]
  have hcard := Finset.card_le_card_of_injOn code
    (s := sourceOmega (B := B) lo D)
    (t := (Finset.univ : Finset (SourceCubeCode D)))
    (by intro p hp; simp) hinj
  have hcodecard : Fintype.card (SourceCubeCode D) = 16 * (D + 1)^4 := by
    simp [SourceCubeCode, Fintype.card_prod]
    ring
  simpa [hcodecard] using hcard


theorem sourceCurrentChain_add {B : Box 4} (q r : IntegerCurrent B) :
    sourceCurrentChain (q + r) = sourceCurrentChain q + sourceCurrentChain r := by
  simp [sourceCurrentChain, Finsupp.embDomain_add]


/- The source's two-form `μρ` is the integer Lemma 1 filling, scaled by `2π`.
The `RealChain` carrier records the source's coefficient group explicitly. -/


@[expose] def sourceOmegaMax {B : Box 4} (lo : Fin 4 → ℕ) (D : ℕ)
    (field : SourcePlaquette B → ℝ) : ℝ :=
  sSup ((fun p => |field p|) '' (sourceOmega (B := B) lo D : Set (SourcePlaquette B)))

theorem sourceOmegaMax_nonneg {B : Box 4} (lo : Fin 4 → ℕ) (D : ℕ)
    (field : SourcePlaquette B → ℝ) : 0 ≤ sourceOmegaMax lo D field := by
  classical
  unfold sourceOmegaMax
  let S := (fun p : SourcePlaquette B => |field p|) ''
    (sourceOmega (B := B) lo D : Set (SourcePlaquette B))
  have hfinite : S.Finite := by
    exact (sourceOmega (B := B) lo D).finite_toSet.image _
  by_cases hS : S.Nonempty
  · rcases hS with ⟨x, hx⟩
    rcases hx with ⟨p, hp, rfl⟩
    calc
      0 ≤ |field p| := abs_nonneg _
      _ ≤ sSup S := le_csSup hfinite.bddAbove ⟨p, hp, rfl⟩
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    change 0 ≤ sSup S
    rw [hEmpty, Real.sSup_empty]

theorem sourceOmegaMax_bound {B : Box 4} (lo : Fin 4 → ℕ) (D : ℕ)
    (field : SourcePlaquette B → ℝ) {p : SourcePlaquette B}
    (hp : p ∈ sourceOmega (B := B) lo D) : |field p| ≤ sourceOmegaMax lo D field := by
  classical
  unfold sourceOmegaMax
  let S := (fun p : SourcePlaquette B => |field p|) ''
    (sourceOmega (B := B) lo D : Set (SourcePlaquette B))
  have hfinite : S.Finite := by
    exact (sourceOmega (B := B) lo D).finite_toSet.image _
  exact le_csSup hfinite.bddAbove ⟨p, hp, rfl⟩

noncomputable def sourceMaximizingPlaquette {B : Box 4} (lo : Fin 4 → ℕ)
    (D : ℕ) (field : SourcePlaquette B → ℝ)
    (hΩ : (sourceOmega (B := B) lo D).Nonempty) : SourcePlaquette B :=
  Classical.choose (Finset.exists_max_image (sourceOmega (B := B) lo D)
    (fun p => |field p|) hΩ)

theorem sourceMaximizingPlaquette_mem {B : Box 4} (lo : Fin 4 → ℕ)
    (D : ℕ) (field : SourcePlaquette B → ℝ)
    (hΩ : (sourceOmega (B := B) lo D).Nonempty) :
    sourceMaximizingPlaquette lo D field hΩ ∈ sourceOmega lo D :=
  (Classical.choose_spec (Finset.exists_max_image
    (sourceOmega (B := B) lo D) (fun p => |field p|) hΩ)).1

theorem sourceMaximizingPlaquette_max {B : Box 4} (lo : Fin 4 → ℕ)
    (D : ℕ) (field : SourcePlaquette B → ℝ)
    (hΩ : (sourceOmega (B := B) lo D).Nonempty)
    {p : SourcePlaquette B} (hp : p ∈ sourceOmega lo D) :
    |field p| ≤ |field (sourceMaximizingPlaquette lo D field hΩ)| :=
  (Classical.choose_spec (Finset.exists_max_image
    (sourceOmega (B := B) lo D) (fun p => |field p|) hΩ)).2 p hp

theorem sourceOmegaMax_eq_maximizingPlaquette {B : Box 4}
    (lo : Fin 4 → ℕ) (D : ℕ) (field : SourcePlaquette B → ℝ)
    (hΩ : (sourceOmega (B := B) lo D).Nonempty) :
    sourceOmegaMax lo D field =
      |field (sourceMaximizingPlaquette lo D field hΩ)| := by
  apply le_antisymm
  · unfold sourceOmegaMax
    have hS : ((fun p => |field p|) ''
        (sourceOmega (B := B) lo D : Set (SourcePlaquette B))).Nonempty := by
      rcases hΩ with ⟨p, hp⟩
      exact ⟨|field p|, p, hp, rfl⟩
    apply csSup_le hS
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact sourceMaximizingPlaquette_max lo D field hΩ hp
  · exact sourceOmegaMax_bound lo D field
      (sourceMaximizingPlaquette_mem lo D field hΩ)


end
end FroehlichSpencer.FS82.Currents

end
