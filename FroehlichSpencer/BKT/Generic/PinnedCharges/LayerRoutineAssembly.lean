/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineBase

/-!
`PinnedTerminalProfiles` asks for it on every comb terminal.

Everything else of `PinnedTerminalWaves` is supplied here (**part 1**): the doubled base sign
waves (`LayerRoutineBase`), the support sets, sizes, routes, `|S| ≲ d_Λ²` and overlap `≤ 1`
(`LayerRoutineLocal`), and the assembly of the graded waves (`routineWave`).

* `pinnedTerminalWaves_of_profiles`: `PinnedTerminalProfiles → PinnedTerminalWaves`;
* `theoremC_of_pinnedTerminalProfiles`, `exists_transition_of_pinnedTerminalProfiles`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open Filter
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- **Part 2: the profile family** on a terminal ensemble `F` (indexed by the neutralized
densities). -/
structure TerminalProfiles (L : ℕ) (α K₀ K₁ cP : ℝ) (F : Finset (ChargeDensity L)) where
  /-- The profile indices of each density. -/
  ι : (RotatorDualFace L → ℤ) → Type
  [fin : ∀ ϱ, Fintype (ι ϱ)]
  /-- Scales (all positive). -/
  scale : ∀ ϱ, ι ϱ → ℕ
  /-- The profiles. -/
  piece : ∀ ϱ, ι ϱ → RotatorDualFace L → ℝ
  /-- Their charges `⟨ψ_t, ϱ⟩`. -/
  charge : ∀ ϱ, ι ϱ → ℝ
  one_le_scale : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t, 1 ≤ scale ϱ t
  pairing : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t,
    Multigraph.pairing (piece ϱ t) (fun j => (ϱ j : ℝ)) = charge ϱ t
  charge_ge_one : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t, 1 ≤ |charge ϱ t|
  energy_le : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t,
    (squareZero L).energy (piece ϱ t) ≤ K₀ * charge ϱ t ^ 2
  grad_le : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t (e : SquareZeroBond L),
    |(squareZero L).grad (piece ϱ t) e| ≤ K₁ * (2 : ℝ) ^ (-(1 - 1 / α) * (scale ϱ t : ℝ))
  edge_count : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t,
    ((Finset.univ.filter fun e : SquareZeroBond L =>
      (squareZero L).grad (piece ϱ t) e ≠ 0).card : ℝ) ≤ 100 * 4 ^ scale ϱ t
  grad_disjoint : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t t', t ≠ t' → ∀ e : SquareZeroBond L,
    (squareZero L).grad (piece ϱ t) e = 0 ∨ (squareZero L).grad (piece ϱ t') e = 0
  supp : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t,
    Function.support (piece ϱ t) ⊆ (squareZero L).densityDomain ϱ (routineCenter ϱ)
  count : ∀ ϱ ∈ F.image neutralizeAtWiredRoot,
    cP * layerSelectedSum ϱ ≤ (Fintype.card (ι ϱ) : ℝ)
  local_ : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t (e : SquareZeroBond L),
    (squareZero L).grad (piece ϱ t) e ≠ 0 → e ∈ routineS ϱ
  avoid : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t, ∀ σ ∈ F, ∀ x ∈ chargeSupport σ,
    ∀ e : SquareZeroBond L, ((squareZero L).src e = some x ∨ (squareZero L).tgt e = some x) →
      (squareZero L).grad (piece ϱ t) e = 0
  orth : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ t, ∀ ϱ' ∈ F.image neutralizeAtWiredRoot,
    ϱ' ≠ ϱ → ∑ j, piece ϱ t j * (ϱ' j : ℝ) = 0
  disj : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, ∀ ϱ' ∈ F.image neutralizeAtWiredRoot, ϱ ≠ ϱ' →
    ∀ t t' (e : SquareZeroBond L),
      (squareZero L).grad (piece ϱ t) e = 0 ∨ (squareZero L).grad (piece ϱ' t') e = 0

attribute [instance] TerminalProfiles.fin

/-- **The profile hypothesis**: part 2 on every comb terminal. -/
def PinnedTerminalProfiles (α K₀ K₁ cP : ℝ) (L₀ : ℕ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L → ∀ N : ℕ, 1 ≤ N → ∀ T : SelConfig L, IsCombTerminal N T →
    Nonempty (TerminalProfiles L α K₀ K₁ cP T.F)

/-- The graded wave: doubled base bumps and the profiles. -/
def routineWave {α K₀ K₁ cP : ℝ} {F : Finset (ChargeDensity L)}
    (P : TerminalProfiles L α K₀ K₁ cP F) (hα : 1 < α) (hL : 1 < L) (ϱ : RotatorDualFace L → ℤ) (hϱ : ϱ ∈ F.image neutralizeAtWiredRoot)
    (hϱ0 : ϱ ≠ 0) (hsum : ∑ j, ϱ j = 0) :
    GradedSpinWave.{0, 0, 0} (squareZero L) ∅ routineCenter ϱ :=
  { ι := {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ
    finite := inferInstance
    alpha := α
    alpha_gt_one := hα
    K₀ := max 4 K₀
    K₀_nonneg := le_max_of_le_left (by norm_num)
    K₁ := max 2 K₁
    K₁_nonneg := le_max_of_le_left (by norm_num)
    scale := Sum.elim (fun _ => 0) (P.scale ϱ)
    piece := Sum.elim (fun x => basePiece ϱ x.1) (P.piece ϱ)
    charge := Sum.elim (fun x => 2 * |(ϱ (some x.1) : ℝ)|) (P.charge ϱ)
    countPerScale := fun k => ((Finset.univ.filter fun (t : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ) =>
      Sum.elim (fun _ => 0) (P.scale ϱ) t = k).card : ℝ)
    countPerScale_nonneg := fun _ => Nat.cast_nonneg _
    count := fun _ => le_rfl
    grad_disjoint := by
      intro t t' hne e
      have hx : ∀ x : {x // x ∈ baseSites ϱ}, ϱ (some x.1) ≠ 0 ∧
          (x.1.1.val + x.1.2.val) % 2 = baseParity ϱ := fun x => by
        have := x.2
        unfold baseSites at this
        exact (Finset.mem_filter.mp this).2
      have hsupp : ∀ x : {x // x ∈ baseSites ϱ}, ∃ σ ∈ F, x.1 ∈ chargeSupport σ := fun x => by
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hϱ
        exact ⟨σ, hσ, by unfold chargeSupport; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hx x).1⟩⟩
      rcases t with x | t <;> rcases t' with x' | t'
      · by_contra h
        push Not at h
        have hxx : x.1 ≠ x'.1 := fun h' => hne (congrArg Sum.inl (Subtype.ext h'))
        have h1 := l1_eq_one_of_grad_basePiece hxx h.1 h.2
        have p1 := (hx x).2
        have p2 := (hx x').2
        unfold l1 at h1
        omega
      · by_cases h : (squareZero L).grad (basePiece ϱ x.1) e = 0
        · exact Or.inl h
        · obtain ⟨σ, hσ, hxσ⟩ := hsupp x
          exact Or.inr (P.avoid ϱ hϱ t' σ hσ x.1 hxσ e (grad_basePiece_incident h))
      · by_cases h : (squareZero L).grad (basePiece ϱ x'.1) e = 0
        · exact Or.inr h
        · obtain ⟨σ, hσ, hxσ⟩ := hsupp x'
          exact Or.inl (P.avoid ϱ hϱ t σ hσ x'.1 hxσ e (grad_basePiece_incident h))
      · exact P.grad_disjoint ϱ hϱ t t' (fun h => hne (congrArg Sum.inr h)) e
    const_plus := fun t ρ' hρ' => by simp [Multigraph.comparableDensities] at hρ'
    supp := by
      intro t
      rcases t with x | t
      · have := x.2
        unfold baseSites at this
        exact support_basePiece_subset hL hϱ0 hsum (Finset.mem_filter.mp this).2.1
      · exact P.supp ϱ hϱ t
    pairing := by
      intro t
      rcases t with x | t
      · have := x.2
        unfold baseSites at this
        exact pairing_basePiece_self ϱ (Finset.mem_filter.mp this).2.1
      · exact P.pairing ϱ hϱ t
    charge_ge_one := by
      intro t
      rcases t with x | t
      · have := x.2
        unfold baseSites at this
        have h1 : (1 : ℝ) ≤ |(ϱ (some x.1) : ℝ)| := by
          exact_mod_cast Int.one_le_abs (Finset.mem_filter.mp this).2.1
        simp only [Sum.elim_inl]
        rw [abs_of_nonneg (by positivity)]
        linarith
      · exact P.charge_ge_one ϱ hϱ t
    energy_le := by
      intro t
      rcases t with x | t
      · have := x.2
        unfold baseSites at this
        have h1 : (1 : ℝ) ≤ |(ϱ (some x.1) : ℝ)| := by
          exact_mod_cast Int.one_le_abs (Finset.mem_filter.mp this).2.1
        have he := energy_basePiece_le ϱ x.1
        simp only [Sum.elim_inl]
        have hm : (4 : ℝ) ≤ max 4 K₀ := le_max_left _ _
        have hsq : (4 : ℝ) ≤ (2 * |(ϱ (some x.1) : ℝ)|) ^ 2 := by nlinarith
        nlinarith
      · have he := P.energy_le ϱ hϱ t
        simp only [Sum.elim_inr]
        have : K₀ * P.charge ϱ t ^ 2 ≤ max 4 K₀ * P.charge ϱ t ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
        linarith
    grad_le := by
      intro t e
      rcases t with x | t
      · have := abs_grad_basePiece_le ϱ x.1 e
        simp only [Sum.elim_inl, CharP.cast_eq_zero, mul_zero, Real.rpow_zero, mul_one]
        exact this.trans (le_max_left _ _)
      · have := P.grad_le ϱ hϱ t e
        simp only [Sum.elim_inr]
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) }

theorem neutral_of_mem_image {F : Finset (ChargeDensity L)} (hF : ∀ ρ ∈ F, ρ ≠ 0)
    {ϱ : RotatorDualFace L → ℤ} (h : ϱ ∈ F.image neutralizeAtWiredRoot) :
    ϱ ≠ 0 ∧ ∑ j, ϱ j = 0 := by
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
  refine ⟨fun h0 => hF ρ hρ ?_, sum_neutralizeAtWiredRoot ρ⟩
  rw [← siteRestrict_neutralize ρ, h0]
  rfl

/-- **Part 1 discharged: the terminal waves from the profile family.** -/
theorem pinnedTerminalWaves_of_profiles {α K₀ K₁ cP : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hP : PinnedTerminalProfiles α K₀ K₁ cP L₀) :
    PinnedTerminalWaves α (max 4 K₀) (max 2 K₁) cP routineKv 1 (max L₀ 2) := by
  intro L hL
  have hL2 : 1 < L := by have := le_max_right L₀ 2; omega
  refine ⟨routineCenter, routineDsc, fun ρ hρ => routineDsc_spec hρ, fun N hN T hT => ?_⟩
  obtain ⟨P⟩ := hP L (le_of_max_le_left hL) N hN T hT
  have hgeo := hT.geometry
  have hF0 : ∀ ρ ∈ T.F, ρ ≠ 0 := hgeo.ensemble.1
  have hsep := hgeo.separated
  have hn := fun ϱ (h : ϱ ∈ T.F.image neutralizeAtWiredRoot) => neutral_of_mem_image hF0 h
  -- the base faces of a density lie in its support
  have hbase : ∀ (ϱ : RotatorDualFace L → ℤ), ∀ x ∈ baseSites ϱ, ϱ (some x) ≠ 0 :=
      fun ϱ x hx => by
    unfold baseSites at hx
    exact (Finset.mem_filter.mp hx).2.1
  refine ⟨routineS, fun ϱ h => routineWave P hα hL2 ϱ h (hn ϱ h).1 (hn ϱ h).2,
    fun ϱ h => ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- half mass on the base pieces
    have hm := half_mass_le_base ϱ (hn ϱ h).2
    refine hm.trans (le_of_eq ?_)
    show _ = ∑ t ∈ (Finset.univ : Finset ({x // x ∈ baseSites ϱ} ⊕ P.ι ϱ)).filter
      (fun t => Sum.elim (fun _ => 0) (P.scale ϱ) t = 0),
        |Sum.elim (fun x => 2 * |(ϱ (some x.1) : ℝ)|) (P.charge ϱ) t|
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    have h2 : ∑ t : P.ι ϱ, (if Sum.elim (fun _ => 0) (P.scale ϱ)
        (Sum.inr t : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ) = 0 then
        |Sum.elim (fun x => 2 * |(ϱ (some x.1) : ℝ)|) (P.charge ϱ)
          (Sum.inr t : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ)| else 0) = 0 :=
      Finset.sum_eq_zero fun t _ => ite_eq_right_iff.mpr fun h0 =>
        absurd h0 (show ¬ P.scale ϱ t = 0 by have := P.one_le_scale ϱ h t; omega)
    rw [h2, add_zero, ← Finset.sum_coe_sort (baseSites ϱ)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [abs_mul]
  · intro t
    rcases t with x | t
    · simp only [routineWave, Sum.elim_inl, pow_zero, mul_one]
      refine le_trans ?_ (show ((4 : ℕ) : ℝ) ≤ 100 by norm_num)
      exact_mod_cast (Finset.card_le_card fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        grad_basePiece_incident (Finset.mem_filter.mp he).2⟩).trans (card_incident_le_four x.1)
    · exact P.edge_count ϱ h t
  · have hcard : (((Finset.univ : Finset ({x // x ∈ baseSites ϱ} ⊕ P.ι ϱ)).filter fun t =>
        1 ≤ Sum.elim (fun _ => 0) (P.scale ϱ) t).card : ℝ) = Fintype.card (P.ι ϱ) := by
      rw [Finset.card_filter, Fintype.sum_sum_type]
      have h1 : ∑ x : {x // x ∈ baseSites ϱ}, (if 1 ≤ Sum.elim (fun _ => 0) (P.scale ϱ)
          (Sum.inl x : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ) then 1 else 0) = 0 :=
        Finset.sum_eq_zero fun x _ => by simp
      have h2 : ∑ t : P.ι ϱ, (if 1 ≤ Sum.elim (fun _ => 0) (P.scale ϱ)
          (Sum.inr t : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ) then 1 else 0) = Fintype.card (P.ι ϱ) := by
        rw [Finset.card_univ.symm, Finset.card_eq_sum_ones]
        exact Finset.sum_congr rfl fun t _ => ite_eq_left_iff.mpr fun h0 =>
          absurd (P.one_le_scale ϱ h t) h0
      rw [h1, h2, zero_add]
    exact (P.count ϱ h).trans hcard.ge
  · -- locality
    intro t e he
    rcases t with x | t
    · have hx := hbase ϱ x.1 x.2
      unfold routineS
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1, grad_basePiece_incident he, x.1,
        by unfold chargeSupport; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, ?_⟩
      rw [siteDist_self]
      have := boundaryAdjustedSize_nonneg (siteRestrict ϱ)
      linarith
    · exact P.local_ ϱ h t e he
  · -- orthogonality
    intro t ϱ' h' hne
    rcases t with x | t
    · simp only [routineWave, Sum.elim_inl]
      rw [pairing_basePiece]
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h'
      have hρσ : ρ ≠ σ := fun e => hne (e ▸ rfl)
      have hxρ : x.1 ∈ chargeSupport ρ := by
        unfold chargeSupport; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbase _ x.1 x.2⟩
      have hd := hgeo.ensemble.2 ρ hρ σ hσ hρσ
      have hxσ : x.1 ∉ chargeSupport σ := Finset.disjoint_left.mp hd hxρ
      have : σ x.1 = 0 := by unfold chargeSupport at hxσ; simpa using hxσ
      simp [this]
    · exact P.orth ϱ h t ϱ' h' hne
  · -- cross-density gradient disjointness
    intro ϱ' h' hne t t' e
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h'
    have hρσ : ρ ≠ σ := fun e => hne (e ▸ rfl)
    have memsupp : ∀ (τ : ChargeDensity L) (x : {x // x ∈ baseSites (neutralizeAtWiredRoot τ)}),
        x.1 ∈ chargeSupport τ := fun τ x => by
      unfold chargeSupport; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbase _ x.1 x.2⟩
    rcases t with x | t <;> rcases t' with x' | t'
    · by_contra hh
      push Not at hh
      have hxx : x.1 ≠ x'.1 := fun hx => Finset.disjoint_left.mp
        (hgeo.ensemble.2 ρ hρ σ hσ hρσ) (memsupp ρ x) (hx ▸ memsupp σ x')
      have h1 := l1_eq_one_of_grad_basePiece hxx hh.1 hh.2
      have hd : euclideanSetDistance (chargeSupport ρ) (chargeSupport σ) ≤ 1 := by
        have := (setDist_le_siteDist (memsupp ρ x) (memsupp σ x')).trans
          (siteDist_le_l1 x.1 x'.1)
        rw [h1] at this
        simpa using this
      have hs := hsep ρ hρ σ hσ hρσ
      have hmin : 1 ≤ min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) :=
        le_min (one_le_boundaryAdjustedSize (hF0 ρ hρ)) (one_le_boundaryAdjustedSize (hF0 σ hσ))
      have hpow := le_rpow_self hmin one_le_chargeCoverExponent
      have hM : (chargeCoverScale : ℝ) = 65536 := by norm_num [chargeCoverScale]
      rw [hM] at hs
      linarith
    · by_cases hb : (squareZero L).grad (basePiece (neutralizeAtWiredRoot ρ) x.1) e = 0
      · exact Or.inl hb
      · exact Or.inr (P.avoid _ h' t' ρ hρ x.1 (memsupp ρ x) e (grad_basePiece_incident hb))
    · by_cases hb : (squareZero L).grad (basePiece (neutralizeAtWiredRoot σ) x'.1) e = 0
      · exact Or.inr hb
      · exact Or.inl (P.avoid _ h t σ hσ x'.1 (memsupp σ x') e (grad_basePiece_incident hb))
    · exact P.disj _ h _ h' hne t t' e
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
    exact card_routineS_le (hF0 ρ hρ)
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
    exact exists_routineRoute hL2 (hF0 ρ hρ)
  · exact fun k e U hU hk => routineS_overlap hsep hF0 k e U hU hk

theorem routineKv_nonneg : (0 : ℝ) ≤ routineKv := by
  unfold routineKv
  positivity

/-- **FS81 Theorem C from the profile family.** -/
theorem theoremC_of_pinnedTerminalProfiles {α K₀ K₁ cP : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hcP : 0 < cP) (hP : PinnedTerminalProfiles α K₀ K₁ cP L₀) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_pinnedTerminalWaves hα (lt_max_of_lt_left (by norm_num))
    (lt_max_of_lt_left (by norm_num)) hcP routineKv_nonneg
    (pinnedTerminalWaves_of_profiles hα hP)

/-- **The Kosterlitz–Thouless transition from the profile family.** -/
theorem exists_transition_of_pinnedTerminalProfiles {α K₀ K₁ cP : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hcP : 0 < cP) (hP : PinnedTerminalProfiles α K₀ K₁ cP L₀) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_pinnedTerminalWaves hα (lt_max_of_lt_left (by norm_num))
    (lt_max_of_lt_left (by norm_num)) hcP routineKv_nonneg
    (pinnedTerminalWaves_of_profiles hα hP)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
