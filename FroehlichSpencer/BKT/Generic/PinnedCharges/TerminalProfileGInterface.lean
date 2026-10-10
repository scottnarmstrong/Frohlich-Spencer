/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineAssembly

/-!
# The corrected profile interface: pieces for charged selected squares (TW1G)

A selected square whose charge restriction is **neutral**
(possible exactly when its cluster has diameter in `(2^j, √2·2^j]`, where isolation does not
apply) admits no piece: a piece is flat at every charge (`avoid`), so on a dense neutral cluster it
is constant and pairs to zero.

The neutral selected clusters form a laminar family of sets with at
least two charges, hence number fewer than `‖ρ‖₁`; this module therefore asks only for

`c_P · Σ_j |P'_j| ≤ #pieces + ‖ϱ‖₁`   (`TerminalProfilesW.countW`),

and shows that this weaker count still yields the pinned layer (`layerA_le_piecesW`: the extra
`‖ϱ‖₁` is absorbed with the same `D₁`), hence Theorem C:

* `pinnedTerminalWavesW_of_profilesW`, `pinnedLayerHypothesisD_of_terminalWavesW`;
* `theoremC_of_pinnedTerminalProfilesW`, `exists_transition_of_pinnedTerminalProfilesW`.

`TerminalProfilesW` extends `TerminalProfiles … 0 …` (whose own count clause is then trivial).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open Filter
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}


structure TerminalProfilesW (L : ℕ) (α K₀ K₁ cP : ℝ) (F : Finset (ChargeDensity L))
    extends TerminalProfiles L α K₀ K₁ 0 F where
  countW : ∀ ϱ ∈ F.image neutralizeAtWiredRoot,
    cP * layerSelectedSum ϱ ≤ (Fintype.card (ι ϱ) : ℝ) + ∑ j, |(ϱ j : ℝ)|

/-- **The corrected profile hypothesis** on every comb terminal. -/
def PinnedTerminalProfilesW (α K₀ K₁ cP : ℝ) (L₀ : ℕ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L → ∀ N : ℕ, 1 ≤ N → ∀ T : SelConfig L, IsCombTerminal N T →
    Nonempty (TerminalProfilesW L α K₀ K₁ cP T.F)

/-- The terminal waves with the weak count. -/
def PinnedTerminalWavesW (α K₀ K₁ cP Kv : ℝ) (Kov L₀ : ℕ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L →
  ∃ (centerOf : (RotatorDualFace L → ℤ) → RotatorDualFace L)
    (dsc : (RotatorDualFace L → ℤ) → ℕ),
    (∀ ρ : ChargeDensity L, ρ ≠ 0 →
      1 ≤ dsc (neutralizeAtWiredRoot ρ) ∧
        (dsc (neutralizeAtWiredRoot ρ) : ℝ) + 1 ≤ 2 ^ 16 * boundaryAdjustedSize ρ) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ T : SelConfig L, IsCombTerminal N T →
    ∃ (S : (RotatorDualFace L → ℤ) → Finset (SquareZeroBond L))
      (wv : ∀ ϱ ∈ T.F.image neutralizeAtWiredRoot,
        GradedSpinWave.{0, 0, 0} (squareZero L) ∅ centerOf ϱ),
      (∀ ϱ (h : ϱ ∈ T.F.image neutralizeAtWiredRoot),
        IsTerminalWave α K₀ K₁ 0 ϱ (wv ϱ h) ∧
        cP * layerSelectedSum ϱ ≤ ((letI := (wv ϱ h).finite;
          (Finset.univ.filter fun t => 1 ≤ (wv ϱ h).scale t).card : ℕ) : ℝ) +
          ∑ j, |(ϱ j : ℝ)| ∧
        (∀ t e, (squareZero L).grad ((wv ϱ h).piece t) e ≠ 0 → e ∈ S ϱ) ∧
        (∀ t, ∀ ϱ' ∈ T.F.image neutralizeAtWiredRoot, ϱ' ≠ ϱ →
          ∑ j, (wv ϱ h).piece t j * (ϱ' j : ℝ) = 0) ∧
        (∀ ϱ' (h' : ϱ' ∈ T.F.image neutralizeAtWiredRoot), ϱ ≠ ϱ' → ∀ t t' e,
          (squareZero L).grad ((wv ϱ h).piece t) e = 0 ∨
            (squareZero L).grad ((wv ϱ' h').piece t') e = 0) ∧
        ((S ϱ).card : ℝ) ≤ Kv * ((dsc ϱ : ℝ) + 1) ^ 2 ∧
        (∃ r : SquareZeroBond L → ℤ, (∀ e, r e ≠ 0 → e ∈ S ϱ) ∧
          (∀ e, |(r e : ℝ)| ≤ ∑ j, |(ϱ j : ℝ)|) ∧
          ∀ σ : RotatorDualFace L → ℝ,
            ∑ j, σ j * (ϱ j : ℝ) = ∑ e, (r e : ℝ) * (squareZero L).grad σ e)) ∧
      ∀ (k : ℕ) (e : SquareZeroBond L) (U : Finset (RotatorDualFace L → ℤ)),
        U ⊆ T.F.image neutralizeAtWiredRoot →
        (∀ ρ ∈ U, 2 ^ k - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (k + 1) - 2 ∧ e ∈ S ρ) → U.card ≤ Kov


theorem pinnedTerminalWavesW_of_profilesW {α K₀ K₁ cP : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hP : PinnedTerminalProfilesW α K₀ K₁ cP L₀) :
    PinnedTerminalWavesW α (max 4 K₀) (max 2 K₁) cP routineKv 1 (max L₀ 2) := by
  intro L hL
  have hL2 : 1 < L := by have := le_max_right L₀ 2; omega
  refine ⟨routineCenter, routineDsc, fun ρ hρ => routineDsc_spec hρ, fun N hN T hT => ?_⟩
  obtain ⟨PW⟩ := hP L (le_of_max_le_left hL) N hN T hT
  let P := PW.toTerminalProfiles
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
    fun ϱ h => ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
  · rw [zero_mul]
    exact Nat.cast_nonneg _
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
    exact (PW.countW ϱ h).trans (by rw [← hcard]; exact le_rfl)
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


/-- `A ≤ D₁(‖ϱ‖₁ + #pieces)` with `D₁ = layerD₁ (1 + 1/c_P)` when `c_P · #selected ≤ #pieces`. -/
theorem layerA_le_piecesW {L : ℕ} {F : Finset (ChargeDensity L)}
    (hiso : HasBoundaryIsolation (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ : ChargeDensity L} (hρ : ρ ∈ F) (hρ0 : ρ ≠ 0) {cP P : ℝ} (hcP : 0 < cP)
    (hP0 : 0 ≤ P) (hP : cP * layerSelectedSum (neutralizeAtWiredRoot ρ) ≤
      P + ∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)|) :
    layerA (neutralizeAtWiredRoot ρ) ≤
      layerD₁ * (1 + 1 / cP) * (∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)| + P) := by
  set m := ∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)|
  have hsel : layerSelectedSum (neutralizeAtWiredRoot ρ) ≤ (P + m) / cP := by
    rw [le_div_iff₀ hcP]
    linarith
  have h := layerA_le hiso hρ hρ0 hsel
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP0 : 0 ≤ P := hP0
  have hD := layerD₁_pos
  have hinv : 0 < 1 / cP := by positivity
  have hPc : (P + m) / cP = (1 / cP) * P + (1 / cP) * m := by ring
  refine h.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hD.le
  rw [hPc]
  nlinarith

/-- **The pinned layer hypothesis from the terminal waves and the coefficient bound.** -/
theorem pinnedLayerHypothesisD_of_terminalWavesW {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hC : CombCoefficientBound c₁ c₂) {α K₀ K₁ cP Kv : ℝ} {Kov L₀ : ℕ} (hα : 1 < α)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hcP : 0 < cP) (hKv : 0 ≤ Kv)
    (hW : PinnedTerminalWavesW α K₀ K₁ cP Kv Kov L₀) :
    PinnedLayerHypothesisD := by
  refine ⟨layerD₁ * (1 + 1 / cP), c₁ + c₂, α, K₀, K₁, Kv, 0, 0, Kov, L₀, hα, hK₀, hK₁,
    by have := layerD₁_pos; positivity, hKv, ?_⟩
  intro L hL N hN
  obtain ⟨centerOf, dsc, hdsc, hT⟩ := hW L hL
  have spec := combBranches_spec (L := L) hN
  have hterm : ∀ i : Fin (combBranches L N).length,
      IsCombTerminal N ((combBranches L N)[i.1]).2 :=
    fun i => (spec.1 _ (List.getElem_mem _)).2
  choose S wv hcl hov using fun i : Fin (combBranches L N).length =>
    hT N hN ((combBranches L N)[i.1]).2 (hterm i)
  have hne : ∀ i : Fin (combBranches L N).length, ∀ ρ ∈ ((combBranches L N)[i.1]).2.F, ρ ≠ 0 :=
    fun i => (hterm i).geometry.ensemble.1
  let layer : RootedChargeLayerD (squareZero L) none (pinnedCombLam L N) centerOf layerA
      (fun _ => 1) (layerD₁ * (1 + 1 / cP)) (c₁ + c₂) α K₀ K₁ :=
    { n := (combBranches L N).length
      N := fun i => ((combBranches L N)[i.1]).2.F.image neutralizeAtWiredRoot
      c := fun i => ((combBranches L N)[i.1]).1
      K := fun i ϱ => ((combBranches L N)[i.1]).2.K (siteRestrict ϱ)
      S := S
      c_pos := fun i => (spec.1 _ (List.getElem_mem _)).1
      c_sum := by
        rw [Fin.sum_univ_fun_getElem (combBranches L N) fun b => b.1]
        exact spec.2.1
      neutral := fun i ϱ hϱ => by
        obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hϱ
        exact sum_neutralizeAtWiredRoot ρ
      expand := fun ψ hψ => by
        rw [prod_pinnedCombLam_eq_branches hN ψ hψ, ← Fin.sum_univ_fun_getElem]
      entropy := fun i ϱ hϱ => by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        rw [siteRestrict_neutralize, mul_one]
        exact (hC L N _ (hterm i) ρ hρ).trans
          (Real.exp_le_exp.mpr (exp_le_of_coefficientBound hc₁ hc₂ ρ))
      wv := wv
      layer := fun i ϱ hϱ => by
        obtain ⟨hα', hK₀', hK₁', hbase, hedge, -⟩ := (hcl i ϱ hϱ).1
        have hsel := (hcl i ϱ hϱ).2.1
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        exact ⟨hα', hK₀', hK₁', hbase, hedge,
          layerA_le_piecesW (hterm i).geometry.isolated hρ (hne i ρ hρ) hcP (Nat.cast_nonneg _) hsel,
          fun _ _ h => absurd h (Finset.notMem_empty _)⟩
      wv_local := fun i ϱ hϱ t e he => (hcl i ϱ hϱ).2.2.1 t e he
      wv_orth := fun i ϱ hϱ t ϱ' hϱ' hne' => (hcl i ϱ hϱ).2.2.2.1 t ϱ' hϱ' hne'
      wv_disj := fun i ϱ hϱ ϱ' hϱ' hne' t t' e => (hcl i ϱ hϱ).2.2.2.2.1 ϱ' hϱ' hne' t t' e }
  refine ⟨{
    centerOf := centerOf
    A := layerA
    Zent := fun _ => 1
    layer := layer
    dsc := dsc
    isLocal := ?_
    entropy_exp := fun ϱ => by simp }⟩
  refine ⟨fun i ϱ hϱ => ?_, fun i ϱ hϱ => ?_, fun i ϱ hϱ => (hcl i ϱ hϱ).2.2.2.2.2.1,
    fun i ϱ hϱ => (hcl i ϱ hϱ).2.2.2.2.2.2, fun i k e U hU hk => hov i k e U hU hk,
    fun i ϱ hϱ => ?_⟩
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    intro h0
    apply hne i ρ hρ
    rw [← siteRestrict_neutralize ρ, h0]
    rfl
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    exact (hdsc ρ (hne i ρ hρ)).1
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    exact logb_le_layerA (hne i ρ hρ) (hdsc ρ (hne i ρ hρ)).2


/-- **FS81 Theorem C from the corrected profile family.** -/
theorem theoremC_of_pinnedTerminalProfilesW {α K₀ K₁ cP : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hcP : 0 < cP) (hP : PinnedTerminalProfilesW α K₀ K₁ cP L₀) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_pinnedLayerD (pinnedLayerHypothesisD_of_terminalWavesW
    (Real.log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    combCoefficientBound hα (lt_max_of_lt_left (by norm_num)) (lt_max_of_lt_left (by norm_num))
    hcP routineKv_nonneg (pinnedTerminalWavesW_of_profilesW hα hP))

/-- **The Kosterlitz–Thouless transition from the corrected profile family.** -/
theorem exists_transition_of_pinnedTerminalProfilesW {α K₀ K₁ cP : ℝ} {L₀ : ℕ} (hα : 1 < α)
    (hcP : 0 < cP) (hP : PinnedTerminalProfilesW α K₀ K₁ cP L₀) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_pinnedLayerD (pinnedLayerHypothesisD_of_terminalWavesW
    (Real.log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    combCoefficientBound hα (lt_max_of_lt_left (by norm_num)) (lt_max_of_lt_left (by norm_num))
    hcP routineKv_nonneg (pinnedTerminalWavesW_of_profilesW hα hP))

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
