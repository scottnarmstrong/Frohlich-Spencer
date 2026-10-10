/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryAssemblyRemainder
import Mathlib.Tactic


@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator

variable {R n : ℕ}

/-- The face parts of the extended ensemble `rem(C) ∪ {p}` at the D1 scales. -/
def rootedMarkedExtFaces (R n : ℕ) (hn : n ≤ R)
    (N C T : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    Finset (ChargeDensity (sideLength R)) :=
  (rootedMarkedExtension (chargeCoverScale : ℝ) chargeCoverExponent R n hn N C T).image siteRestrict


def rootedMarkedProfileWave (R n : ℕ) (hn : n ≤ R) (ξ : ℝ)
    (N C T : Finset (RotatorDualFace (sideLength R) → ℤ)) (c₀ : ℝ)
    (q : rootedMarkedP4Index (rootedMarkedProxy R n hn C T) → ℝ) :
    RotatorDualFace (sideLength R) → ℝ :=
  fun j => c₀ * rootedRealSquareBaseWave (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) j +
    ∑ t, q t * rootedMarkedP4Wave (rootedMarkedExtFaces R n hn N C T)
      (rootedMarkedProxy R n hn C T) t j

/-- **The remainder waves of a marked term.** -/
theorem exists_rootedMarkedRemainderWaves (hn : n ≤ R) (hn0 : 0 < n)
    {ξ τ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hτ : 0 < τ)
    (F : Finset (ChargeDensity (sideLength R)))
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    (hbad : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, badSelectedSum ϱ ≤ ∑ j, |(ϱ j : ℝ)|)
    (K : (RotatorDualFace (sideLength R) → ℤ) → ℝ)
    (hK : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, |K ϱ| ≤ Real.exp (fejerLayerD₂ * layerA ϱ))
    {amp : ℝ} {k₀ : ℕ} (hamp : 0 ≤ amp) (hk₀ : 1 ≤ k₀)
    (hs : 0 ≤ amp / (8 * fejerLayerD₁) - fejerLayerD₂)
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 8)
    (hexp : 100 * 4 ^ k₀ * costMajorant (τ / 2) (τ / 2) (amp * 8) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (τ / 2) * 6400))
    (C : Finset (RotatorDualFace (sideLength R) → ℤ))
    (hC : C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot))
    (T : Finset (RotatorDualFace (sideLength R) → ℤ)) (hT : T ⊆ C)
    (hL : 1 < sideLength R) (c₀ : ℝ)
    (q : rootedMarkedP4Index (rootedMarkedProxy R n hn C T) → ℝ) :
    let Rm := remainder (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot) C
    let σ := rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
    let a₀ := rootedMarkedProfileWave R n hn ξ (F.image neutralizeAtWiredRoot) C T c₀ q
    ∃ a : (RotatorDualFace (sideLength R) → ℤ) → RotatorDualFace (sideLength R) → ℝ,
      (∀ ϱ ∈ Rm, Multigraph.pairing (a ϱ) σ = 0) ∧
      (∀ ϱ ∈ Rm, ∀ ϱ' ∈ Rm, ϱ ≠ ϱ' →
        Multigraph.pairing (a ϱ) (fun j => (ϱ' j : ℝ)) = 0) ∧
      (∀ ϱ ∈ Rm, Multigraph.pairing a₀ ((squareZero (sideLength R)).laplacian (a ϱ)) = 0) ∧
      (∀ ϱ ∈ Rm, ∀ ϱ' ∈ Rm, ϱ ≠ ϱ' →
        Multigraph.pairing (a ϱ) ((squareZero (sideLength R)).laplacian (a ϱ')) = 0) ∧
      (∀ ϱ ∈ Rm, |K ϱ| * Real.exp (-gffTranslationEnergy (squareZero (sideLength R)) τ (a ϱ)
        (fun j => (ϱ j : ℝ))) ≤ 1) := by
  intro Rm σ a₀
  classical
  set N := F.image neutralizeAtWiredRoot with hN
  set p := rootedMarkedProxy R n hn C T with hp
  set Fext := rootedMarkedExtFaces R n hn N C T with hFext
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hEG := rootedMarkedExtensionGeometry_holds (M := (chargeCoverScale : ℝ))
    (α := chargeCoverExponent) (by norm_num [chargeCoverScale])
    (le_trans zero_le_one one_le_chargeCoverExponent) hn hn0 F hgeo.ensemble hgeo.separated
    C T hCN hT
  obtain ⟨hFextPin, hFextSep, hNeutralExt, hpNotRem, -⟩ := hEG
  change IsPinnedChargeEnsemble Fext at hFextPin
  change IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent Fext at hFextSep
  change Fext.image neutralizeAtWiredRoot = _ at hNeutralExt
  have hmemRm : ∀ ϱ ∈ Rm, ϱ ∈ Fext.image neutralizeAtWiredRoot := fun ϱ h => by
    rw [hNeutralExt]
    exact Finset.mem_insert_of_mem h
  have hmemP : p ∈ Fext.image neutralizeAtWiredRoot := by
    rw [hNeutralExt]
    exact Finset.mem_insert_self _ _
  have hneu : ∀ ϱ ∈ Fext.image neutralizeAtWiredRoot, ϱ ≠ 0 ∧ ∑ j, ϱ j = 0 :=
    fun ϱ h => neutral_of_mem_image hFextPin.1 h
  have hsr : ∀ ϱ ∈ Fext.image neutralizeAtWiredRoot,
      siteRestrict ϱ ∈ Fext ∧ neutralizeAtWiredRoot (siteRestrict ϱ) = ϱ :=
    fun ϱ h => neutralize_siteRestrict_of_mem h
  have hne_p : ∀ ϱ ∈ Rm, ϱ ≠ p := by
    intro ϱ h e
    have hpRm : p ∈ Rm := e ▸ h
    exact hpNotRem hpRm
  have hsr_ne : ∀ ϱ ∈ Rm, siteRestrict ϱ ≠ siteRestrict p := by
    intro ϱ h e
    apply hne_p ϱ h
    rw [← (hsr ϱ (hmemRm ϱ h)).2, ← (hsr p hmemP).2, e]
  have hα : (1 : ℝ) < 7 / 4 := by norm_num
  let PG := markedProfilesG hFextPin.1 hFextSep hL (7 / 4) (by norm_num)
  let P := PG.toTerminalProfiles
  let Wv : ∀ ϱ, ϱ ∈ Rm → GradedSpinWave.{0, 0, 0} (squareZero (sideLength R)) ∅ routineCenter ϱ :=
    fun ϱ h => routineWave P hα hL ϱ (hmemRm ϱ h) (hneu ϱ (hmemRm ϱ h)).1 (hneu ϱ (hmemRm ϱ h)).2
  let a : (RotatorDualFace (sideLength R) → ℤ) → RotatorDualFace (sideLength R) → ℝ := fun ϱ =>
    if h : ϱ ∈ Rm then envelopeWave (Wv ϱ h) (τ / 2) amp k₀ else 0
  have ha : ∀ ϱ (h : ϱ ∈ Rm), a ϱ = envelopeWave (Wv ϱ h) (τ / 2) amp k₀ :=
    fun ϱ h => by simp only [a, h, ↓reduceDIte]
  -- the face supports of the members
  have hbaseSupp : ∀ (ϱ : RotatorDualFace (sideLength R) → ℤ) (x : {x // x ∈ baseSites ϱ}),
      x.1 ∈ chargeSupport (siteRestrict ϱ) := by
    intro ϱ x
    have hx := x.2
    unfold baseSites at hx
    exact mem_chargeSupport'.2 (Finset.mem_filter.mp hx).2.1
  have hσp : ∀ y : Generic.PinnedCharges.Site (sideLength R), σ (some y) ≠ 0 →
      y ∈ chargeSupport (siteRestrict p) := fun y hy =>
    mem_chargeSupport'.2 ((rootedMarkedComposite_ne_zero_iff_proxy hn hξ0 hξ1 C T (some y)).mp hy)
  -- every piece of a remainder wave avoids the composite wave
  have hpieceA₀ : ∀ ϱ (h : ϱ ∈ Rm) (t : (Wv ϱ h).ι) (e : SquareZeroBond (sideLength R)),
      (squareZero (sideLength R)).grad ((Wv ϱ h).piece t) e = 0 ∨
        (squareZero (sideLength R)).grad a₀ e = 0 := by
    intro ϱ h t e
    by_cases hpt : (squareZero (sideLength R)).grad ((Wv ϱ h).piece t) e = 0
    · exact Or.inl hpt
    right
    have hϱF := (hsr ϱ (hmemRm ϱ h)).1
    have hpF := (hsr p hmemP).1
    apply grad_add_sum_eq_zero
    · by_contra hb
      obtain ⟨y, hyσ, hinc⟩ := exists_face_of_rootedRealSquareBaseWave_grad_ne σ e hb
      rcases t with x | t
      · exact not_incident_both_of_separated hFextPin hFextSep hϱF hpF (hsr_ne ϱ h)
          (hbaseSupp ϱ x) (hσp y hyσ) (grad_basePiece_incident hpt) hinc
      · exact hpt (P.avoid ϱ (hmemRm ϱ h) t (siteRestrict p) hpF y (hσp y hyσ) e hinc)
    · intro t'
      rcases t with x | t
      · exact P.avoid p hmemP t' (siteRestrict ϱ) hϱF x.1 (hbaseSupp ϱ x) e
          (grad_basePiece_incident hpt)
      · exact (P.disj ϱ (hmemRm ϱ h) p hmemP (hne_p ϱ h) t t' e).resolve_left hpt
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · -- orthogonality to the composite
    intro ϱ h
    rw [ha ϱ h]
    apply pairing_envelopeWave_eq_zero
    intro t
    rcases t with x | t
    · have hx : x.1 ∉ chargeSupport (siteRestrict p) := fun hx =>
        Finset.disjoint_left.mp (hFextPin.2 _ (hsr ϱ (hmemRm ϱ h)).1 _ (hsr p hmemP).1
          (hsr_ne ϱ h)) (hbaseSupp ϱ x) hx
      exact pairing_basePiece_rootedMarkedComposite hn hξ0 hξ1 ϱ hx
    · have hc := rootedMarkedProfileContext_of_profileIndex hFextPin.1 hFextSep (hmemRm ϱ h)
        t.1 t.2
      exact ProfileContext.pairing_profilePiece_rootedMarkedComposite hn hn0 hc ξ
        (hsr p hmemP).1 (hsr_ne ϱ h).symm (hsr p hmemP).2
  · -- mutual orthogonality
    intro ϱ h ϱ' h' hne
    rw [ha ϱ h]
    apply pairing_envelopeWave_eq_zero
    intro t
    exact routineWave_orth P hα hL hFextPin (hmemRm ϱ h) _ _ t (hmemRm ϱ' h') (Ne.symm hne)
  · -- gradient orthogonality to the composite wave
    intro ϱ h
    rw [ha ϱ h]
    apply pairing_laplacian_eq_zero_of_grad_disjoint
    intro e
    exact (grad_envelopeWave_disjoint (Wv ϱ h) (τ / 2) amp k₀ (hpieceA₀ ϱ h) e).symm
  · -- mutual gradient orthogonality
    intro ϱ h ϱ' h' hne
    rw [ha ϱ h, ha ϱ' h']
    apply pairing_laplacian_eq_zero_of_grad_disjoint
    apply grad_envelopeWave_disjoint
    intro t e
    exact (grad_envelopeWave_disjoint (Wv ϱ' h') (τ / 2) amp k₀
      (fun t' e => (routineWave_grad_disjoint_cross P hα hL hFextPin hFextSep (hmemRm ϱ h) _ _
        (hmemRm ϱ' h') _ _ hne t t' e).symm) e).symm
  · -- renormalized activities
    intro ϱ h
    rw [ha ϱ h]
    obtain ⟨hbase, hedge, hcard⟩ := routineWave_layerData P hα hL (hmemRm ϱ h)
      (hneu ϱ (hmemRm ϱ h)).1 (hneu ϱ (hmemRm ϱ h)).2
    have hϱN : ϱ ∈ N := remainder_subset _ _ h
    obtain ⟨hρF, hρeq⟩ := neutralize_siteRestrict_of_mem hϱN
    have hρ0 : siteRestrict ϱ ≠ 0 := hgeo.ensemble.1 _ hρF
    have hcount : (1 / 3 : ℝ) * layerSelectedSum (neutralizeAtWiredRoot (siteRestrict ϱ)) ≤
        (Fintype.card (P.ι ϱ) : ℝ) + ∑ k, |(neutralizeAtWiredRoot (siteRestrict ϱ) k : ℝ)| := by
      rw [hρeq, layerSelectedSum_eq_good_add_bad]
      have hg := PG.countG ϱ (hmemRm ϱ h)
      have hb := hbad ϱ hϱN
      have hb0 := badSelectedSum_nonneg ϱ
      change goodSelectedSum ϱ ≤ 3 * (Fintype.card (P.ι ϱ) : ℝ) at hg
      linarith
    have hcover := layerA_le_piecesW hgeo.isolated hρF hρ0 (by norm_num : (0 : ℝ) < 1 / 3)
      (Nat.cast_nonneg _) hcount
    rw [hρeq] at hcover
    have hA0 : 0 ≤ layerA ϱ := by
      unfold layerA layerCoverSum
      exact add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    refine abs_mul_exp_envelopeWave_le_one (Wv ϱ h) (A := layerA ϱ) (D₁ := fejerLayerD₁)
      (D₂ := fejerLayerD₂) (α := 7 / 4) (K₀ := 6400) (K₁ := 8) rfl
      (by simp only [Wv, routineWave]; norm_num) (by simp only [Wv, routineWave]; norm_num) hbase hedge ?_ (hK ϱ hϱN) hA0 hτ
      (by norm_num) (by norm_num) ?_ hamp hk₀ hs hquad₂ hexp hquad₁
    · rw [hcard]
      simpa [fejerLayerD₁, add_comm] using hcover
    · unfold fejerLayerD₁
      have := layerD₁_pos
      positivity

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
