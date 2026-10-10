/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProxy
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGState
import Mathlib.Tactic

/-!
Proofs of the two Appendix D statements of `MarkedGeometryProxy.lean`.

* **`rootedMarkedExtensionGeometry_holds`**: the face parts of the extended ensemble
  `rem(C) ∪ {p}` form a pinned, boundary-separated ensemble.

The remainder is separated from the
  composite support `X(C)` at scale `M min(d_Λ(ϱ), D(C))^α` because it is not adjacent to `C`.

`D(C)` dominates `d_Λ` of the proxy's face part (`boundaryAdjustedSize_siteRestrict_proxy_le`).
* **`rootedMarkedChargedSplit_holds`**: the rooted charged-split lemma.

Take a boundary-far
  isolated part `A` of `X(C)` that does not cut the mark.

The integer satellite has nonzero
  charge on `A` (`sum_rootedMarkedSatellite_ne_zero_of_split`).
  - A member meeting `A` is *big* if it straddles the split, or if it is face-charged and lies
    in `A`.

Big members have `M d_Λ^α > diam(A)`, so two of them would violate the Appendix D
    separation.
  - If a big member exists, it is the only member with charge on `A`.

A straddling member is
    charged on `A` by Appendix D isolation; a charged member lies inside `A` with its charge.
  - Otherwise `A` and `B` both consist of whole members, and the member closest to the mark
    side violates the cluster adjacency (`exists_adj_sdiff_of_mem_clusters`).
* **`hasFarConstituentCharge_rootedMarkedProxy`**: the proxy's face part has the charged half of
  Appendix D isolation on boundary-far constituents.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges (euclideanSetDistance euclideanSetDiameter
  euclideanBoundaryDistance boundaryAdjustedSize totalCharge chargeEuclideanDiameter
  chargeBoundaryDistance IsConstituent IsPinnedChargeEnsemble IsBoundarySeparated
  AppendixDChargeGeometry neutralizeAtWiredRoot chargeRestriction)

/-! ### Generic facts -/

/-- A member of a part of a cluster is adjacent to the rest of the cluster. -/
theorem exists_adj_sdiff_of_mem_clusters {ι : Type*} [DecidableEq ι]
    {adj : ι → Finset ι → Prop} (hmono : AdjMonotone adj) {N C : Finset ι}
    (hC : C ∈ clusters adj N) {CQ : Finset ι} (hCQ : CQ ⊆ C) (hne : CQ.Nonempty) :
    ∃ m ∈ CQ, adj m (C \ CQ) := by
  by_contra h
  push Not at h
  have hsub : component adj C ⊆ C \ CQ := component_subset_of_closed hmono fun m hm hadj => by
    by_cases hmQ : m ∈ CQ
    · exact absurd hadj (h m hmQ)
    · exact Finset.mem_sdiff.2 ⟨hm, hmQ⟩
  rw [(mem_clusters.1 hC).2] at hsub
  obtain ⟨x, hx⟩ := hne
  exact (Finset.mem_sdiff.1 (hsub (hCQ hx))).2 hx

section Euclid

variable {L : ℕ}

/-- The boundary distance of a finite set decreases when the set grows. -/
theorem euclideanBoundaryDistance_anti {s t : Finset (Fin L × Fin L)} (hs : s.Nonempty)
    (hst : s ⊆ t) : euclideanBoundaryDistance t ≤ euclideanBoundaryDistance s := by
  unfold euclideanBoundaryDistance
  rw [dite_eq_left hs, dite_eq_left (hs.mono hst)]
  exact Finset.min'_subset _ (Finset.image_subset_image hst)

theorem euclideanBoundaryDistance_nonneg (s : Finset (Fin L × Fin L)) :
    0 ≤ euclideanBoundaryDistance s := by
  by_cases hs : s.Nonempty
  · exact (Generic.PinnedCharges.euclideanBoundaryDistance_pos_of_nonempty s hs).le
  · unfold euclideanBoundaryDistance
    rw [dite_eq_right hs]

/-- The distance to a set decreases when the set grows. -/
theorem euclideanSetDistance_anti_right (s : Finset (Fin L × Fin L))
    {t t' : Finset (Fin L × Fin L)} (ht : t.Nonempty) (h : t ⊆ t') :
    euclideanSetDistance s t' ≤ euclideanSetDistance s t := by
  by_cases hs : s.Nonempty
  · exact Generic.PinnedCharges.SelectionG.setDist_le_of_subset (Finset.Subset.refl s) h hs ht
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hs
    subst this
    simp [euclideanSetDistance]

/-- `d_Λ ≤ max(d_bdry, diam)` for every density. -/
theorem boundaryAdjustedSize_le_max (ρ : ChargeDensity L) :
    boundaryAdjustedSize ρ ≤ max (chargeBoundaryDistance ρ) (chargeEuclideanDiameter ρ) := by
  by_cases hρ : totalCharge ρ = 0
  · rw [Generic.PinnedCharges.boundaryAdjustedSize_of_neutral ρ hρ]
    exact le_max_right _ _
  · rw [Generic.PinnedCharges.boundaryAdjustedSize_of_charged ρ hρ]

end Euclid

/-! ### The cluster scale -/

section Scale

variable {R n : ℕ}

theorem one_le_diam_rootedMarkedSupport (hn : n ≤ R) (hn0 : 0 < n)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    1 ≤ euclideanSetDiameter (rootedMarkedSupport R n hn C) :=
  (Generic.PinnedCharges.SelectionG.one_le_siteDist (rootedCenter_ne_axialSite hn hn0)).trans
    (Generic.PinnedCharges.SelectionG.siteDist_le_diam
      (rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites]))
      (rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])))

theorem diam_rootedMarkedSupport_le_rootedClusterSize (hn : n ≤ R)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    euclideanSetDiameter (rootedMarkedSupport R n hn C) ≤ rootedClusterSize R n hn C := by
  unfold rootedClusterSize
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem rootedClusterSize_nonneg (hn : n ≤ R) (C : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    0 ≤ rootedClusterSize R n hn C :=
  (Generic.PinnedCharges.SelectionG.diam_nonneg _).trans
    (diam_rootedMarkedSupport_le_rootedClusterSize hn C)

/-- `D(C) = diam X(C)` for a cluster of face-neutral members. -/
theorem rootedClusterSize_of_neutral (hn : n ≤ R)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : ∀ m ∈ C, totalCharge (siteRestrict m) = 0) :
    rootedClusterSize R n hn C = euclideanSetDiameter (rootedMarkedSupport R n hn C) := by
  unfold rootedClusterSize
  rw [ite_eq_left hC]

theorem rootedClusterSize_mono (hn : n ≤ R)
    {C C' : Finset (RotatorDualFace (sideLength R) → ℤ)} (h : C ⊆ C') :
    rootedClusterSize R n hn C ≤ rootedClusterSize R n hn C' := by
  have hd : euclideanSetDiameter (rootedMarkedSupport R n hn C) ≤
      euclideanSetDiameter (rootedMarkedSupport R n hn C') :=
    Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _ (rootedMarkedSupport_nonempty hn C)
      (rootedMarkedSupport_nonempty hn C') (rootedMarkedSupport_mono hn h)
  unfold rootedClusterSize
  split_ifs with h1 h2 h2
  · exact hd
  · exact hd.trans (le_max_right _ _)
  · exact absurd (fun m hm => h2 m (h hm)) h1
  · exact max_le_max le_rfl hd

theorem rootedMarkScale_nonneg (hn : n ≤ R) (ϱ : RotatorDualFace (sideLength R) → ℤ)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) : 0 ≤ rootedMarkScale R n hn ϱ C :=
  le_min (Generic.PinnedCharges.SelectionG.boundaryAdjustedSize_nonneg _)
    (rootedClusterSize_nonneg hn C)

/-- **The marked adjacency is monotone**, so `cos_mul_prod_eq_sum_clusters` applies. -/
theorem rootedMarkAdjacent_monotone {M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α) (hn : n ≤ R) :
    AdjMonotone (RootedMarkAdjacent M α R n hn) := by
  intro ϱ C C' h hadj
  unfold RootedMarkAdjacent at hadj ⊢
  calc euclideanSetDistance (chargeSupport (siteRestrict ϱ)) (rootedMarkedSupport R n hn C')
      ≤ euclideanSetDistance (chargeSupport (siteRestrict ϱ)) (rootedMarkedSupport R n hn C) :=
        euclideanSetDistance_anti_right _ (rootedMarkedSupport_nonempty hn C)
          (rootedMarkedSupport_mono hn h)
    _ < M * rootedMarkScale R n hn ϱ C ^ α := hadj
    _ ≤ M * rootedMarkScale R n hn ϱ C' ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (rootedMarkScale_nonneg hn ϱ C)
          (min_le_min le_rfl (rootedClusterSize_mono hn h)) hα) hM

/-- The face charge of the proxy: twice the satellite's. -/
theorem totalCharge_siteRestrict_rootedMarkedProxy (hn : n ≤ R) (hn0 : 0 < n)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    totalCharge (siteRestrict (rootedMarkedProxy R n hn C T)) =
      2 * (∑ m ∈ T, totalCharge (siteRestrict m) - ∑ m ∈ C \ T, totalCharge (siteRestrict m)) := by
  have hmark := sum_rootedDipoleMark_some hn hn0 Finset.univ
  simp only [Finset.mem_univ, ite_true, sub_self] at hmark
  unfold totalCharge
  simp only [siteRestrict_rootedMarkedProxy, Finset.sum_add_distrib, hmark, zero_add,
    ← Finset.mul_sum]
  congr 1
  unfold rootedMarkedSatellite siteRestrict
  rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := C \ T)]

/-- **`D(C)` dominates `d_Λ` of the proxy's face part**, for every orientation. -/
theorem boundaryAdjustedSize_siteRestrict_proxy_le (hn : n ≤ R) (hn0 : 0 < n)
    {C T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) :
    boundaryAdjustedSize (siteRestrict (rootedMarkedProxy R n hn C T)) ≤
      rootedClusterSize R n hn C := by
  set p := siteRestrict (rootedMarkedProxy R n hn C T)
  have hsub := chargeSupport_siteRestrict_rootedMarkedProxy_subset hn hT
  have hmarks := rootedMarkSites_subset_chargeSupport_proxy hn C T
  have hmne : (rootedMarkSites R n hn).Nonempty := ⟨center R, by simp [rootedMarkSites]⟩
  have hpne : (chargeSupport p).Nonempty := hmne.mono hmarks
  have hdiam : chargeEuclideanDiameter p ≤ euclideanSetDiameter (rootedMarkedSupport R n hn C) :=
    Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _ hpne
      (rootedMarkedSupport_nonempty hn C) hsub
  unfold rootedClusterSize
  split_ifs with hC
  · have hq : totalCharge p = 0 := by
      rw [totalCharge_siteRestrict_rootedMarkedProxy hn hn0,
        Finset.sum_eq_zero fun m hm => hC m (hT hm),
        Finset.sum_eq_zero fun m hm => hC m (Finset.mem_sdiff.1 hm).1]
      simp
    rw [Generic.PinnedCharges.boundaryAdjustedSize_of_neutral p hq]
    exact hdiam
  · exact (boundaryAdjustedSize_le_max p).trans
      (max_le_max (euclideanBoundaryDistance_anti hmne hmarks) hdiam)

end Scale

/-! ### The extended ensemble -/

section Extension

variable {R n : ℕ}

theorem siteRestrict_mem_of_mem_image {L : ℕ} {F : Finset (ChargeDensity L)}
    {ϱ : RotatorDualFace L → ℤ} (h : ϱ ∈ F.image neutralizeAtWiredRoot) :
    siteRestrict ϱ ∈ F ∧ neutralizeAtWiredRoot (siteRestrict ϱ) = ϱ := by
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 h
  simp [hρ]

theorem sum_eq_zero_of_mem_image {L : ℕ} {F : Finset (ChargeDensity L)}
    {ϱ : RotatorDualFace L → ℤ} (h : ϱ ∈ F.image neutralizeAtWiredRoot) : ∑ j, ϱ j = 0 := by
  obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.1 h
  exact Generic.PinnedCharges.sum_neutralizeAtWiredRoot ρ

/-- **The remainder is separated from the composite** at the adjacency scale. -/
theorem le_euclideanSetDistance_of_mem_remainder {M α : ℝ} (hn : n ≤ R)
    {N C : Finset (RotatorDualFace (sideLength R) → ℤ)} {ϱ : RotatorDualFace (sideLength R) → ℤ}
    (hϱ : ϱ ∈ remainder (RootedMarkAdjacent M α R n hn) N C) :
    M * rootedMarkScale R n hn ϱ C ^ α ≤
      euclideanSetDistance (chargeSupport (siteRestrict ϱ)) (rootedMarkedSupport R n hn C) :=
  not_lt.1 (not_adj_of_mem_remainder hϱ)

/-- **The extension geometry** (`RootedMarkedExtensionGeometry`). -/
theorem rootedMarkedExtensionGeometry_holds {M α : ℝ} (hM : 0 < M) (hα : 0 ≤ α) (hn : n ≤ R)
    (hn0 : 0 < n) : RootedMarkedExtensionGeometry M α R n hn := by
  classical
  intro F hF hFs C T hCN hT
  set N := F.image neutralizeAtWiredRoot with hN
  set Rm := remainder (RootedMarkAdjacent M α R n hn) N C with hRm
  set p := rootedMarkedProxy R n hn C T with hp
  set X := rootedMarkedSupport R n hn C with hX
  have hRN : Rm ⊆ N := remainder_subset _ _
  have hCn : ∀ m ∈ C, ∑ j, m j = 0 := fun m hm => sum_eq_zero_of_mem_image (hCN hm)
  have hsepX : ∀ ϱ ∈ Rm, M * rootedMarkScale R n hn ϱ C ^ α ≤
      euclideanSetDistance (chargeSupport (siteRestrict ϱ)) X :=
    fun ϱ hϱ => le_euclideanSetDistance_of_mem_remainder hn hϱ
  have hne : ∀ ϱ ∈ Rm, siteRestrict ϱ ≠ 0 := fun ϱ hϱ =>
    hF.1 _ (siteRestrict_mem_of_mem_image (hRN hϱ)).1
  have hMle : ∀ ϱ ∈ Rm, M ≤ euclideanSetDistance (chargeSupport (siteRestrict ϱ)) X := by
    intro ϱ hϱ
    have h1 : 1 ≤ rootedMarkScale R n hn ϱ C :=
      le_min (Generic.PinnedCharges.Layer.one_le_boundaryAdjustedSize (hne ϱ hϱ))
        ((one_le_diam_rootedMarkedSupport hn hn0 C).trans
          (diam_rootedMarkedSupport_le_rootedClusterSize hn C))
    have h2 : 1 ≤ rootedMarkScale R n hn ϱ C ^ α := Real.one_le_rpow h1 hα
    nlinarith [hsepX ϱ hϱ]
  have hdisjX : ∀ ϱ ∈ Rm, Disjoint (chargeSupport (siteRestrict ϱ)) X := by
    intro ϱ hϱ
    rw [Finset.disjoint_left]
    intro x hx hxX
    have h0 := Generic.PinnedCharges.SelectionG.setDist_le_siteDist hx hxX
    rw [Generic.PinnedCharges.SelectionG.siteDist_self] at h0
    linarith [hMle ϱ hϱ]
  have hsuppP : chargeSupport (siteRestrict p) ⊆ X :=
    chargeSupport_siteRestrict_rootedMarkedProxy_subset hn hT
  have hcP : center R ∈ chargeSupport (siteRestrict p) :=
    rootedMarkSites_subset_chargeSupport_proxy hn C T (by simp [rootedMarkSites])
  have hpne : (chargeSupport (siteRestrict p)).Nonempty := ⟨_, hcP⟩
  have hp0 : siteRestrict p ≠ 0 := by
    intro h
    rw [h] at hcP
    exact (mem_chargeSupport'.1 hcP) rfl
  have hpR : p ∉ Rm := by
    intro h
    exact Finset.disjoint_left.1 (hdisjX p h) hcP (hsuppP hcP)
  -- the proxy against a remainder member
  have hpair : ∀ ϱ ∈ Rm, M * min (boundaryAdjustedSize (siteRestrict ϱ))
      (boundaryAdjustedSize (siteRestrict p)) ^ α ≤
        euclideanSetDistance (chargeSupport (siteRestrict ϱ)) (chargeSupport (siteRestrict p)) := by
    intro ϱ hϱ
    have hϱne := Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero _ (hne ϱ hϱ)
    calc M * min (boundaryAdjustedSize (siteRestrict ϱ))
          (boundaryAdjustedSize (siteRestrict p)) ^ α
        ≤ M * rootedMarkScale R n hn ϱ C ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
            (le_min (Generic.PinnedCharges.SelectionG.boundaryAdjustedSize_nonneg _)
              (Generic.PinnedCharges.SelectionG.boundaryAdjustedSize_nonneg _))
            (min_le_min le_rfl (boundaryAdjustedSize_siteRestrict_proxy_le hn hn0 hT)) hα)
            hM.le
      _ ≤ euclideanSetDistance (chargeSupport (siteRestrict ϱ)) X := hsepX ϱ hϱ
      _ ≤ euclideanSetDistance (chargeSupport (siteRestrict ϱ))
            (chargeSupport (siteRestrict p)) :=
          Generic.PinnedCharges.SelectionG.setDist_le_of_subset (Finset.Subset.refl _) hsuppP
            hϱne hpne
  have himage : (rootedMarkedExtension M α R n hn N C T).image siteRestrict =
      insert (siteRestrict p) (Rm.image siteRestrict) := by
    unfold rootedMarkedExtension
    rw [Finset.image_insert]
  have hmemE : ∀ ρ, ρ ∈ (rootedMarkedExtension M α R n hn N C T).image siteRestrict ↔
      ρ = siteRestrict p ∨ ∃ ϱ ∈ Rm, siteRestrict ϱ = ρ := by
    intro ρ
    rw [himage, Finset.mem_insert, Finset.mem_image]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, hpR, hdisjX⟩
  · -- nonzero members
    intro ρ hρ
    rcases (hmemE ρ).1 hρ with rfl | ⟨ϱ, hϱ, rfl⟩
    · exact hp0
    · exact hne ϱ hϱ
  · -- disjoint supports
    intro ρ hρ σ hσ hρσ
    rcases (hmemE ρ).1 hρ with rfl | ⟨ϱ, hϱ, rfl⟩ <;>
      rcases (hmemE σ).1 hσ with rfl | ⟨ϱ', hϱ', rfl⟩
    · exact absurd rfl hρσ
    · exact Finset.disjoint_of_subset_left hsuppP (hdisjX ϱ' hϱ').symm
    · exact Finset.disjoint_of_subset_right hsuppP (hdisjX ϱ hϱ)
    · exact hF.2 _ (siteRestrict_mem_of_mem_image (hRN hϱ)).1 _
        (siteRestrict_mem_of_mem_image (hRN hϱ')).1 hρσ
  · -- boundary separation
    intro ρ hρ σ hσ hρσ
    rcases (hmemE ρ).1 hρ with rfl | ⟨ϱ, hϱ, rfl⟩ <;>
      rcases (hmemE σ).1 hσ with rfl | ⟨ϱ', hϱ', rfl⟩
    · exact absurd rfl hρσ
    · rw [min_comm, Generic.PinnedCharges.SelectionG.setDist_comm]
      exact hpair ϱ' hϱ'
    · exact hpair ϱ hϱ
    · exact hFs _ (siteRestrict_mem_of_mem_image (hRN hϱ)).1 _
        (siteRestrict_mem_of_mem_image (hRN hϱ')).1 hρσ
  · -- the extension is the neutralization of its face parts
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := rootedMarkedExtension M α R n hn N C T)]
    refine Finset.image_congr fun ϱ hϱ => ?_
    simp only [Function.comp_apply, id]
    unfold rootedMarkedExtension at hϱ
    rcases Finset.mem_insert.1 hϱ with rfl | hϱ
    · exact neutralizeAtWiredRoot_siteRestrict_rootedMarkedProxy hn hn0 C T hCn hT
    · exact (siteRestrict_mem_of_mem_image (hRN hϱ)).2

end Extension

/-! ### The rooted charged split -/

section Split

variable {R n : ℕ}

theorem totalCharge_chargeRestriction {L : ℕ} (ρ : ChargeDensity L) (S : Finset (Fin L × Fin L)) :
    totalCharge (chargeRestriction ρ S) = ∑ x ∈ S, ρ x := by
  unfold totalCharge chargeRestriction
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The rooted charged split, integer form.** For a cluster `C` of the marked adjacency, an
orientation `T ⊆ C` and a split `A = X(C) ∩ S`, `B = X(C) ∖ S` that does not cut the mark,
with `A` isolated (`2M diam(A)^α ≤ dist(A, B)`) and boundary-far (`diam(A) < M d_bdry(A)^α`),
the satellite has nonzero charge on `A`. -/
theorem sum_rootedMarkedSatellite_ne_zero_of_split {M α : ℝ} (hM : 1 < M) (hα : 1 ≤ α)
    (hn : n ≤ R) {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry M α F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) (S : Finset (Site R))
    (hA : (rootedMarkedSupport R n hn C ∩ S).Nonempty)
    (hB : (rootedMarkedSupport R n hn C \ S).Nonempty)
    (hiso : 2 * M * euclideanSetDiameter (rootedMarkedSupport R n hn C ∩ S) ^ α ≤
      euclideanSetDistance (rootedMarkedSupport R n hn C ∩ S) (rootedMarkedSupport R n hn C \ S))
    (hfar : euclideanSetDiameter (rootedMarkedSupport R n hn C ∩ S) <
      M * euclideanBoundaryDistance (rootedMarkedSupport R n hn C ∩ S) ^ α)
    (hcut : center R ∈ S ↔ axialSite R n hn ∈ S) :
    ∑ x ∈ rootedMarkedSupport R n hn C ∩ S, rootedMarkedSatellite C T (some x) ≠ 0 := by
  classical
  set X := rootedMarkedSupport R n hn C with hX
  set A := X ∩ S with hAdef
  set B := X \ S with hBdef
  set d := euclideanSetDiameter A with hd
  set δ := euclideanSetDistance A B with hδ
  have hM0 : 0 < M := by linarith
  have hα0 : 0 ≤ α := by linarith
  have hCN : C ⊆ F.image neutralizeAtWiredRoot := (mem_clusters.1 hC).1
  have hmono := rootedMarkAdjacent_monotone hM0.le hα0 hn
  -- member data
  have hmF : ∀ m ∈ C, siteRestrict m ∈ F := fun m hm =>
    (siteRestrict_mem_of_mem_image (hCN hm)).1
  have hinj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → siteRestrict m ≠ siteRestrict m' := by
    intro m hm m' hm' hne h
    apply hne
    rw [← (siteRestrict_mem_of_mem_image (hCN hm)).2,
      ← (siteRestrict_mem_of_mem_image (hCN hm')).2, h]
  have hsubX : ∀ m ∈ C, chargeSupport (siteRestrict m) ⊆ X := fun m hm =>
    chargeSupport_subset_rootedMarkedSupport hn hm
  have hsuppne : ∀ m ∈ C, (chargeSupport (siteRestrict m)).Nonempty := fun m hm =>
    Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero _ (hgeo.ensemble.1 _ (hmF m hm))
  have hAorB : ∀ m ∈ C, ∀ y, m (some y) ≠ 0 → y ∈ A ∨ y ∈ B := by
    intro m hm y hy
    have hyX := hsubX m hm (mem_chargeSupport_siteRestrict.2 hy)
    by_cases hyS : y ∈ S
    · exact Or.inl (Finset.mem_inter.2 ⟨hyX, hyS⟩)
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hyX, hyS⟩)
  -- the elementary geometry of the split
  have hd0 : 0 ≤ d := Generic.PinnedCharges.SelectionG.diam_nonneg A
  have hdα0 : 0 ≤ d ^ α := Real.rpow_nonneg hd0 α
  have hδ1 : 1 ≤ δ := Generic.PinnedCharges.SelectionG.le_setDist hA hB fun x hx y hy =>
    Generic.PinnedCharges.SelectionG.one_le_siteDist fun hxy =>
      (Finset.mem_sdiff.1 hy).2 (hxy ▸ (Finset.mem_inter.1 hx).2)
  have hdδ : d ≤ δ := by
    rcases Generic.PinnedCharges.SelectionG.diam_eq_zero_or_one_le A with h0 | h1
    · rw [← hd] at h0
      linarith
    · have hpow : d ≤ d ^ α := by
        calc d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
          _ ≤ d ^ α := Real.rpow_le_rpow_of_exponent_le h1 hα
      nlinarith
  have hbigδ : d < M * δ ^ α := by
    have h1 : δ ≤ δ ^ α := by
      calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ α := Real.rpow_le_rpow_of_exponent_le hδ1 hα
    nlinarith
  -- two big members meeting `A` violate the Appendix D separation
  have hbig : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → (∃ x ∈ A, m (some x) ≠ 0) →
      (∃ x ∈ A, m' (some x) ≠ 0) →
      d < M * boundaryAdjustedSize (siteRestrict m) ^ α →
      d < M * boundaryAdjustedSize (siteRestrict m') ^ α → False := by
    intro m hm m' hm' hne ⟨x, hxA, hx⟩ ⟨x', hx'A, hx'⟩ h1 h2
    have hsep := hgeo.separated _ (hmF m hm) _ (hmF m' hm') (hinj m hm m' hm' hne)
    have hdist : euclideanSetDistance (chargeSupport (siteRestrict m))
        (chargeSupport (siteRestrict m')) ≤ d :=
      (Generic.PinnedCharges.SelectionG.setDist_le_siteDist
        (mem_chargeSupport_siteRestrict.2 hx) (mem_chargeSupport_siteRestrict.2 hx')).trans
        (Generic.PinnedCharges.SelectionG.siteDist_le_diam hxA hx'A)
    rcases min_choice (boundaryAdjustedSize (siteRestrict m))
      (boundaryAdjustedSize (siteRestrict m')) with h | h <;> rw [h] at hsep <;> linarith
  -- a straddling member is big
  have hstrad_big : ∀ m ∈ C, ∀ p ∈ A, ∀ q ∈ B, m (some p) ≠ 0 → m (some q) ≠ 0 →
      d < M * boundaryAdjustedSize (siteRestrict m) ^ α := by
    intro m _ p hp q hq hmp hmq
    have h1 : δ ≤ boundaryAdjustedSize (siteRestrict m) :=
      ((Generic.PinnedCharges.SelectionG.setDist_le_siteDist hp hq).trans
        (Generic.PinnedCharges.SelectionG.siteDist_le_diam (mem_chargeSupport_siteRestrict.2 hmp)
          (mem_chargeSupport_siteRestrict.2 hmq))).trans
        (Generic.PinnedCharges.chargeEuclideanDiameter_le_boundaryAdjustedSize _)
    have h2 : δ ^ α ≤ boundaryAdjustedSize (siteRestrict m) ^ α :=
      Real.rpow_le_rpow (by linarith) h1 hα0
    nlinarith
  -- a face-charged member inside `A` is big
  have hcharged_big : ∀ m ∈ C, chargeSupport (siteRestrict m) ⊆ A →
      totalCharge (siteRestrict m) ≠ 0 → d < M * boundaryAdjustedSize (siteRestrict m) ^ α := by
    intro m hm hsub hq
    have h1 : euclideanBoundaryDistance A ≤ boundaryAdjustedSize (siteRestrict m) :=
      (euclideanBoundaryDistance_anti (hsuppne m hm) hsub).trans
        (Generic.PinnedCharges.chargeBoundaryDistance_le_boundaryAdjustedSize_of_charged _ hq)
    have h2 := Real.rpow_le_rpow (euclideanBoundaryDistance_nonneg A) h1 hα0
    nlinarith
  -- the charge of a member on `A`
  have hQS : ∀ m ∈ C, ∑ x ∈ A, m (some x) = ∑ x ∈ S, siteRestrict m x := by
    intro m hm
    refine Finset.sum_subset Finset.inter_subset_right fun x hxS hxA => ?_
    by_contra hx
    rcases hAorB m hm x hx with h | h
    · exact hxA h
    · exact (Finset.mem_sdiff.1 h).2 hxS
  have hQin : ∀ m ∈ C, chargeSupport (siteRestrict m) ⊆ A →
      ∑ x ∈ A, m (some x) = totalCharge (siteRestrict m) := by
    intro m _ hsub
    refine Finset.sum_subset (Finset.subset_univ A) fun x _ hxA => ?_
    by_contra hx
    exact hxA (hsub (mem_chargeSupport_siteRestrict.2 hx))
  have hsat : ∑ x ∈ A, rootedMarkedSatellite C T (some x) =
      ∑ m ∈ T, ∑ x ∈ A, m (some x) - ∑ m ∈ C \ T, ∑ x ∈ A, m (some x) := by
    unfold rootedMarkedSatellite
    rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (s := A)]
  -- a single member charged on `A` decides the satellite charge
  have hsingle : ∀ m₀ ∈ C, (∀ m ∈ C, m ≠ m₀ → ∑ x ∈ A, m (some x) = 0) →
      ∑ x ∈ A, m₀ (some x) ≠ 0 → ∑ x ∈ A, rootedMarkedSatellite C T (some x) ≠ 0 := by
    intro m₀ hm₀ hzero hQ
    have hsum : ∀ U ⊆ C, ∑ m ∈ U, ∑ x ∈ A, m (some x) =
        if m₀ ∈ U then ∑ x ∈ A, m₀ (some x) else 0 := by
      intro U hU
      rw [Finset.sum_congr rfl fun m hm => (show ∑ x ∈ A, m (some x) =
        if m = m₀ then ∑ x ∈ A, m₀ (some x) else 0 by
          split_ifs with h
          · rw [h]
          · exact hzero m (hU hm) h), Finset.sum_ite_eq']
    rw [hsat, hsum T hT, hsum (C \ T) Finset.sdiff_subset]
    by_cases hm₀T : m₀ ∈ T
    · have h' : m₀ ∉ C \ T := fun h => (Finset.mem_sdiff.1 h).2 hm₀T
      simpa [hm₀T, h'] using hQ
    · have h' : m₀ ∈ C \ T := Finset.mem_sdiff.2 ⟨hm₀, hm₀T⟩
      simpa [hm₀T, h'] using hQ
  by_cases hex : ∃ m₀ ∈ C, ((∃ x ∈ A, m₀ (some x) ≠ 0) ∧ (∃ y ∈ B, m₀ (some y) ≠ 0)) ∨
      (chargeSupport (siteRestrict m₀) ⊆ A ∧ totalCharge (siteRestrict m₀) ≠ 0)
  · -- a straddling or a face-charged inner member: it alone is charged on `A`
    obtain ⟨m₀, hm₀, hbig₀⟩ := hex
    have hmeet₀ : ∃ x ∈ A, m₀ (some x) ≠ 0 := by
      rcases hbig₀ with ⟨h, -⟩ | ⟨hsub, -⟩
      · exact h
      · obtain ⟨x, hx⟩ := hsuppne m₀ hm₀
        exact ⟨x, hsub hx, mem_chargeSupport_siteRestrict.1 hx⟩
    have hlarge₀ : d < M * boundaryAdjustedSize (siteRestrict m₀) ^ α := by
      rcases hbig₀ with ⟨⟨x, hxA, hx⟩, ⟨y, hyB, hy⟩⟩ | ⟨hsub, hq⟩
      · exact hstrad_big m₀ hm₀ x hxA y hyB hx hy
      · exact hcharged_big m₀ hm₀ hsub hq
    have hzero : ∀ m ∈ C, m ≠ m₀ → ∑ x ∈ A, m (some x) = 0 := by
      intro m hm hne
      by_cases hmeet : ∃ x ∈ A, m (some x) ≠ 0
      · have hsmall : ¬ d < M * boundaryAdjustedSize (siteRestrict m) ^ α := fun h =>
          hbig m hm m₀ hm₀ hne hmeet hmeet₀ h hlarge₀
        have hin : chargeSupport (siteRestrict m) ⊆ A := by
          intro y hy
          rcases hAorB m hm y (mem_chargeSupport_siteRestrict.1 hy) with h | h
          · exact h
          · obtain ⟨x, hxA, hx⟩ := hmeet
            exact absurd (hstrad_big m hm x hxA y h hx (mem_chargeSupport_siteRestrict.1 hy))
              hsmall
        rw [hQin m hm hin]
        by_contra hq
        exact hsmall (hcharged_big m hm hin hq)
      · push Not at hmeet
        exact Finset.sum_eq_zero hmeet
    refine hsingle m₀ hm₀ hzero ?_
    by_cases hstr : ∃ y ∈ B, m₀ (some y) ≠ 0
    · -- the straddling member is charged on `A` (Appendix D isolation)
      obtain ⟨x, hxA, hx⟩ := hmeet₀
      obtain ⟨y, hyB, hy⟩ := hstr
      set ρ := siteRestrict m₀ with hρ
      set ρ₁ := chargeRestriction ρ S with hρ₁
      have hconst : IsConstituent ρ ρ₁ :=
        Generic.PinnedCharges.chargeRestriction_constituent ρ S
          ⟨x, mem_chargeSupport_siteRestrict.2 hx, (Finset.mem_inter.1 hxA).2⟩
      have hsub₁ : chargeSupport ρ₁ ⊆ A := by
        intro z hz
        obtain ⟨hzS, hzρ⟩ := (Generic.PinnedCharges.mem_chargeSupport_restriction_iff ρ S z).1 hz
        exact Finset.mem_inter.2 ⟨hsubX m₀ hm₀ hzρ, hzS⟩
      have hsub₂ : chargeSupport (fun z => ρ z - ρ₁ z) ⊆ B := by
        rw [Generic.PinnedCharges.SelectionG.chargeSupport_sub_constituent hconst]
        intro z hz
        obtain ⟨hzρ, hz₁⟩ := Finset.mem_sdiff.1 hz
        refine Finset.mem_sdiff.2 ⟨hsubX m₀ hm₀ hzρ, fun hzS => hz₁ ?_⟩
        exact (Generic.PinnedCharges.mem_chargeSupport_restriction_iff ρ S z).2 ⟨hzS, hzρ⟩
      have hne₁ : (chargeSupport ρ₁).Nonempty :=
        Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero _ hconst.1
      have hne₂ : (chargeSupport (fun z => ρ z - ρ₁ z)).Nonempty := by
        refine ⟨y, ?_⟩
        rw [Generic.PinnedCharges.SelectionG.chargeSupport_sub_constituent hconst]
        refine Finset.mem_sdiff.2 ⟨mem_chargeSupport_siteRestrict.2 hy, fun hy₁ => ?_⟩
        exact (Finset.mem_sdiff.1 hyB).2
          ((Generic.PinnedCharges.mem_chargeSupport_restriction_iff ρ S y).1 hy₁).1
      have hdiam₁ : chargeEuclideanDiameter ρ₁ ≤ d :=
        Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _ hne₁ hA hsub₁
      have htrig : 2 * M * chargeEuclideanDiameter ρ₁ ^ α ≤
          euclideanSetDistance (chargeSupport ρ₁) (chargeSupport (fun z => ρ z - ρ₁ z)) := by
        calc 2 * M * chargeEuclideanDiameter ρ₁ ^ α ≤ 2 * M * d ^ α :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
                (Generic.PinnedCharges.SelectionG.diam_nonneg _) hdiam₁ hα0) (by linarith)
          _ ≤ δ := hiso
          _ ≤ _ := Generic.PinnedCharges.SelectionG.setDist_le_of_subset hsub₁ hsub₂ hne₁ hne₂
      have hq := (hgeo.isolated ρ (hmF m₀ hm₀) ρ₁ hconst htrig).1
      rwa [hρ₁, totalCharge_chargeRestriction, ← hQS m₀ hm₀] at hq
    · -- the member lies in `A` and is face-charged
      push Not at hstr
      rcases hbig₀ with ⟨-, ⟨y, hyB, hy⟩⟩ | ⟨hsub, hq⟩
      · exact absurd (hstr y hyB) hy
      · rw [hQin m₀ hm₀ hsub]
        exact hq
  · -- whole face-neutral members on both sides: the cluster is not connected
    exfalso
    push Not at hex
    have hclass : ∀ m ∈ C, (chargeSupport (siteRestrict m) ⊆ A ∧
        totalCharge (siteRestrict m) = 0) ∨ chargeSupport (siteRestrict m) ⊆ B := by
      intro m hm
      by_cases hmeet : ∃ x ∈ A, m (some x) ≠ 0
      · have hnoB := (hex m hm).1 hmeet
        have hsub : chargeSupport (siteRestrict m) ⊆ A := by
          intro y hy
          rcases hAorB m hm y (mem_chargeSupport_siteRestrict.1 hy) with h | h
          · exact h
          · exact absurd (hnoB y h) (mem_chargeSupport_siteRestrict.1 hy)
        exact Or.inl ⟨hsub, (hex m hm).2 hsub⟩
      · push Not at hmeet
        refine Or.inr fun y hy => ?_
        rcases hAorB m hm y (mem_chargeSupport_siteRestrict.1 hy) with h | h
        · exact absurd (hmeet y h) (mem_chargeSupport_siteRestrict.1 hy)
        · exact h
    have hAB : ∀ m ∈ C, ¬ (chargeSupport (siteRestrict m) ⊆ A ∧
        chargeSupport (siteRestrict m) ⊆ B) := by
      rintro m hm ⟨hA', hB'⟩
      obtain ⟨y, hy⟩ := hsuppne m hm
      exact (Finset.mem_sdiff.1 (hB' hy)).2 (Finset.mem_inter.1 (hA' hy)).2
    have hcX : center R ∈ X :=
      rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])
    have haX : axialSite R n hn ∈ X :=
      rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])
    -- the contradiction from a member adjacent across the split
    have hcross : ∀ m ∈ C, ∀ Y : Finset (Site R), Y.Nonempty →
        ((chargeSupport (siteRestrict m) ⊆ B ∧ Y ⊆ A) ∨
          (chargeSupport (siteRestrict m) ⊆ A ∧ Y ⊆ B)) →
        M * d ^ α < euclideanSetDistance (chargeSupport (siteRestrict m)) Y := by
      intro m hm Y hY hcase
      have hge : δ ≤ euclideanSetDistance (chargeSupport (siteRestrict m)) Y := by
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hδ, Generic.PinnedCharges.SelectionG.setDist_comm]
          exact Generic.PinnedCharges.SelectionG.setDist_le_of_subset h1 h2 (hsuppne m hm) hY
        · exact Generic.PinnedCharges.SelectionG.setDist_le_of_subset h1 h2 (hsuppne m hm) hY
      have hpos : 0 < M * d ^ α ∨ d ^ α = 0 := by
        rcases hdα0.lt_or_eq with h | h
        · exact Or.inl (mul_pos hM0 h)
        · exact Or.inr h.symm
      rcases hpos with h | h
      · nlinarith
      · rw [h, mul_zero]
        linarith
    by_cases hcS : center R ∈ S
    · -- the mark lies in `A`; the members on `B` form `CQ`
      have haS : axialSite R n hn ∈ S := hcut.1 hcS
      set CQ := C.filter fun m => chargeSupport (siteRestrict m) ⊆ B with hCQ
      have hCQne : CQ.Nonempty := by
        obtain ⟨y, hyB⟩ := hB
        obtain ⟨hyX, hyS⟩ := Finset.mem_sdiff.1 hyB
        rcases mem_rootedMarkedSupport.1 hyX with hmark | ⟨m, hm, hmy⟩
        · rcases hmark with rfl | rfl
          · exact absurd hcS hyS
          · exact absurd haS hyS
        · refine ⟨m, Finset.mem_filter.2 ⟨hm, ?_⟩⟩
          rcases hclass m hm with ⟨hsub, -⟩ | hsub
          · exact absurd (Finset.mem_inter.1 (hsub (mem_chargeSupport_siteRestrict.2 hmy))).2 hyS
          · exact hsub
      obtain ⟨m', hm'Q, hadj⟩ :=
        exists_adj_sdiff_of_mem_clusters hmono hC (Finset.filter_subset _ _) hCQne
      obtain ⟨hm'C, hm'B⟩ := Finset.mem_filter.1 hm'Q
      have hrest : ∀ m ∈ C \ CQ, chargeSupport (siteRestrict m) ⊆ A ∧
          totalCharge (siteRestrict m) = 0 := by
        intro m hm
        obtain ⟨hmC, hmQ⟩ := Finset.mem_sdiff.1 hm
        rcases hclass m hmC with h | h
        · exact h
        · exact absurd (Finset.mem_filter.2 ⟨hmC, h⟩) hmQ
      have hYA : rootedMarkedSupport R n hn (C \ CQ) ⊆ A := by
        intro x hx
        rcases mem_rootedMarkedSupport.1 hx with hmark | ⟨m, hm, hmx⟩
        · rcases hmark with rfl | rfl
          · exact Finset.mem_inter.2 ⟨hcX, hcS⟩
          · exact Finset.mem_inter.2 ⟨haX, haS⟩
        · exact (hrest m hm).1 (mem_chargeSupport_siteRestrict.2 hmx)
      have hscale : rootedMarkScale R n hn m' (C \ CQ) ≤ d := by
        refine (min_le_right _ _).trans ?_
        rw [rootedClusterSize_of_neutral hn fun m hm => (hrest m hm).2]
        exact Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _
          (rootedMarkedSupport_nonempty hn _) hA hYA
      have hlt := hcross m' hm'C _ (rootedMarkedSupport_nonempty hn _) (Or.inl ⟨hm'B, hYA⟩)
      have hpow := Real.rpow_le_rpow (rootedMarkScale_nonneg hn m' (C \ CQ)) hscale hα0
      unfold RootedMarkAdjacent at hadj
      nlinarith
    · -- the mark lies in `B`; the members on `A` form `CQ`
      have haS : axialSite R n hn ∉ S := fun h => hcS (hcut.2 h)
      set CQ := C.filter fun m => chargeSupport (siteRestrict m) ⊆ A with hCQ
      have hCQne : CQ.Nonempty := by
        obtain ⟨x, hxA⟩ := hA
        obtain ⟨hxX, hxS⟩ := Finset.mem_inter.1 hxA
        rcases mem_rootedMarkedSupport.1 hxX with hmark | ⟨m, hm, hmx⟩
        · rcases hmark with rfl | rfl
          · exact absurd hxS hcS
          · exact absurd hxS haS
        · refine ⟨m, Finset.mem_filter.2 ⟨hm, ?_⟩⟩
          rcases hclass m hm with ⟨hsub, -⟩ | hsub
          · exact hsub
          · exact absurd hxS (Finset.mem_sdiff.1 (hsub (mem_chargeSupport_siteRestrict.2 hmx))).2
      obtain ⟨m', hm'Q, hadj⟩ :=
        exists_adj_sdiff_of_mem_clusters hmono hC (Finset.filter_subset _ _) hCQne
      obtain ⟨hm'C, hm'A⟩ := Finset.mem_filter.1 hm'Q
      have hm'n : totalCharge (siteRestrict m') = 0 := by
        rcases hclass m' hm'C with h | h
        · exact h.2
        · exact absurd ⟨hm'A, h⟩ (hAB m' hm'C)
      have hYB : rootedMarkedSupport R n hn (C \ CQ) ⊆ B := by
        intro x hx
        rcases mem_rootedMarkedSupport.1 hx with hmark | ⟨m, hm, hmx⟩
        · rcases hmark with rfl | rfl
          · exact Finset.mem_sdiff.2 ⟨hcX, hcS⟩
          · exact Finset.mem_sdiff.2 ⟨haX, haS⟩
        · obtain ⟨hmC, hmQ⟩ := Finset.mem_sdiff.1 hm
          rcases hclass m hmC with h | h
          · exact absurd (Finset.mem_filter.2 ⟨hmC, h.1⟩) hmQ
          · exact h (mem_chargeSupport_siteRestrict.2 hmx)
      have hscale : rootedMarkScale R n hn m' (C \ CQ) ≤ d := by
        refine (min_le_left _ _).trans ?_
        rw [Generic.PinnedCharges.boundaryAdjustedSize_of_neutral _ hm'n]
        exact Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _ (hsuppne m' hm'C) hA hm'A
      have hlt := hcross m' hm'C _ (rootedMarkedSupport_nonempty hn _) (Or.inr ⟨hm'A, hYB⟩)
      have hpow := Real.rpow_le_rpow (rootedMarkScale_nonneg hn m' (C \ CQ)) hscale hα0
      unfold RootedMarkAdjacent at hadj
      nlinarith

/-- **The rooted charged split, proxy form**: on an isolated boundary-far part `A` of `X(C)`, the
proxy's face charge is nonzero. A cut of the mark carries an odd charge; any other part carries
twice the nonzero satellite charge. -/
theorem sum_siteRestrict_rootedMarkedProxy_ne_zero_of_split {M α : ℝ} (hM : 1 < M) (hα : 1 ≤ α)
    (hn : n ≤ R) (hn0 : 0 < n) {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry M α F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) (S : Finset (Site R))
    (hA : (rootedMarkedSupport R n hn C ∩ S).Nonempty)
    (hB : (rootedMarkedSupport R n hn C \ S).Nonempty)
    (hiso : 2 * M * euclideanSetDiameter (rootedMarkedSupport R n hn C ∩ S) ^ α ≤
      euclideanSetDistance (rootedMarkedSupport R n hn C ∩ S) (rootedMarkedSupport R n hn C \ S))
    (hfar : euclideanSetDiameter (rootedMarkedSupport R n hn C ∩ S) <
      M * euclideanBoundaryDistance (rootedMarkedSupport R n hn C ∩ S) ^ α) :
    ∑ x ∈ rootedMarkedSupport R n hn C ∩ S, siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0 := by
  classical
  have hcX : center R ∈ rootedMarkedSupport R n hn C :=
    rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])
  have haX : axialSite R n hn ∈ rootedMarkedSupport R n hn C :=
    rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])
  have hval : ∑ x ∈ rootedMarkedSupport R n hn C ∩ S,
      siteRestrict (rootedMarkedProxy R n hn C T) x =
      ∑ x ∈ rootedMarkedSupport R n hn C ∩ S, rootedDipoleMark R n hn (some x) +
        2 * ∑ x ∈ rootedMarkedSupport R n hn C ∩ S, rootedMarkedSatellite C T (some x) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rfl
  have hc : center R ∈ rootedMarkedSupport R n hn C ∩ S ↔ center R ∈ S :=
    ⟨fun h => (Finset.mem_inter.1 h).2, fun h => Finset.mem_inter.2 ⟨hcX, h⟩⟩
  have ha : axialSite R n hn ∈ rootedMarkedSupport R n hn C ∩ S ↔ axialSite R n hn ∈ S :=
    ⟨fun h => (Finset.mem_inter.1 h).2, fun h => Finset.mem_inter.2 ⟨haX, h⟩⟩
  rw [hval, sum_rootedDipoleMark_some hn hn0]
  have hk := fun hcut : (center R ∈ S ↔ axialSite R n hn ∈ S) =>
    sum_rootedMarkedSatellite_ne_zero_of_split hM hα hn hgeo hC hT S hA hB hiso hfar hcut
  by_cases hcS : center R ∈ S <;> by_cases haS : axialSite R n hn ∈ S <;>
    simp only [hc, ha, hcS, haS, ↓reduceIte]
  · have := hk ⟨fun _ => haS, fun _ => hcS⟩
    omega
  · omega
  · omega
  · have := hk ⟨fun h => absurd h hcS, fun h => absurd h haS⟩
    omega

/-- **The rooted charged split** (`RootedMarkedChargedSplit`): an isolated boundary-far part of
the composite support carries composite charge at least `min(ξ, 1 − ξ)`. -/
theorem rootedMarkedChargedSplit_holds {M α : ℝ} (hM : 1 < M) (hα : 1 ≤ α) (hn : n ≤ R)
    (hn0 : 0 < n) : RootedMarkedChargedSplit M α R n hn := by
  intro F hgeo C hC T hT S hA hB hiso hfar ξ
  exact dipoleGap_le_abs_sum_rootedMarkedComposite hn hn0 ξ C T _
    (sum_siteRestrict_rootedMarkedProxy_ne_zero_of_split hM hα hn hn0 hgeo hC hT S hA hB hiso
      hfar)

/-- The members of a cluster of an Appendix D branch have pairwise disjoint face supports. -/
theorem disjoint_siteRestrict_of_subset_image {L : ℕ} {F : Finset (ChargeDensity L)}
    (hF : IsPinnedChargeEnsemble F) {C : Finset (RotatorDualFace L → ℤ)}
    (hCN : C ⊆ F.image neutralizeAtWiredRoot) :
    ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (chargeSupport (siteRestrict m)) (chargeSupport (siteRestrict m')) := by
  intro m hm m' hm' hne
  refine hF.2 _ (siteRestrict_mem_of_mem_image (hCN hm)).1 _
    (siteRestrict_mem_of_mem_image (hCN hm')).1 fun h => hne ?_
  rw [← (siteRestrict_mem_of_mem_image (hCN hm)).2, ← (siteRestrict_mem_of_mem_image (hCN hm')).2,
    h]

/-- **The proxy has the charged half of Appendix D isolation on boundary-far constituents.** -/
theorem hasFarConstituentCharge_rootedMarkedProxy {M α : ℝ} (hM : 1 < M) (hα : 1 ≤ α)
    (hn : n ≤ R) (hn0 : 0 < n) {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry M α F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) :
    HasFarConstituentCharge M α (siteRestrict (rootedMarkedProxy R n hn C T)) := by
  classical
  intro ρ₁ hconst htrig hfar
  set p := siteRestrict (rootedMarkedProxy R n hn C T) with hp
  set X := rootedMarkedSupport R n hn C with hX
  have hsuppP : chargeSupport p = X := chargeSupport_siteRestrict_rootedMarkedProxy hn hT
    (disjoint_siteRestrict_of_subset_image hgeo.ensemble (mem_clusters.1 hC).1)
  set S := chargeSupport ρ₁ with hS
  have hSX : S ⊆ X := hsuppP ▸ hconst.2.1
  have hAS : X ∩ S = S := Finset.inter_eq_right.2 hSX
  have hBS : X \ S = chargeSupport (fun x => p x - ρ₁ x) := by
    rw [Generic.PinnedCharges.SelectionG.chargeSupport_sub_constituent hconst, hsuppP]
  have hSne : S.Nonempty := Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero ρ₁ hconst.1
  have hBne : (X \ S).Nonempty := by
    by_contra hBe
    rw [Finset.not_nonempty_iff_eq_empty] at hBe
    have hSeq : S = X := Finset.Subset.antisymm hSX (Finset.sdiff_eq_empty_iff_subset.1 hBe)
    rw [← hBS, hBe, Generic.PinnedCharges.SelectionG.setDist_empty_right] at htrig
    have h1 : 1 ≤ chargeEuclideanDiameter ρ₁ := by
      change 1 ≤ euclideanSetDiameter S
      rw [hSeq]
      exact one_le_diam_rootedMarkedSupport hn hn0 C
    have h2 : 1 ≤ chargeEuclideanDiameter ρ₁ ^ α := Real.one_le_rpow h1 (by linarith)
    nlinarith
  have hsplit := sum_siteRestrict_rootedMarkedProxy_ne_zero_of_split hM hα hn hn0 hgeo hC hT S
    (by rw [hAS]; exact hSne) hBne (by rw [hAS, hBS]; exact htrig) (by rw [hAS]; exact hfar)
  rw [hAS] at hsplit
  have hq : totalCharge ρ₁ = ∑ x ∈ S, p x := by
    unfold totalCharge
    rw [← Finset.sum_subset (Finset.subset_univ S) fun x _ hx => by
      by_contra h
      exact hx (mem_chargeSupport'.2 h)]
    exact Finset.sum_congr rfl fun x hx => (hconst.2.2 x hx).symm
  rw [hq]
  exact hsplit

/-- Appendix D isolation gives the charged half on boundary-far constituents. -/
theorem hasFarConstituentCharge_of_hasBoundaryIsolation {L : ℕ} {M α : ℝ}
    {N : Finset (ChargeDensity L)} (hN : Generic.PinnedCharges.HasBoundaryIsolation M α N)
    {ρ : ChargeDensity L} (hρ : ρ ∈ N) : HasFarConstituentCharge M α ρ :=
  fun ρ₁ hconst htrig _ => (hN ρ hρ ρ₁ hconst htrig).1

/-- **Every member of the extended ensemble** has the charged half of Appendix D isolation on
boundary-far constituents. The remainder inherits the full clause from the branch; the proxy
satisfies `hasFarConstituentCharge_rootedMarkedProxy`. -/
theorem hasFarConstituentCharge_of_mem_rootedMarkedExtension {M α : ℝ} (hM : 1 < M)
    (hα : 1 ≤ α) (hn : n ≤ R) (hn0 : 0 < n) {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry M α F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C)
    {ρ : ChargeDensity (sideLength R)}
    (hρ : ρ ∈ (rootedMarkedExtension M α R n hn (F.image neutralizeAtWiredRoot) C T).image
      siteRestrict) : HasFarConstituentCharge M α ρ := by
  classical
  unfold rootedMarkedExtension at hρ
  rw [Finset.image_insert, Finset.mem_insert] at hρ
  rcases hρ with rfl | hρ
  · exact hasFarConstituentCharge_rootedMarkedProxy hM hα hn hn0 hgeo hC hT
  · obtain ⟨ϱ, hϱ, rfl⟩ := Finset.mem_image.1 hρ
    exact hasFarConstituentCharge_of_hasBoundaryIsolation hgeo.isolated
      (siteRestrict_mem_of_mem_image (remainder_subset _ _ hϱ)).1

end Split

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
