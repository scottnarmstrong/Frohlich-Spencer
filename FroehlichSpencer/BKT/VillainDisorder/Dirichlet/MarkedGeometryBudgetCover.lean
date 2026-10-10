/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryBudgetProxy
import Mathlib.Tactic

/-!
# Cover subadditivity of a marked cluster against its proxy (D2G3b)

The cluster members' cover costs are paid by the proxy's cover cost:
* `boundaryAdjustedSize_member_le`: every member has `d_Λ(m) ≤ 2 d_Λ(p)`. A face-charged member
  is within `diam X + d_bdry` of the boundary. When `p` is neutral, a second charged member exists,
  and Appendix D separation puts one of the two within `diam X` of the boundary;
* `layerCutoff_member_le`: hence `n_Λ(m) ≤ n_Λ(p) + 2`;
* `sum_layerCoverSum_members_le`: the members below their cutoff at scale `j` are
  `2^{j−1}`-separated, so a scale-`j` square meets at most 100 of them (`card_meet_le_100`).
  This gives `∑_C A_cover(m) ≤ 100 (A_cover(p) + 2 |X|)`;
* `logb_le_layerCoverSum_proxy`: `log₂(n + 1) ≤ A_cover(p)`, since `X` contains both dipole
  faces.
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
  chargeBoundaryDistance IsPinnedChargeEnsemble IsBoundarySeparated neutralizeAtWiredRoot
  siteBoundaryDepth euclideanSiteDistance boundaryChargeCutoff)

/-! ### Generic facts -/

section Generic

variable {L : ℕ}

/-- `sum_cover_le` with the parts' supports contained in (not equal to) the support of `a`. -/
theorem sum_cover_le_of_subset {P : Finset (ChargeDensity L)} {a : ChargeDensity L}
    (hsupp : P.biUnion chargeSupport ⊆ chargeSupport a) {i m : ℕ}
    (hm : ∀ Q ∈ kpSquares .free L i,
      (P.filter fun b => (Q ∩ chargeSupport b).Nonempty).card ≤ m) :
    ∑ b ∈ P, squareCoverNumber .free L i b ≤ m * squareCoverNumber .free L i a := by
  classical
  obtain ⟨C, hC, hCcard⟩ := exists_minCover i a
  have hcov : ∀ b ∈ P, squareCoverNumber .free L i b ≤
      (C.filter fun Q => (Q ∩ chargeSupport b).Nonempty).card := by
    intro b hb
    refine squareCoverNumber_le .free L i b _ ⟨fun Q hQ => hC.1 (Finset.mem_filter.mp hQ).1,
      fun x hx => ?_⟩
    have hxa : x ∈ chargeSupport a := hsupp (Finset.mem_biUnion.mpr ⟨b, hb, hx⟩)
    obtain ⟨Q, hQ, hxQ⟩ := hC.2 x hxa
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, x, Finset.mem_inter.mpr ⟨hxQ, hx⟩⟩, hxQ⟩
  calc ∑ b ∈ P, squareCoverNumber .free L i b
      ≤ ∑ b ∈ P, (C.filter fun Q => (Q ∩ chargeSupport b).Nonempty).card :=
        Finset.sum_le_sum hcov
    _ = ∑ Q ∈ C, (P.filter fun b => (Q ∩ chargeSupport b).Nonempty).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _Q ∈ C, m := Finset.sum_le_sum fun Q hQ => hm Q (hC.1 hQ)
    _ = m * squareCoverNumber .free L i a := by
        rw [Finset.sum_const, smul_eq_mul, hCcard, mul_comm]

/-- A density below its cutoff at scale `j` has `2^j < 2 M d_Λ^α`. -/
theorem two_pow_lt_of_le_layerCutoff {ϱ : RotatorDualFace L → ℤ} (hϱ : siteRestrict ϱ ≠ 0)
    {j : ℕ} (hj : j ≤ layerCutoff ϱ) :
    (2 : ℝ) ^ j < 2 * ((chargeCoverScale : ℝ) *
      boundaryAdjustedSize (siteRestrict ϱ) ^ chargeCoverExponent) := by
  set w := (chargeCoverScale : ℝ) * boundaryAdjustedSize (siteRestrict ϱ) ^ chargeCoverExponent
  have hd1 := one_le_boundaryAdjustedSize hϱ
  have hw1 : 1 ≤ w := by
    have h1 : 1 ≤ boundaryAdjustedSize (siteRestrict ϱ) ^ chargeCoverExponent :=
      Real.one_le_rpow hd1 (by norm_num [chargeCoverExponent])
    have h2 : (1 : ℝ) ≤ (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
    nlinarith
  have hy0 : 0 ≤ Real.logb 2 w := Real.logb_nonneg (by norm_num) hw1
  have hceil : (j : ℝ) < Real.logb 2 w + 1 := by
    have h1 : (j : ℝ) ≤ (layerCutoff ϱ : ℝ) := by exact_mod_cast hj
    have h2 : (layerCutoff ϱ : ℝ) < Real.logb 2 w + 1 := by
      unfold layerCutoff boundaryChargeCutoff
      exact Nat.ceil_lt_add_one hy0
    linarith
  have h3 : (2 : ℝ) ^ (j : ℝ) < (2 : ℝ) ^ (Real.logb 2 w + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hceil
  rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
    Real.rpow_one, Real.rpow_natCast] at h3
  linarith

end Generic

variable {R n : ℕ}

/-! ### The boundary-adjusted sizes of the members -/

/-- **Members are at most twice the proxy's size**: `d_Λ(m|faces) ≤ 2 d_Λ(p|faces)`. -/
theorem boundaryAdjustedSize_member_le (hn : n ≤ R) (hn0 : 0 < n)
    {F : Finset (ChargeDensity (sideLength R))} (hF : IsPinnedChargeEnsemble F)
    (hFs : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)} (hCN : C ⊆ F.image neutralizeAtWiredRoot)
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C)
    {m : RotatorDualFace (sideLength R) → ℤ} (hm : m ∈ C) :
    boundaryAdjustedSize (siteRestrict m) ≤
      2 * boundaryAdjustedSize (siteRestrict (rootedMarkedProxy R n hn C T)) := by
  classical
  set p := siteRestrict (rootedMarkedProxy R n hn C T) with hp
  set X := rootedMarkedSupport R n hn C with hX
  set M : ℝ := (chargeCoverScale : ℝ) with hMdef
  set α : ℝ := chargeCoverExponent with hαdef
  have hM1 : (1 : ℝ) < M := by norm_num [hMdef, chargeCoverScale]
  have hα1 : (1 : ℝ) ≤ α := by norm_num [hαdef, chargeCoverExponent]
  have hsuppP : chargeSupport p = X := chargeSupport_siteRestrict_rootedMarkedProxy hn hT
    (disjoint_siteRestrict_of_subset_image hF hCN)
  have hmF : siteRestrict m ∈ F := (siteRestrict_mem_of_mem_image (hCN hm)).1
  have hm0 : siteRestrict m ≠ 0 := hF.1 _ hmF
  have hmne := Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero _ hm0
  have hmX : chargeSupport (siteRestrict m) ⊆ X := chargeSupport_subset_rootedMarkedSupport hn hm
  have hXne := rootedMarkedSupport_nonempty hn C
  have hX1 : 1 ≤ euclideanSetDiameter X := one_le_diam_rootedMarkedSupport hn hn0 C
  have hdiamX : euclideanSetDiameter X ≤ boundaryAdjustedSize p := by
    have h := Generic.PinnedCharges.chargeEuclideanDiameter_le_boundaryAdjustedSize p
    unfold chargeEuclideanDiameter at h
    rwa [hsuppP] at h
  have hdm : chargeEuclideanDiameter (siteRestrict m) ≤ euclideanSetDiameter X :=
    Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _ hmne hXne hmX
  have hp0 : 0 ≤ boundaryAdjustedSize p :=
    Generic.PinnedCharges.SelectionG.boundaryAdjustedSize_nonneg p
  by_cases hq : totalCharge (siteRestrict m) = 0
  · rw [Generic.PinnedCharges.boundaryAdjustedSize_of_neutral _ hq]
    linarith
  rw [Generic.PinnedCharges.boundaryAdjustedSize_of_charged _ hq]
  refine max_le ?_ (by linarith)
  -- the boundary distance of a face-charged member
  have hbd_le : ∀ y ∈ X, chargeBoundaryDistance (siteRestrict m) ≤
      (siteBoundaryDepth y : ℝ) + euclideanSetDiameter X := by
    intro y hy
    obtain ⟨x, hx⟩ := hmne
    calc chargeBoundaryDistance (siteRestrict m) ≤ (siteBoundaryDepth x : ℝ) :=
          euclideanBoundaryDistance_le_depth hx
      _ ≤ siteBoundaryDepth y + euclideanSiteDistance x y := depth_le_add_siteDist x y
      _ ≤ siteBoundaryDepth y + euclideanSetDiameter X := by
          have := Generic.PinnedCharges.SelectionG.siteDist_le_diam (hmX hx) hy
          linarith
  by_cases hpq : totalCharge p = 0
  · -- a neutral proxy: a second face-charged member
    obtain ⟨m', hm'C, hm'm, hq'⟩ : ∃ m' ∈ C, m' ≠ m ∧ totalCharge (siteRestrict m') ≠ 0 := by
      by_contra hall
      push Not at hall
      have hsum : ∀ U ⊆ C, ∑ m'' ∈ U, totalCharge (siteRestrict m'') =
          if m ∈ U then totalCharge (siteRestrict m) else 0 := by
        intro U hU
        rw [Finset.sum_congr rfl fun m'' hm'' => (show totalCharge (siteRestrict m'') =
          if m'' = m then totalCharge (siteRestrict m) else 0 by
            split_ifs with h
            · rw [h]
            · exact hall m'' (hU hm'') h), Finset.sum_ite_eq']
      have htot := totalCharge_siteRestrict_rootedMarkedProxy hn hn0 C T
      rw [hsum T hT, hsum (C \ T) Finset.sdiff_subset] at htot
      rw [← hp, hpq] at htot
      by_cases hmT : m ∈ T
      · have h' : m ∉ C \ T := fun h => (Finset.mem_sdiff.1 h).2 hmT
        simp only [hmT, h', ↓reduceIte, sub_zero] at htot
        omega
      · have h' : m ∈ C \ T := Finset.mem_sdiff.2 ⟨hm, hmT⟩
        simp only [hmT, h', ↓reduceIte, zero_sub] at htot
        omega
    have hm'F : siteRestrict m' ∈ F := (siteRestrict_mem_of_mem_image (hCN hm'C)).1
    have hm'0 : siteRestrict m' ≠ 0 := hF.1 _ hm'F
    have hm'ne := Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero _ hm'0
    have hm'X : chargeSupport (siteRestrict m') ⊆ X :=
      chargeSupport_subset_rootedMarkedSupport hn hm'C
    have hne : siteRestrict m ≠ siteRestrict m' := fun h => hm'm (by
      rw [← (siteRestrict_mem_of_mem_image (hCN hm'C)).2, ← h,
        (siteRestrict_mem_of_mem_image (hCN hm)).2])
    have hsep := hFs _ hmF _ hm'F hne
    have hdist : euclideanSetDistance (chargeSupport (siteRestrict m))
        (chargeSupport (siteRestrict m')) ≤ euclideanSetDiameter X :=
      Generic.PinnedCharges.SelectionG.setDist_le_diam hmX hm'X hmne hm'ne
    have hb := Generic.PinnedCharges.chargeBoundaryDistance_le_boundaryAdjustedSize_of_charged
      _ hq
    have hb' := Generic.PinnedCharges.chargeBoundaryDistance_le_boundaryAdjustedSize_of_charged
      _ hq'
    -- one of the two charged members is within `diam X` of the boundary
    have hmin : min (chargeBoundaryDistance (siteRestrict m))
        (chargeBoundaryDistance (siteRestrict m')) ≤ euclideanSetDiameter X := by
      by_contra hlt
      push Not at hlt
      set μ := min (boundaryAdjustedSize (siteRestrict m)) (boundaryAdjustedSize (siteRestrict m'))
      have hμ : euclideanSetDiameter X < μ :=
        hlt.trans_le (min_le_min hb hb')
      have hμ1 : 1 ≤ μ := by linarith
      have hpow : μ ≤ μ ^ α := by
        calc μ = μ ^ (1 : ℝ) := (Real.rpow_one μ).symm
          _ ≤ μ ^ α := Real.rpow_le_rpow_of_exponent_le hμ1 hα1
      nlinarith
    -- the boundary distance of `m'` bounds that of `m`
    have hm'bd : chargeBoundaryDistance (siteRestrict m) ≤
        chargeBoundaryDistance (siteRestrict m') + euclideanSetDiameter X := by
      obtain ⟨y', hy', hdy'⟩ := exists_depth_eq_chargeBoundaryDistance hm'0
      have := hbd_le y' (hm'X hy')
      linarith
    have hdp : euclideanSetDiameter X ≤ boundaryAdjustedSize p := hdiamX
    rcases min_choice (chargeBoundaryDistance (siteRestrict m))
      (chargeBoundaryDistance (siteRestrict m')) with h | h <;> rw [h] at hmin <;> linarith
  · -- a charged proxy: its boundary distance and diameter bound the member's
    have hpne : siteRestrict (rootedMarkedProxy R n hn C T) ≠ 0 := by
      intro h0
      apply hpq
      rw [hp, h0]
      simp [totalCharge]
    obtain ⟨y, hy, hdy⟩ := exists_depth_eq_chargeBoundaryDistance hpne
    have hyX : y ∈ X := by rw [← hsuppP]; exact hy
    have h1 := hbd_le y hyX
    have h2 : chargeBoundaryDistance p ≤ boundaryAdjustedSize p :=
      Generic.PinnedCharges.chargeBoundaryDistance_le_boundaryAdjustedSize_of_charged _ hpq
    rw [hdy] at h1
    linarith

/-- **The member cutoffs**: `n_Λ(m) ≤ n_Λ(p) + 2`. -/
theorem layerCutoff_member_le (hn : n ≤ R) (hn0 : 0 < n)
    {F : Finset (ChargeDensity (sideLength R))} (hF : IsPinnedChargeEnsemble F)
    (hFs : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)} (hCN : C ⊆ F.image neutralizeAtWiredRoot)
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C)
    {m : RotatorDualFace (sideLength R) → ℤ} (hm : m ∈ C) :
    layerCutoff m ≤ layerCutoff (rootedMarkedProxy R n hn C T) + 2 := by
  set dm := boundaryAdjustedSize (siteRestrict m)
  set dp := boundaryAdjustedSize (siteRestrict (rootedMarkedProxy R n hn C T))
  set M : ℝ := (chargeCoverScale : ℝ) with hMdef
  set α : ℝ := chargeCoverExponent with hαdef
  have hM0 : (0 : ℝ) < M := by norm_num [hMdef, chargeCoverScale]
  have hle := boundaryAdjustedSize_member_le hn hn0 hF hFs hCN hT hm
  have hdm1 : 1 ≤ dm :=
    one_le_boundaryAdjustedSize (hF.1 _ (siteRestrict_mem_of_mem_image (hCN hm)).1)
  have hdp : (1 / 2 : ℝ) ≤ dp := by linarith
  have hdp0 : 0 < dp := by linarith
  have hlog : Real.logb 2 (M * dm ^ α) ≤ Real.logb 2 (M * dp ^ α) + 2 := by
    have h1 : M * dm ^ α ≤ M * (2 * dp) ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hle (by norm_num [hαdef,
        chargeCoverExponent])) hM0.le
    have h2 : M * (2 * dp) ^ α = (2 : ℝ) ^ α * (M * dp ^ α) := by
      rw [Real.mul_rpow (by norm_num) hdp0.le]
      ring
    have h3 : Real.logb 2 ((2 : ℝ) ^ α * (M * dp ^ α)) = α + Real.logb 2 (M * dp ^ α) := by
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num)
        (by norm_num)]
    have h4 : Real.logb 2 (M * dm ^ α) ≤ Real.logb 2 (M * (2 * dp) ^ α) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    rw [h2, h3] at h4
    have hα2 : α ≤ 2 := by norm_num [hαdef, chargeCoverExponent]
    linarith
  unfold layerCutoff boundaryChargeCutoff
  rw [Nat.ceil_le]
  have := Nat.le_ceil (Real.logb 2 (M * dp ^ α))
  push_cast
  linarith

/-! ### Cover subadditivity -/

/-- The members below their cutoff at scale `j` form a `2^{j−1}`-separated family. -/
theorem isSeparatedFamily_members_below_cutoff {F : Finset (ChargeDensity (sideLength R))}
    (hF : IsPinnedChargeEnsemble F)
    (hFs : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)} (hCN : C ⊆ F.image neutralizeAtWiredRoot)
    (j : ℕ) :
    IsSeparatedFamily ((2 : ℝ) ^ j / 2)
      ((C.filter fun m => j ≤ layerCutoff m).image siteRestrict) := by
  classical
  intro b hb b' hb' hne
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hb
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hb'
  obtain ⟨hmC, hmj⟩ := Finset.mem_filter.1 hm
  obtain ⟨hm'C, hm'j⟩ := Finset.mem_filter.1 hm'
  have hmF := (siteRestrict_mem_of_mem_image (hCN hmC)).1
  have hm'F := (siteRestrict_mem_of_mem_image (hCN hm'C)).1
  have h1 := two_pow_lt_of_le_layerCutoff (hF.1 _ hmF) hmj
  have h2 := two_pow_lt_of_le_layerCutoff (hF.1 _ hm'F) hm'j
  have hsep := hFs _ hmF _ hm'F hne
  rcases min_choice (boundaryAdjustedSize (siteRestrict m))
    (boundaryAdjustedSize (siteRestrict m')) with h | h <;> rw [h] at hsep <;> linarith

/-- **Per-scale subadditivity**: the members below their cutoff at scale `j` need at most `100`
times as many scale-`j` squares as the proxy. -/
theorem sum_squareCoverNumber_members_le (hn : n ≤ R)
    {F : Finset (ChargeDensity (sideLength R))} (hF : IsPinnedChargeEnsemble F)
    (hFs : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)} (hCN : C ⊆ F.image neutralizeAtWiredRoot)
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) (j : ℕ) :
    ∑ m ∈ C.filter (fun m => j ≤ layerCutoff m), squareCoverNumber .free (sideLength R) j
        (siteRestrict m) ≤
      100 * squareCoverNumber .free (sideLength R) j
        (siteRestrict (rootedMarkedProxy R n hn C T)) := by
  classical
  have hinj : Set.InjOn siteRestrict
      ((C.filter fun m => j ≤ layerCutoff m : Finset _) :
        Set (RotatorDualFace (sideLength R) → ℤ)) := by
    intro m hm m' hm' h
    have hmC := (Finset.mem_filter.1 hm).1
    have hm'C := (Finset.mem_filter.1 hm').1
    rw [← (siteRestrict_mem_of_mem_image (hCN hmC)).2, ← (siteRestrict_mem_of_mem_image
      (hCN hm'C)).2, h]
  rw [← Finset.sum_image (f := fun b => squareCoverNumber .free (sideLength R) j b) hinj]
  have hsuppP := chargeSupport_siteRestrict_rootedMarkedProxy hn hT
    (disjoint_siteRestrict_of_subset_image hF hCN)
  refine sum_cover_le_of_subset ?_ fun Q hQ => card_meet_le_100 (by positivity)
    (isSeparatedFamily_members_below_cutoff hF hFs hCN j) (by linarith) hQ
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hb
  rw [hsuppP]
  exact chargeSupport_subset_rootedMarkedSupport hn (Finset.mem_filter.1 hm).1 hxb

/-- **Cover subadditivity of the cluster**: `∑_C A_cover(m) ≤ 100 (A_cover(p) + 2 |X|)`. -/
theorem sum_layerCoverSum_members_le (hn : n ≤ R) (hn0 : 0 < n)
    {F : Finset (ChargeDensity (sideLength R))} (hF : IsPinnedChargeEnsemble F)
    (hFs : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)} (hCN : C ⊆ F.image neutralizeAtWiredRoot)
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) :
    ∑ m ∈ C, layerCoverSum m ≤
      100 * (layerCoverSum (rootedMarkedProxy R n hn C T) +
        2 * ((chargeSupport (siteRestrict (rootedMarkedProxy R n hn C T))).card : ℝ)) := by
  classical
  set p := rootedMarkedProxy R n hn C T with hp
  set np := layerCutoff p with hnp
  set N : ℕ → (RotatorDualFace (sideLength R) → ℤ) → ℝ :=
    fun j ϱ => (squareCoverNumber .free (sideLength R) j (siteRestrict ϱ) : ℝ) with hN
  have hmem : ∀ m ∈ C, layerCoverSum m =
      ∑ j ∈ Finset.range (np + 3), if j ≤ layerCutoff m then N j m else 0 := by
    intro m hm
    have hle : layerCutoff m ≤ np + 2 := layerCutoff_member_le hn hn0 hF hFs hCN hT hm
    unfold layerCoverSum
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  have hswap : ∑ m ∈ C, layerCoverSum m =
      ∑ j ∈ Finset.range (np + 3), ∑ m ∈ C.filter (fun m => j ≤ layerCutoff m), N j m := by
    rw [Finset.sum_congr rfl hmem, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_filter]
  have hscale : ∀ j, ∑ m ∈ C.filter (fun m => j ≤ layerCutoff m), N j m ≤ 100 * N j p := by
    intro j
    have h := sum_squareCoverNumber_members_le hn hF hFs hCN hT j
    simp only [hN]
    exact_mod_cast h
  have hcard : ∀ j, N j p ≤ ((chargeSupport (siteRestrict p)).card : ℝ) := fun j => by
    simp only [hN]
    exact_mod_cast squareCoverNumber_le_card j (siteRestrict p)
  have hsplit : ∑ j ∈ Finset.range (np + 3), N j p =
      layerCoverSum p + N (np + 1) p + N (np + 2) p := by
    unfold layerCoverSum
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [hswap]
  calc ∑ j ∈ Finset.range (np + 3), ∑ m ∈ C.filter (fun m => j ≤ layerCutoff m), N j m
      ≤ ∑ j ∈ Finset.range (np + 3), 100 * N j p := Finset.sum_le_sum fun j _ => hscale j
    _ = 100 * (layerCoverSum p + N (np + 1) p + N (np + 2) p) := by
        rw [← Finset.mul_sum, hsplit]
    _ ≤ _ := by
        have := hcard (np + 1)
        have := hcard (np + 2)
        nlinarith

/-! ### The dipole term -/

/-- **The dipole's logarithm is paid by the proxy's cover cost**: `log₂(n + 1) ≤ A_cover(p)`. -/
theorem logb_le_layerCoverSum_proxy (hn : n ≤ R) (hn0 : 0 < n)
    {C T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (chargeSupport (siteRestrict m)) (chargeSupport (siteRestrict m'))) :
    Real.logb 2 ((n : ℝ) + 1) ≤ layerCoverSum (rootedMarkedProxy R n hn C T) := by
  set p := rootedMarkedProxy R n hn C T with hp
  set d := boundaryAdjustedSize (siteRestrict p) with hd
  set M : ℝ := (chargeCoverScale : ℝ) with hMdef
  set α : ℝ := chargeCoverExponent with hαdef
  have hsuppP := chargeSupport_siteRestrict_rootedMarkedProxy hn hT hdisj (n := n)
  have hcX : center R ∈ rootedMarkedSupport R n hn C :=
    rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])
  have haX : axialSite R n hn ∈ rootedMarkedSupport R n hn C :=
    rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])
  have hp0 : siteRestrict p ≠ 0 := by
    intro h0
    have hc : center R ∈ chargeSupport (siteRestrict p) := by rw [hsuppP]; exact hcX
    rw [h0] at hc
    exact (mem_chargeSupport'.1 hc) rfl
  -- `d ≥ n`
  have hdn : (n : ℝ) ≤ d := by
    have h1 := abs_fst_le_siteDist (center R) (axialSite R n hn)
    have h2 := Generic.PinnedCharges.SelectionG.siteDist_le_diam hcX haX
    have h3 := Generic.PinnedCharges.chargeEuclideanDiameter_le_boundaryAdjustedSize
      (siteRestrict p)
    unfold chargeEuclideanDiameter at h3
    rw [hsuppP] at h3
    have h4 : |((center R).1.val : ℝ) - (axialSite R n hn).1.val| = n := by
      simp only [center, axialSite]
      push_cast
      rw [show (R : ℝ) - (R + n) = -n by ring, abs_neg, abs_of_nonneg (by positivity)]
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hd1 : 1 ≤ d := le_trans hn1 hdn
  have hw : (n : ℝ) + 1 ≤ M * d ^ α := by
    have hpow : d ≤ d ^ α := by
      calc d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
        _ ≤ d ^ α := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num [hαdef,
          chargeCoverExponent])
    have hM : (2 : ℝ) ≤ M := by norm_num [hMdef, chargeCoverScale]
    nlinarith
  have hlog : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 (M * d ^ α) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hw
  have hceil : Real.logb 2 (M * d ^ α) ≤ (layerCutoff p : ℝ) := by
    unfold layerCutoff boundaryChargeCutoff
    exact Nat.le_ceil _
  have hsum : ((layerCutoff p : ℕ) : ℝ) + 1 ≤ layerCoverSum p := by
    unfold layerCoverSum
    have h1 : ∀ j ∈ Finset.range (layerCutoff p + 1),
        (1 : ℝ) ≤ (squareCoverNumber .free (sideLength R) j (siteRestrict p) : ℝ) :=
      fun j _ => by exact_mod_cast one_le_squareCoverNumber j hp0
    have h2 := Finset.sum_le_sum h1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h2
    push_cast at h2
    exact h2
  linarith

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
