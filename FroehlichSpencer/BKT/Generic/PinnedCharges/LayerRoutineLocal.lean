/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineGraph

/-!
For a density `ρ` of the box (neutralized `ϱ` on `squareZero`):

* `routineCenter`: a support face of minimal boundary depth;
* `routineS ϱ`: the `squareZero` edges with a bounded endpoint within Euclidean distance
  `64 d_Λ(ρ)` of `supp ρ`; `routineDsc ϱ = ⌈d_Λ(ρ)⌉`;
* `card_routineS_le`: `|S| ≤ routineKv (dsc + 1)²`;
* `routineS_overlap`: in a boundary-separated family, densities with `dsc` in one dyadic band have
  disjoint `S` (overlap `≤ 1`);
* `exists_routineRoute`: the neutralized density is an integer combination of edge gradients on
  `S`, with coefficients bounded by `‖ϱ‖₁` (charges routed to the center along geodesics; path
  locality keeps every geodesic within `2 d_Λ` of the support).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The routing center: a support face of minimal boundary depth (`none` for the zero density). -/
def routineCenter (ϱ : RotatorDualFace L → ℤ) : RotatorDualFace L :=
  if h : (chargeSupport (siteRestrict ϱ)).Nonempty then
    some (Classical.choose ((chargeSupport (siteRestrict ϱ)).exists_min_image siteBoundaryDepth h))
  else none

/-- The support set: edges with a bounded endpoint within `64 d_Λ` of the support. -/
def routineS (ϱ : RotatorDualFace L → ℤ) : Finset (SquareZeroBond L) := by
  classical
  exact Finset.univ.filter fun e => ∃ y : Site L,
    ((squareZero L).src e = some y ∨ (squareZero L).tgt e = some y) ∧
      ∃ x ∈ chargeSupport (siteRestrict ϱ),
        euclideanSiteDistance y x ≤ 64 * boundaryAdjustedSize (siteRestrict ϱ)

/-- The size `⌈d_Λ⌉`. -/
def routineDsc (ϱ : RotatorDualFace L → ℤ) : ℕ := ⌈boundaryAdjustedSize (siteRestrict ϱ)⌉₊

/-- The constant of `|S| ≤ Kv (dsc + 1)²`. -/
def routineKv : ℝ := 4 * 522 ^ 2

theorem routineCenter_spec' (ϱ : RotatorDualFace L → ℤ)
    (h : (chargeSupport (siteRestrict ϱ)).Nonempty) :
    ∃ j ∈ chargeSupport (siteRestrict ϱ), routineCenter ϱ = some j ∧
      ∀ x ∈ chargeSupport (siteRestrict ϱ), siteBoundaryDepth j ≤ siteBoundaryDepth x := by
  have hspec := Classical.choose_spec
    ((chargeSupport (siteRestrict ϱ)).exists_min_image siteBoundaryDepth h)
  refine ⟨_, hspec.1, ?_, hspec.2⟩
  unfold routineCenter
  rw [dite_eq_left h]

theorem routineCenter_spec {ρ : ChargeDensity L} (hρ : ρ ≠ 0) :
    ∃ j ∈ chargeSupport ρ, routineCenter (neutralizeAtWiredRoot ρ) = some j ∧
      ∀ x ∈ chargeSupport ρ, siteBoundaryDepth j ≤ siteBoundaryDepth x := by
  have h := routineCenter_spec' (neutralizeAtWiredRoot ρ)
    (by rw [siteRestrict_neutralize]; exact chargeSupport_nonempty_of_ne_zero ρ hρ)
  rwa [siteRestrict_neutralize] at h

theorem one_le_boundaryAdjustedSize {ρ : ChargeDensity L} (hρ : ρ ≠ 0) :
    1 ≤ boundaryAdjustedSize ρ := by
  by_cases hq : totalCharge ρ = 0
  · exact boundaryAdjustedSize_ge_one_of_neutral_ne_zero ρ hq hρ
  · rw [boundaryAdjustedSize_of_charged ρ hq]
    exact (chargeBoundaryDistance_ge_one_of_ne_zero ρ hρ).trans (le_max_left _ _)

theorem routineDsc_spec {ρ : ChargeDensity L} (hρ : ρ ≠ 0) :
    1 ≤ routineDsc (neutralizeAtWiredRoot ρ) ∧
      (routineDsc (neutralizeAtWiredRoot ρ) : ℝ) + 1 ≤ 2 ^ 16 * boundaryAdjustedSize ρ := by
  have hd := one_le_boundaryAdjustedSize hρ
  unfold routineDsc
  rw [siteRestrict_neutralize]
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne', ?_⟩
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ boundaryAdjustedSize ρ)
  linarith

theorem siteDist_le_l1 (x y : Site L) : euclideanSiteDistance x y ≤ l1 x y := by
  unfold euclideanSiteDistance l1
  push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs]
  push_cast
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg ((x.1.val : ℝ) - y.1.val), abs_nonneg ((x.2.val : ℝ) - y.2.val),
    sq_abs ((x.1.val : ℝ) - y.1.val), sq_abs ((x.2.val : ℝ) - y.2.val)]

theorem l1_le_two_siteDist (x y : Site L) : (l1 x y : ℝ) ≤ 2 * euclideanSiteDistance x y := by
  have h1 := abs_fst_le_siteDist x y
  have h2 := abs_snd_le_siteDist x y
  unfold l1
  push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs]
  push_cast
  linarith

theorem coord_le_of_near {x x₀ y : Site L} {r : ℝ} (hy : euclideanSiteDistance y x ≤ r)
    {d : ℝ} (hx : euclideanSiteDistance x x₀ ≤ d) :
    |(y.1.val : ℝ) - x₀.1.val| ≤ r + d ∧ |(y.2.val : ℝ) - x₀.2.val| ≤ r + d := by
  have a1 := abs_fst_le_siteDist y x
  have a2 := abs_snd_le_siteDist y x
  have b1 := abs_fst_le_siteDist x x₀
  have b2 := abs_snd_le_siteDist x x₀
  have t1 := abs_sub_le ((y.1.val : ℝ)) (x.1.val : ℝ) (x₀.1.val : ℝ)
  have t2 := abs_sub_le ((y.2.val : ℝ)) (x.2.val : ℝ) (x₀.2.val : ℝ)
  constructor <;> linarith

/-- **`|S| ≲ d_Λ²`.** -/
theorem card_routineS_le {ρ : ChargeDensity L} (hρ : ρ ≠ 0) :
    ((routineS (neutralizeAtWiredRoot ρ)).card : ℝ) ≤
      routineKv * ((routineDsc (neutralizeAtWiredRoot ρ) : ℝ) + 1) ^ 2 := by
  classical
  set d := boundaryAdjustedSize ρ with hd
  have hd1 : 1 ≤ d := one_le_boundaryAdjustedSize hρ
  obtain ⟨x₀, hx₀⟩ := chargeSupport_nonempty_of_ne_zero ρ hρ
  let Y : Finset (Site L) := Finset.univ.filter fun y =>
    ∃ x ∈ chargeSupport ρ, euclideanSiteDistance y x ≤ 64 * d
  have hY : (Y.card : ℝ) ≤ (4 * (65 * d) / (1 / 2) + 2) ^ 2 := by
    refine card_le_of_separated (fun y => y) (by norm_num) ((x₀.1.val : ℝ), (x₀.2.val : ℝ))
      (fun y hy => ?_) (fun y _ y' _ hne => ?_)
    · obtain ⟨x, hx, hyx⟩ := (Finset.mem_filter.mp hy).2
      have hxx₀ : euclideanSiteDistance x x₀ ≤ d :=
        (siteDist_le_diam hx hx₀).trans (chargeEuclideanDiameter_le_boundaryAdjustedSize ρ)
      have := coord_le_of_near hyx hxx₀
      constructor <;> simp only <;> linarith [this.1, this.2]
    · have := one_le_siteDist hne
      linarith
  have hsub : routineS (neutralizeAtWiredRoot ρ) ⊆ Y.biUnion fun y =>
      Finset.univ.filter fun e : SquareZeroBond L =>
        (squareZero L).src e = some y ∨ (squareZero L).tgt e = some y := by
    intro e he
    unfold routineS at he
    obtain ⟨y, hye, x, hx, hyx⟩ := (Finset.mem_filter.mp he).2
    rw [siteRestrict_neutralize] at hx hyx
    exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hyx⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hye⟩⟩
  have hS : ((routineS (neutralizeAtWiredRoot ρ)).card : ℝ) ≤ 4 * Y.card := by
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ y ∈ Y, (Finset.univ.filter fun e : SquareZeroBond L =>
        (squareZero L).src e = some y ∨ (squareZero L).tgt e = some y).card ≤ ∑ _y ∈ Y, 4 :=
      Finset.sum_le_sum fun y _ => card_incident_le_four y
    rw [Finset.sum_const, smul_eq_mul] at h2
    have : (routineS (neutralizeAtWiredRoot ρ)).card ≤ 4 * Y.card := by linarith
    exact_mod_cast this
  have hdsc : d ≤ (routineDsc (neutralizeAtWiredRoot ρ) : ℝ) + 1 := by
    unfold routineDsc
    rw [siteRestrict_neutralize]
    have := Nat.le_ceil d
    linarith
  have hbound : (4 * (65 * d) / (1 / 2) + 2) ^ 2 ≤ (522 * d) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    have : 4 * (65 * d) / (1 / 2) = 520 * d := by ring
    linarith
  calc ((routineS (neutralizeAtWiredRoot ρ)).card : ℝ) ≤ 4 * (522 * d) ^ 2 := by nlinarith
    _ = routineKv * d ^ 2 := by unfold routineKv; ring
    _ ≤ routineKv * ((routineDsc (neutralizeAtWiredRoot ρ) : ℝ) + 1) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by unfold routineKv; positivity)
        exact pow_le_pow_left₀ (by linarith) hdsc 2

/-- Two bounded endpoints of one edge are within Euclidean distance `1`. -/
theorem siteDist_le_one_of_endpoints {e : SquareZeroBond L} {u v : Site L}
    (hu : (squareZero L).src e = some u ∨ (squareZero L).tgt e = some u)
    (hv : (squareZero L).src e = some v ∨ (squareZero L).tgt e = some v) :
    (l1 u v : ℝ) ≤ 1 := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, Option.some.injEq] at hv; subst hv; simp [l1_self]
  · exact_mod_cast (l1_of_edge hu hv).le
  · rw [l1_comm]; exact_mod_cast (l1_of_edge hv hu).le
  · rw [hu, Option.some.injEq] at hv; subst hv; simp [l1_self]

/-- **Overlap `≤ 1`.** -/
theorem routineS_overlap {F : Finset (ChargeDensity L)}
    (hsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    (hne : ∀ ρ ∈ F, ρ ≠ 0) (k : ℕ) (e : SquareZeroBond L)
    (U : Finset (RotatorDualFace L → ℤ)) (hU : U ⊆ F.image neutralizeAtWiredRoot)
    (hk : ∀ ϱ ∈ U, 2 ^ k - 1 ≤ routineDsc ϱ ∧ routineDsc ϱ ≤ 2 ^ (k + 1) - 2 ∧
      e ∈ routineS ϱ) : U.card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp (hU ha)
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (hU hb)
  by_contra hab
  have hρσ : ρ ≠ σ := fun h => hab (h ▸ rfl)
  obtain ⟨hk1, hk2, he1⟩ := hk _ ha
  obtain ⟨hk1', hk2', he2⟩ := hk _ hb
  unfold routineS at he1 he2
  obtain ⟨u, hu, x, hx, hux⟩ := (Finset.mem_filter.mp he1).2
  obtain ⟨v, hv, z, hz, hvz⟩ := (Finset.mem_filter.mp he2).2
  unfold routineDsc at hk1 hk2 hk1' hk2'
  simp only [siteRestrict_neutralize] at hx hux hz hvz hk1 hk2 hk1' hk2'
  set dρ := boundaryAdjustedSize ρ
  set dσ := boundaryAdjustedSize σ
  have hdρ : 1 ≤ dρ := one_le_boundaryAdjustedSize (hne ρ hρ)
  have hdσ : 1 ≤ dσ := one_le_boundaryAdjustedSize (hne σ hσ)
  -- the bands
  have hpow1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have hpow2 : (2 : ℕ) ≤ 2 ^ (k + 1) := by
    rw [pow_succ]; omega
  have band : ∀ {d : ℝ}, 0 ≤ d → 2 ^ k - 1 ≤ ⌈d⌉₊ → ⌈d⌉₊ ≤ 2 ^ (k + 1) - 2 →
      d < 2 * 2 ^ k ∧ (2 : ℝ) ^ k < d + 2 := by
    intro d hd0 h1 h2
    have c1 : ((2 ^ k - 1 : ℕ) : ℝ) ≤ (⌈d⌉₊ : ℝ) := by exact_mod_cast h1
    have c2 : (⌈d⌉₊ : ℝ) ≤ ((2 ^ (k + 1) - 2 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_sub hpow1] at c1
    rw [Nat.cast_sub hpow2] at c2
    push_cast at c1 c2
    have := Nat.le_ceil d
    have := Nat.ceil_lt_add_one hd0
    rw [pow_succ] at c2
    constructor <;> linarith
  obtain ⟨bρ1, bρ2⟩ := band (by linarith) hk1 hk2
  obtain ⟨bσ1, bσ2⟩ := band (by linarith) hk1' hk2'
  -- the distance through the shared edge
  have huv := siteDist_le_one_of_endpoints hu hv
  have hxz : euclideanSiteDistance x z ≤ 2 * (64 * dρ) + 1 + 2 * (64 * dσ) := by
    have t1 := l1_triangle x u z
    have t2 := l1_triangle u v z
    have e1 := l1_le_two_siteDist x u
    have e2 := l1_le_two_siteDist v z
    rw [siteDist_comm] at hux
    have c1 : (l1 x z : ℝ) ≤ l1 x u + l1 u v + l1 v z := by exact_mod_cast (t1.trans (by omega))
    exact (siteDist_le_l1 x z).trans (by linarith)
  have hsepρσ := hsep ρ hρ σ hσ hρσ
  have hd := (setDist_le_siteDist hx hz).trans hxz
  have hmin : 1 ≤ min dρ dσ := le_min hdρ hdσ
  have hpow := le_rpow_self hmin one_le_chargeCoverExponent
  have hM : (chargeCoverScale : ℝ) = 65536 := by norm_num [chargeCoverScale]
  rw [hM] at hsepρσ
  rcases le_total dρ dσ with h | h
  · rw [min_eq_left h] at hpow hsepρσ
    nlinarith
  · rw [min_eq_right h] at hpow hsepρσ
    nlinarith

theorem src_some (e : SquareZeroBond L) : ∃ y : Site L, (squareZero L).src e = some y := by
  cases e with
  | inl f => exact ⟨_, rfl⟩
  | inr b => exact ⟨_, rfl⟩

/-- The center's boundary depth is at most the boundary distance of the support. -/
theorem depth_center_le {ρ : ChargeDensity L} (hρ : ρ ≠ 0) {j : Site L}
    (hjmin : ∀ x ∈ chargeSupport ρ, siteBoundaryDepth j ≤ siteBoundaryDepth x) :
    (siteBoundaryDepth j : ℝ) ≤ chargeBoundaryDistance ρ := by
  classical
  have hne := chargeSupport_nonempty_of_ne_zero ρ hρ
  unfold chargeBoundaryDistance euclideanBoundaryDistance
  rw [dite_eq_left hne]
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp (Finset.min'_mem ((chargeSupport ρ).image
    fun x => (siteBoundaryDepth x : ℝ)) (Finset.image_nonempty.mpr hne))
  rw [← hyeq]
  exact_mod_cast hjmin y hy

/-- **The route.** -/
theorem exists_routineRoute (hL : 1 < L) {ρ : ChargeDensity L} (hρ : ρ ≠ 0) :
    ∃ r : SquareZeroBond L → ℤ, (∀ e, r e ≠ 0 → e ∈ routineS (neutralizeAtWiredRoot ρ)) ∧
      (∀ e, |(r e : ℝ)| ≤ ∑ j, |(neutralizeAtWiredRoot ρ j : ℝ)|) ∧
      ∀ σ : RotatorDualFace L → ℝ, ∑ j, σ j * (neutralizeAtWiredRoot ρ j : ℝ) =
        ∑ e, (r e : ℝ) * (squareZero L).grad σ e := by
  classical
  obtain ⟨j, hj, -, hjmin⟩ := routineCenter_spec hρ
  have hG := squareZero_connected L hL
  have hex : ∀ v, ∃ w : (squareZero L).toSimpleGraph.Walk (some j) v,
      w.IsPath ∧ w.length = (squareZero L).toSimpleGraph.dist (some j) v :=
    fun v => hG.exists_path_of_dist (some j) v
  choose w hwp hwl using hex
  have hco := fun v => (squareZero L).exists_path_coeff (w v) (hwp v)
  choose p hp1 hp2 hp3 using hco
  set d := boundaryAdjustedSize ρ
  have hd1 : 1 ≤ d := one_le_boundaryAdjustedSize hρ
  refine ⟨fun e => ∑ v, neutralizeAtWiredRoot ρ v * p v e, fun e he => ?_, fun e => ?_,
    fun σ => ?_⟩
  · obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    have hϱv : neutralizeAtWiredRoot ρ v ≠ 0 := left_ne_zero_of_mul hv
    have hpv : p v e ≠ 0 := right_ne_zero_of_mul hv
    obtain ⟨y, hy⟩ := src_some e
    have hs : some y ∈ (w v).support := hy ▸ (hp2 v e hpv).1
    have hloc := path_site_local (w v) (hwp v) hs
    unfold routineS
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, Or.inl hy, ?_⟩
    rw [siteRestrict_neutralize]
    cases v with
    | some v' =>
      have hv' : v' ∈ chargeSupport ρ := by simpa [chargeSupport] using hϱv
      have hlen : ((w (some v')).length : ℝ) ≤ 2 * d := by
        rw [hwl]
        have h1 : ((squareZero L).toSimpleGraph.dist (some j) (some v') : ℝ) ≤ l1 j v' := by
          exact_mod_cast dist_some_le_l1 j v'
        have h2 := l1_le_two_siteDist j v'
        have h3 : euclideanSiteDistance j v' ≤ d :=
          (siteDist_le_diam hj hv').trans (chargeEuclideanDiameter_le_boundaryAdjustedSize ρ)
        linarith
      rcases hloc with h | ⟨b', hb', h⟩
      · refine ⟨j, hj, ?_⟩
        rw [siteDist_comm]
        have : (l1 j y : ℝ) ≤ (w (some v')).length := by exact_mod_cast h
        linarith [siteDist_le_l1 j y]
      · rw [Option.some.injEq] at hb'
        subst hb'
        refine ⟨v', hv', ?_⟩
        have : (l1 y v' : ℝ) ≤ (w (some v')).length := by exact_mod_cast h
        linarith [siteDist_le_l1 y v']
    | none =>
      have hq : totalCharge ρ ≠ 0 := by
        intro h0
        apply hϱv
        unfold totalCharge at h0
        simp [neutralizeAtWiredRoot, h0]
      have hlen : ((w none).length : ℝ) ≤ d := by
        rw [hwl, squareZero_distance_root_eq_siteBoundaryDepth hL j]
        refine (depth_center_le hρ hjmin).trans ?_
        rw [show d = boundaryAdjustedSize ρ from rfl, boundaryAdjustedSize_of_charged ρ hq]
        exact le_max_left _ _
      rcases hloc with h | ⟨b', hb', -⟩
      · refine ⟨j, hj, ?_⟩
        rw [siteDist_comm]
        have : (l1 j y : ℝ) ≤ (w none).length := by exact_mod_cast h
        linarith [siteDist_le_l1 j y]
      · exact absurd hb' (by simp)
  · push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    rw [abs_mul]
    have : |((p v e : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hp1 v e
    nlinarith [abs_nonneg ((neutralizeAtWiredRoot ρ v : ℤ) : ℝ)]
  · have hsum : ∑ v, (neutralizeAtWiredRoot ρ v : ℝ) = 0 := by
      exact_mod_cast sum_neutralizeAtWiredRoot ρ
    push_cast
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← hp3]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
