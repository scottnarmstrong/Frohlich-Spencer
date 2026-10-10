/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProxyCut
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerPacking
import Mathlib.Tactic

/-!
For a branch family `F` with the Appendix D geometry and any set `C` of members, the members
adjacent to `C` (for `RootedMarkAdjacent`) but outside `C` satisfy

`∑_{m ∈ ∂C} e^{−A(m)} ≤ K_nb (1 + ∑_{m ∈ C} A(m) + ℓ)`   (`ℓ ≥ 0`, `A = layerA`),

with the absolute constant `K_nb = 4 (8 · 2^α + 2)²` (`rootedMarkNeighbourConst`).

Each `m ∈ ∂C` has a face `y_m` of its support within
`M ρ_m^α` of a face `x_m ∈ X(C)`, where `ρ_m = min(d_Λ(m), D(C)) ≥ 1`.

Let `k_m = ⌊log₂ ⌊ρ_m⌋⌋`,
so `2^{k_m} ≤ ρ_m < 2^{k_m + 1}`.

The members with the same pair `(x_m, k_m) = (x, k)`:
* have `y_m` in the box of half-width `M 2^{(k+1)α}` around `x`;
* are pairwise more than `M 2^{kα}/2` apart, since their supports are `M min(d_Λ, d_Λ')^α`-separated
  and `d_Λ ≥ ρ ≥ 2^k`.

Cell packing (`card_le_of_separated`) bounds each such group by `(8 · 2^α + 2)²`.

Since
`A(m) ≥ log₂(⌊ρ_m⌋ + 1) ≥ k_m` (`logb_le_layerA`), summing over `x ∈ X(C)` and `k ≥ 0` gives at most
`2 (8 · 2^α + 2)² |X(C)|`.

Finally `|X(C)| ≤ 2 + ∑_{m ∈ C} ‖m‖₁ ≤ 2 + ∑_{m ∈ C} A(m)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator

/-- The cell-packing constant of one group of neighbours, `(8 · 2^α + 2)²`. -/
def rootedMarkPackingConst : ℝ := (8 * (2 : ℝ) ^ chargeCoverExponent + 2) ^ 2

/-- The neighbour constant `K_nb = 4 (8 · 2^α + 2)²`. -/
def rootedMarkNeighbourConst : ℝ := 4 * rootedMarkPackingConst

theorem rootedMarkPackingConst_nonneg : 0 ≤ rootedMarkPackingConst := by
  unfold rootedMarkPackingConst
  positivity

theorem rootedMarkNeighbourConst_nonneg : 0 ≤ rootedMarkNeighbourConst := by
  unfold rootedMarkNeighbourConst
  have := rootedMarkPackingConst_nonneg
  positivity

section Counting

variable {L : ℕ}

theorem layerA_ge_sum_abs (ϱ : RotatorDualFace L → ℤ) : ∑ j, |(ϱ j : ℝ)| ≤ layerA ϱ := by
  unfold layerA layerCoverSum
  have : 0 ≤ ∑ j ∈ Finset.range (layerCutoff ϱ + 1),
      (squareCoverNumber .free L j (siteRestrict ϱ) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  linarith

theorem layerA_nonneg_of_sum (ϱ : RotatorDualFace L → ℤ) : 0 ≤ layerA ϱ :=
  (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (layerA_ge_sum_abs ϱ)

/-- The face support of a rooted density has at most `‖ϱ‖₁` faces. -/
theorem card_chargeSupport_siteRestrict_le (ϱ : RotatorDualFace L → ℤ) :
    ((chargeSupport (siteRestrict ϱ)).card : ℝ) ≤ ∑ j, |(ϱ j : ℝ)| := by
  classical
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Fintype.sum_option]
  have h1 : ∑ x ∈ chargeSupport (siteRestrict ϱ), ((1 : ℕ) : ℝ) ≤
      ∑ x ∈ chargeSupport (siteRestrict ϱ), |(ϱ (some x) : ℝ)| := by
    refine Finset.sum_le_sum fun x hx => ?_
    have hx' : ϱ (some x) ≠ 0 := mem_chargeSupport'.1 hx
    push_cast
    exact_mod_cast Int.one_le_abs hx'
  have h2 : ∑ x ∈ chargeSupport (siteRestrict ϱ), |(ϱ (some x) : ℝ)| ≤
      ∑ x, |(ϱ (some x) : ℝ)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
  have h3 := abs_nonneg (ϱ none : ℝ)
  linarith

end Counting

variable {R n : ℕ}

/-- `|X(C)| ≤ 2 + ∑_{m ∈ C} A(m)`. -/
theorem card_rootedMarkedSupport_le (hn : n ≤ R)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    ((rootedMarkedSupport R n hn C).card : ℝ) ≤ 2 + ∑ m ∈ C, layerA m := by
  classical
  unfold rootedMarkedSupport
  have h1 := Finset.card_union_le (rootedMarkSites R n hn)
    (C.biUnion fun m => chargeSupport (siteRestrict m))
  have h2 : (rootedMarkSites R n hn).card ≤ 2 := by
    unfold rootedMarkSites
    exact Finset.card_le_two
  have h3 := Finset.card_biUnion_le (s := C) (t := fun m => chargeSupport (siteRestrict m))
  have h4 : ∑ m ∈ C, ((chargeSupport (siteRestrict m)).card : ℝ) ≤ ∑ m ∈ C, layerA m :=
    Finset.sum_le_sum fun m _ =>
      (card_chargeSupport_siteRestrict_le m).trans (layerA_ge_sum_abs m)
  have h5 : ((rootedMarkSites R n hn ∪ C.biUnion fun m => chargeSupport (siteRestrict m)).card : ℝ)
      ≤ (rootedMarkSites R n hn).card + ∑ m ∈ C, ((chargeSupport (siteRestrict m)).card : ℝ) := by
    have := h1.trans (Nat.add_le_add_left h3 _)
    exact_mod_cast this
  have h2' : ((rootedMarkSites R n hn).card : ℝ) ≤ 2 := by exact_mod_cast h2
  linarith

/-- The dyadic scale of `ρ ≥ 1`: `2^k ≤ ρ < 2^{k+1}` for `k = log₂ ⌊ρ⌋`. -/
theorem two_pow_log_floor_le {ρ : ℝ} (hρ : 1 ≤ ρ) :
    (2 : ℝ) ^ Nat.log 2 ⌊ρ⌋₊ ≤ ρ ∧ ρ < (2 : ℝ) ^ (Nat.log 2 ⌊ρ⌋₊ + 1) ∧
      (2 : ℝ) ^ Nat.log 2 ⌊ρ⌋₊ ≤ (⌊ρ⌋₊ : ℝ) := by
  have hfl : 1 ≤ ⌊ρ⌋₊ := Nat.one_le_floor_iff _ |>.mpr hρ
  have h1 : 2 ^ Nat.log 2 ⌊ρ⌋₊ ≤ ⌊ρ⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h2 : ⌊ρ⌋₊ < 2 ^ (Nat.log 2 ⌊ρ⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1' : (2 : ℝ) ^ Nat.log 2 ⌊ρ⌋₊ ≤ (⌊ρ⌋₊ : ℝ) := by exact_mod_cast h1
  have h2' : ((⌊ρ⌋₊ : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊ρ⌋₊ + 1) := by exact_mod_cast h2
  refine ⟨h1'.trans (Nat.floor_le (by linarith)), ?_, h1'⟩
  have := Nat.lt_floor_add_one ρ
  linarith

/-- **One group of neighbours**: statement within `2^α s` of a point and pairwise at least `s` apart
number at most `(8 · 2^α + 2)²`. -/
theorem card_group_le {L : ℕ} {ι : Type*} {T : Finset ι} (y : ι → Generic.PinnedCharges.Site L)
    (x₀ : Generic.PinnedCharges.Site L) {s : ℝ} (hs : 0 < s)
    (hball : ∀ m ∈ T, euclideanSiteDistance (y m) x₀ ≤ (2 : ℝ) ^ chargeCoverExponent * s)
    (hsep : ∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → s ≤ euclideanSiteDistance (y m) (y m')) :
    (T.card : ℝ) ≤ rootedMarkPackingConst := by
  have hbox : ∀ m ∈ T, |((y m).1.val : ℝ) - (x₀.1.val : ℝ)| ≤ (2 : ℝ) ^ chargeCoverExponent * s ∧
      |((y m).2.val : ℝ) - (x₀.2.val : ℝ)| ≤ (2 : ℝ) ^ chargeCoverExponent * s := fun m hm =>
    ⟨(abs_fst_le_siteDist _ _).trans (hball m hm), (abs_snd_le_siteDist _ _).trans (hball m hm)⟩
  have hsep' : ∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → s / 2 < euclideanSiteDistance (y m) (y m') :=
    fun m hm m' hm' hne => by linarith [hsep m hm m' hm' hne]
  have hcard := card_le_of_separated (T := T) y (half_pos hs) ((x₀.1.val : ℝ), (x₀.2.val : ℝ))
    hbox hsep'
  have hval : 4 * ((2 : ℝ) ^ chargeCoverExponent * s) / (s / 2) + 2 =
      8 * (2 : ℝ) ^ chargeCoverExponent + 2 := by
    field_simp
    ring
  rw [hval] at hcard
  exact hcard

/-- **Summation over the groups**: if the members with a given statement and dyadic scale number at
most `c_P`, and each cost dominates its scale, then `∑ e^{−A} ≤ 2 c_P |X|`. -/
theorem sum_exp_neg_le_of_groups {ι κ : Type*} [DecidableEq κ] (D : Finset ι) (X : Finset κ)
    (x : ι → κ) (k : ι → ℕ) (A : ι → ℝ) {cP : ℝ} (hcP : 0 ≤ cP)
    (hx : ∀ m ∈ D, x m ∈ X) (hA : ∀ m ∈ D, (k m : ℝ) ≤ A m)
    (hgroup : ∀ p : κ × ℕ, (((D.filter fun m => (x m, k m) = p).card : ℕ) : ℝ) ≤ cP) :
    ∑ m ∈ D, Real.exp (-1 * A m) ≤ 2 * cP * X.card := by
  classical
  set K : ℕ := D.sup k + 1 with hKdef
  have hmaps : ∀ m ∈ D, (x m, k m) ∈ X ×ˢ Finset.range K := by
    intro m hm
    refine Finset.mem_product.mpr ⟨hx m hm, Finset.mem_range.mpr ?_⟩
    have := Finset.le_sup (f := k) hm
    omega
  have hstep1 : ∑ m ∈ D, Real.exp (-1 * A m) ≤ ∑ m ∈ D, Real.exp (-(k m : ℝ)) :=
    Finset.sum_le_sum fun m hm => Real.exp_le_exp.mpr (by linarith [hA m hm])
  have hstep2 : ∑ m ∈ D, Real.exp (-(k m : ℝ)) =
      ∑ p ∈ X ×ˢ Finset.range K, ∑ m ∈ D with (x m, k m) = p, Real.exp (-(k m : ℝ)) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hstep3 : ∀ p ∈ X ×ˢ Finset.range K,
      ∑ m ∈ D with (x m, k m) = p, Real.exp (-(k m : ℝ)) ≤ cP * Real.exp (-(p.2 : ℝ)) := by
    intro p _
    have heq : ∀ m ∈ D.filter (fun m => (x m, k m) = p),
        Real.exp (-(k m : ℝ)) = Real.exp (-(p.2 : ℝ)) := by
      intro m hm
      have hk : k m = p.2 := congrArg Prod.snd (Finset.mem_filter.mp hm).2
      rw [hk]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hgroup p) (Real.exp_pos _).le
  have hgeom : ∑ i ∈ Finset.range K, Real.exp (-(i : ℝ)) ≤ 2 := by
    have he : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      exact inv_anti₀ (by norm_num) h2
    calc ∑ i ∈ Finset.range K, Real.exp (-(i : ℝ)) =
        ∑ i ∈ Finset.range K, Real.exp (-1) ^ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Real.exp_nat_mul]
          ring_nf
      _ ≤ ∑ i ∈ Finset.range K, (1 / (2 : ℝ)) ^ i :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (Real.exp_pos _).le he i
      _ ≤ 2 := sum_geometric_two_le K
  have hstep4 : ∑ p ∈ X ×ˢ Finset.range K, cP * Real.exp (-(p.2 : ℝ)) ≤ 2 * cP * X.card := by
    rw [Finset.sum_product]
    calc ∑ a ∈ X, ∑ i ∈ Finset.range K, cP * Real.exp (-(i : ℝ)) =
        ∑ a ∈ X, cP * ∑ i ∈ Finset.range K, Real.exp (-(i : ℝ)) := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ _a ∈ X, cP * 2 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left hgeom hcP
      _ = 2 * cP * X.card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  rw [hstep2] at hstep1
  exact (hstep1.trans (Finset.sum_le_sum hstep3)).trans hstep4

/-- The statement of an adjacent member: a face of its support within the adjacency radius of a face
of `X(C)`. -/
theorem exists_anchor_of_rootedMarkAdjacent (hn : n ≤ R)
    {m : RotatorDualFace (sideLength R) → ℤ} (hm0 : siteRestrict m ≠ 0)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hadj : RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn m C) :
    ∃ y ∈ chargeSupport (siteRestrict m), ∃ x ∈ rootedMarkedSupport R n hn C,
      euclideanSiteDistance y x <
        (chargeCoverScale : ℝ) * rootedMarkScale R n hn m C ^ chargeCoverExponent := by
  obtain ⟨y, hy, x, hx, heq⟩ := exists_setDist_eq
    (chargeSupport_nonempty_of_ne_zero _ hm0) (rootedMarkedSupport_nonempty hn C)
  exact ⟨y, hy, x, hx, heq ▸ hadj⟩

/-- **The neighbour count of the marked clusters.** -/
theorem sum_exp_neg_layerA_rootedMarkNeighbour_le (hn : n ≤ R) (hn0 : 0 < n)
    (F : Finset (ChargeDensity (sideLength R)))
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∑ m ∈ F.image neutralizeAtWiredRoot \ (C ∪ remainder
        (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
        (F.image neutralizeAtWiredRoot) C), Real.exp (-1 * layerA m) ≤
      rootedMarkNeighbourConst * (1 + ∑ m ∈ C, layerA m + ℓ) := by
  classical
  have : Nonempty (Site R) := ⟨center R⟩
  set N := F.image neutralizeAtWiredRoot with hN
  set D := N \ (C ∪ remainder (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent
    R n hn) N C) with hD
  have hα0 : 0 ≤ chargeCoverExponent := le_trans zero_le_one one_le_chargeCoverExponent
  have hM : (0 : ℝ) < chargeCoverScale := by norm_num [chargeCoverScale]
  -- the members of `∂C`
  have hmem : ∀ m ∈ D, m ∈ N ∧
      RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn m C := by
    intro m hm
    rw [hD, Finset.mem_sdiff, Finset.mem_union] at hm
    push Not at hm
    refine ⟨hm.1, ?_⟩
    by_contra hadj
    exact hm.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hm.1, hm.2.1⟩, hadj⟩)
  have hsr : ∀ m ∈ D, siteRestrict m ∈ F ∧ neutralizeAtWiredRoot (siteRestrict m) = m :=
    fun m hm => siteRestrict_mem_of_mem_image (hmem m hm).1
  have hne0 : ∀ m ∈ D, siteRestrict m ≠ 0 := fun m hm => hgeo.ensemble.1 _ (hsr m hm).1
  have hD1 : 1 ≤ rootedClusterSize R n hn C :=
    (one_le_diam_rootedMarkedSupport hn hn0 C).trans
      (diam_rootedMarkedSupport_le_rootedClusterSize hn C)
  have hρ1 : ∀ m ∈ D, 1 ≤ rootedMarkScale R n hn m C := fun m hm =>
    le_min (one_le_boundaryAdjustedSize (hne0 m hm)) hD1
  have hρd : ∀ m, rootedMarkScale R n hn m C ≤ boundaryAdjustedSize (siteRestrict m) :=
    fun m => min_le_left _ _
  have hpair : ∀ m ∈ D, ∃ y ∈ chargeSupport (siteRestrict m), ∃ x ∈ rootedMarkedSupport R n hn C,
      euclideanSiteDistance y x <
        (chargeCoverScale : ℝ) * rootedMarkScale R n hn m C ^ chargeCoverExponent :=
    fun m hm => exists_anchor_of_rootedMarkAdjacent hn (hne0 m hm) (hmem m hm).2
  choose! y hy x hx hdist using hpair
  set k : (RotatorDualFace (sideLength R) → ℤ) → ℕ :=
    fun m => Nat.log 2 ⌊rootedMarkScale R n hn m C⌋₊ with hkdef
  have hk : ∀ m ∈ D, (2 : ℝ) ^ k m ≤ rootedMarkScale R n hn m C ∧
      rootedMarkScale R n hn m C < (2 : ℝ) ^ (k m + 1) :=
    fun m hm => ⟨(two_pow_log_floor_le (hρ1 m hm)).1, (two_pow_log_floor_le (hρ1 m hm)).2.1⟩
  -- the cost dominates the scale
  have hAk : ∀ m ∈ D, (k m : ℝ) ≤ layerA m := by
    intro m hm
    have h3 := (two_pow_log_floor_le (hρ1 m hm)).2.2
    have hd : ((⌊rootedMarkScale R n hn m C⌋₊ : ℕ) : ℝ) + 1 ≤
        2 ^ 16 * boundaryAdjustedSize (siteRestrict m) := by
      have h4 : ((⌊rootedMarkScale R n hn m C⌋₊ : ℕ) : ℝ) ≤
          boundaryAdjustedSize (siteRestrict m) :=
        (Nat.floor_le (by linarith [hρ1 m hm])).trans (hρd m)
      have h5 := one_le_boundaryAdjustedSize (hne0 m hm)
      nlinarith
    have hlog := logb_le_layerA (hne0 m hm) hd
    rw [(hsr m hm).2] at hlog
    refine le_trans ?_ hlog
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    linarith
  -- one group of neighbours
  have hgroup : ∀ p : Site R × ℕ,
      (((D.filter fun m => (x m, k m) = p).card : ℕ) : ℝ) ≤ rootedMarkPackingConst := by
    intro p
    have hGD : ∀ m ∈ D.filter (fun m => (x m, k m) = p), m ∈ D :=
      fun m hm => (Finset.mem_filter.mp hm).1
    have hGp : ∀ m ∈ D.filter (fun m => (x m, k m) = p), x m = p.1 ∧ k m = p.2 :=
      fun m hm => Prod.ext_iff.mp (Finset.mem_filter.mp hm).2
    refine card_group_le y p.1 (s := (chargeCoverScale : ℝ) * ((2 : ℝ) ^ p.2) ^ chargeCoverExponent)
      (by positivity) ?_ ?_
    · intro m hm
      have hmD := hGD m hm
      obtain ⟨hxm, hkm⟩ := hGp m hm
      have hρk : rootedMarkScale R n hn m C ^ chargeCoverExponent ≤
          ((2 : ℝ) ^ (p.2 + 1)) ^ chargeCoverExponent :=
        Real.rpow_le_rpow (by linarith [hρ1 m hmD]) (hkm ▸ (hk m hmD).2).le hα0
      have hsplit : ((2 : ℝ) ^ (p.2 + 1)) ^ chargeCoverExponent =
          (2 : ℝ) ^ chargeCoverExponent * ((2 : ℝ) ^ p.2) ^ chargeCoverExponent := by
        rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num), mul_comm]
      have h1 := hdist m hmD
      rw [hxm] at h1
      have h2 := mul_le_mul_of_nonneg_left hρk hM.le
      rw [hsplit] at h2
      nlinarith
    · intro m hm m' hm' hne
      have hmD := hGD m hm
      have hm'D := hGD m' hm'
      have hsrne : siteRestrict m ≠ siteRestrict m' := by
        intro h
        apply hne
        rw [← (hsr m hmD).2, ← (hsr m' hm'D).2, h]
      have hF := hgeo.separated _ (hsr m hmD).1 _ (hsr m' hm'D).1 hsrne
      have hmin : (2 : ℝ) ^ p.2 ≤
          min (boundaryAdjustedSize (siteRestrict m)) (boundaryAdjustedSize (siteRestrict m')) :=
        le_min ((hGp m hm).2 ▸ (hk m hmD).1.trans (hρd m))
          ((hGp m' hm').2 ▸ (hk m' hm'D).1.trans (hρd m'))
      have hpow : ((2 : ℝ) ^ p.2) ^ chargeCoverExponent ≤
          min (boundaryAdjustedSize (siteRestrict m))
            (boundaryAdjustedSize (siteRestrict m')) ^ chargeCoverExponent :=
        Real.rpow_le_rpow (by positivity) hmin hα0
      have hset := setDist_le_siteDist (hy m hmD) (hy m' hm'D)
      calc (chargeCoverScale : ℝ) * ((2 : ℝ) ^ p.2) ^ chargeCoverExponent
          ≤ (chargeCoverScale : ℝ) * min (boundaryAdjustedSize (siteRestrict m))
              (boundaryAdjustedSize (siteRestrict m')) ^ chargeCoverExponent :=
            mul_le_mul_of_nonneg_left hpow hM.le
        _ ≤ _ := hF.trans hset
  have hsum := sum_exp_neg_le_of_groups D (rootedMarkedSupport R n hn C) x k layerA
    rootedMarkPackingConst_nonneg hx hAk hgroup
  have hX := card_rootedMarkedSupport_le hn C
  have hCA : 0 ≤ ∑ m ∈ C, layerA m := Finset.sum_nonneg fun m _ => layerA_nonneg_of_sum m
  have hP := rootedMarkPackingConst_nonneg
  calc ∑ m ∈ D, Real.exp (-1 * layerA m)
      ≤ 2 * rootedMarkPackingConst * (rootedMarkedSupport R n hn C).card := hsum
    _ ≤ 2 * rootedMarkPackingConst * (2 + ∑ m ∈ C, layerA m) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ rootedMarkNeighbourConst * (1 + ∑ m ∈ C, layerA m + ℓ) := by
        unfold rootedMarkNeighbourConst
        nlinarith

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
