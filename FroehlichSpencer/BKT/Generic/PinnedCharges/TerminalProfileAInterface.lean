/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAGeometry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3Support

/-!
# The profile potential and the support-control input )

* `zero`: `f = 0` on `K`;
* `lipschitz`: `f` grows by at most one per lattice step;
* `collapse`: `f` is constant across every lattice step inside the neighbourhood
  `E_σ = {x : dist(x, supp σ) ≤ 8 d_Λ(σ) + 2}` (the terminal decomposition's `profileA3NeutralNeighborhood`) of each
  density of `profileCollapseFamily`: the densities `σ ≠ ρ` of the ensemble that are neutral, tiny
  (`M d_Λ(σ)^α ≤ 5·2^j`), and whose `E_σ` meets the Euclidean `(9/4)·2^j`-neighbourhood of `K`;
* `support`: the terminal decomposition's `ProfileA3CollapsedSupportControl j K f`, i.e.

`f x < 2^{j+1}` forces
  `dist(K, x) ≤ (9/8) f x`.

The collapsed lattice metric `d̃_j(·, K)` of the note (steps inside one collapsed `E_σ` cost `0`)
satisfies the first three clauses by construction, for any collapse family containing
`profileCollapseFamily`.

`TerminalSupportControl` asks for such a
potential for every charged selected square of every comb terminal; it is the one input of the
construction.

This file also records the data of a charged selected square (`ChargedSelectedSquare`):
the square, boundary depth `≥ 2^{j+2}` on the cluster, distance `≥ 2M 2^{αj}` from the cluster to
the rest of `ρ`, and `d_Λ(ρ) ≥ 2^{j+1}`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The densities collapsed by the scale-`j` profile of `ρ` with cluster `K`: the other neutral
densities of the ensemble with `M d_Λ(σ)^α ≤ 5·2^j` whose neighbourhood `E_σ` meets the Euclidean
`(9/4)·2^j`-neighbourhood of `K`. -/
def profileCollapseFamily (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K : Finset (Site L)) : Finset (ChargeDensity L) := by
  classical
  exact F.filter fun σ => σ ≠ ρ ∧ totalCharge σ = 0 ∧
    (chargeCoverScale : ℝ) * boundaryAdjustedSize σ ^ chargeCoverExponent ≤ 5 * 2 ^ j ∧
    (profileA3NeutralNeighborhood σ ∩ boundaryEnergyNeighborhood (9 / 4 * 2 ^ j) K).Nonempty

/-- **A profile potential** for the scale-`j` cluster `K` of `ρ` in the ensemble `F`. -/
structure IsProfilePotential (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K : Finset (Site L)) (f : Site L → ℝ) : Prop where
  zero : ∀ x ∈ K, f x = 0
  lipschitz : ∀ x y : Site L, l1 x y = 1 → f x ≤ f y + 1
  collapse : ∀ σ ∈ profileCollapseFamily F ρ j K, ∀ x ∈ profileA3NeutralNeighborhood σ,
    ∀ y ∈ profileA3NeutralNeighborhood σ, l1 x y = 1 → f x = f y
  support : ProfileA3CollapsedSupportControl j K f


def TerminalSupportControl : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T → ∀ ρ ∈ T.F,
    ∀ j ∈ Finset.Icc 1 (layerCutoff (neutralizeAtWiredRoot ρ)),
    ∀ s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j,
      totalCharge (chargeRestriction ρ s) ≠ 0 →
        ∃ f : Site L → ℝ, IsProfilePotential T.F ρ j (chargeSupport (chargeRestriction ρ s)) f

/-! ## Charged selected squares -/

/-- The selection separation `R_j = 2M 2^{αj}`. -/
def selectionSeparation (j : ℕ) : ℝ :=
  2 * (chargeCoverScale : ℝ) * (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ))

theorem chargeCoverScale_eq : (chargeCoverScale : ℝ) = 65536 := by
  norm_num [chargeCoverScale]

theorem two_pow_le_selectionSeparation (j : ℕ) :
    2 * 65536 * (2 : ℝ) ^ j ≤ selectionSeparation j := by
  unfold selectionSeparation
  rw [chargeCoverScale_eq]
  have h : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (le_mul_of_one_le_left (Nat.cast_nonneg j) one_le_chargeCoverExponent)
  linarith

theorem euclideanBoundaryDistance_le_depth {s : Finset (Site L)} {x : Site L} (hx : x ∈ s) :
    euclideanBoundaryDistance s ≤ siteBoundaryDepth x := by
  unfold euclideanBoundaryDistance
  rw [dite_eq_left ⟨x, hx⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)

/-- **The data of a charged selected square.** -/
structure ChargedSelectedSquare (ρ : ChargeDensity L) (j : ℕ) (s : Finset (Site L)) : Prop where
  square : s ∈ kpSquares .free L j
  charged : totalCharge (chargeRestriction ρ s) ≠ 0
  depth : ∀ k ∈ chargeSupport (chargeRestriction ρ s), (2 : ℝ) ^ (j + 2) ≤ siteBoundaryDepth k
  far : ∀ k ∈ chargeSupport (chargeRestriction ρ s), ∀ y ∈ chargeSupport ρ, y ∉ s →
    selectionSeparation j ≤ euclideanSiteDistance k y
  size : (2 : ℝ) ^ (j + 1) ≤ boundaryAdjustedSize ρ

theorem chargedSelectedSquare_of_mem {ρ : ChargeDensity L} {j : ℕ} {s : Finset (Site L)}
    (hs : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ
      (boundaryEntropyMinimumCover ρ j))
    (hq : totalCharge (chargeRestriction ρ s) ≠ 0) : ChargedSelectedSquare ρ j s := by
  classical
  set C := boundaryEntropyMinimumCover ρ j with hCdef
  have hC : IsMinimumSquareCover .free L j ρ C := boundaryEntropyMinimumCover_isMinimum ρ j
  obtain ⟨hsC, hsq⟩ := pinnedPPrime_mem_of_minimumCover _ _ j ρ C hC hs
  have hK : chargeRestriction ρ s ≠ 0 := fun h => hq (by simp [h, totalCharge])
  obtain ⟨k₀, hk₀⟩ := chargeSupport_nonempty_of_ne_zero _ hK
  have hk₀' := (mem_chargeSupport_restriction_iff ρ s k₀).mp hk₀
  have hρ : ρ ≠ 0 := by
    rintro rfl
    exact (Finset.mem_filter.mp hk₀'.2).2 rfl
  by_cases hsingle : C.card = 1
  · have hkeep : totalCharge ρ ≠ 0 ∧ singletonBoundaryMargin j ≤ chargeBoundaryDistance ρ := by
      by_contra hfail
      rw [pinnedPPrime_eq_empty_of_singleton_exception_fails _ _ j ρ C hsingle hfail] at hs
      exact Finset.notMem_empty _ hs
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsingle
    have hsupp : chargeSupport ρ ⊆ s := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
      have htu : t = u := by simpa [hu] using ht
      have hsu : s = u := by simpa [hu] using hsC
      rw [hsu, ← htu]
      exact hxt
    have hbd : (2 : ℝ) ^ (j + 3) ≤ chargeBoundaryDistance ρ := by
      simpa [singletonBoundaryMargin] using hkeep.2
    refine ⟨hsq, hq, fun k hk => ?_, fun k _ y hy hys => absurd (hsupp hy) hys, ?_⟩
    · have hkρ := ((mem_chargeSupport_restriction_iff ρ s k).mp hk).2
      have hle : chargeBoundaryDistance ρ ≤ siteBoundaryDepth k :=
        euclideanBoundaryDistance_le_depth hkρ
      have : (2 : ℝ) ^ (j + 2) ≤ 2 ^ (j + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    · have hle := chargeBoundaryDistance_le_boundaryAdjustedSize_of_charged ρ hkeep.1
      have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ (j + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  · obtain ⟨-, hsep, hmargin⟩ := (mem_pinnedPPrime_of_cover_card_ne_one _ _ j ρ C hsingle s).1 hs
    have hdepth : ∀ k ∈ chargeSupport (chargeRestriction ρ s),
        (2 : ℝ) ^ (j + 2) ≤ siteBoundaryDepth k := by
      intro k hk
      have hks := ((mem_chargeSupport_restriction_iff ρ s k).mp hk).1
      have := euclideanBoundaryDistance_le_depth hks
      have hm : scaleBoundaryMargin j = (2 : ℝ) ^ (j + 2) := rfl
      linarith
    have hfar : ∀ k ∈ chargeSupport (chargeRestriction ρ s), ∀ y ∈ chargeSupport ρ, y ∉ s →
        selectionSeparation j ≤ euclideanSiteDistance k y := by
      intro k hk y hy hys
      have hks := ((mem_chargeSupport_restriction_iff ρ s k).mp hk).1
      obtain ⟨t, ht, hyt⟩ := hC.1.2 y hy
      have hts : t ≠ s := by rintro rfl; exact hys hyt
      exact (hsep t ht hts).trans (setDist_le_siteDist hks hyt)
    refine ⟨hsq, hq, hdepth, hfar, ?_⟩
    by_cases hQ : totalCharge ρ = 0
    · -- a neutral parent has charge outside the square
      obtain ⟨y, hy, hys⟩ : ∃ y ∈ chargeSupport ρ, y ∉ s := by
        by_contra hall
        push Not at hall
        apply hq
        have : chargeRestriction ρ s = ρ := by
          funext x
          by_cases hxs : x ∈ s
          · simp [chargeRestriction, hxs]
          · have hx0 : ρ x = 0 := by
              by_contra hx
              exact hxs (hall x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
            simp [chargeRestriction, hxs, hx0]
        rw [this]
        exact hQ
      have h1 := hfar k₀ hk₀ y hy hys
      have h2 := two_pow_le_selectionSeparation j
      have h3 : euclideanSiteDistance k₀ y ≤ chargeEuclideanDiameter ρ := siteDist_le_diam hk₀'.2 hy
      have h4 := chargeEuclideanDiameter_le_boundaryAdjustedSize ρ
      have h5 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      have h6 : (0 : ℝ) < 2 ^ j := by positivity
      linarith
    · have h1 := depth_le_two_boundaryAdjustedSize hQ hk₀'.2
      have h2 := hdepth k₀ hk₀
      have h3 : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      linarith

/-- Two distinct selected squares of one scale are `R_j` apart. -/
theorem selectionSeparation_le_of_ne {ρ : ChargeDensity L} {j : ℕ} {s s' : Finset (Site L)}
    (hs : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ
      (boundaryEntropyMinimumCover ρ j))
    (hs' : s' ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ
      (boundaryEntropyMinimumCover ρ j))
    (hne : s ≠ s') {k k' : Site L} (hk : k ∈ s) (hk' : k' ∈ s') :
    selectionSeparation j ≤ euclideanSiteDistance k k' := by
  classical
  set C := boundaryEntropyMinimumCover ρ j
  have hC : IsMinimumSquareCover .free L j ρ C := boundaryEntropyMinimumCover_isMinimum ρ j
  have hsC := (pinnedPPrime_mem_of_minimumCover _ _ j ρ C hC hs).1
  have hs'C := (pinnedPPrime_mem_of_minimumCover _ _ j ρ C hC hs').1
  by_cases hsingle : C.card = 1
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsingle
    have h1 : s = u := by simpa [hu] using hsC
    have h2 : s' = u := by simpa [hu] using hs'C
    exact absurd (h1.trans h2.symm) hne
  · obtain ⟨-, hsep, -⟩ := (mem_pinnedPPrime_of_cover_card_ne_one _ _ j ρ C hsingle s).1 hs
    exact (hsep s' hs'C (Ne.symm hne)).trans (setDist_le_siteDist hk hk')

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
