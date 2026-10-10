/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3CertPath
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3Terminal

/-!
# Path certificates for the collapsed potential, and Theorem C from the component decomposition

**The input** is the max-scale component decomposition of the zero-cost components of
`profileCollapsedSets`. Its consequence, used here, is `ProfileA3RootedComponents`: every
component `C` has a root `σ` in the collapse family whose support lies in `C`, with every point of
`C` within `ℓ¹` length `40 d_Λ(σ)` of `supp σ` (`ProfileA3ComponentRootedAt`) and `C` of `ℓ¹`
diameter at most `40 d_Λ(σ)`. the terminal decomposition's decomposition form (`ProfileA3UniqueMaxDecomposition`) implies
it through the terminal decomposition's `profileA3_component_bounds_of_uniqueMax_decomposition`
(`profileA3RootedComponents_of_uniqueMaxDecomposition`).

**The certificate.** For `x` with `d(x) < 2^{j+1}`, take a walk from `K` to `x` of paid length
`d(x)` (`exists_walk_of_lt`) and its shortcut decomposition (`exists_collapsedPathData`).

* If it visits a zero-cost component, `profileA3PathWitness_of_data` builds the terminal decomposition's
  `ProfileA3PathWitness`:
  - components are the visited ones, with size `d_Λ(root)` and diameter `40·size`;
  - bins are `⌊log₂ size⌋`, positions come from the decomposition, and the budget is
    `d(x) + Σ diameters`;
  - the parent is the largest visited component.

  Same-bin separation follows from the terminal decomposition's inter-component bound with
  `65536·(2^k)^{7/4} − 160·2^k ≥ 32768·2^k(4/3)^k`.
* If it visits none, `eucl ≤ d(x)` directly.

Hence `ProfileA3CollapsedSupportControl` (`collapsedSupportControl_of_rootedComponents`), and
Theorem C from the decomposition alone (`theoremC_of_rootedComponents`,
`theoremC_of_uniqueMaxDecomposition`).

**About `TerminalProfileA3PathCertificatesLarge`.** That hypothesis asks for a witness at *every*
`x`. A witness forces `budget ≥ 65496` (parent separation) and `budget ≤ (80/79) d(x)`, so none
exists where `d(x) < 64000`, in particular on the cluster itself
(`not_nonempty_profileA3PathWitness_of_lt`, `not_nonempty_profileA3PathWitness_of_mem`). The
hypothesis is therefore unsatisfiable on any terminal with a charged selected square at a scale
`j ≥ 14`. The support control only needs the points with `d(x) < 2^{j+1}`, and the component-free
walks need no certificate; the route here takes that into account.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open Filter
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-! ## The witness format cannot hold near the cluster -/

/-- A path witness at `x` forces `d(x) ≥ 64000`. -/
theorem le_of_nonempty_profileA3PathWitness {K : Finset (Site L)} {d : Site L → ℝ} {x : Site L}
    (W : ProfileA3PathWitness K d x) : 64000 ≤ d x := by
  have hmax : 1 ≤ W.maxSize := by
    calc (1 : ℝ) ≤ (2 : ℝ) ^ W.maxBin := one_le_pow₀ (by norm_num)
      _ ≤ W.maxSize := W.max_size_lower
  have hparent := profileA3_parent_budget_from_separation W.maxSize W.parentSize
    W.parentDistance W.budget hmax W.parent_scale_order
    W.parent_component_separation W.parent_path_length
  have hcost := @profileA3_path_component_cost_small W.Index W.indexDecidableEq W.components W.size
    W.diameter W.bin W.maxBin W.budget W.maxSize W.packing W.component_diameter hparent
  have hb := W.budget_eq
  nlinarith

theorem not_nonempty_profileA3PathWitness_of_lt {K : Finset (Site L)} {d : Site L → ℝ}
    {x : Site L} (hx : d x < 64000) : ¬ Nonempty (ProfileA3PathWitness K d x) :=
  fun ⟨W⟩ => absurd (le_of_nonempty_profileA3PathWitness W) (not_le.mpr hx)

/-- **On the cluster no witness exists**: `TerminalProfileA3PathCertificatesLarge` is unsatisfiable
on any terminal with a charged selected square at a scale `j ≥ 14`. -/
theorem not_nonempty_profileA3PathWitness_of_mem {F : Finset (ChargeDensity L)}
    {ρ : ChargeDensity L} {j : ℕ} {K : Finset (Site L)} {x : Site L} (hx : x ∈ K) :
    ¬ Nonempty (ProfileA3PathWitness K (profileCollapsedPotential F ρ j K) x) := by
  apply not_nonempty_profileA3PathWitness_of_lt
  unfold profileCollapsedPotential
  rw [collapsedDistance_eq_zero hx, Nat.cast_zero]
  norm_num

/-! ## The component hypothesis -/

/-- **The rooted component decomposition** of the zero-cost components of the scale-`j` profile
of `ρ` with cluster `K`. -/
def ProfileA3RootedComponents (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K : Finset (Site L)) : Prop :=
  ∀ y, InCollapsed (profileCollapsedSets F ρ j K) y →
    ∃ σ ∈ profileCollapseFamily F ρ j K,
      chargeSupport σ ⊆ collapsedComponent (profileCollapsedSets F ρ j K) y ∧
      ProfileA3ComponentRootedAt (collapsedComponent (profileCollapsedSets F ρ j K) y) σ
        (boundaryAdjustedSize σ) ∧
      ∀ z ∈ collapsedComponent (profileCollapsedSets F ρ j K) y,
        ∀ z' ∈ collapsedComponent (profileCollapsedSets F ρ j K) y,
          profileA3GraphLength z z' ≤ 40 * boundaryAdjustedSize σ

/-- **the terminal decomposition's decomposition form**: each zero-cost component is the neighbourhood of its maximal
member together with low pieces of `ℓ¹` diameter `≤ 4 d_Λ` attached at `ℓ¹` length `≤ 1`. -/
def ProfileA3UniqueMaxDecomposition (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K : Finset (Site L)) : Prop :=
  ∀ y, InCollapsed (profileCollapsedSets F ρ j K) y →
    ∃ σ ∈ profileCollapseFamily F ρ j K, ∃ lowPieces : Finset (Finset (Site L)),
      collapsedComponent (profileCollapsedSets F ρ j K) y =
        profileA3NeutralNeighborhood σ ∪ lowPieces.biUnion id ∧
      (∀ S ∈ lowPieces, ∀ x ∈ S, ∀ x' ∈ S,
        profileA3GraphLength x x' ≤ 4 * boundaryAdjustedSize σ) ∧
      (∀ S ∈ lowPieces, ∃ z ∈ S, ∃ u ∈ profileA3NeutralNeighborhood σ,
        profileA3GraphLength z u ≤ 1)

/-- The decomposition gives rooted components (the terminal decomposition's gluing lemma). -/
theorem profileA3RootedComponents_of_uniqueMaxDecomposition {F : Finset (ChargeDensity L)}
    (hF : ∀ σ ∈ F, σ ≠ 0) {ρ : ChargeDensity L} {j : ℕ} {K : Finset (Site L)}
    (h : ProfileA3UniqueMaxDecomposition F ρ j K) : ProfileA3RootedComponents F ρ j K := by
  classical
  intro y hy
  obtain ⟨σ, hσ, lowPieces, hcover, hlowDiam, hlowAttach⟩ := h y hy
  have hσ0 : σ ≠ 0 := hF σ (Finset.mem_filter.mp hσ).1
  obtain ⟨hroot, hdiam⟩ := profileA3_component_bounds_of_uniqueMax_decomposition σ hσ0
    (collapsedComponent (profileCollapsedSets F ρ j K) y) (profileA3NeutralNeighborhood σ)
    lowPieces rfl hcover hlowDiam hlowAttach
  refine ⟨σ, hσ, fun a ha => ?_, hroot, hdiam⟩
  rw [hcover]
  refine Finset.mem_union_left _ ?_
  rw [profileA3NeutralNeighborhood, mem_boundaryEnergyNeighborhood_iff]
  refine ⟨a, ha, ?_⟩
  rw [siteDist_self]
  have := boundaryAdjustedSize_nonneg σ
  linarith

/-- The rooted decomposition on every comb terminal, at the scales `j ≥ 14`. -/
def TerminalProfileA3RootedComponentsLarge : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T → ∀ ρ ∈ T.F,
    ∀ j ∈ Finset.Icc 14 (layerCutoff (neutralizeAtWiredRoot ρ)),
    ∀ s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j,
      totalCharge (chargeRestriction ρ s) ≠ 0 →
        ProfileA3RootedComponents T.F ρ j (chargeSupport (chargeRestriction ρ s))

/-- the terminal decomposition's decomposition on every comb terminal, at the scales `j ≥ 14`. -/
def TerminalProfileA3UniqueMaxDecompositionLarge : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T → ∀ ρ ∈ T.F,
    ∀ j ∈ Finset.Icc 14 (layerCutoff (neutralizeAtWiredRoot ρ)),
    ∀ s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j,
      totalCharge (chargeRestriction ρ s) ≠ 0 →
        ProfileA3UniqueMaxDecomposition T.F ρ j (chargeSupport (chargeRestriction ρ s))

theorem terminalRootedComponentsLarge_of_decomposition
    (h : TerminalProfileA3UniqueMaxDecompositionLarge) : TerminalProfileA3RootedComponentsLarge :=
  fun L N T hT ρ hρ j hj s hs hq =>
    profileA3RootedComponents_of_uniqueMaxDecomposition hT.geometry.ensemble.1
      (h L N T hT ρ hρ j hj s hs hq)

/-! ## Dyadic bins -/

/-- The dyadic bin `⌊log₂ D⌋` of a size `D ≥ 1`. -/
def profileA3Bin (D : ℝ) : ℕ := Nat.log 2 ⌊D⌋₊

theorem two_pow_profileA3Bin_le {D : ℝ} (hD : 1 ≤ D) : (2 : ℝ) ^ profileA3Bin D ≤ D := by
  have hn : ⌊D⌋₊ ≠ 0 := by
    have := Nat.floor_pos.mpr hD
    omega
  have h1 : 2 ^ profileA3Bin D ≤ ⌊D⌋₊ := Nat.pow_log_le_self 2 hn
  have h2 : ((⌊D⌋₊ : ℕ) : ℝ) ≤ D := Nat.floor_le (by linarith)
  calc (2 : ℝ) ^ profileA3Bin D = ((2 ^ profileA3Bin D : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ D := h2

theorem lt_two_pow_profileA3Bin_succ (D : ℝ) :
    D < (2 : ℝ) ^ (profileA3Bin D + 1) := by
  have h1 : ⌊D⌋₊ < 2 ^ (profileA3Bin D).succ := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : D < (⌊D⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one D
  have h3 : ((⌊D⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (profileA3Bin D + 1) : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h3
  linarith

theorem profileA3Bin_mono {D D' : ℝ} (h : D ≤ D') : profileA3Bin D ≤ profileA3Bin D' :=
  Nat.log_mono_right (Nat.floor_mono h)

/-- `8/3 ≤ 2^{7/4}`. -/
theorem eight_thirds_le_rpow : (8 / 3 : ℝ) ≤ (2 : ℝ) ^ (7 / 4 : ℝ) := by
  have h4 : ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ (4 : ℕ) = 128 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos : 0 ≤ (2 : ℝ) ^ (7 / 4 : ℝ) := by positivity
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt hpos (by norm_num : (4 : ℕ) ≠ 0)
  rw [h4] at this
  norm_num at this

/-- The same-bin separation: `32768·2^k(4/3)^k ≤ 65536 min(D,D')^{7/4} − 40(D + D')` for sizes in
the bin `[2^k, 2^{k+1})`. -/
theorem sameBin_separation_le (k : ℕ) {D D' : ℝ} (hD : (2 : ℝ) ^ k ≤ D) (hD' : (2 : ℝ) ^ k ≤ D')
    (hDu : D < (2 : ℝ) ^ (k + 1)) (hD'u : D' < (2 : ℝ) ^ (k + 1)) :
    (32768 : ℝ) * (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k ≤
      (65536 : ℝ) * min D D' ^ (7 / 4 : ℝ) - 40 * (D + D') := by
  have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hmin : (2 : ℝ) ^ k ≤ min D D' := le_min hD hD'
  have hpow : ((2 : ℝ) ^ k) ^ (7 / 4 : ℝ) ≤ min D D' ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hmin (by norm_num)
  have hX : ((2 : ℝ) ^ k) ^ (7 / 4 : ℝ) = ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hthirds : ((8 : ℝ) / 3) ^ k ≤ ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ k :=
    pow_le_pow_left₀ (by norm_num) eight_thirds_le_rpow k
  have hsplit : (2 : ℝ) ^ k * ((4 : ℝ) / 3) ^ k = ((8 : ℝ) / 3) ^ k := by
    rw [← mul_pow]; norm_num
  have h2le : (2 : ℝ) ^ k ≤ ((8 : ℝ) / 3) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hup : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [mul_assoc, hsplit]
  nlinarith

/-! ## The certificate -/

/-- The pointwise `9/8` bound from one witness (the body of the terminal decomposition's
`profileA3CollapsedSupportControl_of_path_witness`). -/
theorem le_nine_eighths_of_profileA3PathWitness {K : Finset (Site L)} {d : Site L → ℝ}
    {x : Site L} (W : ProfileA3PathWitness K d x) :
    euclideanSetDistance K {x} ≤ (9 / 8 : ℝ) * d x := by
  have hmax : 1 ≤ W.maxSize := by
    calc (1 : ℝ) ≤ (2 : ℝ) ^ W.maxBin := one_le_pow₀ (by norm_num)
      _ ≤ W.maxSize := W.max_size_lower
  have hparent := profileA3_parent_budget_from_separation W.maxSize W.parentSize
    W.parentDistance W.budget hmax W.parent_scale_order
    W.parent_component_separation W.parent_path_length
  exact @profileA3_collapsed_support_point_of_dyadic_path W.Index W.indexDecidableEq
    L K d x W.components W.size
    W.diameter W.bin W.maxBin W.budget W.maxSize W.packing W.component_diameter
    hparent W.budget_eq W.endpoint_bound W.collapsed_nonneg

/-- The root chosen for a component (Hilbert choice; a valid root whenever one exists). -/
def profileA3RootOf (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K C : Finset (Site L)) : ChargeDensity L :=
  Classical.epsilon fun σ => σ ∈ profileCollapseFamily F ρ j K ∧ chargeSupport σ ⊆ C ∧
    ProfileA3ComponentRootedAt C σ (boundaryAdjustedSize σ) ∧
    ∀ z ∈ C, ∀ z' ∈ C, profileA3GraphLength z z' ≤ 40 * boundaryAdjustedSize σ

section Certificate

variable {N : ℕ} {T : SelConfig L} {ρ : ChargeDensity L} {j : ℕ} {s : Finset (Site L)}

theorem profileA3RootOf_spec {F : Finset (ChargeDensity L)} {ρ : ChargeDensity L} {j : ℕ}
    {K : Finset (Site L)} (hroot : ProfileA3RootedComponents F ρ j K) {y : Site L}
    (hy : InCollapsed (profileCollapsedSets F ρ j K) y) :
    profileA3RootOf F ρ j K (collapsedComponent (profileCollapsedSets F ρ j K) y) ∈
        profileCollapseFamily F ρ j K ∧
      chargeSupport (profileA3RootOf F ρ j K (collapsedComponent (profileCollapsedSets F ρ j K) y))
        ⊆ collapsedComponent (profileCollapsedSets F ρ j K) y ∧
      ProfileA3ComponentRootedAt (collapsedComponent (profileCollapsedSets F ρ j K) y)
        (profileA3RootOf F ρ j K (collapsedComponent (profileCollapsedSets F ρ j K) y))
        (boundaryAdjustedSize
          (profileA3RootOf F ρ j K (collapsedComponent (profileCollapsedSets F ρ j K) y))) ∧
      ∀ z ∈ collapsedComponent (profileCollapsedSets F ρ j K) y,
        ∀ z' ∈ collapsedComponent (profileCollapsedSets F ρ j K) y,
          profileA3GraphLength z z' ≤ 40 * boundaryAdjustedSize
            (profileA3RootOf F ρ j K (collapsedComponent (profileCollapsedSets F ρ j K) y)) :=
  Classical.epsilon_spec (hroot y hy)

/-- **The support control from the rooted decomposition**, on one charged selected square. -/
theorem collapsedSupportControl_of_rootedComponents (hT : IsCombTerminal N T) (hρ : ρ ∈ T.F)
    (hs : s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j)
    (hq : totalCharge (chargeRestriction ρ s) ≠ 0)
    (hroot : ProfileA3RootedComponents T.F ρ j (chargeSupport (chargeRestriction ρ s))) :
    ProfileA3CollapsedSupportControl j (chargeSupport (chargeRestriction ρ s))
      (profileCollapsedPotential T.F ρ j (chargeSupport (chargeRestriction ρ s))) := by
  classical
  set K := chargeSupport (chargeRestriction ρ s) with hK
  set 𝓔 := profileCollapsedSets T.F ρ j K with h𝓔
  set d := profileCollapsedPotential T.F ρ j K with hd
  intro x hx
  -- an optimal walk
  have hlt : collapsedDistance 𝓔 K (2 ^ (j + 1)) x < 2 ^ (j + 1) := by
    have hx' : ((collapsedDistance 𝓔 K (2 ^ (j + 1)) x : ℕ) : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by
      push_cast; exact hx
    exact_mod_cast hx'
  obtain ⟨k, hk, w, hw⟩ := exists_walk_of_lt hlt
  have hdx : d x = (collapsedDistance 𝓔 K (2 ^ (j + 1)) x : ℝ) := rfl
  have hcost : pathCost 𝓔 (k :: w.support.tail) = collapsedDistance 𝓔 K (2 ^ (j + 1)) x := by
    rw [← support_eq_cons_tail w, ← collapsedCost_eq_pathCost, hw]
  have hd0 : 0 ≤ d x := by rw [hdx]; exact Nat.cast_nonneg _
  -- the component sizes
  set root : Finset (Site L) → ChargeDensity L := fun C => profileA3RootOf T.F ρ j K C with hrootdef
  set δ : Finset (Site L) → ℝ := fun C => 40 * boundaryAdjustedSize (root C) with hδdef
  have hspec : ∀ y, InCollapsed 𝓔 y → _ := fun y hy => profileA3RootOf_spec hroot hy
  have hδ : ∀ y, InCollapsed 𝓔 y → 0 ≤ δ (collapsedComponent 𝓔 y) ∧
      ∀ z ∈ collapsedComponent 𝓔 y, ∀ z' ∈ collapsedComponent 𝓔 y,
        euclideanSiteDistance z z' ≤ δ (collapsedComponent 𝓔 y) := by
    intro y hy
    obtain ⟨-, -, -, hdiam⟩ := hspec y hy
    refine ⟨by have := boundaryAdjustedSize_nonneg (root (collapsedComponent 𝓔 y)); positivity,
      fun z hz z' hz' => (euclideanSiteDistance_le_profileA3GraphLength z z').trans
        (hdiam z hz z' hz')⟩
  have hchain : List.IsChain (fun a b => l1 a b = 1) (k :: w.support.tail) := by
    rw [← support_eq_cons_tail w]; exact isChain_support w
  have hlast : (k :: w.support.tail).getLast? = some x := by
    rw [← support_eq_cons_tail w]; exact getLast?_support w
  obtain ⟨V, pos, hV1, hV2, hV3, hV4, hV5⟩ :=
    exists_collapsedPathData 𝓔 δ hδ w.support.tail k x hchain hlast
  rw [hcost] at hV2 hV3
  have hendK : euclideanSetDistance K {x} ≤ euclideanSiteDistance k x :=
    setDist_le_siteDist hk (Finset.mem_singleton_self x)
  rcases V.eq_empty_or_nonempty with hVe | hVne
  · -- no component visited
    rw [hVe, Finset.sum_empty, add_zero] at hV2
    rw [← hdx] at hV2
    linarith
  -- the data of the visited components
  have hdata : ∀ C ∈ V, ∃ y, InCollapsed 𝓔 y ∧ C = collapsedComponent 𝓔 y := by
    intro C hC
    obtain ⟨y, -, hy, hyC⟩ := hV1 C hC
    exact ⟨y, hy, hyC⟩
  choose yOf hyOf hCy using hdata
  have hmember : ∀ C ∈ V, root C ∈ profileCollapseFamily T.F ρ j K ∧ chargeSupport (root C) ⊆ C ∧
      ProfileA3ComponentRootedAt C (root C) (boundaryAdjustedSize (root C)) ∧
      ∀ z ∈ C, ∀ z' ∈ C, profileA3GraphLength z z' ≤ 40 * boundaryAdjustedSize (root C) := by
    intro C hC
    have h := hspec (yOf C hC) (hyOf C hC)
    rw [← h𝓔, ← hCy C hC] at h
    exact h
  have hmemberData : ∀ C ∈ V, _ := fun C hC =>
    profileA3_terminal_collapse_member_data N T hT ρ hρ j s hs hq (root C) (hmember C hC).1
  have hsize1 : ∀ C ∈ V, 1 ≤ boundaryAdjustedSize (root C) := fun C hC =>
    one_le_boundaryAdjustedSize (hmemberData C hC).2.2.2.1
  have hCne : ∀ C ∈ V, C.Nonempty := fun C hC => by
    have h := mem_collapsedComponent_self 𝓔 (yOf C hC)
    rw [← hCy C hC] at h
    exact ⟨_, h⟩
  have hδnn : ∀ C ∈ V, 0 ≤ δ C := fun C hC => by
    have := hsize1 C hC; simp only [hδdef]; linarith
  obtain ⟨Cs, hCs, hCsmax⟩ := V.exists_max_image (fun C => boundaryAdjustedSize (root C)) hVne
  set budget := d x + ∑ C ∈ V, δ C with hbudget
  have hposb : ∀ C ∈ V, 0 ≤ pos C ∧ pos C ≤ budget := by
    intro C hC
    obtain ⟨h1, h2⟩ := hV3 C hC
    have := hδnn C hC
    rw [← hdx] at h2
    exact ⟨h1, by linarith⟩
  have hSq := chargedSelectedSquare_of_mem hs hq
  have hKne : K.Nonempty := chargeSupport_nonempty_of_ne_zero _
    (fun h0 => hq (by simp [h0, totalCharge]))
  have hKρ : K ⊆ chargeSupport ρ := profileA3_restriction_support_subset ρ s
  have hM : (chargeCoverScale : ℝ) = 65536 := chargeCoverScale_eq
  have hα : chargeCoverExponent = (7 / 4 : ℝ) := rfl
  let W : ProfileA3PathWitness K d x :=
    { Index := Finset (Site L)
      indexDecidableEq := inferInstance
      components := V
      size := fun C => boundaryAdjustedSize (root C)
      diameter := δ
      bin := fun C => profileA3Bin (boundaryAdjustedSize (root C))
      maxBin := profileA3Bin (boundaryAdjustedSize (root Cs))
      budget := budget
      maxSize := boundaryAdjustedSize (root Cs)
      parentSize := boundaryAdjustedSize ρ
      parentDistance := euclideanSetDistance K Cs
      collapsed_nonneg := hd0
      packing :=
        { budget_nonneg := by
            have := Finset.sum_nonneg hδnn
            rw [hbudget]; linarith
          max_lower := two_pow_profileA3Bin_le (hsize1 Cs hCs)
          max_upper := hCsmax
          bin_bound := fun C hC => profileA3Bin_mono (hCsmax C hC)
          bin_lower := fun C hC => two_pow_profileA3Bin_le (hsize1 C hC)
          bin_upper := fun C hC => lt_two_pow_profileA3Bin_succ _
          position := pos
          position_bounds := hposb
          same_bin_separation := by
            intro C hC C' hC' hbin hne
            obtain ⟨u, hu, u', hu', huu'⟩ := hV5 C hC C' hC' hne
            obtain ⟨hσF, hσsupp, hσroot, -⟩ := hmember C hC
            obtain ⟨hσF', hσsupp', hσroot', -⟩ := hmember C' hC'
            have hdisj : Disjoint C C' := by
              rw [hCy C hC, hCy C' hC']
              apply disjoint_collapsedComponent
              rw [← hCy C hC, ← hCy C' hC']
              exact hne
            have hσne : root C ≠ root C' := by
              intro heq
              obtain ⟨a, ha⟩ := chargeSupport_nonempty_of_ne_zero _ (hmemberData C hC).2.2.2.1
              exact Finset.disjoint_left.mp hdisj (hσsupp ha) (hσsupp' (heq ▸ ha))
            have hsep := hT.geometry.separated (root C) (hmemberData C hC).1 (root C')
              (hmemberData C' hC').1 hσne
            rw [hM, hα] at hsep
            have hcomp := profileA3_distinct_components_separation (65536 : ℝ) (7 / 4 : ℝ)
              (boundaryAdjustedSize (root C)) (boundaryAdjustedSize (root C')) (root C)
              (root C') C C' hsep hσroot hσroot' (hCne C hC) (hCne C' hC')
            have hdist : euclideanSetDistance C C' ≤ euclideanSiteDistance u u' :=
              setDist_le_siteDist hu hu'
            have hnum := sameBin_separation_le (D := boundaryAdjustedSize (root C))
              (D' := boundaryAdjustedSize (root C')) (profileA3Bin (boundaryAdjustedSize (root C)))
              (two_pow_profileA3Bin_le (hsize1 C hC))
              (by rw [hbin]; exact two_pow_profileA3Bin_le (hsize1 C' hC'))
              (lt_two_pow_profileA3Bin_succ _)
              (by rw [hbin]; exact lt_two_pow_profileA3Bin_succ _)
            linarith }
      max_size_lower := two_pow_profileA3Bin_le (hsize1 Cs hCs)
      component_diameter := fun C _ => le_rfl
      parent_scale_order := (hmemberData Cs hCs).2.2.2.2.1.le
      parent_component_separation := by
        obtain ⟨hσF, -, hσroot, -⟩ := hmember Cs hCs
        have hsep := hT.geometry.separated ρ hρ (root Cs) (hmemberData Cs hCs).1
          (hmemberData Cs hCs).2.1.symm
        rw [hM, hα] at hsep
        exact profileA3_parent_component_separation (65536 : ℝ) (7 / 4 : ℝ)
          (boundaryAdjustedSize ρ) (boundaryAdjustedSize (root Cs)) ρ (root Cs) K Cs hsep
          hσroot hKρ hKne (hCne Cs hCs)
      parent_path_length := by
        obtain ⟨u, hu, hku⟩ := hV4 Cs hCs
        exact (setDist_le_siteDist hk hu).trans (hku.trans (hposb Cs hCs).2)
      budget_eq := rfl
      endpoint_bound := by
        rw [← hdx] at hV2
        exact hendK.trans hV2 }
  exact le_nine_eighths_of_profileA3PathWitness W

end Certificate

/-! ## Theorem C from the decomposition -/

/-- **The large-scale support control from the rooted decomposition.** -/
theorem terminalCollapsedSupportControlLarge_of_rootedComponents
    (h : TerminalProfileA3RootedComponentsLarge) : TerminalCollapsedSupportControlLarge :=
  fun L N T hT ρ hρ j hj s hs hq =>
    collapsedSupportControl_of_rootedComponents hT hρ hs hq (h L N T hT ρ hρ j hj s hs hq)

/-- **FS81 Theorem C from the rooted component decomposition.** -/
theorem theoremC_of_rootedComponents (h : TerminalProfileA3RootedComponentsLarge) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_collapsedSupportControl (terminalCollapsedSupportControl_of_large
    (terminalCollapsedSupportControlLarge_of_rootedComponents h))

/-- **The Kosterlitz–Thouless transition from the rooted component decomposition.** -/
theorem exists_transition_of_rootedComponents (h : TerminalProfileA3RootedComponentsLarge) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_collapsedSupportControl (terminalCollapsedSupportControl_of_large
    (terminalCollapsedSupportControlLarge_of_rootedComponents h))

/-- **FS81 Theorem C from the terminal decomposition's unique-maximum decomposition.** -/
theorem theoremC_of_uniqueMaxDecomposition (h : TerminalProfileA3UniqueMaxDecompositionLarge) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_rootedComponents (terminalRootedComponentsLarge_of_decomposition h)

/-- **The Kosterlitz–Thouless transition from the terminal decomposition's unique-maximum decomposition.** -/
theorem exists_transition_of_uniqueMaxDecomposition
    (h : TerminalProfileA3UniqueMaxDecompositionLarge) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_rootedComponents (terminalRootedComponentsLarge_of_decomposition h)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
