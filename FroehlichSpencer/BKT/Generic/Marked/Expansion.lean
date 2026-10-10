/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Gap
public import FroehlichSpencer.BKT.Charges.Theorem22
public import FroehlichSpencer.BKT.Charges.ScaleGeometry
public import FroehlichSpencer.BKT.Charges.ScaleAtoms
public import FroehlichSpencer.BKT.Charges.PatchIsolation
public import FroehlichSpencer.BKT.Charges.L41Source
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import FroehlichSpencer.BKT.SpinWaves.LatticePacking
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
import Mathlib.Tactic

/-!
# The marked-charge expansion on KP's charge layer

Documented variant of FS81 (2.29): the marked
terms are regrouped by the **component of the mark** rather than presented as convex two-term
factors.

**Construction.** Take KP's convex expansion `∏_j λ_j = ∑_i c_i ∏_{ϱ ∈ N_i} (1 + K_i(ϱ) cos⟨ψ,ϱ⟩)`.

A member `ϱ` is *adjacent* to a set `C` of members (`MarkAdjacent`) when it violates KP's
separation from the composite support `supp ϱ₀ ∪ ⋃ C`, at the scale `min(d(ϱ), d(C))` (both
neutral) or `max(…)` (something charged).

Adjacency is monotone (`markAdjacent_monotone`), so the
subset expansion of `∏(1 + u)` regroups by the mark's component (`prod_one_add_eq_sum_clusters`,
a general lemma on `component`/`clusters`/`remainder`):

`cos(ξ⟨ψ,ϱ₀⟩) ∏_{N} (1 + K cos) = ∑_{C cluster} ∑_{T ⊆ C} 2^{−|C|} (∏_C K) cos⟨ψ, ξϱ₀ + ϱ^𝒩⟩ ∏_{rem(C)} (1 + K cos)`

with the satellite `ϱ^𝒩 = ∑_T m − ∑_{C∖T} m` (`markedExpansion`, `cos_mul_prod_eq_sum_clusters`).

**Results.**
* `MarkedT22Step`, `markedT22Step_of_t22Step`, `markedT22Statement`: the marked T2.2 on every
  square domain, with KP's branch data `(N, c, K)` and properties (a)–(d) unchanged and the
  marked identity for **every** mark `ϱ₀ ≠ 0` and **every** `ξ` (the branch data are
  `ξ`-independent, as Corollary 2.4 needs; `markedT22_zero_mark` is CORE.s7).
* FS81's local identities (2.25) and (2.26): `cos_mul_one_add_mul_cos`, `marked_pair_identity`.
* The remainder inherits (a)–(c) (`markedRemainder_t22`) and is separated from the composite in
  both forms of KP T2.2(b) (`markedRemainder_separation_min`,
  `markedRemainder_separation_of_charged`).
* `abs_clusterWeight_le`: the composite's activity in lineage form; **`sum_chargeCoverCost_le`**
  (`∑_{m ∈ C} A(m) ≤ 289 A(X)`, a packing count per scale, `card_members_meeting_square_le`) turns
  it into **FS81 (2.30)** in KP's functional, `abs_clusterWeight_le_coverCost`:
  `|2^{−|C|} ∏_C K| ≤ 2^{−|C|} e^{289 D₂ A(X)} ∏_{m ∈ C} ∏_{j ∈ supp m} e^{m(j)²} |λ̂_j|`, with
  `X = s(ϱ₀, ϱ^𝒩)` measured through the integer proxy `supportProxy X`.
* **`markedComposite_charged_split`**: for a neutral mark with gapped proper restrictions, every
  KP-separated split of a neutral composite carries charge `≥ η` (T2.3(c) for these composites);
  **`dipoleComposite_charged_split`**: the Coulomb-B dipole, `η = min(ξ, 1 − ξ)`.

The proof uses
  `not_two_cut` (two members cannot straddle a separated split) and `cluster_not_separated`
  (connectivity of a cluster).

FS81's general Condition (2.28) is not used ; for non-neutral marks the
full-support case would reappear and is not treated.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

/-! ### The component of the mark under a monotone adjacency -/

section Component

open Classical

variable {ι : Type*} [DecidableEq ι] (adj : ι → Finset ι → Prop)

/-- One growth step inside `T`: add the members of `T` adjacent to the current cluster `C`. -/
def growStep (T C : Finset ι) : Finset ι :=
  C ∪ T.filter fun m => adj m C

/-- The `k`-th growth stage of the mark's component inside `T`, starting from the bare mark. -/
def growIter (T : Finset ι) (k : ℕ) : Finset ι :=
  (growStep adj T)^[k] ∅

/-- The component of the mark inside `T`: the members reachable from the mark by successive
adjacencies (the growth stabilizes after at most `|T|` steps, `growStep_component`). -/
def component (T : Finset ι) : Finset ι :=
  growIter adj T T.card

/-- Adjacency to a cluster is monotone in the cluster. -/
def AdjMonotone : Prop :=
  ∀ m C C', C ⊆ C' → adj m C → adj m C'

/-- The clusters of `N`: subsets equal to their own component. -/
def clusters (N : Finset ι) : Finset (Finset ι) :=
  N.powerset.filter fun C => component adj C = C

/-- The members of `N` outside `C` that are not adjacent to `C`. -/
def remainder (N C : Finset ι) : Finset ι :=
  (N \ C).filter fun m => ¬ adj m C

variable {adj}

theorem growIter_zero (T : Finset ι) : growIter adj T 0 = ∅ := rfl

theorem growIter_succ (T : Finset ι) (k : ℕ) :
    growIter adj T (k + 1) = growStep adj T (growIter adj T k) :=
  Function.iterate_succ_apply' _ _ _

theorem growIter_subset_succ (T : Finset ι) (k : ℕ) :
    growIter adj T k ⊆ growIter adj T (k + 1) := by
  rw [growIter_succ]
  exact Finset.subset_union_left

theorem growIter_mono (T : Finset ι) {k k' : ℕ} (h : k ≤ k') :
    growIter adj T k ⊆ growIter adj T k' := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (growIter_subset_succ T _)

theorem growIter_subset (T : Finset ι) (k : ℕ) : growIter adj T k ⊆ T := by
  induction k with
  | zero => simp [growIter_zero]
  | succ k ih =>
    rw [growIter_succ]
    exact Finset.union_subset ih (Finset.filter_subset _ _)

theorem growIter_eq_of_succ_eq (T : Finset ι) {k : ℕ}
    (h : growIter adj T (k + 1) = growIter adj T k) :
    ∀ k', k ≤ k' → growIter adj T k' = growIter adj T k := by
  intro k' hk'
  induction hk' with
  | refl => rfl
  | step _ ih => rw [growIter_succ, ih, ← growIter_succ, h]

theorem le_card_growIter (T : Finset ι) (k : ℕ)
    (h : ∀ j < k, growIter adj T j ≠ growIter adj T (j + 1)) :
    k ≤ (growIter adj T k).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih fun j hj => h j (by omega)
    have h2 : growIter adj T k ⊂ growIter adj T (k + 1) :=
      Finset.ssubset_iff_subset_ne.2 ⟨growIter_subset_succ T k, h k (by omega)⟩
    have := Finset.card_lt_card h2
    omega

/-- The component is a fixed point of the growth step. -/
theorem growStep_component (T : Finset ι) :
    growStep adj T (component adj T) = component adj T := by
  have hex : ∃ j ≤ T.card, growIter adj T (j + 1) = growIter adj T j := by
    by_contra hall
    push Not at hall
    have h1 := le_card_growIter (adj := adj) T (T.card + 1) fun j hj =>
      (hall j (by omega)).symm
    have h2 := Finset.card_le_card (growIter_subset (adj := adj) T (T.card + 1))
    omega
  obtain ⟨j, hj, hjeq⟩ := hex
  have h1 := growIter_eq_of_succ_eq T hjeq T.card hj
  have h2 := growIter_eq_of_succ_eq T hjeq (T.card + 1) (by omega)
  unfold component
  rw [← growIter_succ, h2, h1]

theorem component_subset (T : Finset ι) : component adj T ⊆ T :=
  growIter_subset T _

theorem not_adj_of_not_mem_component {T : Finset ι} {m : ι} (hm : m ∈ T)
    (hmc : m ∉ component adj T) : ¬ adj m (component adj T) := by
  intro hadj
  apply hmc
  rw [← growStep_component]
  exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hm, hadj⟩)

theorem component_subset_of_closed (hmono : AdjMonotone adj) {T C' : Finset ι}
    (hC' : ∀ m ∈ T, adj m C' → m ∈ C') : component adj T ⊆ C' := by
  have : ∀ k, growIter adj T k ⊆ C' := by
    intro k
    induction k with
    | zero => simp [growIter_zero]
    | succ k ih =>
      rw [growIter_succ]
      refine Finset.union_subset ih fun m hm => ?_
      obtain ⟨hmT, hadj⟩ := Finset.mem_filter.1 hm
      exact hC' m hmT (hmono m _ _ ih hadj)
  exact this _

theorem component_mono (hmono : AdjMonotone adj) {T T' : Finset ι} (h : T ⊆ T') :
    component adj T ⊆ component adj T' :=
  component_subset_of_closed hmono fun m hm hadj => by
    by_contra hmc
    exact not_adj_of_not_mem_component (h hm) hmc hadj

/-- **Characterization of the component**: `component T = C` iff `C` is a cluster contained in
`T` and no member of `T ∖ C` is adjacent to `C`. -/
theorem component_eq_iff (hmono : AdjMonotone adj) {T C : Finset ι} :
    component adj T = C ↔ component adj C = C ∧ C ⊆ T ∧ ∀ m ∈ T \ C, ¬ adj m C := by
  constructor
  · rintro rfl
    refine ⟨?_, component_subset T, fun m hm => ?_⟩
    · refine le_antisymm (component_subset _) ?_
      refine component_subset_of_closed hmono fun m hmT hadj => ?_
      by_contra hmc
      have hmC : m ∈ component adj T := by
        by_contra hmT'
        exact not_adj_of_not_mem_component hmT hmT'
          (hmono m _ _ (component_subset _) hadj)
      exact not_adj_of_not_mem_component hmC hmc hadj
    · obtain ⟨hmT, hmC⟩ := Finset.mem_sdiff.1 hm
      exact not_adj_of_not_mem_component hmT hmC
  · rintro ⟨hC, hCT, hrest⟩
    refine le_antisymm ?_ ?_
    · refine component_subset_of_closed hmono fun m hmT hadj => ?_
      by_contra hmC
      exact hrest m (Finset.mem_sdiff.2 ⟨hmT, hmC⟩) hadj
    · calc C = component adj C := hC.symm
        _ ⊆ component adj T := component_mono hmono hCT

theorem component_component (hmono : AdjMonotone adj) (T : Finset ι) :
    component adj (component adj T) = component adj T :=
  ((component_eq_iff hmono).1 rfl).1

theorem mem_clusters {N C : Finset ι} : C ∈ clusters adj N ↔ C ⊆ N ∧ component adj C = C := by
  unfold clusters
  rw [Finset.mem_filter, Finset.mem_powerset]

theorem remainder_subset (N C : Finset ι) : remainder adj N C ⊆ N :=
  (Finset.filter_subset _ _).trans Finset.sdiff_subset

theorem disjoint_remainder (N C : Finset ι) : Disjoint C (remainder adj N C) :=
  Finset.disjoint_of_subset_right (Finset.filter_subset _ _) Finset.disjoint_sdiff

theorem not_adj_of_mem_remainder {N C : Finset ι} {m : ι} (hm : m ∈ remainder adj N C) :
    ¬ adj m C :=
  (Finset.mem_filter.1 hm).2

/-- Every member of a cluster entered at some growth stage, adjacent to the earlier stage. -/
theorem exists_stage_of_mem_component {T : Finset ι} {m : ι} (hm : m ∈ component adj T) :
    ∃ k, m ∉ growIter adj T k ∧ m ∈ growIter adj T (k + 1) ∧ adj m (growIter adj T k) := by
  classical
  have hex : ∃ k, m ∈ growIter adj T k := ⟨_, hm⟩
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, growIter_zero] at hspec
    exact absurd hspec (Finset.notMem_empty m)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmem : m ∈ growIter adj T (j + 1) := by
    have : Nat.find hex = j + 1 := hj
    rw [← this]; exact hspec
  have hnot : m ∉ growIter adj T j := Nat.find_min hex (by omega)
  refine ⟨j, hnot, hmem, ?_⟩
  rw [growIter_succ] at hmem
  rcases Finset.mem_union.1 hmem with h | h
  · exact absurd h hnot
  · exact (Finset.mem_filter.1 h).2

/-! ### The cluster regrouping identity -/

/-- **Regrouping by the mark's component.** For a monotone adjacency, the subset expansion of
`∏_{m ∈ N} (1 + u_m)` regroups by the component of the mark: each cluster `C` contributes
`∏_{m ∈ C} u_m` times the full product over the members not adjacent to `C`. -/
theorem prod_one_add_eq_sum_clusters {R : Type*} [CommRing R] (hmono : AdjMonotone adj)
    (N : Finset ι) (u : ι → R) :
    ∏ m ∈ N, (1 + u m) =
      ∑ C ∈ clusters adj N, (∏ m ∈ C, u m) * ∏ m ∈ remainder adj N C, (1 + u m) := by
  rw [Finset.prod_one_add]
  have hmaps : ∀ T ∈ N.powerset, component adj T ∈ clusters adj N := fun T hT =>
    mem_clusters.2 ⟨(component_subset T).trans (Finset.mem_powerset.1 hT),
      component_component hmono T⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨hCN, hCC⟩ := mem_clusters.1 hC
  rw [Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_nbij' (fun T => T \ C) (fun R => C ∪ R) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    obtain ⟨hTN, hTC⟩ := Finset.mem_filter.1 hT
    obtain ⟨-, -, hrest⟩ := (component_eq_iff hmono).1 hTC
    refine Finset.mem_powerset.2 fun m hm => ?_
    obtain ⟨hmT, hmC⟩ := Finset.mem_sdiff.1 hm
    exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_powerset.1 hTN hmT, hmC⟩,
      hrest m hm⟩
  · intro R hR
    have hRrem := Finset.mem_powerset.1 hR
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2
      (Finset.union_subset hCN (hRrem.trans (remainder_subset N C))), ?_⟩
    refine (component_eq_iff hmono).2 ⟨hCC, Finset.subset_union_left, fun m hm => ?_⟩
    obtain ⟨hmCR, hmC⟩ := Finset.mem_sdiff.1 hm
    rcases Finset.mem_union.1 hmCR with h | h
    · exact absurd h hmC
    · exact not_adj_of_mem_remainder (hRrem h)
  · intro T hT
    obtain ⟨hTN, hTC⟩ := Finset.mem_filter.1 hT
    obtain ⟨-, hCT, -⟩ := (component_eq_iff hmono).1 hTC
    exact Finset.union_sdiff_of_subset hCT
  · intro R hR
    have hRrem := Finset.mem_powerset.1 hR
    have hdisj : Disjoint C R :=
      Finset.disjoint_of_subset_right hRrem (disjoint_remainder N C)
    exact Finset.union_sdiff_cancel_left hdisj
  · intro T hT
    obtain ⟨hTN, hTC⟩ := Finset.mem_filter.1 hT
    obtain ⟨-, hCT, -⟩ := (component_eq_iff hmono).1 hTC
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hCT]

end Component

/-! ### Marked cosine identities -/

section Cosine

variable {ι : Type*} [DecidableEq ι]

/-- FS81 (2.25): `cos a (1 + K cos θ) = ½(cos a + K cos(a + θ)) + ½(cos a + K cos(a − θ))`. -/
theorem cos_mul_one_add_mul_cos (a θ K : ℝ) :
    Real.cos a * (1 + K * Real.cos θ) =
      1 / 2 * (Real.cos a + K * Real.cos (a + θ)) +
        1 / 2 * (Real.cos a + K * Real.cos (a - θ)) := by
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- FS81 (2.26), with `ϱ₁ = ξ ϱ₀ + ϱ₁'` written as the phase `a + θ₁'`. -/
theorem marked_pair_identity (a θ₁' θ₂ K₁ K₂ : ℝ) :
    (Real.cos a + K₁ * Real.cos (a + θ₁')) * (1 + K₂ * Real.cos θ₂) =
      1 / 3 * (Real.cos a + 3 * K₁ * Real.cos (a + θ₁')) +
      1 / 6 * (Real.cos a + 3 * K₂ * Real.cos (a + θ₂)) +
      1 / 6 * (Real.cos a + 3 * K₂ * Real.cos (a - θ₂)) +
      1 / 6 * (Real.cos a + 3 * K₁ * K₂ * Real.cos (a + θ₁' + θ₂)) +
      1 / 6 * (Real.cos a + 3 * K₁ * K₂ * Real.cos (a + θ₁' - θ₂)) := by
  simp only [Real.cos_add, Real.cos_sub]
  ring

/-- Product-to-sum with a phase: `cos a ∏_{m ∈ C} cos θ_m = 2^{−|C|} ∑_{T ⊆ C} cos(a + θ(T) − θ(C ∖ T))`. -/
theorem cos_mul_prod_cos (a : ℝ) (C : Finset ι) (θ : ι → ℝ) :
    Real.cos a * ∏ m ∈ C, Real.cos (θ m) =
      (1 / 2) ^ C.card * ∑ T ∈ C.powerset,
        Real.cos (a + ∑ m ∈ T, θ m - ∑ m ∈ C \ T, θ m) := by
  induction C using Finset.induction_on generalizing a with
  | empty => simp
  | @insert b C hb ih =>
    rw [Finset.prod_insert hb, Finset.card_insert_of_notMem hb, Finset.sum_powerset_insert hb]
    have hsplit : Real.cos a * (Real.cos (θ b) * ∏ m ∈ C, Real.cos (θ m)) =
        1 / 2 * (Real.cos (a + θ b) * ∏ m ∈ C, Real.cos (θ m)) +
          1 / 2 * (Real.cos (a - θ b) * ∏ m ∈ C, Real.cos (θ m)) := by
      rw [Real.cos_add, Real.cos_sub]
      ring
    rw [hsplit, ih (a + θ b), ih (a - θ b)]
    have h1 : ∀ T ∈ C.powerset, Real.cos (a - θ b + ∑ m ∈ T, θ m - ∑ m ∈ C \ T, θ m) =
        Real.cos (a + ∑ m ∈ T, θ m - ∑ m ∈ insert b C \ T, θ m) := by
      intro T hT
      have hbT : b ∉ T := fun h => hb (Finset.mem_powerset.1 hT h)
      rw [Finset.insert_sdiff_of_notMem _ hbT, Finset.sum_insert
        (fun h => hb (Finset.mem_sdiff.1 h).1)]
      congr 1
      ring
    have h2 : ∀ T ∈ C.powerset, Real.cos (a + θ b + ∑ m ∈ T, θ m - ∑ m ∈ C \ T, θ m) =
        Real.cos (a + ∑ m ∈ insert b T, θ m - ∑ m ∈ insert b C \ insert b T, θ m) := by
      intro T hT
      have hbT : b ∉ T := fun h => hb (Finset.mem_powerset.1 hT h)
      rw [Finset.sum_insert hbT, Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hb]
      congr 1
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    ring

/-- **The marked expansion of an ensemble product** (FS81 (2.24)–(2.29), regrouped by the mark's
component): for a monotone adjacency,
`cos a ∏_{m ∈ N} (1 + K_m cos θ_m) = ∑_{C cluster} ∑_{T ⊆ C} 2^{−|C|} (∏_C K) cos(a + θ(T) − θ(C ∖ T)) ∏_{m ∈ rem(C)} (1 + K_m cos θ_m)`. -/
theorem cos_mul_prod_eq_sum_clusters {adj : ι → Finset ι → Prop} (hmono : AdjMonotone adj)
    (N : Finset ι) (K θ : ι → ℝ) (a : ℝ) :
    Real.cos a * ∏ m ∈ N, (1 + K m * Real.cos (θ m)) =
      ∑ C ∈ clusters adj N, ∑ T ∈ C.powerset,
        ((1 / 2) ^ C.card * ∏ m ∈ C, K m) *
          Real.cos (a + ∑ m ∈ T, θ m - ∑ m ∈ C \ T, θ m) *
          ∏ m ∈ remainder adj N C, (1 + K m * Real.cos (θ m)) := by
  rw [prod_one_add_eq_sum_clusters hmono N (fun m => K m * Real.cos (θ m)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hprod : ∏ m ∈ C, K m * Real.cos (θ m) = (∏ m ∈ C, K m) * ∏ m ∈ C, Real.cos (θ m) :=
    Finset.prod_mul_distrib
  rw [hprod, show Real.cos a * ((∏ m ∈ C, K m) * (∏ m ∈ C, Real.cos (θ m)) *
      ∏ m ∈ remainder adj N C, (1 + K m * Real.cos (θ m))) =
      (∏ m ∈ C, K m) * (Real.cos a * ∏ m ∈ C, Real.cos (θ m)) *
        ∏ m ∈ remainder adj N C, (1 + K m * Real.cos (θ m)) by ring,
    cos_mul_prod_cos, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

end Cosine

/-! ### The marked expansion on KP's square domains -/

section KP

open Classical

variable (boundary : SquareBoundary) (L : ℕ)

/-- The support of the marked composite with cluster `C`: `supp ϱ₀ ∪ ⋃_{m ∈ C} supp m`. -/
def markedSupport (ϱ₀ : ChargeDensity L) (C : Finset (ChargeDensity L)) :
    Finset (Fin L × Fin L) :=
  chargeSupport ϱ₀ ∪ C.biUnion chargeSupport

/-- The adjacency scale of a member `ϱ` against the marked cluster `C`: the smaller of `d(ϱ)` and
the cluster diameter when `ϱ` and `C` are neutral, the larger otherwise (the two clauses of
KP T2.2(b)). -/
def markScale (ϱ₀ ϱ : ChargeDensity L) (C : Finset (ChargeDensity L)) : ℝ :=
  if (∑ j, ϱ j ≠ 0) ∨ ∃ m ∈ C, ∑ j, m j ≠ 0 then
    ((max (chargeDiameter boundary L ϱ) (squareDiameter boundary L (markedSupport L ϱ₀ C)) : ℕ) :
      ℝ)
  else
    ((min (chargeDiameter boundary L ϱ) (squareDiameter boundary L (markedSupport L ϱ₀ C)) : ℕ) :
      ℝ)

/-- A member `ϱ` is **adjacent** to the marked cluster `C` when it violates KP's separation from
the cluster support: `dist(ϱ, supp ϱ₀ ∪ ⋃ C) < M · scale^α`. -/
def MarkAdjacent (ϱ₀ ϱ : ChargeDensity L) (C : Finset (ChargeDensity L)) : Prop :=
  (squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C) : ℝ) <
    (chargeCoverScale : ℝ) * markScale boundary L ϱ₀ ϱ C ^ chargeCoverExponent

/-- The marked clusters of an ensemble: the sets of members that the mark reaches by successive
adjacencies. -/
def markedClusters (ϱ₀ : ChargeDensity L) (N : Finset (ChargeDensity L)) :
    Finset (Finset (ChargeDensity L)) :=
  clusters (MarkAdjacent boundary L ϱ₀) N

/-- The ensemble left beside the cluster `C`: the members of `N ∖ C` not adjacent to `C`. -/
def markedRemainder (ϱ₀ : ChargeDensity L) (N C : Finset (ChargeDensity L)) :
    Finset (ChargeDensity L) :=
  remainder (MarkAdjacent boundary L ϱ₀) N C

/-- The satellite `ϱ^𝒩 = ∑_{m ∈ T} m − ∑_{m ∈ C ∖ T} m` of the orientation `T ⊆ C`. -/
def satellite (C T : Finset (ChargeDensity L)) : ChargeDensity L :=
  fun j => ∑ m ∈ T, m j - ∑ m ∈ C \ T, m j

variable {boundary L}

theorem mem_chargeSupport' {ϱ : ChargeDensity L} {j : Fin L × Fin L} :
    j ∈ chargeSupport ϱ ↔ ϱ j ≠ 0 := by
  unfold chargeSupport
  simp

theorem chargeSupport_nonempty' {ϱ : ChargeDensity L} (h : ϱ ≠ 0) :
    (chargeSupport ϱ).Nonempty := by
  by_contra hne
  apply h
  funext j
  by_contra hj
  exact hne ⟨j, mem_chargeSupport'.2 hj⟩

theorem markedSupport_mono (ϱ₀ : ChargeDensity L) {C C' : Finset (ChargeDensity L)}
    (h : C ⊆ C') : markedSupport L ϱ₀ C ⊆ markedSupport L ϱ₀ C' :=
  Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.biUnion_subset_biUnion_of_subset_left _ h)

theorem chargeSupport_subset_markedSupport (ϱ₀ : ChargeDensity L)
    (C : Finset (ChargeDensity L)) : chargeSupport ϱ₀ ⊆ markedSupport L ϱ₀ C :=
  Finset.subset_union_left

theorem chargeSupport_subset_markedSupport_of_mem {ϱ₀ m : ChargeDensity L}
    {C : Finset (ChargeDensity L)} (hm : m ∈ C) : chargeSupport m ⊆ markedSupport L ϱ₀ C :=
  (Finset.subset_biUnion_of_mem chargeSupport hm).trans Finset.subset_union_right

theorem mem_markedSupport {ϱ₀ : ChargeDensity L} {C : Finset (ChargeDensity L)}
    {j : Fin L × Fin L} :
    j ∈ markedSupport L ϱ₀ C ↔ ϱ₀ j ≠ 0 ∨ ∃ m ∈ C, m j ≠ 0 := by
  unfold markedSupport
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_chargeSupport']

theorem markScale_nonneg (ϱ₀ ϱ : ChargeDensity L) (C : Finset (ChargeDensity L)) :
    0 ≤ markScale boundary L ϱ₀ ϱ C := by
  unfold markScale
  split_ifs <;> positivity

theorem markScale_mono (ϱ₀ ϱ : ChargeDensity L) {C C' : Finset (ChargeDensity L)}
    (h : C ⊆ C') : markScale boundary L ϱ₀ ϱ C ≤ markScale boundary L ϱ₀ ϱ C' := by
  have hd := squareDiameter_mono boundary L (markedSupport_mono (L := L) ϱ₀ h)
  unfold markScale
  split_ifs with h1 h2 h2
  · exact_mod_cast max_le_max le_rfl hd
  · exfalso
    rcases h1 with h1 | ⟨m, hm, hm'⟩
    · exact h2 (Or.inl h1)
    · exact h2 (Or.inr ⟨m, h hm, hm'⟩)
  · exact_mod_cast (min_le_left _ _).trans (le_max_left _ _)
  · exact_mod_cast min_le_min le_rfl hd

theorem markScale_of_neutral {ϱ₀ ϱ : ChargeDensity L} {C : Finset (ChargeDensity L)}
    (hϱ : ∑ j, ϱ j = 0) (hC : ∀ m ∈ C, ∑ j, m j = 0) :
    markScale boundary L ϱ₀ ϱ C =
      ((min (chargeDiameter boundary L ϱ)
        (squareDiameter boundary L (markedSupport L ϱ₀ C)) : ℕ) : ℝ) := by
  have hneg : ¬ ((∑ j, ϱ j ≠ 0) ∨ ∃ m ∈ C, ∑ j, m j ≠ 0) := by
    push Not
    exact ⟨hϱ, hC⟩
  unfold markScale
  simp only [hneg, ↓reduceIte]

private theorem squareDistance_eq_zero_of_not_nonempty {s t : Finset (Fin L × Fin L)}
    (hs : ¬ s.Nonempty) : squareDistance boundary L s t = 0 := by
  have : ¬ (s.product t).Nonempty := fun ⟨p, hp⟩ => hs ⟨p.1, (Finset.mem_product.1 hp).1⟩
  unfold squareDistance
  rw [dite_eq_right this]

/-- Adjacency to the marked cluster is monotone in the cluster. -/
theorem markAdjacent_monotone {ϱ₀ : ChargeDensity L} (hϱ₀ : ϱ₀ ≠ 0) :
    AdjMonotone (MarkAdjacent boundary L ϱ₀) := by
  intro ϱ C C' h hadj
  unfold MarkAdjacent at hadj ⊢
  have hXne : (markedSupport L ϱ₀ C).Nonempty :=
    (chargeSupport_nonempty' hϱ₀).mono (chargeSupport_subset_markedSupport ϱ₀ C)
  have hdist : squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C') ≤
      squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C) := by
    by_cases hϱ : (chargeSupport ϱ).Nonempty
    · exact squareDistance_le_of_subset boundary L hϱ hXne (Finset.Subset.refl _)
        (markedSupport_mono ϱ₀ h)
    · rw [squareDistance_eq_zero_of_not_nonempty hϱ]
      exact Nat.zero_le _
  have hα : (0 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  calc (squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C') : ℝ)
      ≤ squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C) := by
        exact_mod_cast hdist
    _ < _ := hadj
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (markScale_nonneg ϱ₀ ϱ C) (markScale_mono ϱ₀ ϱ h) hα)
        (by norm_num [chargeCoverScale])

theorem sum_mul_satellite (ψ : Fin L × Fin L → ℝ) (C T : Finset (ChargeDensity L)) :
    ∑ j, ψ j * (satellite L C T j : ℝ) =
      ∑ m ∈ T, ∑ j, ψ j * (m j : ℝ) - ∑ m ∈ C \ T, ∑ j, ψ j * (m j : ℝ) := by
  unfold satellite
  push_cast
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := C \ T)]

theorem sum_mul_markedDensity_satellite (ψ : Fin L × Fin L → ℝ) (ξ : ℝ) (ϱ₀ : ChargeDensity L)
    (C T : Finset (ChargeDensity L)) :
    ∑ j, ψ j * markedDensity ξ ϱ₀ (satellite L C T) j =
      ξ * ∑ j, ψ j * (ϱ₀ j : ℝ) +
        (∑ m ∈ T, ∑ j, ψ j * (m j : ℝ) - ∑ m ∈ C \ T, ∑ j, ψ j * (m j : ℝ)) := by
  rw [← sum_mul_satellite]
  unfold markedDensity
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The marked expansion of one ensemble** (FS81 (2.29), regrouped by the mark's component):
`cos(ξ⟨ψ, ϱ₀⟩) ∏_{ϱ ∈ N} (1 + K(ϱ) cos⟨ψ, ϱ⟩)` is the sum over marked clusters `C` and
orientations `T ⊆ C` of `2^{−|C|} ∏_C K` times the character of the real composite
`ξ ϱ₀ + ϱ^𝒩` times the full product over the remainder. Nothing on the right depends on `ξ`
except the composite. -/
theorem markedExpansion {ϱ₀ : ChargeDensity L} (hϱ₀ : ϱ₀ ≠ 0) (N : Finset (ChargeDensity L))
    (K : ChargeDensity L → ℝ) (ξ : ℝ) (ψ : Fin L × Fin L → ℝ) :
    Real.cos (ξ * ∑ j, ψ j * (ϱ₀ j : ℝ)) *
        ∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, ψ j * (ϱ j : ℝ))) =
      ∑ C ∈ markedClusters boundary L ϱ₀ N, ∑ T ∈ C.powerset,
        ((1 / 2) ^ C.card * ∏ m ∈ C, K m) *
          Real.cos (∑ j, ψ j * markedDensity ξ ϱ₀ (satellite L C T) j) *
          ∏ ϱ ∈ markedRemainder boundary L ϱ₀ N C,
            (1 + K ϱ * Real.cos (∑ j, ψ j * (ϱ j : ℝ))) := by
  rw [cos_mul_prod_eq_sum_clusters (markAdjacent_monotone hϱ₀) N K
    (fun ϱ => ∑ j, ψ j * (ϱ j : ℝ))]
  unfold markedClusters markedRemainder
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun T _ => ?_
  rw [sum_mul_markedDensity_satellite]
  ring_nf

/-! #### The marked T2.2 step -/

/-- **The marked analogue of KP Theorem 2.2** (FS81 Theorem 2.3, in the cluster-regrouped form)
on one square domain, with constant `D₂`. For every family of real, even, normalized
trigonometric site weights there is **one** convex expansion `(N, c, K)` with KP's properties
(a)–(d) such that, for **every** integer mark `ϱ₀ ≠ 0`, every `ξ ∈ ℝ` and every `ψ`,
`cos(ξ⟨ψ, ϱ₀⟩) ∏_j λ_j(ψ_j)` expands over the marked clusters of each `N i`. The branch data
`(n, N, c, K)` are independent of `ξ` and of the mark; the clusters and satellites depend only on
supports (FS81's "coefficients independent of `ξ`", needed for Corollary 2.4). -/
def MarkedT22Step (boundary : SquareBoundary) (L : ℕ) (D₂ : ℝ) : Prop :=
  ∀ (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ)
    (lamHat : Fin L × Fin L → ℕ → ℝ),
    (∀ j, 0 < Nq j) → (∀ j q, Nq j < q → lamHat j q = 0) →
    (∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ)) →
    ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
      (K : Fin n → (Fin L × Fin L → ℤ) → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
      (∀ ψ : Fin L × Fin L → ℝ,
        ∏ j, lam j (ψ j) = ∑ i, c i * ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, ψ j * ϱ j))) ∧
      (∀ i, AtMostOneNonNeutral (N i) ∧ IsScaleSeparated boundary L (N i) ∧
        NeutralSplitsAreCharged boundary L (N i) ∧
        ∀ ϱ ∈ N i, ∑ j, ϱ j = 0 →
          |K i ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
            ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|) ∧
      ∀ ϱ₀ : ChargeDensity L, ϱ₀ ≠ 0 → ∀ (ξ : ℝ) (ψ : Fin L × Fin L → ℝ),
        Real.cos (ξ * ∑ j, ψ j * (ϱ₀ j : ℝ)) * ∏ j, lam j (ψ j) =
          ∑ i, c i * ∑ C ∈ markedClusters boundary L ϱ₀ (N i), ∑ T ∈ C.powerset,
            ((1 / 2) ^ C.card * ∏ m ∈ C, K i m) *
              Real.cos (∑ j, ψ j * markedDensity ξ ϱ₀ (satellite L C T) j) *
              ∏ ϱ ∈ markedRemainder boundary L ϱ₀ (N i) C,
                (1 + K i ϱ * Real.cos (∑ j, ψ j * (ϱ j : ℝ)))

/-- KP T2.2 on a domain gives the marked T2.2 on that domain, with the same branch data. -/
theorem markedT22Step_of_t22Step {D₂ : ℝ} (h : Reduction.T22Step boundary L D₂) :
    MarkedT22Step boundary L D₂ := by
  intro lam Nq lamHat hNq hzero hlam
  obtain ⟨n, N, c, K, hens, hc, hsum, hid, hprop⟩ := h lam Nq lamHat hNq hzero hlam
  refine ⟨n, N, c, K, hens, hc, hsum, hid, hprop, fun ϱ₀ hϱ₀ ξ ψ => ?_⟩
  rw [hid ψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, markedExpansion hϱ₀]

/--
**The marked T2.2** (FS81 Theorem 2.3, cluster form) on every square domain, from the
KP T2.2 (`t22Statement_of_repairedBasicLemma`).
-/
theorem markedT22Statement :
    ∃ D₂ : ℝ, 0 < D₂ ∧ ∀ L : ℕ, 1 < L →
      MarkedT22Step .free L D₂ ∧ (Even L → MarkedT22Step .periodic L D₂) := by
  obtain ⟨D₂, hD₂, h⟩ := t22Statement_of_repairedBasicLemma
  exact ⟨D₂, hD₂, fun L hL => ⟨markedT22Step_of_t22Step (h L hL).1,
    fun he => markedT22Step_of_t22Step ((h L hL).2 he)⟩⟩

/-! #### The remainder: KP properties and separation from the composite -/

theorem isChargeEnsemble_mono {N N' : Finset (ChargeDensity L)} (h : IsChargeEnsemble N)
    (hsub : N' ⊆ N) : IsChargeEnsemble N' :=
  ⟨fun ϱ hϱ => h.1 ϱ (hsub hϱ), fun ϱ₁ h₁ ϱ₂ h₂ hne => h.2 ϱ₁ (hsub h₁) ϱ₂ (hsub h₂) hne⟩

theorem atMostOneNonNeutral_mono {N N' : Finset (ChargeDensity L)}
    (h : AtMostOneNonNeutral N) (hsub : N' ⊆ N) : AtMostOneNonNeutral N' :=
  fun ϱ₁ h₁ ϱ₂ h₂ => h ϱ₁ (hsub h₁) ϱ₂ (hsub h₂)

theorem isScaleSeparated_mono {N N' : Finset (ChargeDensity L)}
    (h : IsScaleSeparated boundary L N) (hsub : N' ⊆ N) : IsScaleSeparated boundary L N' :=
  ⟨fun ϱ₁ h₁ ϱ₂ h₂ hne => h.1 ϱ₁ (hsub h₁) ϱ₂ (hsub h₂) hne,
    fun ϱc hc hq ϱ hϱ hne => h.2 ϱc (hsub hc) hq ϱ (hsub hϱ) hne⟩

theorem neutralSplitsAreCharged_mono {N N' : Finset (ChargeDensity L)}
    (h : NeutralSplitsAreCharged boundary L N) (hsub : N' ⊆ N) :
    NeutralSplitsAreCharged boundary L N' :=
  fun ϱ hϱ => h ϱ (hsub hϱ)

/-- The remainder of a cluster inherits KP T2.2 (a)–(c). -/
theorem markedRemainder_t22 {ϱ₀ : ChargeDensity L} {N C : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) (ha : AtMostOneNonNeutral N) (hb : IsScaleSeparated boundary L N)
    (hc : NeutralSplitsAreCharged boundary L N) :
    IsChargeEnsemble (markedRemainder boundary L ϱ₀ N C) ∧
      AtMostOneNonNeutral (markedRemainder boundary L ϱ₀ N C) ∧
      IsScaleSeparated boundary L (markedRemainder boundary L ϱ₀ N C) ∧
      NeutralSplitsAreCharged boundary L (markedRemainder boundary L ϱ₀ N C) :=
  have hsub := remainder_subset (adj := MarkAdjacent boundary L ϱ₀) N C
  ⟨isChargeEnsemble_mono hens hsub, atMostOneNonNeutral_mono ha hsub,
    isScaleSeparated_mono hb hsub, neutralSplitsAreCharged_mono hc hsub⟩

/-- **Separation of the remainder from the marked composite**: every member `ϱ` left beside the
cluster satisfies `M · scale^α ≤ dist(ϱ, supp ϱ₀ ∪ ⋃ C)`. -/
theorem markedRemainder_separation {ϱ₀ : ChargeDensity L} {N C : Finset (ChargeDensity L)}
    {ϱ : ChargeDensity L} (hϱ : ϱ ∈ markedRemainder boundary L ϱ₀ N C) :
    (chargeCoverScale : ℝ) * markScale boundary L ϱ₀ ϱ C ^ chargeCoverExponent ≤
      squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C) :=
  not_lt.1 (not_adj_of_mem_remainder hϱ)

/-- KP T2.2(b), first clause, for the remainder against the composite:
`M · min(d(ϱ), d(composite))^α ≤ dist`. -/
theorem markedRemainder_separation_min {ϱ₀ : ChargeDensity L} {N C : Finset (ChargeDensity L)}
    {ϱ : ChargeDensity L} (hϱ : ϱ ∈ markedRemainder boundary L ϱ₀ N C) :
    (chargeCoverScale : ℝ) * ((min (chargeDiameter boundary L ϱ)
        (squareDiameter boundary L (markedSupport L ϱ₀ C)) : ℕ) : ℝ) ^ chargeCoverExponent ≤
      squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C) := by
  refine le_trans ?_ (markedRemainder_separation hϱ)
  have hα : (0 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hα)
    (by norm_num [chargeCoverScale])
  unfold markScale
  split_ifs
  · exact_mod_cast min_le_max
  · exact le_rfl

/-- KP T2.2(b), second clause: if `ϱ` or the cluster is charged, the remainder member is separated
at the larger scale, `M · max(d(ϱ), d(composite))^α ≤ dist`. -/
theorem markedRemainder_separation_of_charged {ϱ₀ : ChargeDensity L}
    {N C : Finset (ChargeDensity L)} {ϱ : ChargeDensity L}
    (hϱ : ϱ ∈ markedRemainder boundary L ϱ₀ N C)
    (hq : (∑ j, ϱ j ≠ 0) ∨ ∃ m ∈ C, ∑ j, m j ≠ 0) :
    (chargeCoverScale : ℝ) * ((max (chargeDiameter boundary L ϱ)
        (squareDiameter boundary L (markedSupport L ϱ₀ C)) : ℕ) : ℝ) ^ chargeCoverExponent ≤
      squareDistance boundary L (chargeSupport ϱ) (markedSupport L ϱ₀ C) := by
  have h := markedRemainder_separation hϱ
  unfold markScale at h
  simpa only [hq, ↓reduceIte] using h

/-- **The activity of a neutral cluster** (FS81 (2.30), lineage form): from KP T2.2(d) for the
members, `|2^{−|C|} ∏_C K| ≤ 2^{−|C|} ∏_{m ∈ C} e^{D₂ A(m)} ∏_{j ∈ supp m} e^{m(j)²} |λ̂_j(|m(j)|)|`. -/
theorem abs_clusterWeight_le {N : Finset (ChargeDensity L)} {K : ChargeDensity L → ℝ} {D₂ : ℝ}
    {lamHat : Fin L × Fin L → ℕ → ℝ}
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    {C : Finset (ChargeDensity L)} (hC : C ⊆ N) (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    |(1 / 2) ^ C.card * ∏ m ∈ C, K m| ≤
      (1 / 2) ^ C.card * ∏ m ∈ C, (Real.exp (D₂ * chargeCoverCost boundary L m) *
        ∏ j ∈ chargeSupport m, Real.exp ((m j : ℝ) ^ 2) * |lamHat j (m j).natAbs|) := by
  have hhalf : (0 : ℝ) ≤ (1 / 2) ^ C.card := by positivity
  rw [abs_mul, abs_of_nonneg hhalf, Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    fun m hm => hd m (hC hm) (hCn m hm)) hhalf

/-! #### Charged splits of a neutral marked composite -/

private theorem eq_of_latticeDistance_eq_zero (hL : 1 < L) {x y : Fin L × Fin L}
    (h : latticeDistance boundary L x y = 0) : x = y := by
  cases boundary with
  | free =>
    exact ((squareFree_connected L hL).preconnected x y).dist_eq_zero_iff.1 h
  | periodic =>
    exact ((squarePeriodic_connected L hL).preconnected x y).dist_eq_zero_iff.1 h

/-- Two distinct members of a scale-separated ensemble cannot both straddle a separated split. -/
theorem not_two_cut (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hb : IsScaleSeparated boundary L N) {A B : Finset (Fin L × Fin L)} (hAB : Disjoint A B)
    (hsep : 2 * (chargeCoverScale : ℝ) *
        ((min (squareDiameter boundary L A) (squareDiameter boundary L B) : ℕ) : ℝ) ^
          chargeCoverExponent ≤ squareDistance boundary L A B)
    {m₁ m₂ : ChargeDensity L} (h₁ : m₁ ∈ N) (h₂ : m₂ ∈ N) (hne : m₁ ≠ m₂)
    {p₁ p₁' p₂ p₂' : Fin L × Fin L}
    (hp₁ : p₁ ∈ chargeSupport m₁) (hp₁' : p₁' ∈ chargeSupport m₁)
    (hp₂ : p₂ ∈ chargeSupport m₂) (hp₂' : p₂' ∈ chargeSupport m₂)
    (hA₁ : p₁ ∈ A) (hA₂ : p₂ ∈ A) (hB₁ : p₁' ∈ B) (hB₂ : p₂' ∈ B) : False := by
  set μ := min (squareDiameter boundary L A) (squareDiameter boundary L B) with hμ
  set δ := min (chargeDiameter boundary L m₁) (chargeDiameter boundary L m₂) with hδ
  have hd₁ : squareDistance boundary L A B ≤ chargeDiameter boundary L m₁ :=
    (squareDistance_le_latticeDistance_of_mem boundary L A B p₁ p₁' hA₁ hB₁).trans
      (latticeDistance_le_squareDiameter_of_mem boundary L _ p₁ p₁' hp₁ hp₁')
  have hd₂ : squareDistance boundary L A B ≤ chargeDiameter boundary L m₂ :=
    (squareDistance_le_latticeDistance_of_mem boundary L A B p₂ p₂' hA₂ hB₂).trans
      (latticeDistance_le_squareDiameter_of_mem boundary L _ p₂ p₂' hp₂ hp₂')
  have hdist : densityDistance boundary L m₁ m₂ ≤ μ := by
    refine le_min ?_ ?_
    · exact (squareDistance_le_latticeDistance_of_mem boundary L _ _ p₁ p₂ hp₁ hp₂).trans
        (latticeDistance_le_squareDiameter_of_mem boundary L A p₁ p₂ hA₁ hA₂)
    · exact (squareDistance_le_latticeDistance_of_mem boundary L _ _ p₁' p₂' hp₁' hp₂').trans
        (latticeDistance_le_squareDiameter_of_mem boundary L B p₁' p₂' hB₁ hB₂)
  have hbsep := hb.1 m₁ h₁ m₂ h₂ hne
  rw [← hδ] at hbsep
  have hM : (1 : ℝ) ≤ chargeCoverScale := by norm_num [chargeCoverScale]
  have hα : (1 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  have hδsep : (squareDistance boundary L A B : ℝ) ≤ δ := by exact_mod_cast le_min hd₁ hd₂
  have hMδ : (chargeCoverScale : ℝ) * (δ : ℝ) ^ chargeCoverExponent ≤ μ := by
    refine hbsep.trans ?_
    exact_mod_cast hdist
  rcases Nat.eq_zero_or_pos μ with hμ0 | hμ0
  · -- `μ = 0`: then `δ = 0`, so a straddling member has a one-point support
    have hδ0 : δ = 0 := by
      by_contra hδ0
      have hδ1 : (1 : ℝ) ≤ δ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hδ0
      have : (1 : ℝ) ≤ (δ : ℝ) ^ chargeCoverExponent := Real.one_le_rpow hδ1 (by linarith)
      rw [hμ0, Nat.cast_zero] at hMδ
      nlinarith
    have hcases : chargeDiameter boundary L m₁ = 0 ∨ chargeDiameter boundary L m₂ = 0 := by
      omega
    rcases hcases with h | h
    · have hz : latticeDistance boundary L p₁ p₁' = 0 := by
        have := latticeDistance_le_squareDiameter_of_mem boundary L _ p₁ p₁' hp₁ hp₁'
        unfold chargeDiameter at h
        omega
      have := eq_of_latticeDistance_eq_zero hL hz
      subst this
      exact Finset.disjoint_left.1 hAB hA₁ hB₁
    · have hz : latticeDistance boundary L p₂ p₂' = 0 := by
        have := latticeDistance_le_squareDiameter_of_mem boundary L _ p₂ p₂' hp₂ hp₂'
        unfold chargeDiameter at h
        omega
      have := eq_of_latticeDistance_eq_zero hL hz
      subst this
      exact Finset.disjoint_left.1 hAB hA₂ hB₂
  · -- `μ ≥ 1`: the two scale inequalities are incompatible
    have hμ1 : (1 : ℝ) ≤ μ := by exact_mod_cast hμ0
    have hμα : (μ : ℝ) ≤ (μ : ℝ) ^ chargeCoverExponent := Real.self_le_rpow_of_one_le hμ1 hα
    have h2 : 2 * (μ : ℝ) ≤ δ := by
      have := hsep.trans hδsep
      nlinarith
    have hδ1 : (1 : ℝ) ≤ δ := by linarith
    have hδα : (δ : ℝ) ≤ (δ : ℝ) ^ chargeCoverExponent := Real.self_le_rpow_of_one_le hδ1 hα
    nlinarith

/-- **Connectivity of a cluster.** If a nonempty part `CQ` of a neutral cluster is removed, some
member of `CQ` is adjacent, at the neutral (minimum) scale, to the marked support of the rest. -/
theorem exists_cluster_link {ϱ₀ : ChargeDensity L} (hϱ₀ : ϱ₀ ≠ 0)
    {N C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L ϱ₀ N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) {CQ : Finset (ChargeDensity L)} (hCQ : CQ ⊆ C)
    (hne : CQ.Nonempty) :
    ∃ m ∈ CQ, (squareDistance boundary L (chargeSupport m)
        (markedSupport L ϱ₀ (C \ CQ)) : ℝ) <
      (chargeCoverScale : ℝ) * ((min (chargeDiameter boundary L m)
        (squareDiameter boundary L (markedSupport L ϱ₀ (C \ CQ))) : ℕ) : ℝ) ^
          chargeCoverExponent := by
  have hcomp := (mem_clusters.1 hC).2
  set adj := MarkAdjacent boundary L ϱ₀ with hadjdef
  have hex : ∃ k, ∃ m ∈ CQ, m ∈ growIter adj C k := by
    obtain ⟨m, hm⟩ := hne
    refine ⟨C.card, m, hm, ?_⟩
    have : component adj C = growIter adj C C.card := rfl
    rw [← this, hcomp]
    exact hCQ hm
  have hspec := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    obtain ⟨m, _, hm⟩ := hspec
    rw [h0, growIter_zero] at hm
    exact Finset.notMem_empty m hm
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hj' : Nat.find hex = j + 1 := hj
  have hmin : ∀ m ∈ CQ, m ∉ growIter adj C j := by
    intro m hm hmj
    exact Nat.find_min hex (show j < Nat.find hex by omega) ⟨m, hm, hmj⟩
  obtain ⟨m, hmCQ, hmk⟩ := hspec
  rw [hj', growIter_succ] at hmk
  have hadj : adj m (growIter adj C j) := by
    rcases Finset.mem_union.1 hmk with h | h
    · exact absurd h (hmin m hmCQ)
    · exact (Finset.mem_filter.1 h).2
  have hsub : growIter adj C j ⊆ C \ CQ := fun m' hm' =>
    Finset.mem_sdiff.2 ⟨growIter_subset C j hm', fun h => hmin m' h hm'⟩
  have hadj' : adj m (C \ CQ) := markAdjacent_monotone hϱ₀ m _ _ hsub hadj
  refine ⟨m, hmCQ, ?_⟩
  have h := hadj'
  simp only [hadjdef, MarkAdjacent] at h
  rwa [markScale_of_neutral (hCn m (hCQ hmCQ))
    (fun m' hm' => hCn m' (Finset.mem_sdiff.1 hm').1)] at h

/-- A neutral cluster whose pieces fall on two sides `P ⊇` (mark and rest) and `Q ⊇` (a nonempty
part `CQ`) is never KP-separated: `dist(P, Q) < M · min(d(P), d(Q))^α`. -/
theorem cluster_not_separated {ϱ₀ : ChargeDensity L} (hϱ₀ : ϱ₀ ≠ 0)
    {N C : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hC : C ∈ markedClusters boundary L ϱ₀ N) (hCn : ∀ m ∈ C, ∑ j, m j = 0)
    {CQ : Finset (ChargeDensity L)} (hCQ : CQ ⊆ C) (hne : CQ.Nonempty)
    {P Q : Finset (Fin L × Fin L)} (hP : markedSupport L ϱ₀ (C \ CQ) ⊆ P)
    (hQ : ∀ m ∈ CQ, chargeSupport m ⊆ Q) :
    (squareDistance boundary L P Q : ℝ) <
      (chargeCoverScale : ℝ) * ((min (squareDiameter boundary L P)
        (squareDiameter boundary L Q) : ℕ) : ℝ) ^ chargeCoverExponent := by
  obtain ⟨m, hmCQ, hlink⟩ := exists_cluster_link hϱ₀ hC hCn hCQ hne
  have hmN : m ∈ N := (mem_clusters.1 hC).1 (hCQ hmCQ)
  have hmne : (chargeSupport m).Nonempty := chargeSupport_nonempty' (hens.1 m hmN)
  have hXne : (markedSupport L ϱ₀ (C \ CQ)).Nonempty :=
    (chargeSupport_nonempty' hϱ₀).mono (chargeSupport_subset_markedSupport ϱ₀ _)
  have hdist : squareDistance boundary L P Q ≤
      squareDistance boundary L (chargeSupport m) (markedSupport L ϱ₀ (C \ CQ)) := by
    rw [squareDistance_comm boundary L P Q]
    exact squareDistance_le_of_subset boundary L hmne hXne (hQ m hmCQ) hP
  have hmin : min (chargeDiameter boundary L m)
      (squareDiameter boundary L (markedSupport L ϱ₀ (C \ CQ))) ≤
      min (squareDiameter boundary L P) (squareDiameter boundary L Q) := by
    rw [min_comm (squareDiameter boundary L P)]
    exact min_le_min (squareDiameter_mono boundary L (hQ m hmCQ))
      (squareDiameter_mono boundary L hP)
  have hα : (0 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  calc (squareDistance boundary L P Q : ℝ)
      ≤ squareDistance boundary L (chargeSupport m) (markedSupport L ϱ₀ (C \ CQ)) := by
        exact_mod_cast hdist
    _ < _ := hlink
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmin) hα)
        (by norm_num [chargeCoverScale])

private theorem sum_eq_sum_univ_of_support_subset {f : ChargeDensity L}
    {U : Finset (Fin L × Fin L)} (h : chargeSupport f ⊆ U) : ∑ j ∈ U, f j = ∑ j, f j :=
  Finset.sum_subset (Finset.subset_univ U) fun j _ hjU => by
    by_contra hf
    exact hjU (h (mem_chargeSupport'.2 hf))

private theorem sum_eq_zero_of_disjoint {f : ChargeDensity L} {U S : Finset (Fin L × Fin L)}
    (h : Disjoint (chargeSupport f) S) : ∑ j ∈ U ∩ S, f j = 0 :=
  Finset.sum_eq_zero fun j hj => by
    by_contra hf
    exact Finset.disjoint_left.1 h (mem_chargeSupport'.2 hf) (Finset.mem_inter.1 hj).2

/-- **Charged splits of a neutral marked composite** (FS81 Theorem 2.3(c) for the cluster
composites of `MarkedT22Step`, neutral marks). Let the mark `ϱ₀` be neutral and assume that its
proper restrictions have `η`-gapped `ξ`-charge (FS81 (2.28) for restrictions; for the dipole this
is `dipole_condition228_restriction`). Let `C` be a marked cluster of a KP ensemble with neutral
members and `T ⊆ C`. Then every KP-separated split `(X ∩ S, X ∖ S)` of the composite support
`X = supp ϱ₀ ∪ ⋃ C` carries charge at least `η` in absolute value.

Proof: a split cutting the mark is `η`-gapped by hypothesis; otherwise the charge is an integer.
At most one member can straddle a separated split (`not_two_cut`), and a straddling neutral member
is charged on each side by KP T2.2(c). If no member straddles, the split separates whole pieces of
the cluster, which contradicts its connectivity (`cluster_not_separated`). -/
theorem markedComposite_charged_split (hL : 1 < L) {ϱ₀ : ChargeDensity L} (hϱ₀ : ϱ₀ ≠ 0)
    (hmark : ∑ j, ϱ₀ j = 0) {ξ η : ℝ} (hη : η ≤ 1)
    (hgap : ∀ S : Finset (Fin L × Fin L), (∃ j ∈ S, ϱ₀ j ≠ 0) → (∃ j ∉ S, ϱ₀ j ≠ 0) →
      IsGapped η (ξ * ((∑ j ∈ S, ϱ₀ j : ℤ) : ℝ)))
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hb : IsScaleSeparated boundary L N) (hc : NeutralSplitsAreCharged boundary L N)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L ϱ₀ N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) {T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (S : Finset (Fin L × Fin L))
    (hA : (markedSupport L ϱ₀ C ∩ S).Nonempty) (hB : (markedSupport L ϱ₀ C \ S).Nonempty)
    (hsep : 2 * (chargeCoverScale : ℝ) *
        ((min (squareDiameter boundary L (markedSupport L ϱ₀ C ∩ S))
          (squareDiameter boundary L (markedSupport L ϱ₀ C \ S)) : ℕ) : ℝ) ^
            chargeCoverExponent ≤
        squareDistance boundary L (markedSupport L ϱ₀ C ∩ S) (markedSupport L ϱ₀ C \ S)) :
    η ≤ |setCharge (markedDensity ξ ϱ₀ (satellite L C T)) (markedSupport L ϱ₀ C ∩ S)| := by
  set X := markedSupport L ϱ₀ C with hX
  set A := X ∩ S with hAdef
  set B := X \ S with hBdef
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hAB : Disjoint A B :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right Finset.disjoint_sdiff
  have hmemX : ∀ {m j}, m ∈ C → m j ≠ 0 → j ∈ X := fun hm hj =>
    chargeSupport_subset_markedSupport_of_mem hm (mem_chargeSupport'.2 hj)
  rw [setCharge_markedDensity]
  by_cases hcut : (∃ j ∈ A, ϱ₀ j ≠ 0) ∧ (∃ j ∉ A, ϱ₀ j ≠ 0)
  · exact ((hgap A hcut.1 hcut.2).add_int _).le_abs
  have hmark0 : ∑ j ∈ A, ϱ₀ j = 0 := by
    by_cases hin : ∃ j ∈ A, ϱ₀ j ≠ 0
    · have hall : chargeSupport ϱ₀ ⊆ A := fun j hj => by
        by_contra hjA
        exact hcut ⟨hin, j, hjA, mem_chargeSupport'.1 hj⟩
      rw [sum_eq_sum_univ_of_support_subset hall, hmark]
    · push Not at hin
      exact Finset.sum_eq_zero hin
  rw [hmark0, Int.cast_zero, mul_zero, zero_add]
  suffices hne : ∑ j ∈ A, satellite L C T j ≠ 0 by
    have h1 : (1 : ℝ) ≤ |((∑ j ∈ A, satellite L C T j : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne
    linarith
  have hM0 : (0 : ℝ) ≤ chargeCoverScale := by norm_num [chargeCoverScale]
  by_cases hcutm : ∃ m ∈ C, (∃ p ∈ chargeSupport m, p ∈ S) ∧ (∃ p ∈ chargeSupport m, p ∉ S)
  · obtain ⟨m, hmC, ⟨p, hp, hpS⟩, ⟨p', hp', hp'S⟩⟩ := hcutm
    have hpA : p ∈ A := Finset.mem_inter.2 ⟨hmemX hmC (mem_chargeSupport'.1 hp), hpS⟩
    have hp'B : p' ∈ B := Finset.mem_sdiff.2 ⟨hmemX hmC (mem_chargeSupport'.1 hp'), hp'S⟩
    have huniq : ∀ m' ∈ C, m' ≠ m →
        chargeSupport m' ⊆ S ∨ Disjoint (chargeSupport m') S := by
      intro m' hm'C hne
      by_contra hcontra
      push Not at hcontra
      obtain ⟨hnsub, hndisj⟩ := hcontra
      obtain ⟨q', hq', hq'S⟩ := Finset.not_subset.1 hnsub
      obtain ⟨q, hq, hqS⟩ := Finset.not_disjoint_iff.1 hndisj
      exact not_two_cut hL hb hAB hsep (hCN hmC) (hCN hm'C) (Ne.symm hne) hp hp' hq hq' hpA
        (Finset.mem_inter.2 ⟨hmemX hm'C (mem_chargeSupport'.1 hq), hqS⟩) hp'B
        (Finset.mem_sdiff.2 ⟨hmemX hm'C (mem_chargeSupport'.1 hq'), hq'S⟩)
    have hwhole : ∀ m' ∈ C, m' ≠ m → ∑ j ∈ A, m' j = 0 := by
      intro m' hm'C hne
      rcases huniq m' hm'C hne with hsub | hdisj
      · have hsubA : chargeSupport m' ⊆ A := fun j hj =>
          Finset.mem_inter.2 ⟨hmemX hm'C (mem_chargeSupport'.1 hj), hsub hj⟩
        rw [sum_eq_sum_univ_of_support_subset hsubA, hCn m' hm'C]
      · exact sum_eq_zero_of_disjoint hdisj
    have hsum_of : ∀ U ⊆ C, ∑ m' ∈ U, ∑ j ∈ A, m' j =
        if m ∈ U then ∑ j ∈ A, m j else 0 := by
      intro U hU
      rw [Finset.sum_congr rfl fun m' hm' => (show ∑ j ∈ A, m' j =
        if m' = m then ∑ j ∈ A, m j else 0 by
          split_ifs with h
          · rw [h]
          · exact hwhole m' (hU hm') h), Finset.sum_ite_eq']
    have hsat : ∑ j ∈ A, satellite L C T j =
        (if m ∈ T then ∑ j ∈ A, m j else 0) - (if m ∈ C \ T then ∑ j ∈ A, m j else 0) := by
      unfold satellite
      rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (s := A),
        hsum_of T hT, hsum_of (C \ T) Finset.sdiff_subset]
    -- the straddling member is charged on `A` (KP T2.2(c))
    set m₁ : ChargeDensity L := fun j => if j ∈ S then m j else 0 with hm₁
    set m₂ : ChargeDensity L := fun j => if j ∈ S then 0 else m j with hm₂
    have hsupp₁ : chargeSupport m₁ ⊆ A := fun j hj => by
      have hj' := mem_chargeSupport'.1 hj
      simp only [hm₁] at hj'
      split_ifs at hj' with hjS
      · exact Finset.mem_inter.2 ⟨hmemX hmC hj', hjS⟩
      · exact absurd rfl hj'
    have hsupp₂ : chargeSupport m₂ ⊆ B := fun j hj => by
      have hj' := mem_chargeSupport'.1 hj
      simp only [hm₂] at hj'
      split_ifs at hj' with hjS
      · exact absurd rfl hj'
      · exact Finset.mem_sdiff.2 ⟨hmemX hmC hj', hjS⟩
    have hm₁p : m₁ p ≠ 0 := by simpa [hm₁, hpS] using mem_chargeSupport'.1 hp
    have hm₂p : m₂ p' ≠ 0 := by simpa [hm₂, hp'S] using mem_chargeSupport'.1 hp'
    have h₁ : m₁ ≠ 0 := fun h => hm₁p (by rw [h]; rfl)
    have h₂ : m₂ ≠ 0 := fun h => hm₂p (by rw [h]; rfl)
    have hdisj : Disjoint (Function.support m₁) (Function.support m₂) := by
      rw [Function.disjoint_support_iff]
      intro j hj
      simp only [hm₂]
      by_cases hjS : j ∈ S
      · simp [hjS]
      · exact absurd (by simp [hm₁, hjS]) hj
    have hsplit : m = m₁ + m₂ := by
      funext j
      by_cases hjS : j ∈ S <;> simp [hm₁, hm₂, hjS]
    have hne₁ := chargeSupport_nonempty' h₁
    have hne₂ := chargeSupport_nonempty' h₂
    have hsep' : 2 * (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L m₁) (chargeDiameter boundary L m₂) : ℕ) : ℝ) ^
          chargeCoverExponent ≤ densityDistance boundary L m₁ m₂ := by
      have hdist : squareDistance boundary L A B ≤ densityDistance boundary L m₁ m₂ :=
        squareDistance_le_of_subset boundary L hne₁ hne₂ hsupp₁ hsupp₂
      have hmin : min (chargeDiameter boundary L m₁) (chargeDiameter boundary L m₂) ≤
          min (squareDiameter boundary L A) (squareDiameter boundary L B) :=
        min_le_min (squareDiameter_mono boundary L hsupp₁) (squareDiameter_mono boundary L hsupp₂)
      have hα : (0 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
      calc 2 * (chargeCoverScale : ℝ) *
            ((min (chargeDiameter boundary L m₁) (chargeDiameter boundary L m₂) : ℕ) : ℝ) ^
              chargeCoverExponent
          ≤ 2 * (chargeCoverScale : ℝ) *
            ((min (squareDiameter boundary L A) (squareDiameter boundary L B) : ℕ) : ℝ) ^
              chargeCoverExponent :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmin) hα) (by positivity)
        _ ≤ squareDistance boundary L A B := hsep
        _ ≤ densityDistance boundary L m₁ m₂ := by exact_mod_cast hdist
    have hcharged := (hc m (hCN hmC) (hCn m hmC) m₁ m₂ h₁ h₂ hdisj hsplit hsep').1
    have hm₁sum : ∑ j, m₁ j = ∑ j ∈ A, m j := by
      have h1 : ∑ j, m₁ j = ∑ j ∈ S, m j := by
        simp only [hm₁]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [h1]
      refine (Finset.sum_subset Finset.inter_subset_right fun j hjS hjA => ?_).symm
      by_contra hmj
      exact hjA (Finset.mem_inter.2 ⟨hmemX hmC hmj, hjS⟩)
    rw [hm₁sum] at hcharged
    rw [hsat]
    have hmCT : m ∈ C \ T ↔ m ∉ T := ⟨fun h => (Finset.mem_sdiff.1 h).2,
      fun h => Finset.mem_sdiff.2 ⟨hmC, h⟩⟩
    by_cases hmT : m ∈ T
    · rw [ite_eq_left hmT, ite_eq_right (fun h => (hmCT.1 h) hmT), sub_zero]
      exact hcharged
    · rw [ite_eq_right hmT, ite_eq_left (hmCT.2 hmT), zero_sub, neg_ne_zero]
      exact hcharged
  · exfalso
    push Not at hcutm
    have hside : ∀ m ∈ C, chargeSupport m ⊆ S ∨ Disjoint (chargeSupport m) S := by
      intro m hm
      by_cases hmeet : ∃ p ∈ chargeSupport m, p ∈ S
      · exact Or.inl fun p hp => hcutm m hm hmeet p hp
      · push Not at hmeet
        exact Or.inr (Finset.disjoint_left.2 hmeet)
    have hpos : (0 : ℝ) ≤ (chargeCoverScale : ℝ) *
        ((min (squareDiameter boundary L A) (squareDiameter boundary L B) : ℕ) : ℝ) ^
          chargeCoverExponent := by positivity
    by_cases hmarkA : ∃ j ∈ A, ϱ₀ j ≠ 0
    · -- the mark lies in `S`; the far side `B` holds a nonempty part of the cluster
      have hmS : chargeSupport ϱ₀ ⊆ S := fun j hj => by
        by_contra hjS
        exact hcut ⟨hmarkA, j, fun hjA => hjS (Finset.mem_inter.1 hjA).2,
          mem_chargeSupport'.1 hj⟩
      set CQ := C.filter fun m => Disjoint (chargeSupport m) S with hCQ
      have hCQne : CQ.Nonempty := by
        obtain ⟨j, hj⟩ := hB
        obtain ⟨hjX, hjS⟩ := Finset.mem_sdiff.1 hj
        rcases mem_markedSupport.1 hjX with h0 | ⟨m, hmC, hmj⟩
        · exact absurd (hmS (mem_chargeSupport'.2 h0)) hjS
        · refine ⟨m, Finset.mem_filter.2 ⟨hmC, ?_⟩⟩
          rcases hside m hmC with hsub | hdisj
          · exact absurd (hsub (mem_chargeSupport'.2 hmj)) hjS
          · exact hdisj
      have hP : markedSupport L ϱ₀ (C \ CQ) ⊆ A := by
        intro j hj
        rcases mem_markedSupport.1 hj with h0 | ⟨m, hm, hmj⟩
        · exact Finset.mem_inter.2 ⟨chargeSupport_subset_markedSupport ϱ₀ C
            (mem_chargeSupport'.2 h0), hmS (mem_chargeSupport'.2 h0)⟩
        · obtain ⟨hmC, hmQ⟩ := Finset.mem_sdiff.1 hm
          have hnd : ¬ Disjoint (chargeSupport m) S := fun h =>
            hmQ (Finset.mem_filter.2 ⟨hmC, h⟩)
          rcases hside m hmC with hsub | hdisj
          · exact Finset.mem_inter.2 ⟨hmemX hmC hmj, hsub (mem_chargeSupport'.2 hmj)⟩
          · exact absurd hdisj hnd
      have hQ : ∀ m ∈ CQ, chargeSupport m ⊆ B := by
        intro m hm j hj
        obtain ⟨hmC, hmd⟩ := Finset.mem_filter.1 hm
        exact Finset.mem_sdiff.2 ⟨hmemX hmC (mem_chargeSupport'.1 hj),
          Finset.disjoint_left.1 hmd hj⟩
      have hlt := cluster_not_separated hϱ₀ hens hC hCn (Finset.filter_subset _ _) hCQne hP hQ
      linarith
    · -- the mark avoids `S`; the side `A` holds a nonempty part of the cluster
      push Not at hmarkA
      have hmB : ∀ j, ϱ₀ j ≠ 0 → j ∈ B := fun j hj =>
        Finset.mem_sdiff.2 ⟨chargeSupport_subset_markedSupport ϱ₀ C (mem_chargeSupport'.2 hj),
          fun hjS => hj (hmarkA j (Finset.mem_inter.2
            ⟨chargeSupport_subset_markedSupport ϱ₀ C (mem_chargeSupport'.2 hj), hjS⟩))⟩
      set CQ := C.filter fun m => chargeSupport m ⊆ S with hCQ
      have hCQne : CQ.Nonempty := by
        obtain ⟨j, hj⟩ := hA
        obtain ⟨hjX, hjS⟩ := Finset.mem_inter.1 hj
        rcases mem_markedSupport.1 hjX with h0 | ⟨m, hmC, hmj⟩
        · exact absurd hjS (Finset.mem_sdiff.1 (hmB j h0)).2
        · refine ⟨m, Finset.mem_filter.2 ⟨hmC, ?_⟩⟩
          rcases hside m hmC with hsub | hdisj
          · exact hsub
          · exact absurd hjS (Finset.disjoint_left.1 hdisj (mem_chargeSupport'.2 hmj))
      have hP : markedSupport L ϱ₀ (C \ CQ) ⊆ B := by
        intro j hj
        rcases mem_markedSupport.1 hj with h0 | ⟨m, hm, hmj⟩
        · exact hmB j h0
        · obtain ⟨hmC, hmQ⟩ := Finset.mem_sdiff.1 hm
          rcases hside m hmC with hsub | hdisj
          · exact absurd (Finset.mem_filter.2 ⟨hmC, hsub⟩) hmQ
          · exact Finset.mem_sdiff.2 ⟨hmemX hmC hmj,
              Finset.disjoint_left.1 hdisj (mem_chargeSupport'.2 hmj)⟩
      have hQ : ∀ m ∈ CQ, chargeSupport m ⊆ A := by
        intro m hm j hj
        obtain ⟨hmC, hmS⟩ := Finset.mem_filter.1 hm
        exact Finset.mem_inter.2 ⟨hmemX hmC (mem_chargeSupport'.1 hj), hmS hj⟩
      have hlt := cluster_not_separated hϱ₀ hens hC hCn (Finset.filter_subset _ _) hCQne hP hQ
      rw [squareDistance_comm, min_comm] at hlt
      linarith

/-- **The Coulomb-B composite** (FS81 §5.1, `ϱ₀ = δ_o − δ_x`): for a neutral cluster of a KP
ensemble, every KP-separated split of the marked composite `ξ(δ_o − δ_x) + ϱ^𝒩` carries charge at
least `η = min(ξ, 1 − ξ)` in absolute value (CG.s5 with the expansion of `MarkedT22Step`). -/
theorem dipoleComposite_charged_split (hL : 1 < L) {o x : Fin L × Fin L} (hox : o ≠ x)
    (ξ : ℝ) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hb : IsScaleSeparated boundary L N) (hc : NeutralSplitsAreCharged boundary L N)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) {T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (S : Finset (Fin L × Fin L))
    (hA : (markedSupport L (dipoleMark o x) C ∩ S).Nonempty)
    (hB : (markedSupport L (dipoleMark o x) C \ S).Nonempty)
    (hsep : 2 * (chargeCoverScale : ℝ) *
        ((min (squareDiameter boundary L (markedSupport L (dipoleMark o x) C ∩ S))
          (squareDiameter boundary L (markedSupport L (dipoleMark o x) C \ S)) : ℕ) : ℝ) ^
            chargeCoverExponent ≤
        squareDistance boundary L (markedSupport L (dipoleMark o x) C ∩ S)
          (markedSupport L (dipoleMark o x) C \ S)) :
    dipoleGap ξ ≤ |setCharge (markedDensity ξ (dipoleMark o x) (satellite L C T))
      (markedSupport L (dipoleMark o x) C ∩ S)| :=
  markedComposite_charged_split hL (dipoleMark_ne_zero hox) (sum_univ_dipoleMark o x)
    (dipoleGap_le_one ξ) (fun S h1 h2 => dipole_isGapped_restriction ξ S h1 h2) hens hb hc hC
    hCn hT S hA hB hsep

/-- **No cancellation in the Coulomb-B composite**: for the dipole, `0 < ξ < 1` and a cluster
with pairwise disjoint member supports, the real composite `ξ(δ_o − δ_x) + ϱ^𝒩` vanishes exactly
off `supp ϱ₀ ∪ ⋃ C`. So the support-based splits of `dipoleComposite_charged_split` are the splits
of the composite density itself. -/
theorem dipole_markedDensity_ne_zero_iff {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℝ}
    (h0 : 0 < ξ) (h1 : ξ < 1) {C T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m')) (j : Fin L × Fin L) :
    markedDensity ξ (dipoleMark o x) (satellite L C T) j ≠ 0 ↔
      j ∈ markedSupport L (dipoleMark o x) C := by
  constructor
  · intro hne
    by_contra hj
    rw [mem_markedSupport] at hj
    push Not at hj
    apply hne
    have hsat : satellite L C T j = 0 := by
      unfold satellite
      rw [Finset.sum_eq_zero fun m hm => hj.2 m (hT hm),
        Finset.sum_eq_zero fun m hm => hj.2 m (Finset.mem_sdiff.1 hm).1, sub_zero]
    unfold markedDensity
    rw [hj.1, hsat]
    simp
  · intro hj
    by_cases hm0 : dipoleMark o x j = 0
    · obtain ⟨m, hmC, hmj⟩ := (mem_markedSupport.1 hj).resolve_left (by simpa using hm0)
      have hother : ∀ m' ∈ C, m' ≠ m → m' j = 0 := by
        intro m' hm' hne
        by_contra h
        exact Set.disjoint_left.1 (hdisj m' hm' m hmC hne) h hmj
      have hsum : ∀ U ⊆ C, ∑ m' ∈ U, m' j = if m ∈ U then m j else 0 := by
        intro U hU
        rw [Finset.sum_congr rfl fun m' hm' => (show m' j = if m' = m then m j else 0 by
          split_ifs with h
          · rw [h]
          · exact hother m' (hU hm') h), Finset.sum_ite_eq']
      have hsat : satellite L C T j = (if m ∈ T then m j else 0) -
          (if m ∈ C \ T then m j else 0) := by
        unfold satellite
        rw [hsum T hT, hsum (C \ T) Finset.sdiff_subset]
      unfold markedDensity
      rw [hm0, Int.cast_zero, mul_zero, zero_add, hsat]
      by_cases hmT : m ∈ T
      · rw [ite_eq_left hmT, ite_eq_right (fun h => (Finset.mem_sdiff.1 h).2 hmT), sub_zero]
        exact_mod_cast hmj
      · rw [ite_eq_right hmT, ite_eq_left (Finset.mem_sdiff.2 ⟨hmC, hmT⟩), zero_sub]
        push_cast
        exact neg_ne_zero.2 (by exact_mod_cast hmj)
    · have hk : dipoleMark o x j = 1 ∨ dipoleMark o x j = -1 := by
        unfold dipoleMark at hm0 ⊢
        by_cases hjo : j = o
        · subst hjo
          simp [hox]
        · by_cases hjx : j = x
          · subst hjx
            simp [hjo]
          · simp [hjo, hjx] at hm0
      have hg := isGapped_mul_add_int (ξ := ξ) hk (satellite L C T j)
      have hne := hg.ne_zero (dipoleGap_pos h0 h1)
      unfold markedDensity
      rwa [mul_comm] at hne


/-- **Zero-mark limit** (FS81 Corollary 2.4, CORE.s7): at `ξ = 0` the marked expansion of
`MarkedT22Step` is an expansion of `∏_j λ_j` itself, with the same (`ξ`-independent) data. -/
theorem markedT22_zero_mark {lam : Fin L × Fin L → ℝ → ℝ} {n : ℕ}
    {N : Fin n → Finset (Fin L × Fin L → ℤ)} {c : Fin n → ℝ}
    {K : Fin n → (Fin L × Fin L → ℤ) → ℝ} {ϱ₀ : ChargeDensity L}
    (h : ∀ (ξ : ℝ) (ψ : Fin L × Fin L → ℝ),
      Real.cos (ξ * ∑ j, ψ j * (ϱ₀ j : ℝ)) * ∏ j, lam j (ψ j) =
        ∑ i, c i * ∑ C ∈ markedClusters boundary L ϱ₀ (N i), ∑ T ∈ C.powerset,
          ((1 / 2) ^ C.card * ∏ m ∈ C, K i m) *
            Real.cos (∑ j, ψ j * markedDensity ξ ϱ₀ (satellite L C T) j) *
            ∏ ϱ ∈ markedRemainder boundary L ϱ₀ (N i) C,
              (1 + K i ϱ * Real.cos (∑ j, ψ j * (ϱ j : ℝ))))
    (ψ : Fin L × Fin L → ℝ) :
    ∏ j, lam j (ψ j) =
      ∑ i, c i * ∑ C ∈ markedClusters boundary L ϱ₀ (N i), ∑ T ∈ C.powerset,
        ((1 / 2) ^ C.card * ∏ m ∈ C, K i m) *
          Real.cos (∑ j, ψ j * (satellite L C T j : ℝ)) *
          ∏ ϱ ∈ markedRemainder boundary L ϱ₀ (N i) C,
            (1 + K i ϱ * Real.cos (∑ j, ψ j * (ϱ j : ℝ))) := by
  have h0 := h 0 ψ
  simp only [zero_mul, Real.cos_zero, one_mul] at h0
  rw [h0]
  unfold markedDensity
  simp only [zero_mul, zero_add]

end KP

section CoverCost

open Classical

variable {boundary : SquareBoundary} {L : ℕ}

/-- The integer proxy `𝟙_X` of a finite set of sites: KP's square covers, separated squares and
cover costs of the marked composite are those of this proxy (all KP geometry is support-based). -/
def supportProxy (X : Finset (Fin L × Fin L)) : ChargeDensity L :=
  fun j => if j ∈ X then 1 else 0

theorem chargeSupport_supportProxy (X : Finset (Fin L × Fin L)) :
    chargeSupport (supportProxy X) = X := by
  ext j
  rw [mem_chargeSupport']
  unfold supportProxy
  split_ifs with h <;> simp [h]

theorem chargeCutoff_mono {ϱ ϱ' : ChargeDensity L} (h1 : 1 ≤ chargeDiameter boundary L ϱ)
    (h2 : 1 ≤ chargeDiameter boundary L ϱ')
    (h : chargeDiameter boundary L ϱ ≤ chargeDiameter boundary L ϱ') :
    chargeCutoff boundary L ϱ h1 ≤ chargeCutoff boundary L ϱ' h2 := by
  unfold chargeCutoff
  apply Nat.ceil_mono
  have hd1 : (1 : ℝ) ≤ chargeDiameter boundary L ϱ := by exact_mod_cast h1
  have hpos : (0 : ℝ) < (chargeCoverScale : ℝ) *
      (chargeDiameter boundary L ϱ : ℝ) ^ chargeCoverExponent := by
    have : (0 : ℝ) < (chargeDiameter boundary L ϱ : ℝ) ^ chargeCoverExponent :=
      Real.rpow_pos_of_pos (by linarith) _
    have hM : (0 : ℝ) < chargeCoverScale := by norm_num [chargeCoverScale]
    positivity
  refine Real.logb_le_logb_of_le (by norm_num) hpos ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast h)
    (by norm_num [chargeCoverExponent])) (by norm_num [chargeCoverScale])

/-- A scale below the cutoff `n(ϱ) = ⌈log₂(M d(ϱ)^α)⌉` satisfies `2^k < 2 M d(ϱ)^α`. -/
theorem two_pow_lt_of_le_chargeCutoff {ϱ : ChargeDensity L}
    (h1 : 1 ≤ chargeDiameter boundary L ϱ) {k : ℕ} (hk : k ≤ chargeCutoff boundary L ϱ h1) :
    (2 : ℝ) ^ k < 2 * ((chargeCoverScale : ℝ) *
      (chargeDiameter boundary L ϱ : ℝ) ^ chargeCoverExponent) := by
  set w := (chargeCoverScale : ℝ) * (chargeDiameter boundary L ϱ : ℝ) ^ chargeCoverExponent
    with hw
  have hd1 : (1 : ℝ) ≤ chargeDiameter boundary L ϱ := by exact_mod_cast h1
  have hwpos : 0 < w := by
    have : (0 : ℝ) < (chargeDiameter boundary L ϱ : ℝ) ^ chargeCoverExponent :=
      Real.rpow_pos_of_pos (by linarith) _
    have hM : (0 : ℝ) < chargeCoverScale := by norm_num [chargeCoverScale]
    positivity
  have hceil : (k : ℝ) < Real.logb 2 w + 1 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 w by
      apply Real.logb_nonneg (by norm_num)
      have hM : (1 : ℝ) ≤ chargeCoverScale := by norm_num [chargeCoverScale]
      have : (1 : ℝ) ≤ (chargeDiameter boundary L ϱ : ℝ) ^ chargeCoverExponent :=
        Real.one_le_rpow hd1 (by norm_num [chargeCoverExponent])
      nlinarith)
    have hk' : (k : ℝ) ≤ (chargeCutoff boundary L ϱ h1 : ℝ) := by exact_mod_cast hk
    unfold chargeCutoff at hk'
    linarith
  have h2 : (2 : ℝ) ^ ((k : ℝ) - 1) < w := by
    calc (2 : ℝ) ^ ((k : ℝ) - 1) < (2 : ℝ) ^ (Real.logb 2 w) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = w := Real.rpow_logb (by norm_num) (by norm_num) hwpos
  have h3 : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ ((k : ℝ) - 1) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one]
    ring
  rw [h3]
  linarith

/-- A KP square of scale `k` meets at most `289` members of a scale-separated ensemble that are
below their cutoff at scale `k` (a packing count, as in KP (4.20)). -/
theorem card_members_meeting_square_le (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) (hb : IsScaleSeparated boundary L N) (k : ℕ)
    {Q : Finset (Fin L × Fin L)} (hQ : Q ∈ kpSquares boundary L k)
    {C' : Finset (ChargeDensity L)} (hC' : C' ⊆ N)
    (hcut : ∀ m ∈ C', (2 : ℝ) ^ k < 2 * ((chargeCoverScale : ℝ) *
      (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent))
    (hmeet : ∀ m ∈ C', (Q ∩ chargeSupport m).Nonempty) :
    C'.card ≤ 289 := by
  rcases C'.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  have : Nonempty (Fin L × Fin L) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  choose! p hp using hmeet
  have hpQ : ∀ m ∈ C', p m ∈ Q := fun m hm => (Finset.mem_inter.1 (hp m hm)).1
  have hpS : ∀ m ∈ C', p m ∈ chargeSupport m := fun m hm => (Finset.mem_inter.1 (hp m hm)).2
  have hinj : Set.InjOn p (C' : Set (ChargeDensity L)) := by
    intro m hm m' hm' heq
    by_contra hne'
    have hdisj := hens.2 m (hC' hm) m' (hC' hm') hne'
    have h1 : p m ∈ Function.support m := mem_chargeSupport'.1 (hpS m hm)
    have h2 : p m ∈ Function.support m' := by
      rw [heq]
      exact mem_chargeSupport'.1 (hpS m' hm')
    exact Set.disjoint_left.1 hdisj h1 h2
  rw [← Finset.card_image_of_injOn hinj]
  obtain ⟨m₀, hm₀⟩ := hne
  set y₀ := p m₀ with hy₀
  have hdiamQ : squareDiameter boundary L Q ≤ 2 * (2 ^ k - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L k Q hQ
    | periodic => exact periodic_squareDiameter_le L k hL Q hQ
  have hR : ∀ q ∈ C'.image p, latticeDistance boundary L q y₀ ≤ 2 * (2 ^ k - 1) := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
    exact (latticeDistance_le_squareDiameter_of_mem boundary L Q _ _ (hpQ m hm)
      (hpQ m₀ hm₀)).trans hdiamQ
  -- distinct points are more than `2^{k−1}` apart
  have hsep : ∀ m ∈ C', ∀ m' ∈ C', m ≠ m' →
      (2 : ℝ) ^ k < 2 * (latticeDistance boundary L (p m) (p m') : ℝ) := by
    intro m hm m' hm' hne'
    have hb1 := hb.1 m (hC' hm) m' (hC' hm') hne'
    have hdist : densityDistance boundary L m m' ≤ latticeDistance boundary L (p m) (p m') :=
      squareDistance_le_latticeDistance_of_mem boundary L _ _ _ _ (hpS m hm) (hpS m' hm')
    have hα : (0 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
    have hmin : (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L m) (chargeDiameter boundary L m') : ℕ) : ℝ) ^
          chargeCoverExponent =
        min ((chargeCoverScale : ℝ) * (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent)
          ((chargeCoverScale : ℝ) * (chargeDiameter boundary L m' : ℝ) ^ chargeCoverExponent) := by
      rcases le_total (chargeDiameter boundary L m) (chargeDiameter boundary L m') with h | h
      · rw [min_eq_left h, min_eq_left]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast h)
          hα) (by norm_num [chargeCoverScale])
      · rw [min_eq_right h, min_eq_right]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast h)
          hα) (by norm_num [chargeCoverScale])
    have h1 := hcut m hm
    have h2 := hcut m' hm'
    have hlt : (2 : ℝ) ^ k < 2 * (densityDistance boundary L m m' : ℝ) := by
      rw [hmin] at hb1
      have : (2 : ℝ) ^ k < 2 * min ((chargeCoverScale : ℝ) *
          (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent)
          ((chargeCoverScale : ℝ) * (chargeDiameter boundary L m' : ℝ) ^ chargeCoverExponent) := by
        rcases min_cases ((chargeCoverScale : ℝ) *
            (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent)
            ((chargeCoverScale : ℝ) * (chargeDiameter boundary L m' : ℝ) ^ chargeCoverExponent)
          with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
      linarith
    have : (densityDistance boundary L m m' : ℝ) ≤ latticeDistance boundary L (p m) (p m') := by
      exact_mod_cast hdist
    linarith
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- scales `0, 1`: points are pairwise at distance `≥ 2^k`, inside a square of side `2^k`
    interval_cases k
    · -- side one: every point is the statement point, so at most one member meets `Q`
      have hle : (C'.image p).card ≤ (2 * (2 * (2 ^ 0 - 1)) / 1 + 1) ^ 2 := by
        refine card_le_of_pairwise_latticeDistance_ge boundary hL y₀ _ 1 le_rfl _ hR ?_
        intro q hq q' hq' hqq'
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
        obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hq'
        have hz : latticeDistance boundary L (p m) (p m') = 0 := by
          have := (latticeDistance_le_squareDiameter_of_mem boundary L Q _ _ (hpQ m hm)
            (hpQ m' hm')).trans hdiamQ
          simpa using this
        exfalso
        apply hqq'
        cases boundary with
        | free =>
          exact ((squareFree_connected L hL).preconnected _ _).dist_eq_zero_iff.1 hz
        | periodic =>
          exact ((squarePeriodic_connected L hL).preconnected _ _).dist_eq_zero_iff.1 hz
      norm_num at hle
      omega
    · have hle : (C'.image p).card ≤ (2 * (2 * (2 ^ 1 - 1)) / 1 + 1) ^ 2 := by
        refine card_le_of_pairwise_latticeDistance_ge boundary hL y₀ _ 1 le_rfl _ hR ?_
        intro q hq q' hq' hqq'
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
        obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hq'
        have hmm' : m ≠ m' := fun h => hqq' (by rw [h])
        have h2 : 1 < latticeDistance boundary L (p m) (p m') := by
          have h := hsep m hm m' hm' hmm'
          norm_num at h
          exact_mod_cast h
        omega
      norm_num at hle
      omega
  · -- scales `k ≥ 2`: spacing `2^{k−1}`, radius `2(2^k − 1)`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hjk : j + 2 - 2 = j := by omega
    have hle : (C'.image p).card ≤ (2 * (2 * (2 ^ (j + 2) - 1)) / 2 ^ j + 1) ^ 2 := by
      refine card_le_of_pairwise_latticeDistance_ge boundary hL y₀ _ (2 ^ j)
        (Nat.one_le_two_pow) _ hR ?_
      intro q hq q' hq' hqq'
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hq'
      have hmm' : m ≠ m' := fun h => hqq' (by rw [h])
      have h := hsep m hm m' hm' hmm'
      have hpow : (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j := by
        rw [pow_add]
        ring
      have : (2 * 2 ^ j : ℝ) < latticeDistance boundary L (p m) (p m') := by
        rw [hpow] at h
        linarith
      have : 2 * 2 ^ j < latticeDistance boundary L (p m) (p m') := by exact_mod_cast this
      omega
    have hbound : 2 * (2 * (2 ^ (j + 2) - 1)) / 2 ^ j + 1 ≤ 17 := by
      have hk2 : 2 ^ (j + 2) = 4 * 2 ^ j := by
        rw [pow_add]
        ring
      have hpos : 0 < 2 ^ j := Nat.two_pow_pos _
      have : 2 * (2 * (2 ^ (j + 2) - 1)) / 2 ^ j ≤ 16 := by
        rw [Nat.div_le_iff_le_mul_add_pred hpos, hk2]
        omega
      omega
    calc (C'.image p).card ≤ (2 * (2 * (2 ^ (j + 2) - 1)) / 2 ^ j + 1) ^ 2 := hle
      _ ≤ 17 ^ 2 := Nat.pow_le_pow_left hbound 2
      _ = 289 := by norm_num

/-- **Per-scale cover subadditivity of a cluster**: the members below their cutoff at scale `k`
need at most `289` times as many scale-`k` squares as the cluster support `X`. -/
theorem sum_squareCoverNumber_le (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) (hb : IsScaleSeparated boundary L N)
    {C : Finset (ChargeDensity L)} (hC : C ⊆ N) {X : Finset (Fin L × Fin L)}
    (hX : ∀ m ∈ C, chargeSupport m ⊆ X) (k : ℕ) :
    ∑ m ∈ C.filter (fun m => (2 : ℝ) ^ k < 2 * ((chargeCoverScale : ℝ) *
        (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent)),
      squareCoverNumber boundary L k m ≤
        289 * squareCoverNumber boundary L k (supportProxy X) := by
  obtain ⟨Qs, hQs⟩ := exists_minimumSquareCover boundary L k (supportProxy X)
  set C' := C.filter (fun m => (2 : ℝ) ^ k < 2 * ((chargeCoverScale : ℝ) *
      (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent)) with hC'
  have hcov : ∀ m ∈ C', squareCoverNumber boundary L k m ≤
      (Qs.filter fun Q => (Q ∩ chargeSupport m).Nonempty).card := by
    intro m hm
    apply squareCoverNumber_le
    refine ⟨(Finset.filter_subset _ _).trans hQs.1.1, fun x hx => ?_⟩
    have hxX : x ∈ chargeSupport (supportProxy X) := by
      rw [chargeSupport_supportProxy]
      exact hX m (Finset.mem_filter.1 hm).1 hx
    obtain ⟨Q, hQ, hxQ⟩ := hQs.1.2 x hxX
    exact ⟨Q, Finset.mem_filter.2 ⟨hQ, x, Finset.mem_inter.2 ⟨hxQ, hx⟩⟩, hxQ⟩
  calc ∑ m ∈ C', squareCoverNumber boundary L k m
      ≤ ∑ m ∈ C', (Qs.filter fun Q => (Q ∩ chargeSupport m).Nonempty).card :=
        Finset.sum_le_sum hcov
    _ = ∑ Q ∈ Qs, (C'.filter fun m => (Q ∩ chargeSupport m).Nonempty).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _Q ∈ Qs, 289 := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        refine card_members_meeting_square_le hL hens hb k (hQs.1.1 hQ)
          ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans hC))
          (fun m hm => (Finset.mem_filter.1 (Finset.mem_filter.1 hm).1).2)
          (fun m hm => (Finset.mem_filter.1 hm).2)
    _ = 289 * squareCoverNumber boundary L k (supportProxy X) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm,
          card_eq_squareCoverNumber_of_isMinimumSquareCover boundary L k _ Qs hQs]

/-- **Cover-cost subadditivity of a cluster** (the entropy estimate behind FS81 (2.30)):
`∑_{m ∈ C} A(m) ≤ 289 · A(X)` for members of a scale-separated ensemble supported in `X`,
`d(X) ≥ 1`. -/
theorem sum_chargeCoverCost_le (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) (hb : IsScaleSeparated boundary L N)
    {C : Finset (ChargeDensity L)} (hC : C ⊆ N) {X : Finset (Fin L × Fin L)}
    (hX : ∀ m ∈ C, chargeSupport m ⊆ X) (hXd : 1 ≤ squareDiameter boundary L X) :
    ∑ m ∈ C, chargeCoverCost boundary L m ≤
      289 * chargeCoverCost boundary L (supportProxy X) := by
  have hdX : chargeDiameter boundary L (supportProxy X) = squareDiameter boundary L X := by
    unfold chargeDiameter
    rw [chargeSupport_supportProxy]
  have hdX1 : 1 ≤ chargeDiameter boundary L (supportProxy X) := hdX ▸ hXd
  set nX := chargeCutoff boundary L (supportProxy X) hdX1 with hnX
  have hcostX : chargeCoverCost boundary L (supportProxy X) =
      ∑ k ∈ Finset.range (nX + 1), squareCoverNumber boundary L k (supportProxy X) := by
    have hne : ¬ chargeDiameter boundary L (supportProxy X) = 0 := by omega
    unfold chargeCoverCost
    rw [dite_eq_right hne]
  let f : ℕ → ChargeDensity L → ℕ := fun k m =>
    if (2 : ℝ) ^ k < 2 * ((chargeCoverScale : ℝ) *
      (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent)
    then squareCoverNumber boundary L k m else 0
  have hm : ∀ m ∈ C, chargeCoverCost boundary L m ≤ ∑ k ∈ Finset.range (nX + 1), f k m := by
    intro m hmC
    unfold chargeCoverCost
    split_ifs with hd0
    · exact Nat.zero_le _
    · have hd1 : 1 ≤ chargeDiameter boundary L m := Nat.one_le_iff_ne_zero.mpr hd0
      have hdm : chargeDiameter boundary L m ≤ chargeDiameter boundary L (supportProxy X) := by
        rw [hdX]
        exact squareDiameter_mono boundary L (hX m hmC)
      have hcut := chargeCutoff_mono hd1 hdX1 hdm
      calc ∑ k ∈ Finset.range (chargeCutoff boundary L m _ + 1),
            squareCoverNumber boundary L k m
          = ∑ k ∈ Finset.range (chargeCutoff boundary L m hd1 + 1), f k m := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hk' : k ≤ chargeCutoff boundary L m hd1 := Nat.lt_succ_iff.1
              (Finset.mem_range.1 hk)
            simp only [f]
            rw [ite_eq_left (two_pow_lt_of_le_chargeCutoff hd1 hk')]
        _ ≤ ∑ k ∈ Finset.range (nX + 1), f k m :=
            Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
  calc ∑ m ∈ C, chargeCoverCost boundary L m
      ≤ ∑ m ∈ C, ∑ k ∈ Finset.range (nX + 1), f k m := Finset.sum_le_sum hm
    _ = ∑ k ∈ Finset.range (nX + 1), ∑ m ∈ C, f k m := Finset.sum_comm
    _ = ∑ k ∈ Finset.range (nX + 1), ∑ m ∈ C.filter (fun m => (2 : ℝ) ^ k <
          2 * ((chargeCoverScale : ℝ) * (chargeDiameter boundary L m : ℝ) ^
            chargeCoverExponent)), squareCoverNumber boundary L k m := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.range (nX + 1), 289 * squareCoverNumber boundary L k (supportProxy X) :=
        Finset.sum_le_sum fun k _ => sum_squareCoverNumber_le hL hens hb hC hX k
    _ = 289 * chargeCoverCost boundary L (supportProxy X) := by
        rw [hcostX, Finset.mul_sum]

/-- **FS81 (2.30) for the cluster composite**, in KP's functional: for a neutral cluster of a
KP ensemble with property (d),
`|2^{−|C|} ∏_C K| ≤ 2^{−|C|} e^{289 D₂ A(X)} ∏_{m ∈ C} ∏_{j ∈ supp m} e^{m(j)²} |λ̂_j(|m(j)|)|`,
with `X = supp ϱ₀ ∪ ⋃ C` the composite support (FS81's `s(ϱ₀, ϱ^𝒩)`). -/
theorem abs_clusterWeight_le_coverCost (hL : 1 < L) {N : Finset (ChargeDensity L)}
    {K : ChargeDensity L → ℝ} {D₂ : ℝ} (hD₂ : 0 ≤ D₂) {lamHat : Fin L × Fin L → ℕ → ℝ}
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    (hens : IsChargeEnsemble N) (hb : IsScaleSeparated boundary L N) {ϱ₀ : ChargeDensity L}
    {C : Finset (ChargeDensity L)} (hC : C ⊆ N) (hCn : ∀ m ∈ C, ∑ j, m j = 0)
    (hXd : 1 ≤ squareDiameter boundary L (markedSupport L ϱ₀ C)) :
    |(1 / 2) ^ C.card * ∏ m ∈ C, K m| ≤
      (1 / 2) ^ C.card * Real.exp (289 * D₂ *
          chargeCoverCost boundary L (supportProxy (markedSupport L ϱ₀ C))) *
        ∏ m ∈ C, ∏ j ∈ chargeSupport m, Real.exp ((m j : ℝ) ^ 2) * |lamHat j (m j).natAbs| := by
  refine (abs_clusterWeight_le hd hC hCn).trans ?_
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← mul_assoc]
  have hsum := sum_chargeCoverCost_le hL hens hb hC
    (fun m hm => chargeSupport_subset_markedSupport_of_mem hm) hXd
  have hsumR : ∑ m ∈ C, D₂ * (chargeCoverCost boundary L m : ℝ) ≤
      289 * D₂ * chargeCoverCost boundary L (supportProxy (markedSupport L ϱ₀ C)) := by
    rw [← Finset.mul_sum]
    have : (∑ m ∈ C, (chargeCoverCost boundary L m : ℝ)) ≤
        289 * (chargeCoverCost boundary L (supportProxy (markedSupport L ϱ₀ C)) : ℝ) := by
      exact_mod_cast hsum
    nlinarith
  have hP : 0 ≤ ∏ m ∈ C, ∏ j ∈ chargeSupport m,
      Real.exp ((m j : ℝ) ^ 2) * |lamHat j (m j).natAbs| :=
    Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 hsumR) (by positivity)) hP

/-- The Coulomb-B composite has diameter at least one (it contains `o ≠ x`). -/
theorem one_le_squareDiameter_markedSupport_dipole (hL : 1 < L) {o x : Fin L × Fin L}
    (hox : o ≠ x) (C : Finset (ChargeDensity L)) :
    1 ≤ squareDiameter boundary L (markedSupport L (dipoleMark o x) C) := by
  have ho : o ∈ markedSupport L (dipoleMark o x) C :=
    chargeSupport_subset_markedSupport _ C (mem_chargeSupport'.2 (by simp [dipoleMark, hox]))
  have hx : x ∈ markedSupport L (dipoleMark o x) C :=
    chargeSupport_subset_markedSupport _ C
      (mem_chargeSupport'.2 (by simp [dipoleMark, Ne.symm hox]))
  exact (one_le_latticeDistance_of_ne boundary hL hox).trans
    (latticeDistance_le_squareDiameter_of_mem boundary L _ o x ho hx)

end CoverCost

end FroehlichSpencer.BKT.Generic.Marked
