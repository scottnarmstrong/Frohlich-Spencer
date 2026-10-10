/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Renormalization.ChargeLayer
public import FroehlichSpencer.BKT.Generic.Moment.Aggregate
public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter
import Mathlib.Algebra.Order.Chebyshev

/-!
# Obstructions to running the KP charge layer in the wired metric of `squareZero L`

The `squareZero L` is the
pinned carrier of FS81 (1.35): the bounded faces `Fin L × Fin L` and the wired vertex `none`, to
which every boundary face is joined (`WiredAdapter`).

In its graph metric every boundary face is at
distance `1` from `none`.

This module records three precise facts which show that KP's
square-domain counts do not transfer to this metric.

* **boundary geometry** (`not_exists_layerWave_of_supp_subset_plus`, general multigraph): if a neutral density
  `ϱ ≠ 0` lies inside the enlarged domain `D⁺(ϱ′)` of a comparable density `ϱ′` of the same
  ensemble, no graded spin wave of `ϱ` relative to that ensemble satisfies the translation clauses
  `HasLayerWave`.

On `squareZero` (`not_exists_layerWave_two_boundary_charges`): two root dipoles
  `q(δ_x − δ_none)`, `q′(δ_y − δ_none)` at boundary faces cannot share an ensemble when `ϱ′` is
  centred in its support (KP's center convention), because `D(ϱ′)` contains `none`, whose neighbours
  are all the boundary faces.
* **** (`not_exists_uniform_hvol_squareZero`): KP's/exponential-moment's edge-volume bound
  `|edgesTouching(D_j(ϱ))| ≤ Kv (d(ϱ) + 1)²` has no uniform constant on the family `squareZero L`.
* **** (`energy_ge_of_root_profile`): a profile equal to `1` at the wired vertex and `0` at depth
  `> R` along the bottom side has energy at least `L/(R+1)` (the `L` column paths from `none` are
  edge-disjoint).

KP's `O(1)`-energy profiles around separated cover sets therefore fail for sets
  containing (or reaching) the wired vertex at scales `≪ L`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Wired

open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.PinnedCharges

/-! ## boundary geometry: a density inside the enlarged domain of a comparable one has no layer wave -/

/-- **boundary geometry.** A neutral density `ϱ ≠ 0` contained in `D⁺(ϱ′)` for a comparable `ϱ′` of the
ensemble `N₀` has no graded spin wave relative to `N₀` with the spin-wave clauses: every piece is constant
on `supp ϱ` (`const_plus`), so it pairs to `0` with `ϱ`, contradicting `|charge| ≥ 1`; and without
pieces the base clause fails. -/
theorem not_exists_layerWave_of_supp_subset_plus {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (A : (V → ℤ) → ℝ) (D₁ α K₀ K₁ : ℝ) {ϱ ϱ' : V → ℤ} (hϱ0 : ϱ ≠ 0)
    (hneutral : ∑ j, ϱ j = 0) (hcomp : ϱ' ∈ G.comparableDensities N₀ ϱ)
    (hsub : ∀ j, ϱ j ≠ 0 → j ∈ G.densityDomainPlus ϱ' (centerOf ϱ')) :
    ¬ ∃ Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ϱ,
      HasLayerWave G N₀ centerOf A D₁ α K₀ K₁ ϱ Wv := by
  rintro ⟨Wv, -, -, -, hbase, -⟩
  let _ := Wv.finite
  have hnone : ∀ t : Wv.ι, False := by
    intro t
    obtain ⟨c, hc⟩ := Wv.const_plus t ϱ' hcomp
    have h0 : Multigraph.pairing (Wv.piece t) (fun j => (ϱ j : ℝ)) = 0 := by
      unfold Multigraph.pairing
      have hterm : ∀ j, Wv.piece t j * (ϱ j : ℝ) = c * (ϱ j : ℝ) := by
        intro j
        by_cases hj : ϱ j = 0
        · simp [hj]
        · rw [hc j (hsub j hj)]
      rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum]
      have hs : ∑ j, (ϱ j : ℝ) = 0 := by exact_mod_cast hneutral
      rw [hs, mul_zero]
    have h1 := Wv.charge_ge_one t
    rw [← Wv.pairing t, h0, abs_zero] at h1
    linarith
  have h2 := hbase.trans (le_of_eq (Finset.sum_eq_zero fun t _ => (hnone t).elim))
  obtain ⟨j, hj⟩ : ∃ j, ϱ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hϱ0 (funext h)
  have hpos : 0 < ∑ j, |(ϱ j : ℝ)| :=
    lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hj))
      (Finset.single_le_sum (f := fun j => |(ϱ j : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j))
  linarith

/-! ## Root dipoles on `squareZero` -/

variable {L : ℕ}

/-- The root dipole `q(δ_x − δ_none)`: a charge `q` at the bounded face `x`, neutralized at the
wired vertex. -/
def rootDipole (x : Fin L × Fin L) (q : ℤ) : Option (Fin L × Fin L) → ℤ :=
  fun j => if j = some x then q else if j = none then -q else 0

theorem rootDipole_ne_zero_iff (x : Fin L × Fin L) {q : ℤ} (hq : q ≠ 0)
    (j : Option (Fin L × Fin L)) : rootDipole x q j ≠ 0 ↔ j = some x ∨ j = none := by
  unfold rootDipole
  by_cases h1 : j = some x
  · simp [h1, hq]
  · by_cases h2 : j = none
    · simp [h2, hq]
    · simp [h1, h2]

theorem sum_rootDipole (x : Fin L × Fin L) (q : ℤ) : ∑ j, rootDipole x q j = 0 := by
  rw [Fintype.sum_option]
  simp only [rootDipole, reduceCtorEq, ite_false, ite_true]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    have : (some y : Option (Fin L × Fin L)) ≠ some x := fun h => hy (Option.some_injective _ h)
    simp [this]
  · simp

theorem rootDipole_ne_zero (x : Fin L × Fin L) {q : ℤ} (hq : q ≠ 0) : rootDipole x q ≠ 0 := by
  intro h
  have := congrFun h (some x)
  simp [rootDipole, hq] at this

/-- A bounded face of depth one is adjacent to the wired vertex. -/
theorem adj_none_of_depth_one (hL : 1 < L) {x : Fin L × Fin L} (hx : siteBoundaryDepth x = 1) :
    (squareZero L).toSimpleGraph.Adj (some x) none := by
  rw [← SimpleGraph.dist_eq_one_iff_adj, squareZero_distance_root_eq_siteBoundaryDepth hL, hx]

theorem densityDiameter_rootDipole (hL : 1 < L) {x : Fin L × Fin L}
    (hx : siteBoundaryDepth x = 1) {q : ℤ} (hq : q ≠ 0) :
    (squareZero L).densityDiameter (rootDipole x q) = 1 := by
  classical
  have hdist : (squareZero L).toSimpleGraph.dist (some x) none = 1 := by
    rw [squareZero_distance_root_eq_siteBoundaryDepth hL, hx]
  have hdist' : (squareZero L).toSimpleGraph.dist none (some x) = 1 := by
    rw [SimpleGraph.dist_comm, hdist]
  unfold Multigraph.densityDiameter
  refine le_antisymm (Finset.sup_le fun p hp => ?_) ?_
  · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      rootDipole_ne_zero_iff x hq] at hp
    rcases hp with ⟨h1 | h1, h2 | h2⟩ <;> rw [h1, h2] <;> simp [hdist, hdist']
  · have hmem : ((some x, none) : Option (Fin L × Fin L) × Option (Fin L × Fin L)) ∈
        (Finset.univ.filter fun j => rootDipole x q j ≠ 0) ×ˢ
          (Finset.univ.filter fun j => rootDipole x q j ≠ 0) := by
      simp [rootDipole_ne_zero_iff x hq]
    have := Finset.le_sup (f := fun p => (squareZero L).toSimpleGraph.dist p.1 p.2) hmem
    simpa [hdist] using this

/-- **boundary geometry on `squareZero`.** Two root dipoles at boundary faces cannot share an ensemble when the
second is centred in its support: the first has no layer wave relative to the ensemble. -/
theorem not_exists_layerWave_two_boundary_charges (hL : 1 < L) {x y : Fin L × Fin L}
    (hx : siteBoundaryDepth x = 1) (hy : siteBoundaryDepth y = 1) {q q' : ℤ} (hq : q ≠ 0)
    (hq' : q' ≠ 0) (N₀ : Finset (Option (Fin L × Fin L) → ℤ)) (h' : rootDipole y q' ∈ N₀)
    (hne : rootDipole x q ≠ rootDipole y q')
    (centerOf : (Option (Fin L × Fin L) → ℤ) → Option (Fin L × Fin L))
    (hc : rootDipole y q' (centerOf (rootDipole y q')) ≠ 0)
    (A : (Option (Fin L × Fin L) → ℤ) → ℝ) (D₁ α K₀ K₁ : ℝ) :
    ¬ ∃ Wv : GradedSpinWave.{0, 0, 0} (squareZero L) N₀ centerOf (rootDipole x q),
      HasLayerWave (squareZero L) N₀ centerOf A D₁ α K₀ K₁ (rootDipole x q) Wv := by
  classical
  refine not_exists_layerWave_of_supp_subset_plus _ N₀ centerOf A D₁ α K₀ K₁
    (ϱ' := rootDipole y q') (rootDipole_ne_zero x hq) (sum_rootDipole x q) ?_ ?_
  · rw [Multigraph.mem_comparableDensities, densityDiameter_rootDipole hL hy hq',
      densityDiameter_rootDipole hL hx hq]
    exact ⟨h', by norm_num, hne⟩
  · -- `none ∈ D(ϱ′)`, and every boundary face is a neighbour of `none`
    have hnoneD : (none : Option (Fin L × Fin L)) ∈
        (squareZero L).densityDomain (rootDipole y q') (centerOf (rootDipole y q')) := by
      show (squareZero L).toSimpleGraph.dist none (centerOf (rootDipole y q')) <
        2 * (squareZero L).densityDiameter (rootDipole y q')
      rw [densityDiameter_rootDipole hL hy hq']
      rcases (rootDipole_ne_zero_iff y hq' _).mp hc with h | h <;> rw [h]
      · rw [SimpleGraph.dist_comm, squareZero_distance_root_eq_siteBoundaryDepth hL, hy]
        norm_num
      · simp
    intro j hj
    rcases (rootDipole_ne_zero_iff x hq j).mp hj with h | h <;> rw [h]
    · exact ⟨none, hnoneD, Or.inr (adj_none_of_depth_one hL hx)⟩
    · exact ⟨none, hnoneD, Or.inl rfl⟩

/-! ##  no uniform edge-volume bound on `squareZero` -/

/-- A face of the bottom row has depth one. -/
theorem siteBoundaryDepth_bottom (i : Fin L) (h0 : 0 < L) :
    siteBoundaryDepth ((i, ⟨0, h0⟩) : Fin L × Fin L) = 1 := by
  unfold siteBoundaryDepth
  have := i.2
  simp only
  omega

/-- A boundary edge at the bottom face of column `i`. -/
theorem exists_bottom_edge (hL : 1 < L) (i : Fin L) :
    ∃ e : SquareZeroBond L, ((squareZero L).src e = some (i, ⟨0, by omega⟩) ∧
      (squareZero L).tgt e = none) ∨
      ((squareZero L).src e = none ∧ (squareZero L).tgt e = some (i, ⟨0, by omega⟩)) := by
  have hadj := adj_none_of_depth_one hL (siteBoundaryDepth_bottom i (by omega))
  rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj.2 with ⟨e, he⟩ | ⟨e, he⟩
  · exact ⟨e, he⟩
  · exact ⟨e, he.symm⟩

/-- The chosen bottom boundary edge of column `i`. -/
def bottomEdge (hL : 1 < L) (i : Fin L) : SquareZeroBond L :=
  Classical.choose (exists_bottom_edge hL i)

theorem bottomEdge_spec (hL : 1 < L) (i : Fin L) :
    ((squareZero L).src (bottomEdge hL i) = some (i, ⟨0, by omega⟩) ∧
      (squareZero L).tgt (bottomEdge hL i) = none) ∨
      ((squareZero L).src (bottomEdge hL i) = none ∧
        (squareZero L).tgt (bottomEdge hL i) = some (i, ⟨0, by omega⟩)) :=
  Classical.choose_spec (exists_bottom_edge hL i)

theorem bottomEdge_injective (hL : 1 < L) : Function.Injective (bottomEdge hL) := by
  intro i i' h
  have h1 := bottomEdge_spec hL i
  have h2 := bottomEdge_spec hL i'
  rw [h] at h1
  rcases h1 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h2 with ⟨c, d⟩ | ⟨c, d⟩
  · have := a.symm.trans c
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  · rw [a] at c; exact absurd c (by simp)
  · rw [a] at c; exact absurd c (by simp)
  · have := b.symm.trans d
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1

/-- **.** No constant `Kv` bounds the edges touching the KP domains on every `squareZero L` by
`Kv (d + 1)²`: the root dipole at a bottom face has `d = 1`, its domain about `none` contains
`none`, and the `L` bottom boundary edges all touch it. -/
theorem not_exists_uniform_hvol_squareZero :
    ¬ ∃ Kv : ℝ, ∀ L : ℕ, 1 < L → ∀ (ρ : Option (Fin L × Fin L) → ℤ) (j : Option (Fin L × Fin L)),
      ((edgesTouching (squareZero L) ((squareZero L).densityDomain ρ j)).card : ℝ) ≤
        Kv * (((squareZero L).densityDiameter ρ : ℝ) + 1) ^ 2 := by
  classical
  rintro ⟨Kv, hKv⟩
  set L : ℕ := ⌈4 * Kv⌉₊ + 2 with hLdef
  have hL : 1 < L := by omega
  have h0 : 0 < L := by omega
  set x : Fin L × Fin L := (⟨0, h0⟩, ⟨0, h0⟩)
  have hx : siteBoundaryDepth x = 1 := siteBoundaryDepth_bottom _ h0
  have h := hKv L hL (rootDipole x 1) none
  rw [densityDiameter_rootDipole hL hx one_ne_zero] at h
  -- the bottom edges all touch the domain
  have hsub : (Finset.univ.image (bottomEdge hL)) ⊆
      edgesTouching (squareZero L) ((squareZero L).densityDomain (rootDipole x 1) none) := by
    intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    rw [mem_edgesTouching]
    have hnone : (none : Option (Fin L × Fin L)) ∈
        (squareZero L).densityDomain (rootDipole x 1) none := by
      show (squareZero L).toSimpleGraph.dist none none <
        2 * (squareZero L).densityDiameter (rootDipole x 1)
      rw [densityDiameter_rootDipole hL hx one_ne_zero]
      simp
    rcases bottomEdge_spec hL i with ⟨-, ht⟩ | ⟨hs, -⟩
    · exact Or.inr (by rw [ht]; exact hnone)
    · exact Or.inl (by rw [hs]; exact hnone)
  have hcard : (L : ℝ) ≤
      ((edgesTouching (squareZero L) ((squareZero L).densityDomain (rootDipole x 1) none)).card :
        ℝ) := by
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (bottomEdge_injective hL), Finset.card_univ,
      Fintype.card_fin] at this
    exact_mod_cast this
  have hceil : 4 * Kv ≤ (⌈4 * Kv⌉₊ : ℝ) := Nat.le_ceil _
  have hLr : (L : ℝ) = (⌈4 * Kv⌉₊ : ℝ) + 2 := by rw [hLdef]; push_cast; ring
  norm_num at h
  linarith

/-! ##  the energy of a profile separating the wired vertex -/

/-- The bond between the faces `(i, k)` and `(i, k + 1)`. -/
def verticalBond (i : Fin L) (k : ℕ) (hk : k + 1 < L) : SquareZeroBond L :=
  Sum.inl ⟨((i, ⟨k, by omega⟩), (i, ⟨k + 1, hk⟩)), by
    refine ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by simp [Fin.lt_def]⟩), ?_⟩
    simp⟩

theorem src_verticalBond (i : Fin L) (k : ℕ) (hk : k + 1 < L) :
    (squareZero L).src (verticalBond i k hk) = some (i, ⟨k, by omega⟩) := rfl

theorem tgt_verticalBond (i : Fin L) (k : ℕ) (hk : k + 1 < L) :
    (squareZero L).tgt (verticalBond i k hk) = some (i, ⟨k + 1, hk⟩) := rfl

/-- The column path from the wired vertex up to depth `R`: the bottom boundary edge and the `R`
vertical bonds above it. -/
def columnPath (hL : 1 < L) (R : ℕ) (hR : R < L) (i : Fin L) : Finset (SquareZeroBond L) :=
  insert (bottomEdge hL i) (Finset.univ.image fun k : Fin R => verticalBond i k (by omega))

/-- Every edge of the column path of `i` has a bounded endpoint, and all its bounded endpoints lie
in column `i`. -/
theorem columnPath_endpoints (hL : 1 < L) (R : ℕ) (hR : R < L) (i : Fin L)
    (e : SquareZeroBond L) (he : e ∈ columnPath hL R hR i) :
    (∃ z, (squareZero L).src e = some z ∨ (squareZero L).tgt e = some z) ∧
      ∀ z, ((squareZero L).src e = some z ∨ (squareZero L).tgt e = some z) → z.1 = i := by
  rcases Finset.mem_insert.mp he with rfl | he
  · rcases bottomEdge_spec hL i with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · refine ⟨⟨_, Or.inl hs⟩, fun z hz => ?_⟩
      rcases hz with hz | hz
      · rw [hs] at hz; exact (Prod.mk.inj (Option.some_injective _ hz)).1 ▸ rfl
      · rw [ht] at hz; exact absurd hz (by simp)
    · refine ⟨⟨_, Or.inr ht⟩, fun z hz => ?_⟩
      rcases hz with hz | hz
      · rw [hs] at hz; exact absurd hz (by simp)
      · rw [ht] at hz; exact (Prod.mk.inj (Option.some_injective _ hz)).1 ▸ rfl
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp he
    refine ⟨⟨_, Or.inl (src_verticalBond i k (by omega))⟩, fun z hz => ?_⟩
    rcases hz with hz | hz
    · rw [src_verticalBond] at hz; exact (Prod.mk.inj (Option.some_injective _ hz)).1 ▸ rfl
    · rw [tgt_verticalBond] at hz; exact (Prod.mk.inj (Option.some_injective _ hz)).1 ▸ rfl

theorem columnPath_disjoint (hL : 1 < L) (R : ℕ) (hR : R < L) :
    (Set.univ : Set (Fin L)).PairwiseDisjoint (columnPath hL R hR) := by
  intro i _ i' _ hii'
  refine Finset.disjoint_left.mpr fun e he he' => hii' ?_
  obtain ⟨⟨z, hz⟩, h1⟩ := columnPath_endpoints hL R hR i e he
  obtain ⟨-, h2⟩ := columnPath_endpoints hL R hR i' e he'
  exact (h1 z hz).symm.trans (h2 z hz)

theorem card_columnPath_le (hL : 1 < L) (R : ℕ) (hR : R < L) (i : Fin L) :
    (columnPath hL R hR i).card ≤ R + 1 := by
  unfold columnPath
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_image_le (s := (Finset.univ : Finset (Fin R)))
    (f := fun k : Fin R => verticalBond i k (by omega))
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- Along one column path, the total drop of `u` from the wired vertex to depth `R` is at most the
sum of the absolute gradients. -/
theorem abs_drop_le_sum_columnPath (hL : 1 < L) (R : ℕ) (hR : R < L) (i : Fin L)
    (u : Option (Fin L × Fin L) → ℝ) :
    |u none - u (some (i, ⟨R, hR⟩))| ≤
      ∑ e ∈ columnPath hL R hR i, |(squareZero L).grad u e| := by
  classical
  set g : ℕ → ℝ := fun k => if h : k < L then u (some (i, ⟨k, h⟩)) else 0 with hg
  have hnotmem : bottomEdge hL i ∉ Finset.univ.image fun k : Fin R =>
      verticalBond i k (by omega) := by
    intro h
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h
    rcases bottomEdge_spec hL i with ⟨-, ht⟩ | ⟨hs, -⟩
    · rw [← hk, tgt_verticalBond] at ht; exact absurd ht (by simp)
    · rw [← hk, src_verticalBond] at hs; exact absurd hs (by simp)
  have hinj : Function.Injective fun k : Fin R => verticalBond i k (by omega) := by
    intro k k' h
    have := congrArg (squareZero L).src h
    simp only [src_verticalBond, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at this
    exact Fin.ext this.2
  unfold columnPath
  rw [Finset.sum_insert hnotmem, Finset.sum_image fun k _ k' _ h => hinj h]
  -- the bottom edge
  have hb : |u none - g 0| ≤ |(squareZero L).grad u (bottomEdge hL i)| := by
    have hg0 : g 0 = u (some (i, ⟨0, by omega⟩)) := by simp [hg, show 0 < L by omega]
    rw [hg0]
    rcases bottomEdge_spec hL i with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [Multigraph.grad, hs, ht, abs_sub_comm]
    · rw [Multigraph.grad, hs, ht]
  -- the vertical bonds telescope
  have hv : g 0 - g R = ∑ k : Fin R, (squareZero L).grad u (verticalBond i k (by omega)) := by
    have hterm : ∀ k : Fin R, (squareZero L).grad u (verticalBond i k (by omega)) =
        g k - g (k + 1) := fun k => by
      rw [Multigraph.grad, src_verticalBond, tgt_verticalBond]
      simp [hg, show (k : ℕ) < L by omega, show (k : ℕ) + 1 < L by omega]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Fin.sum_univ_eq_sum_range
      (fun k => g k - g (k + 1)), Finset.sum_range_sub']
  have hgR : g R = u (some (i, ⟨R, hR⟩)) := by simp [hg, hR]
  calc |u none - u (some (i, ⟨R, hR⟩))| = |(u none - g 0) + (g 0 - g R)| := by
        rw [hgR]; ring_nf
    _ ≤ |u none - g 0| + |g 0 - g R| := abs_add_le _ _
    _ ≤ |(squareZero L).grad u (bottomEdge hL i)| +
        ∑ k : Fin R, |(squareZero L).grad u (verticalBond i k (by omega))| := by
      refine add_le_add hb ?_
      rw [hv]
      exact Finset.abs_sum_le_sum_abs _ _

/-- ** (isoperimetry at the wired vertex).** A function on the faces of `squareZero L` that is
`1` at the wired vertex and `0` at depth `R` above every bottom face has energy at least
`L/(R + 1)`. -/
theorem energy_ge_of_root_profile (hL : 1 < L) (R : ℕ) (hR : R < L)
    (u : Option (Fin L × Fin L) → ℝ) (hroot : u none = 1)
    (hdeep : ∀ i : Fin L, u (some (i, ⟨R, hR⟩)) = 0) :
    (L : ℝ) / (R + 1) ≤ (squareZero L).energy u := by
  classical
  have hR1 : (0 : ℝ) < R + 1 := by positivity
  have hcol : ∀ i : Fin L, 1 / (R + 1 : ℝ) ≤
      ∑ e ∈ columnPath hL R hR i, (squareZero L).grad u e ^ 2 := by
    intro i
    have h1 := abs_drop_le_sum_columnPath hL R hR i u
    rw [hroot, hdeep i, sub_zero, abs_one] at h1
    have hcs := sq_sum_le_card_mul_sum_sq (s := columnPath hL R hR i)
      (f := fun e => |(squareZero L).grad u e|)
    simp only [sq_abs] at hcs
    have hcard : ((columnPath hL R hR i).card : ℝ) ≤ R + 1 := by
      exact_mod_cast card_columnPath_le hL R hR i
    have hS0 : 0 ≤ ∑ e ∈ columnPath hL R hR i, (squareZero L).grad u e ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [div_le_iff₀ hR1]
    calc (1 : ℝ) ≤ (∑ e ∈ columnPath hL R hR i, |(squareZero L).grad u e|) ^ 2 := by
          nlinarith
      _ ≤ _ := hcs
      _ ≤ (R + 1) * ∑ e ∈ columnPath hL R hR i, (squareZero L).grad u e ^ 2 :=
          mul_le_mul_of_nonneg_right hcard hS0
      _ = _ := mul_comm _ _
  have hsum : ∑ i : Fin L, ∑ e ∈ columnPath hL R hR i, (squareZero L).grad u e ^ 2 ≤
      (squareZero L).energy u := by
    rw [← Finset.sum_biUnion (fun i _ i' _ h => columnPath_disjoint hL R hR (Set.mem_univ i)
      (Set.mem_univ i') h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => sq_nonneg _
  calc (L : ℝ) / (R + 1) = ∑ _i : Fin L, 1 / (R + 1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hcol i
    _ ≤ _ := hsum

end FroehlichSpencer.BKT.Generic.Wired

end
