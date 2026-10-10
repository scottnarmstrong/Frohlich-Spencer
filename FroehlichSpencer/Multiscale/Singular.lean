/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Multiscale.Basic
public import FroehlichSpencer.Multiscale.Clusters
public import FroehlichSpencer.Surface.HamiltonianHermitian
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# The singular-set recursion

FS83 (2.3)-(2.7) : `S_{i+1} = S_i ∖ S_i^g`, where `S_i^g` is the union of all
gentle `2 r_i`-chain clusters of `S_i`.
-/

@[expose] public section

namespace FroehlichSpencer.Multiscale


def IsGentle {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν)) (i : ℕ)
    (v : Site ν → ℝ) (C : Set (Site ν)) : Prop :=
  ∃ hC : C.Finite, DiamLE (siteDist ν) C (scaleD P.K₀ i) ∧
    ∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
      |(hamiltonian_isHermitian ν (blk (thicken hC.toFinset (4 * scaleD P.K₀ i))) v).eigenvalues j
        - P.E|

/--
The gentle part `S_i^g` of a set `S` at scale `i`: the union of all gentle `2 r_i`-chain
clusters of `S` (FS83 (2.3) ).
-/
def gentlePart {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν)) (i : ℕ)
    (v : Site ν → ℝ) (S : Set (Site ν)) : Set (Site ν) :=
  ⋃₀ {C | C ∈ chainClusters (siteDist ν) S (2 * scaleR P.K₀ i) ∧ IsGentle P blk i v C}

/-- The singular sets `S_0 ⊇ S_1 ⊇ …` (FS83 (2.3)), generic in the initial set and block map. -/
def singularSetsGen {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν))
    (S₀ : Set (Site ν)) (v : Site ν → ℝ) : ℕ → Set (Site ν)
  | 0 => S₀
  | i + 1 => singularSetsGen P blk S₀ v i \ gentlePart P blk i v (singularSetsGen P blk S₀ v i)

/-- Infinite-volume singular sets: `S₀ = singular0 P v`, blocks `C̄`. -/
def singularSets {ν : ℕ} (P : Params) (v : Site ν → ℝ) : ℕ → Set (Site ν) :=
  singularSetsGen P id (singular0 P v) v

/-- `Λ`-restricted singular sets: `S₀ ∩ Λ`, blocks `C̄ ∩ Λ` (FS83: `v = +∞` outside `Λ`). -/
def singularSetsIn {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    ℕ → Set (Site ν) :=
  singularSetsGen P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v

variable {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν)) (S₀ : Set (Site ν))
  (v : Site ν → ℝ)

theorem singularSetsGen_succ (i : ℕ) :
    singularSetsGen P blk S₀ v (i + 1) =
      singularSetsGen P blk S₀ v i \ gentlePart P blk i v (singularSetsGen P blk S₀ v i) := rfl

theorem gentlePart_subset (i : ℕ) (S : Set (Site ν)) : gentlePart P blk i v S ⊆ S := by
  rintro y ⟨C, ⟨hC, -⟩, hy⟩
  obtain ⟨x, -, rfl⟩ := hC
  exact chainCluster_subset x hy

theorem singularSetsGen_antitone : Antitone (singularSetsGen P blk S₀ v) :=
  antitone_nat_of_succ_le fun i => by
    rw [singularSetsGen_succ]
    exact Set.sdiff_subset

theorem singularSetsGen_subset_zero (i : ℕ) : singularSetsGen P blk S₀ v i ⊆ S₀ :=
  singularSetsGen_antitone P blk S₀ v (Nat.zero_le i)

theorem mem_singularSetsGen_succ_iff (i : ℕ) (x : Site ν) :
    x ∈ singularSetsGen P blk S₀ v (i + 1) ↔ x ∈ singularSetsGen P blk S₀ v i ∧
      ¬ IsGentle P blk i v
        (chainCluster (siteDist ν) (singularSetsGen P blk S₀ v i) (2 * scaleR P.K₀ i) x) := by
  rw [singularSetsGen_succ]
  set S := singularSetsGen P blk S₀ v i
  have key : x ∈ gentlePart P blk i v S ↔ x ∈ S ∧
      IsGentle P blk i v (chainCluster (siteDist ν) S (2 * scaleR P.K₀ i) x) := by
    constructor
    · rintro ⟨C, ⟨⟨y, hy, rfl⟩, hg⟩, hx⟩
      refine ⟨gentlePart_subset P blk v i S ⟨_, ⟨⟨y, hy, rfl⟩, hg⟩, hx⟩, ?_⟩
      rwa [chainCluster_eq_of_mem (siteDist_comm ν) hx]
    · rintro ⟨hx, hg⟩
      exact ⟨_, ⟨⟨x, hx, rfl⟩, hg⟩, mem_chainCluster_self hx⟩
  rw [Set.mem_sdiff, key]
  tauto

theorem two_mul_scaleR_le_siteDist {i : ℕ} {S : Set (Site ν)} {C : Set (Site ν)}
    (hC : C ∈ chainClusters (siteDist ν) S (2 * scaleR P.K₀ i)) {c y : Site ν} (hc : c ∈ C)
    (hy : y ∈ S) (hyC : y ∉ C) : 2 * scaleR P.K₀ i ≤ siteDist ν c y := by
  obtain ⟨x, -, rfl⟩ := hC
  exact le_of_mem_chainCluster_of_not_mem hc hy hyC

theorem IsGentle.subset_ball {i : ℕ} {C : Set (Site ν)} (h : IsGentle P blk i v C) {x : Site ν}
    (hx : x ∈ C) : C ⊆ {y | siteDist ν x y ≤ scaleD P.K₀ i} := by
  obtain ⟨-, hd, -⟩ := h
  exact fun y hy => hd x hx y hy

theorem singularSetsIn_subset (Λ : Finset (Site ν)) (i : ℕ) :
    singularSetsIn P Λ v i ⊆ Λ := fun _ hx =>
  (singularSetsGen_subset_zero P _ _ v i hx).2

end FroehlichSpencer.Multiscale
