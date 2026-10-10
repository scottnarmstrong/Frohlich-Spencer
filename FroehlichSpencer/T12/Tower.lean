/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Annuli
public import FroehlichSpencer.T12.InductionDefs
public import FroehlichSpencer.T12.Section5
public import FroehlichSpencer.T12.Residual
public import FroehlichSpencer.Multiscale.Measurability

/-!
# The tower event, tower levels and nested tower regions

The
tower event is formalized in ball form: for each stage `j` the ball `B(a, 4^j L + 1)` avoids
`S_{k_j}^Λ` where `k_j = towerLevel K₀ (4^j L)`.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale Filter


noncomputable def towerLevel (K₀ l : ℝ) : ℕ := sSup {k : ℕ | scaleD K₀ k / 5 ≤ l ^ (3 / 4 : ℝ)}


def towerEvent {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (a : Site ν) (L : ℝ) :
    Set (Configuration ν) :=
  {v | ∀ (j : ℕ) (x : Site ν), siteDist ν a x ≤ 4 ^ j * L + 1 →
    x ∉ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))}


def towerRegion {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ) (a : Site ν) (L : ℝ)
    (j : ℕ) : Set (Site ν) :=
  annulusRegion P.K₀ (restrictedClasses P Λ v) (towerLevel P.K₀ (4 ^ j * L)) a (4 ^ j * L)

private theorem bddAbove_towerSet {K₀ l : ℝ} (hK : 0 < K₀) :
    BddAbove {k : ℕ | scaleD K₀ k / 5 ≤ l ^ (3 / 4 : ℝ)} := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_scaleD_atTop hK).eventually_gt_atTop (5 * l ^ (3 / 4 : ℝ)))
  refine ⟨N, fun k hk => ?_⟩
  by_contra h
  have := hN k (not_le.1 h).le
  have hk' : scaleD K₀ k / 5 ≤ l ^ (3 / 4 : ℝ) := hk
  linarith


theorem towerLevel_spec {K₀ l : ℝ} (hK : 0 < K₀) (h0 : scaleD K₀ 0 / 5 ≤ l ^ (3 / 4 : ℝ)) :
    scaleD K₀ (towerLevel K₀ l) / 5 ≤ l ^ (3 / 4 : ℝ) ∧
      ∀ i, scaleD K₀ i / 5 ≤ l ^ (3 / 4 : ℝ) → i ≤ towerLevel K₀ l :=
  ⟨Nat.sSup_mem ⟨0, h0⟩ (bddAbove_towerSet hK), fun _ hi => le_csSup (bddAbove_towerSet hK) hi⟩


theorem one_le_towerLevel {K₀ l : ℝ} (hK : 0 < K₀) (h1 : scaleD K₀ 1 / 5 ≤ l ^ (3 / 4 : ℝ)) :
    1 ≤ towerLevel K₀ l :=
  le_csSup (bddAbove_towerSet hK) h1


theorem lt_scaleD_towerLevel {K₀ l : ℝ} (hK : 0 < K₀)
    (h0 : scaleD K₀ 0 / 5 ≤ l ^ (3 / 4 : ℝ)) :
    (5 * l ^ (3 / 4 : ℝ)) ^ (4 / 5 : ℝ) < scaleD K₀ (towerLevel K₀ l) :=
  lt_scaleD_of_maximal (towerLevel_spec hK h0).2 (towerLevel_spec hK h0).1


theorem measurableSet_towerEvent {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (a : Site ν)
    (L : ℝ) : MeasurableSet (towerEvent P Λ a L) := by
  have : towerEvent P Λ a L = ⋂ (j : ℕ), ⋂ (x : Site ν),
      {v : Configuration ν | siteDist ν a x ≤ 4 ^ j * L + 1 →
        x ∉ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))} := by
    ext v; simp [towerEvent]
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun x => ?_
  by_cases h : siteDist ν a x ≤ 4 ^ j * L + 1
  · have : {v : Configuration ν | siteDist ν a x ≤ 4 ^ j * L + 1 →
        x ∉ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))} =
        {v : Configuration ν | x ∈ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))}ᶜ := by
      ext v; simp [h]
    rw [this]
    exact (measurableSet_mem_singularSetsIn P Λ x _).compl
  · have : {v : Configuration ν | siteDist ν a x ≤ 4 ^ j * L + 1 →
        x ∉ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))} = Set.univ := by
      ext v; simp [h]
    rw [this]
    exact MeasurableSet.univ

private theorem pos_of_scaleConditions {K₀ : ℝ} (hK : ScaleConditions K₀) : 0 < K₀ := by
  have h := hK.1
  unfold scaleD at h
  by_contra hn
  push Not at hn
  have : Real.exp (K₀ * (5 / 4 : ℝ) ^ 0) ≤ 1 := by
    rw [Real.exp_le_one_iff]; simpa using hn
  linarith

private theorem le_pow_mul {L : ℝ} (hL : 0 ≤ L) (j : ℕ) : L ≤ 4 ^ j * L :=
  le_mul_of_one_le_left hL (one_le_pow₀ (by norm_num))

private theorem tower_sep {L₁ : ℝ} (hL₁ : ∀ (K₀ l : ℝ) (k : ℕ), L₁ ≤ l →
    scaleD K₀ k / 5 ≤ l ^ (3 / 4 : ℝ) → k = 0 ∨ 10 * scaleD K₀ (k - 1) ≤ l / 2 - 2)
    {K₀ l : ℝ} (hK : 0 < K₀) (hl : L₁ ≤ l) :
    towerLevel K₀ l = 0 ∨ 10 * scaleD K₀ (towerLevel K₀ l - 1) ≤ l / 2 - 2 := by
  by_cases hne : {k : ℕ | scaleD K₀ k / 5 ≤ l ^ (3 / 4 : ℝ)}.Nonempty
  · exact hL₁ K₀ l _ hl (Nat.sSup_mem hne (bddAbove_towerSet hK))
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold towerLevel
    rw [hne]; exact csSup_empty


theorem exists_towerRegion_spec (ν : ℕ) : ∃ L₀ : ℝ, ∀ (P : Params), ScaleConditions P.K₀ →
    ∀ (Λ : Finset (Site ν)) (v : Site ν → ℝ) (a : Site ν) (L : ℝ), L₀ ≤ L → ∀ j : ℕ,
      (towerRegion P Λ v a L j).Finite ∧ a ∈ towerRegion P Λ v a L j ∧
      (∀ x ∈ towerRegion P Λ v a L j, ∀ y ∈ towerRegion P Λ v a L j,
        y ∈ nnComponent (towerRegion P Λ v a L j) x) ∧
      (∀ b ∈ vertexBoundary (towerRegion P Λ v a L j),
        4 ^ j * L / 2 ≤ siteDist ν a b ∧ siteDist ν a b ≤ 4 ^ j * L) ∧
      towerRegion P Λ v a L j ⊆ {x | siteDist ν a x ≤ 4 ^ j * L} ∧
      Admissible P.K₀ (restrictedClasses P Λ v) (towerLevel P.K₀ (4 ^ j * L))
        (towerRegion P Λ v a L j) ∧
      towerRegion P Λ v a L j ⊆ towerRegion P Λ v a L (j + 1) := by
  obtain ⟨L₁, hL₁⟩ := exists_annulusLevel_sep
  refine ⟨max L₁ 4, fun P hK Λ v a L hL j => ?_⟩
  have hL4 : 4 ≤ L := (le_max_right _ _).trans hL
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have hKp := pos_of_scaleConditions hK
  have hG := obstacleFamily_gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v
  have hl : 4 ≤ 4 ^ j * L := hL4.trans (le_pow_mul (by linarith) j)
  have hsep := tower_sep hL₁ hKp (hL1.trans (le_pow_mul (by linarith) j))
  have hspec := annulusRegion_spec hK hG (n := towerLevel P.K₀ (4 ^ j * L)) a hl hsep
  refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2, ?_⟩
  have h4 : (4 : ℝ) ^ (j + 1) * L = 4 * (4 ^ j * L) := by ring
  unfold towerRegion
  rw [h4]
  exact annulusRegion_subset hK hG a hl hsep


theorem towerRegion_disjoint_singularSetsIn {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) {v : Configuration ν} {a : Site ν} {L : ℝ} (hL : 2 ≤ L)
    (hv : v ∈ towerEvent P Λ a L) (j : ℕ) :
    ∀ x ∈ towerRegion P Λ v a L j, x ∉ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L)) :=
  annulusRegion_disjoint_singularSetsIn P hK Λ v a (le_trans hL (le_pow_mul (by linarith) j))
    (hv j)


theorem exists_norm_finiteGreen_towerRegion_le (ν : ℕ) : ∃ L₀ : ℝ, ∀ (P : Params),
    ScaleConditions P.K₀ → ∀ (Λ : Finset (Site ν)) (v : Configuration ν) (a : Site ν) (L : ℝ),
      L₀ ≤ L → scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) → v ∈ towerEvent P Λ a L →
      ∀ (M : ℝ) (j : ℕ), JPred P Λ v (towerLevel P.K₀ (4 ^ j * L)) M →
      ∀ (hfin : (towerRegion P Λ v a L j).Finite) (ε : ℝ) (hε : ε ≠ 0)
        (x y : {x // x ∈ hfin.toFinset ∩ Λ}), (4 ^ j * L) ^ (3 / 4 : ℝ) ≤ siteDist ν x y →
        ‖finiteGreen ν (hfin.toFinset ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (-M * siteDist ν x y) := by
  obtain ⟨L₀, hL₀⟩ := exists_towerRegion_spec ν
  refine ⟨max L₀ 4, fun P hK Λ v a L hL h1 hv M j hJ hfin ε hε x y hxy => ?_⟩
  have hL4 : 4 ≤ L := (le_max_right _ _).trans hL
  have hL0 : L₀ ≤ L := (le_max_left _ _).trans hL
  have hKp := pos_of_scaleConditions hK
  have hadm := (hL₀ P hK Λ v a L hL0 j).2.2.2.2.2.1
  have havoid := towerRegion_disjoint_singularSetsIn P hK Λ (by linarith) hv j
  have hLl : L ^ (3 / 4 : ℝ) ≤ (4 ^ j * L) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (le_pow_mul (by linarith) j) (by norm_num)
  have hd01 : scaleD P.K₀ 0 ≤ scaleD P.K₀ 1 := scaleD_mono_of_nonneg hKp.le (Nat.zero_le 1)
  have h0 : scaleD P.K₀ 0 / 5 ≤ (4 ^ j * L) ^ (3 / 4 : ℝ) := by linarith
  have hspec := (towerLevel_spec hKp h0).1
  have hA := hJ hfin.toFinset (by rw [Set.Finite.coe_toFinset]; exact hadm)
    (fun x hx => havoid x (by
      have := (Finset.mem_inter.1 hx).1
      simpa using this)) ε hε x y (by linarith)
  exact hA

end FroehlichSpencer.T12

end
