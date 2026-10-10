/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Phase3
public import FroehlichSpencer.FS82.XY.Extent3
public import FroehlichSpencer.FS82.XY.Activity3

/-!
# phase representatives of the short lineages of a branch

A lineage of a terminal branch whose current `J` is nonzero is co-closed and good, so its `L`
links have pairwise extent `L − 1`.

If `L < m ≤ B k` in every direction, the local relative
filling `F` of `Extent3` exists.

It gives the phase representative `2π⟨ε, F⟩` of `Phase3`, with

* `∑ |F(p)| ≤ 64 ‖J‖² L⁴`,
* a plaquette `p₀` in the support of `F` at which `|ε|` is maximal on that support,
* every link of `J` within coordinate distance `2L` of `p₀`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-! ## The current of a lineage of a branch -/

theorem xy3BranchCurrent_coClosed (ω : XY3Branch B) (i : XY3BranchIndex ω) :
    RootedTreeGauge.CoClosed (xyDual3RootedTree B) (xy3BranchCurrent ω i) :=
  closedCurrent_coClosed _

theorem xy3BranchCurrent_eq_lineageCurrent (ω : XY3Branch B) (i : XY3BranchIndex ω)
    {e : Dual3Links B} (he : xy3BranchCurrent ω i e ≠ 0) :
    xy3BranchCurrent ω i = Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1 := by
  unfold xy3BranchCurrent stateCurrent at he ⊢
  by_cases hcl : RootedTreeGauge.CoClosed (xyDual3RootedTree B)
      (Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1)
  · exact closedCurrent_of_coClosed hcl
  · rw [closedCurrent_of_not_coClosed hcl] at he
    exact absurd rfl he

theorem xy3BranchCurrent_support (ω : XY3Branch B) (i : XY3BranchIndex ω)
    {e : Dual3Links B} (he : xy3BranchCurrent ω i e ≠ 0) :
    currentSupport (xy3BranchCurrent ω i) = i.1.active := by
  obtain ⟨hgood, hq⟩ := ((xy3Terms_spec ω.1).2.2.1 _ (xy3BranchTerm_mem ω)).1 i.1 i.2
  rw [xy3BranchCurrent_eq_lineageCurrent ω i he]
  exact ActivityLineage.currentSupport_value_eq_active hgood _ hq

theorem xy3BranchCurrent_extent (ω : XY3Branch B) (i : XY3BranchIndex ω)
    (e f : Dual3Links B) (he : xy3BranchCurrent ω i e ≠ 0) (hf : xy3BranchCurrent ω i f ≠ 0)
    (k : Fin 3) :
    cellBase e.1 k + 1 ≤ cellBase f.1 k + currentLength3 (xy3BranchCurrent ω i) := by
  obtain ⟨hgood, _⟩ := ((xy3Terms_spec ω.1).2.2.1 _ (xy3BranchTerm_mem ω)).1 i.1 i.2
  have hsupp := xy3BranchCurrent_support ω i he
  have hea : e ∈ i.1.active := by
    rw [← hsupp]
    simp [currentSupport, he]
  have hfa : f ∈ i.1.active := by
    rw [← hsupp]
    simp [currentSupport, hf]
  unfold currentLength3
  rw [hsupp]
  exact good_active_extent hgood e hea f hfa k


theorem exists_ne_zero_of_length_pos {j : Dual3Links B → ℤ} (h : 1 ≤ currentLength3 j) :
    ∃ e, j e ≠ 0 := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  exact ⟨e, (Finset.mem_filter.mp he).2⟩

/-- A lineage with a nonzero amplitude has a nonzero current. -/
theorem xy3BranchAmp_ne_zero_length_pos {β : ℝ} (ω : XY3Branch B) (i : XY3BranchIndex ω)
    (h : xy3BranchAmp β ω i ≠ 0) : 1 ≤ currentLength3 (xy3BranchCurrent ω i) := by
  have hcl : RootedTreeGauge.CoClosed (xyDual3RootedTree B)
      (Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1) := by
    by_contra hncl
    apply h
    unfold xy3BranchAmp stateAmp familyAmp stateActivity
    rw [closedActivity_of_not_coClosed _ hncl, zero_mul]
  have hcur : xy3BranchCurrent ω i =
      Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1 := closedCurrent_of_coClosed hcl
  rw [hcur]
  exact xy3Branch_lineageCurrent_length_pos ω i.2

theorem sum_natAbs_le_currentEnergy3 (j : Dual3Links B → ℤ) :
    ((∑ e : Dual3Links B, (j e).natAbs : ℕ) : ℝ) ≤ currentEnergy3 j := by
  unfold currentEnergy3
  have hE : ∑ e ∈ currentSupport j, ((j e : ℤ) : ℝ) ^ 2 = ∑ e : Dual3Links B, ((j e : ℤ) : ℝ) ^ 2 := by
    refine Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_
    have h0 : j e = 0 := by
      by_contra hne
      exact he (by simp [currentSupport, hne])
    simp [h0]
  rw [hE, Nat.cast_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have habs : (((j e).natAbs : ℕ) : ℝ) = |((j e : ℤ) : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [habs, ← sq_abs]
  by_cases h0 : j e = 0
  · simp [h0]
  · have h1 : (1 : ℝ) ≤ |((j e : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |j e| := Int.one_le_abs h0
      exact_mod_cast this
    nlinarith

/-! ## The short lineages -/

/-- **The filling data of a short lineage of a branch.** -/
theorem xy3Branch_short_filling {β : ℝ} (hβ : 0 < β) (m : ℕ) (hm : ∀ k, m ≤ B k)
    (x y : XYSites B) (ω : XY3Branch B) (i : XY3BranchIndex ω)
    (hpos : 1 ≤ currentLength3 (xy3BranchCurrent ω i))
    (hshort : currentLength3 (xy3BranchCurrent ω i) < m) :
    ∃ (F : Dual3Plaquettes B → ℤ) (p₀ : Dual3Plaquettes B),
      (∃ n : ℤ, linkPairing (xy3PathShift β x y) (xy3BranchCurrent ω i) +
        2 * Real.pi * ∑ p, xy3ResidualField x y p * ((F p : ℤ) : ℝ) = 2 * Real.pi * (n : ℝ)) ∧
      (∑ p, |((F p : ℤ) : ℝ)| ≤ 64 * currentEnergy3 (xy3BranchCurrent ω i) *
        (currentLength3 (xy3BranchCurrent ω i) : ℝ) ^ 4) ∧
      (∀ p, F p ≠ 0 → |xy3ResidualField x y p| ≤ |xy3ResidualField x y p₀|) ∧
      (∀ e : Dual3Links B, xy3BranchCurrent ω i e ≠ 0 → ∀ k,
        cellBase p₀.1 k ≤ cellBase e.1 k + 2 * currentLength3 (xy3BranchCurrent ω i) ∧
        cellBase e.1 k ≤ cellBase p₀.1 k + 2 * currentLength3 (xy3BranchCurrent ω i)) := by
  classical
  set J := xy3BranchCurrent ω i with hJdef
  set L := currentLength3 J with hLdef
  obtain ⟨e₀, he₀⟩ := exists_ne_zero_of_length_pos hpos
  have hJ := xy3BranchCurrent_coClosed ω i
  have hext : ∀ e f, J e ≠ 0 → J f ≠ 0 → ∀ k, cellBase e.1 k ≤ cellBase f.1 k + (L - 1) := by
    intro e f he hf k
    have h : cellBase e.1 k + 1 ≤ cellBase f.1 k + L := xy3BranchCurrent_extent ω i e f he hf k
    omega
  have hD : ∀ k, L - 1 < B k := fun k => by
    have := hm k
    omega
  obtain ⟨F, hF, hsupp, hbound⟩ := exists_relativeFilling_of_extent J hJ e₀ he₀ (L - 1) hext hD
  have hFne : ∃ p, F p ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : (WithLp.toLp 2 fun p => ((F p : ℤ) : ℝ) :
        EuclideanSpace ℝ (Dual3Plaquettes B)) = 0 := by
      ext p
      simp [hall p]
    rw [hzero, map_zero] at hF
    have h0 : currentVector J e₀ = 0 := by rw [← hF]; rfl
    rw [currentVector_apply] at h0
    exact he₀ (Int.cast_eq_zero.mp h0)
  set S : Finset (Dual3Plaquettes B) := Finset.univ.filter fun p => F p ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨p, hp⟩ := hFne
    exact ⟨p, by simp [hS, hp]⟩
  obtain ⟨p₀, hp₀S, hmax⟩ := Finset.exists_max_image S (fun p => |xy3ResidualField x y p|) hSne
  have hp₀ : F p₀ ≠ 0 := (Finset.mem_filter.mp hp₀S).2
  refine ⟨F, p₀, xy3_phase_representative_of_filling hβ x y hJ F hF, ?_, ?_, ?_⟩
  · have hcardS : S.card ≤ 8 * ((L - 1) + ((L - 1) + 1) + 1) ^ 3 := by
      refine (Finset.card_le_card ?_).trans
        (card_window_le (fun p : Dual3Plaquettes B => p.1) Subtype.val_injective
          (fun k => cellBase e₀.1 k) (L - 1) ((L - 1) + 1))
      intro p hp
      have hpF : F p ≠ 0 := (Finset.mem_filter.mp hp).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsupp p hpF
    have hcard' : (S.card : ℝ) ≤ 64 * (L : ℝ) ^ 3 := by
      have h2 : (L - 1) + ((L - 1) + 1) + 1 = 2 * L := by omega
      rw [h2] at hcardS
      have : (S.card : ℝ) ≤ ((8 * (2 * L) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcardS
      refine this.trans (le_of_eq ?_)
      push_cast
      ring
    have hnorm := sum_natAbs_le_currentEnergy3 J
    have hE0 := currentEnergy3_nonneg J
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hpos
    have hterm : ∀ p ∈ S, |((F p : ℤ) : ℝ)| ≤ currentEnergy3 J := by
      intro p _
      have h1 : |((F p : ℤ) : ℝ)| = (((F p).natAbs : ℕ) : ℝ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [h1]
      exact (by exact_mod_cast hbound p : (((F p).natAbs : ℕ) : ℝ) ≤
        ((∑ e : Dual3Links B, (J e).natAbs : ℕ) : ℝ)).trans hnorm
    calc ∑ p, |((F p : ℤ) : ℝ)| = ∑ p ∈ S, |((F p : ℤ) : ℝ)| := by
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
          have h0 : F p = 0 := by
            by_contra hne
            exact hp (by simp [hS, hne])
          simp [h0]
      _ ≤ ∑ _p ∈ S, currentEnergy3 J := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * currentEnergy3 J := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 64 * (L : ℝ) ^ 3 * currentEnergy3 J := mul_le_mul_of_nonneg_right hcard' hE0
      _ ≤ 64 * currentEnergy3 J * (L : ℝ) ^ 4 := by
          have hpow : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ 4 := by
            have h3 : (0 : ℝ) ≤ (L : ℝ) ^ 3 := by positivity
            nlinarith
          nlinarith
  · intro p hp
    exact hmax p (by simp [hS, hp])
  · intro e he k
    have h1 := hsupp p₀ hp₀ k
    have h2 := hext e e₀ he he₀ k
    have h3 := hext e₀ e he₀ he k
    omega

end FroehlichSpencer.FS82.XY

end
