/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Packing3

/-!
# the finite-volume lower bound (4.38) for the Villain `XY` model, `D = 3`

`exp(−(1/(2β) + d(β)) ‖ε‖² − 5π² · #links · e^{−a(β) m}) ≤ Re ⟨e^{i(θ_x − θ_y)}⟩_B(β)`,

This is FS82 (4.38) in finite
volume; the last term in the exponent accounts for the currents that are as long as the box and
vanishes in the limit of cubes.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-- The Jensen rate `d(β)` of FS82 (4.38) in three dimensions. -/
noncomputable def xy3JensenRate (β : ℝ) : ℝ :=
  81 * cpack (xy3ActivityRate β) (2 * Real.pi * 64)

theorem xy3JensenRate_nonneg (β : ℝ) : 0 ≤ xy3JensenRate β :=
  mul_nonneg (by norm_num) (cpack_nonneg _ _)

/-- The Jensen rate is exponentially small in `β`. -/
theorem xy3JensenRate_le {β : ℝ} (hβ : 136 ≤ β) :
    xy3JensenRate β ≤
      81 * (1280 * (2 * Real.pi * 64) ^ 2 * polyTail11) * Real.exp (51 - 3 * β / 8) := by
  have ha1 : 1 ≤ xy3ActivityRate β := by
    unfold xy3ActivityRate
    linarith
  have ha0 : 0 < xy3ActivityRate β := by linarith
  have h := cpack_le_exponential_tail (xy3ActivityRate β) (2 * Real.pi * 64) ha0 ha1
  have hpoly : 0 ≤ polyTail11 := by
    unfold polyTail11
    exact tsum_nonneg fun L => by positivity
  have hexp : Real.exp (1 - xy3ActivityRate β) = Real.exp (51 - 3 * β / 8) := by
    congr 1
    unfold xy3ActivityRate
    ring
  have hdiv : 1280 * (2 * Real.pi * 64) ^ 2 / xy3ActivityRate β ^ 2 ≤
      1280 * (2 * Real.pi * 64) ^ 2 := by
    apply div_le_self (by positivity)
    nlinarith
  unfold xy3JensenRate
  rw [hexp] at h
  have hexp0 : 0 ≤ Real.exp (51 - 3 * β / 8) := (Real.exp_pos _).le
  calc 81 * cpack (xy3ActivityRate β) (2 * Real.pi * 64)
      ≤ 81 * (1280 * (2 * Real.pi * 64) ^ 2 / xy3ActivityRate β ^ 2 *
          Real.exp (51 - 3 * β / 8) * polyTail11) := by linarith
    _ ≤ 81 * (1280 * (2 * Real.pi * 64) ^ 2 * Real.exp (51 - 3 * β / 8) * polyTail11) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdiv hexp0) hpoly
        linarith
    _ = 81 * (1280 * (2 * Real.pi * 64) ^ 2 * polyTail11) * Real.exp (51 - 3 * β / 8) := by ring

/-! ## The long lineages -/

/-- The total length of the lineage currents of a branch is at most the number of links. -/
theorem xy3Branch_sum_length_le (ω : XY3Branch B) :
    ∑ i : XY3BranchIndex ω, currentLength3 (xy3BranchCurrent ω i) ≤
      Fintype.card (Dual3Links B) := by
  classical
  have hdisj : ∀ i ∈ (Finset.univ : Finset (XY3BranchIndex ω)),
      ∀ j ∈ (Finset.univ : Finset (XY3BranchIndex ω)), i ≠ j →
      Disjoint (currentSupport (xy3BranchCurrent ω i)) (currentSupport (xy3BranchCurrent ω j)) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun e hei hej => ?_
    have h1 : xy3BranchCurrent ω i e ≠ 0 := (Finset.mem_filter.mp hei).2
    have h2 : xy3BranchCurrent ω j e ≠ 0 := (Finset.mem_filter.mp hej).2
    exact stateCurrent_separated (xy3BranchState_separated ω) i j hij e e h1 h2
      (Or.inl (linkBaseNear_refl e))
  unfold currentLength3
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_univ _

/-- The Jensen term of a long lineage with a representative in `[−π, π]`. -/
theorem xy3Branch_long_term_le {β : ℝ} (hβ : 136 ≤ β) (m : ℕ) (ω : XY3Branch B)
    (i : XY3BranchIndex ω) (hpos : 1 ≤ currentLength3 (xy3BranchCurrent ω i))
    (hlong : m ≤ currentLength3 (xy3BranchCurrent ω i)) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    sourceJensenGamma (xy3BranchAmp β ω i) * θ ^ 2 ≤
      5 * Real.pi ^ 2 * Real.exp (-(xy3ActivityRate β * (m : ℝ))) := by
  have ha1 : 1 ≤ xy3ActivityRate β := by
    unfold xy3ActivityRate
    linarith
  set L := currentLength3 (xy3BranchCurrent ω i) with hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hpos
  have hLm : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlong
  have hlog : Real.log 2 ≤ xy3ActivityRate β * (L : ℝ) := by
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    nlinarith
  have hamp := xy3BranchAmp_le (show (400 : ℝ) / 3 ≤ β by linarith) ω i
  have hE0 := currentEnergy3_nonneg (xy3BranchCurrent ω i)
  have hz : xy3BranchAmp β ω i ≤ Real.exp (-(xy3ActivityRate β * (L : ℝ))) := by
    refine hamp.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have hγ := sourceJensenGamma_le_five_exp_of_logEnvelope hlog (xy3BranchAmp_nonneg β ω i) hz
  have hγ0 : 0 ≤ sourceJensenGamma (xy3BranchAmp β ω i) :=
    sourceJensenGamma_nonneg (xy3BranchAmp_nonneg β ω i)
      (xy3BranchAmp_lt_one (show (400 : ℝ) / 3 < β by linarith) ω i)
  have hexp : Real.exp (-(xy3ActivityRate β * (L : ℝ))) ≤
      Real.exp (-(xy3ActivityRate β * (m : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsq : θ ^ 2 ≤ Real.pi ^ 2 := by
    have := abs_le.mp hθ
    nlinarith [Real.pi_pos]
  calc sourceJensenGamma (xy3BranchAmp β ω i) * θ ^ 2
      ≤ (5 * Real.exp (-(xy3ActivityRate β * (m : ℝ)))) * Real.pi ^ 2 :=
        mul_le_mul (hγ.trans (by linarith)) hsq (sq_nonneg _) (by positivity)
    _ = 5 * Real.pi ^ 2 * Real.exp (-(xy3ActivityRate β * (m : ℝ))) := by ring

/-! ## The Jensen budget of a branch -/

/-- **Phase representatives on every branch, with their Jensen budget.** -/
theorem xy3Branch_phaseRepresentatives {β : ℝ} (hβ : 136 ≤ β) (m : ℕ) (hm : ∀ k, m ≤ B k)
    (x y : XYSites B) (ω : XY3Branch B) :
    ∃ θ' : XY3BranchIndex ω → ℝ,
      (∀ i, xy3BranchAmp β ω i ≠ 0 → ∃ n : ℤ,
        linkPairing (xy3PathShift β x y) (xy3BranchCurrent ω i) + θ' i =
          2 * Real.pi * (n : ℝ)) ∧
      ∑ i, sourceJensenGamma (xy3BranchAmp β ω i) * θ' i ^ 2 ≤
        xy3JensenRate β * xyDual3ResidualEnergy x y +
          5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) *
            Real.exp (-(xy3ActivityRate β * (m : ℝ))) := by
  classical
  obtain ⟨θs, hs1, hs2⟩ := xy3Branch_short_packing hβ m hm x y ω
  choose θl hl1 hl2 using fun i : XY3BranchIndex ω =>
    xy3_exists_phase_representative_abs_le_pi
      (linkPairing (xy3PathShift β x y) (xy3BranchCurrent ω i))
  set short : XY3BranchIndex ω → Prop := fun i =>
    1 ≤ currentLength3 (xy3BranchCurrent ω i) ∧ currentLength3 (xy3BranchCurrent ω i) < m
    with hshort
  set c : ℝ := 5 * Real.pi ^ 2 * Real.exp (-(xy3ActivityRate β * (m : ℝ))) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨fun i => if short i then θs i
    else if 1 ≤ currentLength3 (xy3BranchCurrent ω i) then θl i else 0, ?_, ?_⟩
  · intro i hamp
    have hpos := xy3BranchAmp_ne_zero_length_pos ω i hamp
    by_cases hsh : short i
    · simp only [hsh, ↓reduceIte]
      exact hs1 i hsh.1 hsh.2
    · simp only [hsh, hpos, ↓reduceIte]
      exact hl1 i
  · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ short]
    have hfirst : ∑ i ∈ Finset.univ.filter short,
        sourceJensenGamma (xy3BranchAmp β ω i) *
          (if short i then θs i
            else if 1 ≤ currentLength3 (xy3BranchCurrent ω i) then θl i else 0) ^ 2 =
        ∑ i ∈ Finset.univ.filter short, sourceJensenGamma (xy3BranchAmp β ω i) * θs i ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hsh : short i := (Finset.mem_filter.mp hi).2
      simp only [hsh, ↓reduceIte]
    have hsecond : ∑ i ∈ Finset.univ.filter (fun i => ¬ short i),
        sourceJensenGamma (xy3BranchAmp β ω i) *
          (if short i then θs i
            else if 1 ≤ currentLength3 (xy3BranchCurrent ω i) then θl i else 0) ^ 2 ≤
        ∑ i ∈ Finset.univ.filter (fun i => ¬ short i),
          (currentLength3 (xy3BranchCurrent ω i) : ℝ) * c := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hsh : ¬ short i := (Finset.mem_filter.mp hi).2
      by_cases hpos : 1 ≤ currentLength3 (xy3BranchCurrent ω i)
      · have hlong : m ≤ currentLength3 (xy3BranchCurrent ω i) := by
          by_contra hlt
          exact hsh ⟨hpos, by omega⟩
        simp only [hsh, hpos, ↓reduceIte]
        have hterm := xy3Branch_long_term_le hβ m ω i hpos hlong (θl i) (hl2 i)
        have hL1 : (1 : ℝ) ≤ (currentLength3 (xy3BranchCurrent ω i) : ℝ) := by
          exact_mod_cast hpos
        calc sourceJensenGamma (xy3BranchAmp β ω i) * θl i ^ 2 ≤ c := hterm
          _ ≤ (currentLength3 (xy3BranchCurrent ω i) : ℝ) * c := by nlinarith
      · simp only [hsh, hpos, ↓reduceIte]
        have h0 : currentLength3 (xy3BranchCurrent ω i) = 0 := by omega
        simp [h0]
    have hsumL : ∑ i ∈ Finset.univ.filter (fun i => ¬ short i),
        (currentLength3 (xy3BranchCurrent ω i) : ℝ) * c ≤
        (Fintype.card (Dual3Links B) : ℝ) * c := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hc0
      have hsub : ∑ i ∈ Finset.univ.filter (fun i => ¬ short i),
          (currentLength3 (xy3BranchCurrent ω i) : ℝ) ≤
          ∑ i : XY3BranchIndex ω, (currentLength3 (xy3BranchCurrent ω i) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => Nat.cast_nonneg _
      refine hsub.trans ?_
      exact_mod_cast xy3Branch_sum_length_le ω
    rw [hfirst]
    have hs2' : ∑ i ∈ Finset.univ.filter short,
        sourceJensenGamma (xy3BranchAmp β ω i) * θs i ^ 2 ≤
        xy3JensenRate β * xyDual3ResidualEnergy x y := by
      unfold xy3JensenRate
      convert hs2 using 2
    calc ∑ i ∈ Finset.univ.filter short, sourceJensenGamma (xy3BranchAmp β ω i) * θs i ^ 2 +
          ∑ i ∈ Finset.univ.filter (fun i => ¬ short i),
            sourceJensenGamma (xy3BranchAmp β ω i) *
              (if short i then θs i
                else if 1 ≤ currentLength3 (xy3BranchCurrent ω i) then θl i else 0) ^ 2
        ≤ xy3JensenRate β * xyDual3ResidualEnergy x y +
            (Fintype.card (Dual3Links B) : ℝ) * c :=
          add_le_add hs2' (hsecond.trans hsumL)
      _ = _ := by rw [hc]; ring

/-! ## The finite-volume bound -/

/-- **FS82 (4.38) in finite volume for the three-dimensional Villain `XY` model.** -/
theorem xy3_endpointExpectation_lower {β : ℝ} (hβ : 136 ≤ β) (m : ℕ) (hm : ∀ k, m ≤ B k)
    (x y : XYSites B) :
    Real.exp (-((1 / (2 * β) + xy3JensenRate β) * xyDual3ResidualEnergy x y) -
        5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) *
          Real.exp (-(xy3ActivityRate β * (m : ℝ)))) ≤
      (xyEndpointCharacterExpectation β x y).re := by
  have h := xy3_endpointExpectation_lower_of_phaseRepresentatives_of_threshold
    (show (400 : ℝ) / 3 < β by linarith) x y
    (xy3JensenRate β * xyDual3ResidualEnergy x y +
      5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) *
        Real.exp (-(xy3ActivityRate β * (m : ℝ))))
    (fun ω => xy3Branch_phaseRepresentatives hβ m hm x y ω)
  refine le_trans (le_of_eq ?_) h
  congr 1
  ring

end FroehlichSpencer.FS82.XY

end
