/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.ShortPhase3
public import FroehlichSpencer.FS82.XY.EndpointLower3

/-!
# the Jensen budget of a branch and the finite-volume bound (4.38) for `D = 3`

On a terminal branch the lineages with a nonzero current split into the short ones, with fewer
than `m` links, and the long ones, where `m ≤ B k` in every direction.

* The short ones have the phase representatives `2π⟨ε, F⟩` of their local relative fillings.

Their activity is at most `e^{−a m}`, and their
  supports are disjoint, so their budget is at most `5π² · #links · e^{−a m}`.

With `Endpoint3` this gives, for `β ≥ 136`,

`exp(−(1/(2β) + d(β)) ‖ε‖² − 5π² · #links · e^{−a m}) ≤ Re ⟨e^{i(θ_x − θ_y)}⟩`,

`d(β) = 81 · cpack(3β/8 − 50, 128π)`: this is FS82 (4.38) in finite volume, with the contribution
of the currents that are as long as the box written out.

On cubes of side `N` one takes `m = N`,
and the last term tends to zero as `N → ∞`.
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

/-- Every real phase has a representative modulo `2π` of absolute value at most `π`. -/
theorem xy3_exists_phase_representative_abs_le_pi (x : ℝ) :
    ∃ θ : ℝ, (∃ n : ℤ, x + θ = 2 * Real.pi * (n : ℝ)) ∧ |θ| ≤ Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ) - x,
    ⟨round (x / (2 * Real.pi)), by ring⟩, ?_⟩
  have h := abs_sub_round (x / (2 * Real.pi))
  have hrew : 2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ) - x =
      -(2 * Real.pi) * (x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ)) := by
    field_simp
    ring
  rw [hrew, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  nlinarith

theorem sourceJensenGamma_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ sourceJensenGamma z := by
  unfold sourceJensenGamma
  have h1 : 0 < 1 - z := by linarith
  positivity

theorem cpack_nonneg (a C : ℝ) : 0 ≤ cpack a C := by
  unfold cpack
  refine mul_nonneg (by positivity) (tsum_nonneg fun L => ?_)
  positivity

/-! ## The box of links around a plaquette -/

/-- The links within coordinate distance `2L` of a dual plaquette; empty for `L = 0`. -/
noncomputable def xy3LinkBox (p : Dual3Plaquettes B) (L : ℕ) : Finset (Dual3Links B) :=
  open Classical in
  if L = 0 then ∅ else
    Finset.univ.filter fun e : Dual3Links B =>
      ∀ k, cellBase p.1 k ≤ cellBase e.1 k + 2 * L ∧ cellBase e.1 k ≤ cellBase p.1 k + 2 * L

theorem xy3LinkBox_card_le (p : Dual3Plaquettes B) (L : ℕ) :
    (xy3LinkBox p L).card ≤ 4 * (6 * L) ^ 4 := by
  classical
  unfold xy3LinkBox
  by_cases hL : L = 0
  · simp [hL]
  · simp only [hL, ↓reduceIte]
    have h := card_window_le (fun e : Dual3Links B => e.1) Subtype.val_injective
      (fun k => cellBase p.1 k) (2 * L) (2 * L)
    refine (le_trans (le_of_eq ?_) h).trans ?_
    · congr 1
    · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL
      have h1 : 2 * L + 2 * L + 1 ≤ 5 * L := by omega
      calc 8 * (2 * L + 2 * L + 1) ^ 3 ≤ 8 * (5 * L) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
        _ = 1000 * L ^ 3 := by ring
        _ ≤ 5184 * L ^ 4 := by
            have : L ^ 3 ≤ L ^ 4 := Nat.pow_le_pow_right hL1 (by norm_num)
            omega
        _ = 4 * (6 * L) ^ 4 := by ring

/-! ## The short lineages -/

/-- **The Jensen budget of the short lineages of a branch.** -/
theorem xy3Branch_short_packing {β : ℝ} (hβ : 136 ≤ β) (m : ℕ) (hm : ∀ k, m ≤ B k)
    (x y : XYSites B) (ω : XY3Branch B) :
    ∃ θs : XY3BranchIndex ω → ℝ,
      (∀ i, 1 ≤ currentLength3 (xy3BranchCurrent ω i) →
        currentLength3 (xy3BranchCurrent ω i) < m → ∃ n : ℤ,
          linkPairing (xy3PathShift β x y) (xy3BranchCurrent ω i) + θs i =
            2 * Real.pi * (n : ℝ)) ∧
      (open Classical in
        ∑ i ∈ Finset.univ.filter (fun i : XY3BranchIndex ω =>
            1 ≤ currentLength3 (xy3BranchCurrent ω i) ∧
              currentLength3 (xy3BranchCurrent ω i) < m),
          sourceJensenGamma (xy3BranchAmp β ω i) * θs i ^ 2) ≤
        81 * cpack (xy3ActivityRate β) (2 * Real.pi * 64) * xyDual3ResidualEnergy x y := by
  classical
  have hβ0 : 0 < β := by linarith
  have hrate : 1 ≤ xy3ActivityRate β := by
    unfold xy3ActivityRate
    linarith
  set T := Finset.univ.filter (fun i : XY3BranchIndex ω =>
    1 ≤ currentLength3 (xy3BranchCurrent ω i) ∧ currentLength3 (xy3BranchCurrent ω i) < m)
    with hT
  have hEres : 0 ≤ xyDual3ResidualEnergy x y := by
    rw [← xy3ResidualField_normSq]
    exact Finset.sum_nonneg fun p _ => sq_nonneg _
  by_cases hTne : T.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hTne
    have hi₀' := (Finset.mem_filter.mp hi₀).2
    obtain ⟨_, p₀', _⟩ := xy3Branch_short_filling hβ0 m hm x y ω i₀ hi₀'.1 hi₀'.2
    have hdata : ∀ i : XY3BranchIndex ω, ∃ (F : Dual3Plaquettes B → ℤ)
        (p₀ : Dual3Plaquettes B),
        (1 ≤ currentLength3 (xy3BranchCurrent ω i) ∧
          currentLength3 (xy3BranchCurrent ω i) < m) →
        (∃ n : ℤ, linkPairing (xy3PathShift β x y) (xy3BranchCurrent ω i) +
          2 * Real.pi * ∑ p, xy3ResidualField x y p * ((F p : ℤ) : ℝ) =
            2 * Real.pi * (n : ℝ)) ∧
        (∑ p, |((F p : ℤ) : ℝ)| ≤ 64 * currentEnergy3 (xy3BranchCurrent ω i) *
          (currentLength3 (xy3BranchCurrent ω i) : ℝ) ^ 4) ∧
        (∀ p, F p ≠ 0 → |xy3ResidualField x y p| ≤ |xy3ResidualField x y p₀|) ∧
        (∀ e : Dual3Links B, xy3BranchCurrent ω i e ≠ 0 → ∀ k,
          cellBase p₀.1 k ≤ cellBase e.1 k + 2 * currentLength3 (xy3BranchCurrent ω i) ∧
          cellBase e.1 k ≤ cellBase p₀.1 k + 2 * currentLength3 (xy3BranchCurrent ω i)) := by
      intro i
      by_cases hs : 1 ≤ currentLength3 (xy3BranchCurrent ω i) ∧
          currentLength3 (xy3BranchCurrent ω i) < m
      · obtain ⟨F, p₀, h⟩ := xy3Branch_short_filling hβ0 m hm x y ω i hs.1 hs.2
        exact ⟨F, p₀, fun _ => h⟩
      · exact ⟨fun _ => 0, p₀', fun h => absurd h hs⟩
    choose F p₀ hprops using hdata
    refine ⟨fun i => 2 * Real.pi * ∑ p, xy3ResidualField x y p * ((F i p : ℤ) : ℝ), ?_, ?_⟩
    · intro i h1 h2
      exact (hprops i ⟨h1, h2⟩).1
    · have hpack := xy3_relativePhase_packing (I := XY3BranchIndex ω)
        (P := Dual3Plaquettes B) (α := Dual3Links B) T
        (T.image fun i => currentLength3 (xy3BranchCurrent ω i))
        (fun i => currentSupport (xy3BranchCurrent ω i)) xy3LinkBox p₀
        (fun i => currentLength3 (xy3BranchCurrent ω i)) (fun i => xy3BranchAmp β ω i)
        (fun i => currentEnergy3 (xy3BranchCurrent ω i))
        (fun i => 2 * Real.pi * ∑ p, xy3ResidualField x y p * ((F i p : ℤ) : ℝ))
        (fun p => xy3ResidualField x y p) (fun i p => ((F i p : ℤ) : ℝ))
        (xy3ActivityRate β) 64 (by linarith) hrate (by norm_num)
        (fun i hi => Finset.mem_image_of_mem _ hi)
        (by
          intro L hL
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hL
          exact (Finset.mem_filter.mp hi).2.1)
        (fun i _ => currentEnergy3_nonneg _)
        (fun i _ => xy3BranchAmp_nonneg β ω i)
        (fun i _ => xy3BranchAmp_le (by linarith) ω i)
        (fun i _ => rfl)
        (fun i hi => (hprops i (Finset.mem_filter.mp hi).2).2.1)
        (by
          intro i hi p hp
          refine (hprops i (Finset.mem_filter.mp hi).2).2.2.1 p ?_
          intro h0
          exact hp (by simp [h0]))
        (by
          intro i _ j _ hij
          refine Finset.disjoint_left.mpr fun e hei hej => ?_
          have h1 : xy3BranchCurrent ω i e ≠ 0 := (Finset.mem_filter.mp hei).2
          have h2 : xy3BranchCurrent ω j e ≠ 0 := (Finset.mem_filter.mp hej).2
          exact stateCurrent_separated (xy3BranchState_separated ω) i j hij e e h1 h2
            (Or.inl (linkBaseNear_refl e)))
        (fun i _ => rfl)
        (by
          intro i hi e he
          have hs := (Finset.mem_filter.mp hi).2
          have hne : xy3BranchCurrent ω i e ≠ 0 := (Finset.mem_filter.mp he).2
          have hL0 : currentLength3 (xy3BranchCurrent ω i) ≠ 0 := by omega
          unfold xy3LinkBox
          simp only [hL0, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (hprops i hs).2.2.2 e hne)
        xy3LinkBox_card_le
      rw [xy3ResidualField_normSq] at hpack
      exact hpack
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i h1 h2
      exact absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1, h2⟩⟩ hTne
    · rw [Finset.not_nonempty_iff_eq_empty.mp hTne, Finset.sum_empty]
      exact mul_nonneg (mul_nonneg (by norm_num) (cpack_nonneg _ _)) hEres

end FroehlichSpencer.FS82.XY

end
