/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Mixture3

/-!
# the endpoint character from below by Jensen on the branches

`exp(−‖ε‖²/(2β) − E) ≤ Re ⟨e^{i(θ_x − θ_y)}⟩`,

This is
FS82 (4.35)–(4.38) with the Jensen error left as the explicit quantity `E`; it is the
three-dimensional counterpart of `Wilson.sourceDualMoment_lower_of_phaseRepresentatives`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.XY.Expansion3
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-! ## The zero tilt and the endpoint tilt -/

theorem tiltVector_zero (τ : (xyDual3RootedTree B).Chord → ℝ) :
    tiltVector (xyDual3RootedTree B) τ 0 = 0 := by
  funext c
  simp [tiltVector]

theorem tiltShift_zero (A : Matrix (xyDual3RootedTree B).Chord (xyDual3RootedTree B).Chord ℝ) :
    tiltShift (xyDual3RootedTree B) A 0 = 0 := by
  funext e
  simp [tiltShift, RootedTreeGauge.extendChord]

theorem tiltConstant_zero
    (A : Matrix (xyDual3RootedTree B).Chord (xyDual3RootedTree B).Chord ℝ) :
    tiltConstant (xyDual3RootedTree B) A 0 = 1 := by
  simp [tiltConstant, chordBilinear]

/-- The link translation of the endpoint pair `x, y`, in radians. -/
noncomputable def xy3PathShift (β : ℝ) (x y : XYSites B) : Dual3Links B → ℝ :=
  tiltShift (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
    (tiltVector (xyDual3RootedTree B) (xyDual3PathChordSource x y) (-β⁻¹))

/-- The chord pairing of two co-closed one-forms is `2πβ` times their Hodge pairing. -/
theorem chordBilinear_restrictChord_pair {β : ℝ} (hβ : 0 < β)
    (μ ν : coClosed (dual3ExactOneComplex B)) :
    chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
        ((xyDual3RootedTree B).restrictChord μ.1.ofLp)
        ((xyDual3RootedTree B).restrictChord ν.1.ofLp) =
      2 * Real.pi * β * inner ℝ μ.1 (dual3HodgeInverse ν).1 := by
  unfold chordBilinear
  rw [xyDual3ChordMatrix_inv hβ, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  exact (xyDual3HodgePairing_eq_chord μ ν).symm

/-- The Gaussian constant of the endpoint tilt. -/
theorem tiltConstant_path {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    tiltConstant (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
        (tiltVector (xyDual3RootedTree B) (xyDual3PathChordSource x y) (-β⁻¹)) =
      Real.exp (inner ℝ (xyDual3PathSourceCoClosed x y).1 (xyDual3PathTau x y).1 / (2 * β)) := by
  have hb := chordBilinear_restrictChord_pair hβ (xyDual3PathSourceCoClosed x y)
    (xyDual3PathSourceCoClosed x y)
  change chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
    (xyDual3PathChordSource x y) (xyDual3PathChordSource x y) =
      2 * Real.pi * β * inner ℝ (xyDual3PathSourceCoClosed x y).1 (xyDual3PathTau x y).1 at hb
  have hscale : tiltVector (xyDual3RootedTree B) (xyDual3PathChordSource x y) (-β⁻¹) =
      (-β⁻¹ / (2 * Real.pi)) • xyDual3PathChordSource x y := by
    funext c
    simp only [tiltVector, Pi.smul_apply, smul_eq_mul]
    ring
  have hsm : chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
      ((-β⁻¹ / (2 * Real.pi)) • xyDual3PathChordSource x y)
      ((-β⁻¹ / (2 * Real.pi)) • xyDual3PathChordSource x y) =
      (-β⁻¹ / (2 * Real.pi)) ^ 2 *
        chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
          (xyDual3PathChordSource x y) (xyDual3PathChordSource x y) := by
    unfold chordBilinear
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  unfold tiltConstant
  rw [hscale, hsm, hb]
  congr 1
  have hπ := Real.pi_pos.ne'
  have hβ' := hβ.ne'
  field_simp

/-- The translated phase of a co-closed integer current is `2π` times its pairing with the
projected path potential. -/
theorem linkPairing_xy3PathShift {β : ℝ} (hβ : 0 < β) (x y : XYSites B)
    {j : Dual3Links B → ℤ} (hj : RootedTreeGauge.CoClosed (xyDual3RootedTree B) j) :
    linkPairing (xy3PathShift β x y) j =
      2 * Real.pi * inner ℝ (currentVector j) (xyDual3PathTau x y).1 := by
  have hb := chordBilinear_restrictChord_pair hβ
    (⟨currentVector j, currentVector_mem_coClosed hj⟩ : coClosed (dual3ExactOneComplex B))
    (xyDual3PathSourceCoClosed x y)
  change chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
    (chordVector (xyDual3RootedTree B) j) (xyDual3PathChordSource x y) =
      2 * Real.pi * β * inner ℝ (currentVector j) (xyDual3PathTau x y).1 at hb
  unfold xy3PathShift
  rw [linkPairing_tiltShift _ (xyDual3ChordMatrix_posDef hβ),
    chordBilinear_comm _ (xyDual3ChordMatrix_posDef hβ)]
  have hscale : tiltVector (xyDual3RootedTree B) (xyDual3PathChordSource x y) (-β⁻¹) =
      (-β⁻¹ / (2 * Real.pi)) • xyDual3PathChordSource x y := by
    funext c
    simp only [tiltVector, Pi.smul_apply, smul_eq_mul]
    ring
  have hsm : chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
      (chordVector (xyDual3RootedTree B) j)
      ((-β⁻¹ / (2 * Real.pi)) • xyDual3PathChordSource x y) =
      (-β⁻¹ / (2 * Real.pi)) *
        chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
          (chordVector (xyDual3RootedTree B) j) (xyDual3PathChordSource x y) := by
    unfold chordBilinear
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [hscale, hsm, hb]
  have hπ := Real.pi_pos.ne'
  have hβ' := hβ.ne'
  field_simp

/-! ## The two chord sums -/

theorem xy3_tiltedChordSum_eq {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    ∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β)
          (realTiltParameter (xyDual3PathChordSource x y) (-β⁻¹)) k =
      Complex.exp ((inner ℝ (xyDual3PathSourceCoClosed x y).1
          (xyDual3PathTau x y).1 : ℝ) / (2 * β)) *
        ∑' ρ : XYDual3IntegerCirculations B, xyDual3PathPhase (le_of_lt hβ) x y ρ := by
  rw [← (xyDual3ChordCurrentEquiv (B := B)).tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun k => xyDual3ChordDualTerm_eq_correctedPhase hβ x y k

theorem xy3_centredChordSum_eq {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    ∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β)
          (realTiltParameter (xyDual3PathChordSource x y) 0) k =
      ∑' ρ : XYDual3IntegerCirculations B, xyDual3Chi0 (le_of_lt hβ) ρ := by
  rw [← (xyDual3ChordCurrentEquiv (B := B)).tsum_eq]
  refine tsum_congr fun k => ?_
  have h := xyDual3ChordDualTerm_eq_correctedPhase hβ x x k
  rw [xyDual3PathPhase_self] at h
  have hsrc : xyDual3PathSource x x = 0 := by
    simp [xyDual3PathSource, xyDual3EndpointPathVector_self]
  have hchord : xyDual3PathChordSource x x = 0 := by
    funext c
    simp [xyDual3PathChordSource, hsrc, RootedTreeGauge.restrictChord]
  have hco : (xyDual3PathSourceCoClosed x x).1 = 0 := hsrc
  rw [hchord, hco] at h
  have ht : realTiltParameter (xyDual3PathChordSource x y) 0 =
      realTiltParameter (0 : (xyDual3RootedTree B).Chord → ℝ) (-β⁻¹) := by
    funext c
    simp [realTiltParameter]
  rw [ht, h]
  simp

/-! ## The lower bound -/

/-- **The endpoint character from below, with phase representatives.** -/
theorem xy3_endpointExpectation_lower_of_phaseRepresentatives {β : ℝ} (hβ : 0 < β)
    (x y : XYSites B) (E : ℝ)
    (hamp : ∀ (ω : XY3Branch B) (i : XY3BranchIndex ω), xy3BranchAmp β ω i < 1)
    (hE : ∀ ω : XY3Branch B, ∃ θ' : XY3BranchIndex ω → ℝ,
      (∀ i, xy3BranchAmp β ω i ≠ 0 → ∃ n : ℤ,
        linkPairing (xy3PathShift β x y) (xy3BranchCurrent ω i) + θ' i =
          2 * Real.pi * (n : ℝ)) ∧
      ∑ i, SourceJensen.sourceJensenGamma (xy3BranchAmp β ω i) * θ' i ^ 2 ≤ E) :
    Real.exp (-(xyDual3ResidualEnergy x y / (2 * β)) - E) ≤
      (xyEndpointCharacterExpectation β x y).re := by
  have hamp' : ∀ (ω : XY3Branch B) (i : XY3BranchIndex ω), xy3BranchAmp β ω i ≤ 1 :=
    fun ω i => (hamp ω i).le
  set σ := xyDual3PathChordSource x y with hσ
  set Nc : ℂ := ∑' k : (xyDual3RootedTree B).Chord → ℤ,
    dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter σ (-β⁻¹)) k with hNc
  set Dc : ℂ := ∑' k : (xyDual3RootedTree B).Chord → ℤ,
    dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter σ 0) k with hDc
  set c : ℝ := Real.exp (inner ℝ (xyDual3PathSourceCoClosed x y).1 (xyDual3PathTau x y).1 /
    (2 * β)) with hc
  have hcpos : 0 < c := Real.exp_pos _
  have hD := xy3_branch_hasSum (B := B) hβ σ 0 hamp'
  have hN := xy3_branch_hasSum (B := B) hβ σ (-β⁻¹) hamp'
  rw [tiltVector_zero, tiltShift_zero, tiltConstant_zero, div_one] at hD
  rw [tiltConstant_path hβ x y] at hN
  change HasSum (fun ω : XY3Branch B => xy3BranchWeight ω *
    xy3BranchIntegral β (xy3PathShift β x y) ω) (Nc.re / c) at hN
  have hbranch : ∀ ω : XY3Branch B,
      Real.exp (-E) * (xy3BranchWeight ω * xy3BranchIntegral β 0 ω) ≤
        xy3BranchWeight ω * xy3BranchIntegral β (xy3PathShift β x y) ω := by
    intro ω
    obtain ⟨θ', hθ, hcost⟩ := hE ω
    have hJ := xy3Branch_jensen hβ (xy3PathShift β x y) ω (hamp ω) θ' hθ
    have hI0 := (xy3BranchIntegral_zero_pos hβ ω (hamp ω)).le
    have h1 : Real.exp (-E) * xy3BranchIntegral β 0 ω ≤
        xy3BranchIntegral β (xy3PathShift β x y) ω :=
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) hI0).trans hJ
    calc Real.exp (-E) * (xy3BranchWeight ω * xy3BranchIntegral β 0 ω)
        = xy3BranchWeight ω * (Real.exp (-E) * xy3BranchIntegral β 0 ω) := by ring
      _ ≤ xy3BranchWeight ω * xy3BranchIntegral β (xy3PathShift β x y) ω :=
        mul_le_mul_of_nonneg_left h1 (xy3BranchWeight_nonneg ω)
  have hle : Real.exp (-E) * Dc.re ≤ Nc.re / c := hasSum_le hbranch (hD.mul_left _) hN
  have hDpos : 0 < Dc.re := by
    let ω₀ : XY3Branch B :=
      ⟨fun _ => 0, ⟨0, List.length_pos_of_ne_nil (xy3Terms_spec _).1⟩⟩
    have hterm : 0 < xy3BranchWeight ω₀ * xy3BranchIntegral β 0 ω₀ :=
      mul_pos (mul_pos (assignmentCoefficient_pos rootActivity _ fun _ => rootActivity_pos _)
        (xy3BranchWeight_pos ω₀)) (xy3BranchIntegral_zero_pos hβ ω₀ (hamp ω₀))
    exact lt_of_lt_of_le hterm (le_hasSum hD ω₀ fun ω _ =>
      mul_nonneg (xy3BranchWeight_nonneg ω) (xy3BranchIntegral_nonneg hβ 0 ω (hamp' ω)))
  have hNre : ((Nc.re : ℝ) : ℂ) = Nc := xy3_chordSum_ofReal_re hβ σ (-β⁻¹)
  have hDre : ((Dc.re : ℝ) : ℂ) = Dc := xy3_chordSum_ofReal_re hβ σ 0
  have hNsum := xy3_tiltedChordSum_eq hβ x y
  have hDsum := xy3_centredChordSum_eq hβ x y
  have hcexp : Complex.exp ((inner ℝ (xyDual3PathSourceCoClosed x y).1
      (xyDual3PathTau x y).1 : ℝ) / (2 * β)) = (c : ℂ) := by
    rw [hc, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hcexp] at hNsum
  have hratio : (∑' ρ : XYDual3IntegerCirculations B, xyDual3PathPhase (le_of_lt hβ) x y ρ) /
      (∑' ρ : XYDual3IntegerCirculations B, xyDual3Chi0 (le_of_lt hβ) ρ) =
      ((Nc.re / c / Dc.re : ℝ) : ℂ) := by
    have hD' : (∑' ρ : XYDual3IntegerCirculations B, xyDual3Chi0 (le_of_lt hβ) ρ) =
        ((Dc.re : ℝ) : ℂ) := by
      rw [hDre]
      exact hDsum.symm
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hN' : (∑' ρ : XYDual3IntegerCirculations B, xyDual3PathPhase (le_of_lt hβ) x y ρ) =
        ((Nc.re / c : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, hNre]
      change _ = (∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β)
          (realTiltParameter (xyDual3PathChordSource x y) (-β⁻¹)) k) / (c : ℂ)
      rw [hNsum]
      field_simp
    rw [hN', hD', ← Complex.ofReal_div]
  rw [xyEndpointCharacterExpectation_eq_dualPhaseRatio hβ x y, hratio]
  have hexp : Complex.exp (-(xyDual3ResidualEnergy x y : ℂ) / (2 * β)) =
      ((Real.exp (-(xyDual3ResidualEnergy x y / (2 * β))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp, ← Complex.ofReal_mul, Complex.ofReal_re, sub_eq_add_neg, Real.exp_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [le_div_iff₀ hDpos]
  exact hle

end FroehlichSpencer.FS82.XY

end
