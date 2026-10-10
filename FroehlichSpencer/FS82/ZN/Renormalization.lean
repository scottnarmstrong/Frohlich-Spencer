/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.SourceLinkColoring
public import FroehlichSpencer.FS82.Currents.SelectedLinkSelection
public import FroehlichSpencer.FS82.Currents.Current
public import FroehlichSpencer.FS82.Currents.ActivityRate
public import FroehlichSpencer.FS82.Currents.PlaquetteDistance
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import FroehlichSpencer.FS82.ZN.Fourier
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# FS82 §3 Wilson one-link contour shift and selected links

The eight direction/parity classes from §2 are reused without changing their
geometry. The scalar Wilson factor is translated by a Cauchy rectangle; its
attenuation is exponential in the absolute current, uniformly over all six
incident plaquette phases.
-/

@[expose] public section

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace FroehlichSpencer.FS82.ZN.Renormalization

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Currents.SourceLinkColoring

variable {B : SourceBox}

/-- The `ℓ¹` mass of a source integer current. -/
noncomputable def sourceCurrentL1Mass (j : IntegerCurrent B) : ℝ :=
  ∑ e ∈ j.support, |(j e : ℝ)|

/-- Select a color class carrying at least one eighteenth of the current's
`ℓ¹` mass. The eight-class coloring is exactly the §2 direction/parity coloring;
no plaquette contains two distinct selected links. -/
theorem selectedCurrentLinks_l1 (j : IntegerCurrent B) :
    ∃ c : Fin 8,
      sourceCurrentL1Mass j / 18 ≤
        classMass j.support linkColor (fun e => |(j e : ℝ)|) c ∧
      ∀ e ∈ colorClass j.support linkColor c,
        ∀ f ∈ colorClass j.support linkColor c,
          ¬ (e ≠ f ∧ ∃ p : SourceDualTwoCells B,
            linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) := by
  have hcolor : ∀ ⦃e f⦄,
      (e ≠ f ∧ ∃ p : SourceDualTwoCells B,
        linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) →
      linkColor e ≠ linkColor f := by
    intro e f h
    exact linkColor_ne_of_sharedPlaquette h.1 h.2
  obtain ⟨c, hmass, hconflict⟩ := selectedClass_noConflict
    j.support linkColor (fun e => |(j e : ℝ)|)
    (fun e f => e ≠ f ∧ ∃ p : SourceDualTwoCells B,
      linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) hcolor
  refine ⟨c, ?_, hconflict⟩
  change (∑ e ∈ j.support, |(j e : ℝ)|) / 18 ≤ _
  have htotal : 0 ≤ ∑ e ∈ j.support, |(j e : ℝ)| := by positivity
  calc
    (∑ e ∈ j.support, |(j e : ℝ)|) / 18 ≤
        (∑ e ∈ j.support, |(j e : ℝ)|) / 8 := by nlinarith [htotal]
    _ ≤ classMass j.support linkColor (fun e => |(j e : ℝ)|) c := hmass


/-- A current is `Nℤ`-valued linkwise. -/
def IsNMultipleSourceCurrent (N : ℕ) (j : IntegerCurrent B) : Prop :=
  ∀ e, ∃ k : ℤ, j e = (N : ℤ) * k


/-- A nonzero `Nℤ` current has at least `N` units of absolute current on
each supported link. -/
theorem sourceCurrentL1Mass_ge_support_mul_N (N : ℕ) (j : IntegerCurrent B)
    (hNmultiple : IsNMultipleSourceCurrent N j) :
    (N : ℝ) * (j.support.card : ℝ) ≤ sourceCurrentL1Mass j := by
  classical
  have hterm : ∀ e ∈ j.support, (N : ℝ) ≤ |(j e : ℝ)| := by
    intro e he
    have hje : j e ≠ 0 := Finsupp.mem_support_iff.mp he
    obtain ⟨k, hk⟩ := hNmultiple e
    have hk0 : k ≠ 0 := by
      intro hkz
      apply hje
      rw [hk, hkz]
      simp
    have hkabs : 1 ≤ |k| := Int.one_le_abs hk0
    have hkabsReal : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkabs
    have hval : (j e : ℝ) = (N : ℝ) * (k : ℝ) := by exact_mod_cast hk
    rw [hval, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    simpa using mul_le_mul_of_nonneg_left hkabsReal (Nat.cast_nonneg N)
  calc
    (N : ℝ) * (j.support.card : ℝ) =
        ∑ e ∈ j.support, (N : ℝ) := by simp; ring
    _ ≤ ∑ e ∈ j.support, |(j e : ℝ)| := by
      apply Finset.sum_le_sum
      intro e he
      exact hterm e he
    _ = sourceCurrentL1Mass j := rfl


noncomputable def wilsonLinkIntegrand (β : ℝ) (q : ℤ) (a : Fin 6 → ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((q : ℂ) * Complex.I * z) *
    ∏ j : Fin 6, Complex.exp ((β : ℂ) * Complex.cos (z + (a j : ℂ)))


noncomputable def wilsonLinkFourierIntegral (β : ℝ) (q : ℤ) (a : Fin 6 → ℝ) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), wilsonLinkIntegrand β q a (x : ℂ)


/-- The normalized complex plaquette factor in (3.33). -/
noncomputable def wilsonShiftFactor (β α φ : ℝ) : ℂ :=
  Complex.exp (-(β * (Real.cosh α - 1) : ℝ)) *
    Complex.exp ((β : ℂ) *
      (Complex.cos ((φ : ℂ) + (α : ℂ) * Complex.I) - Complex.cos (φ : ℂ)))

theorem wilsonShiftFactor_norm_le_one {β α φ : ℝ} (hβ : 0 ≤ β) :
    ‖wilsonShiftFactor β α φ‖ ≤ 1 := by
  have hcos :
      (Complex.cos ((φ : ℂ) + (α : ℂ) * Complex.I) - Complex.cos (φ : ℂ)).re =
        Real.cos φ * (Real.cosh α - 1) := by
    rw [show ((α : ℂ) * Complex.I) = (↑α : ℂ) * Complex.I by rfl,
      Complex.cos_add_mul_I,
      (Complex.ofReal_cos φ).symm, (Complex.ofReal_sin φ).symm,
      (Complex.ofReal_cosh α).symm, (Complex.ofReal_sinh α).symm]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.I_re, Complex.I_im]
    ring_nf
  have hcosle : Real.cos φ - 1 ≤ 0 := by linarith [Real.cos_le_one φ]
  have hcosh : 0 ≤ Real.cosh α - 1 := by linarith [Real.one_le_cosh α]
  have hprod : (Real.cos φ - 1) * (Real.cosh α - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcosle hcosh
  have hnorm : ‖wilsonShiftFactor β α φ‖ =
      Real.exp (-(β * (Real.cosh α - 1))) *
        Real.exp (β * Real.cos φ * (Real.cosh α - 1)) := by
    simp [wilsonShiftFactor, Complex.norm_exp, Complex.mul_re,
      Complex.sub_re, hcos]
    ring
  have hbc : β * (Real.cos φ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hβ hcosle
  have hexp : β * (Real.cos φ - 1) * (Real.cosh α - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hbc hcosh
  rw [hnorm]
  rw [← Real.exp_add]
  have hcombine : -(β * (Real.cosh α - 1)) +
      β * Real.cos φ * (Real.cosh α - 1) =
        β * (Real.cos φ - 1) * (Real.cosh α - 1) := by ring
  rw [hcombine]
  exact Real.exp_le_one_iff.mpr hexp

theorem wilsonShiftFactor_conj (β α φ : ℝ) :
    star (wilsonShiftFactor β α φ) = wilsonShiftFactor β (-α) φ := by
  have harg : star ((φ : ℂ) + (α : ℂ) * Complex.I) =
      (φ : ℂ) + (-α : ℂ) * Complex.I := by simp
  have hcosA : star (Complex.cos ((φ : ℂ) + (α : ℂ) * Complex.I)) =
      Complex.cos ((φ : ℂ) + (-α : ℂ) * Complex.I) := by
    calc
      _ = Complex.cos (star ((φ : ℂ) + (α : ℂ) * Complex.I)) :=
        (Complex.cos_conj _).symm
      _ = _ := by rw [harg]
  have hcosφ : star (Complex.cos (φ : ℂ)) = Complex.cos (φ : ℂ) := by
    rw [← Complex.ofReal_cos]
    exact Complex.conj_ofReal _
  have hphase : star ((β : ℂ) *
      (Complex.cos ((φ : ℂ) + (α : ℂ) * Complex.I) - Complex.cos (φ : ℂ))) =
      (β : ℂ) *
        (Complex.cos ((φ : ℂ) + (-α : ℂ) * Complex.I) - Complex.cos (φ : ℂ)) := by
    rw [star_mul, star_sub, hcosA, hcosφ]
    simp
    ring
  have hreal : star (-(↑(β * (Real.cosh α - 1) : ℝ) : ℂ)) =
      -(↑(β * (Real.cosh (-α) - 1) : ℝ) : ℂ) := by
    simp only [star_neg, Complex.star_def, Complex.conj_ofReal, Real.cosh_neg]
  simp only [wilsonShiftFactor]
  rw [star_mul,
    show star (Complex.exp ((β : ℂ) *
        (Complex.cos ((φ : ℂ) + (α : ℂ) * Complex.I) - Complex.cos (φ : ℂ)))) =
      Complex.exp (star ((β : ℂ) *
        (Complex.cos ((φ : ℂ) + (α : ℂ) * Complex.I) - Complex.cos (φ : ℂ)))) from
      (Complex.exp_conj _).symm,
    show star (Complex.exp (-(↑(β * (Real.cosh α - 1) : ℝ) : ℂ))) =
      Complex.exp (star (-(↑(β * (Real.cosh α - 1) : ℝ) : ℂ))) from
      (Complex.exp_conj _).symm,
    hphase, hreal]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem wilsonShiftFactor_reflect (β α φ : ℝ) :
    wilsonShiftFactor β α (-φ) = wilsonShiftFactor β (-α) φ := by
  have harg : ((-φ : ℝ) : ℂ) + (α : ℂ) * Complex.I =
      -(((φ : ℝ) : ℂ) + (-α : ℂ) * Complex.I) := by
    push_cast
    ring_nf
  have hcosh : Real.cosh (-α) = Real.cosh α := Real.cosh_neg _
  have hphi : Complex.cos ((-φ : ℝ) : ℂ) = Complex.cos (φ : ℂ) := by
    push_cast
    rw [Complex.cos_neg]
  rw [wilsonShiftFactor, wilsonShiftFactor, harg, Complex.cos_neg, hphi, hcosh]
  simp

/-- The six-plaquette factors attached to a finite selected link family. -/
noncomputable def wilsonShiftProduct {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (θ : ι → Fin 6 → ℝ) : ℂ :=
  ∏ i : ι, ∏ j : Fin 6, wilsonShiftFactor β (α i) (θ i j)

/-- The real phase paired with a finite plaquette field and its current
coefficients. -/
noncomputable def wilsonCurrentPhase {ι : Type*} [Fintype ι]
    (q : ι → Fin 6 → ℝ) (θ : ι → Fin 6 → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : Fin 6, q i j * θ i j

/-- The two conjugate terms defining the real factor `F` in (3.36). -/
noncomputable def wilsonRenormalizedF {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (q θ : ι → Fin 6 → ℝ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp
      (Complex.I * (wilsonCurrentPhase q θ : ℂ)) *
      wilsonShiftProduct β α θ +
    (1 / 2 : ℂ) * Complex.exp
      (-Complex.I * (wilsonCurrentPhase q θ : ℂ)) *
      wilsonShiftProduct β (fun i => -α i) θ

theorem wilsonShiftProduct_norm_le_one {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (θ : ι → Fin 6 → ℝ) (hβ : 0 ≤ β) :
    ‖wilsonShiftProduct β α θ‖ ≤ 1 := by
  classical
  unfold wilsonShiftProduct
  simp only [norm_prod]
  have hinner0 (i : ι) :
      0 ≤ ∏ j : Fin 6, ‖wilsonShiftFactor β (α i) (θ i j)‖ :=
    Finset.prod_nonneg fun j hj => norm_nonneg _
  have hinner1 (i : ι) :
      ∏ j : Fin 6, ‖wilsonShiftFactor β (α i) (θ i j)‖ ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j hj
      exact norm_nonneg _
    · intro j hj
      exact wilsonShiftFactor_norm_le_one hβ
  calc
    (∏ i : ι, ∏ j : Fin 6,
      ‖wilsonShiftFactor β (α i) (θ i j)‖) ≤ ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact hinner0 i
        · intro i hi
          exact hinner1 i
    _ = 1 := by simp

theorem wilsonShiftProduct_conj {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (θ : ι → Fin 6 → ℝ) :
    star (wilsonShiftProduct β α θ) = wilsonShiftProduct β (fun i => -α i) θ := by
  classical
  simp [wilsonShiftProduct, wilsonShiftFactor_conj]

theorem wilsonShiftProduct_reflect {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (θ : ι → Fin 6 → ℝ) :
    wilsonShiftProduct β α (fun i j => -θ i j) =
      wilsonShiftProduct β (fun i => -α i) θ := by
  classical
  simp [wilsonShiftProduct, wilsonShiftFactor_reflect]

theorem wilsonCurrentPhase_neg {ι : Type*} [Fintype ι]
    (q θ : ι → Fin 6 → ℝ) :
    wilsonCurrentPhase q (fun i j => -θ i j) = -wilsonCurrentPhase q θ := by
  simp [wilsonCurrentPhase, Finset.sum_neg_distrib, mul_neg]

theorem wilsonRenormalizedF_conj_eq {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (q θ : ι → Fin 6 → ℝ) :
    star (wilsonRenormalizedF β α q θ) = wilsonRenormalizedF β α q θ := by
  classical
  have hchar (t : ℝ) :
      (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ))) =
        Complex.exp (-Complex.I * (t : ℂ)) := by
    rw [(Complex.exp_conj _).symm]
    simp
  have hcharNeg (t : ℝ) :
      (starRingEnd ℂ) (Complex.exp (-(Complex.I * (t : ℂ)))) =
        Complex.exp (Complex.I * (t : ℂ)) := by
    rw [(Complex.exp_conj _).symm]
    simp
  simp [wilsonRenormalizedF, hchar, hcharNeg, wilsonShiftProduct_conj]
  ring

theorem wilsonRenormalizedF_norm_le_one {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (q θ : ι → Fin 6 → ℝ) (hβ : 0 ≤ β) :
    ‖wilsonRenormalizedF β α q θ‖ ≤ 1 := by
  classical
  have hphase (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hplus := wilsonShiftProduct_norm_le_one β α θ hβ
  have hminus := wilsonShiftProduct_norm_le_one β (fun i => -α i) θ hβ
  unfold wilsonRenormalizedF
  calc
    _ ≤ ‖(1 / 2 : ℂ) * Complex.exp
          (Complex.I * (wilsonCurrentPhase q θ : ℂ)) *
          wilsonShiftProduct β α θ‖ +
        ‖(1 / 2 : ℂ) * Complex.exp
          (-Complex.I * (wilsonCurrentPhase q θ : ℂ)) *
          wilsonShiftProduct β (fun i => -α i) θ‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) + 1 / 2 := by
      apply add_le_add
      · rw [norm_mul, norm_mul]
        simp [hphase, hplus]
      · rw [norm_mul, norm_mul]
        have hphase' : ‖Complex.exp
            (-Complex.I * (wilsonCurrentPhase q θ : ℂ))‖ = 1 := by
          rw [Complex.norm_exp]
          simp [Complex.mul_re]
        rw [hphase']
        have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
        rw [hhalf]
        nlinarith [hminus]
    _ = 1 := by norm_num

theorem wilsonRenormalizedF_even {ι : Type*} [Fintype ι]
    (β : ℝ) (α : ι → ℝ) (q θ : ι → Fin 6 → ℝ) :
    wilsonRenormalizedF β α q (fun i j => -θ i j) =
      wilsonRenormalizedF β α q θ := by
  classical
  simp [wilsonRenormalizedF, wilsonCurrentPhase_neg,
    wilsonShiftProduct_reflect]
  ring

/-- The one-current activity after integrating the selected links. The
coefficient factor is retained as `K`; the exponential is the product of the
six-plaquette contour bounds. -/
noncomputable def sourceLocalActivity (β L K selectedMass : ℝ) : ℝ :=
  K * Real.exp (6 * β * (Real.cosh 1 - 1) * L - selectedMass)

/-- Source-shaped corrected estimate: the Fourier/combinatorial input is the
explicit premise `K ≤ exp(cK L + ‖ρ‖₁/N)`, and the contour loss is charged to
the selected links, which carry at least one eighteenth of `‖ρ‖₁`. -/
theorem sourceLocalActivity_linearEnvelope
    (β cK N L mass selectedMass K : ℝ)
    (_hβ : 0 ≤ β) (hN : 0 < N)
    (hK : K ≤ Real.exp (cK * L + mass / N))
    (hselection : mass / 18 ≤ selectedMass) :
    sourceLocalActivity β L K selectedMass ≤
      Real.exp ((cK + 6 * β * (Real.cosh 1 - 1)) * L -
        ((N / 18 - 1) / N) * mass) := by
  have hcosh : 0 ≤ Real.cosh 1 - 1 := by
    linarith [Real.one_le_cosh (1 : ℝ)]
  have hmassReduce : mass / N - selectedMass ≤
      -((N / 18 - 1) / N) * mass := by
    calc
      mass / N - selectedMass ≤ mass / N - mass / 18 := by linarith [hselection]
      _ = -((N / 18 - 1) / N) * mass := by
        field_simp [ne_of_gt hN]
        ring
  have hexp : cK * L + mass / N +
      (6 * β * (Real.cosh 1 - 1) * L - selectedMass) ≤
        (cK + 6 * β * (Real.cosh 1 - 1)) * L -
          ((N / 18 - 1) / N) * mass := by
    calc
      _ = (cK + 6 * β * (Real.cosh 1 - 1)) * L +
          (mass / N - selectedMass) := by ring
      _ ≤ _ := by
        calc
          _ = (mass / N - selectedMass) +
              (cK + 6 * β * (Real.cosh 1 - 1)) * L := by ring
          _ ≤ (cK + 6 * β * (Real.cosh 1 - 1)) * L -
              ((N / 18 - 1) / N) * mass := by
            calc
              _ ≤ -((N / 18 - 1) / N) * mass +
                  (cK + 6 * β * (Real.cosh 1 - 1)) * L :=
                    add_le_add_left hmassReduce _
              _ = _ := by ring
  calc
    sourceLocalActivity β L K selectedMass ≤
        Real.exp (cK * L + mass / N) *
          Real.exp (6 * β * (Real.cosh 1 - 1) * L - selectedMass) :=
      mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ = Real.exp (cK * L + mass / N +
          (6 * β * (Real.cosh 1 - 1) * L - selectedMass)) := by
      rw [← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

/-- The length cost coming from the source factors `3^{N₁(supp ρ)}` and the
per-link Fourier prefactor `2`, using the §2 neighborhood bound. -/
noncomputable def sourceKLengthCoefficient : ℝ :=
  (4 * 7 ^ 4 : ℕ) * Real.log 3 + Real.log 2

/-- The explicit upper coefficient in the source bound (3.19) after applying
the one-link Fourier estimate (3.14) with `ε=1`. -/
noncomputable def sourceFourierKEnvelope {B : SourceBox}
    (N : ℝ) (j : IntegerCurrent B) : ℝ :=
  (3 : ℝ) ^ (oneNeighborSet j.support).card *
    ∏ e ∈ j.support, 2 * Real.exp (|(j e : ℝ)| / N)

private theorem source_three_pow_eq_exp_log (n : ℕ) :
    (3 : ℝ) ^ n = Real.exp (Real.log 3 * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Nat.cast_succ, mul_add, Real.exp_add, ih]
      simp [Real.exp_log (by norm_num : (0 : ℝ) < 3)]

private theorem source_two_pow_eq_exp_log (n : ℕ) :
    (2 : ℝ) ^ n = Real.exp (Real.log 2 * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Nat.cast_succ, mul_add, Real.exp_add, ih]
      simp [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The full combinatorial/Fourier coefficient envelope grows at most
exponentially in support length plus `‖ρ‖₁/N`, with an explicit, volume
independent length constant. This is the concrete input to the corrected
activity estimate. -/
theorem sourceFourierKEnvelope_le_exponential {B : SourceBox}
    (N : ℝ) (j : IntegerCurrent B) :
    sourceFourierKEnvelope N j ≤
      Real.exp (sourceKLengthCoefficient * (j.support.card : ℝ) +
        sourceCurrentL1Mass j / N) := by
  classical
  let S := j.support
  have hneighbor := oneNeighborSet_card_le_localConstant S
  have hneighborR : ((oneNeighborSet S).card : ℝ) ≤
      (4 * 7 ^ 4 : ℕ) * (S.card : ℝ) := by exact_mod_cast hneighbor
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3bound := mul_le_mul_of_nonneg_left hneighborR hlog3
  have hsum : (∑ e ∈ S, |(j e : ℝ)| / N) =
      sourceCurrentL1Mass j / N := by
    unfold sourceCurrentL1Mass
    rw [Finset.sum_div]
  have hprod :
      (∏ e ∈ S, 2 * Real.exp (|(j e : ℝ)| / N)) =
        Real.exp (Real.log 2 * (S.card : ℝ) +
          sourceCurrentL1Mass j / N) := by
    calc
      (∏ e ∈ S, 2 * Real.exp (|(j e : ℝ)| / N)) =
          (2 : ℝ) ^ S.card *
            ∏ e ∈ S, Real.exp (|(j e : ℝ)| / N) := by
              rw [Finset.prod_mul_distrib]
              simp
      _ = Real.exp (Real.log 2 * (S.card : ℝ)) *
            Real.exp (∑ e ∈ S, |(j e : ℝ)| / N) := by
              rw [source_two_pow_eq_exp_log, ← Real.exp_sum]
      _ = Real.exp (Real.log 2 * (S.card : ℝ) +
            sourceCurrentL1Mass j / N) := by rw [hsum, Real.exp_add]
  have hthree :
      (3 : ℝ) ^ (oneNeighborSet S).card =
        Real.exp (Real.log 3 * ((oneNeighborSet S).card : ℝ)) :=
    source_three_pow_eq_exp_log _
  calc
    sourceFourierKEnvelope N j =
        Real.exp (Real.log 3 * ((oneNeighborSet S).card : ℝ)) *
          Real.exp (Real.log 2 * (S.card : ℝ) +
            sourceCurrentL1Mass j / N) := by
              rw [sourceFourierKEnvelope, hthree, hprod]
    _ = Real.exp (Real.log 3 * ((oneNeighborSet S).card : ℝ) +
          Real.log 2 * (S.card : ℝ) + sourceCurrentL1Mass j / N) := by
            rw [← Real.exp_add]
            congr 1
            ring
    _ ≤ Real.exp (sourceKLengthCoefficient * (S.card : ℝ) +
          sourceCurrentL1Mass j / N) := by
            apply Real.exp_le_exp.mpr
            unfold sourceKLengthCoefficient
            have hconst : ((4 * 7 ^ 4 : ℕ) : ℝ) = 9604 := by norm_num
            rw [hconst] at hlog3bound
            nlinarith [hlog3bound]

/-- Monotonicity transfers the modewise Fourier bound (3.14) through the
source's combinatorial product bound (3.19) to the explicit `K` envelope. -/
theorem sourceK_le_sourceFourierKEnvelope {B : SourceBox}
    (N : ℝ) (j : IntegerCurrent B) (K : ℝ)
    (modeCoefficient : SourceDualOneCells B → ℝ)
    (hK : K ≤ (3 : ℝ) ^ (oneNeighborSet j.support).card *
      ∏ e ∈ j.support, modeCoefficient e)
    (hmode : ∀ e ∈ j.support,
      0 ≤ modeCoefficient e ∧
        modeCoefficient e ≤ 2 * Real.exp (|(j e : ℝ)| / N)) :
    K ≤ sourceFourierKEnvelope N j := by
  have hprod :
      (∏ e ∈ j.support, modeCoefficient e) ≤
        ∏ e ∈ j.support, 2 * Real.exp (|(j e : ℝ)| / N) := by
    apply Finset.prod_le_prod₀
    · intro e he
      exact (hmode e he).1
    · intro e he
      exact (hmode e he).2
  calc
    K ≤ (3 : ℝ) ^ (oneNeighborSet j.support).card *
        ∏ e ∈ j.support, modeCoefficient e := hK
    _ ≤ (3 : ℝ) ^ (oneNeighborSet j.support).card *
        ∏ e ∈ j.support, 2 * Real.exp (|(j e : ℝ)| / N) := by
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = sourceFourierKEnvelope N j := rfl


theorem sourceKLengthCoefficient_nonneg : 0 ≤ sourceKLengthCoefficient := by
  unfold sourceKLengthCoefficient
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity


end FroehlichSpencer.FS82.ZN.Renormalization

end
