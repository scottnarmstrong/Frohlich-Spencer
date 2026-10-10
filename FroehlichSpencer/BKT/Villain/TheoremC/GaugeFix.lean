/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.Models
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox
public import FroehlichSpencer.BKT.Villain.TheoremC.Frequency

/-! # Gauge fixing for the finite free Villain system

The current expansion makes the gauge quotient explicit: the full product-circle integral imposes
the divergence constraint at every vertex, while the rooted integral imposes it off the pinned root.
The current divergence sums to zero, so the missing root constraint follows from the others.
-/

@[expose] public section

open MeasureTheory Complex
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The angle coordinates relative to the chosen root, before reducing modulo `2π`. -/
def fullAnglePinned (root : V) (θ : V → ℝ) : FreeAngles V root :=
  fun k => θ k.1 - θ root

/-- The full vertex character induced by the rooted source-shifted Fourier phase. -/
def fullFrequencyVector (G : Multigraph V E) (root : V) (site : FreeVertices V root)
    (ξ : ℤ) (q : E → ℤ) : V → ℤ := fun v =>
  if _hv : v ≠ root then
    -currentDivergence G q v + if v = site.1 then ξ else 0
  else
    -∑ k : FreeVertices V root,
      (-currentDivergence G q k.1 + if k.1 = site.1 then ξ else 0)

/-- The complex Villain density with a full product-circle character inserted. -/
def villainGraphCharacterIntegrand (G : Multigraph V E) (root : V) (β : ℝ)
    (site : FreeVertices V root) (ξ : ℤ) (θ : V → ℝ) : ℂ :=
  (∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e)) : ℂ)) *
    Complex.exp (Complex.I * (ξ : ℂ) * ((θ site.1 - θ root : ℝ) : ℂ))

/-- The full free-vertex Villain Gibbs law associated with an oriented finite graph. -/
def villainGraphGibbs (G : Multigraph V E) (β : ℝ) : Measure (V → ℝ) :=
  pairGibbs circleMeasure (multigraphFrequency G) (fun _ => villainWeight β)

private theorem fullFrequencyVector_zero_iff (G : Multigraph V E) (root : V)
    (site : FreeVertices V root) (ξ : ℤ) (q : E → ℤ) :
    fullFrequencyVector G root site ξ q = 0 ↔ villainFrequencyCurrent G root site ξ q := by
  classical
  constructor
  · intro h k hk
    have hval :
        -currentDivergence G q k + (if k = site.1 then ξ else 0) = 0 := by
      simpa [fullFrequencyVector, hk] using congrFun h k
    by_cases hks : k = site.1 <;> simp [hks] at hval ⊢ <;> omega
  · intro h
    funext v
    by_cases hv : v = root
    · subst v
      have hcoeff : ∀ k : FreeVertices V root,
          -currentDivergence G q k.1 + (if k.1 = site.1 then ξ else 0) = 0 := by
        intro k
        have hk := h k.1 k.2
        by_cases hks : k.1 = site.1
        · have hk' : currentDivergence G q k.1 = ξ := by simpa [hks] using hk
          have hk'' : currentDivergence G q site.1 = ξ := by rw [← hks]; exact hk'
          simp [hks, hk'']
        · have hk' : currentDivergence G q k.1 = 0 := by simpa [hks] using hk
          simp [hks, hk']
      have hsumzero :
          ∑ k : FreeVertices V root,
            (-currentDivergence G q k.1 + if k.1 = site.1 then ξ else 0) = 0 :=
        Finset.sum_eq_zero (fun k hk => hcoeff k)
      simp [fullFrequencyVector, hsumzero]
    · have hlocal := h v hv
      simp [fullFrequencyVector, hv, hlocal]

private theorem villainFrequencyFourierTerm_full_eq (G : Multigraph V E) (root : V)
    (β : ℝ) (site : FreeVertices V root) (ξ : ℤ) (q : E → ℤ) (θ : V → ℝ) :
    villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ) =
      (currentGaussianWeight β q : ℂ) *
        Complex.exp (Complex.I *
          ∑ v : V, (fullFrequencyVector G root site ξ q v : ℂ) * (θ v : ℂ)) := by
  classical
  let a : FreeVertices V root → ℤ := fun k =>
    -currentDivergence G q k.1 + if k.1 = site.1 then ξ else 0
  have hsum :
      ∑ k : FreeVertices V root, (a k : ℂ) *
          (((θ k.1 - θ root : ℝ) : ℂ)) =
        ∑ v : V, (fullFrequencyVector G root site ξ q v : ℂ) * (θ v : ℂ) := by
    have hleft :
        (∑ k : FreeVertices V root, (a k : ℂ) *
          (((θ k.1 - θ root : ℝ) : ℂ))) =
          (∑ k : FreeVertices V root, (a k : ℂ) * (θ k.1 : ℂ)) -
            (∑ k : FreeVertices V root, (a k : ℂ)) * (θ root : ℂ) := by
      simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    have hright :
        (∑ v : V, (fullFrequencyVector G root site ξ q v : ℂ) * (θ v : ℂ)) =
          (∑ k : FreeVertices V root, (a k : ℂ) * (θ k.1 : ℂ)) -
            (∑ k : FreeVertices V root, (a k : ℂ)) * (θ root : ℂ) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne
        (fun v : V => (fullFrequencyVector G root site ξ q v : ℂ) * (θ v : ℂ)) root]
      have hroot :
          (fullFrequencyVector G root site ξ q root : ℂ) =
            -∑ k : FreeVertices V root, (a k : ℂ) := by
        simp [fullFrequencyVector, a, Int.cast_sum]
      have hfree (k : FreeVertices V root) :
          fullFrequencyVector G root site ξ q k.1 = a k := by
        have heq : (k.1 = site.1) ↔ k = site :=
          ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
        simp [fullFrequencyVector, a, k.2, heq]
      rw [hroot]
      simp_rw [hfree]
      ring
    rw [hleft, hright]
  have harg :
      (∑ k : FreeVertices V root,
        Complex.I * (-(currentDivergence G q k.1) : ℂ) *
          ((θ k.1 - θ root : ℝ) : ℂ)) +
        Complex.I * (ξ : ℂ) * ((θ site.1 - θ root : ℝ) : ℂ) =
      Complex.I * ∑ k : FreeVertices V root,
        (a k : ℂ) * ((θ k.1 - θ root : ℝ) : ℂ) := by
    have hdelta :
        (∑ k : FreeVertices V root,
          if k.1 = site.1 then (ξ : ℂ) * ((θ k.1 - θ root : ℝ) : ℂ) else 0) =
          (ξ : ℂ) * ((θ site.1 - θ root : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single site]
      · simp
      · intro k hk hne
        simp [show k.1 ≠ site.1 from fun h => hne (Subtype.ext h)]
      · intro hnot
        exact (hnot (Finset.mem_univ site)).elim
    have hfactor :
        (∑ k : FreeVertices V root,
          Complex.I * (-(currentDivergence G q k.1) : ℂ) *
            ((θ k.1 - θ root : ℝ) : ℂ)) =
          Complex.I * (∑ k : FreeVertices V root,
            (-(currentDivergence G q k.1) : ℂ) *
              ((θ k.1 - θ root : ℝ) : ℂ)) := by
      calc
        _ = ∑ k : FreeVertices V root,
              Complex.I * ((-(currentDivergence G q k.1) : ℂ) *
                ((θ k.1 - θ root : ℝ) : ℂ)) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = _ := by rw [Finset.mul_sum]
    have hsplit :
        (∑ k : FreeVertices V root,
          ((-(currentDivergence G q k.1) : ℂ) *
              ((θ k.1 - θ root : ℝ) : ℂ) +
            (if k.1 = site.1 then (ξ : ℂ) * ((θ k.1 - θ root : ℝ) : ℂ) else 0))) =
          (∑ k : FreeVertices V root,
            (-(currentDivergence G q k.1) : ℂ) *
              ((θ k.1 - θ root : ℝ) : ℂ)) +
            (ξ : ℂ) * ((θ site.1 - θ root : ℝ) : ℂ) := by
      calc
        _ = (∑ k : FreeVertices V root,
              (-(currentDivergence G q k.1) : ℂ) *
                ((θ k.1 - θ root : ℝ) : ℂ)) +
              ∑ k : FreeVertices V root,
                (if k.1 = site.1 then (ξ : ℂ) * ((θ k.1 - θ root : ℝ) : ℂ) else 0) :=
          Finset.sum_add_distrib
        _ = _ := by rw [hdelta]
    calc
      _ = (Complex.I * (∑ k : FreeVertices V root,
            (-(currentDivergence G q k.1) : ℂ) *
              ((θ k.1 - θ root : ℝ) : ℂ)) +
            Complex.I * (ξ : ℂ) * ((θ site.1 - θ root : ℝ) : ℂ)) := by
              exact congrArg₂ (· + ·) hfactor rfl
      _ = Complex.I *
          ((∑ k : FreeVertices V root,
            (-(currentDivergence G q k.1) : ℂ) *
              ((θ k.1 - θ root : ℝ) : ℂ)) +
            (ξ : ℂ) * ((θ site.1 - θ root : ℝ) : ℂ)) := by ring
      _ = Complex.I * ∑ k : FreeVertices V root,
          ((-(currentDivergence G q k.1) : ℂ) *
              ((θ k.1 - θ root : ℝ) : ℂ) +
            (if k.1 = site.1 then (ξ : ℂ) * ((θ k.1 - θ root : ℝ) : ℂ) else 0)) := by
              exact congrArg (fun t : ℂ => Complex.I * t) hsplit.symm
      _ = Complex.I * ∑ k : FreeVertices V root,
          (a k : ℂ) * ((θ k.1 - θ root : ℝ) : ℂ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hks : k.1 = site.1
              · simp [a, hks]
                ring
              · simp [a, hks]
  unfold villainFrequencyFourierTerm currentFourierTerm
  rw [← Complex.exp_sum]
  calc
    (currentGaussianWeight β q : ℂ) *
        Complex.exp (∑ k : FreeVertices V root,
          Complex.I * (-(currentDivergence G q k.1) : ℂ) *
            ((fullAnglePinned root θ k : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (ξ : ℂ) *
          ((fullAnglePinned root θ site : ℝ) : ℂ)) =
      (currentGaussianWeight β q : ℂ) *
        Complex.exp ((∑ k : FreeVertices V root,
          Complex.I * (-(currentDivergence G q k.1) : ℂ) *
            ((θ k.1 - θ root : ℝ) : ℂ)) +
          Complex.I * (ξ : ℂ) * ((θ site.1 - θ root : ℝ) : ℂ)) := by
            calc
              _ = (currentGaussianWeight β q : ℂ) *
                  (Complex.exp (∑ k : FreeVertices V root,
                    Complex.I * (-(currentDivergence G q k.1) : ℂ) *
                      ((fullAnglePinned root θ k : ℝ) : ℂ)) *
                    Complex.exp (Complex.I * (ξ : ℂ) *
                      ((fullAnglePinned root θ site : ℝ) : ℂ))) := by ring
              _ = (currentGaussianWeight β q : ℂ) *
                  Complex.exp ((∑ k : FreeVertices V root,
                    Complex.I * (-(currentDivergence G q k.1) : ℂ) *
                      ((fullAnglePinned root θ k : ℝ) : ℂ)) +
                    Complex.I * (ξ : ℂ) *
                      ((fullAnglePinned root θ site : ℝ) : ℂ)) := by
                    rw [← Complex.exp_add]
              _ = _ := by simp only [fullAnglePinned]
    _ = (currentGaussianWeight β q : ℂ) *
        Complex.exp (Complex.I * ∑ k : FreeVertices V root,
          (a k : ℂ) * ((θ k.1 - θ root : ℝ) : ℂ)) := by rw [harg]
    _ = _ := by rw [hsum]

private theorem integral_villainFrequencyFourierTerm_full (G : Multigraph V E)
    (root : V) (β : ℝ) (site : FreeVertices V root) (ξ : ℤ) (q : E → ℤ) :
    (∫ θ : V → ℝ,
      villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ)
        ∂siteProduct circleMeasure V) =
      (villainFrequencyCurrentGaussianWeight G root site β ξ q : ℂ) *
        (2 * Real.pi : ℂ) ^ Fintype.card V := by
  classical
  have hchar (θ : V → ℝ) :
      Complex.exp (Complex.I *
        ∑ v : V, (fullFrequencyVector G root site ξ q v : ℂ) * (θ v : ℂ)) =
        character (fullFrequencyVector G root site ξ q) θ := by
    unfold character
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [show (fun θ : V → ℝ =>
      villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ)) =
      fun θ => (currentGaussianWeight β q : ℂ) *
        character (fullFrequencyVector G root site ξ q) θ from by
          funext θ
          rw [villainFrequencyFourierTerm_full_eq, hchar]]
  rw [integral_const_mul, integral_character_siteProduct hasRealFourier_circle]
  have horth :
      ((∏ v : V, circleFourier (fullFrequencyVector G root site ξ q v) : ℝ) : ℂ) =
        if villainFrequencyCurrent G root site ξ q then
          (2 * Real.pi : ℂ) ^ Fintype.card V else 0 := by
    have hzero_iff : fullFrequencyVector G root site ξ q = 0 ↔
        villainFrequencyCurrent G root site ξ q :=
      fullFrequencyVector_zero_iff G root site ξ q
    rw [← hzero_iff]
    by_cases hzero : fullFrequencyVector G root site ξ q = 0
    · simp [hzero, circleFourier, Complex.ofReal_pow, Complex.ofReal_mul,
        Complex.ofReal_ofNat]
    · have hne : ∃ v, fullFrequencyVector G root site ξ q v ≠ 0 := by
        by_contra h
        push Not at h
        exact hzero (funext h)
      obtain ⟨v, hv⟩ := hne
      have hzeroFactor : circleFourier (fullFrequencyVector G root site ξ q v) = 0 := by
        simp [circleFourier, hv]
      rw [Finset.prod_eq_zero (Finset.mem_univ v) hzeroFactor]
      simp [hzero]
  rw [horth]
  by_cases hq : villainFrequencyCurrent G root site ξ q
  · simp [villainFrequencyCurrentGaussianWeight, hq]
  · simp [villainFrequencyCurrentGaussianWeight, hq]

private theorem villainFrequencyFourierTerm_full_norm (G : Multigraph V E)
    (root : V) (β : ℝ) (site : FreeVertices V root) (ξ : ℤ) (q : E → ℤ)
    (θ : V → ℝ) :
    ‖villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ)‖ =
      currentGaussianWeight β q := by
  rw [villainFrequencyFourierTerm, norm_mul, currentFourierTerm_norm, Complex.norm_exp]
  have hre : (Complex.I * (ξ : ℂ) *
      (fullAnglePinned root θ site : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero, mul_one]

private theorem continuous_villainFrequencyFourierTerm_full (G : Multigraph V E)
    (root : V) (β : ℝ) (site : FreeVertices V root) (ξ : ℤ) (q : E → ℤ) :
    Continuous (fun θ : V → ℝ =>
      villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ)) := by
  unfold villainFrequencyFourierTerm currentFourierTerm fullAnglePinned
  fun_prop

private theorem integral_villainFrequencyFourierTerm_full_tsum (G : Multigraph V E)
    (root : V) (β : ℝ) (site : FreeVertices V root) (ξ : ℤ) (hβ : 0 < β) :
    (∫ θ : V → ℝ, ∑' q : E → ℤ,
      villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ)
        ∂siteProduct circleMeasure V) =
      ∑' q : E → ℤ, ∫ θ : V → ℝ,
        villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ)
          ∂siteProduct circleMeasure V := by
  classical
  let μ := siteProduct circleMeasure V
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ, siteProduct]
    infer_instance
  change (∫ θ, ∑' q : E → ℤ,
    villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ) ∂μ) = _
  apply integral_tsum
  · intro q
    exact (continuous_villainFrequencyFourierTerm_full G root β site ξ q).aestronglyMeasurable
  · have hweight := currentGaussianWeight_summable (E := E) β hβ
    have hsum : (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) ≠ ⊤ :=
      hweight.tsum_ofReal_ne_top
    have hμ : μ Set.univ ≠ ⊤ := ne_of_lt hfinite.measure_univ_lt_top
    have hconst (q : E → ℤ) :
        (∫⁻ θ, ‖villainFrequencyFourierTerm G root β site ξ q
          (fullAnglePinned root θ)‖ₑ ∂μ) =
          ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
      have hpoint (θ : V → ℝ) :
          ‖villainFrequencyFourierTerm G root β site ξ q
            (fullAnglePinned root θ)‖ₑ = ENNReal.ofReal (currentGaussianWeight β q) := by
        rw [← ofReal_norm, villainFrequencyFourierTerm_full_norm]
      rw [show (fun θ : V → ℝ =>
          ‖villainFrequencyFourierTerm G root β site ξ q
            (fullAnglePinned root θ)‖ₑ) = fun _ =>
          ENNReal.ofReal (currentGaussianWeight β q) from funext hpoint]
      simp [lintegral_const]
    calc
      (∑' q : E → ℤ, ∫⁻ θ,
          ‖villainFrequencyFourierTerm G root β site ξ q
            (fullAnglePinned root θ)‖ₑ ∂μ) =
          ∑' q : E → ℤ,
            ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
        apply tsum_congr
        exact hconst
      _ = (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) * μ Set.univ :=
        ENNReal.tsum_mul_right
      _ ≠ ⊤ := ENNReal.mul_ne_top hsum hμ

private theorem villainGraphCharacter_fourierExpansion (G : Multigraph V E)
    (root : V) (β : ℝ) (hβ : 0 < β) (site : FreeVertices V root) (ξ : ℤ)
    (θ : V → ℝ) :
    villainGraphCharacterIntegrand G root β site ξ θ =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ,
          villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ) := by
  unfold villainGraphCharacterIntegrand
  have hpinned := villain_product_fourier_pointwise G root β hβ
    (fullAnglePinned root θ)
  have hweight :
      (∏ e, (villainWeight β
          (pinnedAngle root (fullAnglePinned root θ) (G.src e) -
            pinnedAngle root (fullAnglePinned root θ) (G.tgt e)) : ℂ)) =
        ∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e)) : ℂ) := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hs : G.src e = root <;> by_cases ht : G.tgt e = root <;>
      simp [pinnedAngle, fullAnglePinned, hs, ht]
  rw [← hweight, hpinned]
  calc
    (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        (∑' q : E → ℤ, currentFourierTerm G root β q (fullAnglePinned root θ)) *
        Complex.exp (Complex.I * (ξ : ℂ) *
          ((θ site.1 - θ root : ℝ) : ℂ)) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ,
          currentFourierTerm G root β q (fullAnglePinned root θ) *
            Complex.exp (Complex.I * (ξ : ℂ) *
              ((θ site.1 - θ root : ℝ) : ℂ)) := by
      calc
        _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
            ((∑' q : E → ℤ, currentFourierTerm G root β q
              (fullAnglePinned root θ)) *
              Complex.exp (Complex.I * (ξ : ℂ) *
                ((θ site.1 - θ root : ℝ) : ℂ))) := by ring
        _ = _ := by congr 1; rw [← tsum_mul_right]
    _ = _ := rfl

private theorem integral_villainGraphCharacterIntegrand_eq (G : Multigraph V E)
    (root : V) (β : ℝ) (hβ : 0 < β) (site : FreeVertices V root) (ξ : ℤ) :
    (∫ θ : V → ℝ, villainGraphCharacterIntegrand G root β site ξ θ
      ∂siteProduct circleMeasure V) =
      ((((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
        (2 * Real.pi) ^ Fintype.card V : ℝ) : ℂ) * ∑' q : E → ℤ,
        (villainFrequencyCurrentGaussianWeight G root site β ξ q : ℂ) := by
  classical
  let A : ℝ := ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
    (2 * Real.pi) ^ Fintype.card V
  have hpoint :
      (fun θ : V → ℝ => villainGraphCharacterIntegrand G root β site ξ θ) =
        fun θ => (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∑' q : E → ℤ,
            villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ) := by
    funext θ
    exact villainGraphCharacter_fourierExpansion G root β hβ site ξ θ
  have hsum :
      (∑' q : E → ℤ,
        ∫ θ : V → ℝ,
          villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ)
            ∂siteProduct circleMeasure V) =
        (2 * Real.pi : ℂ) ^ Fintype.card V *
          ∑' q : E → ℤ,
            (villainFrequencyCurrentGaussianWeight G root site β ξ q : ℂ) := by
    calc
      _ = ∑' q : E → ℤ,
            (2 * Real.pi : ℂ) ^ Fintype.card V *
              (villainFrequencyCurrentGaussianWeight G root site β ξ q : ℂ) := by
        apply tsum_congr
        intro q
        rw [integral_villainFrequencyFourierTerm_full]
        by_cases hq : villainFrequencyCurrent G root site ξ q
        · simp [villainFrequencyCurrentGaussianWeight, hq]
          ring
        · simp [villainFrequencyCurrentGaussianWeight, hq]
      _ = _ := by rw [tsum_mul_left]
  rw [show (fun θ : V → ℝ => villainGraphCharacterIntegrand G root β site ξ θ) =
      fun θ => (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ,
          villainFrequencyFourierTerm G root β site ξ q (fullAnglePinned root θ) from hpoint]
  rw [integral_const_mul,
    integral_villainFrequencyFourierTerm_full_tsum G root β site ξ hβ, hsum]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- The full finite graph Villain character, computed in the product-circle law, equals the
rooted Villain character expectation. -/
theorem integral_villainGraphGibbs_cos_eq_rootedFrequency
    (G : Multigraph V E) (root : V) (β : ℝ) (hβ : 0 < β)
    (site : FreeVertices V root) (ξ : ℤ) :
    (∫ θ : V → ℝ,
      Real.cos (ξ * (θ site.1 - θ root)) ∂villainGraphGibbs G β) =
      (villainFrequencyCharacterExpectation G root β site ξ).re := by
  classical
  let A : ℝ := ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
    (2 * Real.pi) ^ Fintype.card V
  let w : E → ℝ → ℝ := fun _ => villainWeight β
  let d : E → Frequency V := multigraphFrequency G
  have hw : ∀ e, IsBondWeight (w e) := by
    intro e
    simpa [w] using isBondWeight_villain hβ
  have hIntChar : Integrable (villainGraphCharacterIntegrand G root β site ξ)
      (siteProduct circleMeasure V) := by
    have hcont : Continuous (villainGraphCharacterIntegrand G root β site ξ) := by
      unfold villainGraphCharacterIntegrand
      apply Continuous.mul
      · apply continuous_finsetProd
        intro e he
        exact continuous_ofReal.comp
          ((isBondWeight_villain hβ).continuous.comp (by fun_prop))
      · fun_prop
    obtain ⟨C, hC⟩ := exists_pairWeight_le (d := d) hw
    refine Integrable.of_bound hcont.aestronglyMeasurable C
      (ae_of_all _ fun θ => ?_)
    unfold villainGraphCharacterIntegrand
    have hphase : ‖Complex.exp (Complex.I * (ξ : ℂ) *
        (((θ site.1 - θ root : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      have hRe : (Complex.I * (ξ : ℂ) *
          (((θ site.1 - θ root : ℝ) : ℂ))).re = 0 := by simp [Complex.mul_re]
      rw [hRe, Real.exp_zero]
    have hweight :
        ‖∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e)) : ℂ)‖ =
          pairWeight d w θ := by
      rw [norm_prod]
      simp only [pairWeight, d, w, Complex.norm_real, Real.norm_eq_abs,
        phase_multigraphFrequency]
      apply Finset.prod_congr rfl
      intro e he
      exact abs_of_pos (VillainWeight.villainWeight_pos hβ _)
    rw [Complex.norm_mul, hphase, mul_one, hweight]
    exact hC θ
  have hnum :
      (∫ θ : V → ℝ,
        (villainGraphCharacterIntegrand G root β site ξ θ).re
          ∂siteProduct circleMeasure V) =
        A * ∑' q : E → ℤ,
          villainFrequencyCurrentGaussianWeight G root site β ξ q := by
    have hRe := integral_re hIntChar
    calc
      _ = (∫ θ : V → ℝ,
            villainGraphCharacterIntegrand G root β site ξ θ
              ∂siteProduct circleMeasure V).re := hRe
      _ = _ := by
        rw [integral_villainGraphCharacterIntegrand_eq G root β hβ site ξ]
        rw [← Complex.ofReal_tsum]
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have h0 : ∀ q : E → ℤ,
      villainFrequencyCurrentGaussianWeight G root site β 0 q =
        neutralCurrentGaussianWeight G root β q := by
    intro q
    have hconstraint : villainFrequencyCurrent G root site 0 q ↔
        neutralAwayFrom G root q := by
      simp [villainFrequencyCurrent, neutralAwayFrom]
    simp [villainFrequencyCurrentGaussianWeight, neutralCurrentGaussianWeight, hconstraint]
  have hzero :
      (∫ θ : V → ℝ,
        (∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e)) : ℂ))
          ∂siteProduct circleMeasure V) =
        (A : ℂ) * ∑' q : E → ℤ,
          (neutralCurrentGaussianWeight G root β q : ℂ) := by
    have h := integral_villainGraphCharacterIntegrand_eq G root β hβ site 0
    have hcast :
        (fun q : E → ℤ =>
          (villainFrequencyCurrentGaussianWeight G root site β 0 q : ℂ)) =
        fun q => (neutralCurrentGaussianWeight G root β q : ℂ) := by
      funext q
      exact congrArg Complex.ofReal (h0 q)
    simpa [villainGraphCharacterIntegrand] using
      (h.trans (congrArg (fun f : (E → ℤ) → ℂ => (A : ℂ) * ∑' q, f q)
        hcast))
  have hdenComplex :
      (∫ θ : V → ℝ, (pairWeight d w θ : ℂ)
        ∂siteProduct circleMeasure V) =
        (A : ℂ) * ∑' q : E → ℤ,
          (neutralCurrentGaussianWeight G root β q : ℂ) := by
    have hpair :
        (∫ θ : V → ℝ, (pairWeight d w θ : ℂ)
          ∂siteProduct circleMeasure V) =
          ∫ θ : V → ℝ,
            ∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e)) : ℂ)
              ∂siteProduct circleMeasure V := by
      apply integral_congr_ae
      filter_upwards with θ
      simp [pairWeight, d, w, phase_multigraphFrequency]
    exact hpair.trans hzero
  have hden : pairPartition circleMeasure d w =
      A * ∑' q : E → ℤ, neutralCurrentGaussianWeight G root β q := by
    have hcoerce := congrArg Complex.re
      (integral_complex_ofReal (f := pairWeight d w) (μ := siteProduct circleMeasure V))
    rw [hdenComplex] at hcoerce
    rw [← Complex.ofReal_tsum] at hcoerce
    rw [← Complex.ofReal_mul, Complex.ofReal_re] at hcoerce
    simpa [pairPartition, A] using hcoerce.symm
  have hneutral : 0 < ∑' q : E → ℤ,
      neutralCurrentGaussianWeight G root β q :=
    neutralCurrentGaussianWeight_tsum_pos G root β hβ
  have hA : A ≠ 0 := by
    dsimp [A]
    positivity
  have hcosRaw :
      (∫ θ : V → ℝ,
        Real.cos (ξ * (θ site.1 - θ root)) * pairWeight d w θ
          ∂siteProduct circleMeasure V) =
        (∫ θ : V → ℝ,
          (villainGraphCharacterIntegrand G root β site ξ θ).re
            ∂siteProduct circleMeasure V) := by
    apply integral_congr_ae
    filter_upwards with θ
    have hprod :
        (∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e)) : ℂ)) =
          (pairWeight d w θ : ℂ) := by
      simp [pairWeight, d, w, phase_multigraphFrequency]
    have hcharRe :
        (Complex.exp (Complex.I * (ξ : ℂ) *
          ((θ site.1 - θ root : ℝ) : ℂ))).re =
          Real.cos (ξ * (θ site.1 - θ root)) := by
      rw [Complex.exp_re]
      have hRe : (Complex.I * (ξ : ℂ) *
          ((θ site.1 - θ root : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
      have hIm : (Complex.I * (ξ : ℂ) *
          ((θ site.1 - θ root : ℝ) : ℂ)).im =
            ξ * (θ site.1 - θ root) := by simp [Complex.mul_im]
      rw [hRe, Real.exp_zero, hIm]
      simp
    rw [villainGraphCharacterIntegrand, hprod, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hcharRe]
    ring
  rw [show villainGraphGibbs G β = pairGibbs circleMeasure d w from rfl,
    integral_pairGibbs circleMeasure_univ_ne_zero hw, hcosRaw, hnum, hden]
  rw [villainFrequencyCharacterExpectation_eq_realCurrentRatio G root β hβ site ξ]
  have hneutralC :
      (∑' q : E → ℤ, (neutralCurrentGaussianWeight G root β q : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_tsum]
    exact_mod_cast hneutral.ne'
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  field_simp [hA, hneutral.ne', hneutralC]
  simp only [Complex.normSq_ofReal]
  ring_nf

end FroehlichSpencer.BKT.Villain.TheoremC

end
