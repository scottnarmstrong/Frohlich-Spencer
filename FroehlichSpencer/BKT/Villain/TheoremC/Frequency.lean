/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.CurrentFormula

/-! # Rooted Villain characters at arbitrary integer frequency -/

@[expose] public section

open Complex MeasureTheory

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

open FroehlichSpencer.BKT.Villain

variable {V E : Type*} {z : V} [Fintype V] [Fintype E] [DecidableEq V]

/-- The rooted spin character with integer frequency `ξ`. -/
def villainFrequencyCharacter (site : FreeVertices V z) (ξ : ℤ)
    (θ : FreeAngles V z) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * (θ site : ℂ))

/-- The source constraint after inserting a frequency-`ξ` rooted character. -/
def villainFrequencyCurrent (G : Multigraph V E) (z : V) (site : FreeVertices V z)
    (ξ : ℤ) (q : E → ℤ) : Prop :=
  ∀ k, k ≠ z → currentDivergence G q k = if k = site.1 then ξ else 0

/-- Gaussian current weights restricted to the source constraint for frequency `ξ`. -/
noncomputable def villainFrequencyCurrentGaussianWeight (G : Multigraph V E) (z : V)
    (site : FreeVertices V z) (β : ℝ) (ξ : ℤ) (q : E → ℤ) : ℝ := by
  classical
  exact if villainFrequencyCurrent G z site ξ q then currentGaussianWeight β q else 0

/-- The source-shifted Fourier term for a frequency-`ξ` character. -/
def villainFrequencyFourierTerm (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (ξ : ℤ) (q : E → ℤ) (θ : FreeAngles V z) : ℂ :=
  currentFourierTerm G z β q θ *
    Complex.exp (Complex.I * (ξ : ℂ) * (θ site : ℂ))

/-- The unnormalized rooted Villain density with a frequency-`ξ` spin character inserted. -/
def villainFrequencyCharacterIntegrand (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (ξ : ℤ) (θ : FreeAngles V z) : ℂ :=
  (∏ e, (villainWeight β
    (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
      villainFrequencyCharacter site ξ θ

/-- The normalized rooted Villain character expectation at arbitrary integer frequency. -/
noncomputable def villainFrequencyCharacterExpectation (G : Multigraph V E) (z : V)
    (β : ℝ) (site : FreeVertices V z) (ξ : ℤ) : ℂ :=
  (∫ θ, villainFrequencyCharacterIntegrand G z β site ξ θ ∂rootedAngleMeasure z) /
    (villainPartitionFunction G z β : ℂ)

private theorem villainFrequencyFourierTerm_norm (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (ξ : ℤ) (q : E → ℤ) (θ : FreeAngles V z) :
    ‖villainFrequencyFourierTerm G z β site ξ q θ‖ = currentGaussianWeight β q := by
  rw [villainFrequencyFourierTerm, norm_mul, currentFourierTerm_norm, Complex.norm_exp]
  have hre : (Complex.I * (ξ : ℂ) * (θ site : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero, mul_one]

private theorem continuous_villainFrequencyFourierTerm (G : Multigraph V E) (z : V)
    (β : ℝ) (site : FreeVertices V z) (ξ : ℤ) (q : E → ℤ) :
    Continuous (fun θ : FreeAngles V z => villainFrequencyFourierTerm G z β site ξ q θ) := by
  unfold villainFrequencyFourierTerm currentFourierTerm
  fun_prop

/-- The arbitrary-frequency current series can be integrated term by term. -/
theorem integral_villainFrequencyFourierTerm_tsum (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (ξ : ℤ) (hβ : 0 < β) :
    (∫ θ, ∑' q : E → ℤ, villainFrequencyFourierTerm G z β site ξ q θ
      ∂rootedAngleMeasure z) =
      ∑' q : E → ℤ, ∫ θ, villainFrequencyFourierTerm G z β site ξ q θ
        ∂rootedAngleMeasure z := by
  classical
  let μ := rootedAngleMeasure z
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ, rootedAngleMeasure]
    infer_instance
  change (∫ θ, ∑' q : E → ℤ, villainFrequencyFourierTerm G z β site ξ q θ ∂μ) = _
  apply integral_tsum
  · intro q
    exact (continuous_villainFrequencyFourierTerm G z β site ξ q).aestronglyMeasurable
  · have hweight := currentGaussianWeight_summable (E := E) β hβ
    have hsum : (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) ≠ ⊤ :=
      hweight.tsum_ofReal_ne_top
    have hμ : μ Set.univ ≠ ⊤ := ne_of_lt hfinite.measure_univ_lt_top
    have hconst (q : E → ℤ) :
        (∫⁻ θ, ‖villainFrequencyFourierTerm G z β site ξ q θ‖ₑ ∂μ) =
          ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
      have hpoint (θ : FreeAngles V z) :
          ‖villainFrequencyFourierTerm G z β site ξ q θ‖ₑ =
            ENNReal.ofReal (currentGaussianWeight β q) := by
        rw [← ofReal_norm, villainFrequencyFourierTerm_norm]
      rw [show (fun θ : FreeAngles V z =>
          ‖villainFrequencyFourierTerm G z β site ξ q θ‖ₑ) =
          fun _ => ENNReal.ofReal (currentGaussianWeight β q) from funext hpoint]
      simp [lintegral_const]
    calc
      (∑' q : E → ℤ, ∫⁻ θ,
          ‖villainFrequencyFourierTerm G z β site ξ q θ‖ₑ ∂μ) =
          ∑' q : E → ℤ,
            ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
        apply tsum_congr
        exact hconst
      _ = (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) * μ Set.univ :=
        ENNReal.tsum_mul_right
      _ ≠ ⊤ := ENNReal.mul_ne_top hsum hμ

/-- Rooted angle orthogonality imposes precisely the scaled source divergence. -/
private theorem villainFrequencyPhase_prod (G : Multigraph V E) (z : V)
    (site : FreeVertices V z) (ξ : ℤ) (q : E → ℤ) (θ : FreeAngles V z) :
    (∏ k : FreeVertices V z,
      Complex.exp (Complex.I * (-(currentDivergence G q k.1) : ℂ) * (θ k : ℂ))) *
        Complex.exp (Complex.I * (ξ : ℂ) * (θ site : ℂ)) =
      ∏ k : FreeVertices V z,
        Complex.exp (Complex.I *
          ((-(currentDivergence G q k.1) +
            if k.1 = site.1 then ξ else 0 : ℤ) : ℂ) * (θ k : ℂ)) := by
  classical
  have hone :
      (∏ k : FreeVertices V z,
        if k = site then Complex.exp (Complex.I * (ξ : ℂ) * (θ k : ℂ)) else 1) =
      Complex.exp (Complex.I * (ξ : ℂ) * (θ site : ℂ)) := by
    simp
  rw [← hone, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hks : k.1 = site.1
  · have hks' : k = site := Subtype.ext hks
    subst k
    simp only [↓reduceIte]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · have hks' : k ≠ site := fun h => hks (congrArg Subtype.val h)
    simp [hks, hks']

private theorem villainFrequencyFourierTerm_eq (G : Multigraph V E) (z : V)
    (β : ℝ) (site : FreeVertices V z) (ξ : ℤ) (q : E → ℤ)
    (θ : FreeAngles V z) :
    villainFrequencyFourierTerm G z β site ξ q θ =
      (currentGaussianWeight β q : ℂ) *
        ∏ k : FreeVertices V z,
          Complex.exp (Complex.I *
            ((-(currentDivergence G q k.1) +
              if k.1 = site.1 then ξ else 0 : ℤ) : ℂ) * (θ k : ℂ)) := by
  unfold villainFrequencyFourierTerm currentFourierTerm
  rw [mul_assoc, villainFrequencyPhase_prod]

theorem integral_villainFrequencyFourierTerm (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (ξ : ℤ) (q : E → ℤ) :
    (∫ θ, villainFrequencyFourierTerm G z β site ξ q θ ∂rootedAngleMeasure z) =
      (villainFrequencyCurrentGaussianWeight G z site β ξ q : ℂ) *
        (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z) := by
  classical
  rw [show (fun θ : FreeAngles V z => villainFrequencyFourierTerm G z β site ξ q θ) =
      fun θ => (currentGaussianWeight β q : ℂ) *
        ∏ k : FreeVertices V z,
          Complex.exp (Complex.I *
            ((-(currentDivergence G q k.1) +
              if k.1 = site.1 then ξ else 0 : ℤ) : ℂ) * (θ k : ℂ)) from
        funext (villainFrequencyFourierTerm_eq G z β site ξ q)]
  rw [integral_const_mul]
  let n : FreeVertices V z → ℤ := fun k =>
    -currentDivergence G q k.1 + if k.1 = site.1 then ξ else 0
  have horth :
      (∫ θ : FreeAngles V z,
          ∏ k : FreeVertices V z,
            Complex.exp (Complex.I * (n k : ℂ) * (θ k : ℂ))
          ∂rootedAngleMeasure z) =
        if villainFrequencyCurrent G z site ξ q then
          (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z) else 0 := by
    have hn : n = 0 ↔ villainFrequencyCurrent G z site ξ q := by
      constructor
      · intro h k hk
        have hval := congrFun h ⟨k, hk⟩
        by_cases hks : k = site.1
        · simp [n, hks] at hval ⊢
          omega
        · simp [n, hks] at hval ⊢
          omega
      · intro h
        funext k
        by_cases hks : k.1 = site.1
        · have hk := h k.1 k.2
          have hk' : currentDivergence G q k.1 = ξ := by simpa [hks] using hk
          have hk'' : currentDivergence G q site.1 = ξ := by simpa [hks] using hk'
          simp [n, hks, hk'']
        · have hk := h k.1 k.2
          have hk' : currentDivergence G q k.1 = 0 := by simpa [hks] using hk
          simp [n, hks, hk']
    have horth0 := FroehlichSpencer.BKT.integral_product_character_Ico n
    simpa [rootedAngleMeasure, n, hn] using horth0
  rw [horth]
  by_cases hq : villainFrequencyCurrent G z site ξ q
  · simp [villainFrequencyCurrentGaussianWeight, hq]
  · simp [villainFrequencyCurrentGaussianWeight, hq]

private theorem villainFrequencyCharacter_fourierExpansion (G : Multigraph V E) (z : V)
    (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) (ξ : ℤ)
    (θ : FreeAngles V z) :
    villainFrequencyCharacterIntegrand G z β site ξ θ =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ, villainFrequencyFourierTerm G z β site ξ q θ := by
  unfold villainFrequencyCharacterIntegrand villainFrequencyCharacter
  rw [villain_product_fourier_pointwise G z β hβ θ]
  calc
    (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        (∑' q : E → ℤ, currentFourierTerm G z β q θ) *
          Complex.exp (Complex.I * (ξ : ℂ) * (θ site : ℂ)) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ, currentFourierTerm G z β q θ *
          Complex.exp (Complex.I * (ξ : ℂ) * (θ site : ℂ)) := by
      calc
        _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
            ((∑' q : E → ℤ, currentFourierTerm G z β q θ) *
              Complex.exp (Complex.I * (ξ : ℂ) * (θ site : ℂ))) := by ring
        _ = _ := by
          congr 1
          rw [← tsum_mul_right]
    _ = _ := by rfl

omit [Fintype V] in
theorem villainFrequencyCurrentGaussianWeight_summable (G : Multigraph V E)
    (z : V) (site : FreeVertices V z) (β : ℝ) (ξ : ℤ) (hβ : 0 < β) :
    Summable (villainFrequencyCurrentGaussianWeight G z site β ξ) := by
  classical
  apply Summable.of_norm_bounded (currentGaussianWeight_summable (E := E) β hβ)
  intro q
  by_cases hq : villainFrequencyCurrent G z site ξ q
  · simp [villainFrequencyCurrentGaussianWeight, hq, Real.norm_eq_abs,
      abs_of_pos (currentGaussianWeight_pos β q)]
  · simp [villainFrequencyCurrentGaussianWeight, hq]
    exact (currentGaussianWeight_pos β q).le

/-- The arbitrary-frequency rooted Villain expectation is the current-sum ratio with source
current divergence `ξ` at the observed vertex and `−ξ` at the root. -/
theorem villainFrequencyCharacterExpectation_eq_currentRatio (G : Multigraph V E)
    (z : V) (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) (ξ : ℤ) :
    villainFrequencyCharacterExpectation G z β site ξ =
      (∑' q : E → ℤ,
          (villainFrequencyCurrentGaussianWeight G z site β ξ q : ℂ)) /
        (∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ)) := by
  classical
  let A : ℝ := ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
    (2 * Real.pi) ^ Fintype.card (FreeVertices V z)
  have hnum :
      (∫ θ, villainFrequencyCharacterIntegrand G z β site ξ θ ∂rootedAngleMeasure z) =
        (A : ℂ) *
          (∑' q : E → ℤ,
            (villainFrequencyCurrentGaussianWeight G z site β ξ q : ℂ)) := by
    rw [show (fun θ => villainFrequencyCharacterIntegrand G z β site ξ θ) =
        fun θ => (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∑' q : E → ℤ, villainFrequencyFourierTerm G z β site ξ q θ from
        funext (villainFrequencyCharacter_fourierExpansion G z β hβ site ξ)]
    rw [integral_const_mul, integral_villainFrequencyFourierTerm_tsum G z β site ξ hβ]
    rw [show (∑' q : E → ℤ,
        ∫ θ, villainFrequencyFourierTerm G z β site ξ q θ ∂rootedAngleMeasure z) =
        (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z) *
          (∑' q : E → ℤ,
            (villainFrequencyCurrentGaussianWeight G z site β ξ q : ℂ)) from ?_]
    · simp only [A, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring
    · calc
        _ = ∑' q : E → ℤ,
              (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z) *
                (villainFrequencyCurrentGaussianWeight G z site β ξ q : ℂ) := by
            apply tsum_congr
            intro q
            rw [integral_villainFrequencyFourierTerm]
            by_cases hq : villainFrequencyCurrent G z site ξ q
            · simp [villainFrequencyCurrentGaussianWeight, hq]
              ring
            · simp [villainFrequencyCurrentGaussianWeight, hq]
        _ = _ := tsum_mul_left
  have hden : (villainPartitionFunction G z β : ℂ) =
      (A : ℂ) *
        (∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ)) := by
    have hden0 := villain_partition_current_expansion G z β hβ
    rw [villainPartitionFunction, hden0]
    simp only [A, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_tsum,
      Complex.ofReal_ofNat]
  have hA : (A : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    dsimp [A]
    have hp : 0 < (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact ne_of_gt (mul_pos (pow_pos hp _) (pow_pos (by positivity) _))
  have hneutralR : 0 < ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q :=
    neutralCurrentGaussianWeight_tsum_pos G z β hβ
  have hneutral : (∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_tsum]
    exact_mod_cast hneutralR.ne'
  unfold villainFrequencyCharacterExpectation
  rw [hnum, hden]
  field_simp [hA, hneutral]

/-- The arbitrary-frequency rooted Villain expectation is the real ratio of its source and neutral
current sums. -/
theorem villainFrequencyCharacterExpectation_eq_realCurrentRatio (G : Multigraph V E)
    (z : V) (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) (ξ : ℤ) :
    villainFrequencyCharacterExpectation G z β site ξ =
      ((∑' q : E → ℤ, villainFrequencyCurrentGaussianWeight G z site β ξ q) /
        (∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q) : ℂ) := by
  rw [villainFrequencyCharacterExpectation_eq_currentRatio G z β hβ site ξ]
  rw [← Complex.ofReal_tsum]
  rw [← Complex.ofReal_tsum]

end FroehlichSpencer.BKT.Villain.TheoremC

end
