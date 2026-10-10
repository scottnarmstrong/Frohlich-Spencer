/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.CurrentIntegral

/-!
# Orthogonality constraints for Villain currents

The root-pinned product character integral imposes zero divergence away from the pinned vertex,
or a unit source when a spin character is inserted (KP §6.1, p. 33).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FroehlichSpencer.BKT.Villain

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The nonnegative Gaussian weight restricted to currents neutral away from the root. -/
noncomputable def neutralCurrentGaussianWeight (G : Multigraph V E) (z : V) (β : ℝ)
    (q : E → ℤ) : ℝ := by
  classical
  exact if neutralAwayFrom G z q then currentGaussianWeight β q else 0

/-- Positivity of the finite product defining the Gaussian current weight. -/
theorem currentGaussianWeight_pos (β : ℝ) (q : E → ℤ) :
    0 < currentGaussianWeight β q := by
  unfold currentGaussianWeight
  exact Finset.prod_pos fun e he => Real.exp_pos _

omit [Fintype V] in
/-- The neutral current weights are summable, by domination by the unrestricted Gaussian weights.
-/
theorem neutralCurrentGaussianWeight_summable (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) :
    Summable (fun q : E → ℤ => neutralCurrentGaussianWeight G z β q) := by
  classical
  apply Summable.of_norm_bounded (currentGaussianWeight_summable (E := E) β hβ)
  intro q
  by_cases hn : neutralAwayFrom G z q
  · simp [neutralCurrentGaussianWeight, hn, Real.norm_eq_abs,
      abs_of_pos (currentGaussianWeight_pos β q)]
  · simp [neutralCurrentGaussianWeight, hn]
    exact (currentGaussianWeight_pos β q).le

omit [Fintype V] in
/-- The neutral current partition sum is strictly positive because the zero current is admissible.
-/
theorem neutralCurrentGaussianWeight_tsum_pos (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) :
    0 < ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q := by
  classical
  let q₀ : E → ℤ := fun _ => 0
  have hneutral : neutralAwayFrom G z q₀ := by
    intro j hj
    simp [q₀, currentDivergence]
  have hweight : 0 < currentGaussianWeight β q₀ := currentGaussianWeight_pos β q₀
  refine Summable.tsum_pos (neutralCurrentGaussianWeight_summable G z β hβ) ?_ q₀ ?_
  · intro q
    by_cases hn : neutralAwayFrom G z q
    · simp [neutralCurrentGaussianWeight, hn]
      exact (currentGaussianWeight_pos β q).le
    · simp [neutralCurrentGaussianWeight, hn]
  · simpa [neutralCurrentGaussianWeight, hneutral] using hweight

/-- The Gaussian weight restricted to currents with a unit source at `j` and a compensating sink
at the pinned root. -/
noncomputable def sourceCurrentGaussianWeight (G : Multigraph V E) (z j : V) (β : ℝ)
    (q : E → ℤ) : ℝ := by
  classical
  exact if characterCurrent G z j q then currentGaussianWeight β q else 0

omit [Fintype V] in
/-- Unit-source current weights are summable by domination by the unrestricted Gaussian weights. -/
theorem sourceCurrentGaussianWeight_summable (G : Multigraph V E) (z j : V) (β : ℝ)
    (hβ : 0 < β) :
    Summable (fun q : E → ℤ => sourceCurrentGaussianWeight G z j β q) := by
  classical
  apply Summable.of_norm_bounded (currentGaussianWeight_summable (E := E) β hβ)
  intro q
  by_cases hq : characterCurrent G z j q
  · simp [sourceCurrentGaussianWeight, hq, Real.norm_eq_abs,
      abs_of_pos (currentGaussianWeight_pos β q)]
  · simp [sourceCurrentGaussianWeight, hq]
    exact (currentGaussianWeight_pos β q).le

/-- Removing the pinned root leaves exactly `card V - 1` integration coordinates. -/
theorem freeVertices_card_sub_one (z : V) :
    Fintype.card (FreeVertices V z) = Fintype.card V - 1 := by
  classical
  simp [FreeVertices, Fintype.card_subtype_compl]


/-- The frequency seen by a non-root angle after regrouping the edge phases. -/
def currentDivergenceFrequency (G : Multigraph V E) (z : V) (q : E → ℤ)
    (j : FreeVertices V z) : ℤ := -(currentDivergence G q j.1)

/-- The free-vertex Fourier frequency after inserting the positive spin character at `site`. -/
def sourceCurrentFrequency (G : Multigraph V E) (z : V) (q : E → ℤ)
    (site k : FreeVertices V z) : ℤ :=
  currentDivergenceFrequency G z q k + if k.1 = site.1 then 1 else 0

/-- The Fourier term for an integer current with the source shift at `site`. -/
def sourceCurrentFourierTerm (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ)
    (site : FreeVertices V z) (θ : FreeAngles V z) : ℂ :=
  (currentGaussianWeight β q : ℂ) *
    ∏ k : FreeVertices V z,
      Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) * (θ k : ℂ))

omit [Fintype V] in
/-- Orthogonality identifies a zero free-vertex frequency with neutrality away from the root. -/
theorem currentDivergenceFrequency_eq_zero_iff (G : Multigraph V E) (z : V) (q : E → ℤ) :
    currentDivergenceFrequency G z q = 0 ↔ neutralAwayFrom G z q := by
  constructor
  · intro h j hj
    have hj' : currentDivergenceFrequency G z q ⟨j, hj⟩ = 0 := congrFun h ⟨j, hj⟩
    exact neg_eq_zero.mp hj'
  · intro h
    funext j
    exact neg_eq_zero.mpr (h j.1 j.2)

omit [Fintype V] in
/-- A zero shifted frequency is exactly a unit-source current at `site`. -/
theorem sourceCurrentFrequency_eq_zero_iff (G : Multigraph V E) (z : V) (q : E → ℤ)
    (site : FreeVertices V z) :
    sourceCurrentFrequency G z q site = 0 ↔ characterCurrent G z site.1 q := by
  constructor
  · intro h k hk
    have hfreq := congrFun h ⟨k, hk⟩
    by_cases hks : k = site.1
    · simp [sourceCurrentFrequency, currentDivergenceFrequency, hks] at hfreq
      simp [hks]
      omega
    · simp [sourceCurrentFrequency, currentDivergenceFrequency, hks] at hfreq
      simp [hks]
      omega
  · intro h
    funext k
    by_cases hks : k.1 = site.1
    · have hdiv : currentDivergence G q k.1 = 1 := by
        simpa [characterCurrent, hks] using h k.1 k.2
      have hdiv' : currentDivergence G q site.1 = 1 := by simpa [hks] using hdiv
      simp [sourceCurrentFrequency, currentDivergenceFrequency, hks, hdiv']
    · have hdiv : currentDivergence G q k.1 = 0 := by
        simpa [characterCurrent, hks] using h k.1 k.2
      simp [sourceCurrentFrequency, currentDivergenceFrequency, hks, hdiv]

/-- Multiplication by the positive spin character shifts the Fourier frequency at exactly its
site. -/
theorem currentFourierTerm_mul_character (G : Multigraph V E) (z : V) (β : ℝ)
    (q : E → ℤ) (site : FreeVertices V z) (θ : FreeAngles V z) :
    currentFourierTerm G z β q θ * Complex.exp (Complex.I * (θ site : ℂ)) =
      sourceCurrentFourierTerm G z β q site θ := by
  classical
  have hprod :
      (∏ k : FreeVertices V z,
        Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) *
          (θ k : ℂ))) =
        (∏ k : FreeVertices V z,
          Complex.exp (Complex.I * (currentDivergenceFrequency G z q k : ℂ) *
            (θ k : ℂ))) * Complex.exp (Complex.I * (θ site : ℂ)) := by
    have hphase (k : FreeVertices V z) :
        Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) * (θ k : ℂ)) =
          Complex.exp (Complex.I * (currentDivergenceFrequency G z q k : ℂ) * (θ k : ℂ)) *
            (if k = site then Complex.exp (Complex.I * (θ k : ℂ)) else 1) := by
      by_cases hks : k = site
      · subst k
        simp [sourceCurrentFrequency]
        rw [← Complex.exp_add]
        congr 1
        ring
      · have hks' : k.1 ≠ site.1 := fun h => hks (Subtype.ext h)
        simp [sourceCurrentFrequency, hks, hks']
    calc
      ∏ k : FreeVertices V z,
          Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) * (θ k : ℂ)) =
          ∏ k : FreeVertices V z,
            (Complex.exp (Complex.I * (currentDivergenceFrequency G z q k : ℂ) *
              (θ k : ℂ)) *
              (if k = site then Complex.exp (Complex.I * (θ k : ℂ)) else 1)) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact hphase k
      _ = (∏ k : FreeVertices V z,
            Complex.exp (Complex.I * (currentDivergenceFrequency G z q k : ℂ) *
              (θ k : ℂ))) *
            ∏ k : FreeVertices V z,
              (if k = site then Complex.exp (Complex.I * (θ k : ℂ)) else 1) :=
        Finset.prod_mul_distrib
      _ = (∏ k : FreeVertices V z,
            Complex.exp (Complex.I * (currentDivergenceFrequency G z q k : ℂ) *
              (θ k : ℂ))) * Complex.exp (Complex.I * (θ site : ℂ)) := by
        simp
  rw [currentFourierTerm, sourceCurrentFourierTerm]
  have hprod' :
      (∏ k : FreeVertices V z,
        Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) *
          (θ k : ℂ))) =
        (∏ k : FreeVertices V z,
          Complex.exp (Complex.I * (-(currentDivergence G q k.1) : ℂ) *
            (θ k : ℂ))) * Complex.exp (Complex.I * (θ site : ℂ)) := by
    simpa [currentDivergenceFrequency] using hprod
  rw [hprod']
  ring

/-- The source-shifted Fourier character has the same norm as its Gaussian current weight. -/
theorem sourceCurrentFourierTerm_norm (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ)
    (site : FreeVertices V z) (θ : FreeAngles V z) :
    ‖sourceCurrentFourierTerm G z β q site θ‖ = currentGaussianWeight β q := by
  classical
  have hweight : 0 < currentGaussianWeight β q := currentGaussianWeight_pos β q
  rw [sourceCurrentFourierTerm, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hweight, Complex.norm_prod]
  have hphase (k : FreeVertices V z) :
      ‖Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) * (θ k : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre :
        (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) * (θ k : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [show ∏ k : FreeVertices V z,
      ‖Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) * (θ k : ℂ))‖ = 1 by
        apply Finset.prod_eq_one
        intro k hk
        exact hphase k]
  simp

/-- Every source-shifted current term is continuous in the free angles. -/
theorem continuous_sourceCurrentFourierTerm (G : Multigraph V E) (z : V) (β : ℝ)
    (q : E → ℤ) (site : FreeVertices V z) :
    Continuous (fun θ : FreeAngles V z => sourceCurrentFourierTerm G z β q site θ) := by
  unfold sourceCurrentFourierTerm
  fun_prop

/-- The source-shifted Fourier series may be integrated term by term, with the same Gaussian
majorant as the partition series. -/
theorem integral_sourceCurrentFourierTerm_tsum (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) (hβ : 0 < β) :
    (∫ θ, ∑' q : E → ℤ, sourceCurrentFourierTerm G z β q site θ
      ∂rootedAngleMeasure z) =
      ∑' q : E → ℤ, ∫ θ, sourceCurrentFourierTerm G z β q site θ
        ∂rootedAngleMeasure z := by
  classical
  let μ := rootedAngleMeasure z
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ, rootedAngleMeasure]
    infer_instance
  change (∫ θ, ∑' q : E → ℤ, sourceCurrentFourierTerm G z β q site θ ∂μ) = _
  apply integral_tsum
  · intro q
    exact (continuous_sourceCurrentFourierTerm G z β q site).aestronglyMeasurable
  · have hweight := currentGaussianWeight_summable (E := E) β hβ
    have hsum :
        (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) ≠ ⊤ :=
      hweight.tsum_ofReal_ne_top
    have hμ : μ Set.univ ≠ ⊤ := ne_of_lt hfinite.measure_univ_lt_top
    have hconst (q : E → ℤ) :
        (∫⁻ θ, ‖sourceCurrentFourierTerm G z β q site θ‖ₑ ∂μ) =
          ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
      have hpoint (θ : FreeAngles V z) :
          ‖sourceCurrentFourierTerm G z β q site θ‖ₑ =
            ENNReal.ofReal (currentGaussianWeight β q) := by
        calc
          ‖sourceCurrentFourierTerm G z β q site θ‖ₑ =
            ENNReal.ofReal ‖sourceCurrentFourierTerm G z β q site θ‖ :=
            (ofReal_norm (sourceCurrentFourierTerm G z β q site θ)).symm
          _ = ENNReal.ofReal (currentGaussianWeight β q) := by
            rw [sourceCurrentFourierTerm_norm]
      rw [show (fun θ : FreeAngles V z => ‖sourceCurrentFourierTerm G z β q site θ‖ₑ) =
          fun _ => ENNReal.ofReal (currentGaussianWeight β q) from funext hpoint]
      simp [lintegral_const]
    calc
      (∑' q : E → ℤ, ∫⁻ θ, ‖sourceCurrentFourierTerm G z β q site θ‖ₑ ∂μ) =
          ∑' q : E → ℤ,
            ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
        apply tsum_congr
        exact hconst
      _ = (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) * μ Set.univ := by
        rw [ENNReal.tsum_mul_right]
      _ ≠ ⊤ := ENNReal.mul_ne_top hsum hμ

/-- Orthogonality integrates a source-shifted current term to zero unless its current has
divergence `+1` at `site` and zero at every other non-root vertex. -/
theorem integral_sourceCurrentFourierTerm (G : Multigraph V E) (z : V) (β : ℝ)
    (q : E → ℤ) (site : FreeVertices V z)
    [Decidable (characterCurrent G z site.1 q)] :
    (∫ θ, sourceCurrentFourierTerm G z β q site θ ∂rootedAngleMeasure z) =
      if characterCurrent G z site.1 q then
        (currentGaussianWeight β q : ℂ) *
          (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z)
      else 0 := by
  classical
  unfold sourceCurrentFourierTerm
  rw [integral_const_mul]
  have horth :
      (∫ θ : FreeAngles V z,
          ∏ k : FreeVertices V z,
            Complex.exp (Complex.I * (sourceCurrentFrequency G z q site k : ℂ) *
              (θ k : ℂ)) ∂rootedAngleMeasure z) =
        if characterCurrent G z site.1 q then
          (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z) else 0 := by
    have horth0 := FroehlichSpencer.BKT.integral_product_character_Ico
      (fun k : FreeVertices V z => sourceCurrentFrequency G z q site k)
    simpa [rootedAngleMeasure, sourceCurrentFrequency_eq_zero_iff] using horth0
  rw [horth]
  by_cases hq : characterCurrent G z site.1 q <;> simp [hq]

/-- The integral of a current term vanishes unless the current is neutral away from the pinned
vertex. -/
theorem integral_currentFourierTerm (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ)
    [Decidable (neutralAwayFrom G z q)] :
    (∫ θ, currentFourierTerm G z β q θ ∂rootedAngleMeasure z) =
      if neutralAwayFrom G z q then
        (currentGaussianWeight β q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z)
      else 0 := by
  classical
  unfold currentFourierTerm
  rw [integral_const_mul]
  have horth :
      (∫ θ : FreeAngles V z,
          ∏ j : FreeVertices V z,
            Complex.exp (Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ))
          ∂rootedAngleMeasure z) =
        if neutralAwayFrom G z q then
          (2 * Real.pi : ℂ) ^ Fintype.card (FreeVertices V z) else 0 := by
    have horth0 :=
      (FroehlichSpencer.BKT.integral_product_character_Ico
        (fun j : FreeVertices V z => -(currentDivergence G q j.1)))
    have hfreq : (fun j : FreeVertices V z => -(currentDivergence G q j.1)) = 0 ↔
        neutralAwayFrom G z q := by
      constructor
      · intro h j hj
        have h' := congrFun h ⟨j, hj⟩
        exact neg_eq_zero.mp h'
      · intro h
        funext j
        exact neg_eq_zero.mpr (h j.1 j.2)
    simpa [rootedAngleMeasure, hfreq] using horth0
  rw [horth]
  by_cases hn : neutralAwayFrom G z q <;> simp [hn]

/-- The partition integral, with the complex integrand displayed as a cast of the real Villain
weight, equals the neutral-current sum. This is KP §1.4, p. 4 and §6.1, p. 33. -/
theorem villain_partition_current_expansion_complex (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) :
    (∫ θ : FreeAngles V z,
      ∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)
        ∂rootedAngleMeasure z) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) *
          ∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ) := by
  classical
  let c : ℂ := (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E
  have hpoint :
      (fun θ : FreeAngles V z =>
        ∏ e, (villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) =
      fun θ => c * ∑' q : E → ℤ, currentFourierTerm G z β q θ := by
    funext θ
    simpa [c] using villain_product_fourier_pointwise G z β hβ θ
  have hsum :
      (∑' q : E → ℤ, ∫ θ, currentFourierTerm G z β q θ ∂rootedAngleMeasure z) =
        ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) *
          ∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ) := by
    calc
      _ = ∑' q : E → ℤ,
            if neutralAwayFrom G z q then
              (currentGaussianWeight β q : ℂ) *
                ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ)
            else 0 := by
        apply tsum_congr
        intro q
        simpa only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat] using
          integral_currentFourierTerm G z β q
      _ = ∑' q : E → ℤ,
            ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) *
              (neutralCurrentGaussianWeight G z β q : ℂ) := by
        apply tsum_congr
        intro q
        by_cases hn : neutralAwayFrom G z q
        · simp [neutralCurrentGaussianWeight, hn]
          ring
        · simp [neutralCurrentGaussianWeight, hn]
      _ = _ := by rw [tsum_mul_left]
  rw [show (∫ θ : FreeAngles V z,
      ∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)
        ∂rootedAngleMeasure z) =
      ∫ θ, c * ∑' q : E → ℤ, currentFourierTerm G z β q θ ∂rootedAngleMeasure z from
        congrArg (fun f : FreeAngles V z → ℂ => ∫ θ, f θ ∂rootedAngleMeasure z) hpoint]
  rw [integral_const_mul, integral_currentFourierTerm_tsum G z β hβ, hsum]
  simp [c]
  ring

/-- The real KP partition integral is the finite volume factor times the neutral-current sum,
with one factor `(2πβ)^(-1/2)` per edge (KP §1.4, p. 4; §6.1, p. 33). -/
theorem villain_partition_current_expansion (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) :
    (∫ θ : FreeAngles V z,
      ∏ e, villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))
        ∂rootedAngleMeasure z) =
      ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
        (2 * Real.pi) ^ Fintype.card (FreeVertices V z) *
          ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q := by
  classical
  have hcast :
      ((∫ θ : FreeAngles V z,
        ∏ e, villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))
          ∂rootedAngleMeasure z : ℝ) : ℂ) =
        (∫ θ : FreeAngles V z,
          ∏ e, (villainWeight β
            (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)
          ∂rootedAngleMeasure z) := by
    calc
      _ = ∫ θ : FreeAngles V z,
          ((∏ e, villainWeight β
            (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℝ) : ℂ)
          ∂rootedAngleMeasure z :=
        (integral_ofReal (f := fun θ : FreeAngles V z =>
          ∏ e, villainWeight β
            (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)))).symm
      _ = ∫ θ : FreeAngles V z,
          ∏ e, (villainWeight β
            (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)
          ∂rootedAngleMeasure z := by
        apply integral_congr_ae
        filter_upwards with θ
        simp only [Complex.ofReal_prod]
  apply Complex.ofReal_injective
  calc
    (↑(∫ θ : FreeAngles V z,
      ∏ e, villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))
        ∂rootedAngleMeasure z : ℝ) : ℂ) =
        ∫ θ : FreeAngles V z,
          ∏ e, (villainWeight β
            (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)
          ∂rootedAngleMeasure z := hcast
    _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) *
            ∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ) :=
      villain_partition_current_expansion_complex G z β hβ
    _ = ↑(((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
          (2 * Real.pi) ^ Fintype.card (FreeVertices V z) *
            ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_tsum]

/-- The rooted Villain partition integral is strictly positive for `β > 0`, so it can normalize
KP's finite-volume Villain measure (KP §1.4, p. 4). -/
theorem villain_partition_integral_pos (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) :
    0 < ∫ θ : FreeAngles V z,
      ∏ e, villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))
        ∂rootedAngleMeasure z := by
  rw [villain_partition_current_expansion G z β hβ]
  have hfactor : 0 < (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hvolume : 0 < (2 * Real.pi) ^ Fintype.card (FreeVertices V z) :=
    pow_pos (by positivity) _
  exact mul_pos (mul_pos (pow_pos hfactor _) hvolume)
    (neutralCurrentGaussianWeight_tsum_pos G z β hβ)

/-- The finite rooted Villain partition function of KP §1.4, p. 4. Its current-sum
characterization is `villain_partition_current_expansion`. -/
noncomputable def villainPartitionFunction (G : Multigraph V E) (z : V) (β : ℝ) : ℝ :=
  ∫ θ : FreeAngles V z,
    ∏ e, villainWeight β
      (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))
      ∂rootedAngleMeasure z

/-- The normalized complex spin-character expectation in the rooted finite Villain measure.
KP §1.4, p. 4. -/
noncomputable def villainCharacterExpectation (G : Multigraph V E) (z : V) (β : ℝ)
    (site : FreeVertices V z) : ℂ :=
  (∫ θ : FreeAngles V z,
    (∏ e, (villainWeight β
      (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
      Complex.exp (Complex.I * (θ site : ℂ)) ∂rootedAngleMeasure z) /
    (villainPartitionFunction G z β : ℂ)

/-- Inserting `exp (I θ_site)` in the product Fourier series shifts the current constraint to
unit divergence at `site`. KP §6.1, p. 33. -/
theorem villain_product_fourier_with_character_pointwise (G : Multigraph V E) (z : V)
    (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) (θ : FreeAngles V z) :
    (∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
        Complex.exp (Complex.I * (θ site : ℂ)) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ, sourceCurrentFourierTerm G z β q site θ := by
  classical
  let c : ℂ := (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E
  rw [villain_product_fourier_pointwise G z β hβ θ]
  calc
    (c * ∑' q : E → ℤ, currentFourierTerm G z β q θ) *
        Complex.exp (Complex.I * (θ site : ℂ)) =
        c * ((∑' q : E → ℤ, currentFourierTerm G z β q θ) *
          Complex.exp (Complex.I * (θ site : ℂ))) := by ring
    _ = c * ∑' q : E → ℤ,
          currentFourierTerm G z β q θ * Complex.exp (Complex.I * (θ site : ℂ)) := by
        congr 1
        rw [← tsum_mul_right]
    _ = c * ∑' q : E → ℤ, sourceCurrentFourierTerm G z β q site θ := by
        congr 1
        apply tsum_congr
        intro q
        exact currentFourierTerm_mul_character G z β q site θ
    _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ, sourceCurrentFourierTerm G z β q site θ := by rfl

/-- The complex spin-character observable has a current expansion whose currents have divergence
`+1` at the observed vertex and `−1` at the root. KP §1.4, p. 4 and §6.1, p. 33. -/
theorem villain_character_current_expansion_complex (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) (site : FreeVertices V z) :
    (∫ θ : FreeAngles V z,
      (∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
        Complex.exp (Complex.I * (θ site : ℂ)) ∂rootedAngleMeasure z) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) *
          ∑' q : E → ℤ, (sourceCurrentGaussianWeight G z site.1 β q : ℂ) := by
  classical
  let c : ℂ := (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E
  have hpoint :
      (fun θ : FreeAngles V z =>
        (∏ e, (villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
          Complex.exp (Complex.I * (θ site : ℂ))) =
      fun θ => c * ∑' q : E → ℤ, sourceCurrentFourierTerm G z β q site θ := by
    funext θ
    simpa [c] using villain_product_fourier_with_character_pointwise G z β hβ site θ
  have hsum :
      (∑' q : E → ℤ, ∫ θ, sourceCurrentFourierTerm G z β q site θ
        ∂rootedAngleMeasure z) =
        ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) *
          ∑' q : E → ℤ, (sourceCurrentGaussianWeight G z site.1 β q : ℂ) := by
    calc
      _ = ∑' q : E → ℤ,
            if characterCurrent G z site.1 q then
              (currentGaussianWeight β q : ℂ) *
                ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ)
            else 0 := by
        apply tsum_congr
        intro q
        simpa only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat] using
          (integral_sourceCurrentFourierTerm G z β q site)
      _ = ∑' q : E → ℤ,
            ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) *
              (sourceCurrentGaussianWeight G z site.1 β q : ℂ) := by
        apply tsum_congr
        intro q
        by_cases hq : characterCurrent G z site.1 q
        · simp [sourceCurrentGaussianWeight, hq]
          ring
        · simp [sourceCurrentGaussianWeight, hq]
      _ = _ := by rw [tsum_mul_left]
  rw [show (∫ θ : FreeAngles V z,
      (∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) *
        Complex.exp (Complex.I * (θ site : ℂ)) ∂rootedAngleMeasure z) =
      ∫ θ, c * ∑' q : E → ℤ, sourceCurrentFourierTerm G z β q site θ
        ∂rootedAngleMeasure z from
        congrArg (fun f : FreeAngles V z → ℂ => ∫ θ, f θ ∂rootedAngleMeasure z) hpoint]
  rw [integral_const_mul, integral_sourceCurrentFourierTerm_tsum G z β site hβ, hsum]
  simp [c]
  ring

/-- KP's normalized complex character expectation is the ratio of unit-source and neutral current
partition sums; the common Gaussian normalization and the free-angle volume cancel. KP §1.4, p. 4.
-/
theorem villainCharacterExpectation_eq_current_ratio (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) (site : FreeVertices V z) :
    villainCharacterExpectation G z β site =
      (∑' q : E → ℤ, (sourceCurrentGaussianWeight G z site.1 β q : ℂ)) /
        (∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ)) := by
  classical
  let A : ℝ :=
    ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
      (2 * Real.pi) ^ Fintype.card (FreeVertices V z)
  have hden : (villainPartitionFunction G z β : ℂ) =
      (A : ℂ) * ∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ) := by
    have hden0 := villain_partition_current_expansion G z β hβ
    rw [villainPartitionFunction, hden0]
    simp [A, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_tsum]
  have hneutralReal :
      (∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q) ≠ 0 :=
    ne_of_gt (neutralCurrentGaussianWeight_tsum_pos G z β hβ)
  have hneutral :
      (∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_tsum]
    exact_mod_cast hneutralReal
  have hnum := villain_character_current_expansion_complex G z β hβ site
  have hA : (A : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    dsimp [A]
    have hβ' : 0 < 2 * Real.pi * β := by positivity
    have hfac : 0 < (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos hβ' _
    have hvol : 0 < 2 * Real.pi := by positivity
    exact ne_of_gt (mul_pos (pow_pos hfac _) (pow_pos hvol _))
  unfold villainCharacterExpectation
  rw [hnum, hden]
  have hsourceCast :
      (∑' q : E → ℤ, (sourceCurrentGaussianWeight G z site.1 β q : ℂ)) =
        ((∑' q : E → ℤ, sourceCurrentGaussianWeight G z site.1 β q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
  rw [hsourceCast]
  have hneutralCast :
      (∑' q : E → ℤ, (neutralCurrentGaussianWeight G z β q : ℂ)) =
        ((∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
  rw [hneutralCast]
  field_simp [hA, hneutral]
  simp only [A, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

-- Additional expansion theorems follow below.

end FroehlichSpencer.BKT.Villain

end
