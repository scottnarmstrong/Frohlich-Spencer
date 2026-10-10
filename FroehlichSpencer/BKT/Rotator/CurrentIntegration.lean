/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Fourier.Character
public import FroehlichSpencer.BKT.Villain.CurrentExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Raw angle integration for factorized integer-current terms

This is the finite orthogonality step in the plane-rotator expansion. It is stated for any finite
oriented graph and any real edge coefficient. The raw angle measure keeps the factor `(2π)^{|V|}`
explicit. The edge phase uses the negative current divergence; since cosine coefficients are even,
this convention makes a positive inserted character shift the marked coefficient by `+ξ`, as in
FS81 (1.36). A frequency function can also represent an inserted spin character.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

open FroehlichSpencer.BKT.Villain

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

private instance rotatorAngleCoordinate_isFiniteMeasure :
    IsFiniteMeasure (volume.restrict (Ico (-Real.pi) Real.pi)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top

/-- Raw Lebesgue integration over one angle interval for every spin. -/
def rotatorRawAngleMeasure (V : Type*) [Fintype V] [DecidableEq V] : Measure (V → ℝ) :=
  Measure.pi fun _ : V => volume.restrict (Ico (-Real.pi) Real.pi)

/-- The factorized edge weight of an integer current. -/
def rotatorCurrentWeight (w : ℤ → ℝ) (q : E → ℤ) : ℝ :=
  ∏ e, w (q e)

/-- The character term associated with an edge current and a vertex frequency. -/
def rotatorCurrentFourierTerm (G : Multigraph V E) (w : ℤ → ℝ)
    (q : E → ℤ) (χ : V → ℤ) (θ : V → ℝ) : ℂ :=
  (rotatorCurrentWeight w q : ℂ) *
    ∏ v, Complex.exp (Complex.I *
      ((-currentDivergence G q v + χ v : ℤ) : ℂ) * (θ v : ℂ))

/-- The character factors have modulus one, so the current term's norm is its edge-weight norm. -/
theorem rotatorCurrentFourierTerm_norm (G : Multigraph V E) (w : ℤ → ℝ)
    (q : E → ℤ) (χ : V → ℤ) (θ : V → ℝ) :
    ‖rotatorCurrentFourierTerm G w q χ θ‖ =
      |rotatorCurrentWeight w q| := by
  classical
  rw [rotatorCurrentFourierTerm, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_prod]
  have hphase (v : V) :
      ‖Complex.exp (Complex.I *
        ((-currentDivergence G q v + χ v : ℤ) : ℂ) * (θ v : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (Complex.I *
        ((-currentDivergence G q v + χ v : ℤ) : ℂ) * (θ v : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [show ∏ v : V,
      ‖Complex.exp (Complex.I *
        ((-currentDivergence G q v + χ v : ℤ) : ℂ) * (θ v : ℂ))‖ = 1 by
        apply Finset.prod_eq_one
        intro v hv
        exact hphase v]
  simp

/-- Character orthogonality integrates one current term to zero unless its divergence cancels the
inserted vertex frequency. In the neutral case the raw spin integral contributes `(2π)^{|V|}`. -/
theorem rotatorCurrentFourierTerm_integral (G : Multigraph V E) (w : ℤ → ℝ)
    (q : E → ℤ) (χ : V → ℤ) :
    (∫ θ, rotatorCurrentFourierTerm G w q χ θ ∂rotatorRawAngleMeasure V) =
      if (fun v => -currentDivergence G q v + χ v) = 0 then
        (rotatorCurrentWeight w q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card V
      else 0 := by
  classical
  unfold rotatorCurrentFourierTerm
  unfold rotatorRawAngleMeasure
  rw [integral_const_mul]
  have horth := FroehlichSpencer.BKT.integral_product_character_Ico
    (fun v : V => -currentDivergence G q v + χ v)
  rw [horth]
  by_cases hzero : (fun v => -currentDivergence G q v + χ v) = 0
  · simp [hzero]
  · simp [hzero]

/-- The neutral-current specialization of raw angle orthogonality. -/
theorem rotatorCurrentFourierTerm_integral_neutral (G : Multigraph V E)
    (w : ℤ → ℝ) (q : E → ℤ)
    (hneutral : ∀ v, currentDivergence G q v = 0) :
    (∫ θ, rotatorCurrentFourierTerm G w q (fun _ => 0) θ
      ∂rotatorRawAngleMeasure V) =
        (rotatorCurrentWeight w q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card V := by
  rw [rotatorCurrentFourierTerm_integral]
  have hzero : (fun v => -currentDivergence G q v + (fun _ => 0) v) = 0 := by
    funext v
    simp [hneutral v]
  simp only [ite_eq_left hzero]

/-- Every fixed current term is continuous in the finite angle vector. -/
theorem continuous_rotatorCurrentFourierTerm (G : Multigraph V E) (w : ℤ → ℝ)
    (q : E → ℤ) (χ : V → ℤ) :
    Continuous (fun θ : V → ℝ => rotatorCurrentFourierTerm G w q χ θ) := by
  unfold rotatorCurrentFourierTerm rotatorCurrentWeight
  fun_prop

/-- If the absolute current weights are summable, the raw angle integral commutes with the
current sum. -/
theorem rotatorCurrentFourierTerm_tsum_integral (G : Multigraph V E) (w : ℤ → ℝ)
    (χ : V → ℤ) (hweight : Summable (fun q : E → ℤ => |rotatorCurrentWeight w q|)) :
    (∫ θ, ∑' q : E → ℤ, rotatorCurrentFourierTerm G w q χ θ
      ∂rotatorRawAngleMeasure V) =
        ∑' q : E → ℤ,
          ∫ θ, rotatorCurrentFourierTerm G w q χ θ ∂rotatorRawAngleMeasure V := by
  classical
  let μ := rotatorRawAngleMeasure V
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ, rotatorRawAngleMeasure]
    infer_instance
  change (∫ θ, ∑' q : E → ℤ, rotatorCurrentFourierTerm G w q χ θ ∂μ) = _
  apply integral_tsum
  · intro q
    exact (continuous_rotatorCurrentFourierTerm G w q χ).aestronglyMeasurable
  · have hsum :
        (∑' q : E → ℤ, ENNReal.ofReal |rotatorCurrentWeight w q|) ≠ ⊤ :=
      hweight.tsum_ofReal_ne_top
    have hμ : μ Set.univ ≠ ⊤ := ne_of_lt hfinite.measure_univ_lt_top
    have hconst (q : E → ℤ) :
        (∫⁻ θ, ‖rotatorCurrentFourierTerm G w q χ θ‖ₑ ∂μ) =
          ENNReal.ofReal |rotatorCurrentWeight w q| * μ Set.univ := by
      have hpoint (θ : V → ℝ) :
          ‖rotatorCurrentFourierTerm G w q χ θ‖ₑ =
            ENNReal.ofReal |rotatorCurrentWeight w q| := by
        calc
          ‖rotatorCurrentFourierTerm G w q χ θ‖ₑ =
              ENNReal.ofReal ‖rotatorCurrentFourierTerm G w q χ θ‖ :=
            (ofReal_norm _).symm
          _ = ENNReal.ofReal |rotatorCurrentWeight w q| := by
            rw [rotatorCurrentFourierTerm_norm]
      rw [show (fun θ : V → ℝ =>
          ‖rotatorCurrentFourierTerm G w q χ θ‖ₑ) =
            fun _ => ENNReal.ofReal |rotatorCurrentWeight w q| from funext hpoint]
      simp [lintegral_const]
    calc
      (∑' q : E → ℤ,
          ∫⁻ θ, ‖rotatorCurrentFourierTerm G w q χ θ‖ₑ ∂μ) =
          ∑' q : E → ℤ,
            ENNReal.ofReal |rotatorCurrentWeight w q| * μ Set.univ := by
        apply tsum_congr
        exact hconst
      _ = (∑' q : E → ℤ,
            ENNReal.ofReal |rotatorCurrentWeight w q|) * μ Set.univ := by
        rw [ENNReal.tsum_mul_right]
      _ ≠ ⊤ := ENNReal.mul_ne_top hsum hμ

/-- Integrating an absolutely summable current series imposes the vertex frequency constraint and
produces the exact raw factor `(2π)^{|V|}`. `χ = 0` is the partition series; a nonzero `χ` is a
marked spin character. -/
theorem rotatorCurrentSeries_integral (G : Multigraph V E) (w : ℤ → ℝ)
    (χ : V → ℤ) (hweight : Summable (fun q : E → ℤ => |rotatorCurrentWeight w q|)) :
    (∫ θ, ∑' q : E → ℤ, rotatorCurrentFourierTerm G w q χ θ
      ∂rotatorRawAngleMeasure V) =
        (∑' q : E → ℤ,
          if (fun v => -currentDivergence G q v + χ v) = 0 then
            (rotatorCurrentWeight w q : ℂ) else 0) *
          (2 * Real.pi : ℂ) ^ Fintype.card V := by
  rw [rotatorCurrentFourierTerm_tsum_integral G w χ hweight]
  calc
    (∑' q : E → ℤ,
        ∫ θ, rotatorCurrentFourierTerm G w q χ θ ∂rotatorRawAngleMeasure V) =
        ∑' q : E → ℤ,
          (if (fun v => -currentDivergence G q v + χ v) = 0 then
            (rotatorCurrentWeight w q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card V
          else 0) := by
      apply tsum_congr
      intro q
      rw [rotatorCurrentFourierTerm_integral]
    _ = (∑' q : E → ℤ,
          if (fun v => -currentDivergence G q v + χ v) = 0 then
            (rotatorCurrentWeight w q : ℂ) else 0) *
          (2 * Real.pi : ℂ) ^ Fintype.card V := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro q
      by_cases hq : (fun v => -currentDivergence G q v + χ v) = 0 <;>
        simp [hq]

/-- The integer frequency inserted by `exp(i ξ (θ_a - θ_x))`. -/
def rotatorTwoPointFrequency (a x : V) (ξ : ℤ) : V → ℤ := fun v =>
  (if v = a then ξ else 0) + if v = x then -ξ else 0

/-- The integrated marked-current identity in the source orientation. The frequency condition is
`div q = χ`; after shifting the current along an oriented path from `a` to `x`, the marked edge
coefficient has the `+ξ` shift in FS81 (1.36). -/
theorem rotatorMarkedCurrentSeries_integral (G : Multigraph V E) (w : ℤ → ℝ)
    (a x : V) (ξ : ℤ)
    (hweight : Summable (fun q : E → ℤ => |rotatorCurrentWeight w q|)) :
    (∫ θ, ∑' q : E → ℤ,
      rotatorCurrentFourierTerm G w q (rotatorTwoPointFrequency a x ξ) θ
        ∂rotatorRawAngleMeasure V) =
      (∑' q : E → ℤ,
        if (fun v => -currentDivergence G q v +
            rotatorTwoPointFrequency a x ξ v) = 0 then
          (rotatorCurrentWeight w q : ℂ) else 0) *
        (2 * Real.pi : ℂ) ^ Fintype.card V := by
  exact rotatorCurrentSeries_integral G w (rotatorTwoPointFrequency a x ξ) hweight

/-- The unmarked specialization has the exact raw partition factor `(2π)^{|V|}`. -/
theorem rotatorPartitionCurrentSeries_integral (G : Multigraph V E) (w : ℤ → ℝ)
    (hweight : Summable (fun q : E → ℤ => |rotatorCurrentWeight w q|)) :
    (∫ θ, ∑' q : E → ℤ,
      rotatorCurrentFourierTerm G w q (fun _ => 0) θ ∂rotatorRawAngleMeasure V) =
      (∑' q : E → ℤ,
        if (∀ v, currentDivergence G q v = 0) then
          (rotatorCurrentWeight w q : ℂ) else 0) *
        (2 * Real.pi : ℂ) ^ Fintype.card V := by
  have hfreq (q : E → ℤ) :
      (fun v => -currentDivergence G q v) = 0 ↔
        ∀ v, currentDivergence G q v = 0 := by
    constructor
    · intro h v
      have hv := congrFun h v
      exact neg_eq_zero.mp hv
    · intro h
      funext v
      exact neg_eq_zero.mpr (h v)
  simpa [hfreq] using rotatorCurrentSeries_integral G w (fun _ => 0) hweight

/-- Neutral integer currents on a finite oriented graph. -/
def RotatorNeutralCurrents (G : Multigraph V E) :=
  {q : E → ℤ // ∀ v, currentDivergence G q v = 0}

/-- Currents whose divergence equals a prescribed integer frequency. -/
def RotatorSourceCurrents (G : Multigraph V E) (χ : V → ℤ) :=
  {q : E → ℤ // ∀ v, currentDivergence G q v = χ v}

omit [Fintype V] in
theorem rotatorCurrentDivergence_add (G : Multigraph V E) (q r : E → ℤ) (v : V) :
    currentDivergence G (q + r) v =
      currentDivergence G q v + currentDivergence G r v := by
  classical
  unfold currentDivergence
  have hsum (f g : E → ℤ) :
      (∑ e, if G.src e = v then f e + g e else 0) =
        (∑ e, if G.src e = v then f e else 0) +
          ∑ e, if G.src e = v then g e else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  have hsum' (f g : E → ℤ) :
      (∑ e, if G.tgt e = v then f e + g e else 0) =
        (∑ e, if G.tgt e = v then f e else 0) +
          ∑ e, if G.tgt e = v then g e else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  change (∑ e, if G.src e = v then q e + r e else 0) -
      (∑ e, if G.tgt e = v then q e + r e else 0) = _
  rw [hsum q r, hsum' q r]
  ring

omit [Fintype V] in
theorem rotatorCurrentDivergence_sub (G : Multigraph V E) (q r : E → ℤ) (v : V) :
    currentDivergence G (q - r) v =
      currentDivergence G q v - currentDivergence G r v := by
  classical
  unfold currentDivergence
  have hsum (f g : E → ℤ) :
      (∑ e, if G.src e = v then f e - g e else 0) =
        (∑ e, if G.src e = v then f e else 0) -
          ∑ e, if G.src e = v then g e else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  have hsum' (f g : E → ℤ) :
      (∑ e, if G.tgt e = v then f e - g e else 0) =
        (∑ e, if G.tgt e = v then f e else 0) -
          ∑ e, if G.tgt e = v then g e else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  change (∑ e, if G.src e = v then q e - r e else 0) -
      (∑ e, if G.tgt e = v then q e - r e else 0) = _
  rw [hsum q r, hsum' q r]
  ring

/-- A fixed current with divergence `χ` translates neutral currents bijectively to currents with
divergence `χ`. -/
def rotatorCurrentShiftEquiv (G : Multigraph V E) (χ : V → ℤ) (j : E → ℤ)
    (hj : ∀ v, currentDivergence G j v = χ v) :
    RotatorNeutralCurrents G ≃ RotatorSourceCurrents G χ where
  toFun q := ⟨q.1 + j, by
    intro v
    rw [rotatorCurrentDivergence_add, q.2 v, hj v]
    simp⟩
  invFun q := ⟨q.1 - j, by
    intro v
    rw [rotatorCurrentDivergence_sub, q.2 v, hj v]
    simp⟩
  left_inv q := by
    apply Subtype.ext
    funext e
    simp
  right_inv q := by
    apply Subtype.ext
    funext e
    simp

/-- The neutral-current weight after adding a fixed source current. -/
def rotatorCurrentShiftedWeight (w : ℤ → ℝ) (j : E → ℤ)
    (q : E → ℤ) : ℝ :=
  ∏ e, w (q e + j e)

/-- The current factor selected by a prescribed vertex frequency. -/
def rotatorSourceCurrentFactor (G : Multigraph V E) (χ : V → ℤ) (w : ℤ → ℝ) : ℝ :=
  ∑' q : E → ℤ,
    if (∀ v, currentDivergence G q v = χ v) then rotatorCurrentWeight w q else 0

omit [Fintype V] in
/-- Reindexing a source current by a fixed path current produces the `+ξ` edge shifts in the
marked dual weight. -/
theorem rotatorSourceCurrentWeight_tsum_eq_neutralShifted (G : Multigraph V E)
    (χ : V → ℤ) (w : ℤ → ℝ) (j : E → ℤ)
    (hj : ∀ v, currentDivergence G j v = χ v) :
    (∑' q : RotatorSourceCurrents G χ, rotatorCurrentWeight w q.1) =
      ∑' q : RotatorNeutralCurrents G, rotatorCurrentShiftedWeight w j q.1 := by
  classical
  let e := rotatorCurrentShiftEquiv G χ j hj
  calc
    (∑' q : RotatorSourceCurrents G χ, rotatorCurrentWeight w q.1) =
        ∑' q : RotatorNeutralCurrents G, rotatorCurrentWeight w (e q).1 :=
      (Equiv.tsum_eq e
        (fun q : RotatorSourceCurrents G χ => rotatorCurrentWeight w q.1)).symm
    _ = ∑' q : RotatorNeutralCurrents G, rotatorCurrentShiftedWeight w j q.1 := by
      apply tsum_congr
      intro q
      change (∏ e, w (q.1 e + j e)) = ∏ e, w (q.1 e + j e)
      rfl

/-- Translating all edge currents by a fixed source current rewrites the full marked factor as a
neutral-current sum with the corresponding `+j` shifts on edge weights. -/
theorem rotatorSourceCurrentFactor_eq_neutralShifted (G : Multigraph V E)
    (χ : V → ℤ) (w : ℤ → ℝ) (j : E → ℤ)
    (hj : ∀ v, currentDivergence G j v = χ v) :
    rotatorSourceCurrentFactor G χ w =
      ∑' q : E → ℤ,
        if (∀ v, currentDivergence G q v = 0) then
          rotatorCurrentShiftedWeight w j q else 0 := by
  classical
  let e : (E → ℤ) ≃ (E → ℤ) := {
    toFun := fun q => q + j
    invFun := fun q => q - j
    left_inv := by intro q; funext x; simp
    right_inv := by intro q; funext x; simp }
  calc
    rotatorSourceCurrentFactor G χ w =
        ∑' q : E → ℤ,
          if (∀ v, currentDivergence G (e q) v = χ v) then
            rotatorCurrentWeight w (e q) else 0 := by
      unfold rotatorSourceCurrentFactor
      exact (Equiv.tsum_eq e
        (fun q : E → ℤ =>
          if (∀ v, currentDivergence G q v = χ v) then
            rotatorCurrentWeight w q else 0)).symm
    _ = ∑' q : E → ℤ,
        if (∀ v, currentDivergence G q v = 0) then
          rotatorCurrentShiftedWeight w j q else 0 := by
      apply tsum_congr
      intro q
      have hsource : (∀ v, currentDivergence G (e q) v = χ v) ↔
          ∀ v, currentDivergence G q v = 0 := by
        constructor
        · intro h v
          have hv := h v
          rw [show e q = q + j from rfl, rotatorCurrentDivergence_add, hj v] at hv
          omega
        · intro h v
          rw [show e q = q + j from rfl, rotatorCurrentDivergence_add, h v, hj v]
          omega
      rw [if_congr hsource]
      · change (∏ e, w (q e + j e)) = _
        rfl
      · rfl

/-- A marked current factor is positive when its coefficients are strictly positive, its source
constraint has one solution, and the unrestricted edge-current weights are summable. -/
theorem rotatorSourceCurrentFactor_pos (G : Multigraph V E) (χ : V → ℤ)
    (w : ℤ → ℝ) (j : E → ℤ) (hj : ∀ v, currentDivergence G j v = χ v)
    (hw_pos : ∀ m, 0 < w m)
    (hweight : Summable (fun q : E → ℤ => |rotatorCurrentWeight w q|)) :
    0 < rotatorSourceCurrentFactor G χ w := by
  classical
  have hsummable : Summable fun q : E → ℤ =>
      if (∀ v, currentDivergence G q v = χ v) then rotatorCurrentWeight w q else 0 := by
    apply Summable.of_norm_bounded hweight
    intro q
    by_cases hq : ∀ v, currentDivergence G q v = χ v
    · simp [hq, Real.norm_eq_abs]
    · simp [hq]
  have hjpos : 0 < rotatorCurrentWeight w j := by
    unfold rotatorCurrentWeight
    exact Finset.prod_pos fun edge hedge => hw_pos (j edge)
  refine Summable.tsum_pos hsummable ?_ j ?_
  · intro q
    by_cases hq : ∀ v, currentDivergence G q v = χ v
    · simp [hq]
      unfold rotatorCurrentWeight
      exact Finset.prod_nonneg fun edge hedge => (hw_pos (q edge)).le
    · simp [hq]
  · simpa [rotatorSourceCurrentFactor, hj] using hjpos

/-- The neutral-current partition factor is positive when all edge coefficients are nonnegative
and the zero-frequency coefficient is positive. -/
theorem rotatorNeutralCurrentFactor_pos (G : Multigraph V E) (w : ℤ → ℝ)
    (hw_nonneg : ∀ m, 0 ≤ w m) (hw_zero : 0 < w 0)
    (hweight : Summable (fun q : E → ℤ => |rotatorCurrentWeight w q|)) :
    0 < ∑' q : E → ℤ,
      if (∀ v, currentDivergence G q v = 0) then rotatorCurrentWeight w q else 0 := by
  classical
  have hneutralSummable : Summable fun q : E → ℤ =>
      if (∀ v, currentDivergence G q v = 0) then rotatorCurrentWeight w q else 0 := by
    apply Summable.of_norm_bounded hweight
    intro q
    by_cases hn : ∀ v, currentDivergence G q v = 0
    · simp [hn, Real.norm_eq_abs]
    · simp [hn]
  let q0 : E → ℤ := fun _ => 0
  have hneutral0 : ∀ v, currentDivergence G q0 v = 0 := by
    intro v
    simp [q0, currentDivergence]
  have hprod0 : 0 < rotatorCurrentWeight w q0 := by
    unfold rotatorCurrentWeight q0
    exact Finset.prod_pos fun e he => hw_zero
  refine Summable.tsum_pos hneutralSummable ?_ q0 ?_
  · intro q
    by_cases hn : ∀ v, currentDivergence G q v = 0
    · simp [hn]
      unfold rotatorCurrentWeight
      exact Finset.prod_nonneg fun e he => hw_nonneg (q e)
    · simp [hn]
  · simpa [hneutral0] using hprod0

end FroehlichSpencer.BKT.Rotator

end
