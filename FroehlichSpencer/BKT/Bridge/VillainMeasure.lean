/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Fourier.PeriodizedGaussian
public import FroehlichSpencer.BKT.Surface.VillainLaw
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Finite-volume Villain normalization -/

@[expose] public section

namespace FroehlichSpencer.BKT

open MeasureTheory
open Real
open scoped ENNReal

abbrev VillainVertex (L : ℕ) := Option (Fin L × Fin L)

abbrev VillainEdge (L : ℕ) := SquareFreeEdge L ⊕ Σ j : Fin L × Fin L,
  Fin (4 - (Finset.univ.filter fun e : SquareFreeEdge L =>
    (squareFree L).src e = j ∨ (squareFree L).tgt e = j).card)

/-- The KP p. 4 product base measure for the wired square, with the wired angle fixed to zero. -/
noncomputable def villainBaseMeasure (L : ℕ) : Measure (VillainVertex L → ℝ) :=
  Measure.pi fun j =>
    if j = none then Measure.dirac 0
    else volume.restrict (Set.Ico (-Real.pi) Real.pi)

/-- The rooted angle integration box on which the wired Villain base measure is supported. -/
def villainAngleBox (L : ℕ) : Set (VillainVertex L → ℝ) :=
  Set.pi Set.univ fun j =>
    if j = none then {0} else Set.Ico (-Real.pi) Real.pi

/-- The KP p. 4 unnormalized density, with its periodized edge weights written as ENNReal sums. -/
noncomputable def villainDensity (L : ℕ) (β : ℝ) : (VillainVertex L → ℝ) → ENNReal :=
  fun θ => ∏ e : VillainEdge L,
    ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) *
      (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) + 2 * Real.pi * m) ^ 2))

/--
The unnormalized measure in the Villain law.
-/
noncomputable def villainDensityMeasure (L : ℕ) (β : ℝ) : Measure (VillainVertex L → ℝ) :=
  (villainBaseMeasure L).withDensity (villainDensity L β)

/-- The bridge base measure is exactly the root-Dirac and restricted-Lebesgue product in KP's
definition (1.4), p. 4. -/
theorem villainBaseMeasure_eq_kp (L : ℕ) :
    villainBaseMeasure L = Measure.pi (fun j : VillainVertex L =>
      if j = none then Measure.dirac 0
      else volume.restrict (Set.Ico (-Real.pi) Real.pi)) := rfl

/-- The bridge density is exactly the edgewise periodized Gaussian in KP's definition (1.4),
p. 4. -/
theorem villainDensity_eq_kp (L : ℕ) (β : ℝ) (θ : VillainVertex L → ℝ) :
    villainDensity L β θ = ∏ e : VillainEdge L, ∑' m : ℤ,
      ENNReal.ofReal (Real.exp (-(β / 2) *
        (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) + 2 * Real.pi * m) ^ 2)) := rfl

/-- The bridge's unnormalized Villain measure is precisely KP's wired finite-volume measure
before division by its partition function, KP (1.4), p. 4. -/
theorem villainDensityMeasure_eq_kp (L : ℕ) (β : ℝ) :
    villainDensityMeasure L β =
      (Measure.pi (fun j : VillainVertex L =>
        if j = none then Measure.dirac 0
        else volume.restrict (Set.Ico (-Real.pi) Real.pi))).withDensity
        (fun θ => ∏ e : VillainEdge L, ∑' m : ℤ,
          ENNReal.ofReal (Real.exp (-(β / 2) *
            (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) +
              2 * Real.pi * m) ^ 2))) := rfl

/-- KP's normalized wired Villain law is the scalar normalization of the characterized
unnormalized measure, KP (1.4), p. 4. -/
theorem villainLaw_eq_normalizedDensityMeasure (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    villainLaw L β hβ =
      (villainDensityMeasure L β Set.univ)⁻¹ • villainDensityMeasure L β := by
  rw [villainDensityMeasure_eq_kp]
  rfl

private instance villainBaseCoordinate_isFiniteMeasure (L : ℕ)
    (j : VillainVertex L) :
    IsFiniteMeasure (if j = none then Measure.dirac (0 : ℝ)
      else volume.restrict (Set.Ico (-Real.pi) Real.pi)) := by
  classical
  split_ifs with h
  · subst j
    infer_instance
  · refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top

/-- The wired square's restricted product angle measure has finite total mass. -/
theorem villainBaseMeasure_univ_lt_top (L : ℕ) : villainBaseMeasure L Set.univ < ∞ := by
  classical
  rw [villainBaseMeasure, Measure.pi_univ]
  apply ENNReal.prod_lt_top
  intro j hj
  by_cases hj0 : j = none
  · subst j
    simp
  · have hcoord : (volume.restrict (Set.Ico (-Real.pi) Real.pi)) Set.univ < ∞ := by
      rw [Measure.restrict_apply_univ, Real.volume_Ico]
      exact ENNReal.ofReal_lt_top
    convert hcoord using 1; simp [hj0]

/-- The edge periodization is the ENNReal lift of KP's real Villain weight (KP (1.4), p. 4). -/
theorem villainFactor_eq_ofReal_weight (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    (∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))) =
      ENNReal.ofReal (villainWeight β x) := by
  simpa [villainWeight] using
    (ENNReal.ofReal_tsum_of_nonneg (fun m => (Real.exp_pos _).le)
      (VillainWeight.villainWeight_summable hβ x)).symm

/-- A uniform Fourier-series bound for KP's one-edge Villain weight. -/
theorem villainWeight_fourier_bound (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    villainWeight β x ≤ (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
      ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β)) := by
  let a : ℤ → ℝ := fun q => Real.exp (-((q : ℝ) ^ 2) / (2 * β))
  let f : ℤ → ℝ := fun q => a q * Real.cos ((q : ℝ) * x)
  have ha : Summable a := by
    simpa [a] using VillainWeight.villainWeight_fourier_coeff_summable hβ
  have hf : Summable f := by
    apply Summable.of_norm_bounded ha
    intro q
    dsimp [f, a]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * |Real.cos ((q : ℝ) * x)| ≤
          Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-((q : ℝ) ^ 2) / (2 * β)) := by ring
  have hterm (q : ℤ) : f q ≤ a q := by
    dsimp [f, a]
    calc
      Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * Real.cos ((q : ℝ) * x) ≤
          Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-((q : ℝ) ^ 2) / (2 * β)) := by ring
  have hseries : ∑' q : ℤ, f q ≤ ∑' q : ℤ, a q :=
    Summable.tsum_le_tsum hterm hf ha
  rw [VillainWeight.villainWeight_fourier_real hβ x]
  exact mul_le_mul_of_nonneg_left hseries
    (Real.rpow_pos_of_pos (by positivity) _).le

/-- The rooted Villain density equals the finite product of real periodized Gaussian weights. -/
theorem villainDensity_eq_weight_prod (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (θ : VillainVertex L → ℝ) :
    villainDensity L β θ = ∏ e : VillainEdge L,
      ENNReal.ofReal (villainWeight β
        (θ ((squareZero L).src e) - θ ((squareZero L).tgt e))) := by
  classical
  rw [villainDensity_eq_kp]
  apply Finset.prod_congr rfl
  intro e he
  exact villainFactor_eq_ofReal_weight β hβ _

noncomputable def villainFourierBound (β : ℝ) : ℝ :=
  (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
    ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))

/-- Every finite-volume edge factor is bounded by the same finite Fourier coefficient sum. -/
theorem villainDensity_le_const (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (θ : VillainVertex L → ℝ) :
    villainDensity L β θ ≤
      ∏ _e : VillainEdge L, ENNReal.ofReal (villainFourierBound β) := by
  classical
  rw [villainDensity_eq_weight_prod L β hβ θ]
  have hB : 0 ≤ villainFourierBound β := by
    change 0 ≤ (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
      ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
      (tsum_nonneg fun _ => (Real.exp_pos _).le)
  apply Finset.prod_le_prod₀
  · intro _e he
    exact zero_le
  · intro _e he
    rw [ENNReal.ofReal_le_ofReal_iff hB]
    exact villainWeight_fourier_bound β hβ _

/--
Inside the rooted angle box, the Villain density has a uniform strictly positive lower
bound obtained from the zero winding number on each edge.
-/
theorem villainDensity_lower_on_box (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (θ : VillainVertex L → ℝ) (hθ : θ ∈ villainAngleBox L) :
    ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2)) ^
        Fintype.card (VillainEdge L) ≤ villainDensity L β θ := by
  classical
  let d : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2))
  have hangle (j : VillainVertex L) : |θ j| ≤ Real.pi := by
    have hj := (Set.mem_pi.mp hθ) j (Set.mem_univ j)
    by_cases hj0 : j = none
    · subst j
      have hzero : θ none = 0 := by simpa [villainAngleBox] using hj
      simpa [hzero] using Real.pi_pos.le
    · have hi : θ j ∈ Set.Ico (-Real.pi) Real.pi := by
        simpa [villainAngleBox, hj0] using hj
      exact abs_le.mpr ⟨hi.1, hi.2.le⟩
  have hterm (e : VillainEdge L) :
      d ≤ ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) *
        (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) +
          2 * Real.pi * m) ^ 2)) := by
    have habs : |θ ((squareZero L).src e) - θ ((squareZero L).tgt e)| ≤ 2 * Real.pi := by
      calc
        |θ ((squareZero L).src e) - θ ((squareZero L).tgt e)| ≤
            |θ ((squareZero L).src e)| + |θ ((squareZero L).tgt e)| := abs_sub _ _
        _ ≤ Real.pi + Real.pi := add_le_add (hangle _) (hangle _)
        _ = 2 * Real.pi := by ring
    have hsq :
        (θ ((squareZero L).src e) - θ ((squareZero L).tgt e)) ^ 2 ≤
          (2 * Real.pi) ^ 2 := by
      have hnonneg : 0 ≤ 2 * Real.pi := by positivity
      nlinarith [sq_abs
        (θ ((squareZero L).src e) - θ ((squareZero L).tgt e)),
        abs_nonneg (θ ((squareZero L).src e) - θ ((squareZero L).tgt e)), hnonneg]
    have hexp : Real.exp (-(β / 2) * (2 * Real.pi) ^ 2) ≤
        Real.exp (-(β / 2) *
          (θ ((squareZero L).src e) - θ ((squareZero L).tgt e)) ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hsq (by linarith)
    have hzero := ENNReal.le_tsum
      (f := fun m : ℤ => ENNReal.ofReal (Real.exp (-(β / 2) *
        (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) + 2 * Real.pi * m) ^ 2)))
      (0 : ℤ)
    dsimp [d]
    calc
      ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2)) ≤
          ENNReal.ofReal (Real.exp (-(β / 2) *
            (θ ((squareZero L).src e) - θ ((squareZero L).tgt e)) ^ 2)) :=
        ENNReal.ofReal_le_ofReal hexp
      _ = ENNReal.ofReal (Real.exp (-(β / 2) *
            (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) +
              2 * Real.pi * (0 : ℤ)) ^ 2)) := by norm_num
      _ ≤ ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) *
          (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) +
            2 * Real.pi * m) ^ 2)) := hzero
  have hprod :
      ∏ _e : VillainEdge L, d ≤ ∏ e : VillainEdge L,
        ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) *
          (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) +
            2 * Real.pi * m) ^ 2)) := by
    apply Finset.prod_le_prod₀
    · intro _e he
      exact zero_le
    · intro e he
      exact hterm e
  rw [villainDensity_eq_kp]
  calc
    ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2)) ^
        Fintype.card (VillainEdge L) = ∏ _e : VillainEdge L, d := by
          simp only [neg_mul, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
            Finset.prod_const, Finset.card_univ, d]
    _ ≤ ∏ e : VillainEdge L, ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) *
          (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) +
            2 * Real.pi * m) ^ 2)) := hprod

/--
The Villain density measure has positive finite partition mass, KP (1.4), p. 4.
-/
theorem villainDensityMeasure_univ_pos_lt_top (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    0 < villainDensityMeasure L β Set.univ ∧ villainDensityMeasure L β Set.univ < ∞ := by
  classical
  constructor
  · rw [villainDensityMeasure, withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    let S := villainAngleBox L
    let d : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2)) ^
      Fintype.card (VillainEdge L)
    have hSpos : 0 < (villainBaseMeasure L) S := by
      change 0 < (Measure.pi (fun j : VillainVertex L =>
        if j = none then Measure.dirac 0
        else volume.restrict (Set.Ico (-Real.pi) Real.pi)))
          (Set.pi Set.univ fun j : VillainVertex L =>
            if j = none then {0} else Set.Ico (-Real.pi) Real.pi)
      rw [Measure.pi_pi]
      apply pos_iff_ne_zero.mpr
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      by_cases hj0 : j = none
      · subst j
        simp only [↓reduceIte, MeasurableSet.singleton, Measure.dirac_apply', Set.mem_singleton_iff,
          Set.indicator_of_mem, Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true]
      · have hcoord : (volume.restrict (Set.Ico (-Real.pi) Real.pi))
            (Set.Ico (-Real.pi) Real.pi) ≠ 0 := by
          rw [Measure.restrict_apply (measurableSet_Ico), Set.inter_self, Real.volume_Ico]
          have hlen : 0 < Real.pi - -Real.pi := by linarith [Real.pi_pos]
          exact (ENNReal.ofReal_pos.mpr hlen).ne'
        convert hcoord using 1; simp only [hj0, ↓reduceIte, measurableSet_Ico, Measure.restrict_apply,
          Set.inter_self, Real.volume_Ico, sub_neg_eq_add]
    have hdpos : 0 < d := by
      apply pos_iff_ne_zero.mpr
      dsimp [d]
      exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hSmeas : MeasurableSet S := by
      apply (measurableSet_pi Set.countable_univ).mpr
      left
      intro j hj
      split_ifs
      · exact MeasurableSet.singleton 0
      · exact measurableSet_Ico
    have hlintegral : d * (villainBaseMeasure L) S ≤
        ∫⁻ θ, villainDensity L β θ ∂(villainBaseMeasure L) := by
      calc
        d * (villainBaseMeasure L) S =
            ∫⁻ θ, S.indicator (fun _ => d) θ ∂(villainBaseMeasure L) := by
              rw [lintegral_indicator_const hSmeas]
        _ ≤ ∫⁻ θ, villainDensity L β θ ∂(villainBaseMeasure L) :=
          lintegral_mono fun θ => by
            by_cases hθ : θ ∈ S
            · simpa only [Set.indicator, hθ, ↓reduceIte, neg_mul, Fintype.card_sum,
                Fintype.card_sigma, Fintype.card_fin, d] using
                villainDensity_lower_on_box L β hβ θ (by simpa [S] using hθ)
            · simp only [Set.indicator, hθ, ↓reduceIte, zero_le]
    have hprodpos : 0 < d * (villainBaseMeasure L) S :=
      pos_iff_ne_zero.mpr (mul_ne_zero hdpos.ne' hSpos.ne')
    exact lt_of_lt_of_le hprodpos hlintegral
  · rw [villainDensityMeasure, withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    let M : ℝ≥0∞ := ∏ e : VillainEdge L, ENNReal.ofReal (villainFourierBound β)
    have hB : 0 ≤ villainFourierBound β := by
      change 0 ≤ (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
        ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))
      exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
        (tsum_nonneg fun _ => (Real.exp_pos _).le)
    have hMtop : M < ∞ := by
      change (∏ e : VillainEdge L, ENNReal.ofReal (villainFourierBound β)) < ∞
      exact ENNReal.prod_lt_top fun e he => ENNReal.ofReal_lt_top
    have hbaseTop : (villainBaseMeasure L) Set.univ < ∞ :=
      villainBaseMeasure_univ_lt_top L
    have hbound (θ : VillainVertex L → ℝ) : villainDensity L β θ ≤ M := by
      change villainDensity L β θ ≤
        ∏ e : VillainEdge L, ENNReal.ofReal (villainFourierBound β)
      exact villainDensity_le_const L β hβ θ
    calc
      ∫⁻ θ, villainDensity L β θ ∂(villainBaseMeasure L) ≤
          ∫⁻ _ : VillainVertex L → ℝ, M ∂(villainBaseMeasure L) :=
        lintegral_mono hbound
      _ = M * (villainBaseMeasure L) Set.univ := lintegral_const M
      _ < ∞ := ENNReal.mul_lt_top hMtop hbaseTop

end FroehlichSpencer.BKT

end
