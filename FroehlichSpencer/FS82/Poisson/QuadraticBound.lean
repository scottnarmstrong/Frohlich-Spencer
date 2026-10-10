module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Matrix

theorem exists_matrix_quadratic_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → ℝ,
      c * ∑ i, x i ^ 2 ≤ star x ⬝ᵥ A.mulVec x := by
  classical
  let E := EuclideanSpace ℝ ι
  let q : E → ℝ := fun x => star x.ofLp ⬝ᵥ A.mulVec x.ofLp
  have hcont : Continuous q := by
    fun_prop
  let x₀ : E := EuclideanSpace.single (Classical.choice ‹Nonempty ι›) 1
  have hx₀ : x₀ ∈ Metric.sphere (0 : E) 1 := by
    change dist x₀ 0 = 1
    rw [dist_zero_right]
    rw [PiLp.norm_single]
    norm_num
  obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    ⟨x₀, hx₀⟩ hcont.continuousOn
  have hyNorm : ‖y‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hy
  have hyNe : y.ofLp ≠ 0 := by
    intro h
    have : ‖y‖ = 0 := by
      rw [EuclideanSpace.norm_eq]
      simp [h]
    rw [hyNorm] at this
    norm_num at this
  let c : ℝ := q y
  have hc : 0 < c := by
    change 0 < star y.ofLp ⬝ᵥ A.mulVec y.ofLp
    exact hA.dotProduct_mulVec_pos hyNe
  have hqscale (r : ℝ) (x : E) : q (r • x) = r ^ 2 * q x := by
    change star (r • x.ofLp) ⬝ᵥ A.mulVec (r • x.ofLp) =
      r ^ 2 * (star x.ofLp ⬝ᵥ A.mulVec x.ofLp)
    simp [mulVec_smul, dotProduct_smul, mul_comm]
    ring
  have hunit (x : E) (hx : ‖x‖ = 1) : c ≤ q x := by
    apply hmin
    simp [Metric.mem_sphere, hx]
  refine ⟨c, hc, ?_⟩
  intro x
  let v : E := WithLp.toLp 2 x
  by_cases hv : v = 0
  · have hx : x = 0 := by
      have hh := congrArg WithLp.ofLp hv
      simpa [v] using hh
    subst x
    simp
  · have hvNorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let r : ℝ := ‖v‖⁻¹
    have hrnorm : ‖r • v‖ = 1 := by
      rw [norm_smul]
      rw [show ‖r‖ = r by simp [r, abs_of_nonneg (norm_nonneg v)]]
      simp [r, hvNorm.ne']
    have hqv : c ≤ q (r • v) := hunit (r • v) hrnorm
    rw [hqscale] at hqv
    have hsquare : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hqv hsquare
    have hfinal : c * ‖v‖ ^ 2 ≤ q v := by
      calc
        c * ‖v‖ ^ 2 ≤ (r ^ 2 * q v) * ‖v‖ ^ 2 := hmul
        _ = q v := by
          dsimp [r]
          field_simp [ne_of_gt hvNorm]
    have hnormsq : ‖v‖ ^ 2 = ∑ i, x i ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
      · simp [v, Real.norm_eq_abs, sq_abs]
      · exact Finset.sum_nonneg fun i _ => by positivity
    simpa [q, v, hnormsq] using hfinal

end FroehlichSpencer.FS82.Poisson
