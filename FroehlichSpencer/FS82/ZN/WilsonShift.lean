/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.TorusIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# the complex translation of link variables for the Wilson weight

This is the complex translation `θ_xy → θ_xy + iα` of FS82 (3.32), for the Wilson weight
`∏_p e^{β cos(2π(flux_p θ + ε_p))}` of an abstract finite gauge complex: links `E`, plaquettes `P`,
integer incidence `c : P → E → ℤ`.

* `shiftedWeight β c ε η θ = ∏_p exp(β cos(2π(flux_p θ + ε_p) + i η_p))`, the weight with the
  plaquette arguments shifted by `i η_p`.
* `integral_chi_shiftedWeight`: for a character `χ_m`, a real vector `a` on the links and any `η`,
  `∫ χ_m W^η = e^{−(m,a)} ∫ χ_m W^{η + c a}`.

No geometric hypothesis is needed.
* `shiftFactor β η z`, the factor `i_β(η; ·)` of (3.33) as a function on the circle, with
  `‖i_β‖ ≤ 1` (3.34), and `exp_cosShift`, the factorization
  `exp(β cos(x + iη)) = e^{β cos x} e^{β(cosh η − 1)} i_β(η; x)`.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN.Torus

noncomputable section

local instance wilsonShift_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance wilsonShift_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {E P : Type*} [Fintype E] [Fintype P]

/-! ### Flux, weights and characters -/

/-- The flux of a configuration through a plaquette with incidence row `c p`. -/
def flux (c : P → E → ℤ) (p : P) (θ : E → UnitAddCircle) : UnitAddCircle :=
  pair (c p) θ

omit [Fintype P] in
theorem continuous_flux (c : P → E → ℤ) (p : P) : Continuous (flux c p) :=
  continuous_pair (c p)

/-- The Wilson weight `∏_p e^{β cos(2π(flux_p θ + ε_p))}`. -/
def wilsonWeight (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (θ : E → UnitAddCircle) : ℝ :=
  ∏ p, Real.exp (β * cosC (flux c p θ + (ε p : UnitAddCircle)))

theorem wilsonWeight_pos (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (θ : E → UnitAddCircle) :
    0 < wilsonWeight β c ε θ :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

theorem continuous_wilsonWeight (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) :
    Continuous (wilsonWeight β c ε) := by
  unfold wilsonWeight
  refine continuous_finsetProd _ fun p _ => ?_
  exact Real.continuous_exp.comp (continuous_const.mul
    (continuous_cosC.comp ((continuous_flux c p).add continuous_const)))

/-- `cos(2πx + iη)` for `x` on the circle: `cos 2πx cosh η − i sin 2πx sinh η`. -/
def cosShift (z : UnitAddCircle) (η : ℝ) : ℂ :=
  ((cosC z * Real.cosh η : ℝ) : ℂ) - Complex.I * ((sinC z * Real.sinh η : ℝ) : ℂ)

theorem cosShift_coe (x η : ℝ) :
    cosShift (x : UnitAddCircle) η =
      Complex.cos (((2 * Real.pi * x : ℝ) : ℂ) + (η : ℂ) * Complex.I) := by
  rw [Complex.cos_add_mul_I]
  unfold cosShift
  rw [cosC_coe, sinC_coe]
  push_cast
  ring

theorem cosShift_zero (z : UnitAddCircle) : cosShift z 0 = ((cosC z : ℝ) : ℂ) := by
  simp [cosShift]

theorem continuous_cosShift (η : ℝ) : Continuous fun z : UnitAddCircle => cosShift z η := by
  unfold cosShift
  exact (Complex.continuous_ofReal.comp (continuous_cosC.mul continuous_const)).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_sinC.mul continuous_const)))

/-- The Wilson weight with the argument of plaquette `p` shifted by `i η_p`. -/
def shiftedWeight (β : ℝ) (c : P → E → ℤ) (ε η : P → ℝ) (θ : E → UnitAddCircle) : ℂ :=
  ∏ p, Complex.exp ((β : ℂ) * cosShift (flux c p θ + (ε p : UnitAddCircle)) (η p))

theorem continuous_shiftedWeight (β : ℝ) (c : P → E → ℤ) (ε η : P → ℝ) :
    Continuous (shiftedWeight β c ε η) := by
  unfold shiftedWeight
  refine continuous_finsetProd _ fun p _ => ?_
  exact Complex.continuous_exp.comp (continuous_const.mul
    ((continuous_cosShift (η p)).comp ((continuous_flux c p).add continuous_const)))

theorem shiftedWeight_zero (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (θ : E → UnitAddCircle) :
    shiftedWeight β c ε (fun _ => 0) θ = ((wilsonWeight β c ε θ : ℝ) : ℂ) := by
  unfold shiftedWeight wilsonWeight
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [cosShift_zero, Complex.ofReal_exp]
  push_cast
  rfl

/-- The character `e^{2πi (m, θ)}`. -/
def chi (m : E → ℤ) (θ : E → UnitAddCircle) : ℂ :=
  fourier (T := (1 : ℝ)) 1 (pair m θ)

theorem continuous_chi (m : E → ℤ) : Continuous (chi m) :=
  (fourier (T := (1 : ℝ)) 1).continuous.comp (continuous_pair m)

/-! ### The contour shift -/

/-- The entire function of one link variable behind `integral_chi_shiftedWeight_link`. -/
def linkExtension (β : ℝ) (b₀ : ℝ) (n₀ : ℤ) (b : P → ℝ) (n : P → ℤ) (η : P → ℝ) (w : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((b₀ : ℂ) + (n₀ : ℂ) * w)) *
    ∏ p, Complex.exp ((β : ℂ) *
      Complex.cos (2 * Real.pi * ((b p : ℂ) + (n p : ℂ) * w) + (η p : ℂ) * Complex.I))

theorem differentiable_linkExtension (β : ℝ) (b₀ : ℝ) (n₀ : ℤ) (b : P → ℝ) (n : P → ℤ)
    (η : P → ℝ) : Differentiable ℂ (linkExtension β b₀ n₀ b n η) := by
  unfold linkExtension
  fun_prop

theorem linkExtension_periodic (β : ℝ) (b₀ : ℝ) (n₀ : ℤ) (b : P → ℝ) (n : P → ℤ)
    (η : P → ℝ) (w : ℂ) :
    linkExtension β b₀ n₀ b n η (w + 1) = linkExtension β b₀ n₀ b n η w := by
  unfold linkExtension
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((b₀ : ℂ) + (n₀ : ℂ) * (w + 1))) =
      Complex.exp (2 * Real.pi * Complex.I * ((b₀ : ℂ) + (n₀ : ℂ) * w)) := by
    rw [show 2 * Real.pi * Complex.I * ((b₀ : ℂ) + (n₀ : ℂ) * (w + 1)) =
        2 * Real.pi * Complex.I * ((b₀ : ℂ) + (n₀ : ℂ) * w) +
          (n₀ : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [show 2 * Real.pi * ((b p : ℂ) + (n p : ℂ) * (w + 1)) + (η p : ℂ) * Complex.I =
      (2 * Real.pi * ((b p : ℂ) + (n p : ℂ) * w) + (η p : ℂ) * Complex.I) +
        (n p : ℂ) * (2 * Real.pi) by ring, Complex.cos_add_int_mul_two_pi]

variable [DecidableEq E]

omit [Fintype P] in
theorem flux_add_single (c : P → E → ℤ) (p : P) (θ : E → UnitAddCircle) (x : E)
    (u : UnitAddCircle) : flux c p (θ + Pi.single x u) = flux c p θ + c p x • u := by
  unfold flux
  rw [pair_add, pair_single]

/-- **One link.** Shifting the variable of the link `x` by `i a/(2π)` multiplies the character by
`e^{−m_x a}` and adds `c_p(x) a` to the imaginary shift of every plaquette. -/
theorem integral_chi_shiftedWeight_link (β : ℝ) (c : P → E → ℤ) (ε η : P → ℝ)
    (m : E → ℤ) (x : E) (a : ℝ) :
    ∫ θ, chi m θ * shiftedWeight β c ε η θ =
      (Real.exp (-((m x : ℝ) * a)) : ℂ) *
        ∫ θ, chi m θ * shiftedWeight β c ε (fun p => η p + (c p x : ℝ) * a) θ := by
  rw [← integral_const_mul]
  refine integral_shift_link _ _ ((continuous_chi m).mul (continuous_shiftedWeight β c ε η))
    (continuous_const.mul ((continuous_chi m).mul (continuous_shiftedWeight β c ε _)))
    x (a / (2 * Real.pi)) fun θ => ?_
  obtain ⟨b₀, hb₀⟩ := exists_real_lift (pair m θ)
  have hb : ∀ p, ∃ y : ℝ, (y : UnitAddCircle) = flux c p θ + (ε p : UnitAddCircle) :=
    fun p => exists_real_lift _
  choose b hb using hb
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hchi : ∀ u : ℝ, chi m (θ + Pi.single x (u : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ((b₀ : ℂ) + (m x : ℂ) * (u : ℂ))) := by
    intro u
    unfold chi
    rw [pair_add, pair_single, ← hb₀, ← AddCircle.coe_zsmul, ← AddCircle.coe_add, fourier_one_coe]
    congr 1
    push_cast
    ring
  have hflux : ∀ (p : P) (u : ℝ),
      flux c p (θ + Pi.single x (u : UnitAddCircle)) + (ε p : UnitAddCircle) =
        ((b p + (c p x : ℝ) * u : ℝ) : UnitAddCircle) := by
    intro p u
    rw [flux_add_single, add_right_comm, ← hb p, ← AddCircle.coe_zsmul, ← AddCircle.coe_add,
      zsmul_eq_mul]
  have hW : ∀ (η' : P → ℝ) (u : ℝ),
      shiftedWeight β c ε η' (θ + Pi.single x (u : UnitAddCircle)) =
        ∏ p, Complex.exp ((β : ℂ) * Complex.cos
          (2 * Real.pi * ((b p : ℂ) + ((c p x : ℤ) : ℂ) * (u : ℂ)) + (η' p : ℂ) * Complex.I)) := by
    intro η' u
    unfold shiftedWeight
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hflux p u, cosShift_coe]
    congr 3
    push_cast
    ring
  refine ⟨linkExtension β b₀ (m x) b (fun p => c p x) η, differentiable_linkExtension _ _ _ _ _ _,
    linkExtension_periodic _ _ _ _ _ _, fun u => ?_, fun u => ?_⟩
  · rw [hchi u, hW η u]
    rfl
  · rw [hchi u, hW _ u]
    have hexp : Complex.exp (2 * Real.pi * Complex.I *
        ((b₀ : ℂ) + (m x : ℂ) * ((u : ℂ) + ((a / (2 * Real.pi) : ℝ) : ℂ) * Complex.I))) =
        (Real.exp (-((m x : ℝ) * a)) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((b₀ : ℂ) + (m x : ℂ) * (u : ℂ))) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    change _ = Complex.exp (2 * Real.pi * Complex.I *
        ((b₀ : ℂ) + (m x : ℂ) * ((u : ℂ) + ((a / (2 * Real.pi) : ℝ) : ℂ) * Complex.I))) *
      ∏ p, Complex.exp ((β : ℂ) * Complex.cos
        (2 * Real.pi * ((b p : ℂ) + ((c p x : ℤ) : ℂ) *
          ((u : ℂ) + ((a / (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) + (η p : ℂ) * Complex.I))
    rw [hexp]
    refine (mul_assoc _ _ _).symm.trans ?_
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    congr 3
    push_cast
    field_simp
    ring

/-- **Several links.** For a real vector `a` on the links,
`∫ χ_m W^η = e^{−(m,a)} ∫ χ_m W^{η + c a}`. -/
theorem integral_chi_shiftedWeight (β : ℝ) (c : P → E → ℤ) (ε η : P → ℝ)
    (m : E → ℤ) (a : E → ℝ) :
    ∫ θ, chi m θ * shiftedWeight β c ε η θ =
      (Real.exp (-(∑ x, (m x : ℝ) * a x)) : ℂ) *
        ∫ θ, chi m θ * shiftedWeight β c ε (fun p => η p + ∑ x, (c p x : ℝ) * a x) θ := by
  classical
  have key : ∀ s : Finset E,
      ∫ θ, chi m θ * shiftedWeight β c ε η θ =
        (Real.exp (-(∑ x ∈ s, (m x : ℝ) * a x)) : ℂ) *
          ∫ θ, chi m θ * shiftedWeight β c ε (fun p => η p + ∑ x ∈ s, (c p x : ℝ) * a x) θ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
        rw [ih, integral_chi_shiftedWeight_link β c ε _ m x (a x), ← mul_assoc]
        congr 1
        · rw [← Complex.ofReal_mul, ← Real.exp_add, Finset.sum_insert hx]
          congr 2
          ring
        · congr 1
          funext θ
          congr 2
          funext p
          rw [Finset.sum_insert hx]
          ring
  exact key Finset.univ

/-! ### The factor `i_β` -/

/-- The factor `i_β(η; x) = e^{−β(cosh η − 1)} e^{β[cos(x + iη) − cos x]}` of FS82 (3.33), as a
function of a circle variable. -/
def shiftFactor (β η : ℝ) (z : UnitAddCircle) : ℂ :=
  Complex.exp (((β * ((Real.cosh η - 1) * (cosC z - 1)) : ℝ) : ℂ) -
    Complex.I * ((β * (Real.sinh η * sinC z) : ℝ) : ℂ))

theorem continuous_shiftFactor (β η : ℝ) : Continuous (shiftFactor β η) := by
  unfold shiftFactor
  refine Complex.continuous_exp.comp ?_
  exact (Complex.continuous_ofReal.comp (continuous_const.mul
      (continuous_const.mul (continuous_cosC.sub continuous_const)))).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_const.mul continuous_sinC))))

@[simp] theorem shiftFactor_zero (β : ℝ) (z : UnitAddCircle) : shiftFactor β 0 z = 1 := by
  simp [shiftFactor]

/-- FS82 (3.34): `|i_β| ≤ 1`. -/
theorem norm_shiftFactor_le_one {β : ℝ} (hβ : 0 ≤ β) (η : ℝ) (z : UnitAddCircle) :
    ‖shiftFactor β η z‖ ≤ 1 := by
  unfold shiftFactor
  rw [Complex.norm_exp]
  have hre : (((β * ((Real.cosh η - 1) * (cosC z - 1)) : ℝ) : ℂ) -
      Complex.I * ((β * (Real.sinh η * sinC z) : ℝ) : ℂ)).re =
      β * ((Real.cosh η - 1) * (cosC z - 1)) := by
    simp
  rw [hre, Real.exp_le_one_iff]
  have h1 : 0 ≤ Real.cosh η - 1 := by linarith [Real.one_le_cosh η]
  have h2 : cosC z - 1 ≤ 0 := by linarith [(abs_le.mp (abs_cosC_le_one z)).2]
  exact mul_nonpos_of_nonneg_of_nonpos hβ (mul_nonpos_of_nonneg_of_nonpos h1 h2)

theorem shiftFactor_neg_eta (β η : ℝ) (z : UnitAddCircle) :
    shiftFactor β (-η) z = (starRingEnd ℂ) (shiftFactor β η z) := by
  unfold shiftFactor
  rw [← Complex.exp_conj]
  congr 1
  rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I, Real.cosh_neg,
    Real.sinh_neg]
  push_cast
  ring

theorem shiftFactor_neg_arg (β η : ℝ) (z : UnitAddCircle) :
    shiftFactor β η (-z) = (starRingEnd ℂ) (shiftFactor β η z) := by
  unfold shiftFactor
  rw [← Complex.exp_conj]
  congr 1
  rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I, cosC_neg,
    sinC_neg]
  push_cast
  ring

/-- The factorization of the shifted plaquette weight:
`exp(β cos(x + iη)) = e^{β cos x} · e^{β(cosh η − 1)} · i_β(η; x)`. -/
theorem exp_cosShift (β η : ℝ) (z : UnitAddCircle) :
    Complex.exp ((β : ℂ) * cosShift z η) =
      ((Real.exp (β * cosC z) : ℝ) : ℂ) * ((Real.exp (β * (Real.cosh η - 1)) : ℝ) : ℂ) *
        shiftFactor β η z := by
  unfold shiftFactor cosShift
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end

end FroehlichSpencer.FS82.ZN.Torus

end
