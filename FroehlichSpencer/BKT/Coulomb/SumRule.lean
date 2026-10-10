/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Screening and the second-moment sum rule

No spectral measure and no unconditional `tsum` is used: the abstract theorems take a two-point
function `s : ℤ² → ℝ` with the **hypothesis** `∑ (1 + |z|²) |s(z)| < ∞` (implied by the
exponential Debye screening FS81 p. 532 refers to), positive definiteness, and the test-function
bound `∑ g(x) g(y) s(y - x) ≤ c D(g)` proved for the thermodynamic limits in
`Coulomb/ThermodynamicLimit.lean`.

* `fourier_bound_of_dirichlet`: `0 ≤ ŝ(k) ≤ c ε(k)` for `ŝ(k) = ∑_z s(z) cos ⟨k, z⟩`, from the box
  Fourier modes `𝟙_{[-R,R]²} cos ⟨k,·⟩`, `𝟙_{[-R,R]²} sin ⟨k,·⟩`
  (`dirichlet_boxFourier_le`, `sum_box_box_sub`) and dominated convergence for series as `R → ∞`.
* `sumRule_of_dirichlet`: `∑_z s(z) = 0` and `M = -∑_z |z|² s(z) ≤ 4c`.
* `free_sumRule`: for every translation-invariant limit `S(x,y) = s(y - x)` of the free hard-core
  two-point functions with summable second moment, `0 ≤ ŝ ≤ (δ/κ) ε`, `∑ s = 0` and
  `M(κ) ≤ 4δ/κ`.
* **the screening sum-rule comparison, for the two normalizations**:
  `screening_value_ne_dictionary` excludes `M = 4/κ` (the value forced by boundedness of (1.17)
  with `Ĉ(k)⁻¹ = ε(k)`) for every `δ < 1`; `screening_value_ne_printed` excludes the printed
  `M = 2/κ` for `δ < 1/2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology Finset

/-! ### Counting in boxes -/

theorem card_box (R : ℕ) : (boxInternal R).card = (2 * R + 1) ^ 2 := by
  rw [boxInternal, card_product, Int.card_Icc]
  have : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
  rw [this, sq]

/-- The number of `x ∈ [-R,R]²` with `x + z ∈ [-R,R]²`. -/
def boxOverlapInternal (R : ℕ) (z : ℤ × ℤ) : ℕ :=
  ((boxInternal R).filter fun x => x + z ∈ boxInternal R).card

theorem boxOverlap_le (R : ℕ) (z : ℤ × ℤ) : boxOverlapInternal R z ≤ (2 * R + 1) ^ 2 := by
  rw [← card_box]; exact card_filter_le _ _

theorem boxOverlap_eq_zero {R : ℕ} {z : ℤ × ℤ} (hz : z ∉ boxInternal (2 * R)) :
    boxOverlapInternal R z = 0 := by
  rw [boxOverlapInternal, card_eq_zero, filter_eq_empty_iff]
  intro x hx hxz
  apply hz
  rw [mem_box_iff] at hx hxz ⊢
  simp only [Prod.fst_add, Prod.snd_add] at hxz
  push_cast
  constructor
  · calc |z.1| = |(x.1 + z.1) - x.1| := by ring_nf
      _ ≤ |x.1 + z.1| + |x.1| := abs_sub _ _
      _ ≤ 2 * R := by linarith [hxz.1, hx.1]
  · calc |z.2| = |(x.2 + z.2) - x.2| := by ring_nf
      _ ≤ |x.2 + z.2| + |x.2| := abs_sub _ _
      _ ≤ 2 * R := by linarith [hxz.2, hx.2]

theorem boxOverlap_ge {R m : ℕ} {z : ℤ × ℤ} (hm : m ≤ R) (hz1 : |z.1| ≤ m) (hz2 : |z.2| ≤ m) :
    (2 * (R - m) + 1) ^ 2 ≤ boxOverlapInternal R z := by
  rw [← card_box]
  refine card_le_card fun x hx => ?_
  rw [mem_filter]
  rw [mem_box_iff] at hx
  have hRm : ((R - m : ℕ) : ℤ) = R - m := by omega
  rw [hRm] at hx
  constructor
  · rw [mem_box_iff]; constructor <;> linarith [hx.1, hx.2, abs_nonneg z.1]
  · rw [mem_box_iff]
    simp only [Prod.fst_add, Prod.snd_add]
    constructor
    · calc |x.1 + z.1| ≤ |x.1| + |z.1| := abs_add_le _ _
        _ ≤ R := by linarith [hx.1]
    · calc |x.2 + z.2| ≤ |x.2| + |z.2| := abs_add_le _ _
        _ ≤ R := by linarith [hx.2]

/-- Double sums of a difference kernel over a box. -/
theorem sum_box_box_sub (R : ℕ) (F : ℤ × ℤ → ℝ) :
    ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, F (y - x) =
      ∑ z ∈ boxInternal (2 * R), (boxOverlapInternal R z : ℝ) * F z := by
  have hinner : ∀ x ∈ boxInternal R, ∑ y ∈ boxInternal R, F (y - x) =
      ∑ z ∈ boxInternal (2 * R), if x + z ∈ boxInternal R then F z else 0 := by
    intro x hx
    rw [← sum_filter]
    refine sum_nbij' (fun y => y - x) (fun z => x + z) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_filter]
      refine ⟨?_, by simpa using hy⟩
      rw [mem_box_iff] at hx hy ⊢
      simp only [Prod.fst_sub, Prod.snd_sub]
      push_cast
      constructor
      · calc |y.1 - x.1| ≤ |y.1| + |x.1| := abs_sub _ _
          _ ≤ 2 * R := by linarith [hx.1, hy.1]
      · calc |y.2 - x.2| ≤ |y.2| + |x.2| := abs_sub _ _
          _ ≤ 2 * R := by linarith [hx.2, hy.2]
    · intro z hz
      exact (mem_filter.1 hz).2
    · intro y _; simp
    · intro z _; simp
    · intro y _; rfl
  rw [sum_congr rfl hinner, sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [boxOverlapInternal, ← sum_filter, sum_const, nsmul_eq_mul]

/-! ### Box Fourier test functions -/

/-- `𝟙_{[-R,R]²}(x) cos ⟨k, x⟩`. -/
def boxCosInternal (R : ℕ) (k : ℝ × ℝ) (x : ℤ × ℤ) : ℝ :=
  if x ∈ boxInternal R then Real.cos (k.1 * x.1 + k.2 * x.2) else 0

/-- `𝟙_{[-R,R]²}(x) sin ⟨k, x⟩`. -/
def boxSinInternal (R : ℕ) (k : ℝ × ℝ) (x : ℤ × ℤ) : ℝ :=
  if x ∈ boxInternal R then Real.sin (k.1 * x.1 + k.2 * x.2) else 0

theorem boxCos_supported (R : ℕ) (k : ℝ × ℝ) : SupportedInBox R (boxCosInternal R k) :=
  fun x hx => by simp [boxCosInternal, hx]

theorem boxSin_supported (R : ℕ) (k : ℝ × ℝ) : SupportedInBox R (boxSinInternal R k) :=
  fun x hx => by simp [boxSinInternal, hx]

theorem cos_sub_sq_add_sin_sub_sq (θ a : ℝ) :
    (Real.cos θ - Real.cos (θ + a)) ^ 2 + (Real.sin θ - Real.sin (θ + a)) ^ 2 =
      2 * (1 - Real.cos a) := by
  rw [Real.cos_add, Real.sin_add]
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq a
  nlinarith [h1, h2]

theorem mem_box_succ_of_add_mem {R : ℕ} {x e : ℤ × ℤ} (he : |e.1| ≤ 1 ∧ |e.2| ≤ 1)
    (h : x + e ∈ boxInternal R) : x ∈ boxInternal (R + 1) := by
  rw [mem_box_iff] at h ⊢
  simp only [Prod.fst_add, Prod.snd_add] at h
  push_cast
  constructor
  · calc |x.1| = |(x.1 + e.1) - e.1| := by ring_nf
      _ ≤ |x.1 + e.1| + |e.1| := abs_sub _ _
      _ ≤ R + 1 := by linarith [h.1, he.1]
  · calc |x.2| = |(x.2 + e.2) - e.2| := by ring_nf
      _ ≤ |x.2 + e.2| + |e.2| := abs_sub _ _
      _ ≤ R + 1 := by linarith [h.2, he.2]

theorem add_mem_box_of_mem_pred {R : ℕ} (hR : 1 ≤ R) {x e : ℤ × ℤ}
    (he : |e.1| ≤ 1 ∧ |e.2| ≤ 1) (h : x ∈ boxInternal (R - 1)) : x + e ∈ boxInternal R := by
  rw [mem_box_iff] at h ⊢
  have hR' : ((R - 1 : ℕ) : ℤ) = R - 1 := by omega
  rw [hR'] at h
  simp only [Prod.fst_add, Prod.snd_add]
  constructor
  · calc |x.1 + e.1| ≤ |x.1| + |e.1| := abs_add_le _ _
      _ ≤ R := by linarith [h.1, he.1]
  · calc |x.2 + e.2| ≤ |x.2| + |e.2| := abs_add_le _ _
      _ ≤ R := by linarith [h.2, he.2]

/-- The per-edge bound for the box Fourier test functions. -/
theorem boxFourier_edge_le {R : ℕ} (hR : 1 ≤ R) (k : ℝ × ℝ) (x e : ℤ × ℤ)
    (he : |e.1| ≤ 1 ∧ |e.2| ≤ 1) :
    (boxCosInternal R k x - boxCosInternal R k (x + e)) ^ 2 +
        (boxSinInternal R k x - boxSinInternal R k (x + e)) ^ 2 ≤
      (if x ∈ boxInternal R then 2 * (1 - Real.cos (k.1 * e.1 + k.2 * e.2)) else 0) +
        2 * (if x ∈ boxInternal (R + 1) ∧ x ∉ boxInternal (R - 1) then 1 else 0) := by
  have hph : k.1 * ((x + e).1 : ℤ) + k.2 * ((x + e).2 : ℤ) =
      (k.1 * x.1 + k.2 * x.2) + (k.1 * e.1 + k.2 * e.2) := by
    simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring
  have hc := Real.cos_le_one (k.1 * e.1 + k.2 * e.2)
  unfold boxCosInternal boxSinInternal
  by_cases hx : x ∈ boxInternal R <;> by_cases hxe : x + e ∈ boxInternal R
  · simp only [hx, hxe, ite_true]
    rw [hph, cos_sub_sq_add_sin_sub_sq]
    have : (0 : ℝ) ≤ 2 * (if x ∈ boxInternal (R + 1) ∧ x ∉ boxInternal (R - 1) then 1 else 0) := by
      positivity
    linarith
  · have hA : x ∈ boxInternal (R + 1) ∧ x ∉ boxInternal (R - 1) :=
      ⟨box_mono (Nat.le_succ R) hx, fun h => hxe (add_mem_box_of_mem_pred hR he h)⟩
    simp only [hx, hxe, hA, ite_true, ite_false, not_false_eq_true, and_self]
    have := Real.sin_sq_add_cos_sq (k.1 * x.1 + k.2 * x.2)
    nlinarith
  · have hA : x ∈ boxInternal (R + 1) ∧ x ∉ boxInternal (R - 1) :=
      ⟨mem_box_succ_of_add_mem he hxe, fun h => hx (box_mono (Nat.sub_le R 1) h)⟩
    simp only [hx, hxe, hA, ite_true, ite_false, not_false_eq_true, and_self]
    have := Real.sin_sq_add_cos_sq (k.1 * ((x + e).1 : ℤ) + k.2 * ((x + e).2 : ℤ))
    nlinarith
  · simp only [hx, hxe, ite_false]
    have : (0 : ℝ) ≤ 2 * (if x ∈ boxInternal (R + 1) ∧ x ∉ boxInternal (R - 1) then 1 else 0) := by
      positivity
    nlinarith

/-- **Dirichlet energy of the box Fourier modes**:
`D(𝟙_B cos ⟨k,·⟩) + D(𝟙_B sin ⟨k,·⟩) ≤ (2R+1)² ε(k) + 4 ((2R+3)² - (2R-1)²)`. -/
theorem dirichlet_boxFourier_le {R : ℕ} (hR : 1 ≤ R) (k : ℝ × ℝ) :
    latticeDirichletInternal (boxCosInternal R k) + latticeDirichletInternal (boxSinInternal R k) ≤
      ((2 * R + 1 : ℕ) : ℝ) ^ 2 * latticeSymbolInternal k +
        4 * (((2 * R + 3 : ℕ) : ℝ) ^ 2 - ((2 * (R - 1) + 1 : ℕ) : ℝ) ^ 2) := by
  set B1 := boxInternal (R + 1)
  have hsC : SupportedInBox (R + 1) fun x =>
      (boxCosInternal R k x - boxCosInternal R k (x + (1, 0))) ^ 2 +
        (boxCosInternal R k x - boxCosInternal R k (x + (0, 1))) ^ 2 := by
    intro x hx
    simp [(boxCos_supported R k).mono (Nat.le_succ R) x hx,
      (boxCos_supported R k).shift unit_bounds_e1 x hx,
      (boxCos_supported R k).shift unit_bounds_e2 x hx]
  have hsS : SupportedInBox (R + 1) fun x =>
      (boxSinInternal R k x - boxSinInternal R k (x + (1, 0))) ^ 2 +
        (boxSinInternal R k x - boxSinInternal R k (x + (0, 1))) ^ 2 := by
    intro x hx
    simp [(boxSin_supported R k).mono (Nat.le_succ R) x hx,
      (boxSin_supported R k).shift unit_bounds_e1 x hx,
      (boxSin_supported R k).shift unit_bounds_e2 x hx]
  rw [latticeDirichletInternal, latticeDirichletInternal, hsC.finsum_eq_sum subset_rfl,
    hsS.finsum_eq_sum subset_rfl, ← sum_add_distrib]
  have hpt : ∀ x ∈ B1,
      ((boxCosInternal R k x - boxCosInternal R k (x + (1, 0))) ^ 2 +
        (boxCosInternal R k x - boxCosInternal R k (x + (0, 1))) ^ 2) +
      ((boxSinInternal R k x - boxSinInternal R k (x + (1, 0))) ^ 2 +
        (boxSinInternal R k x - boxSinInternal R k (x + (0, 1))) ^ 2) ≤
      (if x ∈ boxInternal R then latticeSymbolInternal k else 0) +
        4 * (if x ∈ boxInternal (R + 1) ∧ x ∉ boxInternal (R - 1) then 1 else 0) := by
    intro x _
    have e1 := boxFourier_edge_le hR k x (1, 0) unit_bounds_e1
    have e2 := boxFourier_edge_le hR k x (0, 1) unit_bounds_e2
    simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero, zero_add] at e1 e2
    unfold latticeSymbolInternal
    split_ifs at e1 e2 ⊢ <;> linarith
  refine (sum_le_sum hpt).trans (le_of_eq ?_)
  rw [sum_add_distrib, ← mul_sum, sum_ite_mem, sum_boole]
  have h1 : B1 ∩ boxInternal R = boxInternal R := inter_eq_right.2 (box_mono (Nat.le_succ R))
  rw [h1, sum_const, nsmul_eq_mul, card_box]
  have h2 : (B1.filter fun x => x ∈ boxInternal (R + 1) ∧ x ∉ boxInternal (R - 1)) =
      B1 \ boxInternal (R - 1) := by
    ext x; simp [B1]
  rw [h2, card_sdiff, inter_eq_left.2 (box_mono (by omega : R - 1 ≤ R + 1)), card_box, card_box]
  push_cast
  rw [Nat.cast_sub (Nat.pow_le_pow_left (by omega) 2)]
  push_cast
  ring

/-! ### The Fourier bound -/

theorem boxOverlap_div_tendsto (z : ℤ × ℤ) :
    Tendsto (fun R : ℕ => (boxOverlapInternal R z : ℝ) / ((2 * R + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 1) := by
  set m := max z.1.natAbs z.2.natAbs
  have hlow : Tendsto (fun R : ℕ => ((2 * ((R : ℝ) - m) + 1) / (2 * R + 1)) ^ 2) atTop (𝓝 1) := by
    have h : Tendsto (fun R : ℕ => (2 * ((R : ℝ) - m) + 1) / (2 * R + 1)) atTop (𝓝 1) := by
      have : (fun R : ℕ => (2 * ((R : ℝ) - m) + 1) / (2 * R + 1)) =
          fun R : ℕ => 1 - (2 * m) / (2 * (R : ℝ) + 1) := by
        funext R
        have : (2 * (R : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [this]
      have h2 : Tendsto (fun R : ℕ => (2 * (m : ℝ)) / (2 * (R : ℝ) + 1)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop).const_mul_atTop
          (by norm_num))
      simpa using tendsto_const_nhds.sub h2
    simpa using h.pow 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop m] with R hR
    have hge := boxOverlap_ge (R := R) (z := z) hR
      (by rw [Int.abs_eq_natAbs]; exact_mod_cast le_max_left _ _)
      (by rw [Int.abs_eq_natAbs]; exact_mod_cast le_max_right _ _)
    have e1 : ((2 * ((R : ℝ) - m) + 1) / (2 * R + 1)) ^ 2 =
        ((2 * (R - m) + 1 : ℕ) : ℝ) ^ 2 / ((2 * R + 1 : ℕ) : ℝ) ^ 2 := by
      rw [div_pow]
      push_cast [Nat.cast_sub hR]
      ring
    rw [e1]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hge) (by positivity)
  · filter_upwards with R
    have hpos : (0 : ℝ) < ((2 * R + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [div_le_one hpos]
    exact_mod_cast boxOverlap_le R z

theorem boundary_ratio_tendsto :
    Tendsto (fun R : ℕ => (((2 * R + 3 : ℕ) : ℝ) ^ 2 - ((2 * (R - 1) + 1 : ℕ) : ℝ) ^ 2) /
      ((2 * R + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have heq : ∀ᶠ R : ℕ in atTop, (((2 * R + 3 : ℕ) : ℝ) ^ 2 - ((2 * (R - 1) + 1 : ℕ) : ℝ) ^ 2) /
      ((2 * R + 1 : ℕ) : ℝ) ^ 2 = 8 / (2 * (R : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    push_cast [Nat.cast_sub hR]
    have : (2 * (R : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  refine tendsto_const_nhds.div_atTop ?_
  exact tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop).const_mul_atTop
    (by norm_num))

/-- **Fourier form of the test-function bound** (the charge structure factor
`ŝ(k) = ∑_z s(z) cos ⟨k, z⟩`): if a summable two-point function `s` is positive definite and
dominated by `c D(g)` on finitely supported test functions, then `0 ≤ ŝ(k) ≤ c ε(k)`. -/
theorem fourier_bound_of_dirichlet (s : ℤ × ℤ → ℝ) (hs : Summable fun z => |s z|) {c : ℝ}
    (hc : 0 ≤ c)
    (hpsd : ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g →
      0 ≤ ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x))
    (hD : ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g →
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x) ≤
        c * latticeDirichletInternal g)
    (k : ℝ × ℝ) :
    0 ≤ ∑' z : ℤ × ℤ, s z * Real.cos (k.1 * z.1 + k.2 * z.2) ∧
      ∑' z : ℤ × ℤ, s z * Real.cos (k.1 * z.1 + k.2 * z.2) ≤ c * latticeSymbolInternal k := by
  set w : ℕ → ℤ × ℤ → ℝ := fun R z =>
    (boxOverlapInternal R z : ℝ) / ((2 * R + 1 : ℕ) : ℝ) ^ 2 * (s z * Real.cos (k.1 * z.1 + k.2 * z.2))
  have hA : ∀ R : ℕ,
      (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, boxCosInternal R k x * boxCosInternal R k y * s (y - x)) +
      (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, boxSinInternal R k x * boxSinInternal R k y * s (y - x)) =
      ((2 * R + 1 : ℕ) : ℝ) ^ 2 * ∑' z, w R z := by
    intro R
    rw [← sum_add_distrib]
    have hin : ∀ x ∈ boxInternal R, (∑ y ∈ boxInternal R, boxCosInternal R k x * boxCosInternal R k y * s (y - x)) +
        ∑ y ∈ boxInternal R, boxSinInternal R k x * boxSinInternal R k y * s (y - x) =
        ∑ y ∈ boxInternal R, s (y - x) * Real.cos (k.1 * ((y - x).1 : ℤ) + k.2 * ((y - x).2 : ℤ)) := by
      intro x hx
      rw [← sum_add_distrib]
      refine sum_congr rfl fun y hy => ?_
      simp only [boxCosInternal, boxSinInternal, hx, hy, ite_true, Prod.fst_sub, Prod.snd_sub]
      push_cast
      rw [show k.1 * ((y.1 : ℝ) - x.1) + k.2 * ((y.2 : ℝ) - x.2) =
        (k.1 * y.1 + k.2 * y.2) - (k.1 * x.1 + k.2 * x.2) by ring, Real.cos_sub]
      ring
    rw [sum_congr rfl hin, sum_box_box_sub R (fun z => s z * Real.cos (k.1 * z.1 + k.2 * z.2))]
    rw [tsum_eq_sum (s := boxInternal (2 * R)) (fun z hz => by
      simp [w, boxOverlap_eq_zero hz]), mul_sum]
    refine sum_congr rfl fun z _ => ?_
    have : ((2 * R + 1 : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
    simp only [w]
    field_simp
  have hlim : Tendsto (fun R => ∑' z, w R z) atTop
      (𝓝 (∑' z : ℤ × ℤ, s z * Real.cos (k.1 * z.1 + k.2 * z.2))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun z => ?_) (Eventually.of_forall fun R z => ?_)
    · have := (boxOverlap_div_tendsto z).mul_const (s z * Real.cos (k.1 * z.1 + k.2 * z.2))
      rw [one_mul] at this
      exact this
    · simp only [w, Real.norm_eq_abs, abs_mul]
      have h1 : |(boxOverlapInternal R z : ℝ) / ((2 * R + 1 : ℕ) : ℝ) ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
        exact_mod_cast boxOverlap_le R z
      have h2 := Real.abs_cos_le_one (k.1 * z.1 + k.2 * z.2)
      calc |(boxOverlapInternal R z : ℝ) / ((2 * R + 1 : ℕ) : ℝ) ^ 2| *
            (|s z| * |Real.cos (k.1 * z.1 + k.2 * z.2)|) ≤ 1 * (|s z| * 1) := by
            gcongr
        _ = |s z| := by ring
  constructor
  · refine ge_of_tendsto hlim (Eventually.of_forall fun R => ?_)
    have h1 := hpsd R _ (boxCos_supported R k)
    have h2 := hpsd R _ (boxSin_supported R k)
    have hsum := hA R
    have hpos : (0 : ℝ) < ((2 * R + 1 : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith
  · have hupper : Tendsto (fun R : ℕ => c * (latticeSymbolInternal k + 4 *
        ((((2 * R + 3 : ℕ) : ℝ) ^ 2 - ((2 * (R - 1) + 1 : ℕ) : ℝ) ^ 2) /
          ((2 * R + 1 : ℕ) : ℝ) ^ 2))) atTop (𝓝 (c * latticeSymbolInternal k)) := by
      simpa using ((tendsto_const_nhds.add (boundary_ratio_tendsto.const_mul 4)).const_mul c)
    refine le_of_tendsto_of_tendsto hlim hupper ?_
    filter_upwards [eventually_ge_atTop 1] with R hR
    have h1 := hD R _ (boxCos_supported R k)
    have h2 := hD R _ (boxSin_supported R k)
    have hd := dirichlet_boxFourier_le hR k
    have hsum := hA R
    have hpos : (0 : ℝ) < ((2 * R + 1 : ℕ) : ℝ) ^ 2 := by positivity
    set P := ((2 * R + 1 : ℕ) : ℝ) ^ 2
    set Bd := ((2 * R + 3 : ℕ) : ℝ) ^ 2 - ((2 * (R - 1) + 1 : ℕ) : ℝ) ^ 2
    have key : P * ∑' z, w R z ≤ P * (c * latticeSymbolInternal k) + c * (4 * Bd) := by
      nlinarith [mul_le_mul_of_nonneg_left hd hc]
    calc ∑' z, w R z = (P * ∑' z, w R z) / P := by field_simp
      _ ≤ (P * (c * latticeSymbolInternal k) + c * (4 * Bd)) / P :=
          div_le_div_of_nonneg_right key hpos.le
      _ = c * (latticeSymbolInternal k + 4 * (Bd / P)) := by field_simp

/-! ### The second-moment sum rule -/

theorem tendsto_sin_mul_div (a : ℝ) :
    Tendsto (fun t : ℝ => Real.sin (t * a) / t) (𝓝[≠] 0) (𝓝 a) := by
  have hd : HasDerivAt (fun t : ℝ => Real.sin (t * a)) a 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).mul_const a).sin
    simpa using this
  have hslope := hd.tendsto_slope_zero
  refine hslope.congr' (Eventually.of_forall fun t => ?_)
  simp [div_eq_inv_mul]

theorem tendsto_cos_sub_one_div_sq (x : ℝ) :
    Tendsto (fun t : ℝ => (Real.cos (t * x) - 1) / t ^ 2) (𝓝[≠] 0) (𝓝 (-(x ^ 2) / 2)) := by
  have h := (tendsto_sin_mul_div (x / 2)).pow 2 |>.const_mul (-2)
  refine (h.congr' ?_).trans (by rw [show -2 * (x / 2) ^ 2 = -(x ^ 2) / 2 by ring])
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero 2 ht')]
  have := one_sub_cos_eq_two_mul_sin_sq (t * x)
  rw [show t * x / 2 = t * (x / 2) by ring] at this
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 ht')]
  linarith

theorem abs_cos_sub_one_div_sq_le (t x : ℝ) (ht : t ≠ 0) :
    |(Real.cos (t * x) - 1) / t ^ 2| ≤ x ^ 2 / 2 := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := t * x)
  have h2 := Real.cos_le_one (t * x)
  have hpos : (0 : ℝ) < t ^ 2 := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_of_nonpos (by linarith)]
  nlinarith

/-- One direction of the sum rule: `-(1/2) ∑ z_i² s(z) ≤ c` from `ŝ(k) ≤ c ε(k)` along an axis. -/
theorem neg_half_moment_le (s : ℤ × ℤ → ℝ) (π : ℤ × ℤ → ℤ)
    (hs2 : Summable fun z => ((π z : ℝ) ^ 2) * |s z|) (hs : Summable fun z => |s z|) {c : ℝ}
    (hs0 : ∑' z, s z = 0)
    (hF : ∀ t : ℝ, ∑' z, s z * Real.cos (t * π z) ≤ c * (2 * (1 - Real.cos t))) :
    -(∑' z, ((π z : ℝ) ^ 2) * s z) / 2 ≤ c := by
  have hsumS : Summable s := hs.of_abs
  have hlim : Tendsto (fun t : ℝ => ∑' z, s z * ((Real.cos (t * π z) - 1) / t ^ 2)) (𝓝[≠] 0)
      (𝓝 (∑' z, s z * (-((π z : ℝ) ^ 2) / 2))) := by
    refine tendsto_tsum_of_dominated_convergence (hs2.div_const 2) (fun z => ?_) ?_
    · exact (tendsto_cos_sub_one_div_sq (π z)).const_mul (s z)
    · filter_upwards [self_mem_nhdsWithin] with t ht z
      rw [Real.norm_eq_abs, abs_mul]
      have := abs_cos_sub_one_div_sq_le t (π z) ht
      calc |s z| * |(Real.cos (t * π z) - 1) / t ^ 2| ≤ |s z| * ((π z : ℝ) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = (π z : ℝ) ^ 2 * |s z| / 2 := by ring
  have hrhs : Tendsto (fun t : ℝ => c * (2 * ((1 - Real.cos t) / t ^ 2))) (𝓝[≠] 0) (𝓝 c) := by
    have h := tendsto_cos_sub_one_div_sq 1
    simp only [mul_one, one_pow] at h
    have h' : Tendsto (fun t : ℝ => (1 - Real.cos t) / t ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
      have := h.neg
      refine this.congr' (Eventually.of_forall fun t => ?_) |>.trans (by norm_num)
      ring
    simpa using (h'.const_mul 2).const_mul c
  have hle : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∑' z, s z * ((Real.cos (t * π z) - 1) / t ^ 2) ≤
      c * (2 * ((1 - Real.cos t) / t ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    have hpos : (0 : ℝ) < t ^ 2 := by positivity
    have hsum1 : Summable fun z => s z * Real.cos (t * π z) :=
      Summable.of_norm_bounded hs fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have e : ∑' z, s z * ((Real.cos (t * π z) - 1) / t ^ 2) =
        (∑' z, s z * Real.cos (t * π z) - ∑' z, s z) / t ^ 2 := by
      rw [← hsum1.tsum_sub hsumS, ← tsum_div_const]
      congr 1; funext z; ring
    rw [e, hs0, sub_zero, div_le_iff₀ hpos]
    have := hF t
    calc ∑' z, s z * Real.cos (t * π z) ≤ c * (2 * (1 - Real.cos t)) := this
      _ = c * (2 * ((1 - Real.cos t) / t ^ 2)) * t ^ 2 := by field_simp
  have hmain := le_of_tendsto_of_tendsto hlim hrhs hle
  have e2 : ∑' z, s z * (-((π z : ℝ) ^ 2) / 2) = -(∑' z, ((π z : ℝ) ^ 2) * s z) / 2 := by
    rw [neg_div, ← tsum_div_const, ← tsum_neg]
    congr 1; funext z; ring
  rwa [e2] at hmain

/-- **The second-moment sum rule bound.** If a two-point function `s` has
`∑ (1 + |z|²) |s(z)| < ∞`, is positive definite and is dominated by `c D(g)` on test functions,
then `∑_z s(z) = 0` (perfect screening of the total charge) and the Stillinger–Lovett moment
`M = -∑_z |z|² s(z)` satisfies `M ≤ 4c`. -/
theorem sumRule_of_dirichlet (s : ℤ × ℤ → ℝ)
    (hs2 : Summable fun z : ℤ × ℤ => (1 + (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) * |s z|) {c : ℝ}
    (hc : 0 ≤ c)
    (hpsd : ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g →
      0 ≤ ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x))
    (hD : ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g →
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x) ≤
        c * latticeDirichletInternal g) :
    ∑' z, s z = 0 ∧ -∑' z : ℤ × ℤ, ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) * s z ≤ 4 * c := by
  have hs : Summable fun z => |s z| := Summable.of_nonneg_of_le (fun z => abs_nonneg _)
    (fun z => by nlinarith [abs_nonneg (s z), sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]) hs2
  have hs1 : Summable fun z : ℤ × ℤ => ((z.1 : ℝ) ^ 2) * |s z| :=
    Summable.of_nonneg_of_le (fun z => by positivity)
      (fun z => by nlinarith [abs_nonneg (s z), sq_nonneg (z.2 : ℝ)]) hs2
  have hs2' : Summable fun z : ℤ × ℤ => ((z.2 : ℝ) ^ 2) * |s z| :=
    Summable.of_nonneg_of_le (fun z => by positivity)
      (fun z => by nlinarith [abs_nonneg (s z), sq_nonneg (z.1 : ℝ)]) hs2
  have F := fourier_bound_of_dirichlet s hs hc hpsd hD
  have hs0 : ∑' z, s z = 0 := by
    have h := F (0, 0)
    simp only [zero_mul, add_zero, Real.cos_zero, mul_one, latticeSymbolInternal, sub_self,
      mul_zero] at h
    linarith [h.1, h.2]
  refine ⟨hs0, ?_⟩
  have d1 := neg_half_moment_le s (fun z => z.1) hs1 hs hs0 (fun t => by
    have := (F (t, 0)).2
    simpa [latticeSymbolInternal] using this)
  have d2 := neg_half_moment_le s (fun z => z.2) hs2' hs hs0 (fun t => by
    have := (F (0, t)).2
    simpa [latticeSymbolInternal] using this)
  have hsum1 : Summable fun z : ℤ × ℤ => ((z.1 : ℝ) ^ 2) * s z :=
    Summable.of_norm_bounded hs1 fun z => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have hsum2 : Summable fun z : ℤ × ℤ => ((z.2 : ℝ) ^ 2) * s z :=
    Summable.of_norm_bounded hs2' fun z => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have e : ∑' z : ℤ × ℤ, ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) * s z =
      ∑' z : ℤ × ℤ, ((z.1 : ℝ) ^ 2) * s z + ∑' z : ℤ × ℤ, ((z.2 : ℝ) ^ 2) * s z := by
    rw [← hsum1.tsum_add hsum2]
    congr 1; funext z; ring
  rw [e]
  linarith

/-! ### Application: translation-invariant thermodynamic limits (FS81 p. 567, (1.17)–(1.18)) -/

/-- ** the screening sum rule fails in every translation-invariant thermodynamic limit with a
summable second moment.** For a limit `S` of the free two-point functions of the hard-core gas
which is translation invariant, `S(x,y) = s(y - x)`, with `∑ (1 + |z|²)|s(z)| < ∞`:
the charge structure factor satisfies `0 ≤ ŝ(k) ≤ (δ/κ) ε(k)` (FS81 p. 567: `S_q ≤ δ κ⁻¹ Ĉ⁻¹`,
`Ĉ(k)⁻¹ = ε(k)`), `∑_z s(z) = 0`, and FS81's moment (1.18) `M(κ) = -∑_j |j|² ⟨q(0) q(j)⟩`
satisfies `M(κ) ≤ 4δ/κ`. -/
theorem free_sumRule {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀) (hδ : 0 ≤ δ)
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {S : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hS : ∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
      (𝓝 (S x y)))
    {s : ℤ × ℤ → ℝ} (hts : ∀ x y, S x y = s (y - x))
    (hs2 : Summable fun z : ℤ × ℤ => (1 + (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) * |s z|) :
    (∀ k : ℝ × ℝ, 0 ≤ ∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2) ∧
      ∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2) ≤ δ / κ * latticeSymbolInternal k) ∧
    ∑' w, s w = 0 ∧
    -∑' w : ℤ × ℤ, ((w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2) * s w ≤ 4 * (δ / κ) := by
  have hc : 0 ≤ δ / κ := div_nonneg hδ hκ.le
  have hscr := fun (R : ℕ) (g : ℤ × ℤ → ℝ) (hg : SupportedInBox R g) =>
    free_infinite_screening h κ hκ hκκ₀ z hz hzκ hφ hS hg
  simp_rw [hts] at hscr
  have hs : Summable fun w => |s w| := Summable.of_nonneg_of_le (fun w => abs_nonneg _)
    (fun w => by nlinarith [abs_nonneg (s w), sq_nonneg (w.1 : ℝ), sq_nonneg (w.2 : ℝ)]) hs2
  exact ⟨fourier_bound_of_dirichlet s hs hc (fun R g hg => (hscr R g hg).1)
      (fun R g hg => (hscr R g hg).2),
    sumRule_of_dirichlet s hs2 hc (fun R g hg => (hscr R g hg).1) (fun R g hg => (hscr R g hg).2)⟩

/-- **the screening sum-rule comparison, alternative (a) (dictionary value).** With `C = (-Δ)⁻¹` and `Ĉ(k)⁻¹ = ε(k)`,
boundedness of (1.17) at `k = 0` requires `S_q(k) = |k|²/κ + o(|k|²)`, i.e. `M = 4/κ`. A moment
bound `M ≤ 4δ/κ` with `δ < 1` excludes this value. -/
theorem screening_value_ne_dictionary {M δ κ : ℝ} (hκ : 0 < κ) (hδ1 : δ < 1)
    (hM : M ≤ 4 * (δ / κ)) : M ≠ 4 / κ := by
  intro hMe
  rw [hMe] at hM
  have : 4 / κ ≤ 4 * δ / κ := by rwa [mul_div_assoc]
  rw [div_le_div_iff_of_pos_right hκ] at this
  linarith

/-- **the screening sum-rule comparison, alternative (b) (printed value).** FS81 (1.18) prints the screening value
`M(β) = 2β⁻¹`; a moment bound `M ≤ 4δ/κ` excludes it when `δ < 1/2`. -/
theorem screening_value_ne_printed {M δ κ : ℝ} (hκ : 0 < κ) (hδ : δ < 1 / 2)
    (hM : M ≤ 4 * (δ / κ)) : M ≠ 2 / κ := by
  intro hMe
  rw [hMe] at hM
  have : 2 / κ ≤ 4 * δ / κ := by rwa [mul_div_assoc]
  rw [div_le_div_iff_of_pos_right hκ] at this
  linarith

end FroehlichSpencer.BKT.Coulomb
