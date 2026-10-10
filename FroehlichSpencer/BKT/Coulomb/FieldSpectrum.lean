/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.SumRule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# FS81 (1.17) in infinite volume and the field spectral bound of p. 567

* `freeSecondMoment_neg_laplacian` / `free_infinite_secondMoment_neg_laplacian`: **(1.17) in real
  space** for the test functions `-Δg`, in finite volume and in every joint free thermodynamic
  limit: `⟨φ(-Δg)²⟩ = κ D(g) - κ² ⟨⟨q, g⟩²⟩` (since `C(-Δg) = g` and `⟨-Δg, g⟩ = D(g)`).
* Box Fourier modes `g_c = 𝟙_{[-R,R]²} cos⟨k,·⟩`, `g_s = 𝟙 sin⟨k,·⟩`:
  `(D(g_c) + D(g_s))/(2R+1)² → ε(k)` (`tendsto_dirichlet_boxFourier`), and for summable
  translation-invariant `s`, `(∑ g_c g_c s + ∑ g_s g_s s)/(2R+1)² → ŝ(k)`
  (`tendsto_boxFourier_quadratic`).
* `fieldFourierInternal Γ R k = ⟨φ(-Δ g_c)²⟩ + ⟨φ(-Δ g_s)²⟩`; in Fourier variables
  `T_R(k)/((2R+1)² ε(k)²)` approximates the field structure factor `⟨|φ̂(k)|²⟩`.
* **`free_field_spectral_lower`** (every free limit, no translation invariance needed):
  `T_R(k) ≥ (1 - δ) κ (D(g_c) + D(g_s))`, so `liminf T_R/((2R+1)²ε²) ≥ (1 - δ) κ Ĉ(k)`.
* **`free_field_spectral_density`** (translation-invariant limit with summable second moment):
  `T_R/((2R+1)²ε²) → S_φ(k) = κ Ĉ(k) - κ² Ĉ(k)² ŝ(k)` — **(1.17) in Fourier form, infinite
  volume** — and `S_φ(k) ≥ (1 - δ) κ Ĉ(k)` (J p. 567).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology Finset

/-! ### The free gas against Laplacian test functions -/

section Laplacian

variable {Λ : Finset (ℤ × ℤ)} {R : ℕ} {g : ℤ × ℤ → ℝ}

theorem sum_neg_laplacian_restrict (hg : SupportedInBox R g) (hΛ : boxInternal (R + 1) ⊆ Λ) :
    ∑ v : Λ, -latticeLaplacianInternal g v.1 = 0 := by
  rw [Finset.sum_neg_distrib, Finset.sum_coe_sort Λ (fun x => latticeLaplacianInternal g x),
    sum_laplacian_eq_zero hg hΛ, neg_zero]

theorem neg_freePotentialOp_neg_laplacian (hg : SupportedInBox R g)
    (hΛ : boxInternal (R + 1) ⊆ Λ) (v : Λ) :
    -(freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)
      (fun u => -latticeLaplacianInternal g u.1) v) = g v.1 := by
  rw [freePotentialOp_apply]
  simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_coe_sort Λ (fun y => potentialKernelInternal (v.1 - y) *
    latticeLaplacianInternal g y), sum_potentialKernel_mul_laplacian hg hΛ]

theorem freeQuad_neg_laplacian (hg : SupportedInBox R g) (hΛ : boxInternal (R + 1) ⊆ Λ) :
    freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) (fun u => -latticeLaplacianInternal g u.1) =
      latticeDirichletInternal g := by
  unfold freeQuadInternal
  simp_rw [neg_freePotentialOp_neg_laplacian hg hΛ]
  have hsupp : SupportedInBox R fun x => g x * -(latticeLaplacianInternal g x) :=
    fun x hx => by simp [hg x hx]
  rw [← finsum_mul_neg_laplacian hg, hsupp.finsum_eq_sum
    ((box_mono (Nat.le_succ R)).trans hΛ), ← Finset.sum_coe_sort Λ]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem freeChargePairing_neg_laplacian (hg : SupportedInBox R g)
    (hΛ : boxInternal (R + 1) ⊆ Λ) (p : Λ → ℤ) :
    freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) (fun u => -latticeLaplacianInternal g u.1) p =
      ∑ v, (p v : ℝ) * g v.1 := by
  unfold freeChargePairingInternal
  simp_rw [neg_freePotentialOp_neg_laplacian hg hΛ]

/-- **FS81 (1.17) for Laplacian test functions, finite volume**:
`⟨φ(-Δg)²⟩_{Λ_n} = κ D(g) - κ² ∑ g(x) g(y) ⟨q(x) q(y)⟩_{Λ_n}` once `Λ_n ⊇ [-(R+1), R+1]²`. -/
theorem freeSecondMoment_neg_laplacian (κ z : ℝ) {n : ℕ} (hn : R + 1 ≤ n)
    (hg : SupportedInBox R g) :
    ∑ x ∈ boxInternal (R + 1), ∑ y ∈ boxInternal (R + 1),
        (-latticeLaplacianInternal g x) * (-latticeLaplacianInternal g y) *
          freeFieldCorrelationInternal κ z n x y =
      κ * latticeDirichletInternal g - κ ^ 2 *
        ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y *
          freeChargeCorrelationInternal κ z n x y := by
  have hΛ : boxInternal (R + 1) ⊆ boxInternal n := box_mono hn
  have hf : SupportedInBox (R + 1) fun x => -latticeLaplacianInternal g x := fun x hx => by
    simp [hg.laplacian x hx]
  have hf0 : ∑ x ∈ boxInternal (R + 1), -latticeLaplacianInternal g x = 0 := by
    rw [Finset.sum_neg_distrib, sum_laplacian_eq_zero hg subset_rfl, neg_zero]
  rw [← freeSecondMoment_box_eq_sum κ z hn hf hf0]
  unfold freeSecondMomentInternal
  rw [freeQuad_neg_laplacian hg hΛ]
  simp_rw [freeChargePairing_neg_laplacian hg hΛ]
  have hsc : freeGasExpectationInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ z
      (fun p => (κ * ∑ v, (p v : ℝ) * g v.1) ^ 2) =
      κ ^ 2 * freeGasExpectationInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ z
        (fun p => (∑ v, (p v : ℝ) * g v.1) ^ 2) := by
    unfold freeGasExpectationInternal
    rw [← gasExpectation_const_mul]
    congr 1; funext p; ring
  rw [hsc, freeGasExpectation_sq_eq_sum κ z hg]
  rfl

end Laplacian

/-! ### (1.17) in infinite volume -/

/-- **FS81 (1.17) in infinite volume, real space** (Laplacian test functions): along any joint
thermodynamic limit `(Γ, S)` of the free field and charge two-point functions,
`∑ (-Δg)(x) (-Δg)(y) Γ(x,y) = κ D(g) - κ² ∑ g(x) g(y) S(x,y)`. -/
theorem free_infinite_secondMoment_neg_laplacian (κ z : ℝ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {Γ S : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hΓ : ∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop (𝓝 (Γ x y)))
    (hS : ∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
      (𝓝 (S x y)))
    {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    ∑ x ∈ boxInternal (R + 1), ∑ y ∈ boxInternal (R + 1),
        (-latticeLaplacianInternal g x) * (-latticeLaplacianInternal g y) * Γ x y =
      κ * latticeDirichletInternal g - κ ^ 2 *
        ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * S x y := by
  have hL := tendsto_finsetSum (boxInternal (R + 1)) fun x _ =>
    tendsto_finsetSum (boxInternal (R + 1)) fun y _ =>
      (hΓ x y).const_mul ((-latticeLaplacianInternal g x) * (-latticeLaplacianInternal g y))
  have hR := (tendsto_const_nhds (x := κ * latticeDirichletInternal g)).sub
    ((tendsto_finsetSum (boxInternal R) fun x _ => tendsto_finsetSum (boxInternal R) fun y _ =>
      (hS x y).const_mul (g x * g y)).const_mul (κ ^ 2))
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop (R + 1)] with k hk
  exact (freeSecondMoment_neg_laplacian κ z hk hg).symm

/-! ### Box Fourier modes -/

theorem boxFourier_edge_ge (R : ℕ) (k : ℝ × ℝ) (x e : ℤ × ℤ) :
    (if x ∈ boxInternal R ∧ x + e ∈ boxInternal R then
        2 * (1 - Real.cos (k.1 * e.1 + k.2 * e.2)) else 0) ≤
      (boxCosInternal R k x - boxCosInternal R k (x + e)) ^ 2 +
        (boxSinInternal R k x - boxSinInternal R k (x + e)) ^ 2 := by
  split_ifs with h
  · have hph : k.1 * ((x + e).1 : ℤ) + k.2 * ((x + e).2 : ℤ) =
        (k.1 * x.1 + k.2 * x.2) + (k.1 * e.1 + k.2 * e.2) := by
      simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring
    simp only [boxCosInternal, boxSinInternal, h.1, h.2, ite_true]
    rw [hph, cos_sub_sq_add_sin_sub_sq]
  · positivity

theorem boxOverlap_eq_sum (R : ℕ) (e : ℤ × ℤ) :
    (boxOverlapInternal R e : ℝ) = ∑ x ∈ boxInternal (R + 1),
      if x ∈ boxInternal R ∧ x + e ∈ boxInternal R then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole, boxOverlapInternal]
  congr 2
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hx, hxe⟩; exact ⟨box_mono (Nat.le_succ R) hx, hx, hxe⟩
  · rintro ⟨_, hx, hxe⟩; exact ⟨hx, hxe⟩

/-- Lower bound for the Dirichlet energy of the box Fourier modes. -/
theorem dirichlet_boxFourier_ge (R : ℕ) (k : ℝ × ℝ) :
    (boxOverlapInternal R (1, 0) : ℝ) * (2 * (1 - Real.cos k.1)) +
        (boxOverlapInternal R (0, 1) : ℝ) * (2 * (1 - Real.cos k.2)) ≤
      latticeDirichletInternal (boxCosInternal R k) + latticeDirichletInternal (boxSinInternal R k) := by
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
    hsS.finsum_eq_sum subset_rfl, ← sum_add_distrib, boxOverlap_eq_sum R (1, 0),
    boxOverlap_eq_sum R (0, 1), Finset.sum_mul, Finset.sum_mul, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  have e1 := boxFourier_edge_ge R k x (1, 0)
  have e2 := boxFourier_edge_ge R k x (0, 1)
  simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero, zero_add] at e1 e2
  split_ifs at e1 e2 ⊢ <;> linarith

/-- `(D(𝟙_B cos) + D(𝟙_B sin)) / (2R+1)² → ε(k)`. -/
theorem tendsto_dirichlet_boxFourier (k : ℝ × ℝ) :
    Tendsto (fun R : ℕ => (latticeDirichletInternal (boxCosInternal R k) +
        latticeDirichletInternal (boxSinInternal R k)) / ((2 * R + 1 : ℕ) : ℝ) ^ 2) atTop
      (𝓝 (latticeSymbolInternal k)) := by
  have hlow : Tendsto (fun R : ℕ => ((boxOverlapInternal R (1, 0) : ℝ) * (2 * (1 - Real.cos k.1)) +
      (boxOverlapInternal R (0, 1) : ℝ) * (2 * (1 - Real.cos k.2))) / ((2 * R + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 (latticeSymbolInternal k)) := by
    have h1 := (boxOverlap_div_tendsto (1, 0)).mul_const (2 * (1 - Real.cos k.1))
    have h2 := (boxOverlap_div_tendsto (0, 1)).mul_const (2 * (1 - Real.cos k.2))
    have := h1.add h2
    rw [one_mul, one_mul] at this
    refine this.congr' (Eventually.of_forall fun R => ?_)
    simp only
    rw [add_div, mul_div_right_comm, mul_div_right_comm]
  have hup : Tendsto (fun R : ℕ => latticeSymbolInternal k + 4 *
      ((((2 * R + 3 : ℕ) : ℝ) ^ 2 - ((2 * (R - 1) + 1 : ℕ) : ℝ) ^ 2) /
        ((2 * R + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 (latticeSymbolInternal k)) := by
    simpa using tendsto_const_nhds.add (boundary_ratio_tendsto.const_mul 4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards with R
    exact div_le_div_of_nonneg_right (dirichlet_boxFourier_ge R k) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with R hR
    have hd := dirichlet_boxFourier_le hR k
    have hpos : (0 : ℝ) < ((2 * R + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    calc _ ≤ _ := hd
      _ = (latticeSymbolInternal k + 4 * ((((2 * R + 3 : ℕ) : ℝ) ^ 2 -
            ((2 * (R - 1) + 1 : ℕ) : ℝ) ^ 2) / ((2 * R + 1 : ℕ) : ℝ) ^ 2)) *
            ((2 * R + 1 : ℕ) : ℝ) ^ 2 := by field_simp

/-- The charge side of the box Fourier modes: for a summable translation-invariant `s`,
`(∑ g_c g_c s + ∑ g_s g_s s)/(2R+1)² → ŝ(k)`. -/
theorem tendsto_boxFourier_quadratic (s : ℤ × ℤ → ℝ) (hs : Summable fun z => |s z|) (k : ℝ × ℝ) :
    Tendsto (fun R : ℕ =>
      ((∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, boxCosInternal R k x * boxCosInternal R k y * s (y - x)) +
        (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, boxSinInternal R k x * boxSinInternal R k y * s (y - x))) /
          ((2 * R + 1 : ℕ) : ℝ) ^ 2) atTop
      (𝓝 (∑' z : ℤ × ℤ, s z * Real.cos (k.1 * z.1 + k.2 * z.2))) := by
  set w : ℕ → ℤ × ℤ → ℝ := fun R z =>
    (boxOverlapInternal R z : ℝ) / ((2 * R + 1 : ℕ) : ℝ) ^ 2 * (s z * Real.cos (k.1 * z.1 + k.2 * z.2))
  have hA : ∀ R : ℕ,
      ((∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, boxCosInternal R k x * boxCosInternal R k y * s (y - x)) +
      (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, boxSinInternal R k x * boxSinInternal R k y * s (y - x))) /
        ((2 * R + 1 : ℕ) : ℝ) ^ 2 = ∑' z, w R z := by
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
      simp [w, boxOverlap_eq_zero hz]), sum_div]
    refine sum_congr rfl fun z _ => ?_
    simp only [w]
    ring
  simp_rw [hA]
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
          (|s z| * |Real.cos (k.1 * z.1 + k.2 * z.2)|) ≤ 1 * (|s z| * 1) := by gcongr
      _ = |s z| := by ring

/-! ### The field spectral bound of J p. 567 -/

/-- The field quadratic form of the box Fourier mode of `-Δφ`:
`T_R(k) = ⟨φ(-Δ 𝟙_B cos⟨k,·⟩)²⟩ + ⟨φ(-Δ 𝟙_B sin⟨k,·⟩)²⟩` for a field two-point function `Γ`. In a
translation-invariant state `T_R(k) / ((2R+1)² ε(k)²)` approximates `⟨|φ̂(k)|²⟩`. -/
def fieldFourierInternal (Γ : ℤ × ℤ → ℤ × ℤ → ℝ) (R : ℕ) (k : ℝ × ℝ) : ℝ :=
  (∑ x ∈ boxInternal (R + 1), ∑ y ∈ boxInternal (R + 1),
    (-latticeLaplacianInternal (boxCosInternal R k) x) *
      (-latticeLaplacianInternal (boxCosInternal R k) y) * Γ x y) +
  (∑ x ∈ boxInternal (R + 1), ∑ y ∈ boxInternal (R + 1),
    (-latticeLaplacianInternal (boxSinInternal R k) x) *
      (-latticeLaplacianInternal (boxSinInternal R k) y) * Γ x y)

theorem wholePlaneQuad_neg_laplacian {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    wholePlaneQuadInternal (R + 1) (fun x => -latticeLaplacianInternal g x) =
      latticeDirichletInternal g := by
  have hf : SupportedInBox (R + 1) fun x => -latticeLaplacianInternal g x := fun x hx => by
    simp [hg.laplacian x hx]
  rw [← freeQuad_box_eq (n := R + 1) le_rfl hf]
  exact freeQuad_neg_laplacian hg subset_rfl

/-- **J p. 567, field spectral bound, every free limit**: for every thermodynamic limit `Γ` of the
free field two-point functions, `T_R(k) ≥ (1 - δ) κ (D(𝟙_B cos) + D(𝟙_B sin))`, and
`(D(𝟙_B cos) + D(𝟙_B sin))/(2R+1)² → ε(k)`. Hence
`liminf_R T_R(k)/((2R+1)² ε(k)²) ≥ (1 - δ) κ / ε(k) = (1 - δ) κ Ĉ(k)`. -/
theorem free_field_spectral_lower {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {Γ : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hΓ : ∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop (𝓝 (Γ x y)))
    (k : ℝ × ℝ) :
    (∀ R : ℕ, (1 - δ) * κ * (latticeDirichletInternal (boxCosInternal R k) +
        latticeDirichletInternal (boxSinInternal R k)) ≤ fieldFourierInternal Γ R k) ∧
    Tendsto (fun R : ℕ => (latticeDirichletInternal (boxCosInternal R k) +
        latticeDirichletInternal (boxSinInternal R k)) / ((2 * R + 1 : ℕ) : ℝ) ^ 2) atTop
      (𝓝 (latticeSymbolInternal k)) := by
  refine ⟨fun R => ?_, tendsto_dirichlet_boxFourier k⟩
  have hc := boxCos_supported R k
  have hs := boxSin_supported R k
  have hfc : SupportedInBox (R + 1) fun x => -latticeLaplacianInternal (boxCosInternal R k) x :=
    fun x hx => by simp [hc.laplacian x hx]
  have hfs : SupportedInBox (R + 1) fun x => -latticeLaplacianInternal (boxSinInternal R k) x :=
    fun x hx => by simp [hs.laplacian x hx]
  have h0 : ∀ {g : ℤ × ℤ → ℝ}, SupportedInBox R g →
      ∑ x ∈ boxInternal (R + 1), -latticeLaplacianInternal g x = 0 := fun hg => by
    rw [Finset.sum_neg_distrib, sum_laplacian_eq_zero hg subset_rfl, neg_zero]
  have Ac := (free_infinite_theoremA h κ hκ hκκ₀ z hz hzκ hφ hΓ hfc (h0 hc)).2.1
  have As := (free_infinite_theoremA h κ hκ hκκ₀ z hz hzκ hφ hΓ hfs (h0 hs)).2.1
  rw [wholePlaneQuad_neg_laplacian hc] at Ac
  rw [wholePlaneQuad_neg_laplacian hs] at As
  unfold fieldFourierInternal
  linarith

/-- **FS81 (1.17) in Fourier form and J p. 567 in a translation-invariant limit.** If the charge
two-point function of a joint free thermodynamic limit is translation invariant,
`S(x,y) = s(y-x)`, with `∑ (1+|z|²)|s(z)| < ∞`, then for `ε(k) ≠ 0` the field structure factor
`T_R(k)/((2R+1)² ε(k)²)` converges to `S_φ(k) = κ Ĉ(k) - κ² Ĉ(k)² ŝ(k)` (`Ĉ = 1/ε`), and
`S_φ(k) ≥ (1 - δ) κ Ĉ(k)`. -/
theorem free_field_spectral_density {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (hδ : 0 ≤ δ) (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {Γ S : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hΓ : ∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop (𝓝 (Γ x y)))
    (hS : ∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
      (𝓝 (S x y)))
    {s : ℤ × ℤ → ℝ} (hts : ∀ x y, S x y = s (y - x))
    (hs2 : Summable fun w : ℤ × ℤ => (1 + (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2) * |s w|)
    (k : ℝ × ℝ) (hk : latticeSymbolInternal k ≠ 0) :
    Tendsto (fun R : ℕ => fieldFourierInternal Γ R k /
        (((2 * R + 1 : ℕ) : ℝ) ^ 2 * latticeSymbolInternal k ^ 2)) atTop
      (𝓝 (κ / latticeSymbolInternal k - κ ^ 2 *
        (∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2)) / latticeSymbolInternal k ^ 2)) ∧
    (1 - δ) * κ / latticeSymbolInternal k ≤ κ / latticeSymbolInternal k - κ ^ 2 *
        (∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2)) / latticeSymbolInternal k ^ 2 := by
  have habs : Summable fun w => |s w| := Summable.of_nonneg_of_le (fun w => abs_nonneg _)
    (fun w => by nlinarith [abs_nonneg (s w), sq_nonneg (w.1 : ℝ), sq_nonneg (w.2 : ℝ)]) hs2
  set ε := latticeSymbolInternal k
  have hεpos : 0 < ε := lt_of_le_of_ne (latticeSymbol_nonneg k) (Ne.symm hk)
  have hid : ∀ R : ℕ, fieldFourierInternal Γ R k =
      κ * (latticeDirichletInternal (boxCosInternal R k) + latticeDirichletInternal (boxSinInternal R k)) -
        κ ^ 2 * ((∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
            boxCosInternal R k x * boxCosInternal R k y * s (y - x)) +
          (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
            boxSinInternal R k x * boxSinInternal R k y * s (y - x))) := by
    intro R
    unfold fieldFourierInternal
    rw [free_infinite_secondMoment_neg_laplacian κ z hφ hΓ hS (boxCos_supported R k),
      free_infinite_secondMoment_neg_laplacian κ z hφ hΓ hS (boxSin_supported R k)]
    simp_rw [hts]
    ring
  have hlim := ((tendsto_dirichlet_boxFourier k).const_mul κ).sub
    ((tendsto_boxFourier_quadratic s habs k).const_mul (κ ^ 2))
  have hlim' := hlim.div_const (ε ^ 2)
  refine ⟨?_, ?_⟩
  · refine (hlim'.congr' (Eventually.of_forall fun R => ?_)).trans ?_
    · rw [hid R]
      have : ((2 * R + 1 : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp
    · rw [show (κ * ε - κ ^ 2 * ∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2)) / ε ^ 2 =
        κ / ε - κ ^ 2 * (∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2)) / ε ^ 2 by
          field_simp]
  · have hb := ((free_sumRule h hδ κ hκ hκκ₀ z hz hzκ hφ hS hts hs2).1 k).2
    set ŝ := ∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2)
    have key : κ ^ 2 * ŝ ≤ δ * κ * ε :=
      calc κ ^ 2 * ŝ ≤ κ ^ 2 * (δ / κ * ε) := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = δ * κ * ε := by field_simp
    have e : κ / ε - κ ^ 2 * ŝ / ε ^ 2 - (1 - δ) * κ / ε = (δ * κ * ε - κ ^ 2 * ŝ) / ε ^ 2 := by
      field_simp; ring
    have : 0 ≤ (δ * κ * ε - κ ^ 2 * ŝ) / ε ^ 2 := div_nonneg (by linarith) (by positivity)
    linarith

end FroehlichSpencer.BKT.Coulomb
