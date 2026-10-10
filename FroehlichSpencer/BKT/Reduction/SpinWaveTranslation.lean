/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.ComplexCharacteristic
public import FroehlichSpencer.BKT.SpinWaves.Defs
public import FroehlichSpencer.BKT.Surface.GFFLaw
import FroehlichSpencer.BKT.Bridge.GFFMeasure
import FroehlichSpencer.BKT.FiniteGraph.Laplacian
import FroehlichSpencer.BKT.Surface.GFFWellDefined

/-!
# Step 3 of KP §2.3: complex translation by orthogonal spin waves

Let `ϱ_i`, `i ∈ ι`, be neutral real charges and `a_i` real spin waves with
`⟨a_i, ϱ_{i'}⟩ = 0` and `⟨a_i, Δ a_{i'}⟩ = 0` for `i ≠ i'`.

Then
`∫ ∏_i [1 + K_i cos(⟨φ, ϱ_i⟩ + s_i)] dμ = ∫ ∏_i [1 + z_i cos(⟨φ, ϱ_i + β Δ a_i⟩ + s_i)] dμ`,
`z_i = K_i e^{-E_β(a_i, ϱ_i)}`, for the GFF `μ = μ^GFF_{β,Λ,v}`.

The proof follows :

1. *Finite expansion (2.18).* `1 + k cos t = ∑_{n ∈ {-1,0,1}} c(k, n) e^{int}` with
   `c(k, 0) = 1`, `c(k, ±1) = k/2`; multiply out over `ι` (`prod_one_add_mul_cos_eq_sum`).
2. *Integration.* Each term is a constant times the characteristic function
   `χ(τ) = ∫ e^{i⟨φ, τ⟩} dμ` at `τ_n = ∑_i n_i ϱ_i` (`gffLaw_integral_prod_one_add_mul_cos`).
3. *Translation (2.19)* (`gff_complex_translation`) at `a_n = ∑_i n_i a_i`.
4. *Additivity.* By orthogonality, `E_β(a_n, τ_n) = ∑_i n_i² E_β(a_i, ϱ_i)`
   (`gffTranslationEnergy_signed_sum`).
5. *Resummation (2.20).* `c(K_i, n_i) e^{-n_i² E_i} = c(z_i, n_i)`, and
   `τ_n + β Δ a_n = ∑_i n_i (ϱ_i + β Δ a_i)`; step 2 read backwards gives the right side.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Reduction

open MeasureTheory

universe u v

/-! ## The finite sign expansion (2.18) -/

/-- The signs `{-1, 0, 1}` of KP (2.18). -/
def signSet : Finset ℤ := {-1, 0, 1}

/-- The coefficient `(k/2)^{|n|}` of the sign `n ∈ {-1, 0, 1}` in KP (2.18). -/
def signCoeff (k : ℝ) (n : ℤ) : ℂ := if n = 0 then 1 else (k : ℂ) / 2

theorem mem_signSet {n : ℤ} : n ∈ signSet ↔ n = -1 ∨ n = 0 ∨ n = 1 := by
  simp [signSet]

/-- `1 + k cos t = ∑_{n ∈ {-1,0,1}} c(k, n) e^{int}`. -/
theorem one_add_mul_cos_eq_sum (k t : ℝ) :
    ((1 + k * Real.cos t : ℝ) : ℂ) =
      ∑ n ∈ signSet, signCoeff k n * Complex.exp (Complex.I * ((n : ℂ) * t)) := by
  have hcos : Complex.cos (t : ℂ) =
      (Complex.exp (Complex.I * t) + Complex.exp (Complex.I * (-t))) / 2 := by
    rw [mul_comm Complex.I, mul_comm Complex.I, Complex.exp_mul_I, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  simp only [signSet, signCoeff]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [hcos]
  simp only [zero_mul, mul_zero, Complex.exp_zero, one_mul, neg_one_mul, mul_neg]
  ring

/-- The product over a finite index of `1 + k_i cos θ_i`, multiplied out over sign vectors. -/
theorem prod_one_add_mul_cos_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (k θ : ι → ℝ) :
    ((∏ i, (1 + k i * Real.cos (θ i)) : ℝ) : ℂ) =
      ∑ n ∈ Fintype.piFinset fun _ : ι => signSet,
        (∏ i, signCoeff (k i) (n i)) * Complex.exp (Complex.I * ∑ i, (n i : ℂ) * θ i) := by
  rw [Complex.ofReal_prod]
  simp_rw [one_add_mul_cos_eq_sum]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.prod_mul_distrib, Finset.mul_sum, Complex.exp_sum]

/-! ## Integration against the GFF -/

section Integration

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]

/-- The complex character `φ ↦ e^{i⟨φ, τ⟩}` of a real field `τ`. -/
def gffCharacter (τ : V → ℝ) (φ : V → ℝ) : ℂ :=
  Complex.exp (Complex.I * ∑ j, (φ j : ℂ) * (τ j : ℂ))

omit [DecidableEq V] in
theorem norm_gffCharacter (τ φ : V → ℝ) : ‖gffCharacter τ φ‖ = 1 := by
  have h : Complex.I * ∑ j, (φ j : ℂ) * (τ j : ℂ) = ((∑ j, φ j * τ j : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [gffCharacter, h, Complex.norm_exp_ofReal_mul_I]

omit [DecidableEq V] in
theorem continuous_gffCharacter (τ : V → ℝ) : Continuous (gffCharacter τ) := by
  unfold gffCharacter
  fun_prop

omit [DecidableEq V] in
theorem integrable_gffCharacter (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] (τ : V → ℝ) :
    Integrable (gffCharacter τ) μ :=
  Integrable.of_bound (continuous_gffCharacter τ).aestronglyMeasurable 1
    (ae_of_all _ fun φ => (norm_gffCharacter τ φ).le)

omit [DecidableEq V] in
/-- KP (2.18) integrated: the integral of `∏_i [1 + k_i cos(⟨φ, w_i⟩ + s_i)]` is the finite sum
over sign vectors `n` of `∏_i c(k_i, n_i) · e^{i ∑_i n_i s_i} · χ(∑_i n_i w_i)`. -/
theorem integral_prod_one_add_mul_cos (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℝ) (w : ι → V → ℝ) (s : ι → ℝ) :
    ((∫ φ, ∏ i, (1 + k i * Real.cos (∑ j, φ j * w i j + s i)) ∂μ : ℝ) : ℂ) =
      ∑ n ∈ Fintype.piFinset fun _ : ι => signSet,
        (∏ i, signCoeff (k i) (n i)) * Complex.exp (Complex.I * ∑ i, (n i : ℂ) * s i) *
          ∫ φ, gffCharacter (fun j => ∑ i, (n i : ℝ) * w i j) φ ∂μ := by
  rw [← integral_complex_ofReal]
  have hpoint : ∀ φ : V → ℝ,
      ((∏ i, (1 + k i * Real.cos (∑ j, φ j * w i j + s i)) : ℝ) : ℂ) =
        ∑ n ∈ Fintype.piFinset fun _ : ι => signSet,
          (∏ i, signCoeff (k i) (n i)) * Complex.exp (Complex.I * ∑ i, (n i : ℂ) * s i) *
            gffCharacter (fun j => ∑ i, (n i : ℝ) * w i j) φ := by
    intro φ
    rw [prod_one_add_mul_cos_eq_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have harg : Complex.I * ∑ i, (n i : ℂ) * ((∑ j, φ j * w i j + s i : ℝ) : ℂ) =
        Complex.I * ∑ i, (n i : ℂ) * s i +
          Complex.I * ∑ j, (φ j : ℂ) * ((∑ i, (n i : ℝ) * w i j : ℝ) : ℂ) := by
      push_cast
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [add_comm, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [gffCharacter, harg, Complex.exp_add, mul_assoc]
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun n _ => (integrable_gffCharacter μ _).const_mul _]
  simp_rw [integral_const_mul]

omit [DecidableEq V] in
/-- A finite product of factors `1 + k_i cos θ_i(φ)` with continuous phases is integrable for
every finite measure. -/
theorem integrable_prod_one_add_mul_cos (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] {ι : Type*}
    (S : Finset ι) (k : ι → ℝ) (θ : ι → (V → ℝ) → ℝ) (hθ : ∀ i, Continuous (θ i)) :
    Integrable (fun φ => ∏ i ∈ S, (1 + k i * Real.cos (θ i φ))) μ := by
  refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) (∏ i ∈ S, (1 + |k i|))
    (ae_of_all _ fun φ => ?_)
  · exact continuous_finsetProd S fun i _ => continuous_const.add
      (continuous_const.mul (Real.continuous_cos.comp (hθ i)))
  · rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
    calc |1 + k i * Real.cos (θ i φ)| ≤ |(1 : ℝ)| + |k i * Real.cos (θ i φ)| := abs_add_le _ _
      _ ≤ 1 + |k i| := by
        rw [abs_one, abs_mul]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

end Integration

/-! ## Energy additivity under orthogonality -/

section Energy

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]

omit [DecidableEq V] in
theorem pairing_sum_sum {ι : Type*} [Fintype ι] (x y : ι → ℝ) (f g : ι → V → ℝ) :
    Multigraph.pairing (fun j => ∑ i, x i * f i j) (fun j => ∑ i, y i * g i j) =
      ∑ i, ∑ i', x i * y i' * Multigraph.pairing (f i) (g i') := by
  unfold Multigraph.pairing
  calc ∑ j, (∑ i, x i * f i j) * (∑ i', y i' * g i' j)
      = ∑ j, ∑ i, ∑ i', x i * y i' * (f i j * g i' j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        ring
    _ = ∑ i, ∑ i', ∑ j, x i * y i' * (f i j * g i' j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.mul_sum]

omit [DecidableEq V] in
theorem pairing_sum_sum_of_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℝ)
    (f g : ι → V → ℝ) (horth : ∀ i i', i ≠ i' → Multigraph.pairing (f i) (g i') = 0) :
    Multigraph.pairing (fun j => ∑ i, x i * f i j) (fun j => ∑ i, y i * g i j) =
      ∑ i, x i * y i * Multigraph.pairing (f i) (g i) := by
  rw [pairing_sum_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun i' _ hne => by rw [horth i i' hne.symm, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)]

omit [Fintype V] in
theorem laplacian_sum (G : Multigraph V E) {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (f : ι → V → ℝ) :
    G.laplacian (fun j => ∑ i, x i * f i j) = fun j => ∑ i, x i * G.laplacian (f i) j := by
  have hsum : (fun j => ∑ i, x i * f i j) = ∑ i, x i • f i := by
    funext j
    simp [Finset.sum_apply, smul_eq_mul]
  have h := congrArg (G.laplacianₗ ℝ) hsum
  simp only [map_sum, map_smul] at h
  funext j
  have hj := congrFun h j
  simpa [Finset.sum_apply, smul_eq_mul] using hj

/-- KP §2.3.3, p. 13: under the orthogonality relations of the spin waves,
`E_β(a_n, τ_n) = ∑_i n_i² E_β(a_i, ϱ_i)` for `a_n = ∑_i n_i a_i`, `τ_n = ∑_i n_i ϱ_i`. -/
theorem gffTranslationEnergy_signed_sum (G : Multigraph V E) (β : ℝ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : ι → ℝ) (a ϱ : ι → V → ℝ)
    (horth₁ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (ϱ i') = 0)
    (horth₂ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (G.laplacian (a i')) = 0) :
    gffTranslationEnergy G β (fun j => ∑ i, x i * a i j) (fun j => ∑ i, x i * ϱ i j) =
      ∑ i, x i ^ 2 * gffTranslationEnergy G β (a i) (ϱ i) := by
  have hlin := pairing_sum_sum_of_orthogonal x x a ϱ horth₁
  have hquad : G.energy (fun j => ∑ i, x i * a i j) = ∑ i, x i ^ 2 * G.energy (a i) := by
    rw [Multigraph.energy_eq_neg_pairing_laplacian, laplacian_sum,
      pairing_sum_sum_of_orthogonal x x a (fun i => G.laplacian (a i)) horth₂]
    simp only [Multigraph.energy_eq_neg_pairing_laplacian G (a _)]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [gffTranslationEnergy]
  rw [hlin, hquad, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Energy

/-! ## The translated identity -/

section Translation

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]

/--
KP (2.19) for the GFF law.
-/
theorem gffLaw_integral_gffCharacter_translation (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (a τ : V → ℝ)
    (hτ : ∑ j, τ j = 0) :
    ∫ φ, gffCharacter τ φ ∂gffLaw G hG β hβ v =
      Complex.exp (-(gffTranslationEnergy G β a τ : ℂ)) *
        ∫ φ, gffCharacter (fun j => τ j + β * G.laplacian a j) φ ∂gffLaw G hG β hβ v := by
  rw [gffLaw_eq_gffMeasure]
  have h := gff_complex_translation G hG β hβ v a τ hτ
  simp only [Multigraph.pairing] at h
  simp only [gffCharacter, Complex.ofReal_add, Complex.ofReal_mul]
  exact h

theorem signCoeff_mul_exp {k e : ℝ} {n : ℤ} (hn : n ∈ signSet) :
    signCoeff k n * Complex.exp (-(((n : ℝ) ^ 2 * e : ℝ) : ℂ)) =
      signCoeff (k * Real.exp (-e)) n := by
  rcases mem_signSet.mp hn with rfl | rfl | rfl <;>
    simp [signCoeff, Complex.ofReal_exp] <;> ring


theorem gffLaw_integral_prod_spinWave_translation (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ϱ : ι → V → ℝ) (hneutral : ∀ i, ∑ j, ϱ i j = 0) (K s : ι → ℝ)
    (a : ι → V → ℝ)
    (horth₁ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (ϱ i') = 0)
    (horth₂ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (G.laplacian (a i')) = 0) :
    ∫ φ, ∏ i, (1 + K i * Real.cos (∑ j, φ j * ϱ i j + s i)) ∂gffLaw G hG β hβ v =
      ∫ φ, ∏ i, (1 + K i * Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)) *
          Real.cos (∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j) + s i))
        ∂gffLaw G hG β hβ v := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  apply Complex.ofReal_injective
  rw [integral_prod_one_add_mul_cos, integral_prod_one_add_mul_cos]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : ∀ i, n i ∈ signSet := Fintype.mem_piFinset.mp hn
  set Ei : ι → ℝ := fun i => gffTranslationEnergy G β (a i) (ϱ i) with hEi
  have hτ : ∑ j, (∑ i, (n i : ℝ) * ϱ i j) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hneutral, mul_zero, Finset.sum_const_zero]
  rw [gffLaw_integral_gffCharacter_translation G hG β hβ v (fun j => ∑ i, (n i : ℝ) * a i j)
    _ hτ, gffTranslationEnergy_signed_sum G β _ a ϱ horth₁ horth₂]
  have hfield : (fun j => ∑ i, (n i : ℝ) * ϱ i j +
      β * G.laplacian (fun j => ∑ i, (n i : ℝ) * a i j) j) =
      fun j => ∑ i, (n i : ℝ) * (ϱ i j + β * G.laplacian (a i) j) := by
    rw [laplacian_sum]
    funext j
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfield]
  have hcoeff : (∏ i, signCoeff (K i) (n i)) *
      Complex.exp (-((∑ i, (n i : ℝ) ^ 2 * Ei i : ℝ) : ℂ)) =
      ∏ i, signCoeff (K i * Real.exp (-Ei i)) (n i) := by
    rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib, Complex.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => signCoeff_mul_exp (hn' i)
  rw [← hcoeff]
  ring

/-- KP §2.3.3 for a finite family of neutral integer densities `𝒩₀` with spin waves `a ϱ`:
`z(ϱ) = K(ϱ) e^{-E_β(a_ϱ, ϱ)}` (KP p. 13, after (2.20)). -/
theorem gffLaw_integral_prod_spinWave_translation_finset (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (N₀ : Finset (V → ℤ))
    (hneutral : ∀ ϱ ∈ N₀, ∑ j, ϱ j = 0) (K : (V → ℤ) → ℝ) (σ : V → ℝ)
    (a : (V → ℤ) → V → ℝ)
    (horth₁ : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' →
      Multigraph.pairing (a ϱ) (fun j => (ϱ' j : ℝ)) = 0)
    (horth₂ : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' →
      Multigraph.pairing (a ϱ) (G.laplacian (a ϱ')) = 0) :
    ∫ φ, ∏ ϱ ∈ N₀, (1 + K ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ)))
        ∂gffLaw G hG β hβ v =
      ∫ φ, ∏ ϱ ∈ N₀, (1 + K ϱ * Real.exp (-SpinWaves.energyFunctional G β (a ϱ) ϱ) *
          Real.cos (∑ j, φ j * ((ϱ j : ℝ) + β * G.laplacian (a ϱ) j) +
            ∑ j, σ j * (ϱ j : ℝ)))
        ∂gffLaw G hG β hβ v := by
  classical
  simp_rw [← Finset.prod_coe_sort N₀]
  exact gffLaw_integral_prod_spinWave_translation G hG β hβ v
    (fun ϱ : N₀ => fun j => ((ϱ : V → ℤ) j : ℝ))
    (fun ϱ => by exact_mod_cast hneutral ϱ ϱ.property) (fun ϱ => K ϱ)
    (fun ϱ => ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ)) (fun ϱ => a ϱ)
    (fun ϱ ϱ' hne => horth₁ ϱ ϱ.property ϱ' ϱ'.property fun h => hne (Subtype.ext h))
    (fun ϱ ϱ' hne => horth₂ ϱ ϱ.property ϱ' ϱ'.property fun h => hne (Subtype.ext h))

end Translation

end FroehlichSpencer.BKT.Reduction

end
