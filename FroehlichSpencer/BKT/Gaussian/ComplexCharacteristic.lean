/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.ComplexTranslation
public import FroehlichSpencer.BKT.Gaussian.ExponentialMoment
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.ComplexMGF

/-!
# The characteristic function and complex translation identity for the GFF

The zero-sum linear statistics of the finite-volume Gaussian free field have
Gaussian characteristic functions. KP (2.19) then follows by applying this
formula before and after adding a Laplacian.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace FroehlichSpencer.BKT

universe u v

variable {V : Type u} {E : Type v}

private theorem pairing_add_right [Fintype V] (f g h : V → ℝ) :
    Multigraph.pairing f (g + h) = Multigraph.pairing f g + Multigraph.pairing f h := by
  unfold Multigraph.pairing
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem pairing_sub_right [Fintype V] (f g h : V → ℝ) :
    Multigraph.pairing f (g - h) = Multigraph.pairing f g - Multigraph.pairing f h := by
  unfold Multigraph.pairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.sub_apply]
  ring

private theorem pairing_const_right [Fintype V] (f : V → ℝ) (c : ℝ) :
    Multigraph.pairing f (fun _ => c) = c * ∑ j, f j := by
  unfold Multigraph.pairing
  change (∑ j, f j * c) = c * ∑ j, f j
  calc
    (∑ j, f j * c) = ∑ j, c * f j := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ j, f j := by rw [Finset.mul_sum]

private theorem pairing_complex_cast [Fintype V] (φ f : V → ℝ) :
    Multigraph.pairing (R := ℂ) (fun j => (φ j : ℂ)) (fun j => (f j : ℂ)) =
      (Multigraph.pairing (R := ℝ) φ f : ℂ) := by
  unfold Multigraph.pairing
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]

/-- The characteristic function of a zero-sum linear statistic of the
rooted finite-volume GFF, computed from its real exponential moments. -/
theorem gff_characteristic_function (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (τ : V → ℝ) (hτ : ∑ j, τ j = 0) :
    (∫ φ, Complex.exp (Complex.I *
      (Multigraph.pairing (R := ℝ) (φ : V → ℝ) τ : ℂ))
      ∂gffMeasure G hG β hβ root) =
      Complex.exp (-(Multigraph.pairing τ (-G.greenOp hG τ)) / (2 * β)) := by
  let μ := gffMeasure G hG β hβ root
  let X : (V → ℝ) → ℝ := fun φ => Multigraph.pairing φ τ
  let Q := Multigraph.pairing τ (-G.greenOp hG τ)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact G.pairing_greenOp_nonneg hG τ hτ
  let variance : ℝ≥0 := ⟨Q / β, div_nonneg hQ hβ.le⟩
  have hvariance : (variance : ℝ) = Q / β := rfl
  have hmgf (t : ℝ) :
      ProbabilityTheory.mgf X μ t = Real.exp (t ^ 2 * Q / (2 * β)) := by
    let f : V → ℝ := t • τ
    have hf : ∑ j, f j = 0 := by
      dsimp [f]
      simp only [← Finset.mul_sum, hτ, mul_zero]
    have hm := gff_exponential_moment G hG β hβ f hf root
    have hgreen : -G.greenOp hG f = t • (-G.greenOp hG τ) := by
      change -G.greenOp hG (t • τ) = t • (-G.greenOp hG τ)
      rw [(G.greenOp hG).map_smul]
      exact (smul_neg t (G.greenOp hG τ)).symm
    have hQf : Multigraph.pairing f (-G.greenOp hG f) = t ^ 2 * Q := by
      change Multigraph.pairing (t • τ) (-G.greenOp hG (t • τ)) =
        t ^ 2 * Multigraph.pairing τ (-G.greenOp hG τ)
      rw [hgreen, pairing_smul_left, pairing_smul_right]
      ring
    calc
      ProbabilityTheory.mgf X μ t =
          ∫ φ, Real.exp (Multigraph.pairing φ f) ∂μ := by
            unfold ProbabilityTheory.mgf X
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun φ => by
              dsimp [f]
              rw [pairing_smul_right]
      _ = Real.exp (Multigraph.pairing f (-G.greenOp hG f) / (2 * β)) := hm.2
      _ = Real.exp (t ^ 2 * Q / (2 * β)) := by rw [hQf]
  have hmgfEq : ProbabilityTheory.mgf X μ =
      ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 variance) := by
    ext t
    rw [ProbabilityTheory.mgf_id_gaussianReal]
    rw [hmgf t]
    rw [hvariance]
    congr 1
    ring
  have hXint (t : ℝ) : Integrable (fun φ => Real.exp (t * X φ)) μ := by
    let f : V → ℝ := t • τ
    have hf : ∑ j, f j = 0 := by
      dsimp [f]
      simp only [← Finset.mul_sum, hτ, mul_zero]
    have hm := gff_exponential_moment G hG β hβ f hf root
    apply hm.1.congr
    filter_upwards with φ
    dsimp [X, f]
    rw [pairing_smul_right]
  have hset : ProbabilityTheory.integrableExpSet X μ = Set.univ := by
    ext t
    simp only [ProbabilityTheory.integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ,
      iff_true]
    exact hXint t
  have hXmeas : AEMeasurable X μ :=
    aemeasurable_of_mem_interior_integrableExpSet (v := (0 : ℝ)) (by
      rw [hset]
      simp)
  have hstrip : (Complex.I).re ∈
      interior (ProbabilityTheory.integrableExpSet X μ) := by
    rw [hset]
    simp
  have hcomplex := (ProbabilityTheory.eqOn_complexMGF_of_mgf hmgfEq) hstrip
  have hcharX := ProbabilityTheory.complexMGF_mul_I hXmeas 1
  have hcharGauss := ProbabilityTheory.complexMGF_id_mul_I
    (μ := ProbabilityTheory.gaussianReal 0 variance) 1
  have hchar : charFun (μ.map X) 1 =
      Complex.exp ((-Q) / (2 * β)) := by
    have hcommon :
        ProbabilityTheory.complexMGF X μ (1 * Complex.I) =
          ProbabilityTheory.complexMGF id
            (ProbabilityTheory.gaussianReal 0 variance) (1 * Complex.I) := by
      simpa using hcomplex
    have h := hcharX.symm.trans (hcommon.trans hcharGauss)
    rw [ProbabilityTheory.charFun_gaussianReal] at h
    have hbase : charFun (μ.map X) 1 =
        Complex.exp (-((Q : ℂ) / (β : ℂ) / 2)) := by
      simpa [Q, hvariance] using h
    have hden : -((Q : ℂ) / (β : ℂ) / 2) =
        (-(Q : ℂ)) / (2 * (β : ℂ)) := by
      field_simp [ne_of_gt hβ]
    have h' : charFun (μ.map X) 1 =
        Complex.exp ((-(Q : ℂ)) / (2 * (β : ℂ))) := by
      simpa only [hden] using hbase
    simpa [Q] using h'
  calc
    (∫ φ, Complex.exp (Complex.I *
        (Multigraph.pairing (R := ℝ) φ τ : ℂ)) ∂μ) =
        ProbabilityTheory.complexMGF X μ Complex.I := by
          unfold ProbabilityTheory.complexMGF X
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun _ => rfl
    _ = charFun (μ.map X) 1 := by
          simpa using hcharX
    _ = Complex.exp ((-Multigraph.pairing τ (-G.greenOp hG τ)) / (2 * β)) := by
          simpa [Q] using hchar

private theorem green_quadratic_laplacian_add (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (a τ : V → ℝ) (hτ : ∑ j, τ j = 0) (β : ℝ) :
    Multigraph.pairing (τ + β • G.laplacian a)
        (-G.greenOp hG (τ + β • G.laplacian a)) =
      Multigraph.pairing τ (-G.greenOp hG τ) -
        2 * β * Multigraph.pairing a τ + β ^ 2 * G.energy a := by
  let p : V → ℝ := (zeroSumProjection hG.nonempty a : V → ℝ)
  have hp : p = a - fun _ => vertexMean V a := by
    funext j
    simp [p]
  have hpsum : ∑ j, G.laplacian a j = 0 := G.sum_laplacian_eq_zero a
  have hΔp : G.laplacian p = G.laplacian a := by
    rw [hp]
    have hlin := (G.laplacianₗ ℝ).map_sub a (fun _ => vertexMean V a)
    have hconst : (G.laplacianₗ ℝ) (fun _ => vertexMean V a) = 0 := by
      change G.laplacian (fun _ => vertexMean V a) = 0
      exact G.laplacian_const _
    change (G.laplacianₗ ℝ) (a - fun _ => vertexMean V a) =
      (G.laplacianₗ ℝ) a
    rw [hlin, hconst, sub_zero]
  have hpSum : ∑ j, p j = 0 := by
    change ∑ j, (zeroSumProjection hG.nonempty a).val j = 0
    exact (zeroSumProjection hG.nonempty a).property
  have hgreenΔ : G.greenOp hG (G.laplacian a) = p := by
    rw [← hΔp]
    exact G.greenOp_laplacian_of_sum_eq_zero hG p hpSum
  have hcross₁ : Multigraph.pairing τ (-G.greenOp hG (G.laplacian a)) =
      -Multigraph.pairing a τ := by
    rw [pairing_neg_right, hgreenΔ, hp, pairing_sub_right,
      pairing_const_right, hτ, mul_zero, sub_zero, Multigraph.pairing_comm]
  have hcross₂ : Multigraph.pairing (G.laplacian a) (-G.greenOp hG τ) =
      -Multigraph.pairing a τ := by
    rw [pairing_neg_right, ← G.pairing_laplacian_comm a (G.greenOp hG τ),
      G.laplacian_greenOp_of_sum_eq_zero hG τ hτ]
  have hquadΔ : Multigraph.pairing (G.laplacian a)
      (-G.greenOp hG (G.laplacian a)) = G.energy a := by
    rw [pairing_neg_right, hgreenΔ, hp, Multigraph.pairing_comm, pairing_sub_left,
      pairing_const_left, hpsum, mul_zero, sub_zero]
    exact (G.energy_eq_neg_pairing_laplacian a).symm
  have hgreenAdd : -G.greenOp hG (τ + β • G.laplacian a) =
      -G.greenOp hG τ + β • (-G.greenOp hG (G.laplacian a)) := by
    rw [(G.greenOp hG).map_add, (G.greenOp hG).map_smul]
    ext j
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hgreenAdd, pairing_add_left, pairing_add_right, pairing_add_right]
  simp only [pairing_smul_left, pairing_smul_right]
  rw [hcross₁, hcross₂, hquadΔ]
  ring

/-- KP (2.19): translating the complex center of a finite-volume GFF by a
real field changes a neutral characteristic function by the exponential of
the KP energy. -/
theorem gff_complex_translation (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : Multigraph.Connected G)
    (β : ℝ) (hβ : 0 < β) (root : V) (a τ : V → ℝ)
    (hτ : ∑ j, τ j = 0) :
    (∫ φ, Complex.exp (Complex.I *
      Multigraph.pairing (fun j => (φ j : ℂ)) (fun j => (τ j : ℂ)))
      ∂gffMeasure G hG β hβ root) =
      Complex.exp (-(gffTranslationEnergy G β a τ)) *
        (∫ φ, Complex.exp (Complex.I *
          Multigraph.pairing (fun j => (φ j : ℂ))
            (fun j => ((τ j + β * G.laplacian a j) : ℂ)))
          ∂gffMeasure G hG β hβ root) := by
  let τ' : V → ℝ := τ + β • G.laplacian a
  have hτ' : ∑ j, τ' j = 0 := by
    dsimp [τ']
    rw [Finset.sum_add_distrib, hτ]
    simp only [← Finset.mul_sum, G.sum_laplacian_eq_zero, mul_zero, zero_add]
  have hchar := gff_characteristic_function G hG β hβ root τ hτ
  have hquad := green_quadratic_laplacian_add G hG a τ hτ β
  have hquad' : Multigraph.pairing τ' (-G.greenOp hG τ') =
      Multigraph.pairing τ (-G.greenOp hG τ) -
        2 * β * Multigraph.pairing a τ + β ^ 2 * G.energy a := by
    simpa [τ'] using hquad
  have hreal :
      -(Multigraph.pairing τ (-G.greenOp hG τ)) / (2 * β) =
        -gffTranslationEnergy G β a τ -
          (Multigraph.pairing τ' (-G.greenOp hG τ')) / (2 * β) := by
    rw [hquad']
    dsimp [gffTranslationEnergy]
    field_simp [ne_of_gt hβ]
    ring_nf
  have hleft :
      (∫ φ, Complex.exp (Complex.I *
        Multigraph.pairing (fun j => (φ j : ℂ)) (fun j => (τ j : ℂ)))
        ∂gffMeasure G hG β hβ root) =
        Complex.exp (-(Multigraph.pairing τ (-G.greenOp hG τ)) / (2 * β)) := by
    convert hchar using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ =>
      congrArg (fun z : ℂ => Complex.exp (Complex.I * z))
        (pairing_complex_cast φ τ)
  have hright :
      (∫ φ, Complex.exp (Complex.I *
        Multigraph.pairing (fun j => (φ j : ℂ)) (fun j => (τ' j : ℂ)))
        ∂gffMeasure G hG β hβ root) =
        Complex.exp (-(Multigraph.pairing τ' (-G.greenOp hG τ')) / (2 * β)) := by
    convert gff_characteristic_function G hG β hβ root τ' hτ' using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ =>
      congrArg (fun z : ℂ => Complex.exp (Complex.I * z))
        (pairing_complex_cast φ τ')
  rw [hleft]
  have htarget :
      (∫ φ, Complex.exp (Complex.I *
        Multigraph.pairing (fun j => (φ j : ℂ))
          (fun j => ((τ j + β * G.laplacian a j) : ℂ)))
        ∂gffMeasure G hG β hβ root) =
      ∫ φ, Complex.exp (Complex.I *
        Multigraph.pairing (fun j => (φ j : ℂ)) (fun j => (τ' j : ℂ)))
        ∂gffMeasure G hG β hβ root := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ => by
      have hsum : (fun j => (τ j + β * G.laplacian a j : ℂ)) =
          (fun j => (τ' j : ℂ)) := by
        funext j
        simp [τ', Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
          Complex.ofReal_mul]
      change Complex.exp (Complex.I *
          Multigraph.pairing (R := ℂ) (fun j => (φ j : ℂ))
            (fun j => ((τ j + β * G.laplacian a j : ℂ)))) =
        Complex.exp (Complex.I * Multigraph.pairing (R := ℂ)
          (fun j => (φ j : ℂ)) (fun j => (τ' j : ℂ)))
      rw [hsum]
  rw [htarget, hright]
  have hreal' :
      -(Multigraph.pairing τ (-G.greenOp hG τ)) / (2 * β) =
        -gffTranslationEnergy G β a τ +
          -(Multigraph.pairing τ' (-G.greenOp hG τ')) / (2 * β) := by
    rw [hquad']
    dsimp [gffTranslationEnergy]
    field_simp [ne_of_gt hβ]
    ring
  have hrealC :
      -(Multigraph.pairing (R := ℝ) τ (-G.greenOp hG τ) : ℂ) / (2 * β) =
        -(gffTranslationEnergy G β a τ : ℂ) +
          -(Multigraph.pairing (R := ℝ) τ' (-G.greenOp hG τ') : ℂ) /
            (2 * β) := by
    exact_mod_cast hreal'
  calc
    Complex.exp (-(Multigraph.pairing τ (-G.greenOp hG τ)) / (2 * β)) =
        Complex.exp (-gffTranslationEnergy G β a τ +
          -(Multigraph.pairing τ' (-G.greenOp hG τ')) / (2 * β)) := by
            rw [← hrealC]
    _ = Complex.exp (-gffTranslationEnergy G β a τ) *
        Complex.exp (-(Multigraph.pairing τ' (-G.greenOp hG τ')) / (2 * β)) :=
          Complex.exp_add _ _

end FroehlichSpencer.BKT

end
