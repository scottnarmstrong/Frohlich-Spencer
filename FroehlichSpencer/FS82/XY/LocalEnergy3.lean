/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Renormalization3
public import FroehlichSpencer.FS82.XY.Poisson3
public import FroehlichSpencer.FS82.XY.BranchGaussian

/-!
# the local lower bound on the dual covariance in three dimensions

For a co-closed real one-form `μ` on the dual complex and a set `S` of dual links no two of which
lie in one dual plaquette,

`∑_{b ∈ S} μ_b² / n_b ≤ ⟨μ, (δd)⁻¹ μ⟩`,

where `n_b` is the number of plaquettes at `b`.

This is the Cauchy–Schwarz inequality
`⟨μ, a⟩² ≤ ⟨μ, (δd)⁻¹μ⟩ ‖da‖²` at `a = ∑_{b ∈ S} (μ_b / n_b) e_b`.

It is the estimate behind the
complex translation of FS82 Section 2.8 and (4.36): the selected links carry independent Gaussian
fluctuations of variance `β / n_b`.

In chord coordinates it gives the hypothesis of
`GaugeAverage.branchCovariance_posSemidef` for a separated family with its six-colour blocks.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.Renormalization3
open FroehlichSpencer.FS82.XY.GaugeAverage

/-! ## The abstract Cauchy–Schwarz inequality -/

section Abstract

variable {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

theorem inner_sq_le_quotientCovarianceQuadratic_mul (C : ExactOneComplex V E P)
    (x : coClosed C) (a : EuclideanSpace ℝ E) :
    (inner ℝ (x : EuclideanSpace ℝ E) a) ^ 2 ≤
      quotientCovarianceQuadratic C x * inner ℝ (C.d₁ a) (C.d₁ a) := by
  set g : EuclideanSpace ℝ E := (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E) with hg
  have hval : formLaplacian C g = x :=
    congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C x)
  have h1 : inner ℝ (x : EuclideanSpace ℝ E) a = inner ℝ (C.d₁ g) (C.d₁ a) := by
    rw [← hval]
    simp [formLaplacian, LinearMap.adjoint_inner_left]
  have h2 : quotientCovarianceQuadratic C x = inner ℝ (C.d₁ g) (C.d₁ g) := by
    unfold quotientCovarianceQuadratic
    rw [← hg]
    nth_rewrite 1 [← hval]
    change inner ℝ (C.d₁.adjoint (C.d₁ g)) g = _
    rw [LinearMap.adjoint_inner_left]
  rw [h1, h2, sq]
  exact real_inner_mul_inner_self_le _ _

theorem sq_sum_eq_sum_sq_of_pairwise {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀ b₁ ∈ S, ∀ b₂ ∈ S, b₁ ≠ b₂ → f b₁ = 0 ∨ f b₂ = 0) :
    (∑ b ∈ S, f b) ^ 2 = ∑ b ∈ S, f b ^ 2 := by
  classical
  by_cases hex : ∃ b₀ ∈ S, f b₀ ≠ 0
  · obtain ⟨b₀, hb₀, hne⟩ := hex
    have hzero : ∀ b ∈ S, b ≠ b₀ → f b = 0 := by
      intro b hb hbne
      rcases h b hb b₀ hb₀ hbne with h0 | h0
      · exact h0
      · exact absurd h0 hne
    rw [Finset.sum_eq_single_of_mem b₀ hb₀ hzero,
      Finset.sum_eq_single_of_mem b₀ hb₀ fun b hb hbne => by rw [hzero b hb hbne]; ring]
  · have hall : ∀ b ∈ S, f b = 0 := by
      intro b hb
      by_contra hne
      exact hex ⟨b, hb, hne⟩
    rw [Finset.sum_eq_zero hall, Finset.sum_eq_zero fun b hb => by rw [hall b hb]; ring]
    ring

end Abstract

variable {B : Dual3Box}

/-! ## The three-dimensional local lower bound -/

theorem dual3D₁_apply_eq_sum_chartIncidence (a : EuclideanSpace ℝ (Dual3Links B))
    (p : Dual3Plaquettes B) :
    dual3D₁ a p = ∑ e, a e * dual3ChartIncidence p e := by
  have ha : a = ∑ e, a e • EuclideanSpace.single e (1 : ℝ) := by
    ext e'
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [ha]
  rw [map_sum]
  simp [dual3ChartIncidence, Finset.sum_apply]

theorem linkMass_dual3ChartIncidence_pos (e : Dual3Links B) :
    0 < linkMass (dual3ChartIncidence (B := B)) e := by
  rw [linkMass_dual3ChartIncidence_eq_incidentPlaquetteCount]
  exact_mod_cast incidentPlaquetteCount_pos e

/-- **The local lower bound.** -/
theorem dual3_selectedEnergy_le_covarianceQuadratic
    (μ : coClosed (dual3ExactOneComplex B)) (S : Finset (Dual3Links B))
    (hind : ∀ p, ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ →
      dual3ChartIncidence p e₁ = 0 ∨ dual3ChartIncidence p e₂ = 0) :
    ∑ b ∈ S, (μ.1 b) ^ 2 / linkMass (dual3ChartIncidence (B := B)) b ≤
      quotientCovarianceQuadratic (dual3ExactOneComplex B) μ := by
  classical
  set n : Dual3Links B → ℝ := linkMass (dual3ChartIncidence (B := B)) with hn
  have hnpos : ∀ b, 0 < n b := linkMass_dual3ChartIncidence_pos
  set M : ℝ := ∑ b ∈ S, (μ.1 b) ^ 2 / n b with hM
  let a : EuclideanSpace ℝ (Dual3Links B) :=
    WithLp.toLp 2 fun b => if b ∈ S then μ.1 b / n b else 0
  have hpair : inner ℝ (μ : EuclideanSpace ℝ (Dual3Links B)) a = M := by
    rw [PiLp.inner_apply, hM, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    have h2 : ∑ b ∈ Finset.univ.filter (fun b => ¬ b ∈ S), inner ℝ (μ.1 b) (a b) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have hbS : b ∉ S := (Finset.mem_filter.mp hb).2
      simp [a, hbS]
    rw [h2, add_zero]
    have hfilter : Finset.univ.filter (fun b => b ∈ S) = S := by
      ext b
      simp
    rw [hfilter]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [a, hb, ↓reduceIte, RCLike.inner_apply, conj_trivial]
    ring
  have hd : ∀ p, (dual3ExactOneComplex B).d₁ a p =
      ∑ b ∈ S, (μ.1 b / n b) * dual3ChartIncidence p b := by
    intro p
    change dual3D₁ a p = _
    rw [dual3D₁_apply_eq_sum_chartIncidence,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    have h2 : ∑ b ∈ Finset.univ.filter (fun b => ¬ b ∈ S), a b * dual3ChartIncidence p b = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have hbS : b ∉ S := (Finset.mem_filter.mp hb).2
      simp [a, hbS]
    rw [h2, add_zero]
    have hfilter : Finset.univ.filter (fun b => b ∈ S) = S := by
      ext b
      simp
    rw [hfilter]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp [a, hb]
  have hnorm : inner ℝ ((dual3ExactOneComplex B).d₁ a) ((dual3ExactOneComplex B).d₁ a) = M := by
    rw [PiLp.inner_apply]
    have hp : ∀ p, inner ℝ ((dual3ExactOneComplex B).d₁ a p)
        ((dual3ExactOneComplex B).d₁ a p) =
        ∑ b ∈ S, (μ.1 b / n b) ^ 2 * dual3ChartIncidence p b ^ 2 := by
      intro p
      rw [RCLike.inner_apply, conj_trivial, hd p, ← sq,
        sq_sum_eq_sum_sq_of_pairwise S _ (fun b₁ hb₁ b₂ hb₂ hne => by
          rcases hind p b₁ hb₁ b₂ hb₂ hne with h0 | h0
          · exact Or.inl (by rw [h0, mul_zero])
          · exact Or.inr (by rw [h0, mul_zero]))]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp_rw [hp]
    rw [Finset.sum_comm, hM]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum]
    change (μ.1 b / n b) ^ 2 * n b = _
    have := (hnpos b).ne'
    field_simp
  have hCS := inner_sq_le_quotientCovarianceQuadratic_mul (dual3ExactOneComplex B) μ a
  rw [hpair, hnorm] at hCS
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun b _ => div_nonneg (sq_nonneg _) (hnpos b).le
  have hQ0 := quotientCovarianceQuadratic_nonneg (dual3ExactOneComplex B) μ
  by_cases hMz : M = 0
  · rw [hMz]
    exact hQ0
  · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hMz)
    nlinarith

/-! ## Chord coordinates -/

/-- The chord quadratic form of a real co-closed one-form is `2πβ` times its dual covariance. -/
theorem chordBilinear_restrictChord_eq {β : ℝ} (hβ : 0 < β)
    (μ : coClosed (dual3ExactOneComplex B)) :
    chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
        ((xyDual3RootedTree B).restrictChord μ.1.ofLp)
        ((xyDual3RootedTree B).restrictChord μ.1.ofLp) =
      2 * Real.pi * β * quotientCovarianceQuadratic (dual3ExactOneComplex B) μ := by
  unfold chordBilinear quotientCovarianceQuadratic
  rw [xyDual3ChordMatrix_inv hβ, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  exact (xyDual3HodgePairing_eq_chord μ μ).symm

end FroehlichSpencer.FS82.XY

end
