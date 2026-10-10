/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedCluster
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedRootAverage
public import FroehlichSpencer.BKT.Coulomb.TheoremB
public import FroehlichSpencer.BKT.Coulomb.ConditionLambda
public import FroehlichSpencer.BKT.Gaussian.FejerAverage
public import FroehlichSpencer.BKT.Bridge.GFFMeasure
import Mathlib.Tactic

/-!
# The Fejér marked ratio on the rooted square

* `integral_cos_mul_gffFejerWeight_nonneg`: the Fejér polynomial is a sine-Gordon weight with
  nonnegative coefficients, so the marked Fejér integral is nonnegative.
* `gffFejerWeight_rerootField`, `prod_rootedFejerLam_rootRelative_eq`: at root offset `t`, the
  site product is D1's branch expansion with the phases `−t ϱ(root)`.
* `rootRelative_marked_bound`: at every root offset,
  `|∫ cos(ξ⟨φ, ϱ₀⟩) P_t| ≤ e^{4K_nb − (γ/2)ℓ} ∫ P_t` and `0 < ∫ P_t`. It combines:
  - the rooted Fejér witness waves (branch comparison and activities);
  - the marked clause (term data and neighbours).
* **`rootedFejer_marked_ratio_bound`**: through the root average of `integral_gffMeasure_rootAverage`,
  the full Fejér ratio on `squareZero` satisfies
  `0 ≤ ∫ cos(ξ⟨φ, ϱ₀⟩) ∏_j F_N(φ_j) dμ ≤ e^{4K_nb − (γ/2)ℓ} ∫ ∏_j F_N(φ_j) dμ`, with a
  positive denominator.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open MeasureTheory FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Rotator

/-! ### Positivity of the Fejér cosine integral -/

/-- The Fejér coefficients as an even nonnegative charge law, `λ(n) = max(0, 1 − |n|/N)`. -/
def fejerLaw (N : ℕ) : ℤ → ℝ := fun n => max 0 (1 - |(n : ℝ)| / N)

theorem fejerPolynomial_eq_sineGordon {N : ℕ} (hN : 0 < N) (x : ℝ) :
    fejerPolynomial N x = Coulomb.sineGordonWeightInternal N (fejerLaw N) x := by
  unfold Coulomb.sineGordonWeightInternal
  rw [Coulomb.sum_Icc_eq_zero_add_two_mul N (fun n => fejerLaw N n * Real.cos (n * x))
    (fun n => by simp [fejerLaw, abs_neg, Real.cos_neg])]
  rw [fejerPolynomial_eq_kp]
  have h0 : fejerLaw N 0 = 1 := by simp [fejerLaw]
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one, h0]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqN : (q : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hq).2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : fejerLaw N (q : ℤ) = fejerCosineCoefficient N q := by
    unfold fejerLaw fejerCosineCoefficient
    have : |((q : ℤ) : ℝ)| = q := by simp
    rw [this, max_eq_right]
    rw [sub_nonneg, div_le_one hNpos]
    exact hqN
  simp only [Int.cast_natCast] at hq ⊢
  rw [hq]
  ring

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Positivity of the marked Fejér integral**: `∫ cos(ξ⟨φ, f⟩) ∏_j F_N(φ_j) dμ ≥ 0` for every
neutral real `f` (the Fejér polynomial has nonnegative cosine coefficients). -/
theorem integral_cos_mul_gffFejerWeight_nonneg (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) {N : ℕ} (hN : 0 < N)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (ξ : ℝ) :
    0 ≤ ∫ φ, Real.cos (ξ * ∑ j, φ j * f j) * gffFejerWeight N φ ∂gffLaw G hG β hβ v := by
  have h := Coulomb.integral_cos_mul_prod_sineGordonWeight_nonneg G hG β hβ v N
    (fun _ => fejerLaw N) (fun _ n => by simp [fejerLaw, abs_neg])
    (fun _ n => le_max_left _ _) f hf ξ
  have hw : ∀ φ : V → ℝ, gffFejerWeight N φ =
      ∏ j, Coulomb.sineGordonWeightInternal N (fejerLaw N) (φ j) := fun φ => by
    unfold gffFejerWeight
    exact Finset.prod_congr rfl fun j _ => fejerPolynomial_eq_sineGordon hN (φ j)
  simp_rw [hw]
  exact h

/-! ### The re-rooted Fejér product on the rooted square -/

section Reroot

variable {L N : ℕ}

/-- The root-relative field with root value `0` and site values `φ − φ(root) + t`. -/
def rootRelativeField (L : ℕ) (t : ℝ) (φ : RotatorDualFace L → ℝ) : RotatorDualFace L → ℝ :=
  fun j => if j = none then 0 else φ j - φ none + t

theorem gffFejerWeight_rerootField (L N : ℕ) (t : ℝ) (φ : RotatorDualFace L → ℝ) :
    gffFejerWeight N (rerootField none t φ) =
      fejerPolynomial N t * ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) := by
  unfold gffFejerWeight rerootField rootRelativeField rootedFejerLam
  rw [Fintype.prod_option, Fintype.prod_option]
  simp

theorem sum_rootRelativeField_mul (L : ℕ) (t : ℝ) (φ : RotatorDualFace L → ℝ)
    {ϱ : RotatorDualFace L → ℤ} (hϱ : ∑ j, ϱ j = 0) :
    ∑ j, rootRelativeField L t φ j * (ϱ j : ℝ) =
      ∑ j, φ j * (ϱ j : ℝ) + -t * (ϱ none : ℝ) := by
  have hn : (ϱ none : ℝ) + ∑ x, (ϱ (some x) : ℝ) = 0 := by
    have := hϱ
    rw [Fintype.sum_option] at this
    exact_mod_cast this
  unfold rootRelativeField
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [ite_true, zero_mul, zero_add, reduceCtorEq, ite_false]
  have e : ∑ x, (φ (some x) - φ none + t) * (ϱ (some x) : ℝ) =
      ∑ x, φ (some x) * (ϱ (some x) : ℝ) + (t - φ none) * ∑ x, (ϱ (some x) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e]
  have e2 : ∑ x, (ϱ (some x) : ℝ) = -(ϱ none : ℝ) := by linarith
  rw [e2]
  ring

/-- The D1 branch expansion of the re-rooted site product: the root offset `t` enters as the
constant phases `−t ϱ(root)`. -/
theorem prod_rootedFejerLam_rootRelative_eq (W : RootedFejerLayerWitness L N) (t : ℝ)
    (φ : RotatorDualFace L → ℝ) :
    ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) =
      ∑ i, W.layer.c i * phaseProduct (W.layer.N i) (W.layer.K i)
        (fun ϱ => -t * (ϱ none : ℝ)) φ := by
  rw [W.layer.expand (rootRelativeField L t φ) (by simp [rootRelativeField])]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold phaseProduct
  refine Finset.prod_congr rfl fun ϱ hϱ => ?_
  rw [sum_rootRelativeField_mul L t φ (W.layer.neutral i ϱ hϱ)]

end Reroot

/-! ### The per-offset marked bound on the rooted square -/

section Offset

variable {L N : ℕ}

theorem layerA_nonneg (ϱ : RotatorDualFace L → ℤ) : 0 ≤ layerA ϱ := by
  unfold layerA layerCoverSum
  have h1 : 0 ≤ ∑ j, |(ϱ j : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : 0 ≤ ∑ j ∈ Finset.range (layerCutoff ϱ + 1),
      (squareCoverNumber .free L j (siteRestrict ϱ) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  linarith

theorem one_le_layerA {ϱ : RotatorDualFace L → ℤ} (hϱ : ϱ ≠ 0) : 1 ≤ layerA ϱ := by
  obtain ⟨j, hj⟩ : ∃ j, ϱ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hϱ (funext h)
  have h1 : (1 : ℝ) ≤ |(ϱ j : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hj
  have h2 : |(ϱ j : ℝ)| ≤ ∑ k, |(ϱ k : ℝ)| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (ϱ k : ℝ)) (Finset.mem_univ j)
  have h3 : 0 ≤ layerCoverSum ϱ := by
    unfold layerCoverSum
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  unfold layerA
  linarith

theorem fejerLayerD₁_pos : 0 < fejerLayerD₁ := by
  unfold fejerLayerD₁
  have := layerD₁_pos
  positivity

/-- **The marked bound at one root offset.** Let `W` be a rooted Fejér witness whose branches carry the
marked clause. With the Gaussian activity parameters (`exists_gaussianActivity_params`), the
rate `s ≥ max(log 2, s₀)` and `γ ≥ max(D₂ + s + log 2 + 4K_nb, 8K_nb)`, the re-rooted site
product `P_t` satisfies `0 < ∫ P_t` and `|∫ cos(ξ⟨φ, ϱ₀⟩) P_t| ≤ e^{4K_nb − (γ/2)ℓ} ∫ P_t`. -/
theorem rootRelative_marked_bound (W : RootedFejerLayerWitness L N)
    (hG : (squareZero L).toSimpleGraph.Connected) {τ : ℝ} (hτ : 0 < τ)
    {adj : (RotatorDualFace L → ℤ) → Finset (RotatorDualFace L → ℤ) → Prop}
    {ρ₀ : RotatorDualFace L → ℤ} (hρ₀ : ∑ j, ρ₀ j = 0) {ξ s₀ Knb γ ℓ : ℝ}
    (hclause : ∀ i, RootedMarkedBranchClause (squareZero L) τ (W.layer.N i) (W.layer.K i)
      layerA ξ ρ₀ adj s₀ Knb γ ℓ)
    {s amp : ℝ} {k₀ : ℕ} (hamp : 0 ≤ amp) (hk₀ : 1 ≤ k₀)
    (hsamp : s ≤ amp / (8 * fejerLayerD₁) - fejerLayerD₂)
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 8)
    (hexp : 100 * 4 ^ k₀ * costMajorant (τ / 2) (τ / 2) (amp * 8) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (τ / 2) * 6400))
    (hs2 : Real.log 2 ≤ s) (hss₀ : s₀ ≤ s) (hℓ : 0 ≤ ℓ)
    (hγ₁ : fejerLayerD₂ + s + Real.log 2 + 4 * Knb ≤ γ) (hγ₂ : 8 * Knb ≤ γ)
    (v : RotatorDualFace L) (t : ℝ) :
    0 < ∫ φ, ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j)
        ∂gffLaw (squareZero L) hG τ hτ v ∧
      |∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
          ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j)
          ∂gffLaw (squareZero L) hG τ hτ v| ≤
        Real.exp (4 * Knb - γ / 2 * ℓ) * ∫ φ, ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j)
          ∂gffLaw (squareZero L) hG τ hτ v := by
  classical
  have := isProbabilityMeasure_gffLaw (squareZero L) hG τ hτ v
  set μ := gffLaw (squareZero L) hG τ hτ v with hμ
  set CL := W.layer with hCL
  set ph : (RotatorDualFace L → ℤ) → ℝ := fun ϱ => -t * (ϱ none : ℝ) with hph
  set ε := Real.exp (4 * Knb - γ / 2 * ℓ) with hε
  have hP : ∀ φ, ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) =
      ∑ i, CL.c i * phaseProduct (CL.N i) (CL.K i) ph φ :=
    fun φ => prod_rootedFejerLam_rootRelative_eq W t φ
  -- the per-branch bounds
  have hs0 : 0 < s := lt_of_lt_of_le (Real.log_pos (by norm_num)) hs2
  have hbranch : ∀ i, 0 < ∫ φ, phaseProduct (CL.N i) (CL.K i) ph φ ∂μ ∧
      |∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * phaseProduct (CL.N i) (CL.K i) ph φ ∂μ| ≤
        ε * ∫ φ, phaseProduct (CL.N i) (CL.K i) ph φ ∂μ := by
    intro i
    set b := rootedSpinWaveD CL (τ / 2) amp k₀ i with hb
    have horth₁ : ∀ ϱ ∈ CL.N i, ∀ ϱ' ∈ CL.N i, ϱ ≠ ϱ' →
        Multigraph.pairing (b ϱ) (fun j => (ϱ' j : ℝ)) = 0 := fun ϱ hϱ ϱ' hϱ' hne =>
      rootedSpinWaveD_orth CL (τ / 2) amp k₀ i hϱ hϱ' hne
    have horth₂ : ∀ ϱ ∈ CL.N i, ∀ ϱ' ∈ CL.N i, ϱ ≠ ϱ' →
        Multigraph.pairing (b ϱ) ((squareZero L).laplacian (b ϱ')) = 0 := by
      intro ϱ hϱ ϱ' hϱ' hne
      rw [Multigraph.pairing_laplacian_eq_neg_sum_grad_mul, neg_eq_zero]
      refine Finset.sum_eq_zero fun e _ => ?_
      rcases grad_rootedSpinWaveD_disjoint CL (τ / 2) amp k₀ i hϱ hϱ' hne e with h | h <;>
        simp [hb, h]
    have hz : ∀ ϱ ∈ CL.N i, |CL.K i ϱ| * Real.exp (-gffTranslationEnergy (squareZero L) τ
        (b ϱ) (fun j => (ϱ j : ℝ))) ≤ Real.exp (-s * layerA ϱ) := fun ϱ hϱ =>
      abs_K_mul_exp_le_of_gaussian CL (by norm_num) (by norm_num) fejerLayerD₁_pos hτ hamp hk₀
        hsamp hquad₂ hexp hquad₁ layerA_nonneg i ϱ hϱ
    have hcost : ∀ m ∈ CL.N i, 1 ≤ layerA m := fun m hm =>
      one_le_layerA (W.isLocal.ne_zero i m hm)
    have hθ : ∀ m ∈ CL.N i, Real.exp (-s * layerA m) < 1 := fun m hm => by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_lt_exp.2 (by nlinarith [hcost m hm])
    obtain ⟨hZ, hM⟩ := abs_markedBranch_le_rooted (squareZero L) hG τ hτ v (CL.N i)
      (fun ϱ hϱ => CL.neutral i ϱ hϱ) (CL.K i) ph (fun ϱ => Real.exp (-s * layerA ϱ)) b
      horth₁ horth₂ hz hθ hρ₀ ξ (hclause i).mono
      (fun C => γ * (∑ m ∈ C, layerA m + ℓ)) (hclause i).term
    have hK : ∀ m ∈ CL.N i, |CL.K i m| ≤ Real.exp (fejerLayerD₂ * layerA m) := fun m hm => by
      have := CL.entropy i m hm
      simpa using this
    have hW := sum_clusterWeight_le (hclause i).mono (CL.N i) (CL.K i) layerA hcost hK hs2 hss₀
      hℓ (hclause i).neighbour hγ₁ hγ₂
    refine ⟨hZ, hM.trans (mul_le_mul_of_nonneg_right hW hZ.le)⟩
  -- the sum over branches
  have hint : ∀ i, Integrable (phaseProduct (CL.N i) (CL.K i) ph) μ := fun i =>
    integrable_phaseProduct μ _ _ _
  have hintc : ∀ i, Integrable (fun φ => Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
      phaseProduct (CL.N i) (CL.K i) ph φ) μ := fun i =>
    (hint i).bdd_mul (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hZsum : ∫ φ, ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) ∂μ =
      ∑ i, CL.c i * ∫ φ, phaseProduct (CL.N i) (CL.K i) ph φ ∂μ := by
    simp_rw [hP]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
    simp_rw [integral_const_mul]
  have hMsum : ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
      ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) ∂μ =
      ∑ i, CL.c i * ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
        phaseProduct (CL.N i) (CL.K i) ph φ ∂μ := by
    have hpt : ∀ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
        ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) =
        ∑ i, CL.c i * (Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
          phaseProduct (CL.N i) (CL.K i) ph φ) := fun φ => by
      rw [hP, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => (hintc i).const_mul (CL.c i)]
    simp_rw [integral_const_mul]
  have hn : (Finset.univ : Finset (Fin CL.n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := CL.c_sum
    rw [h, Finset.sum_empty] at this
    exact zero_ne_one this
  refine ⟨?_, ?_⟩
  · rw [hZsum]
    exact Finset.sum_pos (fun i _ => mul_pos (CL.c_pos i) (hbranch i).1) hn
  · rw [hMsum, hZsum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (CL.c_pos i), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hbranch i).2 (CL.c_pos i).le

end Offset

/-! ### The Fejér marked ratio on the rooted square -/

section Ratio

variable {L N : ℕ}

theorem continuous_gffFejerWeight (V : Type) [Fintype V] (N : ℕ) :
    Continuous (fun φ : V → ℝ => gffFejerWeight N φ) := by
  unfold gffFejerWeight fejerPolynomial
  fun_prop

theorem sum_rerootField_mul (L : ℕ) (t : ℝ) (φ : RotatorDualFace L → ℝ)
    {ρ₀ : RotatorDualFace L → ℤ} (hρ₀ : ∑ j, ρ₀ j = 0) :
    ∑ j, rerootField none t φ j * (ρ₀ j : ℝ) = ∑ j, φ j * (ρ₀ j : ℝ) := by
  have h0 : ∑ j, (ρ₀ j : ℝ) = 0 := by exact_mod_cast hρ₀
  unfold rerootField
  have e : ∑ j, (φ j - φ none + t) * (ρ₀ j : ℝ) =
      ∑ j, φ j * (ρ₀ j : ℝ) + (t - φ none) * ∑ j, (ρ₀ j : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, h0, mul_zero, add_zero]

/-- **The Fejér marked ratio on the rooted square** at one GFF parameter and one cutoff: from a D1
witness carrying the marked clause, with the activity parameters and the gain conditions of
`rootRelative_marked_bound`, the root-window Fejér denominator is positive and
`0 ≤ ∫ cos(ξ⟨φ, ϱ₀⟩) ∏_j F_N(φ_j) dμ ≤ e^{4K_nb − (γ/2)ℓ} ∫ ∏_j F_N(φ_j) dμ`. -/
theorem rootedFejer_marked_ratio_bound (W : RootedFejerLayerWitness L N) (hN : 1 ≤ N)
    (hG : (squareZero L).Connected) {τ : ℝ} (hτ : 0 < τ)
    {adj : (RotatorDualFace L → ℤ) → Finset (RotatorDualFace L → ℤ) → Prop}
    {ρ₀ : RotatorDualFace L → ℤ} (hρ₀ : ∑ j, ρ₀ j = 0) {ξ s₀ Knb γ ℓ : ℝ}
    (hclause : ∀ i, RootedMarkedBranchClause (squareZero L) τ (W.layer.N i) (W.layer.K i)
      layerA ξ ρ₀ adj s₀ Knb γ ℓ)
    {s amp : ℝ} {k₀ : ℕ} (hamp : 0 ≤ amp) (hk₀ : 1 ≤ k₀)
    (hsamp : s ≤ amp / (8 * fejerLayerD₁) - fejerLayerD₂)
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 8)
    (hexp : 100 * 4 ^ k₀ * costMajorant (τ / 2) (τ / 2) (amp * 8) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (τ / 2) * 6400))
    (hs2 : Real.log 2 ≤ s) (hss₀ : s₀ ≤ s) (hℓ : 0 ≤ ℓ)
    (hγ₁ : fejerLayerD₂ + s + Real.log 2 + 4 * Knb ≤ γ) (hγ₂ : 8 * Knb ≤ γ) :
    0 < ∫ φ, gffFejerWeight N φ ∂gffMeasure (squareZero L) hG τ hτ none ∧
      0 ≤ ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * gffFejerWeight N φ
        ∂gffMeasure (squareZero L) hG τ hτ none ∧
      ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * gffFejerWeight N φ
          ∂gffMeasure (squareZero L) hG τ hτ none ≤
        Real.exp (4 * Knb - γ / 2 * ℓ) *
          ∫ φ, gffFejerWeight N φ ∂gffMeasure (squareZero L) hG τ hτ none := by
  classical
  have hNpos : 0 < N := hN
  set μ := gffMeasure (squareZero L) hG τ hτ none with hμ
  have hlaw : gffLaw (squareZero L) hG τ hτ none = μ := gffLaw_eq_gffMeasure _ hG τ hτ none
  set ε := Real.exp (4 * Knb - γ / 2 * ℓ) with hε
  set M : ℝ → ℝ := fun t => ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
    ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) ∂μ with hM
  set Z : ℝ → ℝ := fun t => ∫ φ, ∏ j, rootedFejerLam L N j (rootRelativeField L t φ j) ∂μ
    with hZ
  have hoffset : ∀ t, 0 < Z t ∧ |M t| ≤ ε * Z t := by
    intro t
    have h := rootRelative_marked_bound W hG hτ hρ₀ hclause hamp hk₀ hsamp hquad₂ hexp hquad₁
      hs2 hss₀ hℓ hγ₁ hγ₂ none t
    rw [hlaw] at h
    exact h
  -- the denominator
  have hden : 0 < ∫ φ, gffFejerWeight N φ ∂μ := by
    have h := gffFejerAverage_zero_pos (squareZero L) hG τ hτ none N hNpos
    unfold gffFejerAverage at h
    simpa [Multigraph.pairing] using h
  -- the numerator is nonnegative
  have hnum0 : 0 ≤ ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * gffFejerWeight N φ ∂μ := by
    have h := integral_cos_mul_gffFejerWeight_nonneg (squareZero L) hG τ hτ none hNpos
      (fun j => (ρ₀ j : ℝ)) (by exact_mod_cast hρ₀) ξ
    rw [hlaw] at h
    exact h
  refine ⟨hden, hnum0, ?_⟩
  -- the root averages
  set B : ℝ := (1 + 2 * (N : ℝ)) ^ Fintype.card (RotatorDualFace L) with hB
  have hbd : ∀ φ : RotatorDualFace L → ℝ, |gffFejerWeight N φ| ≤ B := fun φ =>
    gffFejerWeight_abs_le N φ
  have hNum := integral_gffMeasure_rootAverage (squareZero L) hG τ hτ none
    (fun φ => Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * gffFejerWeight N φ)
    ((by fun_prop : Continuous fun φ : RotatorDualFace L → ℝ =>
      Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ))).mul (continuous_gffFejerWeight _ N)).measurable
    (C := B) (fun φ => by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (hbd φ))
  have hDen := integral_gffMeasure_rootAverage (squareZero L) hG τ hτ none
    (fun φ => gffFejerWeight N φ) (continuous_gffFejerWeight _ N).measurable (C := B) hbd
  have hNumt : ∀ t, ∫ φ, (fun φ => Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
      gffFejerWeight N φ) (rerootField none t φ) ∂μ = fejerPolynomial N t * M t := by
    intro t
    simp only [gffFejerWeight_rerootField, sum_rerootField_mul L t _ hρ₀]
    rw [hM, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun φ => by ring)
  have hDent : ∀ t, ∫ φ, gffFejerWeight N (rerootField none t φ) ∂μ =
      fejerPolynomial N t * Z t := by
    intro t
    rw [hZ, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun φ => gffFejerWeight_rerootField L N t φ)
  rw [← hμ] at hNum hDen
  simp_rw [hNumt] at hNum
  simp_rw [hDent] at hDen
  -- integrability of the denominator density in `t`
  have hZint : MeasureTheory.IntegrableOn (fun t => fejerPolynomial N t * Z t)
      (Set.Ico (-Real.pi) Real.pi) := by
    by_contra hni
    have h0 : ∫ t in Set.Ico (-Real.pi) Real.pi, fejerPolynomial N t * Z t = 0 :=
      integral_undef hni
    rw [h0, mul_zero] at hDen
    linarith
  have hpt : ∀ t, |fejerPolynomial N t * M t| ≤ ε * (fejerPolynomial N t * Z t) := by
    intro t
    have hF := fejerPolynomial_nonneg N hNpos t
    rw [abs_mul, abs_of_nonneg hF]
    calc fejerPolynomial N t * |M t| ≤ fejerPolynomial N t * (ε * Z t) :=
          mul_le_mul_of_nonneg_left (hoffset t).2 hF
      _ = ε * (fejerPolynomial N t * Z t) := by ring
  have hint_le : |∫ t in Set.Ico (-Real.pi) Real.pi, fejerPolynomial N t * M t| ≤
      ε * ∫ t in Set.Ico (-Real.pi) Real.pi, fejerPolynomial N t * Z t := by
    rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun t => abs_nonneg _) (hZint.const_mul ε) (ae_of_all _ fun t => hpt t))
  rw [hNum, hDen]
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  calc (2 * Real.pi)⁻¹ * ∫ t in Set.Ico (-Real.pi) Real.pi, fejerPolynomial N t * M t
      ≤ (2 * Real.pi)⁻¹ * |∫ t in Set.Ico (-Real.pi) Real.pi, fejerPolynomial N t * M t| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hpi.le
    _ ≤ (2 * Real.pi)⁻¹ * (ε * ∫ t in Set.Ico (-Real.pi) Real.pi, fejerPolynomial N t * Z t) :=
        mul_le_mul_of_nonneg_left hint_le hpi.le
    _ = ε * ((2 * Real.pi)⁻¹ *
          ∫ t in Set.Ico (-Real.pi) Real.pi, fejerPolynomial N t * Z t) := by ring

end Ratio

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
