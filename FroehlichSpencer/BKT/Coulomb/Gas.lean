/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Fintype.Pi
public import FroehlichSpencer.BKT.Surface.SubGaussian
import Mathlib.Tactic

/-!
# The finite lattice Coulomb gas and its sine-Gordon weights

The finite graph definitions below use a Laplacian pseudoinverse and finite charge cutoffs.

* `chargeConfigsInternal V N`: charge configurations `q : V → ℤ` with `|q j| ≤ N`.
* `chargeEnergyInternal T q`: the electrostatic energy (1.4), `E(q) = ½ ⟨q, C q⟩`, for the
  potential `C = -T`, where `T` is a Laplacian pseudoinverse (KP (1.2)); KP and FS81 both call
  `-Δ⁻¹` the Green function.
* `gasWeightInternal`, `gasPartitionInternal`, `gasExpectationInternal`: the Gibbs weight
  (1.7) **restricted to neutral configurations**, the partition function (1.8) and the
  expectation (1.9).

The neutrality constraint is not imposed by hand in the representation:
  it is what the integration over the constant mode of the rooted GFF produces
  (`Coulomb/SineGordon.lean`).

It matches FS81's free boundary condition, where non-neutral
  configurations have infinite energy ((1.14), p. 531).
* `sineGordonWeightInternal N λ`: the Fourier transform `λ̂(φ) = ∑_{|n| ≤ N} λ(n) e^{i n φ}` of
  (1.15), written with cosines; for even `λ` this is the same function.
* `hardCoreWeightInternal z`: the hard-core weights (1.10), with `λ̂(φ) = 1 + z cos φ` (5.1);
  `regionWeightInternal A λ` puts `λ` on a charge region `A` and the vacuum weight elsewhere.

Charge conjugation (Condition λ (a)): for even weights the Gibbs weight is invariant under
`q ↦ -q` (`gasWeight_neg`), so odd observables have zero expectation
(`gasExpectation_odd_eq_zero`) and the charge characteristic functional
`⟨e^{i⟨q,g⟩}⟩_Λ = ⟨cos ⟨q, g⟩⟩_Λ` is real (`gasExpectation_sin_eq_zero`).

The pointwise identity `prod_sineGordonWeight_eq_sum`,
`∏_j λ̂_j(φ_j) = ∑_q (∏_j λ_j(q_j)) cos ⟨φ, q⟩`, is the algebraic half of (1.15).

**Deviation (recorded).** FS81's free boundary condition uses the whole-plane potential
`C(i - j)` restricted to `Λ` (p. 529, (i)).

Here `C = -T` is the pseudoinverse of the graph
Laplacian of the finite domain carrying the GFF.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Charge configurations `q : V → ℤ` with `|q j| ≤ N` at every site (FS81 p. 529: a
configuration is a function `q_Λ` with values in `ℤ`; here truncated at `N`). -/
def chargeConfigsInternal (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ) : Finset (V → ℤ) :=
  Fintype.piFinset fun _ : V => Finset.Icc (-(N : ℤ)) N

/-- FS81 (1.15): the Fourier transform `λ̂(φ) = ∑_{|n| ≤ N} λ(n) cos (n φ)` of a charge weight
`λ`, truncated at `|n| ≤ N`. For even `λ` it equals `∑_{|n| ≤ N} λ(n) e^{i n φ}`
(`sineGordonWeight_complex`). -/
def sineGordonWeightInternal (N : ℕ) (lam : ℤ → ℝ) (φ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, lam n * Real.cos (n * φ)

/-- FS81 (1.4): the electrostatic energy `E(q) = ½ ∑_{i,j} q(i) q(j) C(i,j)` of a charge
configuration, self-energies included, for the potential `C = -T`. -/
def chargeEnergyInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (q : V → ℤ) : ℝ :=
  (∑ j, (q j : ℝ) * -(T (fun i => (q i : ℝ)) j)) / 2

/-- FS81 (1.7), unnormalized, with the neutrality constraint of the free boundary condition:
`𝟙[∑_j q_j = 0] · ∏_j λ_j(q_j) · e^{-κ E(q)}`. -/
def gasWeightInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) (q : V → ℤ) : ℝ :=
  if ∑ j, q j = 0 then (∏ j, lam j (q j)) * Real.exp (-κ * chargeEnergyInternal T q) else 0

/-- FS81 (1.8): the partition function `Z_Λ` of the neutral gas with charges `|q_j| ≤ N`. -/
def gasPartitionInternal (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) : ℝ :=
  ∑ q ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam q

/-- FS81 (1.9): the finite-volume expectation `⟨F⟩_Λ = Z_Λ⁻¹ ∑_q F(q) · weight(q)` of a
charge observable `F`. -/
def gasExpectationInternal (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (F : (V → ℤ) → ℝ) : ℝ :=
  (∑ q ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam q * F q) /
    gasPartitionInternal N T κ lam

/-! ### The pointwise sine-Gordon expansion -/

omit [Fintype V] [DecidableEq V] in
/-- The symmetric charge window `[-N, N]` is invariant under `n ↦ -n`. -/
theorem sum_Icc_neg_eq {N : ℕ} {M : Type*} [AddCommMonoid M] (g : ℤ → M) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g (-n) = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g n := by
  refine Finset.sum_nbij' (fun n => -n) (fun n => -n) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    constructor <;> linarith [hn.1, hn.2]
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    constructor <;> linarith [hn.1, hn.2]
  · intro n _; simp
  · intro n _; simp
  · intro n _; simp

omit [Fintype V] [DecidableEq V] in
/-- For an even weight, the cosine transform is the exponential transform (FS81 (1.15)). -/
theorem sineGordonWeight_complex (N : ℕ) (lam : ℤ → ℝ) (hlam : ∀ n, lam (-n) = lam n)
    (x : ℝ) :
    ((sineGordonWeightInternal N lam x : ℝ) : ℂ) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        (lam n : ℂ) * Complex.exp (Complex.I * ((n : ℝ) * x : ℝ)) := by
  have hsin : ∑ n ∈ Finset.Icc (-(N : ℤ)) N, lam n * Real.sin (n * x) = 0 := by
    have h := sum_Icc_neg_eq (N := N) (fun n : ℤ => lam n * Real.sin (n * x))
    simp only [hlam, Int.cast_neg, neg_mul, Real.sin_neg, mul_neg, Finset.sum_neg_distrib] at h
    linarith
  have hpt : ∀ n : ℤ, (lam n : ℂ) * Complex.exp (Complex.I * ((n : ℝ) * x : ℝ)) =
      ((lam n * Real.cos (n * x) : ℝ) : ℂ) +
        ((lam n * Real.sin (n * x) : ℝ) : ℂ) * Complex.I := by
    intro n
    rw [mul_comm Complex.I, Complex.exp_mul_I]
    push_cast
    ring
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, hsin]
  simp [sineGordonWeightInternal]

/-- The algebraic half of FS81 (1.15): for even charge weights,
`∏_j λ̂_j(φ_j) = ∑_q (∏_j λ_j(q_j)) cos ⟨φ, q⟩`, the sum running over `|q_j| ≤ N`. -/
theorem prod_sineGordonWeight_eq_sum (N : ℕ) (lam : V → ℤ → ℝ)
    (hlam : ∀ j n, lam j (-n) = lam j n) (φ : V → ℝ) :
    ∏ j, sineGordonWeightInternal N (lam j) (φ j) =
      ∑ q ∈ chargeConfigsInternal V N,
        (∏ j, lam j (q j)) * Real.cos (∑ j, φ j * (q j : ℝ)) := by
  have hC : ((∏ j, sineGordonWeightInternal N (lam j) (φ j) : ℝ) : ℂ) =
      ∑ q ∈ chargeConfigsInternal V N, ((∏ j, lam j (q j) : ℝ) : ℂ) *
        Complex.exp (((∑ j, φ j * (q j : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_prod]
    simp_rw [sineGordonWeight_complex N _ (hlam _)]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_prod]
    congr 2
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hre := congrArg Complex.re hC
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-! ### Charge conjugation -/

omit [DecidableEq V] in
theorem chargeEnergy_neg (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (q : V → ℤ) :
    chargeEnergyInternal T (-q) = chargeEnergyInternal T q := by
  unfold chargeEnergyInternal
  have : (fun i => ((-q) i : ℝ)) = -(fun i => (q i : ℝ)) := by
    funext i; simp
  rw [this, T.map_neg]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

omit [DecidableEq V] in
theorem gasWeight_neg (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (hlam : ∀ j n, lam j (-n) = lam j n) (q : V → ℤ) :
    gasWeightInternal T κ lam (-q) = gasWeightInternal T κ lam q := by
  unfold gasWeightInternal
  rw [chargeEnergy_neg]
  have hs : ∑ j, (-q) j = -∑ j, q j := by simp
  have hp : ∏ j, lam j ((-q) j) = ∏ j, lam j (q j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hlam]
  simp only [hs, hp, neg_eq_zero]

/-- Charge conjugation (FS81 Condition λ (a)): for even weights the gas expectation of an odd
observable vanishes. -/
theorem gasExpectation_odd_eq_zero (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n) {F : (V → ℤ) → ℝ}
    (hF : ∀ q, F (-q) = -F q) : gasExpectationInternal N T κ lam F = 0 := by
  unfold gasExpectationInternal
  have hS : ∑ q ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam q * F q =
      -∑ q ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam q * F q := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun q => -q) (fun q => -q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [chargeConfigsInternal, Fintype.mem_piFinset, Finset.mem_Icc,
        Pi.neg_apply] at hq ⊢
      intro j
      constructor <;> linarith [(hq j).1, (hq j).2]
    · intro q hq
      simp only [chargeConfigsInternal, Fintype.mem_piFinset, Finset.mem_Icc,
        Pi.neg_apply] at hq ⊢
      intro j
      constructor <;> linarith [(hq j).1, (hq j).2]
    · intro q _; simp
    · intro q _; simp
    · intro q _
      rw [gasWeight_neg T κ lam hlam, hF, mul_neg, neg_neg]
  have h0 : ∑ q ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam q * F q = 0 := by
    linarith
  rw [h0, zero_div]

/-- The charge characteristic functional is real: `⟨e^{i⟨q,g⟩}⟩_Λ = ⟨cos ⟨q, g⟩⟩_Λ`. -/
theorem gasExpectation_sin_eq_zero (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n) (g : V → ℝ) :
    gasExpectationInternal N T κ lam (fun q => Real.sin (∑ j, (q j : ℝ) * g j)) = 0 :=
  gasExpectation_odd_eq_zero N T κ lam hlam fun q => by
    simp [neg_mul, Finset.sum_neg_distrib, Real.sin_neg]

/-! ### The hard-core gas -/

/-- FS81 (1.10): the hard-core charge weight, `λ(0) = 1`, `λ(±1) = z/2`, `λ(q) = 0` otherwise. -/
def hardCoreWeightInternal (z : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 1 else if n = 1 ∨ n = -1 then z / 2 else 0

/-- Charge weights on a charge region `A`: `λ` at the sites of `A`, the vacuum weight
`𝟙[q = 0]` elsewhere (no charge can sit outside `A`). -/
def regionWeightInternal (A : Finset V) (lam : ℤ → ℝ) (j : V) (n : ℤ) : ℝ :=
  if j ∈ A then lam n else if n = 0 then 1 else 0

/-- The hard-core sine-Gordon weights on the charge region `A`: `λ̂_j(φ) = 1 + z cos φ` on `A`
and `1` off `A` (`sineGordonWeight_regionHardCore`). -/
abbrev hardCoreSineGordonInternal (A : Finset V) (z : ℝ) : V → ℝ → ℝ :=
  fun j => sineGordonWeightInternal 1 (regionWeightInternal A (hardCoreWeightInternal z) j)

/-- FS81 (1.10) satisfies Condition λ (a), `λ(q) = λ(-q)` (p. 530). -/
theorem hardCoreWeight_neg (z : ℝ) (n : ℤ) :
    hardCoreWeightInternal z (-n) = hardCoreWeightInternal z n := by
  unfold hardCoreWeightInternal
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · have h0' : -n ≠ 0 := neg_ne_zero.mpr h0
    simp only [h0, h0', ite_false]
    congr 1
    apply propext
    omega

omit [Fintype V] in
theorem regionWeight_neg (A : Finset V) {lam : ℤ → ℝ} (hlam : ∀ n, lam (-n) = lam n)
    (j : V) (n : ℤ) : regionWeightInternal A lam j (-n) = regionWeightInternal A lam j n := by
  unfold regionWeightInternal
  split_ifs <;> simp_all

/-- FS81 (5.1): `λ̂(φ) = 1 + z cos φ` for the hard-core gas. -/
theorem sineGordonWeight_hardCore (z φ : ℝ) :
    sineGordonWeightInternal 1 (hardCoreWeightInternal z) φ = 1 + z * Real.cos φ := by
  unfold sineGordonWeightInternal hardCoreWeightInternal
  have : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  rw [this]
  simp [Real.cos_neg]
  ring

omit [Fintype V] in
theorem sineGordonWeight_regionHardCore (A : Finset V) (z : ℝ) (j : V) (φ : ℝ) :
    hardCoreSineGordonInternal A z j φ = if j ∈ A then 1 + z * Real.cos φ else 1 := by
  by_cases hj : j ∈ A
  · simp only [hj, ite_true]
    have : regionWeightInternal A (hardCoreWeightInternal z) j = hardCoreWeightInternal z := by
      funext n; simp [regionWeightInternal, hj]
    rw [hardCoreSineGordonInternal, this, sineGordonWeight_hardCore]
  · simp only [hj, ite_false]
    unfold hardCoreSineGordonInternal sineGordonWeightInternal regionWeightInternal
    have : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
    rw [this]
    simp [hj]


theorem isSubGaussian_one_add_mul_cos (z : ℝ) (hz : 0 ≤ z) (β : ℝ) :
    IsSubGaussian (max 1 (z / 2)) 0 0 β (fun φ => 1 + z * Real.cos φ) := by
  refine ⟨1, one_pos, fun q => if q = 1 then z / 2 else 0, ?_, ?_, ?_⟩
  · intro q hq
    simp [show q ≠ 1 by omega]
  · intro φ
    simp
    ring
  · intro q _
    simp only [zero_div, add_zero, zero_mul, Real.exp_zero, mul_one]
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      exact le_max_right _ _
    · simp


theorem isSubGaussian_one_add_mul_cos_activity (α κ z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) :
    IsSubGaussian (max 1 (Real.exp α / 2)) 0 (1 / 17) κ⁻¹ (fun φ => 1 + z * Real.cos φ) := by
  refine ⟨1, one_pos, fun q => if q = 1 then z / 2 else 0, ?_, ?_, ?_⟩
  · intro q hq
    simp [show q ≠ 1 by omega]
  · intro φ
    simp
    ring
  · intro q _
    dsimp only
    split_ifs with h1
    · subst h1
      rw [abs_of_nonneg (by positivity)]
      have hexp : z / 2 ≤ Real.exp α / 2 * Real.exp (κ / 17) := by
        rw [div_mul_eq_mul_div, ← Real.exp_add, add_comm]
        linarith
      calc z / 2 ≤ Real.exp α / 2 * Real.exp (κ / 17) := hexp
        _ ≤ max 1 (Real.exp α / 2) * Real.exp (κ / 17) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
        _ = _ := by
          congr 2
          field_simp
          norm_num
    · simp only [abs_zero]
      exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le

/-- The vacuum weight `1` is sub-Gaussian for every `Γ ≥ 0`. -/
theorem isSubGaussian_one (Γ η θ β : ℝ) (hΓ : 0 ≤ Γ) :
    IsSubGaussian Γ η θ β (fun _ => 1) := by
  refine ⟨1, one_pos, fun _ => 0, fun _ _ => rfl, fun φ => by simp, fun q _ => ?_⟩
  simp only [abs_zero]
  exact mul_nonneg hΓ (Real.exp_pos _).le

omit [Fintype V] in
/-- Every hard-core region weight in FS81 Theorem 5.1's activity range is
`(max 1 (e^α/2), 0, 1/17)`-sub-Gaussian at `κ⁻¹`. -/
theorem isSubGaussian_hardCoreSineGordon (A : Finset V) (α κ z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) (j : V) :
    IsSubGaussian (max 1 (Real.exp α / 2)) 0 (1 / 17) κ⁻¹ (hardCoreSineGordonInternal A z j) := by
  have hfun : hardCoreSineGordonInternal A z j =
      if j ∈ A then (fun φ => 1 + z * Real.cos φ) else (fun _ => 1) := by
    funext φ
    rw [sineGordonWeight_regionHardCore]
    split_ifs <;> rfl
  rw [hfun]
  split_ifs
  · exact isSubGaussian_one_add_mul_cos_activity α κ z hz hzκ
  · exact isSubGaussian_one _ _ _ _ (zero_le_one.trans (le_max_left _ _))

end FroehlichSpencer.BKT.Coulomb
