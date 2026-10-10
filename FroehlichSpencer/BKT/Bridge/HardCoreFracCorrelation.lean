/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.HardCoreFracCorrelation
public import FroehlichSpencer.BKT.Coulomb.TheoremBLimit
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBGeneral
public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
The `hardCoreFracCorrelation β z hz ξ Λ a b` ) is
* the internal free fractional correlation `Coulomb.freeFracCorrInternal (Subtype.val : Λ → ℤ × ℤ)
  β z ξ a b` (`hardCoreFracCorrelation_eq`): the charge representation
  `e^{-βξ²⟨f, Cf⟩/2} ⟨cosh (ξβ⟨q, Cf⟩)⟩_Λ` with `f = δ_a - δ_b`, by expanding
  `E(q + ξ f) = E(q) + ξ⟨q, Cf⟩ + ξ² E(f)` and symmetrizing under `q ↦ -q`;
* the Condition-λ region correlation of the hard-core law (`hardCoreFracCorrelation_eq_region`).

For `0 ≤ z ≤ K e^{εβ}` the hard-core law satisfies Condition λ with `C = max(1, K/2)`, `α = 0`
(`conditionLambda_hardCore_activity`), so the internal
`coulombB_conditionLambda_free_fullRange_general` gives the finite-volume bound of FS81 (5.27)
(`finite_bound_activityRange`), with the ℓ¹ profile converted to `|x|^{-p}`
(`l1Profile_le_euclidPower`).

The net lemmas `tendsto_val_regions`, `neBot_regions` and
`hardCoreFracCorrelation_self_mem` serve the infinite-volume root.

The roots
`hardCoreGas_fracCorrelation_upper_bound` and `hardCoreGas_fracCorrelationLimit_upper_bound` (FS81
Theorem B, hard-core gas) are proved in `BKT/Provider/`.

The box cover
lemma is source's installed `Bridge.HardCoreSecondMomentFree.subset_box`, and the nonnegativity of
the hard-core law the internal `Coulomb.hardCoreWeight_nonneg`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Generic.Marked (dipoleMark dipoleGap dipoleGap_pos)

/-! ### FS81 (1.23) is the internal free fractional correlation -/

theorem coulombPotential_eq (x : ℤ × ℤ) : coulombPotential x = -potentialKernelInternal x := rfl

section Charge

variable (Λ : Finset (ℤ × ℤ))

/-- `∑_{i,j} ρ(i) σ(j) C(i - j)`. -/
def pairC (ρ σ : Λ → ℝ) : ℝ := ∑ i, ∑ j, ρ i * σ j * coulombPotential ((i : ℤ × ℤ) - j)

theorem pairC_symm (ρ σ : Λ → ℝ) : pairC Λ ρ σ = pairC Λ σ ρ := by
  unfold pairC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [coulombPotential_eq, coulombPotential_eq, ← potentialKernel_neg, neg_sub]
  ring

theorem pairC_add_left (ρ ρ' σ : Λ → ℝ) : pairC Λ (ρ + ρ') σ = pairC Λ ρ σ + pairC Λ ρ' σ := by
  unfold pairC
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]
  ring

theorem pairC_smul_right (c : ℝ) (ρ σ : Λ → ℝ) : pairC Λ ρ (c • σ) = c * pairC Λ ρ σ := by
  unfold pairC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem pairC_neg_left (ρ σ : Λ → ℝ) : pairC Λ (-ρ) σ = -pairC Λ ρ σ := by
  unfold pairC
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply]
  ring

theorem pairC_add_right (ρ σ σ' : Λ → ℝ) : pairC Λ ρ (σ + σ') = pairC Λ ρ σ + pairC Λ ρ σ' := by
  rw [pairC_symm, pairC_add_left, pairC_symm Λ σ, pairC_symm Λ σ']

theorem pairC_smul_left (c : ℝ) (ρ σ : Λ → ℝ) : pairC Λ (c • ρ) σ = c * pairC Λ ρ σ := by
  rw [pairC_symm, pairC_smul_right, pairC_symm]

/-- `E(ρ + c σ) = E(ρ) + c ⟨ρ, Cσ⟩ + c² E(σ)` (as `2E = pairC ρ ρ`). -/
theorem pairC_add_smul (c : ℝ) (ρ σ : Λ → ℝ) :
    pairC Λ (ρ + c • σ) (ρ + c • σ) =
      pairC Λ ρ ρ + 2 * c * pairC Λ ρ σ + c ^ 2 * pairC Λ σ σ := by
  rw [pairC_add_left, pairC_add_right, pairC_add_right, pairC_smul_left, pairC_smul_left,
    pairC_smul_right, pairC_smul_right, pairC_symm Λ σ ρ]
  ring

/-- The exponential bookkeeping of `E(q + ξ f)`. -/
theorem exp_split (β ξ P R Q w : ℝ) :
    w * Real.exp (-β * ((P + 2 * ξ * R + ξ ^ 2 * Q) / 2)) =
      Real.exp (-(β * ξ ^ 2 * Q / 2)) *
        (w * Real.exp (-β * (P / 2)) * Real.exp (-(β * ξ * R))) := by
  rw [show Real.exp (-(β * ξ ^ 2 * Q / 2)) * (w * Real.exp (-β * (P / 2)) * Real.exp (-(β * ξ * R)))
      = w * Real.exp (-(β * ξ ^ 2 * Q / 2) + -β * (P / 2) + -(β * ξ * R)) by
    rw [Real.exp_add, Real.exp_add]; ring]
  congr 2
  ring

/-- The internal free charge energy is `½ ⟨q, C q⟩`. -/
theorem chargeEnergy_eq (q : Λ → ℤ) :
    chargeEnergyInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) q =
      pairC Λ (fun j => (q j : ℝ)) (fun j => (q j : ℝ)) / 2 := by
  unfold chargeEnergyInternal
  rw [sum_mul_neg_freePotentialOp]
  congr 1
  unfold pairC
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coulombPotential_eq]
  ring

theorem freeQuad_eq (f : Λ → ℝ) :
    freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f = pairC Λ f f := by
  unfold freeQuadInternal
  rw [sum_mul_neg_freePotentialOp]
  unfold pairC
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coulombPotential_eq]
  ring

theorem freeChargePairing_eq (f : Λ → ℝ) (q : Λ → ℤ) :
    freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) f q = pairC Λ (fun j => (q j : ℝ)) f := by
  unfold freeChargePairingInternal
  rw [sum_mul_neg_freePotentialOp]
  unfold pairC
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coulombPotential_eq]
  ring

/--
The configurations of the definition are the internal `chargeConfigsInternal Λ 1`.
-/
theorem configs_eq :
    (Fintype.piFinset fun _ : Λ => Finset.Icc (-1 : ℤ) 1) = chargeConfigsInternal Λ 1 := by
  simp [chargeConfigsInternal]

theorem mem_configs {q : Λ → ℤ} (hq : q ∈ chargeConfigsInternal Λ 1) (j : Λ) :
    q j = -1 ∨ q j = 0 ∨ q j = 1 := by
  have := Fintype.mem_piFinset.mp hq j
  simp only [Finset.mem_Icc, Nat.cast_one] at this
  omega

/--
On the configurations, the weight times the Boltzmann factor is the internal gas
weight.
-/
theorem weight_eq (β z : ℝ) {q : Λ → ℤ} (hq : q ∈ chargeConfigsInternal Λ 1) :
    (if ∑ j, q j = 0 then ∏ j, (if q j = 0 then (1 : ℝ) else z / 2) else 0) *
        Real.exp (-β * (pairC Λ (fun j => (q j : ℝ)) (fun j => (q j : ℝ)) / 2)) =
      gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
        (fun _ => hardCoreWeightInternal z) q := by
  unfold gasWeightInternal
  rw [chargeEnergy_eq]
  have hp : ∏ j, (if q j = 0 then (1 : ℝ) else z / 2) = ∏ j, hardCoreWeightInternal z (q j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold hardCoreWeightInternal
    rcases mem_configs Λ hq j with h | h | h <;> simp [h]
  split_ifs
  · rw [hp]
  · rw [zero_mul]

/-- Charge conjugation: an even weight against `e^{-X}` with `X` odd equals the weight against
`cosh X`. -/
theorem sum_exp_neg_eq_sum_cosh (G X : (Λ → ℤ) → ℝ) (hG : ∀ q, G (-q) = G q)
    (hX : ∀ q, X (-q) = -X q) :
    ∑ q ∈ chargeConfigsInternal Λ 1, G q * Real.exp (-X q) =
      ∑ q ∈ chargeConfigsInternal Λ 1, G q * Real.cosh (X q) := by
  have hflip : ∑ q ∈ chargeConfigsInternal Λ 1, G q * Real.exp (-X q) =
      ∑ q ∈ chargeConfigsInternal Λ 1, G q * Real.exp (X q) := by
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
    · intro q _; exact neg_neg q
    · intro q _; exact neg_neg q
    · intro q _
      rw [hG, hX]
  have hc : ∀ q, G q * Real.cosh (X q) = (G q * Real.exp (X q) + G q * Real.exp (-X q)) / 2 :=
    fun q => by rw [Real.cosh_eq]; ring
  rw [Finset.sum_congr rfl fun q _ => hc q, ← Finset.sum_div, Finset.sum_add_distrib, ← hflip]
  ring

/-- **FS81 (1.23) for the hard-core gas is the internal free fractional correlation.** -/
theorem hardCoreFracCorrelation_eq (β z : ℝ) (hz : 0 ≤ z) (ξ : ℝ) (a b : Λ) :
    hardCoreFracCorrelation β z hz ξ Λ a b =
      freeFracCorrInternal (Subtype.val : Λ → ℤ × ℤ) β z ξ a b := by
  set f₀ : Λ → ℝ := dipoleRealInternal a b with hf₀
  have hf : (fun j : Λ => (if j = a then ξ else 0) - (if j = b then ξ else 0)) = ξ • f₀ := by
    funext j
    simp only [hf₀, dipoleRealInternal, dipoleMark, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  set G : (Λ → ℤ) → ℝ := gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
    (fun _ => hardCoreWeightInternal z) with hG
  set X : (Λ → ℤ) → ℝ := fun q => β * ξ * pairC Λ (fun j => (q j : ℝ)) f₀ with hX
  have hGneg : ∀ q, G q = G (-q) := fun q =>
    (gasWeight_neg _ β _ (fun _ n => hardCoreWeight_neg z n) q).symm
  have hXneg : ∀ q, X (-q) = -X q := by
    intro q
    simp only [hX]
    have : (fun j => (((-q) j : ℤ) : ℝ)) = -(fun j => (q j : ℝ)) := by funext j; simp
    rw [this, pairC_neg_left]
    ring
  -- the numerator
  have hnum : ∑ q ∈ Fintype.piFinset (fun _ : Λ => Finset.Icc (-1 : ℤ) 1),
      (if ∑ j, q j = 0 then ∏ j, (if q j = 0 then (1 : ℝ) else z / 2) else 0) *
        Real.exp (-β * (pairC Λ (fun j => (q j : ℝ) + (ξ • f₀) j)
          (fun j => (q j : ℝ) + (ξ • f₀) j) / 2)) =
      Real.exp (-(β * ξ ^ 2 * pairC Λ f₀ f₀ / 2)) *
        ∑ q ∈ chargeConfigsInternal Λ 1, G q * Real.cosh (X q) := by
    rw [configs_eq, ← sum_exp_neg_eq_sum_cosh Λ G X (fun q => (hGneg q).symm) hXneg,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hsplit : (fun j => (q j : ℝ) + (ξ • f₀) j) = (fun j => (q j : ℝ)) + ξ • f₀ := rfl
    have hw := weight_eq Λ β z hq
    rw [← hG] at hw
    rw [hsplit, pairC_add_smul, ← hw]
    simp only [hX]
    exact exp_split β ξ _ _ _ _
  have hden : ∑ q ∈ Fintype.piFinset (fun _ : Λ => Finset.Icc (-1 : ℤ) 1),
      (if ∑ j, q j = 0 then ∏ j, (if q j = 0 then (1 : ℝ) else z / 2) else 0) *
        Real.exp (-β * (pairC Λ (fun j => (q j : ℝ)) (fun j => (q j : ℝ)) / 2)) =
      gasPartitionInternal 1 (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
        (fun _ => hardCoreWeightInternal z) := by
    rw [configs_eq, gasPartitionInternal]
    exact Finset.sum_congr rfl fun q hq => weight_eq Λ β z hq
  have hdef : hardCoreFracCorrelation β z hz ξ Λ a b =
      (∑ q ∈ Fintype.piFinset (fun _ : Λ => Finset.Icc (-1 : ℤ) 1),
        (if ∑ j, q j = 0 then ∏ j, (if q j = 0 then (1 : ℝ) else z / 2) else 0) *
          Real.exp (-β * (pairC Λ (fun j => (q j : ℝ) + (ξ • f₀) j)
            (fun j => (q j : ℝ) + (ξ • f₀) j) / 2))) /
      ∑ q ∈ Fintype.piFinset (fun _ : Λ => Finset.Icc (-1 : ℤ) 1),
        (if ∑ j, q j = 0 then ∏ j, (if q j = 0 then (1 : ℝ) else z / 2) else 0) *
          Real.exp (-β * (pairC Λ (fun j => (q j : ℝ)) (fun j => (q j : ℝ)) / 2)) := by
    rw [← hf]
    rfl
  rw [hdef, hnum, hden, freeFracCorrInternal, freeGasExpectationInternal, gasExpectationInternal,
    freeQuad_eq, mul_div_assoc]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [freeChargePairing_eq, hG]
  simp only [hX, hf₀]
  ring_nf

end Charge

/-! ### Profiles and nets -/

theorem natAbs_sum_eq (x : ℤ × ℤ) :
    (((x.1 - (0 : ℤ × ℤ).1).natAbs + (x.2 - (0 : ℤ × ℤ).2).natAbs : ℕ) : ℝ) =
      |(x.1 : ℝ)| + |(x.2 : ℝ)| := by
  simp [Nat.cast_natAbs]

theorem euclid_pos {x : ℤ × ℤ} (hx : x ≠ 0) : 0 < Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) := by
  apply Real.sqrt_pos.2
  rcases x with ⟨a, b⟩
  have : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by simp [h.1, h.2])
  rcases this with h | h
  · have : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
    simp only
    nlinarith [sq_nonneg (b : ℝ)]
  · have : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
    simp only
    nlinarith [sq_nonneg (a : ℝ)]

theorem euclid_le_abs_add (x : ℤ × ℤ) :
    Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ≤ |(x.1 : ℝ)| + |(x.2 : ℝ)| := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (x.1 : ℝ), abs_nonneg (x.2 : ℝ), sq_abs (x.1 : ℝ), sq_abs (x.2 : ℝ),
    mul_nonneg (abs_nonneg (x.1 : ℝ)) (abs_nonneg (x.2 : ℝ))]

/-- `(|x|₁ + 1)^{-p} ≤ |x|^{-p}` for `x ≠ 0`, `p ≥ 0`. -/
theorem l1Profile_le_euclidPower {x : ℤ × ℤ} (hx : x ≠ 0) {p : ℝ} (hp : 0 ≤ p) :
    ((((x.1 - (0 : ℤ × ℤ).1).natAbs + (x.2 - (0 : ℤ × ℤ).2).natAbs : ℕ) : ℝ) + 1) ^ (-p) ≤
      Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-p) := by
  rw [natAbs_sum_eq]
  exact Real.rpow_le_rpow_of_nonpos (euclid_pos hx) (by linarith [euclid_le_abs_add x])
    (by linarith)

/-- At a single site the fractional dipole vanishes, and `G_{ξ,Λ}(a, a) = Z/Z ∈ [0, 1]`. -/
theorem hardCoreFracCorrelation_self_mem (β z : ℝ) (hz : 0 ≤ z) (ξ : ℝ) (Λ : Finset (ℤ × ℤ))
    (a : Λ) : hardCoreFracCorrelation β z hz ξ Λ a a ∈ Set.Icc 0 1 := by
  unfold hardCoreFracCorrelation
  simp only [sub_self, add_zero]
  generalize (∑ q ∈ Fintype.piFinset fun _ : Λ => Finset.Icc (-1 : ℤ) 1,
    (if ∑ j, q j = 0 then ∏ j, (if q j = 0 then (1 : ℝ) else z / 2) else 0) *
      Real.exp (-β * ((∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) *
        coulombPotential ((i : ℤ × ℤ) - j)) / 2))) = d
  by_cases hd : d = 0
  · simp [hd]
  · simp [hd]

/-- The subtype of indices whose region contains `0` and `x` has a non-trivial `atTop`, and its
inclusion into `ℕ` tends to `atTop`, as soon as the regions tend to `atTop`. -/
theorem tendsto_val_regions {Λs : ℕ → Finset (ℤ × ℤ)} (hΛs : Tendsto Λs atTop atTop)
    (x : ℤ × ℤ) :
    Tendsto (Subtype.val : {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k} → ℕ) atTop atTop := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_atTop.1 hΛs) {0, x})
  have hmem : ∀ k, K ≤ k → (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k := fun k hk =>
    ⟨hK k hk (by simp), hK k hk (by simp)⟩
  have : Nonempty {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k} := ⟨⟨K, hmem K le_rfl⟩⟩
  refine tendsto_atTop_atTop.2 fun b => ⟨⟨max b K, hmem _ (le_max_right _ _)⟩, fun k hk => ?_⟩
  exact (le_max_left b K).trans hk

theorem neBot_regions {Λs : ℕ → Finset (ℤ × ℤ)} (hΛs : Tendsto Λs atTop atTop) (x : ℤ × ℤ) :
    (atTop : Filter {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k}).NeBot := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_atTop.1 hΛs) {0, x})
  have : Nonempty {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k} :=
    ⟨⟨K, hK K le_rfl (by simp), hK K le_rfl (by simp)⟩⟩
  exact atTop_neBot

/-! ### The bridge to the Condition-λ region correlation -/

section Bridge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem hardCoreWeight_eq_zero {z : ℝ} {n : ℤ} (hn : n ∉ Finset.Icc (-1 : ℤ) 1) :
    hardCoreWeightInternal z n = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  unfold hardCoreWeightInternal
  have h0 : n ≠ 0 := by omega
  have h1 : ¬ (n = 1 ∨ n = -1) := by omega
  simp only [h0, h1, ↓reduceIte]

/-- The full gas sum of a hard-core law is the finite configuration sum. -/
theorem tsum_gasWeight_hardCore_mul (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ z : ℝ) (F : (V → ℤ) → ℝ) :
    ∑' q : V → ℤ, gasWeightInternal T κ (fun _ => hardCoreWeightInternal z) q * F q =
      ∑ q ∈ chargeConfigsInternal V 1,
        gasWeightInternal T κ (fun _ => hardCoreWeightInternal z) q * F q := by
  refine tsum_eq_sum fun q hq => ?_
  obtain ⟨j, hj⟩ : ∃ j, q j ∉ Finset.Icc (-1 : ℤ) 1 := by
    by_contra h
    push Not at h
    exact hq (Fintype.mem_piFinset.2 fun j => by simpa using h j)
  unfold gasWeightInternal
  split_ifs
  · rw [Finset.prod_eq_zero (Finset.mem_univ j) (hardCoreWeight_eq_zero hj)]
    ring
  · ring

/-- The internal free hard-core correlation is the Condition-λ correlation of the hard-core law. -/
theorem freeFracCorr_eq_conditionLambda (pos : V → ℤ × ℤ) (κ z ξ : ℝ) (o x : V) :
    freeFracCorrInternal pos κ z ξ o x =
      freeConditionLambdaFracCorrInternal pos κ (hardCoreWeightInternal z) ξ o x := by
  unfold freeFracCorrInternal freeConditionLambdaFracCorrInternal freeGasExpectationInternal
    gasExpectationInternal fullGasExpectationInternal fullGasPartitionInternal gasPartitionInternal
  congr 2
  · rw [tsum_gasWeight_hardCore_mul]
  · have h := tsum_gasWeight_hardCore_mul (freePotentialOpInternal pos) κ z (fun _ => 1)
    simp only [mul_one] at h
    rw [h]

end Bridge

/-- **The bridge**: FS81 (1.23) for the hard-core gas is the Condition-λ region correlation of the
hard-core law. -/
theorem hardCoreFracCorrelation_eq_region (β z : ℝ) (hz : 0 ≤ z) (ξ : ℝ)
    (Λ : Finset (ℤ × ℤ)) (a b : Λ) :
    hardCoreFracCorrelation β z hz ξ Λ a b =
      regionConditionLambdaFracCorrInternal Λ β (hardCoreWeightInternal z) ξ a b := by
  rw [hardCoreFracCorrelation_eq Λ β z hz ξ a b, freeFracCorr_eq_conditionLambda]
  unfold regionConditionLambdaFracCorrInternal
  simp only [a.2, b.2, and_self, ↓reduceDIte]

/-! ### Condition λ for the hard-core law in the activity range -/

/-- For `0 ≤ z ≤ K e^{εβ}`, the hard-core law (1.10) satisfies Condition λ with `C = max(1, K/2)`,
`α = 0` and the same `ε`. -/
theorem conditionLambda_hardCore_activity {z K ε β : ℝ} (hz : 0 ≤ z)
    (hzK : z ≤ K * Real.exp (ε * β)) :
    ConditionLambdaInternal (max 1 (K / 2)) 0 ε β (hardCoreWeightInternal z) := by
  refine ⟨hardCoreWeight_neg z, fun n => ?_⟩
  unfold hardCoreWeightInternal
  split_ifs with h0 h1
  · subst h0
    simp
  · have hn : (n : ℝ) ^ 2 = 1 := by rcases h1 with rfl | rfl <;> norm_num
    rw [hn, abs_of_nonneg (by positivity), mul_one, zero_add]
    have h2 : z / 2 ≤ K / 2 * Real.exp (ε * β) := by linarith
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  · simp only [abs_zero]
    exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le

theorem hardCoreWeight_zero (z : ℝ) : hardCoreWeightInternal z 0 = 1 := by
  simp [hardCoreWeightInternal]

/-! ### The roots -/

/-- The finite-volume bound in the activity range, at the sites `0, x` of `Λ`. -/
theorem finite_bound_activityRange {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) {ε : ℝ}
    (hε : ε < 1 / 16) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ β : ℝ, κ₀ < β →
      ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ K * Real.exp (ε * β) →
      ∀ (Λ : Finset (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ Λ) (x : ℤ × ℤ) (hx : x ∈ Λ), x ≠ 0 →
        0 ≤ hardCoreFracCorrelation β z hz ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ∧
          hardCoreFracCorrelation β z hz ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ≤
            2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * β) *
              Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^
                (-(c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β)) := by
  obtain ⟨c, hc, hgen⟩ := coulombB_conditionLambda_free_fullRange_general
  refine ⟨c, hc, fun K => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := hgen (max 1 (K / 2)) 0 ε (zero_le_one.trans (le_max_left _ _)) le_rfl
    hε 1 one_pos (dipoleGap ξ) (dipoleGap_pos hξ0 hξ1)
  refine ⟨κ₀, hκ₀, fun β hβ z hz hzK Λ h0 x hx hx0 => ?_⟩
  have hδ : 0 < 1 / 16 - max ε 0 := by
    have := max_lt hε (by norm_num : (0 : ℝ) < 1 / 16)
    linarith
  have hb := hF β hβ (hardCoreWeightInternal z) (conditionLambda_hardCore_activity hz hzK)
    (hardCoreWeight_nonneg hz) (hardCoreWeight_zero z).symm.le Λ ξ 0 x h0 hx (Ne.symm hx0)
    hξ0 hξ1 le_rfl
  rw [hardCoreFracCorrelation_eq_region]
  refine ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  have hp : 0 ≤ c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β := by
    have := dipoleGap_pos hξ0 hξ1
    have : 0 < β := hκ₀.trans hβ
    positivity
  exact l1Profile_le_euclidPower hx0 hp

theorem tendsto_exponent_activityRange {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) {ε : ℝ} (hε : ε < 1 / 16) :
    Tendsto (fun β => c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β) atTop atTop := by
  have := dipoleGap_pos hξ0 hξ1
  have hδ : 0 < 1 / 16 - max ε 0 := by
    have := max_lt hε (by norm_num : (0 : ℝ) < 1 / 16)
    linarith
  exact tendsto_id.const_mul_atTop (by positivity)

end FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation

end
