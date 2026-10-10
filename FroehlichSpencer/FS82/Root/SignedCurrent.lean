/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.RenormalizedFamily
public import FroehlichSpencer.FS82.Gaussian.GaugeAveraged
public import FroehlichSpencer.FS82.Currents.ComponentPackingFamily

/-!
# signed sums of currents and the vanishing of non-co-closed modes

A mode of the cosine expansion of `∏ᵢ (1 + Kᵢ cos α(ϱᵢ))` is a signed sum `Σᵢ σᵢ Jᵢ` with
`σᵢ ∈ {0, 1, −1}`.

When distinct currents of the family share no finite `Λ*` vertex, the divergence
of a signed sum at a vertex is the divergence of the single current meeting that vertex.

So a mode
that uses a current with nonzero divergence has nonzero divergence.

This is the reason only
co-closed currents survive the gauge average in FS82 (2.47).
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {B : Box 4}

/-- The integer value of a mode sign: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ −1`. -/
def signInt (σ : Sign) : ℤ :=
  if σ.val = 0 then 0 else if σ.val = 1 then 1 else -1

theorem signValue_eq_signInt (σ : Sign) : signValue σ = (signInt σ : ℝ) := by
  unfold signValue signInt
  split_ifs <;> simp

theorem signInt_eq_zero_iff (σ : Sign) : signInt σ = 0 ↔ σ = 0 := by
  revert σ
  decide

theorem signCoeff_zero_of_ne (σ : Sign) (hσ : σ ≠ 0) : signCoeff 0 σ = 0 := by
  have h : σ.val ≠ 0 := fun h0 => hσ (Fin.ext h0)
  simp [signCoeff, h]

theorem signCoeff_eq_of_zero (K K' : ℝ) : signCoeff K (0 : Sign) = signCoeff K' (0 : Sign) := by
  simp [signCoeff]

/-- The signed sum of a family of integer currents. -/
noncomputable def signedCurrent {ι : Type*} [Fintype ι] (J : ι → IntegerCurrent B)
    (σ : ι → Sign) : IntegerCurrent B :=
  ∑ i, signInt (σ i) • J i

theorem signedCurrent_apply {ι : Type*} [Fintype ι] (J : ι → IntegerCurrent B)
    (σ : ι → Sign) (e : Link B) :
    signedCurrent J σ e = ∑ i, signInt (σ i) * J i e := by
  simp [signedCurrent, Finsupp.finsetSum_apply]

theorem currentDivergence_zsmul (n : ℤ) (j : IntegerCurrent B)
    (v : SourceDualZeroCells B) :
    currentDivergence (n • j) v = (n : ℝ) * currentDivergence j v := by
  rw [currentDivergence_eq_sum_single (n • j), currentDivergence_eq_sum_single j,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [currentDivergence_single_scale e ((n • j) e), currentDivergence_single_scale e (j e)]
  simp only [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]
  ring

theorem currentDivergence_signedCurrent {ι : Type*} [Fintype ι]
    (J : ι → IntegerCurrent B) (σ : ι → Sign) (v : SourceDualZeroCells B) :
    currentDivergence (signedCurrent J σ) v =
      ∑ i, (signInt (σ i) : ℝ) * currentDivergence (J i) v := by
  unfold signedCurrent
  rw [currentDivergence_finset_sum]
  exact Finset.sum_congr rfl fun i _ => currentDivergence_zsmul _ _ _

/-- A signed sum of co-closed currents is co-closed. -/
theorem signedCurrent_divergence_eq_zero {ι : Type*} [Fintype ι]
    (J : ι → IntegerCurrent B) (σ : ι → Sign)
    (hclosed : ∀ i, σ i ≠ 0 → currentDivergence (J i) = 0) :
    currentDivergence (signedCurrent J σ) = 0 := by
  funext v
  rw [currentDivergence_signedCurrent]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hσ : σ i = 0
  · simp [(signInt_eq_zero_iff (σ i)).mpr hσ]
  · rw [hclosed i hσ]
    simp

/-- A vertex with nonzero divergence is met by a support link of the current. -/
theorem exists_incident_support_of_divergence_ne_zero (j : IntegerCurrent B)
    (v : SourceDualZeroCells B) (hv : currentDivergence j v ≠ 0) :
    ∃ e ∈ j.support, linkIncidentAt e v := by
  by_contra hno
  apply hv
  rw [currentDivergence_eq_sum_single]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [currentDivergence_single_scale]
  by_cases he : j e = 0
  · simp [he]
  · have hinc : ¬ linkIncidentAt e v := fun hinc =>
      hno ⟨e, Finsupp.mem_support_iff.mpr he, hinc⟩
    have hzero : currentDivergence (Finsupp.single e (1 : ℤ)) v = 0 := by
      by_contra hne
      exact hinc hne
    simp [hzero]

/-- **Vanishing of non-co-closed modes (2.47).** If distinct currents of the family share no
finite vertex, a signed sum that uses a current with nonzero divergence has nonzero divergence. -/
theorem signedCurrent_divergence_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → IntegerCurrent B)
    (hsep : ∀ i j, i ≠ j → ∀ e ∈ (J i).support, ∀ f ∈ (J j).support,
      ¬ linksShareFiniteVertex e f)
    (σ : ι → Sign) (i₀ : ι) (hσ : σ i₀ ≠ 0)
    (hdiv : currentDivergence (J i₀) ≠ 0) :
    currentDivergence (signedCurrent J σ) ≠ 0 := by
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hdiv
  have hv' : currentDivergence (J i₀) v ≠ 0 := by simpa using hv
  obtain ⟨e, he, heinc⟩ := exists_incident_support_of_divergence_ne_zero (J i₀) v hv'
  have hother : ∀ j, j ≠ i₀ → currentDivergence (J j) v = 0 := by
    intro j hj
    by_contra hne
    obtain ⟨f, hf, hfinc⟩ := exists_incident_support_of_divergence_ne_zero (J j) v hne
    exact hsep i₀ j (Ne.symm hj) e he f hf ⟨v, heinc, hfinc⟩
  intro hzero
  have hval := congrFun hzero v
  rw [currentDivergence_signedCurrent,
    Finset.sum_eq_single i₀ (fun j _ hj => by rw [hother j hj]; simp)
      (fun h => absurd (Finset.mem_univ i₀) h)] at hval
  have hsign : (signInt (σ i₀) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => hσ ((signInt_eq_zero_iff _).mp h)
  simp only [Pi.zero_apply] at hval
  exact hv' ((mul_eq_zero.mp hval).resolve_left hsign)

/-! ## The physical mode vector of a signed sum -/

theorem latticeIntegerModeVector_signedCurrent {ι : Type*} [Fintype ι]
    (J : ι → IntegerCurrent B) (σ : ι → Sign) :
    latticeIntegerModeVector (B := B) (signedCurrent J σ) =
      ∑ i, (signInt (σ i) : ℝ) • latticeIntegerModeVector (B := B) (J i) := by
  ext e
  rw [latticeIntegerModeVector_apply, latticePhysicalMode, signedCurrent_apply]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    latticeIntegerModeVector_apply, latticePhysicalMode]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
