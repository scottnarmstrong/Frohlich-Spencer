/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.State
public import FroehlichSpencer.BKT.SOS.Literal.CombLimit

/-!
# FS81's comb (7.16) at a finite cutoff, and its limit (the finite comb construction)

FS81 write the state (7.16) with the formal comb `∏_{j∈A}[1 + 2Σ_{q≥1} cos(2πqφ(j))]` against the
zero-mass measure (FS81). At cutoff `N` the comb is `regionComb A N`,
`∏_{j∈A} D_N(2πφ(j))` with `D_N(ψ) = 1 + 2Σ_{q=1}^N cos(qψ)`. The cutoff functional
`F ↦ ∫ regionComb · F dμ_{I_β,Ω} / ∫ regionComb dμ_{I_β,Ω}` is signed (`D_N` changes sign).

* `integral_regionComb_mul_eq_sum`: the pairing of `regionComb A N` with an integrable density
  `f` is the box sum `Σ_{q ∈ [−N,N]^A} f̂(q ⊕ 0)` of Fourier coefficients.
* `tendsto_regionCombPairing`: for Schwartz `f` the pairings converge to
  `Σ_{n ∈ ℤ^A} ∫ f(n ⊕ y) dy` (partial Poisson summation, `tsum_fourier_extZero_eq_tsum_marginal`).
* `tendsto_combCutoffMoment`: for `|ε| ≤ β/2`, FS81's cutoff moments of `e^{ε[φ(u)−φ(v)]}`
  converge to the moment of the literal state `literalState L β A`. So the literal state is the
  meaning of (7.16) on the box. The normalization `N_Ω` of `dμ_{I_β,Ω}` cancels in the ratio.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Complex Filter Topology
open scoped SchwartzMap
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening

section Region

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- FS81's comb (7.16) on a region at cutoff `N`: `∏_{j∈A} [1 + 2Σ_{q=1}^N cos(2πq y_j)]`. -/
def regionComb (A : Finset ι) (N : ℕ) (y : ι → ℝ) : ℝ :=
  ∏ x ∈ A, dirichletComb N (2 * Real.pi * y x)

/-- **The Fourier expansion of the comb on a region.** -/
theorem regionComb_eq_sum (A : Finset ι) (N : ℕ) (y : ι → ℝ) :
    ((regionComb A N y : ℝ) : ℂ) = ∑ q ∈ (freqBox N : Finset ({x // x ∈ A} → ℤ)),
      cexp (((-2 * Real.pi * ∑ x, y x * (extZeroInt (· ∈ A) q x : ℝ) : ℝ) : ℂ) * I) := by
  unfold regionComb freqBox
  rw [Complex.ofReal_prod, ← Finset.prod_coe_sort A]
  simp_rw [← sum_Icc_exp_eq_dirichletComb]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  congr 1
  have h := sum_mul_extZero (· ∈ A) y (fun i => (q i : ℝ))
  rw [extZero_intCast] at h
  rw [h]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  ext x
  simp only [Finset.mem_univ]

/-- **The comb pairing is a finite sum of Fourier coefficients.** -/
theorem integral_regionComb_mul_eq_sum (A : Finset ι) (N : ℕ) {f : (ι → ℝ) → ℂ}
    (hf : Integrable f) :
    ∫ y, ((regionComb A N y : ℝ) : ℂ) * f y =
      ∑ q ∈ (freqBox N : Finset ({x // x ∈ A} → ℤ)),
        multiEuclideanFourierCoefficient f (extZeroInt (· ∈ A) q) := by
  simp_rw [regionComb_eq_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun q _ => integrable_char_mul hf _]
  rfl

/-- **The comb (7.16) on `A` inside the continuous field**: the pairings of the cutoff comb with a
Schwartz density converge to the lattice sum of its marginal over the coordinates off `A`. -/
theorem tendsto_regionCombPairing (A : Finset ι) (f : 𝓢(ι → ℝ, ℂ)) :
    Tendsto (fun N : ℕ => ∫ y, ((regionComb A N y : ℝ) : ℂ) * f y) atTop
      (𝓝 (∑' n : {x // x ∈ A} → ℤ, marginalPi (· ∈ A) f (fun i => (n i : ℝ)))) := by
  obtain ⟨heq, hsum, -⟩ := tsum_fourier_extZero_eq_tsum_marginal (· ∈ A) f
  rw [← heq]
  have hmono : Monotone (freqBox (ι := {x // x ∈ A})) := by
    intro N M hNM q hq
    simp only [freqBox, Fintype.mem_piFinset, Finset.mem_Icc] at hq ⊢
    intro x
    have := hq x
    constructor <;> omega
  have hcover : ∀ q : {x // x ∈ A} → ℤ, ∃ N, q ∈ freqBox N := by
    intro q
    refine ⟨∑ x, (q x).natAbs, ?_⟩
    simp only [freqBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro x
    have h1 : (q x).natAbs ≤ ∑ y, (q y).natAbs :=
      Finset.single_le_sum (f := fun y => (q y).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x)
    omega
  exact (hsum.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcover)).congr
    fun N => (integral_regionComb_mul_eq_sum A N f.integrable).symm

end Region

variable {L : ℕ}

/-- FS81's cutoff moment of `e^{ε[φ(u)−φ(v)]}` in (7.16) on the box `Ω = Site L`: the comb on `A`
at cutoff `N` against the zero-exterior `I_β`-weight. -/
def combCutoffMoment (L : ℕ) (β : ℝ) (A : Finset (Site L)) (u v : Site L) (ε : ℝ) (N : ℕ) : ℝ :=
  (∫ y, regionComb A N y * (Real.exp (ε * (y u - y v)) * boxWeight L β y)) /
    ∫ y, regionComb A N y * boxWeight L β y

/-- **The literal state is the limit of FS81's cutoff comb (7.16)**: for `|ε| ≤ β/2` the cutoff
moments converge to the moment of `literalState L β A`. -/
theorem tendsto_combCutoffMoment (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (Site L)} {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) {ε : ℝ} (hε : |ε| ≤ β / 2) :
    Tendsto (combCutoffMoment L β A u v ε) atTop
      (𝓝 (literalMomentExt L β A u v ε).toReal) := by
  have hc0 : ∀ e : SquareZeroBond L, |(0 : SquareZeroBond L → ℝ) e| ≤ β / 2 := fun e => by
    simp only [Pi.zero_apply, abs_zero]; positivity
  have hct : ∀ e, |dipoleTilt hL u v ε e| ≤ β / 2 := fun e =>
    (abs_dipoleTilt_le hL u v ε e).trans hε
  obtain ⟨f0, hf0⟩ := exists_sosDensityCoords_schwartz hL hβ hβ1 hc0
  obtain ⟨ft, hft⟩ := exists_sosDensityCoords_schwartz hL hβ hβ1 hct
  have hreal : ∀ (g : (Site L → ℝ) → ℝ) (f : 𝓢(Site L → ℝ, ℂ)), (∀ y, f y = ((g y : ℝ) : ℂ)) →
      ∀ N : ℕ, ∫ y, regionComb A N y * g y = (∫ y, ((regionComb A N y : ℝ) : ℂ) * f y).re := by
    intro g f hfg N
    simp_rw [hfg, ← Complex.ofReal_mul]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hlim : ∀ f : 𝓢(Site L → ℝ, ℂ), Tendsto
      (fun N : ℕ => (∫ y, ((regionComb A N y : ℝ) : ℂ) * f y).re) atTop
      (𝓝 (∑' n : {x // x ∈ A} → ℤ, marginalPi (· ∈ A) f (fun i => (n i : ℝ))).re) :=
    fun f => (Complex.continuous_re.tendsto _).comp (tendsto_regionCombPairing A f)
  have hnum := hlim ft
  have hden := hlim f0
  rw [show (ft : (Site L → ℝ) → ℂ) = sosDensityCoords L β (dipoleTilt hL u v ε) from funext hft]
    at hnum
  rw [show (f0 : (Site L → ℝ) → ℂ) = sosDensityCoords L β 0 from funext hf0] at hden
  simp_rw [marginal_dipoleTilt hL hβ.le hu hv] at hnum
  simp_rw [marginal_zero hβ.le] at hden
  rw [← Complex.ofReal_tsum, Complex.ofReal_re] at hnum hden
  have hratio := hnum.div hden (tsum_literalWeight_pos hL hβ hβ1 A).ne'
  rw [literalMomentExt_eq hL hβ hβ1 hu hv hε, ENNReal.toReal_ofReal (div_nonneg
    (tsum_nonneg fun n => mul_nonneg (Real.exp_pos _).le (literalWeight_pos hL hβ hβ1 A n).le)
    (tsum_literalWeight_pos hL hβ hβ1 A).le)]
  refine hratio.congr fun N => ?_
  rw [Pi.div_apply]
  unfold combCutoffMoment
  rw [hreal _ ft (fun y => by rw [hft, sosDensityCoords_dipoleTilt hL hβ.le]) N,
    hreal _ f0 (fun y => by rw [hf0, sosDensityCoords_zero_eq hβ.le]) N]
  simp_rw [hft, hf0]

end FroehlichSpencer.BKT.SOS.Literal

end
