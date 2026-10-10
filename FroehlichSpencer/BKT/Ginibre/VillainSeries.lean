/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Fourier.PeriodizedGaussian
public import FroehlichSpencer.BKT.Rotator.Ginibre.Positivity
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Truncated duplicated Villain series

For `0 < β₂ ≤ β₁`, put `a = (1/β₁ + 1/β₂)/8` and `c = (1/β₂ − 1/β₁)/4 ≥ 0`. In the sum–difference
frequencies `(s, t) = (p + q, p − q)` the product of the Villain Fourier coefficients is
`e^{−p²/(2β₁) − q²/(2β₂)} = e^{−a(s² + t²) + c s t}` (and `s + t` is even). Truncating `|s|, |t| ≤ N`
and the exponential series of `e^{c s t}` at order `N` gives finite sums that converge, boundedly,
to `villainWeight β₁ φ · villainWeight β₂ φ'` (up to the Poisson normalizations). The one-copy
series `Σ_{|p| ≤ N} e^{−p²/(2β)} e^{ipφ}` likewise converges boundedly to `villainWeight β φ`.
-/

@[expose] public section

open Filter Topology
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

open FroehlichSpencer.BKT.VillainWeight

/-- The Poisson normalization `(2πβ)^{−1/2}` of the Villain Fourier series. -/
def villainNorm (β : ℝ) : ℝ :=
  (2 * π * β) ^ (-(1 / 2 : ℝ))

/-- The coefficient `a` of the diagonal quadratic part. -/
def villainA (β₁ β₂ : ℝ) : ℝ :=
  (1 / β₁ + 1 / β₂) / 8

/-- The coefficient `c` of the mixed quadratic part. -/
def villainC (β₁ β₂ : ℝ) : ℝ :=
  (1 / β₂ - 1 / β₁) / 4

/-- The `(s, t)` term of the truncated duplicated Villain series at the angles `(φ, φ')`. -/
def villainTerm (β₁ β₂ : ℝ) (N : ℕ) (s t : ℤ) (φ φ' : ℝ) : ℂ :=
  if Even (s + t) then
    ((Real.exp (-(villainA β₁ β₂) * ((s : ℝ) ^ 2 + (t : ℝ) ^ 2)) *
        ∑ k ∈ Finset.range (N + 1),
          (villainC β₁ β₂ * s * t) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) *
      (Complex.exp ((((((s + t) / 2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((((s - t) / 2 : ℤ) : ℝ) * φ' : ℝ) : ℂ) * Complex.I))
  else 0

/-- The truncated duplicated Villain series. -/
def villainSeries (β₁ β₂ : ℝ) (N : ℕ) (φ φ' : ℝ) : ℂ :=
  ∑ s ∈ Finset.Icc (-(N : ℤ)) N, ∑ t ∈ Finset.Icc (-(N : ℤ)) N, villainTerm β₁ β₂ N s t φ φ'

/-- Box partial sums of a norm-summable integer series converge to its sum. -/
private lemma tendsto_box_sum {G : Type*} [NormedAddCommGroup G] [CompleteSpace G] (f : ℤ → G)
    (hf : Summable fun p => ‖f p‖) :
    Tendsto (fun N : ℕ => ∑ p ∈ Finset.Icc (-(N : ℤ)) N, f p) atTop (𝓝 (∑' p, f p)) := by
  classical
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (p : ℤ) => if p ∈ Finset.Icc (-(N : ℤ)) N then f p else 0) (g := f)
    (bound := fun p => ‖f p‖) hf ?_ ?_
  · refine h.congr (fun N => ?_)
    rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N)]
    · exact Finset.sum_congr rfl (fun p hp => by simp [hp])
    · intro p hp
      simp [hp]
  · intro p
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop p.natAbs] with N hN
    have : p ∈ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      omega
    simp [this]
  · exact Filter.Eventually.of_forall fun N p => by split_ifs <;> simp

/-- The summand of the one-copy series. -/
private def vsF (β φ : ℝ) (p : ℤ) : ℂ :=
  (Real.exp (-((p : ℝ) ^ 2) / (2 * β)) : ℂ) * Complex.exp ((((p : ℝ) * φ : ℝ) : ℂ) * Complex.I)

private lemma norm_vsF (β φ : ℝ) (p : ℤ) : ‖vsF β φ p‖ = Real.exp (-((p : ℝ) ^ 2) / (2 * β)) := by
  rw [vsF, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

private lemma summable_norm_vsF {β : ℝ} (hβ : 0 < β) (φ : ℝ) : Summable fun p => ‖vsF β φ p‖ := by
  simpa only [norm_vsF] using villainWeight_fourier_coeff_summable hβ

private lemma weight_eq {β : ℝ} (hβ : 0 < β) (φ : ℝ) :
    (villainWeight β φ : ℂ) = ((villainNorm β : ℝ) : ℂ) * ∑' p, vsF β φ p := by
  rw [villainWeight_fourier_complex_normalized hβ φ]
  unfold villainNorm
  congr 1
  refine tsum_congr fun q => ?_
  unfold vsF
  rw [show Complex.I * (q : ℂ) * (φ : ℂ) = (((q : ℝ) * φ : ℝ) : ℂ) * Complex.I by
    push_cast; ring]

/-- The `(s, t)` entry of the truncated series, zero outside the box. -/
private def vsG (β₁ β₂ : ℝ) (N : ℕ) (φ φ' : ℝ) (st : ℤ × ℤ) : ℂ :=
  if st.1 ∈ Finset.Icc (-(N : ℤ)) N ∧ st.2 ∈ Finset.Icc (-(N : ℤ)) N then
    villainTerm β₁ β₂ N st.1 st.2 φ φ' else 0

/-- The limit entry. -/
private def vsLim (β₁ β₂ : ℝ) (φ φ' : ℝ) (st : ℤ × ℤ) : ℂ :=
  if Even (st.1 + st.2) then
    ((Real.exp (-(villainA β₁ β₂) * ((st.1 : ℝ) ^ 2 + (st.2 : ℝ) ^ 2)) *
        Real.exp (villainC β₁ β₂ * st.1 * st.2) : ℝ) : ℂ) *
      (Complex.exp ((((((st.1 + st.2) / 2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((((st.1 - st.2) / 2 : ℤ) : ℝ) * φ' : ℝ) : ℂ) * Complex.I))
  else 0

/-- The dominating Gaussian. -/
private def vsU (β₁ : ℝ) (q : ℤ) : ℝ := Real.exp (-((q : ℝ) ^ 2) / (2 * (2 * β₁)))

private lemma villainSeries_eq_tsum (β₁ β₂ : ℝ) (N : ℕ) (φ φ' : ℝ) :
    villainSeries β₁ β₂ N φ φ' = ∑' st, vsG β₁ β₂ N φ φ' st := by
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N)]
  · rw [Finset.sum_product]
    unfold villainSeries
    refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
    simp [vsG, hs, ht]
  · intro st hst
    simp only [Finset.mem_product] at hst
    simp only [vsG]
    exact ite_eq_right_iff.mpr (fun h => absurd h hst)

lemma villainC_nonneg {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) : 0 ≤ villainC β₁ β₂ := by
  unfold villainC
  have := one_div_le_one_div_of_le h₂ h₁₂
  linarith

private lemma villainA_sub {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) :
    villainA β₁ β₂ - villainC β₁ β₂ / 2 = 1 / (2 * (2 * β₁)) := by
  have h₁ : β₁ ≠ 0 := (lt_of_lt_of_le h₂ h₁₂).ne'
  have h₂' : β₂ ≠ 0 := h₂.ne'
  unfold villainA villainC
  field_simp
  ring

private lemma vsG_norm_le {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) (N : ℕ) (φ φ' : ℝ) (st : ℤ × ℤ) :
    ‖vsG β₁ β₂ N φ φ' st‖ ≤ vsU β₁ st.1 * vsU β₁ st.2 := by
  have hu : 0 ≤ vsU β₁ st.1 * vsU β₁ st.2 := by unfold vsU; positivity
  unfold vsG
  split_ifs with hbox
  · unfold villainTerm
    split_ifs with he
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul (Complex.exp _) (Complex.exp _),
        Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      set s : ℝ := (st.1 : ℝ) with hs
      set t : ℝ := (st.2 : ℝ) with ht
      have hS := FroehlichSpencer.BKT.Rotator.Ginibre.abs_sum_pow_div_factorial_le (villainC β₁ β₂ * s * t) (N + 1)
      calc Real.exp (-(villainA β₁ β₂) * (s ^ 2 + t ^ 2)) *
            |∑ k ∈ Finset.range (N + 1), (villainC β₁ β₂ * s * t) ^ k / (Nat.factorial k : ℝ)|
          ≤ Real.exp (-(villainA β₁ β₂) * (s ^ 2 + t ^ 2)) * Real.exp |villainC β₁ β₂ * s * t| :=
            mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
        _ = Real.exp (-(villainA β₁ β₂) * (s ^ 2 + t ^ 2) + |villainC β₁ β₂ * s * t|) :=
            (Real.exp_add _ _).symm
        _ ≤ vsU β₁ st.1 * vsU β₁ st.2 := by
          unfold vsU
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hc := villainC_nonneg h₂ h₁₂
          have hk := villainA_sub h₂ h₁₂
          have hst : |s * t| ≤ (s ^ 2 + t ^ 2) / 2 := by
            rw [abs_le]
            constructor <;> nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]
          have h1 : |villainC β₁ β₂ * s * t| ≤ villainC β₁ β₂ * ((s ^ 2 + t ^ 2) / 2) := by
            rw [mul_assoc, abs_mul, abs_of_nonneg hc]
            exact mul_le_mul_of_nonneg_left hst hc
          have h2 : (villainA β₁ β₂ - villainC β₁ β₂ / 2) * (s ^ 2 + t ^ 2) =
              1 / (2 * (2 * β₁)) * (s ^ 2 + t ^ 2) := by rw [hk]
          have e1 : -s ^ 2 / (2 * (2 * β₁)) = -(1 / (2 * (2 * β₁)) * s ^ 2) := by ring
          have e2 : -t ^ 2 / (2 * (2 * β₁)) = -(1 / (2 * (2 * β₁)) * t ^ 2) := by ring
          show _ ≤ -s ^ 2 / (2 * (2 * β₁)) + -t ^ 2 / (2 * (2 * β₁))
          rw [e1, e2]
          nlinarith
    · simpa using hu
  · simpa using hu

private lemma summable_vsU {β₁ : ℝ} (hβ₁ : 0 < β₁) :
    Summable fun st : ℤ × ℤ => vsU β₁ st.1 * vsU β₁ st.2 := by
  have h := villainWeight_fourier_coeff_summable (β := 2 * β₁) (by positivity)
  exact h.mul_of_nonneg h (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)

private lemma tendsto_vsG {β₁ β₂ : ℝ} (φ φ' : ℝ) (st : ℤ × ℤ) :
    Tendsto (fun N : ℕ => vsG β₁ β₂ N φ φ' st) atTop (𝓝 (vsLim β₁ β₂ φ φ' st)) := by
  have hev : ∀ᶠ N : ℕ in atTop, villainTerm β₁ β₂ N st.1 st.2 φ φ' = vsG β₁ β₂ N φ φ' st := by
    filter_upwards [eventually_ge_atTop (max st.1.natAbs st.2.natAbs)] with N hN
    have h1 : st.1 ∈ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      omega
    have h2 : st.2 ∈ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      omega
    simp [vsG, h1, h2]
  refine Tendsto.congr' hev ?_
  unfold villainTerm vsLim
  by_cases he : Even (st.1 + st.2)
  · simp only [he, ↓reduceIte]
    have hS := (FroehlichSpencer.BKT.Rotator.Ginibre.tendsto_sum_pow_div_factorial (villainC β₁ β₂ * st.1 * st.2)).comp (tendsto_add_atTop_nat 1)
    exact ((Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hS)).mul_const _
  · simp only [he, ↓reduceIte]
    exact tendsto_const_nhds

/-- The sum-difference equivalence onto the even-parity lattice. -/
private def vsEquiv : ℤ × ℤ ≃ ↥{st : ℤ × ℤ | Even (st.1 + st.2)} where
  toFun pq := ⟨(pq.1 + pq.2, pq.1 - pq.2), ⟨pq.1, by ring⟩⟩
  invFun x := ((x.1.1 + x.1.2) / 2, (x.1.1 - x.1.2) / 2)
  left_inv pq := by
    ext <;> simp <;> omega
  right_inv x := by
    obtain ⟨⟨s, t⟩, r, hr⟩ := x
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    omega

private lemma vsLim_equiv {β₁ β₂ : ℝ} (h₁ : β₁ ≠ 0) (h₂ : β₂ ≠ 0) (φ φ' : ℝ) (pq : ℤ × ℤ) :
    vsLim β₁ β₂ φ φ' (vsEquiv pq).1 = vsF β₁ φ pq.1 * vsF β₂ φ' pq.2 := by
  obtain ⟨p, q⟩ := pq
  have he : Even ((p + q) + (p - q)) := ⟨p, by ring⟩
  have h1 : ((p + q) + (p - q)) / 2 = p := by omega
  have h2 : ((p + q) - (p - q)) / 2 = q := by omega
  have hexp : Real.exp (-(villainA β₁ β₂) * ((((p + q : ℤ)) : ℝ) ^ 2 + (((p - q : ℤ)) : ℝ) ^ 2)) *
      Real.exp (villainC β₁ β₂ * ((p + q : ℤ) : ℝ) * ((p - q : ℤ) : ℝ)) =
      Real.exp (-((p : ℝ) ^ 2) / (2 * β₁)) * Real.exp (-((q : ℝ) ^ 2) / (2 * β₂)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    unfold villainA villainC
    field_simp
    ring
  show vsLim β₁ β₂ φ φ' (p + q, p - q) = _
  unfold vsLim vsF
  simp only [he, ↓reduceIte, h1, h2]
  rw [hexp]
  push_cast
  ring

private lemma vsLim_sum {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) (φ φ' : ℝ) :
    ∑' st, vsLim β₁ β₂ φ φ' st = (∑' p, vsF β₁ φ p) * ∑' q, vsF β₂ φ' q := by
  have hβ₁ : 0 < β₁ := lt_of_lt_of_le h₂ h₁₂
  have hsupp : Function.support (vsLim β₁ β₂ φ φ') ⊆ {st : ℤ × ℤ | Even (st.1 + st.2)} := by
    intro st hst
    by_contra he
    exact hst (by simp [vsLim, show ¬ Even (st.1 + st.2) from he])
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_vsF hβ₁ φ) (summable_norm_vsF h₂ φ'),
    ← tsum_subtype_eq_of_support_subset hsupp,
    ← vsEquiv.tsum_eq (fun x : ↥{st : ℤ × ℤ | Even (st.1 + st.2)} => vsLim β₁ β₂ φ φ' x.1)]
  exact tsum_congr fun pq => vsLim_equiv hβ₁.ne' h₂.ne' φ φ' pq

theorem tendsto_villainSeries {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) (φ φ' : ℝ) :
    Tendsto (fun N : ℕ => ((villainNorm β₁ * villainNorm β₂ : ℝ) : ℂ) * villainSeries β₁ β₂ N φ φ')
      atTop (𝓝 ((villainWeight β₁ φ * villainWeight β₂ φ' : ℝ) : ℂ)) := by
  have hβ₁ : 0 < β₁ := lt_of_lt_of_le h₂ h₁₂
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (st : ℤ × ℤ) => vsG β₁ β₂ N φ φ' st) (g := vsLim β₁ β₂ φ φ')
    (summable_vsU hβ₁) (tendsto_vsG φ φ')
    (Filter.Eventually.of_forall fun N st => vsG_norm_le h₂ h₁₂ N φ φ' st)
  have hT' : Tendsto (fun N : ℕ => villainSeries β₁ β₂ N φ φ') atTop
      (𝓝 ((∑' p, vsF β₁ φ p) * ∑' q, vsF β₂ φ' q)) := by
    rw [← vsLim_sum h₂ h₁₂ φ φ']
    exact hT.congr (fun N => (villainSeries_eq_tsum β₁ β₂ N φ φ').symm)
  convert hT'.const_mul ((villainNorm β₁ * villainNorm β₂ : ℝ) : ℂ) using 2
  rw [Complex.ofReal_mul (villainWeight β₁ φ), weight_eq hβ₁ φ, weight_eq h₂ φ']
  push_cast
  ring

theorem exists_norm_villainSeries_le {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) :
    ∃ C : ℝ, ∀ (N : ℕ) (φ φ' : ℝ), ‖villainSeries β₁ β₂ N φ φ'‖ ≤ C := by
  have hβ₁ : 0 < β₁ := lt_of_lt_of_le h₂ h₁₂
  refine ⟨∑' st : ℤ × ℤ, vsU β₁ st.1 * vsU β₁ st.2, fun N φ φ' => ?_⟩
  rw [villainSeries_eq_tsum]
  exact tsum_of_norm_bounded (summable_vsU hβ₁).hasSum (vsG_norm_le h₂ h₁₂ N φ φ')

/-- The truncated one-copy Villain series. -/
def villainOneSeries (β : ℝ) (N : ℕ) (φ : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc (-(N : ℤ)) N,
    (Real.exp (-((p : ℝ) ^ 2) / (2 * β)) : ℂ) * Complex.exp ((((p : ℝ) * φ : ℝ) : ℂ) * Complex.I)

theorem tendsto_villainOneSeries {β : ℝ} (hβ : 0 < β) (φ : ℝ) :
    Tendsto (fun N : ℕ => ((villainNorm β : ℝ) : ℂ) * villainOneSeries β N φ) atTop
      (𝓝 ((villainWeight β φ : ℝ) : ℂ)) := by
  rw [weight_eq hβ φ]
  exact (tendsto_box_sum (vsF β φ) (summable_norm_vsF hβ φ)).const_mul _

theorem exists_norm_villainOneSeries_le {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, ∀ (N : ℕ) (φ : ℝ), ‖villainOneSeries β N φ‖ ≤ C := by
  refine ⟨∑' p : ℤ, Real.exp (-((p : ℝ) ^ 2) / (2 * β)), fun N φ => ?_⟩
  have h : villainOneSeries β N φ = ∑ p ∈ Finset.Icc (-(N : ℤ)) N, vsF β φ p := rfl
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_vsF]
  exact (villainWeight_fourier_coeff_summable hβ).sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)

end FroehlichSpencer.BKT.Ginibre

end
