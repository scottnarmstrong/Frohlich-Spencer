/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.SiteMeasure

/-!
# The duplicated Fourier functional and its positivity on Ginibre's cone

For single-site measures `ν, ν'` with real Fourier coefficients `λ, λ'`, the doubled product measure
integrates the evaluation of a duplicated formal polynomial `P` to
`Φ(P) = Σ_{(p, q)} P(p, q) ∏_x λ(p_x) λ'(q_x)`. In the sum–difference coordinates
`(s, t) = (p + q, p − q)` the single-site weight becomes
`k(s, t) = 1[s + t even] λ((s+t)/2) λ'((s−t)/2)`. When `k(s, t) = c · 1[s, t ∈ A, f s = f t]` with
`c ≥ 0` (an *equivalence kernel*), `Φ` is a nonnegative combination of squares on every tensor
square `Y ⊗ Y`, hence nonnegative on Ginibre's cone. This holds for the circle (`A = {0}`), the
`N`-state clock (`A = Nℤ`, `f = (· mod 2N)`) and the mixed clock/circle pair (`A = Nℤ`, `f = id`).
-/

@[expose] public section

open AddMonoidAlgebra MeasureTheory
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

variable {V : Type*} [Fintype V]

/-- The duplicated Fourier functional of two single-site coefficient functions. -/
def dupFunctional (lam lam' : ℤ → ℝ) (P : DupTrigAlgebra V) : ℝ :=
  P.coeff.sum fun g r => r * ∏ x, (lam (g.1 x) * lam' (g.2 x))

theorem dupFunctional_add (lam lam' : ℤ → ℝ) (P Q : DupTrigAlgebra V) :
    dupFunctional lam lam' (P + Q) = dupFunctional lam lam' P + dupFunctional lam lam' Q := by
  unfold dupFunctional
  rw [coeff_add, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem dupFunctional_single (lam lam' : ℤ → ℝ) (g : Frequency V × Frequency V) (r : ℝ) :
    dupFunctional lam lam' (single g r) = r * ∏ x, (lam (g.1 x) * lam' (g.2 x)) := by
  unfold dupFunctional
  rw [coeff_single, Finsupp.sum_single_index (zero_mul _)]

theorem integrable_dupEval_prod {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (P : DupTrigAlgebra V) :
    Integrable (dupEval V P) ((siteProduct ν V).prod (siteProduct ν' V)) := by
  obtain ⟨C, hC⟩ := exists_norm_dupEval_le P
  exact Integrable.of_bound (continuous_dupEval P).aestronglyMeasurable C (ae_of_all _ hC)

/-- The doubled product measure integrates an evaluated duplicated polynomial to its duplicated
Fourier functional. -/
theorem integral_dupEval_siteProduct {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {lam lam' : ℤ → ℝ} (hν : HasRealFourier ν lam) (hν' : HasRealFourier ν' lam')
    (P : DupTrigAlgebra V) :
    ∫ z, dupEval V P z ∂(siteProduct ν V).prod (siteProduct ν' V) =
      (dupFunctional lam lam' P : ℂ) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [dupFunctional]
  | add P Q hP hQ =>
      simp only [map_add, Pi.add_apply]
      rw [integral_add (integrable_dupEval_prod P) (integrable_dupEval_prod Q), hP, hQ,
        dupFunctional_add]
      push_cast
      ring
  | single g r =>
      simp_rw [dupEval_single]
      rw [integral_const_mul, integral_prod_mul (fun θ => character g.1 θ)
        (fun θ => character g.2 θ), integral_character_siteProduct hν,
        integral_character_siteProduct hν', dupFunctional_single, Finset.prod_mul_distrib]
      push_cast
      ring

open Classical in
/-- The single-site sum–difference weight is an *equivalence kernel*:
`1[s + t even] λ((s+t)/2) λ'((s−t)/2) = c · 1[s ∈ A ∧ t ∈ A ∧ f s = f t]` with `c ≥ 0`. -/
def HasEquivKernel (lam lam' : ℤ → ℝ) : Prop :=
  ∃ (c : ℝ) (A : ℤ → Prop) (f : ℤ → ℤ), 0 ≤ c ∧ ∀ s t : ℤ,
    (if Even (s + t) then lam ((s + t) / 2) * lam' ((s - t) / 2) else 0) =
      if A s ∧ A t ∧ f s = f t then c else 0

/-- A sum over pairs restricted to equal labels is a sum of squares. -/
theorem sum_sum_ite_eq_nonneg {α β : Type*} [DecidableEq β] (S : Finset α) (F : α → β)
    (y : α → ℝ) : 0 ≤ ∑ a ∈ S, ∑ b ∈ S, (if F a = F b then y a * y b else 0) := by
  classical
  have h1 : ∀ a ∈ S, (∑ b ∈ S, (if F a = F b then y a * y b else 0)) =
      y a * ∑ b ∈ S.filter (fun b => F b = F a), y b := fun a _ => by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : F a = F b
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_fiberwise_of_maps_to
    (g := F) (t := S.image F) (fun a ha => Finset.mem_image_of_mem F ha)]
  refine Finset.sum_nonneg fun r _ => ?_
  have h2 : ∀ a ∈ S.filter (fun a => F a = r), y a * ∑ b ∈ S.filter (fun b => F b = F a), y b =
      y a * ∑ b ∈ S.filter (fun b => F b = r), y b := fun a ha => by
    rw [(Finset.mem_filter.mp ha).2]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  exact mul_self_nonneg _

/-- **Positivity of the duplicated functional on Ginibre's cone.** -/
theorem dupFunctional_nonneg {lam lam' : ℤ → ℝ} (hK : HasEquivKernel lam lam')
    {P : DupTrigAlgebra V} (hP : IsGinibre P) : 0 ≤ dupFunctional lam lam' P := by
  classical
  obtain ⟨c, A, f, hc, hk⟩ := hK
  let k : ℤ → ℤ → ℝ := fun s t =>
    if Even (s + t) then lam ((s + t) / 2) * lam' ((s - t) / 2) else 0
  let K : Frequency V → Frequency V → ℝ := fun s t => ∏ x, k (s x) (t x)
  let Ψ : DupTrigAlgebra V → ℝ := fun R => R.coeff.sum fun h r => r * K h.1 h.2
  -- the functional in sum-difference coordinates
  have hΨ : dupFunctional lam lam' P = Ψ (sumDiffMap V P) := by
    show _ = (Finsupp.mapDomain (sumDiffHom V) P.coeff).sum fun h r => r * K h.1 h.2
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    refine Finsupp.sum_congr fun g _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    simp only [k, sumDiffHom_apply, Pi.add_apply, Pi.sub_apply]
    have he : Even (g.1 x + g.2 x + (g.1 x - g.2 x)) := ⟨g.1 x, by ring⟩
    rw [ite_eq_left he]
    congr 2 <;> omega
  -- `Ψ` is nonnegative on sums of tensor squares
  have hlin : ∀ R₁ R₂, Ψ (R₁ + R₂) = Ψ R₁ + Ψ R₂ := fun R₁ R₂ => by
    simp only [Ψ]
    rw [coeff_add, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  have hsmul : ∀ (a : ℝ) R, Ψ (a • R) = a * Ψ R := fun a R => by
    simp only [Ψ]
    rw [coeff_smul, Finsupp.sum_smul_index (fun _ => zero_mul _), Finsupp.mul_sum]
    refine Finsupp.sum_congr fun _ _ => ?_
    ring
  have hK' : ∀ s t : Frequency V, K s t =
      if (∀ x, A (s x)) ∧ (∀ x, A (t x)) ∧ (fun x => f (s x)) = (fun x => f (t x)) then
        c ^ Fintype.card V else 0 := fun s t => by
    simp only [K, k, hk]
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_implies, Finset.prod_const, Finset.card_univ]
    congr 1
    simp only [funext_iff]
    apply propext
    constructor
    · intro h
      exact ⟨fun x => (h x).1, fun x => (h x).2.1, fun x => (h x).2.2⟩
    · intro h x
      exact ⟨h.1 x, h.2.1 x, h.2.2 x⟩
  have hsq : ∀ Y : TrigAlgebra V, 0 ≤ Ψ (tensor Y Y) := fun Y => by
    simp only [Ψ]
    rw [Finsupp.sum_of_support_subset _ (s := Y.coeff.support ×ˢ Y.coeff.support) ?_ _
      (fun _ _ => zero_mul _)]
    · rw [Finset.sum_product]
      simp_rw [coeff_tensor, hK']
      have hfilter : ∀ a ∈ Y.coeff.support, (∑ b ∈ Y.coeff.support, Y.coeff a * Y.coeff b *
          (if (∀ x, A (a x)) ∧ (∀ x, A (b x)) ∧ (fun x => f (a x)) = (fun x => f (b x)) then
            c ^ Fintype.card V else 0)) =
          c ^ Fintype.card V * ∑ b ∈ Y.coeff.support, (if (∀ x, A (a x)) ∧ (∀ x, A (b x)) ∧
            (fun x => f (a x)) = (fun x => f (b x)) then Y.coeff a * Y.coeff b else 0) :=
        fun a _ => by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> ring
      rw [Finset.sum_congr rfl hfilter, ← Finset.mul_sum]
      refine mul_nonneg (pow_nonneg hc _) ?_
      have hsplit : (∑ a ∈ Y.coeff.support, ∑ b ∈ Y.coeff.support, (if (∀ x, A (a x)) ∧
          (∀ x, A (b x)) ∧ (fun x => f (a x)) = (fun x => f (b x)) then Y.coeff a * Y.coeff b
            else 0)) =
          ∑ a ∈ Y.coeff.support.filter (fun s => ∀ x, A (s x)),
            ∑ b ∈ Y.coeff.support.filter (fun s => ∀ x, A (s x)),
            (if (fun x => f (a x)) = (fun x => f (b x)) then Y.coeff a * Y.coeff b else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_filter]
        by_cases ha : ∀ x, A (a x)
        · rw [ite_eq_left ha]
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases hb : ∀ x, A (b x)
          · simp [ha, hb]
          · simp [hb]
        · rw [ite_eq_right ha]
          exact Finset.sum_eq_zero fun b _ => by simp [ha]
      rw [hsplit]
      exact sum_sum_ite_eq_nonneg _ (fun (a : Frequency V) (x : V) => f (a x)) (fun a => Y.coeff a)
    · intro h hh
      rw [Finset.mem_product, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      obtain ⟨a, b⟩ := h
      rw [Finsupp.mem_support_iff, coeff_tensor] at hh
      exact ⟨left_ne_zero_of_mul hh, right_ne_zero_of_mul hh⟩
  have hpos : ∀ R, IsSquareSum R → 0 ≤ Ψ R := fun R hR => by
    induction hR with
    | square a ha Y =>
        rw [hsmul]
        exact mul_nonneg ha (hsq Y)
    | add _ _ h₁ h₂ =>
        rw [hlin]
        exact add_nonneg h₁ h₂
  rw [hΨ]
  exact hpos _ hP

/-! ### The circle, the clock and the mixed pair -/

theorem hasEquivKernel_circle : HasEquivKernel circleFourier circleFourier := by
  classical
  refine ⟨4 * π ^ 2, fun s => s = 0, id, by positivity, fun s t => ?_⟩
  simp only [circleFourier, id, Int.even_iff]
  by_cases h : s = 0 ∧ t = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [add_zero, sub_zero, Int.zero_emod, Int.zero_ediv, ite_true, and_self]
    ring
  · have h' : ¬(s = 0 ∧ t = 0 ∧ s = t) := fun h'' => h ⟨h''.1, h''.2.1⟩
    rw [ite_eq_right h']
    split_ifs <;> first | (exfalso; omega) | ring

/-- The clock divisibility identity behind the clock kernel. -/
theorem clock_kernel_iff {N : ℤ} (s t : ℤ) :
    (Even (s + t) ∧ N ∣ (s + t) / 2 ∧ N ∣ (s - t) / 2) ↔
      (N ∣ s ∧ N ∣ t ∧ s % (2 * N) = t % (2 * N)) := by
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩
    have h1 : (s + t) / 2 = m := by omega
    have h2 : (s - t) / 2 = m - t := by omega
    rw [h1] at ha
    rw [h2] at hb
    refine ⟨⟨a + b, by linear_combination ha + hb + hm⟩, ⟨a - b, by linarith⟩, ?_⟩
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have : s - t = 2 * N * b := by linarith
    rw [this, Int.mul_emod_right]
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hst⟩
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at hst
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hst
    set u := N * k with hu
    have hsum : s + t = 2 * (t + u) := by linarith
    have h1 : (s + t) / 2 = t + u := by omega
    have h2 : (s - t) / 2 = u := by omega
    refine ⟨⟨t + u, by linarith⟩, ?_, ?_⟩
    · rw [h1, hb, hu]
      exact ⟨b + k, by ring⟩
    · rw [h2, hu]
      exact ⟨k, rfl⟩

theorem hasEquivKernel_clock (N : ℕ) : HasEquivKernel (clockFourier N) (clockFourier N) := by
  classical
  refine ⟨(N : ℝ) ^ 2, fun s => (N : ℤ) ∣ s, fun s => s % (2 * N), by positivity, fun s t => ?_⟩
  simp only [clockFourier]
  have hiff := clock_kernel_iff (N := (N : ℤ)) s t
  by_cases h : (N : ℤ) ∣ s ∧ (N : ℤ) ∣ t ∧ s % (2 * N) = t % (2 * N)
  · obtain ⟨he, h1, h2⟩ := hiff.mpr h
    rw [ite_eq_left h, ite_eq_left he, ite_eq_left h1, ite_eq_left h2]
    ring
  · rw [ite_eq_right h]
    split_ifs with he h1 h2 <;> first | exact absurd (hiff.mp ⟨he, h1, h2⟩) h | simp

theorem hasEquivKernel_clock_circle (N : ℕ) : HasEquivKernel (clockFourier N) circleFourier := by
  classical
  refine ⟨2 * π * N, fun s => (N : ℤ) ∣ s, id, by positivity, fun s t => ?_⟩
  simp only [clockFourier, circleFourier, id]
  by_cases h : (N : ℤ) ∣ s ∧ (N : ℤ) ∣ t ∧ s = t
  · obtain ⟨hs, -, rfl⟩ := h
    have he : Even (s + s) := ⟨s, rfl⟩
    have h1 : (s + s) / 2 = s := by omega
    rw [ite_eq_left he, h1, ite_eq_left hs, sub_self, Int.zero_ediv, ite_eq_left rfl,
      ite_eq_left ⟨hs, hs, rfl⟩]
    ring
  · rw [ite_eq_right h]
    have key : Even (s + t) → (N : ℤ) ∣ (s + t) / 2 → (s - t) / 2 = 0 → False := by
      intro he h1 h2
      apply h
      rw [Int.even_iff] at he
      have hst : s = t := by omega
      subst hst
      have h3 : (s + s) / 2 = s := by omega
      rw [h3] at h1
      exact ⟨h1, h1, rfl⟩
    split_ifs with he h1 h2 <;> first | exact (key he h1 h2).elim | simp

end FroehlichSpencer.BKT.Ginibre

end
