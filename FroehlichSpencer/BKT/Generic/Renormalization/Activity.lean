/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Energy.CostEnvelope

/-!
# The energy gain of a graded spin wave and its locality (generic core)

* `translationEnergy_envelopeWave_ge_gain`: if the exponential-branch cost of every small-scale
  piece is at most half the amplitude, `N B(λK₁) ≤ λ/2`, and the quadratic-branch amplitudes
  `μ_s` of the large scales are at least `λ`, then
  `E_c(a, ϱ) ≥ (λ/2) (∑_{scale 0} |q_t| + #{pieces of positive scale})`.

The base (scale-zero) pieces contribute their charges linearly, every other piece at least
  `λ/2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open FroehlichSpencer.BKT.Generic.SpinWave

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {centerOf : (V → ℤ) → V} {ρ : V → ℤ}

/-- **The gain of the envelope wave.** Under the exponential-branch smallness `N B(λK₁) ≤ λ/2` for
the pieces below `k₀ ≥ 1` and `λ ≤ μ_s` for the scales `s ≥ k₀`,
`E_c(a, ϱ) ≥ (λ/2) (∑_{t : scale 0} |q_t| + #{t : scale ≥ 1})`. -/
theorem translationEnergy_envelopeWave_ge_gain (Wv : GradedSpinWave G N₀ centerOf ρ)
    {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < Wv.K₀)
    (hK₁ : 0 < Wv.K₁) {lam : ℝ} (hlam : 0 ≤ lam) (hlamW : lam * Wv.K₁ ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) {N : ℝ}
    (hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ N)
    (hexp : N * costMajorant κ κ' (lam * Wv.K₁) ≤ lam / 2)
    (hquad : ∀ s, k₀ ≤ s → lam ≤ quadAmplitude κ Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) s) :
    letI := Wv.finite
    lam / 2 * ((∑ t ∈ Finset.univ.filter (fun t => Wv.scale t = 0), |Wv.charge t|) +
        ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)) ≤
      translationEnergy c (gradLinear G) (envelopeWave Wv κ lam k₀) (fun j => (ρ j : ℝ)) := by
  classical
  let _ := Wv.finite
  have hmain := translationEnergy_envelopeWave_ge Wv hc hκ hK₀ hK₁ hlam hlamW k₀ hcount
  refine le_trans ?_ hmain
  -- the per-piece gain
  set g : Wv.ι → ℝ := fun t => if Wv.scale t = 0 then lam / 2 * |Wv.charge t| else lam / 2
    with hg
  have hlhs : lam / 2 * ((∑ t ∈ Finset.univ.filter (fun t => Wv.scale t = 0), |Wv.charge t|) +
      ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)) = ∑ t, g t := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t => Wv.scale t = 0) g
    rw [← hsplit, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun t ht => by
        rw [hg]; simp only [ite_eq_left (Finset.mem_filter.mp ht).2]
    · have hfilt : (Finset.univ.filter fun t => ¬Wv.scale t = 0) =
          Finset.univ.filter fun t => 1 ≤ Wv.scale t := by
        ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [hfilt, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, mul_one]
      exact Finset.sum_congr rfl fun t ht => by
        have h1 : ¬Wv.scale t = 0 := by have := (Finset.mem_filter.mp ht).2; omega
        rw [hg]; simp only [h1, ite_false]
  rw [hlhs]
  -- each piece's contribution dominates its gain
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => Wv.scale t < k₀) g
  rw [← hsplit]
  refine add_le_add (Finset.sum_le_sum fun t ht => ?_) (Finset.sum_le_sum fun t ht => ?_)
  · have hq := Wv.charge_ge_one t
    have hgt : g t ≤ lam / 2 * |Wv.charge t| := by
      simp only [hg]
      split_ifs
      · exact le_rfl
      · nlinarith
    have hNB : N * costMajorant κ κ' (lam * Wv.K₁) ≤ lam / 2 := hexp
    nlinarith
  · have hs : k₀ ≤ Wv.scale t := by have := (Finset.mem_filter.mp ht).2; omega
    have hs0 : ¬Wv.scale t = 0 := by omega
    have hμ := hquad _ hs
    simp only [hg, hs0, ite_false]
    linarith

/-- The assembled wave is constant on `D⁺(ϱ')` for every comparable `ϱ'` (KP P2.4 (1)). -/
theorem envelopeWave_const_plus (Wv : GradedSpinWave G N₀ centerOf ρ) (κ lam : ℝ) (k₀ : ℕ) :
    ∀ ρ' ∈ G.comparableDensities N₀ ρ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ρ' (centerOf ρ'), envelopeWave Wv κ lam k₀ j = c := by
  classical
  let _ := Wv.finite
  intro ρ' hρ'
  choose cs hcs using fun t => Wv.const_plus t ρ' hρ'
  refine ⟨∑ t, envelopeAmplitude Wv κ lam k₀ t * cs t, fun j hj => ?_⟩
  simp only [envelopeWave]
  exact Finset.sum_congr rfl fun t _ => by rw [hcs t j hj]

/-- The assembled wave is supported in `D(ϱ)` (KP P2.4 (2)). -/
theorem envelopeWave_support_subset (Wv : GradedSpinWave G N₀ centerOf ρ) (κ lam : ℝ) (k₀ : ℕ) :
    Function.support (envelopeWave Wv κ lam k₀) ⊆ G.densityDomain ρ (centerOf ρ) := by
  classical
  let _ := Wv.finite
  intro j hj
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  exact Wv.supp t (right_ne_zero_of_mul ht)

end FroehlichSpencer.BKT.Generic

end
