/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedActivity
public import FroehlichSpencer.BKT.Generic.Marked.Cluster
public import FroehlichSpencer.BKT.Generic.Marked.Domain
import Mathlib.Tactic

/-!
# The cluster algebra of the rooted marked bound

`sum_clusterWeight_le` takes:
- exploration weights `θ = e^{−s·cost} ≤ 1/2`;
- activities `|K| ≤ e^{D₂ cost}`;
- the neighbour bound of `RootedMarkedBranchClause`;
- the composite gain `γ(∑_C cost + ℓ)`.

It bounds the branch weight `∑_C |∏_C K| e^{−γ(∑_C cost + ℓ)} / ∏_{N ∖ rem(C)} (1 − θ)` by
`e^{4K_nb − (γ/2)ℓ}`, provided `γ ≥ D₂ + s + log 2 + 4K_nb` and `γ ≥ 8K_nb`. The proof uses the
exploration-weight sum `sum_le_of_le_explorationWeight`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT.Generic.Marked

variable {ι : Type*} [DecidableEq ι]

/-- `N ∖ rem(C)` splits into the cluster `C` and its neighbours `∂C = N ∖ (C ∪ rem(C))`. -/
theorem prod_sdiff_remainder_eq {adj : ι → Finset ι → Prop} {N C : Finset ι} (hCN : C ⊆ N)
    (f : ι → ℝ) :
    ∏ m ∈ N \ remainder adj N C, f m =
      (∏ m ∈ C, f m) * ∏ m ∈ N \ (C ∪ remainder adj N C), f m := by
  have hsplit : N \ remainder adj N C = C ∪ (N \ (C ∪ remainder adj N C)) := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hm, hr⟩
      by_cases hc : m ∈ C
      · exact Or.inl hc
      · exact Or.inr ⟨hm, fun h => h.elim hc hr⟩
    · rintro (hc | ⟨hm, hn⟩)
      · exact ⟨hCN hc, fun hr => Finset.disjoint_left.1 (disjoint_remainder N C) hc hr⟩
      · exact ⟨hm, fun hr => hn (Or.inr hr)⟩
  have hdisj : Disjoint C (N \ (C ∪ remainder adj N C)) := by
    rw [Finset.disjoint_left]
    intro m hc hm
    exact (Finset.mem_sdiff.1 hm).2 (Finset.mem_union_left _ hc)
  rw [hsplit, Finset.prod_union hdisj]

/-- **The cluster algebra of the marked branch bound.** With exploration weights
`θ = e^{−s·cost} ≤ 1/2`, activities `|K| ≤ e^{D₂·cost}` and costs at least one, the neighbour
bound of the marked clause and the composite gain `γ (∑_C cost + ℓ)` give
`∑_C |∏_C K| e^{−γ(∑_C cost + ℓ)} / ∏_{N ∖ rem(C)} (1 − θ) ≤ e^{4 K_nb − (γ/2) ℓ}`, provided
`γ ≥ D₂ + s + log 2 + 4 K_nb` and `γ ≥ 8 K_nb`. -/
theorem sum_clusterWeight_le {adj : ι → Finset ι → Prop} (hmono : AdjMonotone adj)
    (N : Finset ι) (K cost : ι → ℝ) {D₂ s s₀ Knb γ ℓ : ℝ}
    (hcost : ∀ m ∈ N, 1 ≤ cost m) (hK : ∀ m ∈ N, |K m| ≤ Real.exp (D₂ * cost m))
    (hs : Real.log 2 ≤ s) (hss₀ : s₀ ≤ s) (hℓ : 0 ≤ ℓ)
    (hnb : ∀ C ∈ clusters adj N,
      ∑ m ∈ N \ (C ∪ remainder adj N C), Real.exp (-s₀ * cost m) ≤
        Knb * (1 + ∑ m ∈ C, cost m + ℓ))
    (hγ₁ : D₂ + s + Real.log 2 + 4 * Knb ≤ γ) (hγ₂ : 8 * Knb ≤ γ) :
    ∑ C ∈ clusters adj N, |∏ m ∈ C, K m| * Real.exp (-(γ * (∑ m ∈ C, cost m + ℓ))) /
        ∏ m ∈ N \ remainder adj N C, (1 - Real.exp (-s * cost m)) ≤
      Real.exp (4 * Knb - γ / 2 * ℓ) := by
  classical
  set θ : ι → ℝ := fun m => Real.exp (-s * cost m) with hθ
  have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hs0 : 0 ≤ s := (Real.log_nonneg (by norm_num)).trans hs
  have hθle : ∀ m ∈ N, θ m ≤ 1 / 2 := by
    intro m hm
    have h1 : θ m ≤ Real.exp (-Real.log 2) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [hcost m hm]
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at h1
    simpa using h1
  have hθ0 : ∀ m, 0 < θ m := fun m => Real.exp_pos _
  have hθ1 : ∀ m ∈ N, θ m < 1 := fun m hm => by linarith [hθle m hm]
  refine sum_le_of_le_explorationWeight hmono N θ hθ1 _ fun C hC => ?_
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  set S : ℝ := ∑ m ∈ C, cost m with hS
  set B := N \ (C ∪ remainder adj N C) with hB
  have hBN : B ⊆ N := fun m hm => (Finset.mem_sdiff.1 hm).1
  have hS1 : (C.card : ℝ) ≤ S := by
    rw [hS, Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun m hm => by simpa using hcost m (hCN hm)
  -- the neighbour weight
  have hnbθ : ∑ m ∈ B, θ m ≤ Knb * (1 + S + ℓ) := by
    refine le_trans (Finset.sum_le_sum fun m hm => ?_) (hnb C hC)
    refine Real.exp_le_exp.2 ?_
    have := hcost m (hBN hm)
    nlinarith
  -- lower bounds for the weights
  have hCθ : Real.exp (-((s + Real.log 2) * S)) ≤ ∏ m ∈ C, (θ m * (1 - θ m)) := by
    have hpt : ∀ m ∈ C, Real.exp (-((s + Real.log 2) * cost m)) ≤ θ m * (1 - θ m) := by
      intro m hm
      have h1 : 1 / 2 ≤ 1 - θ m := by linarith [hθle m (hCN hm)]
      have h2 : Real.exp (-((s + Real.log 2) * cost m)) ≤ θ m * (1 / 2) := by
        have e : Real.exp (-((s + Real.log 2) * cost m)) =
            θ m * Real.exp (-(Real.log 2 * cost m)) := by
          rw [hθ, ← Real.exp_add]; ring_nf
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (hθ0 m).le
        have h3 : Real.exp (-(Real.log 2 * cost m)) ≤ Real.exp (-Real.log 2) := by
          refine Real.exp_le_exp.2 ?_
          have := hcost m (hCN hm)
          nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
        rw [hhalf] at h3
        exact h3
      exact h2.trans (mul_le_mul_of_nonneg_left h1 (hθ0 m).le)
    calc Real.exp (-((s + Real.log 2) * S)) =
          ∏ m ∈ C, Real.exp (-((s + Real.log 2) * cost m)) := by
          rw [← Real.exp_sum, hS, Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ _ := Finset.prod_le_prod₀ (fun m _ => (Real.exp_pos _).le) hpt
  have hBθ : Real.exp (-(4 * ∑ m ∈ B, θ m)) ≤ ∏ m ∈ B, ((1 - θ m) * (1 - θ m)) := by
    have hpt : ∀ m ∈ B, Real.exp (-(4 * θ m)) ≤ (1 - θ m) * (1 - θ m) := by
      intro m hm
      have h := exp_neg_two_mul_le_one_sub (hθ0 m).le (hθle m (hBN hm))
      have e : Real.exp (-(4 * θ m)) = Real.exp (-(2 * θ m)) * Real.exp (-(2 * θ m)) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]
      exact mul_le_mul h h (Real.exp_pos _).le (by linarith [hθle m (hBN hm)])
    calc Real.exp (-(4 * ∑ m ∈ B, θ m)) = ∏ m ∈ B, Real.exp (-(4 * θ m)) := by
          rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ _ := Finset.prod_le_prod₀ (fun m _ => (Real.exp_pos _).le) hpt
  have hKC : |∏ m ∈ C, K m| ≤ Real.exp (D₂ * S) := by
    rw [Finset.abs_prod, hS, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun m _ => abs_nonneg _) fun m hm => hK m (hCN hm)
  -- the denominator
  have hden : ∏ m ∈ N \ remainder adj N C, (1 - θ m) =
      (∏ m ∈ C, (1 - θ m)) * ∏ m ∈ B, (1 - θ m) := prod_sdiff_remainder_eq hCN _
  have hpos1 : 0 < ∏ m ∈ C, (1 - θ m) :=
    Finset.prod_pos fun m hm => by linarith [hθle m (hCN hm)]
  have hpos2 : 0 < ∏ m ∈ B, (1 - θ m) :=
    Finset.prod_pos fun m hm => by linarith [hθle m (hBN hm)]
  rw [hden, div_le_iff₀ (mul_pos hpos1 hpos2)]
  -- the exponent algebra
  have hexp : Real.exp (D₂ * S) * Real.exp (-(γ * (S + ℓ))) ≤
      Real.exp (4 * Knb - γ / 2 * ℓ) *
        (Real.exp (-((s + Real.log 2) * S)) * Real.exp (-(4 * ∑ m ∈ B, θ m))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hS0 : 0 ≤ S := le_trans (Nat.cast_nonneg _) hS1
    nlinarith [mul_le_mul_of_nonneg_left hnbθ (by norm_num : (0 : ℝ) ≤ 4),
      mul_le_mul_of_nonneg_right hγ₁ hS0, mul_le_mul_of_nonneg_right hγ₂ hℓ]
  have hprodθ : (∏ m ∈ C, θ m) * (∏ m ∈ C, (1 - θ m)) = ∏ m ∈ C, (θ m * (1 - θ m)) := by
    rw [← Finset.prod_mul_distrib]
  have hprodB : (∏ m ∈ B, (1 - θ m)) * (∏ m ∈ B, (1 - θ m)) =
      ∏ m ∈ B, ((1 - θ m) * (1 - θ m)) := by rw [← Finset.prod_mul_distrib]
  calc |∏ m ∈ C, K m| * Real.exp (-(γ * (S + ℓ)))
      ≤ Real.exp (D₂ * S) * Real.exp (-(γ * (S + ℓ))) :=
        mul_le_mul_of_nonneg_right hKC (Real.exp_pos _).le
    _ ≤ Real.exp (4 * Knb - γ / 2 * ℓ) *
        (Real.exp (-((s + Real.log 2) * S)) * Real.exp (-(4 * ∑ m ∈ B, θ m))) := hexp
    _ ≤ Real.exp (4 * Knb - γ / 2 * ℓ) *
        ((∏ m ∈ C, (θ m * (1 - θ m))) * ∏ m ∈ B, ((1 - θ m) * (1 - θ m))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hCθ hBθ (Real.exp_pos _).le
          (Finset.prod_nonneg fun m hm => by
            have := hθle m (hCN hm); nlinarith [hθ0 m])) (Real.exp_pos _).le
    _ = Real.exp (4 * Knb - γ / 2 * ℓ) * ((∏ m ∈ C, θ m) * ∏ m ∈ B, (1 - θ m)) *
          ((∏ m ∈ C, (1 - θ m)) * ∏ m ∈ B, (1 - θ m)) := by
        rw [← hprodθ, ← hprodB]
        ring

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
