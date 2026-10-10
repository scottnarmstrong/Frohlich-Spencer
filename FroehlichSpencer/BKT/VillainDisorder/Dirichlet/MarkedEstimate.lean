/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedBound
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Assembly
import Mathlib.Tactic

/-!
# The rooted Dirichlet Fejér estimate

**`rootedDirichletFejerEstimate_of_markedExtension`**:
`RootedFejerMarkedExtension → RootedDirichletFejerGlobalInput`. The marked geometry on the D1
witnesses gives D3's quantitative input: the Fejér marked ratio bound
`0 ≤ ratio ≤ 2(n + 1)^{−cη²β}`, uniform in the Fejér cutoff and on all buffered squares.

The constants:
- `c = γ₀ (2π)²/(4 log 2)`;
- `τ = β⁻¹/(2π)²`, so the gain rate is `γ = γ₀η²/τ = γ₀(2π)²η²β`;
- the activity rate is `s = max(log 2, s₀)`;
- `β₀(η)` is the maximum of `1/((2π)² min(τ₀(η), τ₁))`, `(D₂ + s + log 2 + 4K_nb)/((2π)²γ₀η²)`,
  `8K_nb/((2π)²γ₀η²)`, `4K_nb/(cη² log 2)` and `1`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open MeasureTheory FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Rotator

/-! ### The dipole mark and the source -/

theorem center_ne_axialSite {R n : ℕ} (hn : n ≤ R) (hnpos : 1 ≤ n) :
    center R ≠ axialSite R n hn := by
  intro h
  have hv := congrArg (fun p : Site R => p.1.val) h
  simp [center, axialSite] at hv
  omega

theorem rootedDipoleMark_eq_dipoleMark {R n : ℕ} (hn : n ≤ R) (hnpos : 1 ≤ n) :
    rootedDipoleMark R n hn = dipoleMark (some (center R)) (some (axialSite R n hn)) := by
  have hne : (some (center R) : Option (Site R)) ≠ some (axialSite R n hn) := fun h =>
    center_ne_axialSite hn hnpos (Option.some_injective _ h)
  funext j
  unfold rootedDipoleMark dipoleMark
  by_cases h1 : j = some (center R)
  · subst h1
    simp [hne]
  · by_cases h2 : j = some (axialSite R n hn)
    · subst h2
      simp [h1]
    · simp [h1, h2]

theorem sum_rootedDipoleMark {R n : ℕ} (hn : n ≤ R) (hnpos : 1 ≤ n) :
    ∑ j, rootedDipoleMark R n hn j = 0 := by
  rw [rootedDipoleMark_eq_dipoleMark hn hnpos]
  exact sum_univ_dipoleMark _ _

theorem pairing_dirichletDipoleSource_eq_sum (R n : ℕ) (hn : n ≤ R) (φ : Option (Site R) → ℝ) :
    Multigraph.pairing φ (dirichletDipoleSource R n hn) =
      ∑ j, φ j * (rootedDipoleMark R n hn j : ℝ) := by
  unfold Multigraph.pairing
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  unfold dirichletDipoleSource rootedDipoleMark
  split_ifs <;> simp

/-! ### The decay constant -/

/-- The exponent algebra of the final bound: for `γ = γ₀ η² (2π)² β` and
`c = γ₀ (2π)²/(4 log 2)`, `e^{4K_nb − (γ/2) log₂(n+1)} ≤ 2 (n+1)^{−c η² β}` as soon as
`c η² β log 2 ≥ 4K_nb`. -/
theorem exp_le_two_rpow {γ₀ Knb η β : ℝ} {n : ℕ} (hnpos : 1 ≤ n)
    (hpos' : 0 ≤ γ₀ * (2 * Real.pi) ^ 2 / (4 * Real.log 2) * η ^ 2 * β)
    (hβ : 4 * Knb ≤ γ₀ * (2 * Real.pi) ^ 2 / (4 * Real.log 2) * η ^ 2 * β * Real.log 2) :
    Real.exp (4 * Knb - γ₀ * η ^ 2 * (2 * Real.pi) ^ 2 * β / 2 * Real.logb 2 ((n : ℝ) + 1)) ≤
      2 * Real.rpow ((n + 1 : ℕ) : ℝ)
        (-(γ₀ * (2 * Real.pi) ^ 2 / (4 * Real.log 2) * η ^ 2 * β)) := by
  set c := γ₀ * (2 * Real.pi) ^ 2 / (4 * Real.log 2) with hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    linarith
  have hlogn : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) hn1
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [show Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)) =
      ((n + 1 : ℕ) : ℝ) ^ (-(c * η ^ 2 * β)) from rfl, Real.rpow_def_of_pos hpos, hcast]
  have e2 : 2 * Real.exp (Real.log ((n : ℝ) + 1) * -(c * η ^ 2 * β)) =
      Real.exp (Real.log 2 + Real.log ((n : ℝ) + 1) * -(c * η ^ 2 * β)) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  rw [e2]
  refine Real.exp_le_exp.2 ?_
  have hγc : γ₀ * η ^ 2 * (2 * Real.pi) ^ 2 * β / 2 * Real.logb 2 ((n : ℝ) + 1) =
      2 * (c * η ^ 2 * β) * Real.log ((n : ℝ) + 1) := by
    rw [hc, Real.logb]
    field_simp
    ring
  rw [hγc]
  have hx : 4 * Knb - Real.log 2 ≤ c * η ^ 2 * β * Real.log ((n : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hlogn hpos'
    linarith
  nlinarith

/-! ### The marked Fejér estimate -/

/-- **The rooted Dirichlet Fejér estimate from the marked extension** : the marked
geometry `RootedFejerMarkedExtension` on the D1 witnesses gives D3's quantitative input
`RootedDirichletFejerGlobalInput`, uniformly in the Fejér cutoff and on all buffered squares. -/
theorem rootedDirichletFejerEstimate_of_markedExtension (hE : RootedFejerMarkedExtension) :
    RootedDirichletFejerGlobalInput := by
  obtain ⟨γ₀, s₀, Knb, hγ₀, hKnb, hext⟩ := hE
  set s := max (Real.log 2) s₀ with hs
  obtain ⟨amp, k₀, τ₁, hamp, hk₀, hτ₁, hsamp, hquad₂, hτpar⟩ :=
    exists_gaussianActivity_params (α := 7 / 4) (K₀ := 6400) (K₁ := 8)
      (D₁ := fejerLayerD₁) (D₂ := fejerLayerD₂) (by norm_num) (by norm_num) (by norm_num)
      fejerLayerD₁_pos s
  set c := γ₀ * (2 * Real.pi) ^ 2 / (4 * Real.log 2) with hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨c, hc0, fun η hη hη2 => ?_⟩
  obtain ⟨τ₀, hτ₀, hτ⟩ := hext η hη hη2
  set m := min τ₀ τ₁ with hm
  have hm0 : 0 < m := lt_min hτ₀ hτ₁
  set Q := γ₀ * η ^ 2 * (2 * Real.pi) ^ 2 with hQ
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  set β₀ := max (max (1 / ((2 * Real.pi) ^ 2 * m)) ((fejerLayerD₂ + s + Real.log 2 + 4 * Knb) / Q))
    (max (max (8 * Knb / Q) (4 * Knb / (c * η ^ 2 * Real.log 2))) 1) with hβ₀
  have hβ₀1 : 1 ≤ β₀ := le_max_of_le_right (le_max_right _ _)
  refine ⟨β₀, by linarith, fun β hβl ξ hξ0 hξ1 hηξ hη1ξ n hnpos => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hb1 : 1 / ((2 * Real.pi) ^ 2 * m) < β :=
    lt_of_le_of_lt (le_max_of_le_left (le_max_left _ _)) hβl
  have hb2 : (fejerLayerD₂ + s + Real.log 2 + 4 * Knb) / Q < β :=
    lt_of_le_of_lt (le_max_of_le_left (le_max_right _ _)) hβl
  have hb3 : 8 * Knb / Q < β :=
    lt_of_le_of_lt (le_max_of_le_right (le_max_of_le_left (le_max_left _ _))) hβl
  have hb4 : 4 * Knb / (c * η ^ 2 * Real.log 2) < β :=
    lt_of_le_of_lt (le_max_of_le_right (le_max_of_le_left (le_max_right _ _))) hβl
  set τ := dirichletGffParameter β with hτdef
  have hτpos : 0 < τ := dirichletGffParameter_pos hβ0
  have hτm : τ < m := by
    have hb1' : 1 < (2 * Real.pi) ^ 2 * m * β := by
      have h := hb1
      rw [div_lt_iff₀ (by positivity)] at h
      linarith
    have hτeq : τ = 1 / ((2 * Real.pi) ^ 2 * β) := by
      rw [hτdef, dirichletGffParameter]
      field_simp
    rw [hτeq, div_lt_iff₀ (by positivity)]
    linarith
  have hτ₀' : τ < τ₀ := lt_of_lt_of_le hτm (min_le_left _ _)
  have hτ₁' : τ < τ₁ := lt_of_lt_of_le hτm (min_le_right _ _)
  have hγ : γ₀ * η ^ 2 / τ = Q * β := by
    rw [hτdef, dirichletGffParameter, hQ]
    field_simp
  obtain ⟨R₀, hnR₀, hR⟩ := hτ τ hτpos hτ₀' ξ hξ0 hξ1 hηξ hη1ξ n hnpos
  refine ⟨R₀, hnR₀, fun R hbuf hn => ?_⟩
  intro _ _ N hN
  have hR1 : 1 ≤ R := Nat.le_trans hnpos (Nat.le_trans hnR₀ hbuf)
  obtain ⟨W, adj, hcl⟩ := hR R hbuf hn N hN
  obtain ⟨hexp, hquad₁⟩ := hτpar τ hτpos hτ₁'
  have hρ₀ := sum_rootedDipoleMark hn hnpos
  have hℓ : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hγ₁ : fejerLayerD₂ + s + Real.log 2 + 4 * Knb ≤ γ₀ * η ^ 2 / τ := by
    rw [hγ]
    rw [div_lt_iff₀ hQ0] at hb2
    linarith
  have hγ₂ : 8 * Knb ≤ γ₀ * η ^ 2 / τ := by
    rw [hγ]
    rw [div_lt_iff₀ hQ0] at hb3
    linarith
  obtain ⟨hden, hnum0, hnum⟩ := rootedFejer_marked_ratio_bound W hN (graph_connected R hR1)
    hτpos hρ₀ hcl hamp hk₀ hsamp hquad₂ hexp hquad₁ (le_max_left _ _) (le_max_right _ _) hℓ
    hγ₁ hγ₂
  have hpair : ∀ φ : Option (Site R) → ℝ,
      Real.cos (ξ * Multigraph.pairing φ (dirichletDipoleSource R n hn)) =
        Real.cos (ξ * ∑ j, φ j * (rootedDipoleMark R n hn j : ℝ)) := fun φ => by
    rw [pairing_dirichletDipoleSource_eq_sum]
  have hεle : Real.exp (4 * Knb - γ₀ * η ^ 2 / τ / 2 * Real.logb 2 ((n : ℝ) + 1)) ≤
      2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)) := by
    have hb4' : 4 * Knb ≤ c * η ^ 2 * β * Real.log 2 := by
      have hden4 : 0 < c * η ^ 2 * Real.log 2 := by positivity
      rw [div_lt_iff₀ hden4] at hb4
      linarith
    have := exp_le_two_rpow (γ₀ := γ₀) (Knb := Knb) (η := η) (β := β) hnpos
      (by rw [← hc]; positivity) (by rw [← hc]; exact hb4')
    rw [hγ]
    rw [← hc] at this
    convert this using 3
  refine ⟨hden, ?_, ?_⟩
  · unfold dirichletFejerMarkedRatio
    simp_rw [hpair]
    exact div_nonneg hnum0 hden.le
  · unfold dirichletFejerMarkedRatio
    simp_rw [hpair]
    exact (div_le_iff₀ hden).2 (hnum.trans (mul_le_mul_of_nonneg_right hεle hden.le))

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
