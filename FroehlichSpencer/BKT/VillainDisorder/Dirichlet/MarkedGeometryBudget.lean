/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryBudgetCover
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryBudgetBad
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProfileEnergy
import Mathlib.Tactic

/-!
# The profile budget of the rooted marked composite (D2G3b)

`γ (∑_{m ∈ C} A(m) + ℓ) ≤ (‖σ‖²/16 + η² |P4Index(p)|/12800)/τ`,

where:
- `σ` is the real composite and `p` its proxy;
- `η = min(ξ, 1 − ξ)`;
- `A = layerA`;
- `ℓ = log₂(n + 1)`.

This file proves the budget with `γ = γ₀ η²/τ` for an absolute constant `γ₀`
(`markedBudgetConstant`), on every cluster of every Appendix D branch ensemble.

Hence the composite
wave (`CompositeWaveGoal` of the design note) holds unconditionally.

* **Mass.** `η² ‖ϱ‖₁ ≤ 5 ‖σ‖²` for the proxy and the cluster members, and `η² |X| ≤ ‖σ‖²`: every
  face of the support carries `|σ| ≥ η`.
* **Members.** `∑_C A_cover(m) ≤ 100 (A_cover(p) + 2|X|)` (`sum_layerCoverSum_members_le`), and
  `ℓ ≤ A_cover(p)`.
* **Entropy of the proxy.** `A_cover(p) ≤ (29 + |C_T|) ‖p‖₁ + (196/3) |P'(p)|`, from rejected-square
  neighbours (`layerCoverSum_le_of_rejected`, `hasRejectedNeighbor_rootedMarkedProxy`).

The proxy is
  not Appendix D isolated; it needs only this consequence of isolation.
* **Selected squares.** `|P'(p)| = good + bad ≤ 3 |P4Index(p)| + |X|`: good squares by the
  mod-three selection, bad squares by the laminar bound under the charged half of isolation
  (`badSelectedSum_le_card_of_far`).

The buffer `2n ≤ R` keeps the mark away from the boundary at the scale of the dipole.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges (euclideanSetDistance euclideanSetDiameter
  euclideanBoundaryDistance boundaryAdjustedSize totalCharge chargeEuclideanDiameter
  chargeBoundaryDistance IsPinnedChargeEnsemble IsBoundarySeparated AppendixDChargeGeometry
  neutralizeAtWiredRoot boundaryEntropyTerminalWeight)

/-- The entropy constant `29 + |C_T|` of the cover-cost bound. -/
def markedEntropyConstant : ℝ := 29 + |∑' k : ℕ, boundaryEntropyTerminalWeight k|

/-- The mass constant of the budget. -/
def markedMassConstant : ℝ := 204 + 505 * markedEntropyConstant + 19796 / 3

/-- **The absolute budget constant `γ₀`.** -/
def markedBudgetConstant : ℝ := min (1 / (16 * markedMassConstant)) (1 / (12800 * 19796))

theorem markedEntropyConstant_pos : 0 < markedEntropyConstant := by
  unfold markedEntropyConstant
  positivity

theorem markedMassConstant_pos : 0 < markedMassConstant := by
  unfold markedMassConstant
  have := markedEntropyConstant_pos
  positivity

theorem markedBudgetConstant_pos : 0 < markedBudgetConstant := by
  unfold markedBudgetConstant
  have := markedMassConstant_pos
  exact lt_min (by positivity) (by positivity)

variable {R n : ℕ}

/-! ### The mass of the composite -/

section Mass

variable (hn : n ≤ R) {ξ : ℝ}
  {C T : Finset (RotatorDualFace (sideLength R) → ℤ)}

/-- With disjoint face supports, the members' values at a face sum to the satellite's. -/
theorem sum_abs_members_eq_abs_satellite (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (chargeSupport (siteRestrict m)) (chargeSupport (siteRestrict m')))
    (x : Site R) :
    ∑ m ∈ C, |(m (some x) : ℝ)| = |(rootedMarkedSatellite C T (some x) : ℝ)| := by
  classical
  by_cases h : ∃ m ∈ C, m (some x) ≠ 0
  · obtain ⟨m₀, hm₀, hx⟩ := h
    have hother : ∀ m ∈ C, m ≠ m₀ → m (some x) = 0 := by
      intro m hm hne
      by_contra h'
      exact Finset.disjoint_left.1 (hdisj m hm m₀ hm₀ hne)
        (mem_chargeSupport_siteRestrict.2 h') (mem_chargeSupport_siteRestrict.2 hx)
    rw [Finset.sum_eq_single_of_mem m₀ hm₀ fun m hm hne => by rw [hother m hm hne]; simp,
      rootedMarkedSatellite_eq_of_unique hT hm₀ hother]
    split_ifs <;> simp
  · push Not at h
    rw [Finset.sum_eq_zero fun m hm => by rw [h m hm]; simp,
      rootedMarkedSatellite_eq_zero hT h]
    simp

/-- **Pointwise mass**: on every face, `η² |ϱ^𝒩| ≤ 2σ²`, `η² |p| ≤ 5σ²` and `η² 𝟙_X ≤ σ²`. -/
theorem pointwise_mass (hn0 : 0 < n) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (x : Site R) :
    dipoleGap ξ ^ 2 * |(rootedMarkedSatellite C T (some x) : ℝ)| ≤
        2 * rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) ^ 2 ∧
      dipoleGap ξ ^ 2 * |(siteRestrict (rootedMarkedProxy R n hn C T) x : ℝ)| ≤
        5 * rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) ^ 2 ∧
      (siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0 →
        dipoleGap ξ ^ 2 ≤ rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) ^ 2) := by
  classical
  set σ := rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) with hσ
  set k := rootedMarkedSatellite C T (some x) with hk
  set μ := rootedDipoleMark R n hn (some x) with hμ
  set η := dipoleGap ξ with hη
  have hη0 : 0 < η := dipoleGap_pos hξ0 hξ1
  have hη1 : η ≤ 1 := dipoleGap_le_one ξ
  have hσeq : σ = ξ * μ + k := rootedMarkedComposite_eq ξ _ C T (some x)
  have hpval : (siteRestrict (rootedMarkedProxy R n hn C T) x : ℝ) = μ + 2 * k := by
    rw [siteRestrict_rootedMarkedProxy]
    push_cast
    ring
  have hμc := rootedDipoleMark_cases R n hn (some x)
  have hμabs : |(μ : ℝ)| ≤ 1 := by
    rcases hμc with h | h | h <;> rw [← hμ] at h <;> rw [h] <;> norm_num
  have hξμ : |ξ * (μ : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hξ0]
    nlinarith [abs_nonneg (μ : ℝ)]
  -- the gap on the support
  have hgap : siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0 → η ≤ |σ| := by
    intro hp
    have h := dipoleGap_le_abs_sum_rootedMarkedComposite hn hn0 ξ C T {x} (by simpa using hp)
    simpa using h
  by_cases hp : siteRestrict (rootedMarkedProxy R n hn C T) x = 0
  · -- off the support: `μ = 0` and `k = 0`
    have hpz : (μ : ℝ) + 2 * k = 0 := by rw [← hpval, hp]; simp
    have hμ0 : μ = 0 := by
      rcases hμc with h | h | h <;> rw [← hμ] at h
      · have : ((1 : ℤ) : ℝ) + 2 * k = 0 := by rw [← h]; exact hpz
        have : (1 : ℤ) + 2 * k = 0 := by exact_mod_cast this
        omega
      · have : ((-1 : ℤ) : ℝ) + 2 * k = 0 := by rw [← h]; exact hpz
        have : (-1 : ℤ) + 2 * k = 0 := by exact_mod_cast this
        omega
      · exact h
    have hk0 : (k : ℝ) = 0 := by
      rw [hμ0] at hpz
      push_cast at hpz
      linarith
    refine ⟨?_, ?_, fun h => absurd hp h⟩
    · rw [hk0]
      simp
      positivity
    · rw [hp]
      simp
      positivity
  · have hση := hgap hp
    have hσ2 : η ^ 2 ≤ σ ^ 2 := by
      have := abs_nonneg σ
      nlinarith [sq_abs σ]
    have hσ3 : η ^ 2 * |σ| ≤ σ ^ 2 := by
      have ha : 0 ≤ |σ| := abs_nonneg σ
      calc η ^ 2 * |σ| = (η * |σ|) * η := by ring
        _ ≤ (η * |σ|) * |σ| := mul_le_mul_of_nonneg_left hση (by positivity)
        _ ≤ |σ| * |σ| := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left ha hη1) ha
        _ = σ ^ 2 := by rw [abs_mul_abs_self, sq]
    have hkabs : |(k : ℝ)| ≤ |σ| + 1 := by
      have : (k : ℝ) = σ - ξ * μ := by rw [hσeq]; ring
      rw [this]
      calc |σ - ξ * μ| ≤ |σ| + |ξ * μ| := abs_sub _ _
        _ ≤ |σ| + 1 := by linarith
    have hη2 : 0 ≤ η ^ 2 := by positivity
    have hsat : η ^ 2 * |(k : ℝ)| ≤ 2 * σ ^ 2 := by
      calc η ^ 2 * |(k : ℝ)| ≤ η ^ 2 * (|σ| + 1) := mul_le_mul_of_nonneg_left hkabs hη2
        _ = η ^ 2 * |σ| + η ^ 2 := by ring
        _ ≤ 2 * σ ^ 2 := by linarith
    refine ⟨hsat, ?_, fun _ => hσ2⟩
    rw [hpval]
    calc η ^ 2 * |(μ : ℝ) + 2 * k| ≤ η ^ 2 * (|(μ : ℝ)| + 2 * |(k : ℝ)|) := by
          apply mul_le_mul_of_nonneg_left _ hη2
          calc |(μ : ℝ) + 2 * k| ≤ |(μ : ℝ)| + |2 * (k : ℝ)| := abs_add_le _ _
            _ = |(μ : ℝ)| + 2 * |(k : ℝ)| := by rw [abs_mul]; norm_num
      _ ≤ η ^ 2 * 1 + 2 * (η ^ 2 * |(k : ℝ)|) := by nlinarith
      _ ≤ 5 * σ ^ 2 := by linarith

end Mass

/-! ### The budget -/

/-- **The profile budget of the rooted marked composite.** On every cluster `C` of an Appendix D
branch ensemble (for the marked adjacency) and every orientation `T ⊆ C`, with the buffer
`2n ≤ R`,
`γ₀ η² (∑_{m ∈ C} A(m) + log₂(n + 1)) ≤ ‖σ‖²/16 + η² |P4Index(p)| / 12800`,
`η = min(ξ, 1 − ξ)`, `γ₀ = markedBudgetConstant`. -/
theorem rootedMarkedProfileBudget (hn : n ≤ R) (hn0 : 0 < n) (hRn : 2 * n ≤ R) {ξ : ℝ}
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) :
    markedBudgetConstant * dipoleGap ξ ^ 2 *
        (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1)) ≤
      (∑ x : Site R, rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) ^ 2) / 16 +
        dipoleGap ξ ^ 2 / 12800 *
          Fintype.card (rootedMarkedP4Index (rootedMarkedProxy R n hn C T)) := by
  classical
  set η := dipoleGap ξ with hη
  set p := rootedMarkedProxy R n hn C T with hp
  set σ : Site R → ℝ := fun x => rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x)
    with hσ
  set S := ∑ x : Site R, σ x ^ 2 with hS
  set X := chargeSupport (siteRestrict p) with hX
  set P := (Fintype.card (rootedMarkedP4Index p) : ℝ) with hP
  set Lp := layerCoverSum p with hLp
  set KE := markedEntropyConstant with hKEdef
  have hη0 : 0 < η := dipoleGap_pos hξ0 hξ1
  have hη2 : 0 ≤ η ^ 2 := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hCN := (mem_clusters.1 hC).1
  have hdisj := disjoint_siteRestrict_of_subset_image hgeo.ensemble hCN
  have hM1 : (1 : ℝ) < (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
  have hα1 : (1 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  have hsuppP := chargeSupport_siteRestrict_rootedMarkedProxy hn hT hdisj
  have hp0 : siteRestrict p ≠ 0 := by
    intro h0
    have hc : center R ∈ chargeSupport (siteRestrict p) :=
      rootedMarkSites_subset_chargeSupport_proxy hn C T (by simp [rootedMarkSites])
    rw [h0] at hc
    exact (mem_chargeSupport'.1 hc) rfl
  have hmass := fun x => pointwise_mass hn hn0 hξ0 hξ1 x (C := C) (T := T)
  -- the masses
  have hmP : η ^ 2 * ∑ x, |(siteRestrict p x : ℝ)| ≤ 5 * S := by
    rw [Finset.mul_sum, hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => (hmass x).2.1
  have hmX : η ^ 2 * (X.card : ℝ) ≤ S := by
    have h1 : η ^ 2 * (X.card : ℝ) = ∑ x ∈ X, η ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [h1]
    calc ∑ x ∈ X, η ^ 2 ≤ ∑ x ∈ X, σ x ^ 2 :=
          Finset.sum_le_sum fun x hx => (hmass x).2.2 (mem_chargeSupport'.1 hx)
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => sq_nonneg _
  have hmC : η ^ 2 * ∑ m ∈ C, ∑ j, |(m j : ℝ)| ≤ 4 * S := by
    have hrooted : ∀ m ∈ C, ∑ j, |(m j : ℝ)| ≤ 2 * ∑ x : Site R, |(m (some x) : ℝ)| := by
      intro m hm
      have hsum := sum_eq_zero_of_mem_image (hCN hm)
      rw [Fintype.sum_option] at hsum ⊢
      have hnone : (m none : ℝ) = -∑ x : Site R, (m (some x) : ℝ) := by
        have : m none = -∑ x : Site R, m (some x) := by linarith
        rw [this]
        push_cast
        ring
      rw [hnone, abs_neg]
      have := Finset.abs_sum_le_sum_abs (fun x : Site R => (m (some x) : ℝ)) Finset.univ
      linarith
    have hswap : ∑ m ∈ C, ∑ x : Site R, |(m (some x) : ℝ)| =
        ∑ x : Site R, |(rootedMarkedSatellite C T (some x) : ℝ)| := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => sum_abs_members_eq_abs_satellite hT hdisj x
    have hsat : η ^ 2 * ∑ x : Site R, |(rootedMarkedSatellite C T (some x) : ℝ)| ≤ 2 * S := by
      rw [Finset.mul_sum, hS, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => (hmass x).1
    calc η ^ 2 * ∑ m ∈ C, ∑ j, |(m j : ℝ)|
        ≤ η ^ 2 * ∑ m ∈ C, 2 * ∑ x : Site R, |(m (some x) : ℝ)| :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrooted) hη2
      _ = 2 * (η ^ 2 * ∑ x : Site R, |(rootedMarkedSatellite C T (some x) : ℝ)|) := by
          rw [← Finset.mul_sum, hswap]
          ring
      _ ≤ 4 * S := by linarith
  -- the members' cover costs and the dipole term
  have hcover := sum_layerCoverSum_members_le hn hn0 hgeo.ensemble hgeo.separated hCN hT
  have hlog := logb_le_layerCoverSum_proxy hn hn0 hT hdisj
  -- the entropy of the proxy
  have hrej := hasRejectedNeighbor_rootedMarkedProxy hn hRn hgeo hC hT
  have hent := Generic.PinnedCharges.Rejected.layerCoverSum_le_of_rejected hrej hp0
  -- the selected squares
  have hfar := hasFarConstituentCharge_rootedMarkedProxy hM1 hα1 hn hn0 hgeo hC hT
  have hbad := Generic.PinnedCharges.Layer.FarCharge.badSelectedSum_le_card_of_far p hfar
  have hgood := rootedMarkedP4Index_covers_goodSquares p
  have hsel : layerSelectedSum p ≤ 3 * P + (X.card : ℝ) := by
    rw [layerSelectedSum_eq_good_add_bad]
    linarith
  -- assembly
  have hA : ∑ m ∈ C, layerA m = ∑ m ∈ C, ∑ j, |(m j : ℝ)| + ∑ m ∈ C, layerCoverSum m := by
    unfold layerA
    rw [Finset.sum_add_distrib]
  have hKE0 : 0 ≤ KE := markedEntropyConstant_pos.le
  have hentKE : Lp ≤ KE * ∑ x, |(siteRestrict p x : ℝ)| + 196 / 3 * layerSelectedSum p := hent
  have hcost : η ^ 2 * (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1)) ≤
      markedMassConstant * S + 19796 * (η ^ 2 * P) := by
    rw [hA]
    have h1 : η ^ 2 * Lp ≤ KE * (5 * S) + 196 / 3 * (η ^ 2 * (3 * P + (X.card : ℝ))) := by
      calc η ^ 2 * Lp ≤ η ^ 2 * (KE * ∑ x, |(siteRestrict p x : ℝ)| +
            196 / 3 * (3 * P + (X.card : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hη2
            nlinarith
        _ = KE * (η ^ 2 * ∑ x, |(siteRestrict p x : ℝ)|) +
            196 / 3 * (η ^ 2 * (3 * P + (X.card : ℝ))) := by ring
        _ ≤ KE * (5 * S) + 196 / 3 * (η ^ 2 * (3 * P + (X.card : ℝ))) := by
            nlinarith
    have h2 : η ^ 2 * ∑ m ∈ C, layerCoverSum m ≤ 100 * (η ^ 2 * Lp) + 200 * S := by
      have := mul_le_mul_of_nonneg_left hcover hη2
      nlinarith
    have h3 : η ^ 2 * Real.logb 2 ((n : ℝ) + 1) ≤ η ^ 2 * Lp :=
      mul_le_mul_of_nonneg_left hlog hη2
    unfold markedMassConstant
    rw [← hKEdef]
    nlinarith
  -- the constant
  have hγ1 : markedBudgetConstant * markedMassConstant ≤ 1 / 16 := by
    have h := min_le_left (1 / (16 * markedMassConstant)) (1 / (12800 * 19796))
    have hpos := markedMassConstant_pos
    calc markedBudgetConstant * markedMassConstant
        ≤ 1 / (16 * markedMassConstant) * markedMassConstant :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = 1 / 16 := by field_simp
  have hγ2 : markedBudgetConstant * 19796 ≤ 1 / 12800 := by
    have h := min_le_right (1 / (16 * markedMassConstant)) (1 / (12800 * 19796))
    calc markedBudgetConstant * 19796 ≤ 1 / (12800 * 19796) * 19796 :=
          mul_le_mul_of_nonneg_right h (by norm_num)
      _ = 1 / 12800 := by norm_num
  have hγ0 := markedBudgetConstant_pos
  have hP0 : 0 ≤ P := by positivity
  calc markedBudgetConstant * η ^ 2 * (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1))
      = markedBudgetConstant * (η ^ 2 * (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1))) := by
        ring
    _ ≤ markedBudgetConstant * (markedMassConstant * S + 19796 * (η ^ 2 * P)) :=
        mul_le_mul_of_nonneg_left hcost hγ0.le
    _ = (markedBudgetConstant * markedMassConstant) * S +
        (markedBudgetConstant * 19796) * (η ^ 2 * P) := by ring
    _ ≤ 1 / 16 * S + 1 / 12800 * (η ^ 2 * P) := by
        have hηP : 0 ≤ η ^ 2 * P := by positivity
        nlinarith
    _ = S / 16 + η ^ 2 / 12800 * P := by ring

/-! ### The composite wave -/

/--
For every
cluster `C` of an Appendix D branch ensemble and every orientation `T ⊆ C`, with the buffer
`2n ≤ R`, some root-zero wave `a₀` is orthogonal to the remainder and has
`γ₀ η²/τ (∑_{m ∈ C} A(m) + log₂(n + 1)) ≤ E_τ(a₀, σ)`, `η = min(ξ, 1 − ξ)`.
-/
theorem rootedMarkedCompositeWave (hn : n ≤ R) (hn0 : 0 < n) (hRn : 2 * n ≤ R) {ξ τ : ℝ}
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hτ : 0 < τ) {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) :
    ∃ a₀ : RotatorDualFace (sideLength R) → ℝ,
      a₀ none = 0 ∧
      (∀ ϱ ∈ remainder (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
        (F.image neutralizeAtWiredRoot) C,
        Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) ∧
      markedBudgetConstant * dipoleGap ξ ^ 2 / τ *
          (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1)) ≤
        gffTranslationEnergy (squareZero (sideLength R)) τ a₀
          (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) := by
  have hL : 1 < sideLength R := by unfold sideLength; omega
  have hbudget := rootedMarkedProfileBudget hn hn0 hRn hξ0 hξ1 hgeo hC hT
  refine rootedMarkedCompositeWave_of_profileBudget hn hn0 (by norm_num [chargeCoverScale])
    (by norm_num [chargeCoverExponent]) rfl rfl hξ0 hξ1 hτ F hgeo C hC T hT hL ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hτ]
  exact hbudget

/-- **`CompositeWaveGoal` in the interface's rate.** For every gap `0 < η ≤ min(ξ, 1 − ξ)`, every
cluster and orientation of the marked expansion of an Appendix D branch has a composite wave with
gain `γ₀ η²/τ (∑_C A + log₂(n + 1))`. -/
theorem rootedMarkedCompositeWaveGoal (hn : n ≤ R) (hn0 : 0 < n) (hRn : 2 * n ≤ R)
    {ξ τ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hτ : 0 < τ) (hη0 : 0 ≤ η) (hηξ : η ≤ ξ)
    (hη1 : η ≤ 1 - ξ) {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F) :
    ∀ C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot), ∀ T ⊆ C,
      ∃ a₀ : RotatorDualFace (sideLength R) → ℝ,
        (∀ ϱ ∈ remainder (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
          (F.image neutralizeAtWiredRoot) C,
          Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) ∧
        markedBudgetConstant * η ^ 2 / τ * (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1)) ≤
          gffTranslationEnergy (squareZero (sideLength R)) τ a₀
            (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) := by
  intro C hC T hT
  obtain ⟨a₀, -, horth, hE⟩ := rootedMarkedCompositeWave hn hn0 hRn hξ0 hξ1 hτ hgeo hC hT
  refine ⟨a₀, horth, le_trans ?_ hE⟩
  have hηg : η ^ 2 ≤ dipoleGap ξ ^ 2 := by
    have : η ≤ dipoleGap ξ := le_min hηξ hη1
    nlinarith
  have hcost : 0 ≤ ∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1) := by
    have h1 : 0 ≤ ∑ m ∈ C, layerA m := Finset.sum_nonneg fun m _ => by
      unfold layerA layerCoverSum
      positivity
    have h2 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
      Real.logb_nonneg (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg n))
    linarith
  have hγ := markedBudgetConstant_pos
  have hdiv : markedBudgetConstant * η ^ 2 / τ ≤ markedBudgetConstant * dipoleGap ξ ^ 2 / τ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hηg hγ.le) hτ.le
  exact mul_le_mul_of_nonneg_right hdiv hcost

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
