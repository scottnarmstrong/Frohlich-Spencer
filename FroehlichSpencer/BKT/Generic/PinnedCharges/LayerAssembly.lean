/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerMixture
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyApplication
public import FroehlichSpencer.BKT.Rotator.TheoremC.MainD

/-!
`pinnedLayerHypothesisD_of_terminalWaves`: FS81 Theorem C's last input `PinnedLayerHypothesisD`
follows from two statements about the terminal ensembles of the scale-ordered selection run on
the comb (`IsCombTerminal`):

* `CombCoefficientBound c₁ c₂`: every terminal coefficient satisfies
  `|K(ρ)| ≤ exp(c₁ ‖ρ‖₁ + c₂ ∑_{j ≤ n_Λ(ρ)} A_j(ρ))` (`A_j` the scale-`j` cover numbers,
  `n_Λ = ⌈log₂(M d_Λ^α)⌉`);
* `PinnedTerminalWaves`: the Appendix D multiscale spin waves on every comb terminal, with at least
  `c_P ∑_{j=1}^{n_Λ} |P'_j(ρ)|` positive-scale pieces (`P'_j` the selected squares), together with
  the local clauses (support sets, routing, overlap) and a size `dsc + 1 ≤ 2^16 d_Λ`.

`CombCoefficientBound` is proved in `LayerCoefficient` (`combCoefficientBound`).

Everything else is proved here: the convex comb expansion and its neutralization on `squareZero`
(`LayerMixture`), the cover cost `A(ϱ) = ‖ϱ‖₁ + ∑_{j ≤ n_Λ} A_j`, the cover clause
`log₂(dsc + 1) ≤ A`, the layer clause `A ≤ D₁(‖ϱ‖₁ + #pieces)` from the terminal decomposition's boundary entropy count
(`pinned_boundary_entropy_chargeCutoff`, applicable because the selection's terminals are
boundary-isolated), and the entropy clause with `Z ≡ 1`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The cutoff `n_Λ(ρ) = ⌈log₂(M d_Λ(ρ)^α)⌉` of the bounded-face part. -/
def layerCutoff (ϱ : RotatorDualFace L → ℤ) : ℕ :=
  boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent (siteRestrict ϱ)

/-- The cover sum `∑_{j ≤ n_Λ} A_j` of the bounded-face part. -/
def layerCoverSum (ϱ : RotatorDualFace L → ℤ) : ℝ :=
  ∑ j ∈ Finset.range (layerCutoff ϱ + 1), (squareCoverNumber .free L j (siteRestrict ϱ) : ℝ)

/-- The cover cost of the layer: `A(ϱ) = ‖ϱ‖₁ + ∑_{j ≤ n_Λ} A_j`. -/
def layerA (ϱ : RotatorDualFace L → ℤ) : ℝ := ∑ j, |(ϱ j : ℝ)| + layerCoverSum ϱ

/-- The number of selected Appendix D squares `∑_{j=1}^{n_Λ} |P'_j|`. -/
def layerSelectedSum (ϱ : RotatorDualFace L → ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (layerCutoff ϱ),
    boundaryEntropySelectedCount (chargeCoverScale : ℝ) chargeCoverExponent (siteRestrict ϱ) j

/-- The layer constant `D₁ = 30 + |C_T| + 196/3`, `C_T` the terminal decomposition's terminal weight sum. -/
def layerD₁ : ℝ := 30 + |∑' k : ℕ, boundaryEntropyTerminalWeight k| + 196 / 3

theorem layerD₁_pos : 0 < layerD₁ := by
  unfold layerD₁
  positivity

/-! ### Residual statements -/

/-- **The coefficient bound** on comb terminals. -/
def CombCoefficientBound (c₁ c₂ : ℝ) : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T → ∀ ρ ∈ T.F,
    |T.K ρ| ≤ Real.exp (c₁ * ∑ x, |(ρ x : ℝ)| + c₂ * layerCoverSum (neutralizeAtWiredRoot ρ))

/-- The single-density wave clauses: `HasLayerWave` with the cover-cost clause replaced by at least
`c_P` positive-scale pieces per selected Appendix D square. -/
def IsTerminalWave {centerOf : (RotatorDualFace L → ℤ) → RotatorDualFace L} (α K₀ K₁ cP : ℝ)
    (ϱ : RotatorDualFace L → ℤ) (Wv : GradedSpinWave.{0, 0, 0} (squareZero L) ∅ centerOf ϱ) :
    Prop :=
  Wv.alpha = α ∧ Wv.K₀ = K₀ ∧ Wv.K₁ = K₁ ∧
    ((1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
      ∑ t ∈ (letI := Wv.finite; Finset.univ.filter fun t => Wv.scale t = 0), |Wv.charge t|) ∧
    (∀ t, ((Finset.univ.filter fun e => (squareZero L).grad (Wv.piece t) e ≠ 0).card : ℝ) ≤
      100 * 4 ^ Wv.scale t) ∧
    cP * layerSelectedSum ϱ ≤
      ((letI := Wv.finite; (Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℕ) : ℝ)

/-- **The terminal waves**: the Appendix D multiscale spin waves on every comb terminal, with
their local clauses. -/
def PinnedTerminalWaves (α K₀ K₁ cP Kv : ℝ) (Kov L₀ : ℕ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L →
  ∃ (centerOf : (RotatorDualFace L → ℤ) → RotatorDualFace L)
    (dsc : (RotatorDualFace L → ℤ) → ℕ),
    (∀ ρ : ChargeDensity L, ρ ≠ 0 →
      1 ≤ dsc (neutralizeAtWiredRoot ρ) ∧
        (dsc (neutralizeAtWiredRoot ρ) : ℝ) + 1 ≤ 2 ^ 16 * boundaryAdjustedSize ρ) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ T : SelConfig L, IsCombTerminal N T →
    ∃ (S : (RotatorDualFace L → ℤ) → Finset (SquareZeroBond L))
      (wv : ∀ ϱ ∈ T.F.image neutralizeAtWiredRoot,
        GradedSpinWave.{0, 0, 0} (squareZero L) ∅ centerOf ϱ),
      (∀ ϱ (h : ϱ ∈ T.F.image neutralizeAtWiredRoot),
        IsTerminalWave α K₀ K₁ cP ϱ (wv ϱ h) ∧
        (∀ t e, (squareZero L).grad ((wv ϱ h).piece t) e ≠ 0 → e ∈ S ϱ) ∧
        (∀ t, ∀ ϱ' ∈ T.F.image neutralizeAtWiredRoot, ϱ' ≠ ϱ →
          ∑ j, (wv ϱ h).piece t j * (ϱ' j : ℝ) = 0) ∧
        (∀ ϱ' (h' : ϱ' ∈ T.F.image neutralizeAtWiredRoot), ϱ ≠ ϱ' → ∀ t t' e,
          (squareZero L).grad ((wv ϱ h).piece t) e = 0 ∨
            (squareZero L).grad ((wv ϱ' h').piece t') e = 0) ∧
        ((S ϱ).card : ℝ) ≤ Kv * ((dsc ϱ : ℝ) + 1) ^ 2 ∧
        (∃ r : SquareZeroBond L → ℤ, (∀ e, r e ≠ 0 → e ∈ S ϱ) ∧
          (∀ e, |(r e : ℝ)| ≤ ∑ j, |(ϱ j : ℝ)|) ∧
          ∀ σ : RotatorDualFace L → ℝ,
            ∑ j, σ j * (ϱ j : ℝ) = ∑ e, (r e : ℝ) * (squareZero L).grad σ e)) ∧
      ∀ (k : ℕ) (e : SquareZeroBond L) (U : Finset (RotatorDualFace L → ℤ)),
        U ⊆ T.F.image neutralizeAtWiredRoot →
        (∀ ρ ∈ U, 2 ^ k - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (k + 1) - 2 ∧ e ∈ S ρ) → U.card ≤ Kov

/-! ### Cover numbers -/

theorem squareCoverNumber_le_card (j : ℕ) (ρ : ChargeDensity L) :
    (squareCoverNumber .free L j ρ : ℝ) ≤ (chargeSupport ρ).card := by
  classical
  have hcov : IsSquareCover .free L j ρ ((chargeSupport ρ).image (kpSquare .free L j)) :=
    ⟨fun s hs => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩,
     fun x hx => ⟨kpSquare .free L j x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
       anchor_mem_kpSquare .free L j x⟩⟩
  exact_mod_cast (squareCoverNumber_le .free L j ρ _ hcov).trans Finset.card_image_le

theorem one_le_squareCoverNumber (j : ℕ) {ρ : ChargeDensity L} (hρ : ρ ≠ 0) :
    1 ≤ squareCoverNumber .free L j ρ := by
  classical
  obtain ⟨x, hx⟩ := chargeSupport_nonempty_of_ne_zero ρ hρ
  have hmem := Finset.min'_mem ((squareCoverCandidates .free L j ρ).image Finset.card)
    (Finset.image_nonempty.mpr (squareCoverCandidates_nonempty .free L j ρ))
  obtain ⟨C, hC, hcard⟩ := Finset.mem_image.mp hmem
  have hcov := (mem_squareCoverCandidates_iff .free L j ρ C).mp hC
  obtain ⟨s, hs, -⟩ := hcov.2 x hx
  unfold squareCoverNumber
  rw [← hcard]
  exact Finset.card_pos.mpr ⟨s, hs⟩

theorem card_support_le_norm (ρ : ChargeDensity L) :
    ((chargeSupport ρ).card : ℝ) ≤ ∑ x, |(ρ x : ℝ)| := by
  calc ((chargeSupport ρ).card : ℝ) = ∑ x ∈ chargeSupport ρ, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ chargeSupport ρ, |(ρ x : ℝ)| := by
      refine Finset.sum_le_sum fun x hx => ?_
      have hx' : ρ x ≠ 0 := by simpa [chargeSupport] using hx
      have : (1 : ℤ) ≤ |ρ x| := Int.one_le_abs hx'
      exact_mod_cast this
    _ ≤ ∑ x, |(ρ x : ℝ)| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _

theorem norm_le_norm_neutralize (ρ : ChargeDensity L) :
    ∑ x, |(ρ x : ℝ)| ≤ ∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)| := by
  rw [Fintype.sum_option]
  simp only [neutralizeAtWiredRoot_some]
  linarith [abs_nonneg ((neutralizeAtWiredRoot ρ none : ℤ) : ℝ)]

theorem layerCoverSum_nonneg (ϱ : RotatorDualFace L → ℤ) : 0 ≤ layerCoverSum ϱ :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem layerSelectedSum_nonneg (ϱ : RotatorDualFace L → ℤ) : 0 ≤ layerSelectedSum ϱ :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **The layer clause** `A ≤ D₁(‖ϱ‖₁ + p)` from the terminal decomposition's boundary entropy count, for any `p` at least
the number of selected squares. -/
theorem layerA_le {F : Finset (ChargeDensity L)}
    (hiso : HasBoundaryIsolation (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ : ChargeDensity L} (hρ : ρ ∈ F) (hρ0 : ρ ≠ 0) {p : ℝ}
    (hp : layerSelectedSum (neutralizeAtWiredRoot ρ) ≤ p) :
    layerA (neutralizeAtWiredRoot ρ) ≤
      layerD₁ * (∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)| + p) := by
  set CT := ∑' k : ℕ, boundaryEntropyTerminalWeight k
  set m := ∑ x, |(ρ x : ℝ)|
  set mm := ∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)|
  have hm : m ≤ mm := norm_le_norm_neutralize ρ
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp0 : 0 ≤ p := (layerSelectedSum_nonneg _).trans hp
  have hcs : layerCoverSum (neutralizeAtWiredRoot ρ) ≤ (29 + |CT|) * m + 196 / 3 * p := by
    unfold layerCoverSum layerCutoff
    simp only [siteRestrict_neutralize]
    have hA : ∀ j, (squareCoverNumber .free L j ρ : ℝ) ≤ m :=
      fun j => (squareCoverNumber_le_card j ρ).trans (card_support_le_norm ρ)
    by_cases hn : 29 ≤ boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ
    · have hX := pinned_boundary_entropy_chargeCutoff ρ F hiso hρ hρ0 hn
      have hsel : (∑ j ∈ Finset.Icc 1
          (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ),
          boundaryEntropySelectedCount (chargeCoverScale : ℝ) chargeCoverExponent ρ j) ≤ p := by
        simpa [layerSelectedSum, layerCutoff] using hp
      have h0 : CT * (squareCoverNumber .free L 0 ρ : ℝ) ≤ |CT| * m :=
        (mul_le_mul_of_nonneg_right (le_abs_self CT) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hA 0) (abs_nonneg CT))
      have : |CT| * m ≤ (29 + |CT|) * m := by nlinarith
      linarith
    · push Not at hn
      calc (∑ j ∈ Finset.range
            (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1),
            (squareCoverNumber .free L j ρ : ℝ))
          ≤ ∑ _j ∈ Finset.range
            (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1), m :=
            Finset.sum_le_sum fun j _ => hA j
        _ = ((boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1 : ℕ) : ℝ)
            * m := by simp
        _ ≤ 29 * m := by
            apply mul_le_mul_of_nonneg_right _ hm0
            exact_mod_cast hn
        _ ≤ (29 + |CT|) * m + 196 / 3 * p := by nlinarith [abs_nonneg CT]
  unfold layerA layerD₁
  have : |CT| * m ≤ |CT| * mm := mul_le_mul_of_nonneg_left hm (abs_nonneg CT)
  nlinarith [abs_nonneg CT]

/-- **The cover clause** `log₂(dsc + 1) ≤ A` for `dsc + 1 ≤ 2^16 d_Λ`. -/
theorem logb_le_layerA {ρ : ChargeDensity L} (hρ0 : ρ ≠ 0) {d : ℕ}
    (hd : (d : ℝ) + 1 ≤ 2 ^ 16 * boundaryAdjustedSize ρ) :
    Real.logb 2 ((d : ℝ) + 1) ≤ layerA (neutralizeAtWiredRoot ρ) := by
  set D := boundaryAdjustedSize ρ
  have hD1 : 1 ≤ D := by
    by_cases hq : totalCharge ρ = 0
    · exact boundaryAdjustedSize_ge_one_of_neutral_ne_zero ρ hq hρ0
    · rw [show D = boundaryAdjustedSize ρ from rfl, boundaryAdjustedSize_of_charged ρ hq]
      exact (chargeBoundaryDistance_ge_one_of_ne_zero ρ hρ0).trans (le_max_left _ _)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hlogD : 0 ≤ Real.logb 2 D := Real.logb_nonneg (by norm_num) hD1
  have hM : (chargeCoverScale : ℝ) = 2 ^ 16 := by norm_num [chargeCoverScale]
  -- `log₂(d + 1) ≤ 16 + log₂ D`
  have h1 : Real.logb 2 ((d : ℝ) + 1) ≤ 16 + Real.logb 2 D := by
    calc Real.logb 2 ((d : ℝ) + 1) ≤ Real.logb 2 (2 ^ 16 * D) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hd
      _ = 16 + Real.logb 2 D := by
          rw [Real.logb_mul (by positivity) hDpos.ne']
          congr 1
          rw [Real.logb_pow]
          simp
  -- `16 + log₂ D ≤ n_Λ`
  have h2 : 16 + Real.logb 2 D ≤
      (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ : ℝ) := by
    unfold boundaryChargeCutoff
    refine le_trans ?_ (Nat.le_ceil _)
    rw [hM, Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hDpos _).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hDpos, Real.logb_pow]
    simp only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    have : Real.logb 2 D ≤ chargeCoverExponent * Real.logb 2 D := by
      have := one_le_chargeCoverExponent
      nlinarith
    push_cast
    linarith
  -- `n_Λ ≤ ∑_{j ≤ n_Λ} A_j ≤ A`
  have h3 : (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ : ℝ) ≤
      layerCoverSum (neutralizeAtWiredRoot ρ) := by
    unfold layerCoverSum layerCutoff
    simp only [siteRestrict_neutralize]
    calc (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ : ℝ)
        ≤ ∑ _j ∈ Finset.range
            (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1), (1 : ℝ) := by
          simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => by
          exact_mod_cast one_le_squareCoverNumber j hρ0
  have h4 : 0 ≤ ∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold layerA
  linarith

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
