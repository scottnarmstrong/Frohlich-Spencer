/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.FiniteGraph.Basic
public import FroehlichSpencer.BKT.Surface.GFFLaw
public import FroehlichSpencer.BKT.Surface.IntegerGFFLaw
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import FroehlichSpencer.BKT.Surface.SubGaussian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import FroehlichSpencer.BKT.Bridge.GFFMeasure
import FroehlichSpencer.BKT.Bridge.IntegerGFFSecondMoment
import FroehlichSpencer.BKT.Gaussian.Fejer
import FroehlichSpencer.BKT.Gaussian.FejerAverage
import FroehlichSpencer.BKT.Gaussian.FejerCellLimit
import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverseWellDefined

/-! # KP Theorem 1.5 implies the exponential-moment part of Theorem 1.1 -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.BKT.Reduction

/--
The exact proposition stated as KP Theorem 1.5 (KP p. 5), copied from the
renormalization statement.
-/
def t15Statement : Prop :=
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 → ∀ ε : ℝ, 0 < ε →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let bounds : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
            0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) ∧
            ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ, Λ.IsLaplacianPseudoinverse T →
              ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
                Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β)) ≤
                  (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) /
                    ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)
      bounds (squareFree L) (squareFree_connected L hL) ∧
        (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL))

private theorem fejerPolynomial_isSubGaussian (N : ℕ) (hN : 0 < N)
    (β : ℝ) :
    IsSubGaussian 1 0 0 β (fejerPolynomial N) := by
  refine ⟨N, hN, fun q => fejerFourierCoefficient N (q : ℤ), ?_, ?_, ?_⟩
  · intro q hq
    change fejerFourierCoefficient N (q : ℤ) = 0
    rw [fejerFourierCoefficient_nat]
    simp [not_le_of_gt hq]
  · intro φ
    rw [fejerPolynomial_eq_fourierCosineExpansion]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · intro q hq
    have hcoeff := fejerFourierCoefficient_mem_unitInterval N (q : ℤ)
    have habs : |fejerFourierCoefficient N (q : ℤ)| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_trans (by norm_num) hcoeff.1, hcoeff.2⟩
    simpa using habs

private theorem weightedGFF_bound_gives_igff_expMoment
    {V : Type*} {E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (β₀ ε : ℝ) (hε : 0 < ε)
    (hWeighted : ∀ (v : V) (β : ℝ) (hβ : 0 < β), β < β₀ →
      ∀ lam : V → ℝ → ℝ, (∀ j, IsSubGaussian 1 0 0 β (lam j)) →
        0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw G hG β hβ v) ∧
        ∀ T : (V → ℝ) →ₗ[ℝ] V → ℝ, G.IsLaplacianPseudoinverse T →
          ∀ f : V → ℝ, ∑ j, f j = 0 →
            Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β)) ≤
              (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j)
                ∂(gffLaw G hG β hβ v)) /
                ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw G hG β hβ v))
    (root : V) (βIV : ℝ) (hβIV : 0 < βIV)
    (hβlt : βIV < (2 * Real.pi) ^ 2 * β₀)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) :
    ENNReal.ofReal (Real.exp ((∑ j, f j * -(T f j)) /
        (2 * (1 + ε) * βIV))) ≤
      ∫⁻ m, ENNReal.ofReal (Real.exp (∑ j, (m j : ℝ) * f j)) ∂
        integerGFFLaw G hG βIV hβIV root := by
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have ha_ne : a ≠ 0 := ne_of_gt ha
  let βfield : ℝ := βIV / a ^ 2
  have hβfield : 0 < βfield := by
    dsimp [βfield]
    exact div_pos hβIV (sq_pos_of_ne_zero ha_ne)
  have hβfield_lt : βfield < β₀ := by
    dsimp [βfield]
    apply (div_lt_iff₀ (sq_pos_of_ne_zero ha_ne)).2
    calc
      βIV < a ^ 2 * β₀ := by simpa [a] using hβlt
      _ = β₀ * a ^ 2 := by ring
  let g : V → ℝ := fun j => f j / a
  have hg_sum : ∑ j, g j = 0 := by
    calc
      ∑ j, g j = ∑ j, f j / a := rfl
      _ = (∑ j, f j) / a := by rw [Finset.sum_div]
      _ = 0 := by rw [hf]; simp
  obtain ⟨T₀, hT₀, hT₀_unique⟩ := existsUnique_isLaplacianPseudoinverse G hG
  have hT_eq : T = T₀ := hT₀_unique T hT
  have hTg : T₀ g = fun j => a⁻¹ * T₀ f j := by
    have hg_smul : g = a⁻¹ • f := by
      ext j
      change f j / a = a⁻¹ * f j
      rw [div_eq_mul_inv]
      ring
    rw [hg_smul, map_smul]
    ext j
    rfl
  have hQ : (∑ j, g j * -(T₀ g j)) =
      (a⁻¹) ^ 2 * (∑ j, f j * -(T₀ f j)) := by
    calc
      (∑ j, g j * -(T₀ g j)) =
          ∑ j, (f j / a) * -(a⁻¹ * T₀ f j) := by
        rw [hTg]
      _ = (a⁻¹) ^ 2 * (∑ j, f j * -(T₀ f j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hscale : a ^ 2 * βfield = βIV := by
    dsimp [βfield]
    field_simp [ha_ne]
  have hExponent :
      (∑ j, g j * -(T₀ g j)) / (2 * (1 + ε) * βfield) =
        (∑ j, f j * -(T₀ f j)) / (2 * (1 + ε) * βIV) := by
    rw [hQ]
    dsimp [βfield]
    field_simp [ha_ne, hβIV.ne']
  have hT15Moment' (N : ℕ) (hN : 0 < N) :
      Real.exp ((∑ j, f j * -(T₀ f j)) / (2 * (1 + ε) * βIV)) ≤
        gffFejerRatio G (show G.Connected from hG) βfield hβfield root g N := by
    let lam : V → ℝ → ℝ := fun _ => fejerPolynomial N
    have hlam : ∀ j, IsSubGaussian 1 0 0 βfield (lam j) := by
      intro j
      exact fejerPolynomial_isSubGaussian N hN βfield
    have hT15 := hWeighted root βfield hβfield hβfield_lt lam hlam
    have hT15Moment := hT15.2 T₀ hT₀ g hg_sum
    have hnum :
        (∫ φ, Real.exp (∑ j, φ j * g j) *
          ∏ j, fejerPolynomial N (φ j) ∂gffLaw G hG βfield hβfield root) =
          gffFejerAverage G (show G.Connected from hG) βfield hβfield root g N := by
      calc
        _ = ∫ φ, Real.exp (Multigraph.pairing φ g) *
            ∏ j, fejerPolynomial N (φ j) ∂
              gffMeasure G (show G.Connected from hG) βfield hβfield root := by
          rw [gffLaw_eq_gffMeasure G hG βfield hβfield root]
          apply integral_congr_ae
          filter_upwards with φ
          rfl
        _ = gffFejerAverage G (show G.Connected from hG)
            βfield hβfield root g N :=
          (gffFejerAverage_eq_integral G (show G.Connected from hG)
            βfield hβfield root g N).symm
    have hden :
        (∫ φ, ∏ j, fejerPolynomial N (φ j) ∂
          gffLaw G hG βfield hβfield root) =
          gffFejerAverage G (show G.Connected from hG) βfield hβfield root
            (fun _ => 0) N := by
      calc
        _ = ∫ φ, Real.exp (Multigraph.pairing φ (fun _ => 0)) *
            ∏ j, fejerPolynomial N (φ j) ∂
              gffMeasure G (show G.Connected from hG) βfield hβfield root := by
          rw [gffLaw_eq_gffMeasure G hG βfield hβfield root]
          apply integral_congr_ae
          filter_upwards with φ
          simp [Multigraph.pairing]
        _ = gffFejerAverage G (show G.Connected from hG)
            βfield hβfield root (fun _ => 0) N :=
          (gffFejerAverage_eq_integral G (show G.Connected from hG)
            βfield hβfield root (fun _ => 0) N).symm
    rw [hExponent, hnum, hden] at hT15Moment
    simpa [gffFejerRatio] using hT15Moment
  have hlim := tendsto_gffFejerRatio_igff
    G (show G.Connected from hG) βfield hβfield root g
  have hreal : Real.exp ((∑ j, f j * -(T₀ f j)) /
      (2 * (1 + ε) * βIV)) ≤
        gffFejerIGFFTarget G (show G.Connected from hG) βfield hβfield root g := by
    apply (isClosed_Ici.mem_of_tendsto hlim)
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    exact hT15Moment' N hN
  have htarget : gffFejerSourceTarget G (show G.Connected from hG)
      βfield hβfield root g =
      ∫⁻ m, ENNReal.ofReal (Real.exp (∑ j, (m j : ℝ) * f j)) ∂
        integerGFFLaw G hG βIV hβIV root := by
    rw [gffFejerSourceTarget_eq_kp G (show G.Connected from hG)
      βfield hβfield root g]
    have hβeq : (2 * Real.pi) ^ 2 * βfield = βIV := by
      simpa [a] using hscale
    have hmeasure : integerGFFLaw G hG
        ((2 * Real.pi) ^ 2 * βfield)
        (mul_pos (sq_pos_of_ne_zero (by positivity)) hβfield) root =
          integerGFFLaw G hG βIV hβIV root := by
      congr 2
    rw [hmeasure]
    apply lintegral_congr_ae
    filter_upwards with m
    congr 1
    apply congrArg Real.exp
    change a *
        Multigraph.pairing (fun j => (m j : ℝ)) g =
      ∑ j, (m j : ℝ) * f j
    unfold Multigraph.pairing
    dsimp [g]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [ha_ne]
  have hrealT : Real.exp ((∑ j, f j * -(T f j)) /
      (2 * (1 + ε) * βIV)) ≤
        gffFejerIGFFTarget G (show G.Connected from hG)
          βfield hβfield root g := by
    rw [hT_eq]
    exact hreal
  rw [← htarget, gffFejerSourceTarget_eq_ofReal_igff]
  exact ENNReal.ofReal_le_ofReal hrealT

/--
KP Theorem 1.5 implies (1.6) of KP Theorem 1.1 on both  square
carriers, with the source rescaling `β_IV = (2π)² β_field`.
-/
theorem integerGFF_expMoment_lower_bound_of_t15Statement
    (hT15 : t15Statement) :
    ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let bounds : ∀ {E : Type} [Fintype E]
          (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
            Λ.IsLaplacianPseudoinverse T →
            ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
              ENNReal.ofReal (Real.exp ((∑ j, f j * -(T f j)) /
                  (2 * (1 + ε) * β))) ≤
                ∫⁻ m, ENNReal.ofReal (Real.exp (∑ j, (m j : ℝ) * f j)) ∂
                  integerGFFLaw Λ hΛ β hβ v
      bounds (squareFree L) (squareFree_connected L hL) ∧
        (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) := by
  intro ε hε
  obtain ⟨βfield₀, hβfield₀, hT15Bounds⟩ :=
    hT15 1 (by norm_num) 0 0 (by norm_num) (by norm_num) ε hε
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a ^ 2 * βfield₀,
    mul_pos (sq_pos_of_ne_zero (ne_of_gt ha)) hβfield₀, ?_⟩
  intro L hL
  dsimp only
  have hT15L := hT15Bounds L hL
  rcases hT15L with ⟨hFree, hPeriodic⟩
  constructor
  · intro v β hβ hβlt T hT f hf
    exact weightedGFF_bound_gives_igff_expMoment
      (squareFree L) (squareFree_connected L hL) βfield₀ ε hε
      hFree v β hβ (by simpa [a] using hβlt) T hT f hf
  · intro hEven v β hβ hβlt T hT f hf
    exact weightedGFF_bound_gives_igff_expMoment
      (squarePeriodic L) (squarePeriodic_connected L hL) βfield₀ ε hε
      (hPeriodic hEven) v β hβ (by simpa [a] using hβlt) T hT f hf

/-- Package the reduction as the two exponential-moment inputs consumed by
the KP Theorem 1.1 assembly: one family for free boxes and one for even
periodic boxes. -/
theorem integerGFF_expMoment_inputs_of_t15Statement
    (hT15 : t15Statement) :
    ∃ βSmall : ℝ → ℝ,
      (∀ ε : ℝ, 0 < ε → 0 < βSmall ε) ∧
      (∀ (L : ℕ) (hL : 1 < L) (ε : ℝ), 0 < ε →
        ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < βSmall ε →
          ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
            Multigraph.IsLaplacianPseudoinverse (squareFree L) T →
            ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
              ENNReal.ofReal (Real.exp
                (Multigraph.pairing f (-(T f)) /
                  (2 * (1 + ε) * β))) ≤
                ∫⁻ m, ENNReal.ofReal (Real.exp
                  (Multigraph.pairing (fun j => (m j : ℝ)) f)) ∂
                  integerGFFLaw (squareFree L)
                    (squareFree_connected L hL) β hβ v) ∧
      (∀ (L : ℕ) (hL : 1 < L) (ε : ℝ), 0 < ε → Even L →
        ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < βSmall ε →
          ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
            Multigraph.IsLaplacianPseudoinverse (squarePeriodic L) T →
            ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
              ENNReal.ofReal (Real.exp
                (Multigraph.pairing f (-(T f)) /
                  (2 * (1 + ε) * β))) ≤
                ∫⁻ m, ENNReal.ofReal (Real.exp
                  (Multigraph.pairing (fun j => (m j : ℝ)) f)) ∂
                  integerGFFLaw (squarePeriodic L)
                    (squarePeriodic_connected L hL) β hβ v) := by
  classical
  let βSmall : ℝ → ℝ := fun ε =>
    if hε : 0 < ε then
      Classical.choose
        (integerGFF_expMoment_lower_bound_of_t15Statement hT15 ε hε)
    else 1
  have hβSmall (ε : ℝ) (hε : 0 < ε) : βSmall ε = Classical.choose
      (integerGFF_expMoment_lower_bound_of_t15Statement hT15 ε hε) :=
    dite_eq_left hε
  refine ⟨βSmall, ?_, ?_, ?_⟩
  · intro ε hε
    rw [hβSmall ε hε]
    exact (Classical.choose_spec
      (integerGFF_expMoment_lower_bound_of_t15Statement hT15 ε hε)).1
  · intro L hL ε hε v β hβ hβlt T hT f hf
    have hchosen := Classical.choose_spec
      (integerGFF_expMoment_lower_bound_of_t15Statement hT15 ε hε)
    have hβlt' : β < Classical.choose
        (integerGFF_expMoment_lower_bound_of_t15Statement hT15 ε hε) := by
      exact hβlt.trans_eq (hβSmall ε hε)
    have hbox := hchosen.2 L hL
    rcases hbox with ⟨hfree, _hperiodic⟩
    have h := hfree v β hβ hβlt' T hT f hf
    simpa [Multigraph.pairing] using h
  · intro L hL ε hε hEven v β hβ hβlt T hT f hf
    have hchosen := Classical.choose_spec
      (integerGFF_expMoment_lower_bound_of_t15Statement hT15 ε hε)
    have hβlt' : β < Classical.choose
        (integerGFF_expMoment_lower_bound_of_t15Statement hT15 ε hε) := by
      exact hβlt.trans_eq (hβSmall ε hε)
    have hbox := hchosen.2 L hL
    rcases hbox with ⟨_hfree, hperiodic⟩
    have h := hperiodic hEven v β hβ hβlt' T hT f hf
    simpa [Multigraph.pairing] using h

/--
The KP Theorem 1.1 statement follows conditionally from KP Theorem 1.5:
the exponential-moment input above, together with the second-moment
and dipole assembly, gives the theorem's exact proposition.
-/
theorem t11_of_t15Statement :
    t15Statement →
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (L : ℕ) (hL : 1 < L),
        let bounds : ∀ {E : Type} [Fintype E]
            (Λ : Multigraph (Fin L × Fin L) E),
            Λ.toSimpleGraph.Connected → Prop :=
          fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
            (∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
              Multigraph.IsLaplacianPseudoinverse Λ T →
              ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
                ENNReal.ofReal (Real.exp
                    ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β))) ≤
                    ∫⁻ m, ENNReal.ofReal
                      (Real.exp (∑ j, (m j : ℝ) * f j))
                      ∂(integerGFFLaw Λ hΛ β hβ v) ∧
                  ENNReal.ofReal
                      ((∑ j, f j * -(T f j)) / ((1 + ε) * β)) ≤
                    ∫⁻ m, ENNReal.ofReal
                      ((∑ j, (m j : ℝ) * f j) ^ 2)
                      ∂(integerGFFLaw Λ hΛ β hβ v)) ∧
            ∀ j k : Fin L × Fin L,
              ENNReal.ofReal (c / β * Real.log
                (Λ.toSimpleGraph.dist j k + 1)) ≤
                ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - m k) ^ 2)
                  ∂(integerGFFLaw Λ hΛ β hβ v)
        bounds (squareFree L) (squareFree_connected L hL) ∧
          (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) := by
  intro hT15
  rcases integerGFF_expMoment_inputs_of_t15Statement hT15 with
    ⟨βSmall, hβSmall, hExpFree, hExpPeriodic⟩
  rcases integerGFF_delocalization_assemble
      βSmall hβSmall hExpFree hExpPeriodic with ⟨_c, _hc, hbound⟩
  refine ⟨(1 / 48 : ℝ), by norm_num, ?_⟩
  simpa only [Multigraph.pairing, Pi.neg_apply, Nat.cast_add, Nat.cast_one]
    using hbound

end FroehlichSpencer.BKT.Reduction

end
