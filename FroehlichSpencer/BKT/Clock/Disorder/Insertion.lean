/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.FiniteCarrier
public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# Finite insertion and Fourier bookkeeping for the rotator-clock disorder observable
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Periodic

/-- The plane-rotator edge factor used in a finite graph clock law. -/
def insertionEdgeFactor (β t : ℝ) : ℝ := Real.exp (β * Real.cos t)

/-- The finite graph's unnormalized free `ℤ_N` rotator weight. -/
def insertionClockWeight {V E : Type*} [Fintype E]
    (src tgt : E → V) (N : ℕ) (β : ℝ) (_hN : 0 < N) (k : V → Fin N) : ℝ :=
  ∏ e : E, insertionEdgeFactor β (clockAngles N k (src e) - clockAngles N k (tgt e))

/-- The marked-bond disorder insertion, oriented as `src - tgt`. -/
def insertionClockDisorder {V E : Type*} [Fintype E] [DecidableEq E]
    (src tgt : E → V) (N : ℕ) (β ξ : ℝ) (_hN : 0 < N) (M : Finset E)
    (k : V → Fin N) : ℝ :=
  ∏ e : E, if e ∈ M then
    insertionEdgeFactor β (clockAngles N k (src e) - clockAngles N k (tgt e) + 2 * Real.pi * ξ) /
      insertionEdgeFactor β (clockAngles N k (src e) - clockAngles N k (tgt e))
    else 1

/-- The finite graph weight with the fractional twist inserted on each marked bond. -/
def insertionTwistedClockWeight {V E : Type*} [Fintype E] [DecidableEq E]
    (src tgt : E → V) (N : ℕ) (β ξ : ℝ) (_hN : 0 < N) (M : Finset E)
    (k : V → Fin N) : ℝ :=
  ∏ e : E, insertionEdgeFactor β
    (clockAngles N k (src e) - clockAngles N k (tgt e) +
      if e ∈ M then 2 * Real.pi * ξ else 0)

/-- Pointwise finite-volume insertion identity. -/
theorem insertionClockWeight_mul_disorder_eq_twisted {V E : Type*} [Fintype E]
    [DecidableEq E] (src tgt : E → V) (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (M : Finset E) (k : V → Fin N) :
    insertionClockWeight src tgt N β hN k * insertionClockDisorder src tgt N β ξ hN M k =
      insertionTwistedClockWeight src tgt N β ξ hN M k := by
  unfold insertionClockWeight insertionClockDisorder insertionTwistedClockWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  split_ifs with hm
  · simp only [insertionEdgeFactor]
    field_simp [Real.exp_ne_zero]
  · simp [insertionEdgeFactor]

/-- The `Nℤ`-valued signed charge created by choosing one integer Fourier mode on each seam edge.
-/
def seamIntegerCharge {N r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (modes : Fin r → Fin N)
    (v : RotatorSpinSite (2 * L)) : ℤ :=
  ∑ i : Fin r,
    ((if v = seamUpperSite hL hr i then (modes i : ℤ) else 0) -
      (if v = seamLowerSite hL hr i then (modes i : ℤ) else 0))

/-- The real charge paired with a clock angle after the seam's finite Fourier expansion. -/
def seamFourierCharge {r L : ℕ} (N : ℕ) (_hN : 0 < N) (hL : 0 < L) (hr : r ≤ L)
    (modes : Fin r → Fin N) : RotatorSpinSite (2 * L) → ℝ :=
  fun v => (seamIntegerCharge hL hr modes v : ℝ) / N

/-- Every seam Fourier charge is compatible with the `N`-clock comb. -/
theorem seamFourierCharge_clockCompatible {r L : ℕ} (N : ℕ) (hN : 0 < N)
    (hL : 0 < L) (hr : r ≤ L) (modes : Fin r → Fin N) :
    IsClockCompatible (N : ℝ) (seamFourierCharge N hN hL hr modes) := by
  intro v
  refine ⟨seamIntegerCharge hL hr modes v, ?_⟩
  unfold seamFourierCharge
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Each edge mode contributes opposite endpoint charges, so the total seam Fourier charge is
neutral. -/
theorem seamFourierCharge_neutral {r L : ℕ} (N : ℕ) (hN : 0 < N)
    (hL : 0 < L) (hr : r ≤ L) (modes : Fin r → Fin N) :
    ∑ v : RotatorSpinSite (2 * L), seamFourierCharge N hN hL hr modes v = 0 := by
  have hz : ∑ v : RotatorSpinSite (2 * L), seamIntegerCharge hL hr modes v = 0 := by
    unfold seamIntegerCharge
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hz' : ∑ v : RotatorSpinSite (2 * L),
      (seamIntegerCharge hL hr modes v : ℝ) = 0 := by exact_mod_cast hz
  unfold seamFourierCharge
  calc
    ∑ v : RotatorSpinSite (2 * L),
        (seamIntegerCharge hL hr modes v : ℝ) / N =
      (N : ℝ)⁻¹ * ∑ v : RotatorSpinSite (2 * L),
        (seamIntegerCharge hL hr modes v : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          simp only [div_eq_mul_inv]
          ring
    _ = 0 := by rw [hz']; simp

/-- The continuous seam insertion under the compact clock law, written on the `φ = Nθ` carrier.
-/
def clockDisorderField {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (φ : RotatorSpinSite (2 * L) → ℝ) (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  ∏ i : Fin r, Real.exp (β * (Real.cos
    ((φ (seamUpperSite hL hr i) - φ (seamLowerSite hL hr i)) / N + 2 * Real.pi * ξ) -
    Real.cos ((φ (seamUpperSite hL hr i) - φ (seamLowerSite hL hr i)) / N)))

/-- The continuous seam insertion is continuous on the compact angle carrier. -/
theorem continuous_clockDisorderField {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hL : 0 < L) (hr : r ≤ L) :
    Continuous (fun φ : RotatorSpinSite (2 * L) → ℝ => clockDisorderField N β ξ φ hL hr) := by
  unfold clockDisorderField
  fun_prop

/-- A uniform finite bound for the continuous seam insertion. -/
theorem abs_clockDisorderField_le {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hL : 0 < L) (hr : r ≤ L) (φ : RotatorSpinSite (2 * L) → ℝ) :
    |clockDisorderField N β ξ φ hL hr| ≤ Real.exp (2 * |β|) ^ r := by
  have hpos : 0 < clockDisorderField N β ξ φ hL hr := by
    unfold clockDisorderField
    exact Finset.prod_pos fun i _ => Real.exp_pos _
  have hfactor (i : Fin r) :
      Real.exp (β * (Real.cos
          ((φ (seamUpperSite hL hr i) - φ (seamLowerSite hL hr i)) / N + 2 * Real.pi * ξ) -
          Real.cos ((φ (seamUpperSite hL hr i) - φ (seamLowerSite hL hr i)) / N))) ≤
        Real.exp (2 * |β|) := by
    apply Real.exp_le_exp.mpr
    set d := (φ (seamUpperSite hL hr i) - φ (seamLowerSite hL hr i)) / N
    have hc₁ : |Real.cos (d + 2 * Real.pi * ξ)| ≤ 1 := Real.abs_cos_le_one _
    have hc₀ : |Real.cos d| ≤ 1 := Real.abs_cos_le_one _
    have h₁ : β * Real.cos (d + 2 * Real.pi * ξ) ≤ |β| := by
      calc
        β * Real.cos (d + 2 * Real.pi * ξ) ≤ |β * Real.cos (d + 2 * Real.pi * ξ)| :=
          le_abs_self _
        _ = |β| * |Real.cos (d + 2 * Real.pi * ξ)| := abs_mul _ _
        _ ≤ |β| := mul_le_of_le_one_right (abs_nonneg β) hc₁
    have h₀ : -(β * Real.cos d) ≤ |β| := by
      calc
        -(β * Real.cos d) ≤ |-(β * Real.cos d)| := le_abs_self _
        _ = |β| * |Real.cos d| := by rw [abs_neg, abs_mul]
        _ ≤ |β| := mul_le_of_le_one_right (abs_nonneg β) hc₀
    nlinarith
  rw [abs_of_pos hpos]
  unfold clockDisorderField
  calc
    ∏ i : Fin r, Real.exp (β * (Real.cos
        ((φ (seamUpperSite hL hr i) - φ (seamLowerSite hL hr i)) / N + 2 * Real.pi * ξ) -
        Real.cos ((φ (seamUpperSite hL hr i) - φ (seamLowerSite hL hr i)) / N))) ≤
      ∏ _i : Fin r, Real.exp (2 * |β|) := by
        refine Finset.prod_le_prod₀ (fun i _ => Real.exp_pos _ |>.le) fun i _ => hfactor i
    _ = Real.exp (2 * |β|) ^ r := by simp

/-- The continuous seam insertion at each Fejér cell center is the literal finite clock observable.
-/
theorem clockDisorderField_cellCenter {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (hL : 0 < L) (hr : r ≤ L) (k : RotatorSpinSite (2 * L) → Fin N) :
    clockDisorderField N β ξ (fun v => cellCenter N (k v)) hL hr =
      clockDisorder N β ξ hN k hL hr := by
  unfold clockDisorderField clockDisorder
  apply Finset.prod_congr rfl
  intro i hi
  have harg :
      (cellCenter N (k (seamUpperSite hL hr i)) - cellCenter N (k (seamLowerSite hL hr i))) / N =
        clockAngles N k (seamUpperSite hL hr i) - clockAngles N k (seamLowerSite hL hr i) := by
    rw [cellCenter_sub N (k (seamUpperSite hL hr i)) (k (seamLowerSite hL hr i)) hN]
    rfl
  rw [harg]
  unfold clockDisorderFactor
  rw [← Real.exp_sub]
  congr 1
  ring

/-- The Fejér ratio approximating the finite clock-disorder expectation. -/
def clockDisorderFejerRatio {r L : ℕ} (N : ℕ) (β ξ : ℝ) (_hN : 0 < N)
    (hL : 0 < L) (hr : r ≤ L) (M : ℕ) : ℝ :=
  (∫ φ, clockDisorderField N β ξ φ hL hr *
      ∏ v, fejerPolynomial M (φ v - clockOffset N)
      ∂clockLaw β N (squareFree (2 * L + 1))) /
    ∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N)
      ∂clockLaw β N (squareFree (2 * L + 1))

/-- The Fejér ratio converges to the exact finite comb-law seam expectation. -/
theorem tendsto_clockDisorderFejerRatio {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (hβ : 0 ≤ β) (hL : 0 < L) (hr : r ≤ L) :
    Tendsto (clockDisorderFejerRatio N β ξ hN hL hr) atTop
      (𝓝 (clockDisorderExpectation N β ξ hN hL hr)) := by
  let V := RotatorSpinSite (2 * L)
  let G := squareFree (2 * L + 1)
  let μ := ((clockBoxMass β N (relabelGraph G (siteEquiv V)))⁻¹).toReal
  let A := (2 * Real.pi) ^ Fintype.card V
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hμ : 0 < μ := by
    have h0 := clockBoxMass_pos (relabelGraph G (siteEquiv V)) hβ hN'
    have h1 := clockBoxMass_ne_top (n := (N : ℝ)) (relabelGraph G (siteEquiv V)) hβ
    exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0.ne')
  have hA : 0 < A := by
    dsimp [A]
    exact pow_pos (by positivity) _
  have hpartition : 0 < clockDisorderPartition N L β hN :=
    clockDisorderPartition_pos N L β hN
  have hsumDen :
      (∑ k : V → Fin N, clockDensity β N G (fun v => cellCenter N (k v))) =
        clockDisorderPartition N L β hN := by
    unfold clockDisorderPartition
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [clockDensity_cellCenter N (2 * L) hN β k]
  have hsumNum :
      (∑ k : V → Fin N, clockDensity β N G (fun v => cellCenter N (k v)) *
        clockDisorderField N β ξ (fun v => cellCenter N (k v)) hL hr) =
        ∑ k : V → Fin N,
          clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [clockDensity_cellCenter N (2 * L) hN β k,
      clockDisorderField_cellCenter N β ξ hN hL hr k]
    ring
  have hnum0 := tendsto_integral_clockLaw_fejer hβ (n := N) G
    (clockDisorderField N β ξ · hL hr) (continuous_clockDisorderField N β ξ hL hr)
    (C := Real.exp (2 * |β|) ^ r) (fun φ => abs_clockDisorderField_le N β ξ hL hr φ)
  have hnum : Tendsto
      (fun M : ℕ => ∫ φ, clockDisorderField N β ξ φ hL hr *
        ∏ v, fejerPolynomial M (φ v - clockOffset N) ∂clockLaw β N G) atTop
      (𝓝 (μ * (A * ∑ k : V → Fin N,
        clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k))) := by
    have h := hnum0
    rw [hsumNum] at h
    simpa only [μ, A] using h
  have hden0 := tendsto_integral_clockLaw_fejer hβ (n := N) G (fun _ => (1 : ℝ))
    continuous_const (C := 1) (fun _ => by simp)
  have hden : Tendsto
      (fun M : ℕ => ∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N)
        ∂clockLaw β N G) atTop
      (𝓝 (μ * (A * clockDisorderPartition N L β hN))) := by
    have h := hden0
    simp only [one_mul, mul_one] at h
    rw [hsumDen] at h
    simpa only [μ, A] using h
  have hdenlimit : 0 < μ * (A * clockDisorderPartition N L β hN) :=
    mul_pos hμ (mul_pos hA hpartition)
  have hratio := hnum.div hden hdenlimit.ne'
  have hlimEq :
      (μ * (A * ∑ k : V → Fin N,
          clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k)) /
        (μ * (A * clockDisorderPartition N L β hN)) =
        clockDisorderExpectation N β ξ hN hL hr := by
    unfold clockDisorderExpectation
    field_simp [hμ.ne', hA.ne', hpartition.ne']
    ring
  have hratio' : Tendsto
      (fun M : ℕ =>
        (∫ φ, clockDisorderField N β ξ φ hL hr *
            ∏ v, fejerPolynomial M (φ v - clockOffset N) ∂clockLaw β N G) /
          ∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N)
            ∂clockLaw β N G) atTop (𝓝 (clockDisorderExpectation N β ξ hN hL hr)) := by
    rw [hlimEq] at hratio
    exact hratio
  change Tendsto
    (fun M : ℕ =>
      (∫ φ, clockDisorderField N β ξ φ hL hr *
          ∏ v, fejerPolynomial M (φ v - clockOffset N)
          ∂clockLaw β N (squareFree (2 * L + 1))) /
        ∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N)
          ∂clockLaw β N (squareFree (2 * L + 1))) atTop
    (𝓝 (clockDisorderExpectation N β ξ hN hL hr))
  exact hratio'

end FroehlichSpencer.BKT.Clock.Disorder

end
