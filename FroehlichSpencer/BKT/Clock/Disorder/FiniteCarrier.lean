/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
public import FroehlichSpencer.BKT.Rotator.FreeBox
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
The source seam is the vertical path from `(L+i+1,L)` to
`(L+i+1,L+1)`.

The source carrier for the disorder expectation is every subsequential limit along centered
free-square boxes.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Filter Topology
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Compact

/-- Lower seam site at the centered coordinate `(L+i+1,L)` in the free square of radius `L`. -/
def seamLowerSite {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    RotatorSpinSite (2 * L) :=
  (⟨L + i.val + 1, by have := i.isLt; omega⟩, ⟨L, by omega⟩)

/-- Upper seam site at the centered coordinate `(L+i+1,L+1)` in the free square of radius `L`. -/
def seamUpperSite {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    RotatorSpinSite (2 * L) :=
  (⟨L + i.val + 1, by have := i.isLt; omega⟩, ⟨L + 1, by omega⟩)

/-- The source-oriented one-bond disorder ratio at the seam. -/
def clockDisorderFactor {r L : ℕ} (N : ℕ) (β ξ : ℝ) (k : RotatorSpinSite (2 * L) → Fin N)
    (hL : 0 < L) (hr : r ≤ L) (i : Fin r) : ℝ :=
  let d := clockAngles N k (seamUpperSite hL hr i) - clockAngles N k (seamLowerSite hL hr i)
  Real.exp (β * Real.cos (d + 2 * Real.pi * ξ)) / Real.exp (β * Real.cos d)

/-- The (1.32) disorder insertion on the `r` oriented bonds crossing the straight seam. -/
def clockDisorder {r L : ℕ} (N : ℕ) (β ξ : ℝ) (_hN : 0 < N)
    (k : RotatorSpinSite (2 * L) → Fin N)
    (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  ∏ i : Fin r, clockDisorderFactor N β ξ k hL hr i

/--
The partition function of the finite comb law on the centered square of radius `L`.

This is the finite sum of `clockBoxWeight`, the configuration form of (7.1)--(7.2).
-/
def clockDisorderPartition (N L : ℕ) (β : ℝ) (_hN : 0 < N) : ℝ :=
  ∑ k : RotatorSpinSite (2 * L) → Fin N, clockBoxWeight N (2 * L) β k

/-- The probability mass of a clock configuration under the finite free comb law. -/
def clockCombProbabilityMass (N L : ℕ) (β : ℝ) (hN : 0 < N) (k : RotatorSpinSite (2 * L) → Fin N) :
    ℝ := clockBoxWeight N (2 * L) β k / clockDisorderPartition N L β hN

/-- The finite free clock partition function is strictly positive. -/
theorem clockDisorderPartition_pos (N L : ℕ) (β : ℝ) (hN : 0 < N) :
    0 < clockDisorderPartition N L β hN := by
  have hconfig : Nonempty (RotatorSpinSite (2 * L) → Fin N) := ⟨fun _ => ⟨0, hN⟩⟩
  unfold clockDisorderPartition
  exact Finset.sum_pos (fun k _ => Real.exp_pos _)
    ⟨(fun _ => ⟨0, hN⟩), Finset.mem_univ _⟩

/-- The finite comb masses sum to one. -/
theorem sum_clockCombProbabilityMass_eq_one (N L : ℕ) (β : ℝ) (hN : 0 < N) :
    ∑ k : RotatorSpinSite (2 * L) → Fin N, clockCombProbabilityMass N L β hN k = 1 := by
  unfold clockCombProbabilityMass
  calc
    ∑ k : RotatorSpinSite (2 * L) → Fin N,
        clockBoxWeight N (2 * L) β k / clockDisorderPartition N L β hN =
      (clockDisorderPartition N L β hN)⁻¹ *
        ∑ k : RotatorSpinSite (2 * L) → Fin N, clockBoxWeight N (2 * L) β k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [div_eq_mul_inv]
          ring
    _ = 1 := by
      change (clockDisorderPartition N L β hN)⁻¹ *
        clockDisorderPartition N L β hN = 1
      exact inv_mul_cancel₀ (ne_of_gt (clockDisorderPartition_pos N L β hN))

/--
The finite free-box expectation of the seam disorder observable under the finite
comb law (the clock Gibbs weights of (7.1)--(7.2)).
-/
def clockDisorderExpectation {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  (∑ k : RotatorSpinSite (2 * L) → Fin N,
    clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k) /
    clockDisorderPartition N L β hN

/-- The expectation ratio is the ordinary expectation against the normalized finite comb law. -/
theorem clockDisorderExpectation_eq_sum (N : ℕ) {r L : ℕ} (β ξ : ℝ)
    (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    clockDisorderExpectation N β ξ hN hL hr =
      ∑ k : RotatorSpinSite (2 * L) → Fin N,
        clockDisorder N β ξ hN k hL hr * clockCombProbabilityMass N L β hN k := by
  unfold clockDisorderExpectation clockCombProbabilityMass
  calc
    (∑ k : RotatorSpinSite (2 * L) → Fin N,
      clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k) /
        clockDisorderPartition N L β hN =
      (clockDisorderPartition N L β hN)⁻¹ *
        ∑ k : RotatorSpinSite (2 * L) → Fin N,
          clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k := by ring
    _ = ∑ k : RotatorSpinSite (2 * L) → Fin N,
        (clockDisorderPartition N L β hN)⁻¹ *
          (clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k) := by
      rw [Finset.mul_sum]
    _ = ∑ k : RotatorSpinSite (2 * L) → Fin N,
        clockDisorder N β ξ hN k hL hr *
          (clockBoxWeight N (2 * L) β k / clockDisorderPartition N L β hN) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [div_eq_mul_inv]
      ring

/-- The free-box exhaustion sequence, starting with a box containing the complete seam. -/
def clockDisorderExpectationExhaustion (N r : ℕ) (β ξ : ℝ) (hN : 0 < N) (hr : 0 < r) :
    ℕ → ℝ :=
  fun t => clockDisorderExpectation (r := r) (L := r + t) N β ξ hN (by omega) (by omega)

/--
A source free-state value for the disorder observable: any subsequential limit along the
centered-square exhaustion.
-/
def IsClockDisorderLimitPoint (N r : ℕ) (β ξ c : ℝ) (hN : 0 < N) (hr : 0 < r) : Prop :=
  ∃ s : ℕ → ℕ, StrictMono s ∧
    Tendsto (fun t => clockDisorderExpectationExhaustion N r β ξ hN hr (s t)) atTop (𝓝 c)

/-- C0 target: the source free-state carrier is exactly the set of subsequential limits of the
finite comb-law seam expectations along the square exhaustion. -/
theorem clockDisorderLimitPoint_spec (N r : ℕ) (hr : 0 < r) (β ξ c : ℝ) (hN : 0 < N) :
    IsClockDisorderLimitPoint N r β ξ c hN hr ↔
      ∃ s : ℕ → ℕ, StrictMono s ∧
        Tendsto (fun t =>
          clockDisorderExpectation (r := r) (L := r + s t) N β ξ hN (by omega) (by omega))
          atTop (𝓝 c) := Iff.rfl

/-- At zero coupling every finite box has unit disorder expectation. -/
theorem clockDisorderExpectation_zeroCoupling {r L : ℕ} (N : ℕ) (ξ : ℝ)
    (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    clockDisorderExpectation N 0 ξ hN hL hr = 1 := by
  simp [clockDisorderExpectation, clockDisorderPartition, clockDisorder, clockDisorderFactor,
    clockBoxWeight, hN.ne']

/-- Non-vacuity check: at zero coupling the finite disorder expectation is identically one, so
the selected source carrier contains the value one. -/
theorem exists_clockDisorderLimitPoint_zeroCoupling (N r : ℕ) (hr : 0 < r)
    (hN : 0 < N) (ξ : ℝ) :
    ∃ c, IsClockDisorderLimitPoint N r 0 ξ c hN hr := by
  refine ⟨1, ⟨id, strictMono_id, ?_⟩⟩
  have hseq : clockDisorderExpectationExhaustion N r 0 ξ hN hr = fun _ => 1 := by
    funext t
    exact clockDisorderExpectation_zeroCoupling N ξ hN (by omega) (by omega)
  rw [hseq]
  exact tendsto_const_nhds

/-- Every finite seam factor is strictly positive. -/
theorem clockDisorderFactor_pos {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (k : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    0 < clockDisorderFactor N β ξ k hL hr i := by
  unfold clockDisorderFactor
  exact div_pos (Real.exp_pos _) (Real.exp_pos _)

/-- A single seam factor is at most `exp (2 |β|)`. -/
theorem clockDisorderFactor_le {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (k : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    clockDisorderFactor N β ξ k hL hr i ≤ Real.exp (2 * |β|) := by
  unfold clockDisorderFactor
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  let d := clockAngles N k (seamUpperSite hL hr i) - clockAngles N k (seamLowerSite hL hr i)
  have hcos₁ : |Real.cos (d + 2 * Real.pi * ξ)| ≤ 1 := Real.abs_cos_le_one _
  have hcos₀ : |Real.cos d| ≤ 1 := Real.abs_cos_le_one _
  have h₁ : β * Real.cos (d + 2 * Real.pi * ξ) ≤ |β| := by
    calc
      β * Real.cos (d + 2 * Real.pi * ξ) ≤ |β * Real.cos (d + 2 * Real.pi * ξ)| := le_abs_self _
      _ = |β| * |Real.cos (d + 2 * Real.pi * ξ)| := abs_mul _ _
      _ ≤ |β| := mul_le_of_le_one_right (abs_nonneg β) hcos₁
  have h₀ : -(β * Real.cos d) ≤ |β| := by
    calc
      -(β * Real.cos d) ≤ |-(β * Real.cos d)| := le_abs_self _
      _ = |β| * |Real.cos d| := by rw [abs_neg, abs_mul]
      _ ≤ |β| := mul_le_of_le_one_right (abs_nonneg β) hcos₀
  change β * Real.cos (d + 2 * Real.pi * ξ) - β * Real.cos d ≤ 2 * |β|
  linarith

/-- The path insertion is positive and at most the product of its one-bond upper bounds. -/
theorem clockDisorder_pos {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (k : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) :
    0 < clockDisorder N β ξ hN k hL hr := by
  unfold clockDisorder
  exact Finset.prod_pos fun i _ => clockDisorderFactor_pos N β ξ k hL hr i

theorem clockDisorder_le {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (k : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) :
    clockDisorder N β ξ hN k hL hr ≤ Real.exp (2 * |β|) ^ r := by
  unfold clockDisorder
  calc
    ∏ i : Fin r, clockDisorderFactor N β ξ k hL hr i ≤
        ∏ _i : Fin r, Real.exp (2 * |β|) := by
      refine Finset.prod_le_prod₀ (fun i _ => (clockDisorderFactor_pos N β ξ k hL hr i).le)
        fun i _ => clockDisorderFactor_le N β ξ k hL hr i
    _ = Real.exp (2 * |β|) ^ r := by simp

/-- The finite seam expectation lies in the compact interval implied by the factorwise cosine
bound. -/
theorem clockDisorderExpectation_mem_Icc {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    clockDisorderExpectation N β ξ hN hL hr ∈ Set.Icc 0 (Real.exp (2 * |β|) ^ r) := by
  have hweight (k : RotatorSpinSite (2 * L) → Fin N) : 0 < clockBoxWeight N (2 * L) β k :=
    Real.exp_pos _
  have hden : 0 < clockDisorderPartition N L β hN := clockDisorderPartition_pos N L β hN
  have hnum : 0 < ∑ k : RotatorSpinSite (2 * L) → Fin N,
      clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k :=
    Finset.sum_pos (fun k _ => mul_pos (clockDisorder_pos N β ξ hN k hL hr) (hweight k))
      ⟨(fun _ => ⟨0, hN⟩), Finset.mem_univ _⟩
  have hlo : 0 ≤ clockDisorderExpectation N β ξ hN hL hr := by
    unfold clockDisorderExpectation
    exact (div_pos hnum hden).le
  have hnum_le :
      (∑ k : RotatorSpinSite (2 * L) → Fin N,
        clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k) ≤
        ∑ k : RotatorSpinSite (2 * L) → Fin N,
          (Real.exp (2 * |β|) ^ r) * clockBoxWeight N (2 * L) β k :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
      (clockDisorder_le N β ξ hN k hL hr) (hweight k).le
  have hnum_le' :
      (∑ k : RotatorSpinSite (2 * L) → Fin N,
        clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k) ≤
        (Real.exp (2 * |β|) ^ r) * clockDisorderPartition N L β hN := by
    change _ ≤ (Real.exp (2 * |β|) ^ r) *
      ∑ k : RotatorSpinSite (2 * L) → Fin N, clockBoxWeight N (2 * L) β k
    convert hnum_le using 1
    rw [Finset.mul_sum]
  have hhi : clockDisorderExpectation N β ξ hN hL hr ≤ Real.exp (2 * |β|) ^ r := by
    unfold clockDisorderExpectation
    exact (div_le_iff₀ hden).2 hnum_le'
  exact ⟨hlo, hhi⟩

/-- The finite-volume disorder expectations always have a subsequential thermodynamic limit point
along the centered-square exhaustion. -/
theorem exists_clockDisorderLimitPoint (N r : ℕ) (hr : 0 < r) (β ξ : ℝ) (hN : 0 < N) :
    ∃ c, IsClockDisorderLimitPoint N r β ξ c hN hr := by
  let B := Real.exp (2 * |β|) ^ r
  have hcompact : IsCompact (Set.Icc (0 : ℝ) B) := isCompact_Icc
  have hseq : ∀ t, clockDisorderExpectationExhaustion N r β ξ hN hr t ∈ Set.Icc 0 B := by
    intro t
    exact clockDisorderExpectation_mem_Icc N β ξ hN (by omega) (by omega)
  obtain ⟨c, -, s, hs, hlim⟩ := hcompact.tendsto_subseq
    (x := fun t => clockDisorderExpectationExhaustion N r β ξ hN hr t) hseq
  refine ⟨c, ⟨s, hs, ?_⟩⟩
  change Tendsto ((fun t => clockDisorderExpectationExhaustion N r β ξ hN hr t) ∘ s)
    atTop (𝓝 c)
  exact hlim

end FroehlichSpencer.BKT.Clock.Disorder

end
