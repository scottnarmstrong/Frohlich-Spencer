/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.DualGinibre
public import FroehlichSpencer.BKT.Clock.VillainClock.TheoremCFiniteBox
import Mathlib.Tactic

/-!
FS81 Remark 4: the methods give (7.5) for the Villain-constrained `ℤ_N` clock as well.

1.

`freeSquareDisorderExpectation_grid_eq_dual`: the seam disorder expectation at `β` equals the
   two-point function of the dual Villain clock on the faces at `β* = N²/(4π²β)`, with the exterior
   face pinned.
2.

`villainClockModel_twoPoint_le_dual`: by Ginibre's inequality the pinned dual dominates the free
   face model, which is the Ginibre Villain-clock model on the face square.
3.

`finite_correlation_dominates` (Theorem 7.1(1) for the Villain clock): the clock model dominates
   the continuous Villain model.
4.

Domain monotonicity and translation: the face square contains a centred free box around the
   seam.
5.

`villain_finiteBox_lowerBound`: the finite-box form of FS81 Theorem C for the Villain model, at
   `β* ≥ β₀`.

The result is `⟨D^{k/N}⟩ ≥ exp(−p(β*) C₀ k² (1 + log(1 + r)))` on every free square of radius
`L ≥ 2r + L₀ + 3`.

The threshold `n₁(β)` makes `β* ≥ β₀`, and `β''' = 2π p(β*) C₀ N²`.

* **`freeSquareDisorderExpectation_grid_ge`**: the finite-volume bound;
* `IsFreeSquareDisorderThermoLimitPoint`: limit points along strictly increasing box sequences;
* **`villainClock_disorder_lowerBound_grid`**: FS81's (7.5) for the Villain clock, at every
  thermodynamic limit point, with `n₁(β) → ∞` and `β'''`, `const` shared over `k`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open Filter Topology
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Ginibre

/-! ### The finite-volume bound -/

/-- The seam end faces in `ℤ²`: the start face is `(L, L)` and the end face is `(L + r, L)`. -/
theorem siteToZ_seamStartFace {L' : ℕ} (hL : 0 < L' + 1) :
    siteToZ (L := 2 * L' + 1) (seamStartFace hL) = (((L' + 1 : ℕ) : ℤ), ((L' + 1 : ℕ) : ℤ)) :=
  rfl

theorem siteToZ_seamEndFace {r L' : ℕ} (hrL : r < L' + 1) :
    siteToZ (L := 2 * L' + 1) (seamEndFace hrL) = (((L' + 1 + r : ℕ) : ℤ), ((L' + 1 : ℕ) : ℤ)) :=
  rfl

/-- **The Villain-clock (7.5), finite volume.** On the grid `ξ = k/N`, once the dual temperature
`β* = N²/(4π²β)` exceeds `β₀`, every free square of radius `L ≥ 2r + L₀ + 3` satisfies
`exp(−p(β*) C₀ k² (1 + log(1 + r))) ≤ ⟨D^{k/N}⟩`. -/
theorem freeSquareDisorderExpectation_grid_ge :
    ∃ (β₀ C₀ : ℝ) (p : ℝ → ℝ) (L₀ : ℕ), 0 < C₀ ∧ 1 ≤ β₀ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N),
        β₀ ≤ gaussianAliasDualTemperature β N →
          0 ≤ p (gaussianAliasDualTemperature β N) ∧
          ∀ (k : ℤ) (r L : ℕ) (hL : 0 < L) (hrL : r < L), 2 * r + L₀ + 3 ≤ L →
            Real.exp (-((p (gaussianAliasDualTemperature β N) * C₀) *
                ((k : ℝ) ^ 2 * (1 + Real.log (1 + (r : ℝ)))))) ≤
              freeSquareDisorderExpectation N β ((k : ℝ) / N) hβ hN hL hrL.le := by
  obtain ⟨β₀, C₀, p, L₀, hC₀, hβ₀, hC⟩ := villain_finiteBox_lowerBound
  refine ⟨β₀, C₀, p, L₀, hC₀, hβ₀, fun β hβ N hN hβd => ?_⟩
  set βd := gaussianAliasDualTemperature β N with hβd_def
  have hβdpos : 0 < βd := lt_of_lt_of_le (by norm_num) (le_trans hβ₀ hβd)
  obtain ⟨hp, hbound⟩ := hC βd hβdpos hβd
  refine ⟨hp, fun k r L hL hrL hLbig => ?_⟩
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [freeSquareDisorderExpectation_grid_eq_dual β hβ hN hL hrL k]
  have hgin := villainClockModel_twoPoint_le_dual (K := 2 * L' + 1) hN hβdpos k
    (seamStartFace hL) (seamEndFace hrL)
  have hdom := finite_correlation_dominates hN hβdpos k (squareBoxZ (2 * L' + 1))
    (siteToZ (L := 2 * L' + 1) (seamStartFace hL)) (siteToZ (L := 2 * L' + 1) (seamEndFace hrL))
  -- the centred box around the seam start
  set M : ℕ := 2 * r + L₀ + 2 with hM
  set c : ℤ × ℤ := ((L' + 1 : ℕ), (L' + 1 : ℕ)) with hc
  have hsub : translateDomain (freeBox M) c ⊆ squareBoxZ (2 * L' + 1) := by
    intro z hz
    rw [mem_translateDomain, mem_freeBox] at hz
    simp only [squareBoxZ, Finset.mem_product, Finset.mem_Icc, hc] at hz ⊢
    push_cast at hz ⊢
    simp only [Prod.fst_sub, Prod.snd_sub] at hz
    omega
  have hu : (0, 0) + c ∈ translateDomain (freeBox M) c := by
    rw [mem_translateDomain, add_sub_cancel_right]
    exact mem_freeBox.mpr ⟨by simp, by simp, by simp, by simp⟩
  have hv : ((r : ℤ), 0) + c ∈ translateDomain (freeBox M) c := by
    rw [mem_translateDomain, add_sub_cancel_right, mem_freeBox]
    simp only [hM]
    push_cast
    omega
  have hmono := (villainModel βd hβdpos).twoPoint_mono_domain k hsub hu hv
  rw [(villainModel βd hβdpos).twoPoint_translate] at hmono
  have hthm := hbound k (0, 0) ((r : ℤ), 0) M (by
    simp only [l1Norm, boxRadius, hM]
    simp
    omega)
  have hl1 : l1Norm ((0, 0) - ((r : ℤ), 0)) = r := by simp [l1Norm]
  rw [hl1] at hthm
  have hstart : (0, 0) + c = siteToZ (L := 2 * L' + 1) (seamStartFace hL) := by
    rw [siteToZ_seamStartFace, hc]
    simp
  have hend : ((r : ℤ), 0) + c = siteToZ (L := 2 * L' + 1) (seamEndFace hrL) := by
    rw [siteToZ_seamEndFace, hc]
    ext <;> simp
    ring
  rw [hstart, hend] at hmono
  exact hthm.trans (hmono.trans (hdom.trans hgin))

/-! ### Thermodynamic limit points -/

/-- A limit of the centred free-square Villain-clock disorder expectations along a strictly
increasing sequence of boxes. -/
def IsFreeSquareDisorderThermoLimitPoint (N r : ℕ) (β ξ c : ℝ) (hβ : 0 < β) (hN : 0 < N)
    (hr : 0 < r) : Prop :=
  ∃ s : ℕ → ℕ, StrictMono s ∧
    Tendsto (fun t => freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr (s t)) atTop (𝓝 c)

theorem IsFreeSquareDisorderThermoLimitPoint.isFreeSquareDisorderIndexedLimit {N r : ℕ}
    {β ξ c : ℝ} {hβ : 0 < β} {hN : 0 < N} {hr : 0 < r}
    (h : IsFreeSquareDisorderThermoLimitPoint N r β ξ c hβ hN hr) :
    IsFreeSquareDisorderIndexedLimit N r β ξ c hβ hN hr := by
  obtain ⟨s, -, hs⟩ := h
  exact ⟨s, hs⟩

/-! ### FS81's (7.5) for the Villain clock -/

/-- The clock-order threshold `n₁(β)`: it makes the dual temperature at least `β₀`. -/
def villainGridThreshold (β₀ β : ℝ) : ℕ :=
  ⌈2 * Real.pi * Real.sqrt (|β| * β₀)⌉₊ + ⌈β⌉₊ + 1

theorem tendsto_villainGridThreshold (β₀ : ℝ) : Tendsto (villainGridThreshold β₀) atTop atTop := by
  refine (tendsto_natCast_atTop_iff (R := ℝ)).mp ?_
  refine tendsto_atTop_mono (fun β => ?_) tendsto_id
  unfold villainGridThreshold
  push_cast
  have h1 := Nat.le_ceil β
  have h2 : (0 : ℝ) ≤ ⌈2 * Real.pi * Real.sqrt (|β| * β₀)⌉₊ := Nat.cast_nonneg _
  simp only [id]
  linarith

theorem le_gaussianAliasDualTemperature_of_threshold {β₀ β : ℝ} (hβ₀ : 0 ≤ β₀) (hβ : 0 < β)
    {N : ℕ} (hN : villainGridThreshold β₀ β ≤ N) :
    β₀ ≤ gaussianAliasDualTemperature β N := by
  unfold villainGridThreshold at hN
  unfold gaussianAliasDualTemperature
  have hceil := Nat.le_ceil (2 * Real.pi * Real.sqrt (|β| * β₀))
  have hNr : 2 * Real.pi * Real.sqrt (|β| * β₀) ≤ N := by
    have : (⌈2 * Real.pi * Real.sqrt (|β| * β₀)⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega :
      ⌈2 * Real.pi * Real.sqrt (|β| * β₀)⌉₊ ≤ N)
    linarith
  have hsq : (2 * Real.pi * Real.sqrt (|β| * β₀)) ^ 2 ≤ (N : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNr 2
  have hexp : (2 * Real.pi * Real.sqrt (|β| * β₀)) ^ 2 = 4 * Real.pi ^ 2 * (β * β₀) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), abs_of_pos hβ]
    ring
  rw [hexp] at hsq
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/--
There is a threshold `n₁(β) → ∞` such that for every `β > 0` and every clock order `N ≥ n₁(β)`
there are `β''' ≥ 0` and `const > 0`, both shared over `k = 1, …, N − 1`, with: every
thermodynamic limit point `c` of the seam disorder expectation at `ξ = k/N` and seam length
`r ≥ 1` satisfies `const · (1 + r)^{−ξ² β'''/(2π)} ≤ c`.
-/
theorem villainClock_disorder_lowerBound_grid :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N), n₁ β ≤ N →
        ∃ β''' : ℝ, 0 ≤ β''' ∧ ∃ C : ℝ, 0 < C ∧
          ∀ k : ℕ, 1 ≤ k → k < N →
            ∀ (r : ℕ) (hr : 0 < r) (c : ℝ),
              IsFreeSquareDisorderThermoLimitPoint N r β ((k : ℝ) / N) c hβ hN hr →
                C * (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * β''' / (2 * Real.pi))) ≤ c := by
  obtain ⟨β₀, C₀, p, L₀, hC₀, hβ₀, hfin⟩ := freeSquareDisorderExpectation_grid_ge
  refine ⟨villainGridThreshold β₀, tendsto_villainGridThreshold β₀, ?_⟩
  intro β hβ N hN hNth
  have hβd := le_gaussianAliasDualTemperature_of_threshold (by linarith) hβ hNth
  obtain ⟨hp, hbound⟩ := hfin β hβ N hN hβd
  set q : ℝ := p (gaussianAliasDualTemperature β N) * C₀ with hq
  have hq0 : 0 ≤ q := mul_nonneg hp hC₀.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨2 * Real.pi * q * (N : ℝ) ^ 2, by positivity, Real.exp (-(q * (N : ℝ) ^ 2)),
    Real.exp_pos _, ?_⟩
  intro k _ hkN r hr c hc
  -- the power-law form of the finite bound
  have hpow : ∀ (L : ℕ) (hL : 0 < L) (hrL : r < L), 2 * r + L₀ + 3 ≤ L →
      Real.exp (-(q * (N : ℝ) ^ 2)) *
          (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * (2 * Real.pi * q * (N : ℝ) ^ 2) /
            (2 * Real.pi))) ≤
        freeSquareDisorderExpectation N β ((k : ℝ) / N) hβ hN hL hrL.le := by
    intro L hL hrL hLbig
    have h := hbound (k : ℤ) r L hL hrL hLbig
    push_cast at h
    refine le_trans ?_ h
    have hbase : 0 < 1 + (r : ℝ) := by positivity
    have hk2 : (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      have : (k : ℝ) ≤ N := by exact_mod_cast hkN.le
      exact pow_le_pow_left₀ (by positivity) this 2
    have hexpo : ((k : ℝ) / N) ^ 2 * (2 * Real.pi * q * (N : ℝ) ^ 2) / (2 * Real.pi) =
        q * (k : ℝ) ^ 2 := by
      field_simp
    rw [hexpo, Real.rpow_def_of_pos hbase, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hk2 hq0
    nlinarith
  rcases hc with ⟨s, hs, htend⟩
  apply ge_of_tendsto htend
  rw [eventually_atTop]
  refine ⟨r + L₀ + 3, fun t ht => ?_⟩
  have hst : t ≤ s t := hs.id_le t
  exact hpow (r + s t) (by omega) (by omega) (by omega)

end FroehlichSpencer.BKT.Clock.VillainClock

end
