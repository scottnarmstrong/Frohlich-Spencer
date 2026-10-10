/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Surface.ClockDisorderLimit
public import FroehlichSpencer.BKT.Bridge.ClockLaw
public import FroehlichSpencer.BKT.Clock.Disorder.GridRatio
public import FroehlichSpencer.BKT.Clock.Disorder.SeamObstruction
public import FroehlichSpencer.BKT.Clock.Compact.FejerLimit
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBoxSum
public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
import Mathlib.Tactic

/-!
# Bridge: the clock disorder expectations of FS81 (7.5)

* `integral_disorder_eq`: on the centred box `[-L, L]²` the expectation of the disorder
  operator (1.32) under source's `clockLaw` is the internal `clockDisorderExpectation` (the comb
  law on `{0, …, 2L}²`, seam at `(L + i + 1, L)`–`(L + i + 1, L + 1)`), by translation by `(L, L)`.
* `isClockDisorderLimitPoint_of_limit`: every value `D r` of a joint thermodynamic limit is an
  internal limit point; `exists_clockDisorderLimit`: a joint limit exists (compactness).
* `offGrid_xi`: `ξ = 1/(2N)` lies in `(0, 1)` and off the grid `ℤ/N`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ClockDisorder

open Filter Topology MeasureTheory
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Rotator
  FroehlichSpencer.BKT.Rotator.Ginibre FroehlichSpencer.BKT.Clock.Disorder
  FroehlichSpencer.BKT.Bridge.ClockLaw
open FroehlichSpencer.BKT.Clock.Compact
  (clockAngles clockBoxWeight integral_siteProduct_clockMeasure)

/-- The centred box `[-L, L]²`. -/
abbrev cbox (L : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L

/-- The translation `z ↦ z - (L, L)` from `{0, …, 2L}²` onto `[-L, L]²`. -/
def shiftEquiv (L : ℕ) : squareBoxZ (2 * L) ≃ cbox L where
  toFun z := ⟨z.1 - ((L : ℤ), (L : ℤ)), by
    have h := z.2
    simp only [squareBoxZ, Finset.mem_product, Finset.mem_Icc] at h
    simp only [Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
    push_cast at h
    omega⟩
  invFun z := ⟨z.1 + ((L : ℤ), (L : ℤ)), by
    have h := z.2
    simp only [Finset.mem_product, Finset.mem_Icc] at h
    simp only [squareBoxZ, Finset.mem_product, Finset.mem_Icc, Prod.fst_add, Prod.snd_add]
    push_cast
    omega⟩
  left_inv z := Subtype.ext (by simp)
  right_inv z := Subtype.ext (by simp)

/-- The free spin box `{0, …, 2L}²` is the centred box. -/
def boxEquiv (L : ℕ) : RotatorSpinSite (2 * L) ≃ cbox L :=
  (squareBoxEquiv (2 * L)).trans (shiftEquiv L)

theorem boxEquiv_coe {L : ℕ} (p : RotatorSpinSite (2 * L)) :
    ((boxEquiv L p : cbox L) : ℤ × ℤ) = siteToZ p - ((L : ℤ), (L : ℤ)) := rfl

/--
The clock expectation is a ratio of finite sums over the clock configurations.
-/
theorem integral_clockLaw_eq_sum (n : ℕ) (hn : 0 < n) (β : ℝ) (Λ : Finset (ℤ × ℤ))
    (F : (Λ → ℝ) → ℝ) :
    ∫ θ, F θ ∂FroehlichSpencer.BKT.clockLaw n hn β Λ =
      (∑ k : Λ → Fin n, F (clockAngles n k) *
          pairWeight (bondFrequency Λ) (clockBondWeight β Λ) (clockAngles n k)) /
        ∑ k : Λ → Fin n, pairWeight (bondFrequency Λ) (clockBondWeight β Λ) (clockAngles n k) := by
  rw [clockLaw_eq_pairGibbs, integral_pairGibbs (clockMeasure_univ_ne_zero hn)
    (isBondWeight_clockBondWeight β Λ), pairPartition, integral_siteProduct_clockMeasure,
    integral_siteProduct_clockMeasure]
  rfl

theorem pairWeight_eq_exp (β : ℝ) (Λ : Finset (ℤ × ℤ)) (θ : Λ → ℝ) :
    pairWeight (bondFrequency Λ) (clockBondWeight β Λ) θ =
      Real.exp (∑ b : Λ × Λ,
        if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then β * Real.cos (θ b.1 - θ b.2) else 0) := by
  rw [Real.exp_sum, pairWeight]
  refine Fintype.prod_congr _ _ fun b => ?_
  rw [phase_bondFrequency, clockBondWeight]
  split_ifs <;> simp [expCosWeight]

/-- The bond sum of the centred box is the internal bond sum of the free spin box. -/
theorem bondSum_cbox (β : ℝ) (L : ℕ) (θ : cbox L → ℝ) :
    (∑ b : cbox L × cbox L,
        if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then β * Real.cos (θ b.1 - θ b.2) else 0) =
      ∑ e : RotatorInternalBond (2 * L), β * Real.cos
        (θ (boxEquiv L ((rotatorFreeGraph (2 * L)).src e)) -
          θ (boxEquiv L ((rotatorFreeGraph (2 * L)).tgt e))) := by
  classical
  set w : ℤ × ℤ := ((L : ℤ), (L : ℤ))
  have hsum := sum_rotatorInternalBond_eq_sum_latticeStep (2 * L)
    (fun y z => β * Real.cos (latticeAngle θ (y - w) - latticeAngle θ (z - w)))
  have hang : ∀ p : RotatorSpinSite (2 * L), latticeAngle θ (siteToZ p - w) = θ (boxEquiv L p) := by
    intro p
    have h : siteToZ p - w ∈ cbox L := (boxEquiv L p).2
    unfold latticeAngle
    rw [dite_eq_left h]
    rfl
  simp only [hang] at hsum
  rw [hsum]
  symm
  refine Fintype.sum_equiv ((shiftEquiv L).prodCongr (shiftEquiv L)) _ _ fun c => ?_
  have hc : ∀ z : squareBoxZ (2 * L), latticeAngle θ ((z : ℤ × ℤ) - w) = θ (shiftEquiv L z) := by
    intro z
    have h : (z : ℤ × ℤ) - w ∈ cbox L := (shiftEquiv L z).2
    unfold latticeAngle
    rw [dite_eq_left h]
    rfl
  have hstep : LatticeStep ((c.1 : ℤ × ℤ) - w) ((c.2 : ℤ × ℤ) - w) ↔
      LatticeStep (c.1 : ℤ × ℤ) (c.2 : ℤ × ℤ) := by
    unfold LatticeStep
    constructor <;> rintro (h | h) <;> [left; right; left; right] <;>
      first | (rw [sub_eq_iff_eq_add] at h; rw [h]; abel) | (rw [h]; abel)
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hc]
  exact if_congr hstep.symm rfl rfl

theorem pairWeight_cbox (n : ℕ) (β : ℝ) (L : ℕ) (k : cbox L → Fin n) :
    pairWeight (bondFrequency (cbox L)) (clockBondWeight β (cbox L)) (clockAngles n k) =
      clockBoxWeight n (2 * L) β (k ∘ boxEquiv L) := by
  rw [pairWeight_eq_exp, bondSum_cbox]
  rfl

theorem disorder_cbox (n : ℕ) (hn : 0 < n) (β ξ : ℝ) {r L : ℕ} (hL : 0 < L) (hr : r ≤ L)
    (hΛ : ∀ m : Fin r,
      (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ cbox L ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ cbox L)
    (k : cbox L → Fin n) :
    clockDisorderOperator β ξ (cbox L) r hΛ (clockAngles n k) =
      clockDisorder n β ξ hn (k ∘ boxEquiv L) hL hr := by
  unfold clockDisorderOperator clockDisorder clockDisorderFactor
  refine Finset.prod_congr rfl fun m _ => ?_
  have hu : boxEquiv L (seamUpperSite hL hr m) = ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ := by
    refine Subtype.ext ?_
    rw [boxEquiv_coe]
    simp only [seamUpperSite, siteToZ, Prod.mk_sub_mk, Prod.mk.injEq]
    push_cast
    constructor <;> ring
  have hl : boxEquiv L (seamLowerSite hL hr m) = ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩ := by
    refine Subtype.ext ?_
    rw [boxEquiv_coe]
    simp only [seamLowerSite, siteToZ, Prod.mk_sub_mk, Prod.mk.injEq]
    push_cast
    constructor <;> ring
  simp only [Function.comp_apply, clockAngles, hu, hl]

/--
**The disorder expectation is the internal one** on every centred box containing the
seam.
-/
theorem integral_disorder_eq (n : ℕ) (hn : 0 < n) (β ξ : ℝ) {r L : ℕ} (hL : 0 < L) (hr : r ≤ L)
    (hΛ : ∀ m : Fin r,
      (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ cbox L ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ cbox L) :
    ∫ θ, clockDisorderOperator β ξ (cbox L) r hΛ θ ∂FroehlichSpencer.BKT.clockLaw n hn β (cbox L) =
      clockDisorderExpectation n β ξ hn hL hr := by
  rw [integral_clockLaw_eq_sum]
  unfold clockDisorderExpectation clockDisorderPartition
  congr 1
  · exact Fintype.sum_equiv (Equiv.arrowCongr (boxEquiv L).symm (Equiv.refl (Fin n))) _ _
      fun k => by rw [disorder_cbox n hn β ξ hL hr hΛ, pairWeight_cbox]; rfl
  · exact Fintype.sum_equiv (Equiv.arrowCongr (boxEquiv L).symm (Equiv.refl (Fin n))) _ _
      fun k => by rw [pairWeight_cbox]; rfl

theorem expectation_congr (n : ℕ) (hn : 0 < n) (β ξ : ℝ) {r L L' : ℕ} (h : L = L') (hL : 0 < L)
    (hr : r ≤ L) (hL' : 0 < L') (hr' : r ≤ L') :
    clockDisorderExpectation (r := r) (L := L) n β ξ hn hL hr =
      clockDisorderExpectation (r := r) (L := L') n β ξ hn hL' hr' := by
  subst h
  rfl

/-- **Every value of a joint thermodynamic limit is an internal limit point** (along a strictly
increasing subsequence of radii). -/
theorem isClockDisorderLimitPoint_of_limit {n : ℕ} {hn : 0 < n} {β ξ : ℝ} {D : ℕ → ℝ}
    (hD : IsClockDisorderLimit n hn β ξ D) (r : ℕ) (hr : 0 < r) :
    IsClockDisorderLimitPoint n r β ξ (D r) hn hr := by
  obtain ⟨Ls, hLs, hconv⟩ := hD
  obtain ⟨φ, hφ, hφLs⟩ := Filter.strictMono_subseq_of_tendsto_atTop hLs
  have hge : ∀ t, t ≤ Ls (φ t) := fun t => hφLs.id_le t
  have hmem : ∀ t, r ≤ Ls (φ (t + r)) := fun t => (Nat.le_add_left r t).trans (hge (t + r))
  refine ⟨fun t => Ls (φ (t + r)) - r, fun a b hab => ?_, ?_⟩
  · have h1 : Ls (φ (a + r)) < Ls (φ (b + r)) := hφLs (show a + r < b + r by omega)
    have := hmem a
    simp only
    omega
  · have hsub : Tendsto (fun t => (⟨φ (t + r), hmem t⟩ : {k : ℕ // r ≤ Ls k})) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun b => ⟨b.1, fun t ht => ?_⟩
      change b.1 ≤ φ (t + r)
      exact ht.trans ((Nat.le_add_right t r).trans (hφ.id_le _))
    refine ((hconv r).comp hsub).congr fun t => ?_
    simp only [Function.comp_apply, clockDisorderExpectationExhaustion]
    rw [integral_disorder_eq n hn β ξ (lt_of_lt_of_le hr (hmem t)) (hmem t)]
    exact expectation_congr n hn β ξ (by have := hmem t; omega) _ _ _ _

/-- **A joint thermodynamic limit exists** (compactness: `0 ≤ ⟨D⟩ ≤ e^{2|β| r}`). -/
theorem exists_clockDisorderLimit (n : ℕ) (hn : 0 < n) (β ξ : ℝ) :
    ∃ D : ℕ → ℝ, IsClockDisorderLimit n hn β ξ D := by
  let u : ℕ → ℕ → ℝ := fun m r => if h : r ≤ m + 1 then
    clockDisorderExpectation (r := r) (L := m + 1) n β ξ hn (Nat.succ_pos m) h else 0
  have hB : ∀ m r, |u m r| ≤ Real.exp (2 * |β|) ^ r := by
    intro m r
    simp only [u]
    split_ifs with h
    · have := clockDisorderExpectation_mem_Icc n β ξ hn (Nat.succ_pos m) h
      rw [abs_of_nonneg this.1]
      exact this.2
    · simp only [abs_zero]
      positivity
  obtain ⟨φ, hφ, l, hl⟩ := Coulomb.exists_subseq_tendsto_pointwise u _ hB
  refine ⟨l, fun k => φ k + 1, tendsto_atTop_atTop.2 fun b => ⟨b, fun k hk =>
    (hk.trans (hφ.id_le k)).trans (Nat.le_succ _)⟩, fun r => ?_⟩
  have hne : Nonempty {k : ℕ // r ≤ φ k + 1} := ⟨⟨r, by have : r ≤ φ r := hφ.id_le r; omega⟩⟩
  have hsub : Tendsto (Subtype.val : {k : ℕ // r ≤ φ k + 1} → ℕ) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨⟨max b r, ?_⟩, fun x hx => (le_max_left b r).trans hx⟩
    have : max b r ≤ φ (max b r) := hφ.id_le (max b r)
    have := le_max_right b r
    omega
  refine ((hl r).comp hsub).congr fun k => ?_
  simp only [Function.comp_apply, u, dite_eq_left k.2]
  exact (integral_disorder_eq n hn β ξ (Nat.succ_pos _) k.2 _).symm

theorem offGrid_xi {N : ℕ} (hN : 0 < N) :
    0 < (1 : ℝ) / (2 * N) ∧ (1 : ℝ) / (2 * N) < 1 ∧ ∀ j : ℤ, (N : ℝ) * (1 / (2 * N)) ≠ j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by positivity, ?_, fun j hj => ?_⟩
  · rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  · have h2 : (N : ℝ) * (1 / (2 * N)) = 1 / 2 := by
      field_simp
    rw [h2] at hj
    have h3 : (2 : ℝ) * j = 1 := by linarith
    have h4 : (2 : ℤ) * j = 1 := by exact_mod_cast h3
    omega

end FroehlichSpencer.BKT.Bridge.ClockDisorder

end
