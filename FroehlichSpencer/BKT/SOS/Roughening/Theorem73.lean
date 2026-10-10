/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Roughening.Moment
public import FroehlichSpencer.BKT.SOS.Roughening.Resistance
public import FroehlichSpencer.BKT.SOS.Roughening.Variance
public import FroehlichSpencer.BKT.SOS.Roughening.Numbers
public import FroehlichSpencer.BKT.SOS.Layer.Unconditional

/-!
# FS81 Theorem 7.3: logarithmic roughening of the SOS model at high temperature

Fröhlich–Spencer (1981), §7.2, Theorem 7.3 (J p. 590) and Remark 1: for `β` sufficiently small,

`⟨e^{ε[φ(0) − φ(x)]}⟩(β) ≥ e^{(ε²/β') ln(1 + |x|)}` (7.17),
`⟨[φ(0) − φ(x)]²⟩(β) ≥ (1/β') ln(1 + |x|)` (7.18),

with `β' = β'(β) → 0` as `β → 0`.

**The state.** FS81 build the SOS state from the zero-exterior measures `dμ_{I_β,Ω}` with the comb
(7.16), and note that the results extend to Dirichlet conditions.

Here the state is the pinned
(Dirichlet, zero-exterior) SOS model on the box `{0,…,L−1}²`: integer heights `n`, `n = 0` off the
box, weight `∏_{|i−j|=1, i ∈ box} e^{−β|n(i) − n(j)|}` (`sosMoment`, `sosVariance`).

The distance
`|x|` is the `ℓ^∞` distance of the two points, capped at the distance of the first point to the
outside; for points at least `|x|` deep it is `|x|` (`sos_theorem73_deep`).

* the comb is expanded by the Appendix D pinned charge layer (`pinnedLayerHypothesisD_holds`,
  unconditional);
* the tilt `e^{ε(φ(u) − φ(v))} = e^{⟨∇φ, ε∇g⟩}` (`g` the unit dipole potential) is carried
  through the renormalization as the endpoint phases `ε(a_ρ(u) − a_ρ(v))`
  (`Tilt.rootedD_identity_of_law_phased`), and through the branch bound with prefactor one
  (`Tilt.integral_shiftProduct_tilt_ge`);
* the shift `σ = s(g − g(root))`, `s = ε/(4πC₁)`, is FS81's (7.22); the gain is
  `(ε/2π)² R(u, v)/(4C₁)` with the effective resistance `R ≥ (1/32) log(1 + |x|)`
  (`log_le_dipoleResistance_squareZero`, Nash–Williams);
* the losses are the packed phase errors (`C₁ = κ_c + 4ε_p`) and the packed endpoint sum
  `16 ε_end (ε/2π)² R` (`Tilt.sum_abs_mul_tiltExponent_sq_le`); condition (★),
  `128 C₁ ε_end ≤ 1` for small `β`, is `exists_sosNumbers`;
* the comb pairings converge to the SOS sums by Poisson summation (`sosCombPairing_tendsto`);
* (7.18) follows from (7.17) with prefactor one by `le_tsum_sq_mul_of_exp_le`.

The result: `β'(β) = 1024 π² C₁(log(1/β))`, `C₁ = (C + 1) β^{2/3} + 4 C_p β^r → 0`, and (7.17)
holds for `|ε| ≤ β/2` (the tilted sums converge only for `|ε|` of order `β`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open Filter Topology
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site siteBoundaryDepth)
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.SOS.Tilt

variable {L : ℕ}

/-- The pinned SOS weight is even. -/
theorem sosHeightWeight_neg (L : ℕ) (β : ℝ) (n : Site L → ℤ) :
    sosHeightWeight L β (-n) = sosHeightWeight L β n := by
  unfold sosHeightWeight
  refine Finset.prod_congr rfl fun e _ => ?_
  have h : (fun x => (((-n) x : ℤ) : ℝ)) = -(fun x => (n x : ℝ)) := by
    funext x; simp
  rw [h, map_neg, Pi.neg_apply, abs_neg]

/-- The tilted SOS sums converge for `|c| ≤ β/2`. -/
theorem summable_sosTilted (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (u v : Site L)
    {c : ℝ} (hc : |c| ≤ β / 2) :
    Summable fun n : Site L → ℤ => Real.exp (c * ((n u : ℝ) - n v)) * sosHeightWeight L β n := by
  set g := dipolePotential (squareZero L) (squareZero_connected L hL) (some u) (some v) with hg
  set c' : SquareZeroBond L → ℝ := fun e => 2 * Real.pi * (c / (2 * Real.pi) *
    (squareZero L).grad g e) with hc'def
  have hc' : ∀ e, |c' e| ≤ β / 2 := fun e => by
    have hge := abs_grad_dipolePotential_le_one (squareZero L) (squareZero_connected L hL)
      (some u) (some v) e
    have heq : c' e = c * (squareZero L).grad g e := by rw [hc'def]; field_simp
    rw [heq, abs_mul]
    calc |c| * |(squareZero L).grad g e| ≤ |c| * 1 := mul_le_mul_of_nonneg_left hge (abs_nonneg _)
      _ ≤ β / 2 := by rw [mul_one]; exact hc
  obtain ⟨-, hs⟩ := sosCombPairing_tendsto hL hβ hβ1 hc'
  have h := Complex.summable_ofReal.mp ((summable_congr fun n =>
    sosDensityCoords_intCast hβ.le c' n).mp hs)
  refine h.congr fun n => ?_
  rw [hc'def, sum_dipole_mul_pinnedGrad hL u v c n]

/-- The pinned SOS partition function is positive. -/
theorem sosPartition_pos (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (u : Site L) :
    0 < sosPartition L β := by
  have h := summable_sosTilted hL hβ hβ1 u u (c := 0) (by rw [abs_zero]; positivity)
  have h' : Summable fun n : Site L → ℤ => sosHeightWeight L β n := h.congr fun n => by simp
  exact h'.tsum_pos (fun n => (sosHeightWeight_pos L β n).le) 0 (sosHeightWeight_pos L β 0)

/-- The algebra of the exponent: with `R ≥ ℓ/32` and `128 C ε_end ≤ 1`,
`ε² ℓ/(1024π² C) ≤ (ε/2π)² R (1/(4C) − 16 ε_end)`. -/
theorem theorem73_exponent_le {ε ℓ R C εe : ℝ} (hC : 0 < C) (hℓ : 1 / 32 * ℓ ≤ R)
    (hℓ0 : 0 ≤ ℓ) (hsmall : 128 * C * εe ≤ 1) :
    ε ^ 2 / (1024 * Real.pi ^ 2 * C) * ℓ ≤
      (ε / (2 * Real.pi)) ^ 2 * R * (1 / (4 * C) - 16 * εe) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hA : 1 / (8 * C) ≤ 1 / (4 * C) - 16 * εe := by
    have h1 : 16 * εe ≤ 1 / (8 * C) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : 1 / (4 * C) = 2 * (1 / (8 * C)) := by field_simp; ring
    linarith
  calc ε ^ 2 / (1024 * Real.pi ^ 2 * C) * ℓ
      = (ε / (2 * Real.pi)) ^ 2 * (1 / 32 * ℓ) * (1 / (8 * C)) := by
        field_simp; ring
    _ ≤ (ε / (2 * Real.pi)) ^ 2 * R * (1 / 4 / C - 16 * εe) := by
        rw [div_div]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hℓ (sq_nonneg _)) hA (by positivity)
          (mul_nonneg (sq_nonneg _) ((by positivity : (0 : ℝ) ≤ 1 / 32 * ℓ).trans hℓ))
    _ = (ε / (2 * Real.pi)) ^ 2 * R * (1 / (4 * C) - 16 * εe) := by rw [div_div]

/-- **FS81 Theorem 7.3**, (7.17) and (7.18), for the pinned SOS model on the box. There are
`β₀ > 0`, `β' → 0` (as `β → 0⁺`) and `L₀` such that for `0 < β ≤ β₀`, every box of side
`L ≥ L₀`, all points `u, v`, with `ℓ = log(1 + min(‖u − v‖_∞, depth(u)))`:

* `⟨e^{ε[φ(u) − φ(v)]}⟩ ≥ e^{(ε²/β') ℓ}` for `|ε| ≤ β/2`;
* `⟨[φ(u) − φ(v)]²⟩ ≥ ℓ/β'`. -/
theorem sos_theorem73 :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧ Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ L, L₀ ≤ L → ∀ u v : Site L,
        (∀ ε : ℝ, |ε| ≤ β / 2 →
          Real.exp (ε ^ 2 / β' β *
            Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ))) ≤
            sosMoment L β u v ε) ∧
        Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) / β' β ≤
          sosVariance L β u v := by
  obtain ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₁, hα, hK₀, hK₁, hD₁, hKv, hwit⟩ :=
    Layer.sosPinnedCarrierHypothesis_holds
  obtain ⟨T₀, C₁, hT₀, hC₁lim, hnum⟩ := exists_sosNumbers (D₂ := D₂) (a₁ := a₁) (a₂ := a₂) Kov
    hα hK₀ hK₁ hD₁ hKv
  refine ⟨Real.exp (-T₀), fun β => 1024 * Real.pi ^ 2 * C₁ (-Real.log β), max L₁ 2,
    Real.exp_pos _, ?_, fun β hβ hβ₀ => ?_⟩
  · have hlog : Tendsto (fun β : ℝ => -Real.log β) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    simpa using (hC₁lim.comp hlog).const_mul (1024 * Real.pi ^ 2)
  set T := -Real.log β with hTdef
  have hT : T₀ ≤ T := by
    have h := Real.log_le_log hβ hβ₀
    rw [Real.log_exp] at h
    linarith
  have hβT : Real.exp (-T) = β := by rw [hTdef, neg_neg, Real.exp_log hβ]
  have hβ1 : β ≤ 1 := hβ₀.trans (Real.exp_le_one_iff.mpr (by linarith))
  obtain ⟨hC₁pos, M, κc, amp, b, εp, εe, k₀, hlog', hcurv, hamp, hampW, hk₀, hexp, hquad₁, hquad₂,
    hM, hb8, hb₁, hb₂, hthr, hthrE, hC₁eq, hsmall⟩ := hnum T hT
  rw [hβT] at hlog' hcurv hampW hexp hquad₁
  have hπ : 0 < Real.pi := Real.pi_pos
  refine ⟨by positivity, fun L hL u v => ?_⟩
  have hL1 : 1 < L := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hL)
  have hwitL := hwit L (le_trans (le_max_left _ _) hL)
  set ℓ := Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) with hℓdef
  have hR := log_le_dipoleResistance_squareZero hL1 u v
  rw [Nat.cast_add, Nat.cast_one, add_comm] at hR
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (min (linfDist u v) (siteBoundaryDepth u)); linarith)
  have hC : 0 < κc + 4 * εp := by rw [hC₁eq]; exact hC₁pos
  -- (7.17)
  have hmom : ∀ ε : ℝ, |ε| ≤ β / 2 →
      Real.exp (ε ^ 2 / (1024 * Real.pi ^ 2 * C₁ T) * ℓ) ≤ sosMoment L β u v ε := by
    intro ε hε
    have h := sosMoment_ge_of_layer hK₀ hK₁ hD₁ hKv hβ hβ1 hlog' hcurv hamp hampW hk₀ hexp
      hquad₁ hquad₂ hM hb8 hb₁ hb₂ hthr hthrE hC hL1 hwitL u v ε hε
    refine le_trans (Real.exp_le_exp.mpr ?_) h
    rw [hC₁eq]
    exact theorem73_exponent_le hC₁pos hR hℓ0 (by rw [← hC₁eq] at hsmall ⊢; exact hsmall)
  refine ⟨hmom, ?_⟩
  -- (7.18)
  have hZpos := sosPartition_pos hL1 hβ hβ1 u
  have hβ'pos : 0 < 1024 * Real.pi ^ 2 * C₁ T := by positivity
  have key := le_tsum_sq_mul_of_exp_le (Equiv.neg (Site L → ℤ))
    (X := fun n => (n u : ℝ) - n v) (w := sosHeightWeight L β)
    (fun n => by simp only [Equiv.neg_apply, Pi.neg_apply, Int.cast_neg]; ring)
    (fun n => sosHeightWeight_neg L β n) (fun n => (sosHeightWeight_pos L β n).le)
    (δ := β / 2) (a := ℓ / (1024 * Real.pi ^ 2 * C₁ T)) (by positivity)
    (fun c hc => summable_sosTilted hL1 hβ hβ1 u v hc) (fun ε hε0 hεδ => by
      have h := hmom ε (by rw [abs_of_pos hε0]; exact hεδ)
      unfold sosMoment sosTiltedSum at h
      rw [le_div_iff₀ hZpos] at h
      have heq : ℓ / (1024 * Real.pi ^ 2 * C₁ T) * ε ^ 2 =
          ε ^ 2 / (1024 * Real.pi ^ 2 * C₁ T) * ℓ := by ring
      rw [heq]
      exact h)
  unfold sosVariance
  rw [le_div_iff₀ hZpos]
  exact key

/-- **FS81 Theorem 7.3 at deep points**: when `u` is at least `|x| = ‖u − v‖_∞` away from the
outside, the bounds hold with FS81's `ln(1 + |x|)`. -/
theorem sos_theorem73_deep :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧ Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ L, L₀ ≤ L → ∀ u v : Site L,
        linfDist u v ≤ siteBoundaryDepth u →
        (∀ ε : ℝ, |ε| ≤ β / 2 →
          Real.exp (ε ^ 2 / β' β * Real.log (1 + (linfDist u v : ℝ))) ≤ sosMoment L β u v ε) ∧
        Real.log (1 + (linfDist u v : ℝ)) / β' β ≤ sosVariance L β u v := by
  obtain ⟨β₀, β', L₀, hβ₀, hlim, h⟩ := sos_theorem73
  refine ⟨β₀, β', L₀, hβ₀, hlim, fun β hβ hββ₀ => ⟨(h β hβ hββ₀).1, fun L hL u v huv => ?_⟩⟩
  have h' := (h β hβ hββ₀).2 L hL u v
  rw [min_eq_left huv] at h'
  exact h'

end FroehlichSpencer.BKT.SOS.Roughening

end
