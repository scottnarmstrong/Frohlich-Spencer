/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceCurlIncidence
public import FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
public import FroehlichSpencer.FS82.Moment.SourceConstructor
public import FroehlichSpencer.FS82.Currents.ShortComponentPhase
public import FroehlichSpencer.FS82.Currents.SourceLatticeChain

/-!
# the integer incidence of the dual complex

The §3 gauge field is put on the links of the dual complex `Λ*` of a box, in the dual orientation
of its links.

The plaquette incidence is the curl coefficient of the dual differential, which
takes the values `0, ±1`.

* `curlInt p e`: the integer curl coefficient; it vanishes unless the link is incident to the
  plaquette, and `Σ_e curlInt p e · (Tτ)_e = (d₁ τ)_p` for the lattice complex `d₁ = D₁ T`.
* `gaugeDir v e`: the integer gauge direction of the vertex `v`; `Σ_e ρ_e gaugeDir v e` is the
  divergence of `ρ` at `v`, and `Σ_e curlInt p e · gaugeDir v e = 0` (`D₁ D₀ = 0`).
-/

open scoped BigOperators
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

variable {B : Box 4}

/-- The integer curl coefficient of the dual complex. -/
def curlInt (p : SourceDualTwoCells B) (e : Link B) : ℤ := by
  classical
  exact if sourceCurlCoefficient p e = 1 then 1
    else if sourceCurlCoefficient p e = -1 then -1 else 0

theorem curlInt_cast (p : SourceDualTwoCells B) (e : Link B) :
    ((curlInt p e : ℤ) : ℝ) = sourceCurlCoefficient p e := by
  classical
  unfold curlInt
  rcases sourceCurlCoefficient_trichotomy p e with h | h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · rw [h]
    norm_num

theorem abs_curlInt_le_one (p : SourceDualTwoCells B) (e : Link B) : |curlInt p e| ≤ 1 := by
  classical
  unfold curlInt
  split_ifs <;> simp

theorem curlInt_eq_zero_of_not_incident (p : SourceDualTwoCells B) (e : Link B)
    (h : ¬ linkIncidentPlaquette e p) : curlInt p e = 0 := by
  have h0 := sourceCurlCoefficient_eq_zero_of_not_incident p e h
  have hc := curlInt_cast p e
  rw [h0] at hc
  exact_mod_cast hc

theorem linkIncidentPlaquette_of_curlInt_ne_zero {p : SourceDualTwoCells B} {e : Link B}
    (h : curlInt p e ≠ 0) : linkIncidentPlaquette e p := by
  by_contra hn
  exact h (curlInt_eq_zero_of_not_incident p e hn)

/-- The flux of a C2-twisted link field is the lattice differential. -/
theorem sum_curlInt_twistedLinkField (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (p : SourceDualTwoCells B) :
    ∑ e : Link B, ((curlInt p e : ℤ) : ℝ) * twistedLinkField τ e =
      (sourceLatticeComplex (B := B)).d₁ τ p := by
  change _ = sourceDualD₁ (sourceDualTLinear τ) p
  rw [sourceDualD₁_eq_sourceCurl_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [curlInt_cast, sourceDualTLinear_apply]
  rfl

/-- The integer gauge direction of a dual vertex. -/
def gaugeDir (v : SourceDualZeroCells B) (e : Link B) : ℤ :=
  boundary (sourceCurrentLatticeChain (Finsupp.single e (1 : ℤ))) (lambdaCellToBumpedBox v.1)

theorem gaugeDir_cast (v : SourceDualZeroCells B) (e : Link B) :
    ((gaugeDir v e : ℤ) : ℝ) = currentDivergence (Finsupp.single e (1 : ℤ)) v :=
  sourceCurrentLatticeChainDivergence_matches _ v

/-- The pairing of a current with the gauge direction is its divergence. -/
theorem sum_mul_gaugeDir (ρ : IntegerCurrent B) (v : SourceDualZeroCells B) :
    ((∑ e : Link B, ρ e * gaugeDir v e : ℤ) : ℝ) = currentDivergence ρ v := by
  rw [currentDivergence_eq_sum_single]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [currentDivergence_single_scale, gaugeDir_cast]

theorem gaugeDir_eq_D₀ (v : SourceDualZeroCells B) (e : Link B) :
    ((gaugeDir v e : ℤ) : ℝ) = sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ)) e := by
  rw [gaugeDir_cast, currentDivergence_eq_D0_inner, PiLp.inner_apply]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hf
    simp [hf.symm]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- Gauge invariance: every plaquette row annihilates every gauge direction (`D₁ D₀ = 0`). -/
theorem sum_curlInt_gaugeDir (p : SourceDualTwoCells B) (v : SourceDualZeroCells B) :
    ∑ e : Link B, curlInt p e * gaugeDir v e = 0 := by
  have hreal : ((∑ e : Link B, curlInt p e * gaugeDir v e : ℤ) : ℝ) = 0 := by
    push_cast
    have h := sourceDualD₁_eq_sourceCurl_sum
      (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ))) p
    have hzero : sourceDualD₁ (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ))) = 0 := by
      have := congrArg (fun L => L (EuclideanSpace.single v (1 : ℝ)))
        (sourceDualD₁_comp_D₀_zero (B := B))
      simpa using this
    rw [hzero] at h
    rw [show (∑ e : Link B, ((curlInt p e : ℤ) : ℝ) * ((gaugeDir v e : ℤ) : ℝ)) =
      ∑ e : SourceDualOneCells B, sourceCurlCoefficient p e *
        sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ)) e from
      Finset.sum_congr rfl fun e _ => by rw [curlInt_cast, gaugeDir_eq_D₀]]
    exact h.symm
  exact_mod_cast hreal

end

end FroehlichSpencer.FS82.ZN

end
