/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.HarmonicField
public import FroehlichSpencer.BKT.Rotator.FreeBoxBijection
import Mathlib.Tactic

/-!
# Vortex-pair decomposition for the clock disorder seam

The source seam, viewed on the dual square, is an integer current with a unit source and sink.
The rotator harmonic-field construction replaces it by a logarithmic-energy current. The
current/face-height bijection turns the divergence-free difference into an exact gradient.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Villain

private theorem currentDivergence_sub_local {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (q j : E → ℤ) (v : V) :
    currentDivergence G (q - j) v = currentDivergence G q v - currentDivergence G j v := by
  unfold currentDivergence
  have hsrc : (∑ e, if G.src e = v then (q e - j e) else 0) =
      (∑ e, if G.src e = v then q e else 0) -
        (∑ e, if G.src e = v then j e else 0) := by
    calc
      _ = ∑ e, ((if G.src e = v then q e else 0) -
          (if G.src e = v then j e else 0)) := by
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> rfl
      _ = _ := by
        exact (Finset.sum_sub_distrib (s := Finset.univ)
          (fun e => if G.src e = v then q e else 0)
          (fun e => if G.src e = v then j e else 0))
  have htgt : (∑ e, if G.tgt e = v then (q e - j e) else 0) =
      (∑ e, if G.tgt e = v then q e else 0) -
        (∑ e, if G.tgt e = v then j e else 0) := by
    calc
      _ = ∑ e, ((if G.tgt e = v then q e else 0) -
          (if G.tgt e = v then j e else 0)) := by
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> rfl
      _ = _ := by
        exact (Finset.sum_sub_distrib (s := Finset.univ)
          (fun e => if G.tgt e = v then q e else 0)
          (fun e => if G.tgt e = v then j e else 0))
  change ((∑ e, if G.src e = v then (q e - j e) else 0) -
      (∑ e, if G.tgt e = v then (q e - j e) else 0)) = _
  rw [hsrc, htgt]
  ring

/-- A unit source-sink current on the dual square can be spread to logarithmic energy. Its
complement is a graph gradient on the dual-face carrier. The constant is the (coarse) constant
provided by `TheoremC.exists_harmonicField`. -/
theorem exists_scaled_vortex_decomposition {L : ℕ}
    (a x : RotatorSpinSite L)
    (h₁ : siteL1 a x + 1 ≤ (a.1 : ℕ))
    (h₂ : (a.1 : ℕ) + siteL1 a x + 1 ≤ L)
    (h₃ : siteL1 a x + 1 ≤ (a.2 : ℕ))
    (h₄ : (a.2 : ℕ) + siteL1 a x + 1 ≤ L)
    (h₅ : siteL1 a x + 1 ≤ (x.1 : ℕ))
    (h₆ : (x.1 : ℕ) + siteL1 a x + 1 ≤ L)
    (h₇ : siteL1 a x + 1 ≤ (x.2 : ℕ))
    (h₈ : (x.2 : ℕ) + siteL1 a x + 1 ≤ L) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (ξ : ℝ) (q : RotatorInternalBond L → ℤ),
      (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) →
      ∃ (ψ : RotatorDualFace L → ℝ) (θ : RotatorInternalBond L → ℝ),
        (∀ e, 2 * Real.pi * ξ * (q e : ℝ) =
          (rotatorDualGraph L).grad ψ e + θ e) ∧
        (∑ e, θ e ^ 2) ≤ ξ ^ 2 * C₀ *
          (1 + Real.log (1 + (siteL1 a x : ℝ))) := by
  obtain ⟨C₀, hC₀, hfield⟩ := exists_harmonicField
  refine ⟨C₀, hC₀, ?_⟩
  intro ξ q hq
  obtain ⟨j, σ, hj, hσ, henergy⟩ := hfield L a x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  have hneutral : ∀ v, rotatorCurrentDivergence (q - j) v = 0 := by
    intro v
    have hlinear : rotatorCurrentDivergence (q - j) v =
        rotatorCurrentDivergence q v - rotatorCurrentDivergence j v :=
      currentDivergence_sub_local (rotatorFreeGraph L) q j v
    rw [hlinear, hq v, hj v]
    ring
  let h : RotatorFaceHeight L := rotatorHeightFromCurrent (q - j)
  have hcurrent : rotatorFaceHeightCurrent h = q - j :=
    rotatorHeightFromCurrent_current (q - j) hneutral
  let ψ : RotatorDualFace L → ℝ := fun f =>
    ξ * (2 * Real.pi * (h.1 f : ℝ) - σ f)
  let θ : RotatorInternalBond L → ℝ := fun e =>
    ξ * (2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e)
  refine ⟨ψ, θ, ?_, ?_⟩
  · intro e
    rw [Multigraph.grad]
    simp only [ψ, θ]
    have hce := congrFun hcurrent e
    simp only [rotatorFaceHeightCurrent] at hce
    have hcast : ((q e - j e : ℤ) : ℝ) =
        (h.1 ((rotatorDualGraph L).src e) : ℝ) -
          (h.1 ((rotatorDualGraph L).tgt e) : ℝ) := by exact_mod_cast hce.symm
    have hqeq : (q e : ℝ) = (j e : ℝ) + ((q e - j e : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hqeq, hcast]
    rw [Multigraph.grad]
    ring
  · calc
      ∑ e, θ e ^ 2 = ξ ^ 2 * ∑ e, (2 * Real.pi * (j e : ℝ) +
          (rotatorDualGraph L).grad σ e) ^ 2 := by
        simp only [θ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ ≤ ξ ^ 2 * (C₀ * (1 + Real.log (1 + (siteL1 a x : ℝ)))) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg ξ)
      _ = ξ ^ 2 * C₀ * (1 + Real.log (1 + (siteL1 a x : ℝ))) := by ring

end FroehlichSpencer.BKT.Clock.Disorder

end
