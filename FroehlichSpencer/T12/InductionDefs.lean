/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Obstacles
public import FroehlichSpencer.Surface.FiniteGreen

/-!
# The joint induction predicates of Section 3

the deterministic induction’s finite-volume T2.1 at level `k` is `JPred P Λ v (k + 1) M`.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


abbrev restrictedClasses {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    ℕ → Set (Set (Site ν)) :=
  gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v


def JPred {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) (m : ℝ) :
    Prop :=
  ∀ A : Finset (Site ν), Admissible P.K₀ (restrictedClasses P Λ v) k (A : Set (Site ν)) →
    (∀ x ∈ A ∩ Λ, x ∉ singularSetsIn P Λ v k) →
    ∀ (ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ A ∩ Λ}), scaleD P.K₀ k / 5 ≤ siteDist ν x y →
      ‖finiteGreen ν (A ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (-m * siteDist ν x y)


def NPred {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) (b : ℝ) :
    Prop :=
  ∀ A : Finset (Site ν), Admissible P.K₀ (restrictedClasses P Λ v) k (A : Set (Site ν)) →
    (∀ x ∈ A ∩ Λ, x ∉ singularSetsIn P Λ v k) →
    ∀ (ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ A ∩ Λ}), ‖finiteGreen ν (A ∩ Λ) v P.E ε hε x y‖ ≤ b


noncomputable def normBound (K₀ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else Real.exp (8 * Real.sqrt (scaleD K₀ (k - 1)))


noncomputable def massSeq (K₀ mbase Cstep : ℝ) (k : ℕ) : ℝ :=
  mbase - Cstep * ∑ i ∈ Finset.range k, scaleD K₀ i ^ (-(1 / 8 : ℝ))


def FiniteVolumeT21 (ν : ℕ) (P : Params) (M : ℝ) : Prop :=
  ∀ (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ), JPred P Λ v (k + 1) M


def LevelScale (ν : ℕ) (K₀ : ℝ) (k : ℕ) (m τ μ m' : ℝ) : Prop :=
  0 ≤ τ ∧ 0 ≤ μ ∧ μ ≤ m - τ ∧ 0 ≤ m' ∧ 3 ^ 8 ≤ scaleD K₀ k ∧
  (2 * ν * (25 * scaleD K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD K₀ k) - m * scaleD K₀ k) ≤ 1 / 2 ∧
  normBound K₀ k + (2 * ν * (25 * scaleD K₀ k) ^ ν) ^ 2 * normBound K₀ k ^ 2 *
      (2 * Real.exp (Real.sqrt (scaleD K₀ k))) ≤ Real.exp (4 * Real.sqrt (scaleD K₀ k)) ∧
  Real.log (1 + 2 * (2 * ν * (25 * scaleD K₀ k) ^ ν) ^ 2 * normBound K₀ k ^ 2 *
      Real.exp (Real.sqrt (scaleD K₀ k) + m * (2 * scaleD K₀ k + 2 + 2 * scaleD K₀ k / 5))) ≤
    τ * scaleD K₀ k ^ (9 / 8 : ℝ) ∧
  2 * ν * (8 * scaleD K₀ (k + 1)) ^ ν *
      Real.exp (-(m - τ - μ) * (scaleD K₀ (k + 1) / 2) + μ) ≤ 1 / 2 ∧
  Real.log 2 + (m - τ) * scaleD K₀ k ^ (9 / 8 : ℝ) + 4 * Real.sqrt (scaleD K₀ k) ≤
    (μ - m') * (scaleD K₀ (k + 1) / 5) ∧
  2 * ν * (8 * scaleD K₀ (k + 1)) ^ ν * Real.exp (-(m - τ) * (scaleD K₀ (k + 1) / 2)) ≤ 1


noncomputable def locLoss (K₀ mbase : ℝ) (k : ℕ) : ℝ := 3 * mbase * scaleD K₀ k ^ (-(1 / 8 : ℝ))


noncomputable def iterRate (ν : ℕ) (K₀ m τ : ℝ) (k : ℕ) : ℝ :=
  ((m - τ) * (scaleD K₀ (k + 1) / 2) -
      Real.log (2 * (2 * ν * (8 * scaleD K₀ (k + 1)) ^ ν))) / (scaleD K₀ (k + 1) / 2 + 1)

end FroehlichSpencer.T12

end
