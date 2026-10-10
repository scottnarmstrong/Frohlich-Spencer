/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Covers
public import FroehlichSpencer.BKT.Surface.ChargeEnsemble

/-! # Charge ensembles and compatibility (KP §4.2.1)

This module records the source definitions on the finite square carrier. The
charge carrier is C1's function space; the density predicate excludes the zero
function, as in KP §1.7.1. -/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.BKT

/-- A nonzero integer-valued function on the finite square is a charge density. -/
def IsChargeDensity {L : ℕ} (ρ : ChargeDensity L) : Prop := ρ ≠ 0

/-- A finite family of charge densities, represented by its underlying
collection of functions. -/
abbrev ChargeEnsemble (L : ℕ) := Finset (ChargeDensity L)

/-- The signs allowed in compatibility coefficients. -/
def CompatibilitySign := {z : ℤ // z = -1 ∨ z = 0 ∨ z = 1}

instance : Coe CompatibilitySign ℤ := ⟨Subtype.val⟩

/-- The zero compatibility coefficient. -/
def compatibilityZero : CompatibilitySign := ⟨0, Or.inr (Or.inl rfl)⟩

/-- The positive compatibility coefficient. -/
def compatibilityOne : CompatibilitySign := ⟨1, Or.inr (Or.inr rfl)⟩

/-- The negative compatibility coefficient. -/
def compatibilityNegOne : CompatibilitySign := ⟨-1, Or.inl rfl⟩

/-- Coefficients representing a member density by itself. -/
def selfCompatibilityCoefficient {L : ℕ} (ρ : ChargeDensity L) :
    ChargeDensity L → CompatibilitySign := fun σ =>
  if σ = ρ then compatibilityOne else compatibilityZero

/-- The signed sum of an ensemble with coefficients in `{-1,0,1}`. -/
def signedChargeSum {L : ℕ} (E : ChargeEnsemble L)
    (ε : ChargeDensity L → CompatibilitySign) : ChargeDensity L :=
  fun x => E.sum fun ρ => (ε ρ : ℤ) * ρ x

/-- Compatibility in the sense of KP §4.2.1. -/
def IsCompatible {L : ℕ} (E : ChargeEnsemble L) (ρ : ChargeDensity L) : Prop :=
  IsChargeDensity ρ ∧ ∃ ε : ChargeDensity L → CompatibilitySign,
    signedChargeSum E ε = ρ

/-- An ensemble is a finite family of nonzero densities with pairwise
disjoint supports. -/
abbrev IsBKTEnsemble {L : ℕ} (E : ChargeEnsemble L) : Prop :=
  IsChargeEnsemble E

/-- Every subfamily of an ensemble is an ensemble. -/
theorem IsBKTEnsemble_mono {L : ℕ} {E E' : ChargeEnsemble L}
    (hE : IsBKTEnsemble E) (hsub : E' ⊆ E) : IsBKTEnsemble E' := by
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    exact hE.1 ρ (hsub hρ)
  · intro ρ hρ σ hσ hne
    exact hE.2 ρ (hsub hρ) σ (hsub hσ) hne

/-- `E` is a parent of `E'` when each child density is compatible with `E`. -/
def IsParentEnsemble {L : ℕ} (E E' : ChargeEnsemble L) : Prop :=
  ∀ ρ ∈ E', IsCompatible E ρ

/-- Every valid ensemble is its own parent. -/
theorem IsParentEnsemble_refl {L : ℕ} (E : ChargeEnsemble L)
    (hE : IsBKTEnsemble E) : IsParentEnsemble E E := by
  intro ρ hρ
  refine ⟨hE.1 ρ hρ, ?_⟩
  refine ⟨selfCompatibilityCoefficient ρ, ?_⟩
  funext x
  unfold signedChargeSum
  rw [Finset.sum_eq_single ρ]
  · simp [selfCompatibilityCoefficient, compatibilityOne]
  · intro σ hσ hσρ
    simp [selfCompatibilityCoefficient, compatibilityZero, hσρ]
  · intro hnot
    exact (hnot hρ).elim

/-- A two-member signed sum only uses the selected pair; all other members
have zero coefficients. -/
theorem signedChargeSum_pair {L : ℕ} (E : ChargeEnsemble L)
    (ρ σ : ChargeDensity L) (a b : CompatibilitySign)
    (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    signedChargeSum E
        (fun τ => if τ = ρ then a else if τ = σ then b else compatibilityZero) =
      fun x => (a : ℤ) * ρ x + (b : ℤ) * σ x := by
  classical
  funext x
  let ε : ChargeDensity L → CompatibilitySign := fun τ =>
    if τ = ρ then a else if τ = σ then b else compatibilityZero
  have hterm (τ : ChargeDensity L) :
      (ε τ : ℤ) * τ x =
        (if τ = ρ then (a : ℤ) * ρ x else 0) +
          (if τ = σ then (b : ℤ) * σ x else 0) := by
    by_cases hτρ : τ = ρ
    · subst τ
      simp [ε, hne]
    · by_cases hτσ : τ = σ
      · subst τ
        simp [ε, hτρ]
      · simp [ε, hτρ, hτσ, compatibilityZero]
  unfold signedChargeSum
  calc
    E.sum (fun τ => (ε τ : ℤ) * τ x) =
        E.sum (fun τ =>
          (if τ = ρ then (a : ℤ) * ρ x else 0) +
            (if τ = σ then (b : ℤ) * σ x else 0)) := by
      apply Finset.sum_congr rfl
      intro τ hτ
      exact hterm τ
    _ = E.sum (fun τ => if τ = ρ then (a : ℤ) * ρ x else 0) +
        E.sum (fun τ => if τ = σ then (b : ℤ) * σ x else 0) :=
      Finset.sum_add_distrib
    _ = (a : ℤ) * ρ x + (b : ℤ) * σ x := by
      simp [Finset.sum_ite_eq', hρ, hσ]

/-- Constituent relation: support inclusion together with agreement on the
constituent's support. -/
def IsChargeConstituent {L : ℕ} (ρ ρ₁ : ChargeDensity L) : Prop :=
  chargeSupport ρ ⊆ chargeSupport ρ₁ ∧
    ∀ x ∈ chargeSupport ρ, ρ x = ρ₁ x

/-- An integer scale, including KP's `k = -1` endpoint. At that endpoint the
strict natural-distance test `dist > 0` is equivalent to `dist > 2^(-1)`. -/
inductive ChargeScale where
  | minusOne
  | ofNat (k : ℕ)
  deriving DecidableEq, Repr

/-- The natural threshold for separation at a KP scale. -/
def ChargeScale.separationThreshold : ChargeScale → ℕ
  | .minusOne => 0
  | .ofNat k => 2 ^ k

/-- Strictly separated ensembles at KP scale `k`. The natural endpoint
convention in `minusOne` is equivalent to the real threshold `2^(-1)` because
all graph distances are natural numbers. -/
def IsChargeScaleEnsemble {L : ℕ} (boundary : SquareBoundary) (E : ChargeEnsemble L)
    (k : ChargeScale) : Prop :=
  IsBKTEnsemble E ∧
    ∀ ρ ∈ E, ∀ σ ∈ E, ρ ≠ σ →
      ChargeScale.separationThreshold k < densityDistance boundary L ρ σ

/-- The covering cost `A_k`: at scales `-1` and `0` it is support cardinality;
at positive scales it is the minimum square-cover number. -/
noncomputable def chargeA (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) : ChargeScale → ℕ
  | .minusOne => (chargeSupport ρ).card
  | .ofNat 0 => (chargeSupport ρ).card
  | .ofNat (k + 1) => squareCoverNumber boundary L (k + 1) ρ

@[simp]
theorem chargeA_minusOne_eq_supportCard (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) :
    chargeA boundary L ρ .minusOne = (chargeSupport ρ).card := rfl

@[simp]
theorem chargeA_zero_eq_supportCard (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) :
    chargeA boundary L ρ (.ofNat 0) = (chargeSupport ρ).card := rfl

/-- Uniqueness of compatibility coefficients on ensemble members. This is the
precise scope in which coefficients are meaningful. -/
theorem compatibleCoefficients_unique {L : ℕ} (E : ChargeEnsemble L)
    (hE : IsBKTEnsemble E) (ρ : ChargeDensity L)
    (ε₁ ε₂ : ChargeDensity L → CompatibilitySign)
    (h₁ : signedChargeSum E ε₁ = ρ) (h₂ : signedChargeSum E ε₂ = ρ) :
    ∀ σ ∈ E, ε₁ σ = ε₂ σ := by
  intro σ hσ
  have hσne : σ ≠ 0 := hE.1 σ hσ
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ 0 := by
    by_contra h
    apply hσne
    funext y
    by_contra hy
    exact (h ⟨y, hy⟩).elim
  have hxσ : x ∈ chargeSupport σ := by
    simp [chargeSupport, hx]
  have hcollapse (ε : ChargeDensity L → CompatibilitySign) :
      signedChargeSum E ε x = (ε σ : ℤ) * σ x := by
    unfold signedChargeSum
    have hzero : ∀ τ ∈ E, τ ≠ σ → (ε τ : ℤ) * τ x = 0 := by
      intro τ hτ hτσ
      have hdisj := hE.2 σ hσ τ hτ hτσ.symm
      have hτx : τ x = 0 := by
        by_contra hτx
        have hxτ : x ∈ Function.support τ := by
          simp [Function.mem_support, hτx]
        have hxσ' : x ∈ Function.support σ := by
          simp [Function.mem_support, hx]
        exact (Set.disjoint_left.mp hdisj) hxσ' hxτ
      simp [hτx]
    have hnot : σ ∉ E → (ε σ : ℤ) * σ x = 0 := by
      intro hnot
      exact (hnot hσ).elim
    rw [Finset.sum_eq_single σ hzero hnot]
  have hmul : (ε₁ σ : ℤ) * σ x = (ε₂ σ : ℤ) * σ x := by
    calc
      (ε₁ σ : ℤ) * σ x = signedChargeSum E ε₁ x := (hcollapse ε₁).symm
      _ = ρ x := congrFun h₁ x
      _ = signedChargeSum E ε₂ x := (congrFun h₂ x).symm
      _ = (ε₂ σ : ℤ) * σ x := hcollapse ε₂
  apply Subtype.ext
  exact (mul_right_cancel₀ hx) hmul

end FroehlichSpencer.BKT

end
