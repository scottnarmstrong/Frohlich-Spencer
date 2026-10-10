/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# The duplicated-variable algebra behind Ginibre's inequalities

Trigonometric polynomials in two copies `θ, θ'` of the angles are encoded by the real group algebra
of the frequency pairs `(p, q) ∈ ℤ^V × ℤ^V`, the basis element `(p, q)` standing for
`exp(i(p·θ + q·θ'))`. Ginibre's argument (J. Ginibre, Comm. Math. Phys. 16 (1970) 310–328;
external input `X:Ginibre`) changes the frequency coordinates by the injective map
`(p, q) ↦ (p + q, p - q)`. After this change, the formal version of `cos(m·θ) ± cos(m·θ')` is
`½ X ⊗ X` with `X = e_m ± e_{-m}`, so every product of such factors is a nonnegative combination of
tensor squares `Y ⊗ Y`, whose constant coefficient `(Y₀)²` is nonnegative.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

open AddMonoidAlgebra

variable {V : Type*}

/-- Integer frequency vectors on the sites. -/
abbrev Frequency (V : Type*) := V → ℤ

/-- Formal real trigonometric polynomials in one copy of the angles. -/
abbrev TrigAlgebra (V : Type*) := AddMonoidAlgebra ℝ (Frequency V)

/-- Formal real trigonometric polynomials in two copies of the angles. -/
abbrev DupTrigAlgebra (V : Type*) := AddMonoidAlgebra ℝ (Frequency V × Frequency V)

/-- The change of frequency coordinates `(p, q) ↦ (p + q, p - q)`. -/
def sumDiffHom (V : Type*) : (Frequency V × Frequency V) →+ (Frequency V × Frequency V) :=
  AddMonoidHom.prod (AddMonoidHom.fst _ _ + AddMonoidHom.snd _ _)
    (AddMonoidHom.fst _ _ - AddMonoidHom.snd _ _)

theorem sumDiffHom_apply (g : Frequency V × Frequency V) :
    sumDiffHom V g = (g.1 + g.2, g.1 - g.2) := rfl

theorem sumDiffHom_injective : Function.Injective (sumDiffHom V) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  simp only [sumDiffHom_apply, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  have hp : p = p' := by
    funext x
    have a := congrFun h₁ x
    have b := congrFun h₂ x
    simp only [Pi.add_apply, Pi.sub_apply] at a b
    omega
  subst hp
  have hq : q = q' := by
    funext x
    have a := congrFun h₁ x
    simp only [Pi.add_apply] at a
    omega
  rw [hq]

/-- The change of frequency coordinates on formal polynomials. -/
def sumDiffMap (V : Type*) : DupTrigAlgebra V →+* DupTrigAlgebra V :=
  mapDomainRingHom ℝ (sumDiffHom V)

theorem coeff_sumDiffMap_zero (P : DupTrigAlgebra V) :
    (sumDiffMap V P).coeff 0 = P.coeff 0 := by
  have h := Finsupp.mapDomain_apply_of_injective (sumDiffHom_injective (V := V)) P.coeff 0
  rw [map_zero] at h
  exact h

/-- Formal polynomials in the first copy of the angles. -/
def leftEmbed (V : Type*) : TrigAlgebra V →+* DupTrigAlgebra V :=
  mapDomainRingHom ℝ (AddMonoidHom.inl _ _)

/-- Formal polynomials in the second copy of the angles. -/
def rightEmbed (V : Type*) : TrigAlgebra V →+* DupTrigAlgebra V :=
  mapDomainRingHom ℝ (AddMonoidHom.inr _ _)

/-- The tensor product `Y ⊗ Z` of two formal polynomials in one copy of the angles. -/
def tensor (Y Z : TrigAlgebra V) : DupTrigAlgebra V :=
  leftEmbed V Y * rightEmbed V Z

theorem tensor_single_single (m n : Frequency V) (r s : ℝ) :
    tensor (single m r) (single n s) = single (m, n) (r * s) := by
  simp [tensor, leftEmbed, rightEmbed, mapDomain_single, single_mul_single]

theorem coeff_tensor (Y Z : TrigAlgebra V) (a b : Frequency V) :
    (tensor Y Z).coeff (a, b) = Y.coeff a * Z.coeff b := by
  classical
  induction Y using AddMonoidAlgebra.induction_linear with
  | zero => simp [tensor]
  | add Y₁ Y₂ h₁ h₂ =>
      simp only [tensor, map_add, add_mul, coeff_add, Finsupp.add_apply] at h₁ h₂ ⊢
      rw [h₁, h₂]
  | single m r =>
      induction Z using AddMonoidAlgebra.induction_linear with
      | zero => simp [tensor]
      | add Z₁ Z₂ h₁ h₂ =>
          simp only [tensor, map_add, mul_add, coeff_add, Finsupp.add_apply] at h₁ h₂ ⊢
          rw [h₁, h₂]
      | single n s =>
          rw [tensor_single_single]
          simp only [coeff_single, Finsupp.single_apply, Prod.mk.injEq]
          split_ifs <;> simp_all

theorem tensor_mul_tensor (Y Z Y' Z' : TrigAlgebra V) :
    tensor Y Z * tensor Y' Z' = tensor (Y * Y') (Z * Z') := by
  simp only [tensor, map_mul]
  ring

theorem tensor_one : tensor (1 : TrigAlgebra V) 1 = 1 := by
  simp [tensor]

/-- Nonnegative combinations of tensor squares `Y ⊗ Y`. -/
inductive IsSquareSum : DupTrigAlgebra V → Prop
  | square (c : ℝ) (hc : 0 ≤ c) (Y : TrigAlgebra V) : IsSquareSum (c • tensor Y Y)
  | add {P Q : DupTrigAlgebra V} : IsSquareSum P → IsSquareSum Q → IsSquareSum (P + Q)

namespace IsSquareSum

theorem zero : IsSquareSum (0 : DupTrigAlgebra V) := by
  simpa using IsSquareSum.square (0 : ℝ) le_rfl (0 : TrigAlgebra V)

theorem one : IsSquareSum (1 : DupTrigAlgebra V) := by
  simpa [tensor_one] using IsSquareSum.square (1 : ℝ) zero_le_one (1 : TrigAlgebra V)

theorem smul {P : DupTrigAlgebra V} (hP : IsSquareSum P) {c : ℝ} (hc : 0 ≤ c) :
    IsSquareSum (c • P) := by
  induction hP with
  | square c' hc' Y =>
      rw [smul_smul]
      exact IsSquareSum.square _ (mul_nonneg hc hc') Y
  | add _ _ hP hQ =>
      rw [smul_add]
      exact hP.add hQ

theorem mul {P Q : DupTrigAlgebra V} (hP : IsSquareSum P) (hQ : IsSquareSum Q) :
    IsSquareSum (P * Q) := by
  induction hP with
  | square c hc Y =>
      induction hQ with
      | square c' hc' Y' =>
          rw [smul_mul_smul_comm, tensor_mul_tensor]
          exact IsSquareSum.square _ (mul_nonneg hc hc') _
      | add _ _ hP hQ =>
          rw [mul_add]
          exact hP.add hQ
  | add _ _ hP hQ =>
      rw [add_mul]
      exact hP.add hQ

/-- The constant coefficient of a nonnegative combination of tensor squares is nonnegative. -/
theorem coeff_zero_nonneg {P : DupTrigAlgebra V} (hP : IsSquareSum P) : 0 ≤ P.coeff 0 := by
  induction hP with
  | square c hc Y =>
      rw [coeff_smul_apply, Prod.zero_eq_mk, coeff_tensor, smul_eq_mul]
      exact mul_nonneg hc (mul_self_nonneg _)
  | add _ _ hP hQ =>
      rw [coeff_add, Finsupp.add_apply]
      exact add_nonneg hP hQ

end IsSquareSum

/-- Ginibre's cone: formal polynomials that become nonnegative combinations of tensor squares after
the change of frequency coordinates `(p, q) ↦ (p + q, p - q)`. -/
def IsGinibre (P : DupTrigAlgebra V) : Prop :=
  IsSquareSum (sumDiffMap V P)

namespace IsGinibre

theorem zero : IsGinibre (0 : DupTrigAlgebra V) := by
  rw [IsGinibre, map_zero]
  exact IsSquareSum.zero

theorem one : IsGinibre (1 : DupTrigAlgebra V) := by
  rw [IsGinibre, map_one]
  exact IsSquareSum.one

theorem add {P Q : DupTrigAlgebra V} (hP : IsGinibre P) (hQ : IsGinibre Q) :
    IsGinibre (P + Q) := by
  rw [IsGinibre, map_add]
  exact IsSquareSum.add hP hQ

theorem mul {P Q : DupTrigAlgebra V} (hP : IsGinibre P) (hQ : IsGinibre Q) :
    IsGinibre (P * Q) := by
  rw [IsGinibre, map_mul]
  exact IsSquareSum.mul hP hQ

theorem smul {P : DupTrigAlgebra V} (hP : IsGinibre P) {c : ℝ} (hc : 0 ≤ c) :
    IsGinibre (c • P) := by
  have h : sumDiffMap V (c • P) = c • sumDiffMap V P := by
    simp [sumDiffMap, mapDomainRingHom_apply, mapDomain, Finsupp.mapDomain_smul]
  rw [IsGinibre, h]
  exact IsSquareSum.smul hP hc

theorem pow {P : DupTrigAlgebra V} (hP : IsGinibre P) (n : ℕ) : IsGinibre (P ^ n) := by
  induction n with
  | zero => simpa using IsGinibre.one
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hP

theorem sum {ι : Type*} (s : Finset ι) {P : ι → DupTrigAlgebra V} (hP : ∀ i ∈ s, IsGinibre (P i)) :
    IsGinibre (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsGinibre.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hP a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

/-- The constant coefficient of an element of Ginibre's cone is nonnegative. -/
theorem coeff_zero_nonneg {P : DupTrigAlgebra V} (hP : IsGinibre P) : 0 ≤ P.coeff 0 := by
  rw [← coeff_sumDiffMap_zero]
  exact IsSquareSum.coeff_zero_nonneg hP

end IsGinibre

/-- The formal version of `cos(m·θ) + σ cos(m·θ')`. -/
def cosPair (m : Frequency V) (σ : ℝ) : DupTrigAlgebra V :=
  single (m, 0) (1 / 2) + single (-m, 0) (1 / 2) + single (0, m) (σ / 2) + single (0, -m) (σ / 2)

theorem sumDiffMap_cosPair (m : Frequency V) {σ : ℝ} (hσ : σ * σ = 1) :
    sumDiffMap V (cosPair m σ) =
      (1 / 2 : ℝ) • tensor (single m 1 + single (-m) σ) (single m 1 + single (-m) σ) := by
  simp only [cosPair, sumDiffMap, map_add, mapDomainRingHom_apply, mapDomain_single,
    sumDiffHom_apply, tensor, leftEmbed, rightEmbed, add_mul, mul_add, single_mul_single,
    AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_add, sub_zero,
    zero_sub, sub_neg_eq_add, smul_add, smul_single, hσ, smul_eq_mul]
  have h : (1 / 2 : ℝ) * σ = σ / 2 := by ring
  simp only [mul_one, one_mul, h]
  abel

/-- `cos(m·θ) ± cos(m·θ')` lies in Ginibre's cone. -/
theorem isGinibre_cosPair (m : Frequency V) {σ : ℝ} (hσ : σ * σ = 1) :
    IsGinibre (cosPair m σ) := by
  rw [IsGinibre, sumDiffMap_cosPair m hσ]
  exact IsSquareSum.square _ (by positivity) _

end FroehlichSpencer.BKT.Rotator.Ginibre

end
