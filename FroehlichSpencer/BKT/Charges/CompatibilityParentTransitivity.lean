/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.EnsembleDefinitions

/-! # Transitivity of compatibility parenthood

When an intermediate ensemble is itself built from disjoint-support parents,
the signed coefficients compose. Disjoint supports guarantee that each
original density can occur in at most one intermediate density. -/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.BKT

/-- A nonzero charge has a nonempty finite support. -/
private theorem exists_charge_coordinate_ne_zero {L : ℕ}
    (ρ : ChargeDensity L) (hρ : ρ ≠ 0) : ∃ x, ρ x ≠ 0 := by
  by_contra h
  apply hρ
  funext x
  by_contra hx
  exact (h ⟨x, hx⟩).elim

/-- A nonzero compatibility coefficient includes the full support of its
parent in the represented density. -/
theorem chargeSupport_subset_of_nonzero_compatibilityCoefficient {L : ℕ}
    (E : ChargeEnsemble L) (hE : IsBKTEnsemble E) (ρ : ChargeDensity L)
    (ε : ChargeDensity L → CompatibilitySign)
    (hε : signedChargeSum E ε = ρ) (σ : ChargeDensity L)
    (hσ : σ ∈ E) (hcoeff : (ε σ : ℤ) ≠ 0) :
    chargeSupport σ ⊆ chargeSupport ρ := by
  intro x hx
  have hxσ : σ x ≠ 0 := (Finset.mem_filter.mp hx).2
  have hterms : ∀ τ ∈ E, τ ≠ σ → (ε τ : ℤ) * τ x = 0 := by
    intro τ hτ hτσ
    have hdisj := hE.2 σ hσ τ hτ hτσ.symm
    have hτx : τ x = 0 := by
      by_contra hτx
      have hxτ : x ∈ Function.support τ := by
        simp [Function.mem_support, hτx]
      have hxσ' : x ∈ Function.support σ := by
        simp [Function.mem_support, hxσ]
      exact (Set.disjoint_left.mp hdisj) hxσ' hxτ
    simp [hτx]
  have hnot : σ ∉ E → (ε σ : ℤ) * σ x = 0 := by
    intro hnot
    exact (hnot hσ).elim
  have hcollapse : signedChargeSum E ε x = (ε σ : ℤ) * σ x := by
    unfold signedChargeSum
    exact Finset.sum_eq_single σ hterms hnot
  have hxρ : ρ x ≠ 0 := by
    rw [← hε, hcollapse]
    exact mul_ne_zero hcoeff hxσ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxρ⟩

private theorem compatibilityCoeff_mul_values (a b : CompatibilitySign) :
    (a : ℤ) * (b : ℤ) = -1 ∨ (a : ℤ) * (b : ℤ) = 0 ∨
      (a : ℤ) * (b : ℤ) = 1 := by
  rcases a.property with ha | ha | ha <;>
    rcases b.property with hb | hb | hb <;>
    simp [ha, hb]

/-- If `A` and `B` are valid disjoint-support ensembles, and every member of
`B` is compatible with `A`, then every charge compatible with `B` is
compatible with `A`. -/
theorem IsParentEnsemble_trans {L : ℕ} {A B C : ChargeEnsemble L}
    (hA : IsBKTEnsemble A) (hB : IsBKTEnsemble B)
    (hAB : IsParentEnsemble A B) (hBC : IsParentEnsemble B C) :
    IsParentEnsemble A C := by
  classical
  intro ρ hρ
  obtain ⟨hρne, ⟨η, hη⟩⟩ := hBC ρ hρ
  have hABrepr : ∀ b ∈ B, ∃ ε : ChargeDensity L → CompatibilitySign,
      signedChargeSum A ε = b := fun b hb => (hAB b hb).2
  choose ε hε using hABrepr
  let εAll : ChargeDensity L → ChargeDensity L → CompatibilitySign := fun b a =>
    if hb : b ∈ B then
      if ha : a ∈ A then ε b hb a else compatibilityZero
    else compatibilityZero
  have hεAll (b : ChargeDensity L) (hb : b ∈ B) :
      signedChargeSum A (εAll b) = b := by
    funext x
    calc
      signedChargeSum A (εAll b) x = signedChargeSum A (ε b hb) x := by
        unfold signedChargeSum
        apply Finset.sum_congr rfl
        intro a ha
        simp [εAll, hb, ha]
      _ = b x := congrFun (hε b hb) x
  let γ : ChargeDensity L → ℤ := fun a =>
    ∑ b ∈ B, (η b : ℤ) * (εAll b a : ℤ)
  have hgammaVal (a : ChargeDensity L) :
      γ a = -1 ∨ γ a = 0 ∨ γ a = 1 := by
    by_cases ha : a ∈ A
    · let term : ChargeDensity L → ℤ := fun b =>
        (η b : ℤ) * (εAll b a : ℤ)
      have htermVal (b : ChargeDensity L) :
          term b = -1 ∨ term b = 0 ∨ term b = 1 :=
        compatibilityCoeff_mul_values (η b) (εAll b a)
      have hunique (b c : ChargeDensity L) (hb : b ∈ B) (hc : c ∈ B)
          (hbc : b ≠ c) (hbNZ : term b ≠ 0) (hcNZ : term c ≠ 0) : False := by
        have hεb : (εAll b a : ℤ) ≠ 0 := by
          intro hzero
          apply hbNZ
          simp [term, hzero]
        have hεc : (εAll c a : ℤ) ≠ 0 := by
          intro hzero
          apply hcNZ
          simp [term, hzero]
        have hsubB := chargeSupport_subset_of_nonzero_compatibilityCoefficient
          A hA b (εAll b) (hεAll b hb) a ha hεb
        have hsubC := chargeSupport_subset_of_nonzero_compatibilityCoefficient
          A hA c (εAll c) (hεAll c hc) a ha hεc
        obtain ⟨x, hxval⟩ := exists_charge_coordinate_ne_zero a (hA.1 a ha)
        have hxa : x ∈ chargeSupport a := by
          simp [chargeSupport, hxval]
        have hxb : x ∈ Function.support b := by
          simpa [chargeSupport] using hsubB hxa
        have hxc : x ∈ Function.support c := by
          simpa [chargeSupport] using hsubC hxa
        exact (Set.disjoint_left.mp (hB.2 b hb c hc hbc)) hxb hxc
      by_cases hsome : ∃ b ∈ B, term b ≠ 0
      · obtain ⟨b₀, hb₀, hb₀NZ⟩ := hsome
        have hterms : ∀ b ∈ B, b ≠ b₀ → term b = 0 := by
          intro b hb hbb₀
          by_contra hbNZ
          exact hunique b b₀ hb hb₀ hbb₀ hbNZ hb₀NZ
        have hnot : b₀ ∉ B → term b₀ = 0 := by
          intro hnot
          exact (hnot hb₀).elim
        have hsum : (∑ b ∈ B, term b) = term b₀ :=
          Finset.sum_eq_single b₀ hterms hnot
        rw [show γ a = ∑ b ∈ B, term b by rfl, hsum]
        exact htermVal b₀
      · have hzero : ∀ b ∈ B, term b = 0 := by
          intro b hb
          by_contra hbNZ
          exact hsome ⟨b, hb, hbNZ⟩
        rw [show γ a = ∑ b ∈ B, term b by rfl,
          Finset.sum_eq_zero hzero]
        exact Or.inr (Or.inl rfl)
    · have hzero : ∀ b ∈ B, (η b : ℤ) * (εAll b a : ℤ) = 0 := by
        intro b hb
        simp [εAll, hb, ha, compatibilityZero]
      rw [show γ a = ∑ b ∈ B,
        (η b : ℤ) * (εAll b a : ℤ) by rfl,
        Finset.sum_eq_zero hzero]
      exact Or.inr (Or.inl rfl)
  refine ⟨hρne, ?_⟩
  refine ⟨fun a => ⟨γ a, ?_⟩, ?_⟩
  · rcases hgammaVal a with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · funext x
    unfold signedChargeSum
    calc
      ∑ a ∈ A, γ a * a x =
          ∑ a ∈ A, ∑ b ∈ B, (η b : ℤ) * (εAll b a : ℤ) * a x := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [show γ a = ∑ b ∈ B, (η b : ℤ) *
              (εAll b a : ℤ) by rfl, Finset.sum_mul]
      _ = ∑ b ∈ B, ∑ a ∈ A,
            (η b : ℤ) * (εAll b a : ℤ) * a x := by
              rw [Finset.sum_comm]
      _ = ∑ b ∈ B, (η b : ℤ) * b x := by
            apply Finset.sum_congr rfl
            intro b hb
            calc
              ∑ a ∈ A, (η b : ℤ) * (εAll b a : ℤ) * a x =
                  (η b : ℤ) * ∑ a ∈ A, (εAll b a : ℤ) * a x := by
                    calc
                      ∑ a ∈ A, (η b : ℤ) * (εAll b a : ℤ) * a x =
                          ∑ a ∈ A, (η b : ℤ) *
                            ((εAll b a : ℤ) * a x) := by
                              apply Finset.sum_congr rfl
                              intro a ha
                              ring
                      _ =
                          (η b : ℤ) * ∑ a ∈ A,
                            (εAll b a : ℤ) * a x := by
                              exact (Finset.mul_sum A
                                (fun a => (εAll b a : ℤ) * a x)
                                (η b : ℤ)).symm
              _ = (η b : ℤ) * b x := by
                    exact congrArg (fun y : ℤ => (η b : ℤ) * y)
                      (congrFun (hεAll b hb) x)
      _ = ρ x := by
            change signedChargeSum B η x = ρ x
            exact congrFun hη x

end FroehlichSpencer.BKT

end
