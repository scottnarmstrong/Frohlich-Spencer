/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import FroehlichSpencer.BKT.Charges.EnsembleDefinitions

/-! # The two-factor identity behind KP Lemma 4.3

This module formalizes the exact local convex rewrite (4.12). The finite
termination and quantitative merge-tree estimates are separated into the
global basic-lemma module. -/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.BKT

/-- The real phase pairing of a site field with an integer charge density. -/
def chargePhase {L : ℕ} (ψ : (Fin L × Fin L) → ℝ)
    (ρ : ChargeDensity L) : ℝ :=
  ∑ x, ψ x * (ρ x : ℝ)

/-- The density carrying a single integer charge at one site. -/
def pointCharge {L : ℕ} (x : Fin L × Fin L) (q : ℤ) : ChargeDensity L :=
  fun y => if y = x then q else 0

/-- Pairing a point charge reads the field at that site. -/
theorem chargePhase_pointCharge {L : ℕ} (ψ : (Fin L × Fin L) → ℝ)
    (x : Fin L × Fin L) (q : ℤ) :
    chargePhase ψ (pointCharge x q) = (q : ℝ) * ψ x := by
  simp [chargePhase, pointCharge]
  ring

/-- The support of a sum of charges with disjoint supports is their union. -/
theorem functionSupport_add_of_disjoint {L : ℕ} (ρ σ : ChargeDensity L)
    (hdisj : Disjoint (Function.support ρ) (Function.support σ)) :
    Function.support (ρ + σ) = Function.support ρ ∪ Function.support σ := by
  ext x
  simp only [Function.mem_support, Pi.add_apply, Set.mem_union]
  constructor
  · intro hsum
    by_cases hρ : ρ x = 0
    · right
      intro hσ
      have hzero : ρ x + σ x = 0 := by simp [hρ, hσ]
      exact hsum hzero
    · exact Or.inl hρ
  · rintro (hρ | hσ)
    · have hxρ : x ∈ Function.support ρ := by simpa using hρ
      have hxσ : x ∉ Function.support σ := fun hxσ =>
        (Set.disjoint_left.mp hdisj) hxρ hxσ
      have hσ0 : σ x = 0 := by
        by_contra hσ0
        exact hxσ (by simpa using hσ0)
      simpa [hσ0] using hρ
    · have hxσ : x ∈ Function.support σ := by simpa using hσ
      have hxρ : x ∉ Function.support ρ := fun hxρ =>
        (Set.disjoint_left.mp hdisj) hxρ hxσ
      have hρ0 : ρ x = 0 := by
        by_contra hρ0
        exact hxρ (by simpa using hρ0)
      have hnonzero : ρ x + σ x ≠ 0 := by simpa [hρ0] using hσ
      exact hnonzero

/-- Negating a charge does not change its support. -/
theorem functionSupport_neg {L : ℕ} (ρ : ChargeDensity L) :
    Function.support (-ρ) = Function.support ρ := by
  ext x
  simp

/-- The support of a difference of charges with disjoint supports is their union. -/
theorem functionSupport_sub_of_disjoint {L : ℕ} (ρ σ : ChargeDensity L)
    (hdisj : Disjoint (Function.support ρ) (Function.support σ)) :
    Function.support (ρ - σ) = Function.support ρ ∪ Function.support σ := by
  rw [sub_eq_add_neg, functionSupport_add_of_disjoint]
  · rw [functionSupport_neg]
  · simpa only [functionSupport_neg] using hdisj

/-- A nonzero charge is nonzero at some site. -/
theorem exists_coordinate_ne_zero {L : ℕ} (ρ : ChargeDensity L)
    (hρ : ρ ≠ 0) : ∃ x, ρ x ≠ 0 := by
  by_contra h
  apply hρ
  funext x
  by_contra hx
  exact (h ⟨x, hx⟩).elim

/-- Sum and difference charges are compatible with an ensemble containing a
disjoint-support pair. -/
theorem compatible_add_of_pair {L : ℕ} (E : ChargeEnsemble L)
    (hE : IsBKTEnsemble E) (ρ σ : ChargeDensity L)
    (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    IsCompatible E (ρ + σ) := by
  classical
  have hdisj := hE.2 ρ hρ σ hσ hne
  have hρne := hE.1 ρ hρ
  obtain ⟨x, hxρ⟩ := exists_coordinate_ne_zero ρ hρne
  have hxρSupport : x ∈ Function.support ρ := by
    simp [Function.mem_support, hxρ]
  have hσx : σ x = 0 := by
    by_contra hσx
    have hxσ : x ∈ Function.support σ := by
      simp [Function.mem_support, hσx]
    exact (Set.disjoint_left.mp hdisj) hxρSupport hxσ
  have hsumNe : ρ + σ ≠ 0 := by
    intro hzero
    have hval := congrFun hzero x
    simp [hσx] at hval
    exact hxρ hval
  refine ⟨hsumNe, ?_⟩
  refine ⟨fun τ => if τ = ρ then compatibilityOne else
    if τ = σ then compatibilityOne else compatibilityZero, ?_⟩
  have hsum := signedChargeSum_pair E ρ σ compatibilityOne compatibilityOne
    hρ hσ hne
  rw [hsum]
  funext y
  simp [compatibilityOne, Pi.add_apply]

/-- The difference branch in (4.12) is compatible with its two input charges. -/
theorem compatible_sub_of_pair {L : ℕ} (E : ChargeEnsemble L)
    (hE : IsBKTEnsemble E) (ρ σ : ChargeDensity L)
    (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    IsCompatible E (ρ - σ) := by
  classical
  have hdisj := hE.2 ρ hρ σ hσ hne
  have hρne := hE.1 ρ hρ
  obtain ⟨x, hxρ⟩ := exists_coordinate_ne_zero ρ hρne
  have hxρSupport : x ∈ Function.support ρ := by
    simp [Function.mem_support, hxρ]
  have hσx : σ x = 0 := by
    by_contra hσx
    have hxσ : x ∈ Function.support σ := by
      simp [Function.mem_support, hσx]
    exact (Set.disjoint_left.mp hdisj) hxρSupport hxσ
  have hsubNe : ρ - σ ≠ 0 := by
    intro hzero
    have hval := congrFun hzero x
    simp [hσx] at hval
    exact hxρ hval
  refine ⟨hsubNe, ?_⟩
  refine ⟨fun τ => if τ = ρ then compatibilityOne else
    if τ = σ then compatibilityNegOne else compatibilityZero, ?_⟩
  have hsum := signedChargeSum_pair E ρ σ compatibilityOne compatibilityNegOne
    hρ hσ hne
  rw [hsum]
  funext y
  simp [compatibilityOne, compatibilityNegOne, Pi.sub_apply]
  ring

/-- Replacing two members of an ensemble by a charge whose support is exactly
their union preserves the ensemble property. -/
theorem insertMergedCharge_isBKTEnsemble {L : ℕ} (E : ChargeEnsemble L)
    (ρ σ merged : ChargeDensity L) (hE : IsBKTEnsemble E)
    (hρ : ρ ∈ E) (hσ : σ ∈ E)
    (hsupport : Function.support merged =
      Function.support ρ ∪ Function.support σ) :
    IsBKTEnsemble (insert merged (E.erase ρ |>.erase σ)) := by
  classical
  let R := E.erase ρ |>.erase σ
  have hρne : ρ ≠ 0 := hE.1 ρ hρ
  obtain ⟨x, hxρ⟩ : ∃ x, ρ x ≠ 0 := by
    by_contra h
    apply hρne
    funext y
    by_contra hy
    exact (h ⟨y, hy⟩).elim
  have hxρSupport : x ∈ Function.support ρ := by
    simp [Function.mem_support, hxρ]
  have hRparts (τ : ChargeDensity L) (hτ : τ ∈ R) :
      τ ≠ σ ∧ τ ≠ ρ ∧ τ ∈ E := by
    dsimp [R] at hτ
    rcases Finset.mem_erase.mp hτ with ⟨hτσ, hτ⟩
    rcases Finset.mem_erase.mp hτ with ⟨hτρ, hτE⟩
    exact ⟨hτσ, hτρ, hτE⟩
  have hmergedNe (τ : ChargeDensity L) (hτ : τ ∈ R) : merged ≠ τ := by
    intro hEq
    have hdisj := hE.2 ρ hρ τ (hRparts τ hτ).2.2 (hRparts τ hτ).2.1.symm
    have hxMerged : x ∈ Function.support merged := by
      rw [hsupport]
      exact Set.mem_union_left _ hxρSupport
    have hxτ : x ∈ Function.support τ := by
      rw [← hEq]
      exact hxMerged
    exact (Set.disjoint_left.mp hdisj) hxρSupport hxτ
  have hmergedNeZero : merged ≠ 0 := by
    intro hzero
    have hxMerged : x ∈ Function.support merged := by
      rw [hsupport]
      exact Set.mem_union_left _ hxρSupport
    have hxZero : ¬ x ∈ Function.support merged := by
      rw [hzero]
      simp
    exact hxZero hxMerged
  have hdisjMergedR (τ : ChargeDensity L) (hτ : τ ∈ R) :
      Disjoint (Function.support merged) (Function.support τ) := by
    apply Set.disjoint_left.mpr
    intro y hyMerged hyτ
    rw [hsupport] at hyMerged
    rcases hyMerged with hyρ | hyσ
    · have hdisj := hE.2 ρ hρ τ (hRparts τ hτ).2.2 (hRparts τ hτ).2.1.symm
      exact (Set.disjoint_left.mp hdisj) hyρ hyτ
    · have hdisj := hE.2 σ hσ τ (hRparts τ hτ).2.2 (hRparts τ hτ).1.symm
      exact (Set.disjoint_left.mp hdisj) hyσ hyτ
  refine ⟨?_, ?_⟩
  · intro τ hτ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · subst τ
      exact hmergedNeZero
    · exact hE.1 τ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hτ))
  · intro τ hτ υ hυ hτneυ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · subst τ
      rcases Finset.mem_insert.mp hυ with hυ | hυ
      · subst υ
        exact (hτneυ rfl).elim
      · exact hdisjMergedR υ hυ
    · rcases Finset.mem_insert.mp hυ with hυ | hυ
      · subst υ
        exact (hdisjMergedR τ hτ).symm
      · exact hE.2 τ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hτ))
          υ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hυ)) hτneυ

/-- A merged charge cannot coincide with an untouched factor: its support
contains the support of the first input, which is disjoint from the remainder. -/
theorem mergedCharge_not_mem_pairRest {L : ℕ} (E : ChargeEnsemble L)
    (ρ σ merged : ChargeDensity L) (hE : IsBKTEnsemble E)
    (hρ : ρ ∈ E)
    (hsupport : Function.support merged =
      Function.support ρ ∪ Function.support σ) :
    merged ∉ (E.erase ρ |>.erase σ) := by
  classical
  intro hmem
  have hρne : ρ ≠ 0 := hE.1 ρ hρ
  obtain ⟨x, hxρ⟩ := exists_coordinate_ne_zero ρ hρne
  have hxρSupport : x ∈ Function.support ρ := by
    simp [Function.mem_support, hxρ]
  have hparts : merged ≠ ρ ∧ merged ∈ E := by
    rcases Finset.mem_erase.mp hmem with ⟨_, hmem⟩
    rcases Finset.mem_erase.mp hmem with ⟨hmρ, hmE⟩
    exact ⟨hmρ, hmE⟩
  have hdisj := hE.2 ρ hρ merged hparts.2 hparts.1.symm
  have hxMerged : x ∈ Function.support merged := by
    rw [hsupport]
    exact Set.mem_union_left _ hxρSupport
  exact (Set.disjoint_left.mp hdisj) hxρSupport hxMerged

/-- All four outputs of one application of (4.12) remain valid ensembles and
are parented by the original ensemble. -/
theorem pairRewriteBranches_are_parentedEnsembles {L : ℕ}
    (E : ChargeEnsemble L) (hE : IsBKTEnsemble E)
    (ρ σ : ChargeDensity L) (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    let R := E.erase ρ |>.erase σ
    (IsBKTEnsemble (insert ρ R) ∧ IsParentEnsemble E (insert ρ R)) ∧
      (IsBKTEnsemble (insert σ R) ∧ IsParentEnsemble E (insert σ R)) ∧
      (IsBKTEnsemble (insert (ρ - σ) R) ∧
        IsParentEnsemble E (insert (ρ - σ) R)) ∧
      (IsBKTEnsemble (insert (ρ + σ) R) ∧
        IsParentEnsemble E (insert (ρ + σ) R)) := by
  classical
  dsimp
  have hRsub : (E.erase ρ |>.erase σ) ⊆ E := by
    intro τ hτ
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hτ)
  have hparentRefl := IsParentEnsemble_refl E hE
  have hsubρ : insert ρ (E.erase ρ |>.erase σ) ⊆ E := by
    intro τ hτ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · simpa [hτ] using hρ
    · exact hRsub hτ
  have hsubσ : insert σ (E.erase ρ |>.erase σ) ⊆ E := by
    intro τ hτ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · simpa [hτ] using hσ
    · exact hRsub hτ
  have hEρ := IsBKTEnsemble_mono hE hsubρ
  have hEσ := IsBKTEnsemble_mono hE hsubσ
  have hPρ : IsParentEnsemble E (insert ρ (E.erase ρ |>.erase σ)) := by
    intro τ hτ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · subst τ
      exact hparentRefl ρ hρ
    · exact hparentRefl τ (hRsub hτ)
  have hPσ : IsParentEnsemble E (insert σ (E.erase ρ |>.erase σ)) := by
    intro τ hτ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · subst τ
      exact hparentRefl σ hσ
    · exact hparentRefl τ (hRsub hτ)
  have hdisj := hE.2 ρ hρ σ hσ hne
  have hEminus := insertMergedCharge_isBKTEnsemble E ρ σ (ρ - σ)
    hE hρ hσ (functionSupport_sub_of_disjoint ρ σ hdisj)
  have hEplus := insertMergedCharge_isBKTEnsemble E ρ σ (ρ + σ)
    hE hρ hσ (functionSupport_add_of_disjoint ρ σ hdisj)
  have hPminus : IsParentEnsemble E (insert (ρ - σ) (E.erase ρ |>.erase σ)) := by
    intro τ hτ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · subst τ
      exact compatible_sub_of_pair E hE ρ σ hρ hσ hne
    · exact hparentRefl τ (hRsub hτ)
  have hPplus : IsParentEnsemble E (insert (ρ + σ) (E.erase ρ |>.erase σ)) := by
    intro τ hτ
    rcases Finset.mem_insert.mp hτ with hτ | hτ
    · subst τ
      exact compatible_add_of_pair E hE ρ σ hρ hσ hne
    · exact hparentRefl τ (hRsub hτ)
  exact ⟨⟨hEρ, hPρ⟩, ⟨hEσ, hPσ⟩, ⟨hEminus, hPminus⟩, ⟨hEplus, hPplus⟩⟩

/-- A conflict is either absent, in which case the input is already a
strict `k`-ensemble, or it is witnessed by a distinct pair at distance at
most `2^k`. -/
theorem chargeEnsemble_conflict_or_kSeparated {L : ℕ}
    (boundary : SquareBoundary) (k : ℕ) (E : ChargeEnsemble L)
    (hE : IsBKTEnsemble E) :
    IsChargeScaleEnsemble boundary E (.ofNat k) ∨
      ∃ ρ ∈ E, ∃ σ ∈ E, ρ ≠ σ ∧
        densityDistance boundary L ρ σ ≤ 2 ^ k := by
  classical
  by_cases hsep : ∀ ρ ∈ E, ∀ σ ∈ E, ρ ≠ σ →
      2 ^ k < densityDistance boundary L ρ σ
  · exact Or.inl ⟨hE, hsep⟩
  · push Not at hsep
    obtain ⟨ρ, hρ, σ, hσ, hne, hdist⟩ := hsep
    exact Or.inr ⟨ρ, hρ, σ, hσ, hne, hdist⟩

/-- Every branch of one conflict rewrite has one fewer factor than the input.
This cardinality decrease is the termination measure for the finite iteration
in KP's Basic Lemma. -/
theorem pairRewriteBranches_card {L : ℕ} (E : ChargeEnsemble L)
    (hE : IsBKTEnsemble E) (ρ σ : ChargeDensity L)
    (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    let R := E.erase ρ |>.erase σ
    (insert ρ R).card = E.card - 1 ∧
      (insert σ R).card = E.card - 1 ∧
      (insert (ρ - σ) R).card = E.card - 1 ∧
      (insert (ρ + σ) R).card = E.card - 1 := by
  classical
  dsimp
  have hσerase : σ ∈ E.erase ρ := Finset.mem_erase.mpr ⟨hne.symm, hσ⟩
  have hρnot : ρ ∉ (E.erase ρ |>.erase σ) := by simp
  have hσnot : σ ∉ (E.erase ρ |>.erase σ) := by simp
  have hdisj := hE.2 ρ hρ σ hσ hne
  have hminusNot : ρ - σ ∉ (E.erase ρ |>.erase σ) := by
    exact mergedCharge_not_mem_pairRest E ρ σ (ρ - σ) hE hρ
      (functionSupport_sub_of_disjoint ρ σ hdisj)
  have hplusNot : ρ + σ ∉ (E.erase ρ |>.erase σ) := by
    exact mergedCharge_not_mem_pairRest E ρ σ (ρ + σ) hE hρ
      (functionSupport_add_of_disjoint ρ σ hdisj)
  have hRcard : (E.erase ρ |>.erase σ).card = E.card - 2 := by
    rw [Finset.card_erase_of_mem hσerase, Finset.card_erase_of_mem hρ]
    omega
  have hpairSub : ({ρ, σ} : Finset (ChargeDensity L)) ⊆ E := by
    intro τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl
    · exact hρ
    · exact hσ
  have hEcard : 2 ≤ E.card := by
    have hpaircard : ({ρ, σ} : Finset (ChargeDensity L)).card = 2 := by
      simp [hne]
    rw [← hpaircard]
    exact Finset.card_le_card hpairSub
  have hcard {τ : ChargeDensity L} (hτ : τ ∉ (E.erase ρ |>.erase σ)) :
      (insert τ (E.erase ρ |>.erase σ)).card = E.card - 1 := by
    rw [Finset.card_insert_of_notMem hτ, hRcard]
    omega
  exact ⟨hcard hρnot, hcard hσnot, hcard hminusNot, hcard hplusNot⟩

/-- The phase pairing is additive in the charge. -/
theorem chargePhase_add {L : ℕ} (ψ : (Fin L × Fin L) → ℝ)
    (ρ σ : ChargeDensity L) :
    chargePhase ψ (ρ + σ) = chargePhase ψ ρ + chargePhase ψ σ := by
  simp [chargePhase, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

/-- The phase pairing turns charge subtraction into real subtraction. -/
theorem chargePhase_sub {L : ℕ} (ψ : (Fin L × Fin L) → ℝ)
    (ρ σ : ChargeDensity L) :
    chargePhase ψ (ρ - σ) = chargePhase ψ ρ - chargePhase ψ σ := by
  simp [chargePhase, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]

/-- KP's four-term convex identity (4.12). -/
theorem charge_twoFactor_identity {L : ℕ} (ψ : (Fin L × Fin L) → ℝ)
    (ρ σ : ChargeDensity L) (K₁ K₂ : ℝ) :
    (1 + K₁ * Real.cos (chargePhase ψ ρ)) *
        (1 + K₂ * Real.cos (chargePhase ψ σ)) =
      (1 / 3 : ℝ) *
          (1 + 3 * K₁ * Real.cos (chargePhase ψ ρ)) +
        (1 / 3 : ℝ) *
          (1 + 3 * K₂ * Real.cos (chargePhase ψ σ)) +
        (1 / 6 : ℝ) *
          (1 + 3 * K₁ * K₂ * Real.cos (chargePhase ψ (ρ - σ))) +
        (1 / 6 : ℝ) *
          (1 + 3 * K₁ * K₂ * Real.cos (chargePhase ψ (ρ + σ))) := by
  rw [chargePhase_sub, chargePhase_add]
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- The four convex weights in (4.12) are positive and sum to one. -/
theorem charge_twoFactor_weights :
    (0 : ℝ) < 1 / 3 ∧ (0 : ℝ) < 1 / 6 ∧
      (1 / 3 : ℝ) + 1 / 3 + 1 / 6 + 1 / 6 = 1 := by
  norm_num

/-- One factor in a charge product. -/
noncomputable def chargeFactor {L : ℕ} (K : ChargeDensity L → ℝ)
    (ψ : (Fin L × Fin L) → ℝ) (ρ : ChargeDensity L) : ℝ :=
  1 + K ρ * Real.cos (chargePhase ψ ρ)

/-- The product indexed by a finite ensemble of charges. -/
noncomputable def chargeFactorProduct {L : ℕ} (E : ChargeEnsemble L)
    (K : ChargeDensity L → ℝ) (ψ : (Fin L × Fin L) → ℝ) : ℝ :=
  ∏ ρ ∈ E, chargeFactor K ψ ρ

/-- Applying (4.12) to one conflicting pair factors the rest of the product
unchanged and replaces the two selected factors by the four positive-weight
branches. -/
theorem chargeFactorProduct_rewrite_pair {L : ℕ} (E : ChargeEnsemble L)
    (K : ChargeDensity L → ℝ) (ψ : (Fin L × Fin L) → ℝ)
    (ρ σ : ChargeDensity L) (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    let R := E.erase ρ |>.erase σ
    chargeFactorProduct E K ψ =
      (∏ τ ∈ R, chargeFactor K ψ τ) *
        ((1 / 3 : ℝ) * (1 + 3 * K ρ * Real.cos (chargePhase ψ ρ)) +
          (1 / 3 : ℝ) * (1 + 3 * K σ * Real.cos (chargePhase ψ σ)) +
          (1 / 6 : ℝ) *
            (1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ - σ))) +
          (1 / 6 : ℝ) *
            (1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ + σ)))) := by
  classical
  dsimp
  have hσerase : σ ∈ E.erase ρ := Finset.mem_erase.mpr ⟨hne.symm, hσ⟩
  calc
    chargeFactorProduct E K ψ =
        (∏ τ ∈ E.erase ρ |>.erase σ, chargeFactor K ψ τ) *
          (chargeFactor K ψ σ * chargeFactor K ψ ρ) := by
      unfold chargeFactorProduct
      rw [← Finset.prod_erase_mul E (chargeFactor K ψ) hρ]
      rw [← Finset.prod_erase_mul (E.erase ρ) (chargeFactor K ψ) hσerase]
      ring
    _ = (∏ τ ∈ E.erase ρ |>.erase σ, chargeFactor K ψ τ) *
        (chargeFactor K ψ ρ * chargeFactor K ψ σ) := by ring
    _ = _ := by
      unfold chargeFactor
      rw [charge_twoFactor_identity]

/-- The same one-pair rewrite as an explicit four-branch convex sum. Each
branch retains the product over the untouched remainder and adds one factor. -/
theorem chargeFactorProduct_fourBranch_identity {L : ℕ} (E : ChargeEnsemble L)
    (K : ChargeDensity L → ℝ) (ψ : (Fin L × Fin L) → ℝ)
    (ρ σ : ChargeDensity L) (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    let R := E.erase ρ |>.erase σ
    chargeFactorProduct E K ψ =
      (1 / 3 : ℝ) *
          ((∏ τ ∈ R, chargeFactor K ψ τ) *
            (1 + 3 * K ρ * Real.cos (chargePhase ψ ρ))) +
        (1 / 3 : ℝ) *
          ((∏ τ ∈ R, chargeFactor K ψ τ) *
            (1 + 3 * K σ * Real.cos (chargePhase ψ σ))) +
        (1 / 6 : ℝ) *
          ((∏ τ ∈ R, chargeFactor K ψ τ) *
            (1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ - σ)))) +
        (1 / 6 : ℝ) *
          ((∏ τ ∈ R, chargeFactor K ψ τ) *
            (1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ + σ)))) := by
  classical
  dsimp
  rw [chargeFactorProduct_rewrite_pair E K ψ ρ σ hρ hσ hne]
  ring

/-- Coefficients on the four one-step replacement branches of (4.12). -/
def pairRewriteFirstCoefficient {L : ℕ} (K : ChargeDensity L → ℝ)
    (ρ : ChargeDensity L) : ChargeDensity L → ℝ := fun τ =>
  if τ = ρ then 3 * K ρ else K τ

def pairRewriteSecondCoefficient {L : ℕ} (K : ChargeDensity L → ℝ)
    (σ : ChargeDensity L) : ChargeDensity L → ℝ := fun τ =>
  if τ = σ then 3 * K σ else K τ

def pairRewriteDifferenceCoefficient {L : ℕ} (K : ChargeDensity L → ℝ)
    (ρ σ : ChargeDensity L) : ChargeDensity L → ℝ := fun τ =>
  if τ = ρ - σ then 3 * K ρ * K σ else K τ

def pairRewriteSumCoefficient {L : ℕ} (K : ChargeDensity L → ℝ)
    (ρ σ : ChargeDensity L) : ChargeDensity L → ℝ := fun τ =>
  if τ = ρ + σ then 3 * K ρ * K σ else K τ

/-- The factored terms in the local four-branch identity are exactly the
charge-factor products for the four replacement ensembles and coefficients. -/
theorem chargeFactorProduct_pairBranches_identity {L : ℕ}
    (E : ChargeEnsemble L) (hE : IsBKTEnsemble E)
    (K : ChargeDensity L → ℝ) (ψ : (Fin L × Fin L) → ℝ)
    (ρ σ : ChargeDensity L) (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    let R := E.erase ρ |>.erase σ
    chargeFactorProduct E K ψ =
      (1 / 3 : ℝ) * chargeFactorProduct (insert ρ R)
          (pairRewriteFirstCoefficient K ρ) ψ +
        (1 / 3 : ℝ) * chargeFactorProduct (insert σ R)
          (pairRewriteSecondCoefficient K σ) ψ +
        (1 / 6 : ℝ) * chargeFactorProduct (insert (ρ - σ) R)
          (pairRewriteDifferenceCoefficient K ρ σ) ψ +
        (1 / 6 : ℝ) * chargeFactorProduct (insert (ρ + σ) R)
          (pairRewriteSumCoefficient K ρ σ) ψ := by
  classical
  dsimp
  let R := E.erase ρ |>.erase σ
  have hρnot : ρ ∉ R := by simp [R]
  have hσnot : σ ∉ R := by simp [R]
  have hρneR (τ : ChargeDensity L) (hτ : τ ∈ R) : τ ≠ ρ := by
    dsimp [R] at hτ
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hτ).2).1
  have hσneR (τ : ChargeDensity L) (hτ : τ ∈ R) : τ ≠ σ := by
    exact (Finset.mem_erase.mp hτ).1
  have hminusNot : ρ - σ ∉ R :=
    mergedCharge_not_mem_pairRest E ρ σ (ρ - σ) hE hρ
      (functionSupport_sub_of_disjoint ρ σ (hE.2 ρ hρ σ hσ hne))
  have hplusNot : ρ + σ ∉ R :=
    mergedCharge_not_mem_pairRest E ρ σ (ρ + σ) hE hρ
      (functionSupport_add_of_disjoint ρ σ (hE.2 ρ hρ σ hσ hne))
  have hprod₁ : chargeFactorProduct (insert ρ R)
      (pairRewriteFirstCoefficient K ρ) ψ =
      (∏ τ ∈ R, chargeFactor K ψ τ) *
        (1 + 3 * K ρ * Real.cos (chargePhase ψ ρ)) := by
    unfold chargeFactorProduct
    rw [Finset.prod_insert hρnot]
    have hrest : (∏ τ ∈ R,
        chargeFactor (pairRewriteFirstCoefficient K ρ) ψ τ) =
          ∏ τ ∈ R, chargeFactor K ψ τ := by
      apply Finset.prod_congr rfl
      intro τ hτ
      simp [chargeFactor, pairRewriteFirstCoefficient, hρneR τ hτ]
    have hhead : chargeFactor (pairRewriteFirstCoefficient K ρ) ψ ρ =
        1 + 3 * K ρ * Real.cos (chargePhase ψ ρ) := by
      simp [chargeFactor, pairRewriteFirstCoefficient]
    rw [hhead, hrest]
    ring
  have hprod₂ : chargeFactorProduct (insert σ R)
      (pairRewriteSecondCoefficient K σ) ψ =
      (∏ τ ∈ R, chargeFactor K ψ τ) *
        (1 + 3 * K σ * Real.cos (chargePhase ψ σ)) := by
    unfold chargeFactorProduct
    rw [Finset.prod_insert hσnot]
    have hrest : (∏ τ ∈ R,
        chargeFactor (pairRewriteSecondCoefficient K σ) ψ τ) =
          ∏ τ ∈ R, chargeFactor K ψ τ := by
      apply Finset.prod_congr rfl
      intro τ hτ
      simp [chargeFactor, pairRewriteSecondCoefficient, hσneR τ hτ]
    have hhead : chargeFactor (pairRewriteSecondCoefficient K σ) ψ σ =
        1 + 3 * K σ * Real.cos (chargePhase ψ σ) := by
      simp [chargeFactor, pairRewriteSecondCoefficient]
    rw [hhead, hrest]
    ring
  have hprodMinus : chargeFactorProduct (insert (ρ - σ) R)
      (pairRewriteDifferenceCoefficient K ρ σ) ψ =
      (∏ τ ∈ R, chargeFactor K ψ τ) *
        (1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ - σ))) := by
    unfold chargeFactorProduct
    rw [Finset.prod_insert hminusNot]
    have hrest : (∏ τ ∈ R,
        chargeFactor (pairRewriteDifferenceCoefficient K ρ σ) ψ τ) =
          ∏ τ ∈ R, chargeFactor K ψ τ := by
      apply Finset.prod_congr rfl
      intro τ hτ
      have hτne : τ ≠ ρ - σ := by
        intro hEq
        exact hminusNot (hEq.symm ▸ hτ)
      simp [chargeFactor, pairRewriteDifferenceCoefficient, hτne]
    have hhead : chargeFactor (pairRewriteDifferenceCoefficient K ρ σ) ψ (ρ - σ) =
        1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ - σ)) := by
      simp [chargeFactor, pairRewriteDifferenceCoefficient]
    rw [hhead, hrest]
    ring
  have hprodPlus : chargeFactorProduct (insert (ρ + σ) R)
      (pairRewriteSumCoefficient K ρ σ) ψ =
      (∏ τ ∈ R, chargeFactor K ψ τ) *
        (1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ + σ))) := by
    unfold chargeFactorProduct
    rw [Finset.prod_insert hplusNot]
    have hrest : (∏ τ ∈ R,
        chargeFactor (pairRewriteSumCoefficient K ρ σ) ψ τ) =
          ∏ τ ∈ R, chargeFactor K ψ τ := by
      apply Finset.prod_congr rfl
      intro τ hτ
      have hτne : τ ≠ ρ + σ := by
        intro hEq
        exact hplusNot (hEq.symm ▸ hτ)
      simp [chargeFactor, pairRewriteSumCoefficient, hτne]
    have hhead : chargeFactor (pairRewriteSumCoefficient K ρ σ) ψ (ρ + σ) =
        1 + 3 * K ρ * K σ * Real.cos (chargePhase ψ (ρ + σ)) := by
      simp [chargeFactor, pairRewriteSumCoefficient]
    rw [hhead, hrest]
    ring
  have hmain := chargeFactorProduct_fourBranch_identity E K ψ ρ σ hρ hσ hne
  rw [hmain, ← hprod₁, ← hprod₂, ← hprodMinus, ← hprodPlus]

end FroehlichSpencer.BKT

end
