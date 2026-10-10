/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.CompactRealFactor
public import FroehlichSpencer.BKT.Clock.Compact.MarkedBranch
import Mathlib.Tactic

/-!
# The marked branch on the compact Villain law

The Villain analogue of the law-dependent part of `Clock/Compact/MarkedBranch.lean` (FS81
(7.7)–(7.8) for one mixture branch). The composite wave, the wave selection and the composite gain
are the cosine ones: they depend only on the cosine clock cost, which also bounds the Villain shift.

* `abs_villainMarkedTerm_le`, `integral_villainMarkedTerm_eq_zero_of_charged`,
  `villain_branch_comparison`;
* **`abs_villainMarkedBranch_le`**: the marked branch bound under the compact Villain law.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory
open FroehlichSpencer.BKT
open SpinWaves SpinWaves.P47 Reduction
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked

section Term

variable (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]

variable {boundary}

/-- **The bound on one marked term under the compact Villain law** (FS81 (5.31)–(5.34), §7.1). For a
neutral cluster `C` of a KP ensemble `N` and `T ⊆ C`, the dipole mark at the clock frequency
`ξ/n` (`0 < ξ < n`), the renormalized activities of the neutral members at most one, and
`28 λ ≤ n`, `8192 β λ ≤ η n²`:
`|∫ cos⟨φ, (ξ/n)ϱ₀ + ϱ^𝒩⟩ ∏_{rem(C)} (1 + K cos) dμ| ≤ e^{-G(C,T)} ∫ ∏_{rem(C)} (1 + K cos) dμ`
with the clock composite gain `G`. The remainder is renormalized with the clock wave selection
of the extended ensemble `rem(C) ∪ {p}`, the composite with `exists_clockCompositeWave`. -/
theorem abs_villainMarkedTerm_le (hL : 1 < L) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {g : ChargeDensity L → ℝ}
    (h24 : ClockWaveSelection boundary Λ centerOf β n g)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (hNc : NeutralSplitsAreCharged boundary L N) (K : ChargeDensity L → ℝ)
    (hz : ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      g m ≤ translationEnergy (clockShiftCost β n) (gradLinear Λ) a (fun j => (m j : ℝ)) →
      |K m| * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a
        (fun j => (m j : ℝ))) ≤ 1)
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℕ} (hξ0 : 0 < ξ) (hξn : ξ < n) {η : ℝ}
    (hη : 0 < η) (hηξ : η ≤ dipoleGap ((ξ : ℝ) / n)) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlamn : 28 * lam ≤ n) (hcost : 8192 * β * lam ≤ η * n ^ 2)
    {C : Finset (ChargeDensity L)}
    (hC : C ∈ markedClusters boundary L (dipoleMark o x) N) (hCn : ∀ m ∈ C, ∑ j, m j = 0)
    {T : Finset (ChargeDensity L)} (hT : T ⊆ C) :
    |∫ φ, Real.cos (∑ j, φ j * markedDensity ((ξ : ℝ) / n) (dipoleMark o x) (satellite L C T) j) *
        ∏ m ∈ markedRemainder boundary L (dipoleMark o x) N C,
          (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ| ≤
      Real.exp (-clockCompositeGain boundary (by omega) ((ξ : ℝ) / n) η lam (dipoleMark o x)
          C T) *
        ∫ φ, ∏ m ∈ markedRemainder boundary L (dipoleMark o x) N C,
          (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ := by
  classical
  have hL0 : 0 < L := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set ξ' : ℝ := (ξ : ℝ) / n with hξ'
  have hξ'0 : 0 < ξ' := div_pos (by exact_mod_cast hξ0) hn'
  have hξ'1 : ξ' < 1 := (div_lt_one hn').2 (by exact_mod_cast hξn)
  set ρ₀ := dipoleMark o x with hρ₀
  set σ := satellite L C T with hσ
  set ρ := markedDensity ξ' ρ₀ σ with hρdef
  set p := markedProxy ρ₀ C T with hpdef
  set R := markedRemainder boundary L ρ₀ N C with hR
  set N' := markedExtension (boundary := boundary) ρ₀ N C T with hN'
  set μ := villainCompactLaw β n Λ with hμ
  have := isProbabilityMeasure_villainCompactLaw Λ hβ hn'
  obtain ⟨hE, hEa, hEb, hEc, hpN₀, hpR, hsuppP⟩ :=
    markedExtension_kp (boundary := boundary) hL hox hens hNa hNb hNc hC hCn hT
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hRN : R ⊆ N := remainder_subset _ _
  have hdisjC : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m') :=
    fun m hm m' hm' hne => hens.2 m (hCN hm) m' (hCN hm') hne
  have hρsupp : ∀ j, ρ j ≠ 0 ↔ p j ≠ 0 :=
    markedProxy_ne_zero_iff_dipole hox hξ'0 hξ'1 hT hdisjC
  have hρn : ∑ j, ρ j = 0 := by
    have h1 : ∑ j, (ρ₀ j : ℝ) = 0 := by exact_mod_cast sum_univ_dipoleMark o x
    have h2 : ∑ j, (σ j : ℝ) = 0 := by exact_mod_cast sum_satellite hCn hT
    simp only [hρdef, markedDensity, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2,
      mul_zero, add_zero]
  have hρc : IsClockCompatible (n : ℝ) ρ := isClockCompatible_markedDensity hn ξ ρ₀ σ
  -- the patch charges and the site values of the composite
  have hgap : ∀ (k : {k : ℕ // 1 ≤ k}) (s : Finset (Fin L × Fin L)),
      s ∈ separatedSquares boundary L p k (sharedMinimumSquareCover boundary L p hL0 k) →
        η ≤ |∑ j ∈ s, ρ j| := by
    intro k s hs
    have hsP : chargeSupport p = chargeSupport (supportProxy (markedSupport L ρ₀ C)) := by
      rw [hsuppP, chargeSupport_supportProxy]
    have hcovX := isMinimumSquareCover_congr hsP
      (sharedMinimumSquareCover boundary L p hL0 k).property
    have hs' : s ∈ separatedSquares boundary L (supportProxy (markedSupport L ρ₀ C)) k
        ⟨(sharedMinimumSquareCover boundary L p hL0 k).val, hcovX⟩ := by
      unfold separatedSquares at hs ⊢
      exact hs
    have h := dipole_patchCharge_ge hL hox ξ' hens hNb hNc hC hCn hT k _ hs'
    have hsc : setCharge ρ (markedSupport L ρ₀ C ∩ s) = ∑ j ∈ s, ρ j := by
      unfold setCharge
      refine Finset.sum_subset Finset.inter_subset_right fun j hjs hjn => ?_
      by_contra hj
      have hjX : j ∈ markedSupport L ρ₀ C := by
        rw [← hsuppP]
        exact mem_chargeSupport'.2 ((hρsupp j).1 hj)
      exact hjn (Finset.mem_inter.2 ⟨hjX, hjs⟩)
    rw [hsc] at h
    exact hηξ.trans h
  have hsite : ∀ j, ρ j ≠ 0 → η ≤ |ρ j| := by
    intro j hj
    have hne : setCharge (markedDensity ξ' (dipoleMark o x) σ) {j} ≠ 0 := by
      simpa [setCharge] using hj
    have h := dipole_le_abs_setCharge o x ξ' σ {j} hne
    simp only [setCharge, Finset.sum_singleton] at h
    exact hηξ.trans h
  -- the remainder's waves (the clock wave selection of the extended ensemble) and the composite
  have hw' := h24 N' hE hEa hEb hEc
  choose! a' ha' using hw'
  obtain ⟨a₀, h0c, h0s, h0E⟩ := exists_clockCompositeWave boundary hL Λ hΛ hdist B h46
    centerOf hcenter N' hE hEa hEb hEc p hpN₀ ρ hρsupp hη hsite hgap hβ.le hn' hlam hlamn hcost
  set N₀ := neutralPart N' with hN₀
  set A : ChargeDensity L → Fin L × Fin L → ℝ := fun ϱ => if ϱ = p then a₀ else a' ϱ with hA
  have hAp : A p = a₀ := by simp [hA]
  have hAm : ∀ ϱ, ϱ ≠ p → A ϱ = a' ϱ := fun ϱ h => by simp [hA, h]
  have hAc : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ Λ.comparableDensities N₀ ϱ,
      ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), A ϱ j = c := by
    intro ϱ hϱ ϱ' hϱ'
    by_cases h : ϱ = p
    · subst h
      rw [hAp]
      exact h0c ϱ' hϱ'
    · rw [hAm ϱ h]
      exact (ha' ϱ hϱ).1 ϱ' hϱ'
  have hAs : ∀ ϱ ∈ N₀, Function.support (A ϱ) ⊆ Λ.densityDomain ϱ (centerOf ϱ) := by
    intro ϱ hϱ
    by_cases h : ϱ = p
    · subst h
      rw [hAp]
      exact h0s
    · rw [hAm ϱ h]
      exact (ha' ϱ hϱ).2.1
  have hdisjA := grad_disjoint_of_spinWave_clauses Λ N₀ centerOf A hAc hAs
  have horthA : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' → ∑ j, A ϱ j * (ϱ' j : ℝ) = 0 := by
    intro ϱ hϱ ϱ' hϱ' hne
    exact pairing_eq_zero_of_waveClauses Λ hΛ hdist centerOf hcenter hE hEb A hAc hAs hϱ hϱ' hne
      (fun j => (ϱ' j : ℝ)) (fun j hj => by exact_mod_cast hj)
      (by exact_mod_cast (mem_neutralPart.mp hϱ').2)
  -- the neutral remainder inside the extended ensemble
  set R₀ := neutralPart R with hR₀
  have hR₀N₀ : ∀ m ∈ R₀, m ∈ N₀ := fun m hm => by
    obtain ⟨hmR, hmn⟩ := mem_neutralPart.mp hm
    exact mem_neutralPart.mpr ⟨Finset.mem_insert_of_mem hmR, hmn⟩
  have hR₀p : ∀ m ∈ R₀, m ≠ p := fun m hm h => hpR (by
    have hmR := (mem_neutralPart.mp hm).1
    rw [h] at hmR
    exact hmR)
  have hreal : ∀ m ∈ R₀, ∑ j, A m j * ρ j = 0 := fun m hm =>
    pairing_eq_zero_of_waveClauses Λ hΛ hdist centerOf hcenter hE hEb A hAc hAs (hR₀N₀ m hm) hpN₀
      (hR₀p m hm) ρ (fun j hj => (hρsupp j).1 hj) hρn
  -- the renormalized activities of the remainder are at most one
  set z : ChargeDensity L → ℝ := fun m => K m * Real.exp (-translationEnergy (clockShiftCost β n)
    (gradLinear Λ) (A m) (fun j => (m j : ℝ))) with hzdef
  have hzle : ∀ m ∈ R₀, |z m| ≤ 1 := by
    intro m hm
    obtain ⟨hmR, hmn⟩ := mem_neutralPart.mp hm
    rw [hzdef, abs_mul, Real.abs_exp, hAm _ (hR₀p m hm)]
    exact hz m (hRN hmR) hmn _ (ha' m (hR₀N₀ m hm)).2.2
  -- remove the non-neutral member of the remainder
  have hRa : ∀ ϱ₁ ∈ R, ∀ ϱ₂ ∈ R, ∑ j, ϱ₁ j ≠ 0 → ∑ j, ϱ₂ j ≠ 0 → ϱ₁ = ϱ₂ :=
    fun ϱ₁ h₁ ϱ₂ h₂ => hNa ϱ₁ (hRN h₁) ϱ₂ (hRN h₂)
  have hJ0 := villainCompactLaw_integral_cos_mul_prod_eq_neutralPart hn hβ Λ R hRa K ρ hρc hρn
  have hZ0 : ∫ φ, ∏ m ∈ R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∫ φ, ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    have h := villainCompactLaw_integral_cos_mul_prod_eq_neutralPart hn hβ Λ R hRa K (fun _ => 0)
      (fun j => ⟨0, by simp⟩) (by simp)
    simpa using h
  rw [hJ0, hZ0]
  -- the translations
  set ι := {m // m ∈ R₀}
  set f : Option ι → (Fin L × Fin L → ℝ) → ℝ := fun o φ =>
    villainF β n (gradLinear Λ (Option.elim o a₀ fun m => A m.val)) (gradLinear Λ φ)
      (∑ j, φ j * Option.elim o ρ (fun m j => ((m.val j : ℤ) : ℝ)) j + 0) with hf
  have hfc : ∀ o, Continuous (f o) := fun o =>
    continuous_villainF hβ hn' Λ _ _ (by fun_prop)
  have hfb : ∀ o φ, |f o φ| ≤ 1 := fun o φ => abs_villainF_le_one hβ hn' _ _ _
  have hcompO : ∀ o : Option ι,
      IsClockCompatible (n : ℝ) (Option.elim o ρ (fun m j => ((m.val j : ℤ) : ℝ))) := by
    intro o
    rcases o with _ | m
    · exact hρc
    · exact isClockCompatible_intCast n _
  have horthO : ∀ o o' : Option ι, o ≠ o' →
      ∑ j, Option.elim o a₀ (fun m => A m.val) j *
        Option.elim o' ρ (fun m j => ((m.val j : ℤ) : ℝ)) j = 0 := by
    intro o o' hoo'
    rcases o with _ | m <;> rcases o' with _ | m'
    · exact absurd rfl hoo'
    · simp only [Option.elim]
      rw [← hAp]
      exact horthA p hpN₀ m'.val (hR₀N₀ _ m'.property) (Ne.symm (hR₀p _ m'.property))
    · exact hreal m.val m.property
    · simp only [Option.elim]
      exact horthA m.val (hR₀N₀ _ m.property) m'.val (hR₀N₀ _ m'.property)
        fun h => hoo' (congrArg some (Subtype.ext h))
  have hdisjO : ∀ o o' : Option ι, o ≠ o' → ∀ e,
      Λ.grad (Option.elim o a₀ fun m => A m.val) e = 0 ∨
        Λ.grad (Option.elim o' a₀ fun m => A m.val) e = 0 := by
    intro o o' hoo' e
    rcases o with _ | m <;> rcases o' with _ | m'
    · exact absurd rfl hoo'
    · simp only [Option.elim]
      rw [← hAp]
      exact hdisjA p hpN₀ m'.val (hR₀N₀ _ m'.property) (Ne.symm (hR₀p _ m'.property)) e
    · simp only [Option.elim]
      rw [← hAp]
      exact hdisjA m.val (hR₀N₀ _ m.property) p hpN₀ (hR₀p _ m.property) e
    · simp only [Option.elim]
      exact hdisjA m.val (hR₀N₀ _ m.property) m'.val (hR₀N₀ _ m'.property)
        (fun h => hoo' (congrArg some (Subtype.ext h))) e
  have htrO := integral_prod_add_mul_cos_villainCompactLaw_real hn' hβ Λ
    (fun o : Option ι => Option.elim o ρ (fun m j => ((m.val j : ℤ) : ℝ))) hcompO
    (fun o => Option.elim o 0 fun _ => 1) (fun o => Option.elim o 1 fun m => K m.val)
    (fun _ => 0) (fun o => Option.elim o a₀ fun m => A m.val) horthO hdisjO
  have htrR := integral_prod_add_mul_cos_villainCompactLaw_real hn' hβ Λ
    (fun m : ι => fun j => ((m.val j : ℤ) : ℝ)) (fun m => isClockCompatible_intCast n _)
    (fun _ => 1) (fun m => K m.val) (fun _ => 0) (fun m => A m.val)
    (fun m m' hne => horthO (some m) (some m') (fun h => hne (Option.some_injective _ h)))
    (fun m m' hne => hdisjO (some m) (some m') (fun h => hne (Option.some_injective _ h)))
  -- rewrite both sides
  have hJ : ∫ φ, Real.cos (∑ j, φ j * ρ j) *
      ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a₀ ρ) *
        ∫ φ, f none φ * ∏ m : ι, (1 + z m.val * f (some m) φ) ∂μ := by
    have h1 : ∀ φ : Fin L × Fin L → ℝ, Real.cos (∑ j, φ j * ρ j) *
        ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) =
        ∏ o : Option ι, (Option.elim o 0 (fun _ => 1) + Option.elim o 1 (fun m => K m.val) *
          Real.cos (∑ j, φ j * Option.elim o ρ (fun m j => ((m.val j : ℤ) : ℝ)) j + 0)) := by
      intro φ
      rw [Fintype.prod_option]
      simp only [Option.elim, zero_add, one_mul, add_zero]
      rw [← Finset.prod_coe_sort R₀]
    simp_rw [h1]
    rw [htrO, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only
    rw [Fintype.prod_option]
    simp only [Option.elim, zero_add, one_mul, hf, hzdef]
    ring
  have hZ : ∫ φ, ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∫ φ, ∏ m : ι, (1 + z m.val * f (some m) φ) ∂μ := by
    have h1 : ∀ φ : Fin L × Fin L → ℝ,
        ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) =
        ∏ m : ι, (1 + K m.val * Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)) := by
      intro φ
      simp only [add_zero]
      rw [← Finset.prod_coe_sort R₀]
    simp_rw [h1]
    rw [htrR]
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only [hf, hzdef, Option.elim]
  rw [hJ, hZ, abs_mul, Real.abs_exp]
  have hbound := abs_integral_mul_prod_le μ (Finset.univ : Finset ι) (fun m => z m.val)
    (fun m _ => hzle m.val m.property) (f none) (hfb none) (fun m => f (some m))
    (fun m => hfc (some m)) (fun m => hfb (some m))
  have hexp : Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a₀ ρ) ≤
      Real.exp (-clockCompositeGain boundary hL0 ξ' η lam ρ₀ C T) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    unfold clockCompositeGain
    exact h0E
  have hI0 : 0 ≤ ∫ φ, ∏ m : ι, (1 + z m.val * f (some m) φ) ∂μ :=
    integral_nonneg fun φ => prod_one_add_mul_nonneg _ _ _ (fun m _ => hzle m.val m.property)
      fun m _ => hfb (some m) φ
  calc Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a₀ ρ) *
        |∫ φ, f none φ * ∏ m : ι, (1 + z m.val * f (some m) φ) ∂μ|
      ≤ Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a₀ ρ) *
          ∫ φ, ∏ m : ι, (1 + z m.val * f (some m) φ) ∂μ :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp hI0

end Term

section Charged

variable {E : Type} [Fintype E]

/-- **A cluster with a charged member contributes nothing under the compact Villain law**: the satellite then
carries the nonzero integer charge `±Q(ϱ_c)`, the remainder is neutral, and the compact
constant-mode vanishing (`integral_character_mul_prod_villainCompactLaw_eq_zero`) kills both characters of
the composite cosine. -/
theorem integral_villainMarkedTerm_eq_zero_of_charged {L : ℕ} {boundary : SquareBoundary}
    (Λ : Multigraph (Fin L × Fin L) E) {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n)
    {N : Finset (ChargeDensity L)} (hNa : AtMostOneNonNeutral N)
    (K : ChargeDensity L → ℝ) {ρ₀ : ChargeDensity L} (hρ₀ : ∑ j, ρ₀ j = 0) (ξ : ℕ)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L ρ₀ N)
    (hCq : ¬ ∀ m ∈ C, ∑ j, m j = 0) {T : Finset (ChargeDensity L)} (hT : T ⊆ C) :
    ∫ φ, Real.cos (∑ j, φ j * markedDensity ((ξ : ℝ) / n) ρ₀ (satellite L C T) j) *
        ∏ m ∈ markedRemainder boundary L ρ₀ N C,
          (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ = 0 := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := isProbabilityMeasure_villainCompactLaw Λ hβ hn'
  push Not at hCq
  obtain ⟨mc, hmcC, hmcq⟩ := hCq
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  set R := markedRemainder boundary L ρ₀ N C with hR
  have hRN : R ⊆ N := remainder_subset _ _
  have honly : ∀ m ∈ N, ∑ j, m j ≠ 0 → m = mc := fun m hm hq =>
    hNa m hm mc (hCN hmcC) hq hmcq
  have hRn : ∀ m ∈ R, ∑ j, m j = 0 := by
    intro m hm
    by_contra hq
    have hmc := honly m (hRN hm) hq
    exact Finset.disjoint_left.1 (disjoint_remainder (adj := MarkAdjacent boundary L ρ₀) N C)
      (hmc ▸ hmcC) hm
  have hQ : ∀ U ⊆ C, ∑ m ∈ U, ∑ j, m j = if mc ∈ U then ∑ j, mc j else 0 := by
    intro U hU
    split_ifs with h
    · refine Finset.sum_eq_single_of_mem mc h fun m hm hne => ?_
      by_contra hq
      exact hne (honly m (hCN (hU hm)) hq)
    · refine Finset.sum_eq_zero fun m hm => ?_
      by_contra hq
      exact h (honly m (hCN (hU hm)) hq ▸ hm)
  have hσ : ∑ j, satellite L C T j ≠ 0 := by
    unfold satellite
    rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := C \ T),
      hQ T hT, hQ (C \ T) Finset.sdiff_subset]
    by_cases hmT : mc ∈ T
    · rw [ite_eq_left hmT, ite_eq_right fun h => (Finset.mem_sdiff.1 h).2 hmT, sub_zero]
      exact hmcq
    · rw [ite_eq_right hmT, ite_eq_left (Finset.mem_sdiff.2 ⟨hmcC, hmT⟩), zero_sub, neg_ne_zero]
      exact hmcq
  set ρ := markedDensity ((ξ : ℝ) / n) ρ₀ (satellite L C T) with hρdef
  have hρQ : ∑ j, ρ j ≠ 0 := by
    have h1 : ∑ j, (ρ₀ j : ℝ) = 0 := by exact_mod_cast hρ₀
    simp only [hρdef, markedDensity, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_zero,
      zero_add]
    exact_mod_cast hσ
  have hρc : IsClockCompatible (n : ℝ) ρ := isClockCompatible_markedDensity hn ξ ρ₀ _
  have hρnc : IsClockCompatible (n : ℝ) (fun j => -ρ j) := by
    intro j
    obtain ⟨k, hk⟩ := hρc j
    exact ⟨-k, by push_cast; rw [← hk]; ring⟩
  set ι := {m // m ∈ R}
  have hprod : ∀ φ : Fin L × Fin L → ℝ, ∏ m ∈ R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) =
      ∏ m : ι, (1 + K m.val * Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)) := by
    intro φ
    simp only [add_zero]
    rw [← Finset.prod_coe_sort R]
  have hz : ∀ τ : Fin L × Fin L → ℝ, IsClockCompatible (n : ℝ) τ → ∑ j, τ j ≠ 0 →
      ∫ φ, Reduction.gffCharacter τ φ * ((∏ m : ι, (1 + K m.val *
        Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)) : ℝ) : ℂ) ∂villainCompactLaw β n Λ = 0 :=
    fun τ hτc hτ => integral_character_mul_prod_villainCompactLaw_eq_zero hn' hβ Λ τ hτc hτ
      (fun m : ι => fun j => ((m.val j : ℤ) : ℝ)) (fun m => isClockCompatible_intCast n _)
      (fun m => by exact_mod_cast hRn m.val m.property) _ _ _
  have hz₁ := hz ρ hρc hρQ
  have hz₂ := hz (fun j => -ρ j) hρnc (by rw [Finset.sum_neg_distrib, neg_ne_zero]; exact hρQ)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_zero]
  have hpt : ∀ φ : Fin L × Fin L → ℝ, ((Real.cos (∑ j, φ j * ρ j) *
      ∏ m ∈ R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * (Reduction.gffCharacter ρ φ * ((∏ m : ι, (1 + K m.val *
        Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)) : ℝ) : ℂ) +
        Reduction.gffCharacter (fun j => -ρ j) φ * ((∏ m : ι, (1 + K m.val *
          Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)) : ℝ) : ℂ)) := by
    intro φ
    have hc1 : Reduction.gffCharacter ρ φ =
        Complex.exp (Complex.I * ((∑ j, φ j * ρ j : ℝ) : ℂ)) := by
      unfold Reduction.gffCharacter; congr 1; push_cast; ring
    have hc2 : Reduction.gffCharacter (fun j => -ρ j) φ =
        Complex.exp (-(Complex.I * ((∑ j, φ j * ρ j : ℝ) : ℂ))) := by
      unfold Reduction.gffCharacter; congr 1
      push_cast
      rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hcos : ((Real.cos (∑ j, φ j * ρ j) : ℝ) : ℂ) =
        (Reduction.gffCharacter ρ φ + Reduction.gffCharacter (fun j => -ρ j) φ) / 2 := by
      rw [hc1, hc2, Complex.ofReal_cos, Complex.cos]
      generalize ((∑ j, φ j * ρ j : ℝ) : ℂ) = θ₀
      congr 2 <;> congr 1 <;> ring
    rw [hprod]
    generalize Real.cos (∑ j, φ j * ρ j) = c at hcos ⊢
    generalize Reduction.gffCharacter ρ φ = χ₁ at hcos ⊢
    generalize Reduction.gffCharacter (fun j => -ρ j) φ = χ₂ at hcos ⊢
    generalize (∏ m : ι, (1 + K m.val * Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0))) = P
    push_cast
    rw [hcos]
    ring
  simp_rw [hpt]
  have hb : ∀ τ : Fin L × Fin L → ℝ, Integrable (fun φ => Reduction.gffCharacter τ φ *
      ((∏ m : ι, (1 + K m.val * Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)) : ℝ) : ℂ))
      (villainCompactLaw β n Λ) := by
    intro τ
    refine Integrable.of_bound (((Reduction.continuous_gffCharacter τ).mul
      (Complex.continuous_ofReal.comp (continuous_finsetProd _ fun m _ =>
        by fun_prop))).aestronglyMeasurable) (∏ m : ι, (1 + |K m.val|))
      (ae_of_all _ fun φ => ?_)
    rw [norm_mul, Reduction.norm_gffCharacter, one_mul, Complex.norm_real, Real.norm_eq_abs,
      Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun m _ => ?_
    calc |1 + K m.val * Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)|
        ≤ |(1 : ℝ)| + |K m.val * Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)| :=
          abs_add_le _ _
      _ ≤ 1 + |K m.val| := by
        rw [abs_one, abs_mul]
        have := Real.abs_cos_le_one (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)
        nlinarith [abs_nonneg (K m.val)]
  rw [integral_const_mul, integral_add (hb ρ) (hb _), hz₁, hz₂]
  simp

end Charged

section Branch

variable {boundary : SquareBoundary} {L : ℕ} {E : Type} [Fintype E]

/-- **The branch normalizer and its comparison under the compact Villain law** (FS81 (5.35)): with the
clock wave selection of the branch ensemble `N` and renormalized activities `|z_m| ≤ θ_m < 1`,
`Z_N = ∫ ∏_N (1 + K cos) dμ > 0`, and for every subfamily `S ⊆ N`,
`∏_{m ∈ N₀ ∖ S₀} (1 - θ_m) · ∫ ∏_S (1 + K cos) dμ ≤ Z_N`. -/
theorem villain_branch_comparison (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {g : ChargeDensity L → ℝ}
    (h24 : ClockWaveSelection boundary Λ centerOf β n g)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (hNc : NeutralSplitsAreCharged boundary L N) (K θ : ChargeDensity L → ℝ)
    (hθ : ∀ m ∈ N, θ m < 1)
    (hz : ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      g m ≤ translationEnergy (clockShiftCost β n) (gradLinear Λ) a (fun j => (m j : ℝ)) →
      |K m| * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a
        (fun j => (m j : ℝ))) ≤ θ m) :
    0 < ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ ∧
      ∀ S ⊆ N, (∏ m ∈ neutralPart N \ neutralPart S, (1 - θ m)) *
          ∫ φ, ∏ m ∈ S, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ ≤
        ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set μ := villainCompactLaw β n Λ with hμ
  have := isProbabilityMeasure_villainCompactLaw Λ hβ hn'
  have hw := h24 N hens hNa hNb hNc
  choose! a ha using hw
  set N₀ := neutralPart N with hN₀
  have hmem : ∀ ϱ ∈ N₀, ϱ ∈ N ∧ ∑ j, ϱ j = 0 := fun ϱ hϱ => mem_neutralPart.mp hϱ
  have hdisjA := grad_disjoint_of_spinWave_clauses Λ N₀ centerOf a (fun ϱ hϱ => (ha ϱ hϱ).1)
    (fun ϱ hϱ => (ha ϱ hϱ).2.1)
  have horthA : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' → ∑ j, a ϱ j * (ϱ' j : ℝ) = 0 := by
    intro ϱ hϱ ϱ' hϱ' hne
    exact pairing_eq_zero_of_waveClauses Λ hΛ hdist centerOf hcenter hens hNb a
      (fun ϱ hϱ => (ha ϱ hϱ).1) (fun ϱ hϱ => (ha ϱ hϱ).2.1) hϱ hϱ' hne
      (fun j => (ϱ' j : ℝ)) (fun j hj => by exact_mod_cast hj)
      (by exact_mod_cast (hmem ϱ' hϱ').2)
  set z : ChargeDensity L → ℝ := fun m => K m * Real.exp (-translationEnergy
    (clockShiftCost β n) (gradLinear Λ) (a m) (fun j => (m j : ℝ))) with hzdef
  have hzθ : ∀ m ∈ N₀, |z m| ≤ θ m := by
    intro m hm
    rw [hzdef, abs_mul, Real.abs_exp]
    exact hz m (hmem m hm).1 (hmem m hm).2 _ (ha m hm).2.2
  have hz1 : ∀ m ∈ N₀, |z m| ≤ 1 := fun m hm => (hzθ m hm).trans (hθ m (hmem m hm).1).le
  set f : ChargeDensity L → (Fin L × Fin L → ℝ) → ℝ := fun m φ =>
    villainF β n (gradLinear Λ (a m)) (gradLinear Λ φ) (∑ j, φ j * (m j : ℝ) + 0) with hf
  have hfc : ∀ m, Continuous (f m) := fun m => continuous_villainF hβ hn' Λ _ _ (by fun_prop)
  have hfb : ∀ m φ, |f m φ| ≤ 1 := fun m φ => abs_villainF_le_one hβ hn' _ _ _
  have htr : ∀ S ⊆ N, ∫ φ, ∏ m ∈ S, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∫ φ, ∏ m ∈ neutralPart S, (1 + z m * f m φ) ∂μ := by
    intro S hS
    have hSa : ∀ ϱ₁ ∈ S, ∀ ϱ₂ ∈ S, ∑ j, ϱ₁ j ≠ 0 → ∑ j, ϱ₂ j ≠ 0 → ϱ₁ = ϱ₂ :=
      fun ϱ₁ h₁ ϱ₂ h₂ => hNa ϱ₁ (hS h₁) ϱ₂ (hS h₂)
    have h0 := villainCompactLaw_integral_cos_mul_prod_eq_neutralPart hn hβ Λ S hSa K (fun _ => 0)
      (fun j => ⟨0, by simp⟩) (by simp)
    simp only [mul_zero, Finset.sum_const_zero, Real.cos_zero, one_mul] at h0
    rw [h0]
    have hS₀ : ∀ m ∈ neutralPart S, m ∈ N₀ := fun m hm => by
      obtain ⟨hmS, hmn⟩ := mem_neutralPart.mp hm
      exact mem_neutralPart.mpr ⟨hS hmS, hmn⟩
    set ι := {m // m ∈ neutralPart S}
    have h1 := integral_prod_add_mul_cos_villainCompactLaw_real hn' hβ Λ
      (fun m : ι => fun j => ((m.val j : ℤ) : ℝ)) (fun m => isClockCompatible_intCast n _)
      (fun _ => 1) (fun m => K m.val) (fun _ => 0) (fun m => a m.val)
      (fun m m' hne => horthA m.val (hS₀ _ m.property) m'.val (hS₀ _ m'.property)
        fun h => hne (Subtype.ext h))
      (fun m m' hne => hdisjA m.val (hS₀ _ m.property) m'.val (hS₀ _ m'.property)
        (fun h => hne (Subtype.ext h)))
    have hl : ∀ φ : Fin L × Fin L → ℝ,
        ∏ m ∈ neutralPart S, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) =
        ∏ m : ι, (1 + K m.val * Real.cos (∑ j, φ j * ((m.val j : ℤ) : ℝ) + 0)) := by
      intro φ
      simp only [add_zero]
      rw [← Finset.prod_coe_sort (neutralPart S)]
    simp_rw [hl]
    rw [h1]
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only [hf, hzdef]
    rw [← Finset.prod_coe_sort (neutralPart S)]
  have hNN := htr N (Finset.Subset.refl N)
  refine ⟨?_, fun S hS => ?_⟩
  · rw [hNN]
    exact integral_prod_one_add_mul_pos μ N₀ z
      (fun m hm => (hzθ m hm).trans_lt (hθ m (hmem m hm).1)) f hfc hfb
  · rw [hNN, htr S hS]
    have hS₀ : neutralPart S ⊆ N₀ := fun m hm => by
      obtain ⟨hmS, hmn⟩ := mem_neutralPart.mp hm
      exact mem_neutralPart.mpr ⟨hS hmS, hmn⟩
    have hcmp := integral_prod_mul_le_of_subset' μ hS₀ z hz1 f hfc hfb
    have hI0 : 0 ≤ ∫ φ, ∏ m ∈ neutralPart S, (1 + z m * f m φ) ∂μ :=
      integral_nonneg fun φ => prod_one_add_mul_nonneg _ z (fun m => f m φ)
        (fun m hm => hz1 m (hS₀ hm)) fun m _ => hfb m φ
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hI0) hcmp
    refine Finset.prod_le_prod₀ (fun m hm => ?_) fun m hm => ?_
    · have := hθ m (hmem m (Finset.mem_sdiff.1 hm).1).1
      linarith
    · have := hzθ m (Finset.mem_sdiff.1 hm).1
      linarith

/-- **The marked branch bound under the compact Villain law** (FS81 (5.29)–(5.35), §7.1, on one branch).
For a KP ensemble `N` with renormalized activities `|z_m| ≤ θ_m < 1`, the dipole mark at the
clock frequency `ξ/n`, `η ≤ min(ξ/n, 1 − ξ/n)`: the branch normalizer `Z_N` is positive and
`|∫ cos((ξ/n)⟨φ, ϱ₀⟩) ∏_N (1 + K cos) dμ| ≤ W_N · Z_N`, where `W_N` sums, over the neutral marked
clusters `C` and orientations `T ⊆ C`, the bounds `2^{-|C|} |∏_C K| e^{-G(C,T)}` of
`abs_villainMarkedTerm_le`, each divided by the cost `∏_{N₀ ∖ rem(C)₀} (1 - θ_m)` of the dropped
factors (`villain_branch_comparison`). Charged clusters contribute zero. -/
theorem abs_villainMarkedBranch_le (hL : 1 < L) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {g : ChargeDensity L → ℝ}
    (h24 : ClockWaveSelection boundary Λ centerOf β n g)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (hNc : NeutralSplitsAreCharged boundary L N) (K θ : ChargeDensity L → ℝ)
    (hθ : ∀ m ∈ N, θ m < 1)
    (hz : ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      g m ≤ translationEnergy (clockShiftCost β n) (gradLinear Λ) a (fun j => (m j : ℝ)) →
      |K m| * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a
        (fun j => (m j : ℝ))) ≤ θ m)
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℕ} (hξ0 : 0 < ξ) (hξn : ξ < n) {η : ℝ}
    (hη : 0 < η) (hηξ : η ≤ dipoleGap ((ξ : ℝ) / n)) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlamn : 28 * lam ≤ n) (hcost : 8192 * β * lam ≤ η * n ^ 2) :
    0 < ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ ∧
      |∫ φ, Real.cos ((ξ : ℝ) / n * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ| ≤
        (∑ C ∈ markedClusters boundary L (dipoleMark o x) N,
          if ∀ m ∈ C, ∑ j, m j = 0 then
            (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
                Real.exp (-clockCompositeGain boundary (by omega) ((ξ : ℝ) / n) η lam
                  (dipoleMark o x) C T)) /
              ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
                (1 - θ m)
          else 0) *
        ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂villainCompactLaw β n Λ := by
  classical
  have hL0 : 0 < L := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set ξ' : ℝ := (ξ : ℝ) / n with hξ'
  set ρ₀ := dipoleMark o x with hρ₀
  set μ := villainCompactLaw β n Λ with hμ
  have := isProbabilityMeasure_villainCompactLaw Λ hβ hn'
  obtain ⟨hZpos, hcmp⟩ := villain_branch_comparison Λ hΛ hdist centerOf hcenter hβ hn h24 hens
    hNa hNb hNc K θ hθ hz
  refine ⟨hZpos, ?_⟩
  set Z := ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ with hZ
  set R : Finset (ChargeDensity L) → Finset (ChargeDensity L) := fun C =>
    markedRemainder boundary L ρ₀ N C with hR
  set J : Finset (ChargeDensity L) → Finset (ChargeDensity L) → ℝ := fun C T =>
    ∫ φ, Real.cos (∑ j, φ j * markedDensity ξ' ρ₀ (satellite L C T) j) *
      ∏ m ∈ R C, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ with hJ
  have hint : ∀ C T : Finset (ChargeDensity L), Integrable (fun φ : Fin L × Fin L → ℝ =>
      ((1 / 2) ^ C.card * ∏ m ∈ C, K m) *
        Real.cos (∑ j, φ j * markedDensity ξ' ρ₀ (satellite L C T) j) *
        ∏ m ∈ R C, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := by
    intro C T
    have hP := Reduction.integrable_prod_one_add_mul_cos μ (R C) K
      (fun m φ => ∑ j, φ j * (m j : ℝ)) (fun m => by fun_prop)
    have hcP := hP.bdd_mul (c := 1)
      (Continuous.aestronglyMeasurable (by fun_prop : Continuous fun φ : Fin L × Fin L → ℝ =>
        Real.cos (∑ j, φ j * markedDensity ξ' ρ₀ (satellite L C T) j)))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    refine (hcP.const_mul ((1 / 2) ^ C.card * ∏ m ∈ C, K m)).congr
      (ae_of_all _ fun φ => ?_)
    ring
  have hI : ∫ φ, Real.cos (ξ' * ∑ j, φ j * (ρ₀ j : ℝ)) *
      ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∑ C ∈ markedClusters boundary L ρ₀ N, ∑ T ∈ C.powerset,
        ((1 / 2) ^ C.card * ∏ m ∈ C, K m) * J C T := by
    have hpt : ∀ φ : Fin L × Fin L → ℝ, Real.cos (ξ' * ∑ j, φ j * (ρ₀ j : ℝ)) *
        ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) =
        ∑ C ∈ markedClusters boundary L ρ₀ N, ∑ T ∈ C.powerset,
          ((1 / 2) ^ C.card * ∏ m ∈ C, K m) *
            Real.cos (∑ j, φ j * markedDensity ξ' ρ₀ (satellite L C T) j) *
            ∏ m ∈ R C, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) := fun φ =>
      markedExpansion (dipoleMark_ne_zero hox) N K ξ' φ
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ fun C _ => integrable_finsetSum _ fun T _ => hint C T]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [integral_finsetSum _ fun T _ => hint C T]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [hJ, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
  rw [hI]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun C hC => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  split_ifs with hCn
  · have hRN : R C ⊆ N := remainder_subset _ _
    have hθC : 0 < ∏ m ∈ neutralPart N \ neutralPart (R C), (1 - θ m) :=
      Finset.prod_pos fun m hm => by
        have := hθ m (mem_neutralPart.mp (Finset.mem_sdiff.1 hm).1).1
        linarith
    have hRZ : ∫ φ, ∏ m ∈ R C, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ ≤
        Z / ∏ m ∈ neutralPart N \ neutralPart (R C), (1 - θ m) := by
      rw [le_div_iff₀ hθC, mul_comm]
      exact hcmp (R C) hRN
    rw [div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_le_sum fun T hT => ?_
    have hT' : T ⊆ C := Finset.mem_powerset.1 hT
    have hterm := abs_villainMarkedTerm_le hL Λ hΛ hdist B h46 centerOf hcenter hβ hn h24 hens
      hNa hNb hNc K (fun m hm hq a ha => (hz m hm hq a ha).trans (hθ m hm).le) hox hξ0 hξn hη
      hηξ hlam hlamn hcost hC hCn hT'
    rw [abs_mul, mul_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine hterm.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hRZ (Real.exp_pos _).le
  · rw [zero_mul]
    refine le_of_eq (Finset.sum_eq_zero fun T hT => ?_)
    rw [show J C T = 0 from integral_villainMarkedTerm_eq_zero_of_charged Λ hβ hn hNa K
      (sum_univ_dipoleMark o x) ξ hC hCn (Finset.mem_powerset.1 hT), mul_zero, abs_zero]

end Branch

end FroehlichSpencer.BKT.Clock.VillainClock

end
