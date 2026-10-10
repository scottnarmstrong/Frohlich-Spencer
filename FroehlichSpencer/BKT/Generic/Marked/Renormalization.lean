/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Waves
public import FroehlichSpencer.BKT.Generic.Marked.Comparison
public import FroehlichSpencer.BKT.Reduction.T16Assembly
import Mathlib.Tactic

/-!
# The marked T1.6 assembly on one branch

Every term of the marked expansion
`cos(ξ⟨φ, ϱ₀⟩) ∏_N (1 + K cos) = ∑_{C, T} 2^{-|C|} (∏_C K) cos⟨φ, ξϱ₀ + ϱ^𝒩⟩ ∏_{rem(C)} (1 + K cos)`
is renormalized with two sets of waves:
- KP's P2.4 waves of the extended ensemble `rem(C) ∪ {p}`;
- the composite wave of `Generic/Marked/Waves.lean`.

* `WaveSelection` is the conclusion of KP P2.4 (`Reduction.P24Step`) after the centre and cover
  choices.

`compositeGain` is the energy bound of the composite wave.
* **`abs_markedTerm_le`** (FS81 (5.31)–(5.34)): for a neutral cluster, if the renormalized
  activities are at most one,
  `|∫ cos⟨φ, ξϱ₀ + ϱ^𝒩⟩ ∏_{rem(C)} (1 + K cos) dμ| ≤ e^{-G(C,T)} ∫ ∏_{rem(C)} (1 + K cos) dμ`.

The renormalized remainder factors are positive.
* `integral_markedTerm_eq_zero_of_charged`: clusters with a charged member contribute nothing.
* `branch_comparison` (FS81 (5.35), with KP's own waves of `N`): `Z_N > 0` and
  `∏_{N₀ ∖ S₀} (1 − θ) ∫ ∏_S (1 + K cos) dμ ≤ Z_N`.
* **`abs_markedBranch_le`**: `|∫ cos(ξ⟨φ, ϱ₀⟩) ∏_N (1 + K cos) dμ| ≤ W_N Z_N`.

Here `W_N` sums,
  over neutral clusters and orientations, the term bounds divided by the dropped-factor costs.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

open MeasureTheory SpinWaves Reduction

/-! ### Interfaces -/

section Interfaces

variable (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]

/-- The conclusion of KP Proposition 2.4 (`Reduction.P24Step`) for one center choice and one
cover selection: every neutral member of every KP ensemble has a spin wave with clauses
(1)–(3) and the energy bound (2.17). -/
def WaveSelection (Λ : Multigraph (Fin L × Fin L) E)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L) (cover : MinimumCoverSelection boundary L)
    (D₃ : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N →
    AtMostOneNonNeutral N → IsScaleSeparated boundary L N →
    NeutralSplitsAreCharged boundary L N →
    ∀ ϱ ∈ neutralPart N, ∃ a : Fin L × Fin L → ℝ,
      (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) ϱ,
        ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), a j = c) ∧
      Function.support a ⊆ Λ.densityDomain ϱ (centerOf ϱ) ∧
      Function.support (Λ.laplacian a) ⊆ Λ.densityDomain ϱ (centerOf ϱ) ∧
      1 / β * (1 / 16 * ∑ j, (ϱ j : ℝ) ^ 2 +
          D₃ * separatedSquareTotal boundary L cover ϱ) ≤
        SpinWaves.energyFunctional Λ β a ϱ

/-- The energy gain `β⁻¹ (‖ρ‖²/16 + (η²/8192) ∑_k |𝒮_k^sep(p)|)` of the composite wave of the
marked term `(C, T)` (`exists_realCompositeWave`), with `ρ = ξ ϱ₀ + ϱ^𝒩` and `p` its proxy. -/
def compositeGain {L : ℕ} (hL0 : 0 < L) (ξ η β : ℝ) (ρ₀ : ChargeDensity L)
    (C T : Finset (ChargeDensity L)) : ℝ :=
  ((∑ j, markedDensity ξ ρ₀ (satellite L C T) j ^ 2) / 16 + η ^ 2 / 8192 *
    (separatedSquareTotal boundary L (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k)
      (markedProxy ρ₀ C T) : ℝ)) / β

end Interfaces

/-! ### Helpers -/

section Helpers

variable {L : ℕ}

theorem isMinimumSquareCover_congr {boundary : SquareBoundary} {k : ℕ} {ρ ρ' : ChargeDensity L}
    (h : chargeSupport ρ = chargeSupport ρ') {Cov : Finset (Finset (Fin L × Fin L))}
    (hC : IsMinimumSquareCover boundary L k ρ Cov) : IsMinimumSquareCover boundary L k ρ' Cov := by
  unfold IsMinimumSquareCover IsSquareCover at hC ⊢
  rw [← h]
  exact hC

theorem energyFunctional_eq_gffTranslationEnergy {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (β : ℝ) (a : V → ℝ) (ϱ : V → ℤ) :
    SpinWaves.energyFunctional G β a ϱ = gffTranslationEnergy G β a (fun j => (ϱ j : ℝ)) :=
  rfl

/-- The pairing of a spin wave of `m` with a real neutral density supported in the support of
another member `p`: zero, by constancy on `D⁺(p)` (comparable `p`) or by the support clause
(`p` much larger), as in `spinWave_orthogonality`. -/
theorem pairing_real_eq_zero_of_clauses {V E : Type*} [Fintype V] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    {p m : V → ℤ} (hp : p ∈ N₀) (hmp : m ≠ p) (hpn : ∑ j, p j = 0)
    (hpc : G.IsDensityCenter p (centerOf p)) (am : V → ℝ)
    (hconst : ∀ ϱ' ∈ G.comparableDensities N₀ m,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), am j = c)
    (hsupp : Function.support am ⊆ G.densityDomain m (centerOf m))
    (hfar : 2 * G.densityDiameter m < G.densityDiameter p →
      ∀ y, p y ≠ 0 → y ∉ G.densityDomain m (centerOf m))
    (ρ : V → ℝ) (hρsupp : ∀ j, ρ j ≠ 0 → p j ≠ 0) (hρ : ∑ j, ρ j = 0) :
    Multigraph.pairing am ρ = 0 := by
  by_cases hle : G.densityDiameter p ≤ 2 * G.densityDiameter m
  · obtain ⟨c, hc⟩ := hconst p (G.mem_comparableDensities.mpr ⟨hp, hle, hmp⟩)
    have hterm : ∀ j, am j * ρ j = c * ρ j := by
      intro j
      by_cases hj : ρ j = 0
      · rw [hj, mul_zero, mul_zero]
      · rw [hc j (G.mem_densityDomainPlus_of_center hG hpn hpc (hρsupp j hj))]
    rw [Multigraph.pairing, Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, hρ,
      mul_zero]
  · have hterm : ∀ j, am j * ρ j = 0 := by
      intro j
      by_cases hj : ρ j = 0
      · rw [hj, mul_zero]
      · have hnot := hfar (not_le.mp hle) j (hρsupp j hj)
        have ha : am j = 0 := by
          by_contra ha
          exact hnot (hsupp ha)
        rw [ha, zero_mul]
    rw [Multigraph.pairing, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_const_zero]

end Helpers

/-! ### The marked term -/

section Term

variable {boundary : SquareBoundary} {L : ℕ} {E : Type} [Fintype E]

/-- **The bound on one marked term** (FS81 (5.31)–(5.34) for one cluster and orientation; marked
P4.7/P2.4 assembly). For a neutral cluster `C` of a KP ensemble `N` and `T ⊆ C`, with the dipole
mark and `0 < ξ < 1`,
`|∫ cos⟨φ, ξϱ₀ + ϱ^𝒩⟩ ∏_{rem(C)} (1 + K cos) dμ| ≤ e^{-G(C,T)} ∫ ∏_{rem(C)} (1 + K cos) dμ`,
`G(C,T) = β⁻¹ (‖ξϱ₀ + ϱ^𝒩‖²/16 + (η²/8192) ∑_k |𝒮_k^sep(p)|)`, provided the renormalized
activities of the members are at most one. The remainder's waves are KP's P2.4 waves for the
extended ensemble `rem(C) ∪ {p}` (`markedExtension_kp`), the composite's wave is
`exists_realCompositeWave`, and the translation is `gffLaw_integral_cos_mul_prod_translation`. -/
theorem abs_markedTerm_le (hL : 1 < L) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {D₃ : ℝ} (cover : MinimumCoverSelection boundary L)
    (h24 : WaveSelection boundary Λ centerOf cover D₃) {β : ℝ} (hβ : 0 < β)
    (v : Fin L × Fin L) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (hNc : NeutralSplitsAreCharged boundary L N) (K : ChargeDensity L → ℝ)
    (hz : ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 + D₃ * separatedSquareTotal boundary L cover m) ≤
        SpinWaves.energyFunctional Λ β a m →
      |K m| * Real.exp (-SpinWaves.energyFunctional Λ β a m) ≤ 1)
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 ≤ η)
    (hηξ : η ≤ dipoleGap ξ) {C : Finset (ChargeDensity L)}
    (hC : C ∈ markedClusters boundary L (dipoleMark o x) N) (hCn : ∀ m ∈ C, ∑ j, m j = 0)
    {T : Finset (ChargeDensity L)} (hT : T ⊆ C) :
    |∫ φ, Real.cos (∑ j, φ j * markedDensity ξ (dipoleMark o x) (satellite L C T) j) *
        ∏ m ∈ markedRemainder boundary L (dipoleMark o x) N C,
          (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v| ≤
      Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T) *
        ∫ φ, ∏ m ∈ markedRemainder boundary L (dipoleMark o x) N C,
          (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v := by
  classical
  have hL0 : 0 < L := by omega
  set ρ₀ := dipoleMark o x with hρ₀
  set σ := satellite L C T with hσ
  set ρ := markedDensity ξ ρ₀ σ with hρdef
  set p := markedProxy ρ₀ C T with hpdef
  set R := markedRemainder boundary L ρ₀ N C with hR
  set N' := markedExtension (boundary := boundary) ρ₀ N C T with hN'
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  obtain ⟨hE, hEa, hEb, hEc, hpN₀, hpR, hsuppP⟩ :=
    markedExtension_kp (boundary := boundary) hL hox hens hNa hNb hNc hC hCn hT
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hRN : R ⊆ N := remainder_subset _ _
  have hdisjC : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m') :=
    fun m hm m' hm' hne => hens.2 m (hCN hm) m' (hCN hm') hne
  have hρsupp : ∀ j, ρ j ≠ 0 ↔ p j ≠ 0 :=
    markedProxy_ne_zero_iff_dipole hox hξ0 hξ1 hT hdisjC
  have hρn : ∑ j, ρ j = 0 := by
    have h1 : ∑ j, (ρ₀ j : ℝ) = 0 := by exact_mod_cast sum_univ_dipoleMark o x
    have h2 : ∑ j, (σ j : ℝ) = 0 := by exact_mod_cast sum_satellite hCn hT
    simp only [hρdef, markedDensity, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2,
      mul_zero, add_zero]
  -- the patch charges of the composite
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
    have h := dipole_patchCharge_ge hL hox ξ hens hNb hNc hC hCn hT k _ hs'
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
  -- the remainder's waves (KP P2.4 for the extended ensemble) and the composite wave
  have hw' := h24 β hβ N' hE hEa hEb hEc
  choose! a' ha' using hw'
  obtain ⟨a₀, h0c, h0s, h0l, h0E⟩ := exists_realCompositeWave boundary hL Λ hΛ hdist B h46
    centerOf hcenter N' hE hEa hEb hEc p hpN₀ ρ hρsupp hρn hη hgap hβ
  set N₀ := neutralPart N' with hN₀
  set A : ChargeDensity L → Fin L × Fin L → ℝ := fun ϱ => if ϱ = p then a₀ else a' ϱ with hA
  have hAp : A p = a₀ := by simp [hA]
  have hAm : ∀ ϱ, ϱ ≠ p → A ϱ = a' ϱ := fun ϱ h => by simp [hA, h]
  have hmem₀ : ∀ ϱ ∈ N₀, ϱ ∈ N' ∧ ∑ j, ϱ j = 0 := fun ϱ hϱ => mem_neutralPart.mp hϱ
  have hne0 : ∀ ϱ ∈ N₀, ϱ ≠ 0 := fun ϱ hϱ => hE.1 ϱ (hmem₀ ϱ hϱ).1
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
  have hAl : ∀ ϱ ∈ N₀,
      Function.support (Λ.laplacian (A ϱ)) ⊆ Λ.densityDomain ϱ (centerOf ϱ) := by
    intro ϱ hϱ
    by_cases h : ϱ = p
    · subst h
      rw [hAp]
      exact h0l
    · rw [hAm ϱ h]
      exact (ha' ϱ hϱ).2.2.1
  have hfar : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' →
      2 * Λ.densityDiameter ϱ < Λ.densityDiameter ϱ' →
        ∀ y, ϱ' y ≠ 0 → y ∉ Λ.densityDomain ϱ (centerOf ϱ) :=
    fun ϱ hϱ ϱ' hϱ' hne hlt y hy =>
      notMem_densityDomain_of_scaleSeparated boundary Λ hΛ hdist (hne0 ϱ hϱ) (hmem₀ ϱ hϱ).2
        (hEb.1 ϱ (hmem₀ ϱ hϱ).1 ϱ' (hmem₀ ϱ' hϱ').1 hne) hlt (hcenter ϱ (hne0 ϱ hϱ)) hy
  obtain ⟨ho1, ho2⟩ := spinWave_orthogonality Λ hΛ N₀ (fun ϱ hϱ => (hmem₀ ϱ hϱ).2) centerOf
    (fun ϱ hϱ => hcenter ϱ (hne0 ϱ hϱ)) A hAc hAs hAl hfar
  -- the neutral remainder inside the extended ensemble
  set R₀ := neutralPart R with hR₀
  have hR₀N₀ : ∀ m ∈ R₀, m ∈ N₀ := fun m hm => by
    obtain ⟨hmR, hmn⟩ := mem_neutralPart.mp hm
    exact mem_neutralPart.mpr ⟨Finset.mem_insert_of_mem hmR, hmn⟩
  have hR₀p : ∀ m ∈ R₀, m ≠ p := fun m hm h => hpR (by
    have hmR := (mem_neutralPart.mp hm).1
    rw [h] at hmR
    exact hmR)
  -- the orthogonality relations of the translation
  have hreal : ∀ m ∈ R₀, Multigraph.pairing (A m) ρ = 0 := by
    intro m hm
    have hmN₀ := hR₀N₀ m hm
    exact pairing_real_eq_zero_of_clauses Λ hΛ N₀ centerOf hpN₀ (hR₀p m hm)
      (hmem₀ p hpN₀).2 (hcenter p (hne0 p hpN₀)) (A m) (hAc m hmN₀) (hAs m hmN₀)
      (fun hlt y hy => hfar m hmN₀ p hpN₀ (hR₀p m hm) hlt y hy) ρ
      (fun j hj => (hρsupp j).1 hj) hρn
  have htr := gffLaw_integral_cos_mul_prod_translation Λ hΛ β hβ v ρ a₀ hρn
    (fun i : {m // m ∈ R₀} => fun j => ((i.val j : ℤ) : ℝ))
    (fun i => by exact_mod_cast (mem_neutralPart.mp i.property).2) (fun i => K i.val)
    (fun i => A i.val)
    (fun i => by
      rw [← hAp]
      exact ho1 p hpN₀ i.val (hR₀N₀ _ i.property) (Ne.symm (hR₀p _ i.property)))
    (fun i => hreal i.val i.property)
    (fun i i' hne => ho1 i.val (hR₀N₀ _ i.property) i'.val (hR₀N₀ _ i'.property)
      fun h => hne (Subtype.ext h))
    (fun i => by
      rw [← hAp]
      exact ho2 p hpN₀ i.val (hR₀N₀ _ i.property) (Ne.symm (hR₀p _ i.property)))
    (fun i i' hne => ho2 i.val (hR₀N₀ _ i.property) i'.val (hR₀N₀ _ i'.property)
      fun h => hne (Subtype.ext h))
  obtain ⟨htr1, htr2⟩ := htr
  -- the renormalized activities of the remainder are at most one
  have hzle : ∀ i : {m // m ∈ R₀}, |K i.val *
      Real.exp (-gffTranslationEnergy Λ β (A i.val) (fun j => ((i.val j : ℤ) : ℝ)))| ≤ 1 := by
    intro i
    obtain ⟨hmR, hmn⟩ := mem_neutralPart.mp i.property
    have hEi := (ha' i.val (hR₀N₀ _ i.property)).2.2.2
    rw [abs_mul, Real.abs_exp, ← energyFunctional_eq_gffTranslationEnergy,
      hAm _ (hR₀p _ i.property)]
    exact hz i.val (hRN hmR) hmn _ hEi
  -- remove the non-neutral member of the remainder
  have hRa : ∀ ϱ₁ ∈ R, ∀ ϱ₂ ∈ R, ∑ j, ϱ₁ j ≠ 0 → ∑ j, ϱ₂ j ≠ 0 → ϱ₁ = ϱ₂ :=
    fun ϱ₁ h₁ ϱ₂ h₂ => hNa ϱ₁ (hRN h₁) ϱ₂ (hRN h₂)
  have hJ0 := gffLaw_integral_cos_mul_prod_eq_neutralPart Λ hΛ β hβ v R hRa K ρ hρn
  have hZ0 : ∫ φ, ∏ m ∈ R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∫ φ, ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    have h := gffLaw_integral_prod_eq_neutralPart Λ hΛ β hβ v R hRa K (fun _ => 0)
    simp only [add_zero] at h
    exact h
  rw [hJ0, hZ0]
  -- products over the subtype
  have hJ : ∫ φ, Real.cos (∑ j, φ j * ρ j) *
      ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∫ φ, Real.cos (∑ j, φ j * ρ j) * ∏ i : {m // m ∈ R₀},
        (1 + K i.val * Real.cos (∑ j, φ j * ((i.val j : ℤ) : ℝ))) ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    exact congrArg (Real.cos (∑ j, φ j * ρ j) * ·)
      (Finset.prod_coe_sort R₀ fun m => 1 + K m * Real.cos (∑ j, φ j * ((m j : ℤ) : ℝ))).symm
  have hZ : ∫ φ, ∏ m ∈ R₀, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∫ φ, ∏ i : {m // m ∈ R₀},
        (1 + K i.val * Real.cos (∑ j, φ j * ((i.val j : ℤ) : ℝ))) ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    exact (Finset.prod_coe_sort R₀ fun m =>
      1 + K m * Real.cos (∑ j, φ j * ((m j : ℤ) : ℝ))).symm
  rw [hJ, hZ, htr2, htr1, abs_mul, Real.abs_exp]
  have hbound := abs_integral_cos_mul_prod_le μ Finset.univ
    (fun i : {m // m ∈ R₀} => K i.val *
      Real.exp (-gffTranslationEnergy Λ β (A i.val) (fun j => ((i.val j : ℤ) : ℝ))))
    (fun i _ => hzle i) (fun φ => ∑ j, φ j * (ρ j + β * Λ.laplacian a₀ j))
    (fun i φ => ∑ j, φ j * (((i.val j : ℤ) : ℝ) + β * Λ.laplacian (A i.val) j))
    (fun i => by fun_prop)
  have hexp : Real.exp (-gffTranslationEnergy Λ β a₀ ρ) ≤
      Real.exp (-compositeGain boundary hL0 ξ η β ρ₀ C T) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    unfold compositeGain
    exact h0E
  have hI0 : 0 ≤ ∫ φ, ∏ i : {m // m ∈ R₀}, (1 + K i.val *
      Real.exp (-gffTranslationEnergy Λ β (A i.val) (fun j => ((i.val j : ℤ) : ℝ))) *
        Real.cos (∑ j, φ j * (((i.val j : ℤ) : ℝ) + β * Λ.laplacian (A i.val) j))) ∂μ :=
    integral_nonneg fun φ => prod_one_add_mul_cos_nonneg Finset.univ _ (fun i _ => hzle i) _
  calc Real.exp (-gffTranslationEnergy Λ β a₀ ρ) *
        |∫ φ, Real.cos (∑ j, φ j * (ρ j + β * Λ.laplacian a₀ j)) * ∏ i : {m // m ∈ R₀},
          (1 + K i.val *
            Real.exp (-gffTranslationEnergy Λ β (A i.val) (fun j => ((i.val j : ℤ) : ℝ))) *
          Real.cos (∑ j, φ j * (((i.val j : ℤ) : ℝ) + β * Λ.laplacian (A i.val) j))) ∂μ|
      ≤ Real.exp (-gffTranslationEnergy Λ β a₀ ρ) * ∫ φ, ∏ i : {m // m ∈ R₀},
          (1 + K i.val *
            Real.exp (-gffTranslationEnergy Λ β (A i.val) (fun j => ((i.val j : ℤ) : ℝ))) *
          Real.cos (∑ j, φ j * (((i.val j : ℤ) : ℝ) + β * Λ.laplacian (A i.val) j))) ∂μ :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp hI0

end Term

/-! ### Charged clusters -/

section Charged

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **A cluster with a charged member contributes nothing**: the satellite then carries the
nonzero integer charge `±Q(ϱ_c)`, the remainder is neutral, and the constant mode integrates the
term to zero (KP §2.3.1, Step 1). -/
theorem integral_markedTerm_eq_zero_of_charged {L : ℕ} {boundary : SquareBoundary}
    (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β)
    (v : Fin L × Fin L) {N : Finset (ChargeDensity L)} (hNa : AtMostOneNonNeutral N)
    (K : ChargeDensity L → ℝ) {ρ₀ : ChargeDensity L} (hρ₀ : ∑ j, ρ₀ j = 0) (ξ : ℝ)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L ρ₀ N)
    (hCq : ¬ ∀ m ∈ C, ∑ j, m j = 0) {T : Finset (ChargeDensity L)} (hT : T ⊆ C) :
    ∫ φ, Real.cos (∑ j, φ j * markedDensity ξ ρ₀ (satellite L C T) j) *
        ∏ m ∈ markedRemainder boundary L ρ₀ N C,
          (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v = 0 := by
  classical
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
  -- the satellite is charged
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
  have hτ : ∑ j, ξ * (ρ₀ j : ℝ) = 0 := by
    rw [← Finset.mul_sum]
    have : ∑ j, (ρ₀ j : ℝ) = 0 := by exact_mod_cast hρ₀
    rw [this, mul_zero]
  set F : (Fin L × Fin L → ℝ) → ℝ := fun φ =>
    ∏ m ∈ R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ) + 0)) with hF
  have hFshift : GffShiftInvariant F := gffShiftInvariant_prod_neutral R hRn K fun _ => 0
  have hFbound : ∀ φ, |F φ| ≤ ∏ m ∈ R, (1 + |K m|) := by
    intro φ
    simp only [hF]
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun m _ => ?_
    calc |1 + K m * Real.cos (∑ j, φ j * (m j : ℝ) + 0)|
        ≤ |(1 : ℝ)| + |K m * Real.cos (∑ j, φ j * (m j : ℝ) + 0)| := abs_add_le _ _
      _ ≤ 1 + |K m| := by
        rw [abs_one, abs_mul]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h := gffLaw_integral_cos_charged_mul_eq_zero Λ hΛ β hβ v (satellite L C T) hσ
    (fun j => ξ * (ρ₀ j : ℝ)) hτ F hFshift (by simp only [hF]; fun_prop) _ hFbound
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  simp only [hF, add_zero, markedDensity]
  congr 2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Charged

/-! ### The comparison with the branch normalizer -/

section Branch

variable {boundary : SquareBoundary} {L : ℕ} {E : Type} [Fintype E]

/-- **The branch normalizer and its comparison** (FS81 (5.35)): with KP's P2.4 waves of the
branch ensemble `N` and renormalized activities `|z_m| ≤ θ_m < 1`,
`Z_N = ∫ ∏_N (1 + K cos) dμ > 0`, and for every subfamily `S ⊆ N`,
`∏_{m ∈ N₀ ∖ S₀} (1 - θ_m) · ∫ ∏_S (1 + K cos) dμ ≤ Z_N`. -/
theorem branch_comparison (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {D₃ : ℝ} (cover : MinimumCoverSelection boundary L)
    (h24 : WaveSelection boundary Λ centerOf cover D₃) {β : ℝ} (hβ : 0 < β)
    (v : Fin L × Fin L) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (hNc : NeutralSplitsAreCharged boundary L N) (K θ : ChargeDensity L → ℝ)
    (hθ : ∀ m ∈ N, θ m < 1)
    (hz : ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 + D₃ * separatedSquareTotal boundary L cover m) ≤
        SpinWaves.energyFunctional Λ β a m →
      |K m| * Real.exp (-SpinWaves.energyFunctional Λ β a m) ≤ θ m) :
    0 < ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v ∧
      ∀ S ⊆ N, (∏ m ∈ neutralPart N \ neutralPart S, (1 - θ m)) *
          ∫ φ, ∏ m ∈ S, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v ≤
        ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v := by
  classical
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  have hw := h24 β hβ N hens hNa hNb hNc
  choose! a ha using hw
  set N₀ := neutralPart N with hN₀
  have hmem : ∀ ϱ ∈ N₀, ϱ ∈ N ∧ ∑ j, ϱ j = 0 := fun ϱ hϱ => mem_neutralPart.mp hϱ
  have hne0 : ∀ ϱ ∈ N₀, ϱ ≠ 0 := fun ϱ hϱ => hens.1 ϱ (hmem ϱ hϱ).1
  obtain ⟨ho1, ho2⟩ := spinWave_orthogonality Λ hΛ N₀ (fun ϱ hϱ => (hmem ϱ hϱ).2) centerOf
    (fun ϱ hϱ => hcenter ϱ (hne0 ϱ hϱ)) a (fun ϱ hϱ => (ha ϱ hϱ).1) (fun ϱ hϱ => (ha ϱ hϱ).2.1)
    (fun ϱ hϱ => (ha ϱ hϱ).2.2.1)
    (fun ϱ hϱ ϱ' hϱ' hne hlt y hy =>
      notMem_densityDomain_of_scaleSeparated boundary Λ hΛ hdist (hne0 ϱ hϱ) (hmem ϱ hϱ).2
        (hNb.1 ϱ (hmem ϱ hϱ).1 ϱ' (hmem ϱ' hϱ').1 hne) hlt (hcenter ϱ (hne0 ϱ hϱ)) hy)
  set z : ChargeDensity L → ℝ := fun m =>
    K m * Real.exp (-SpinWaves.energyFunctional Λ β (a m) m) with hzdef
  have hzθ : ∀ m ∈ N₀, |z m| ≤ θ m := by
    intro m hm
    rw [hzdef, abs_mul, Real.abs_exp]
    exact hz m (hmem m hm).1 (hmem m hm).2 _ (ha m hm).2.2.2
  have hz1 : ∀ m ∈ N₀, |z m| ≤ 1 := fun m hm => (hzθ m hm).trans (hθ m (hmem m hm).1).le
  set θ' : ChargeDensity L → (Fin L × Fin L → ℝ) → ℝ := fun m φ =>
    ∑ j, φ j * ((m j : ℝ) + β * Λ.laplacian (a m) j) with hθ'
  -- the translated form of a subproduct
  have htr : ∀ S ⊆ N, ∫ φ, ∏ m ∈ S, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∫ φ, ∏ m ∈ neutralPart S, (1 + z m * Real.cos (θ' m φ)) ∂μ := by
    intro S hS
    have hSa : ∀ ϱ₁ ∈ S, ∀ ϱ₂ ∈ S, ∑ j, ϱ₁ j ≠ 0 → ∑ j, ϱ₂ j ≠ 0 → ϱ₁ = ϱ₂ :=
      fun ϱ₁ h₁ ϱ₂ h₂ => hNa ϱ₁ (hS h₁) ϱ₂ (hS h₂)
    have h0 := gffLaw_integral_prod_eq_neutralPart Λ hΛ β hβ v S hSa K (fun _ => 0)
    simp only [add_zero] at h0
    rw [h0]
    have hS₀ : neutralPart S ⊆ N₀ := fun m hm => by
      obtain ⟨hmS, hmn⟩ := mem_neutralPart.mp hm
      exact mem_neutralPart.mpr ⟨hS hmS, hmn⟩
    have h1 := gffLaw_integral_prod_spinWave_translation_finset Λ hΛ β hβ v (neutralPart S)
      (fun m hm => (mem_neutralPart.mp hm).2) K 0 a
      (fun ϱ hϱ ϱ' hϱ' hne => ho1 ϱ (hS₀ hϱ) ϱ' (hS₀ hϱ') hne)
      (fun ϱ hϱ ϱ' hϱ' hne => ho2 ϱ (hS₀ hϱ) ϱ' (hS₀ hϱ') hne)
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at h1
    rw [h1]
  have hcont : ∀ m, Continuous (θ' m) := fun m => by
    simp only [hθ']
    fun_prop
  have hNN := htr N (Finset.Subset.refl N)
  refine ⟨?_, fun S hS => ?_⟩
  · rw [hNN]
    exact integral_prod_pos μ N₀ z (fun m hm => (hzθ m hm).trans_lt (hθ m (hmem m hm).1)) θ'
      hcont
  · rw [hNN, htr S hS]
    have hS₀ : neutralPart S ⊆ N₀ := fun m hm => by
      obtain ⟨hmS, hmn⟩ := mem_neutralPart.mp hm
      exact mem_neutralPart.mpr ⟨hS hmS, hmn⟩
    have hcmp := integral_prod_mul_le_of_subset μ hS₀ z hz1 θ' hcont
    have hI0 : 0 ≤ ∫ φ, ∏ m ∈ neutralPart S, (1 + z m * Real.cos (θ' m φ)) ∂μ :=
      integral_nonneg fun φ => prod_one_add_mul_cos_nonneg _ z
        (fun m hm => hz1 m (hS₀ hm)) _
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hI0) hcmp
    refine Finset.prod_le_prod₀ (fun m hm => ?_) fun m hm => ?_
    · have := hθ m (hmem m (Finset.mem_sdiff.1 hm).1).1
      linarith
    · have := hzθ m (Finset.mem_sdiff.1 hm).1
      linarith

/-- **The marked branch bound** (FS81 (5.29)–(5.35) on one branch of the marked T2.2). For a
KP ensemble `N` with renormalized activities `|z_m| ≤ θ_m < 1`, the dipole mark and
`η ≤ min(ξ, 1 − ξ)`, `0 < ξ < 1`: the branch normalizer `Z_N` is positive and
`|∫ cos(ξ⟨φ, ϱ₀⟩) ∏_N (1 + K cos) dμ| ≤ W_N · Z_N`, where `W_N` sums, over the neutral marked
clusters `C` and orientations `T ⊆ C`, the bounds `2^{-|C|} |∏_C K| e^{-G(C,T)}` of
`abs_markedTerm_le`, each divided by the cost `∏_{N₀ ∖ rem(C)₀} (1 - θ_m)` of the dropped
factors (`branch_comparison`). Charged clusters contribute zero. -/
theorem abs_markedBranch_le (hL : 1 < L) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {D₃ : ℝ} (cover : MinimumCoverSelection boundary L)
    (h24 : WaveSelection boundary Λ centerOf cover D₃) {β : ℝ} (hβ : 0 < β)
    (v : Fin L × Fin L) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (hNc : NeutralSplitsAreCharged boundary L N) (K θ : ChargeDensity L → ℝ)
    (hθ : ∀ m ∈ N, θ m < 1)
    (hz : ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 + D₃ * separatedSquareTotal boundary L cover m) ≤
        SpinWaves.energyFunctional Λ β a m →
      |K m| * Real.exp (-SpinWaves.energyFunctional Λ β a m) ≤ θ m)
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 ≤ η)
    (hηξ : η ≤ dipoleGap ξ) :
    0 < ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v ∧
      |∫ φ, Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v| ≤
        (∑ C ∈ markedClusters boundary L (dipoleMark o x) N,
          if ∀ m ∈ C, ∑ j, m j = 0 then
            (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
                Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T)) /
              ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
                (1 - θ m)
          else 0) *
        ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw Λ hΛ β hβ v := by
  classical
  have hL0 : 0 < L := by omega
  set ρ₀ := dipoleMark o x with hρ₀
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  obtain ⟨hZpos, hcmp⟩ := branch_comparison Λ hΛ hdist centerOf hcenter cover h24 hβ v hens hNa
    hNb hNc K θ hθ hz
  refine ⟨hZpos, ?_⟩
  set Z := ∫ φ, ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ with hZ
  set R : Finset (ChargeDensity L) → Finset (ChargeDensity L) := fun C =>
    markedRemainder boundary L ρ₀ N C with hR
  set J : Finset (ChargeDensity L) → Finset (ChargeDensity L) → ℝ := fun C T =>
    ∫ φ, Real.cos (∑ j, φ j * markedDensity ξ ρ₀ (satellite L C T) j) *
      ∏ m ∈ R C, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ with hJ
  -- integrate the marked expansion
  have hint : ∀ C T : Finset (ChargeDensity L), Integrable (fun φ : Fin L × Fin L → ℝ =>
      ((1 / 2) ^ C.card * ∏ m ∈ C, K m) *
        Real.cos (∑ j, φ j * markedDensity ξ ρ₀ (satellite L C T) j) *
        ∏ m ∈ R C, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := by
    intro C T
    have hP := Reduction.integrable_prod_one_add_mul_cos μ (R C) K
      (fun m φ => ∑ j, φ j * (m j : ℝ)) (fun m => by fun_prop)
    have hcP := hP.bdd_mul (c := 1)
      (Continuous.aestronglyMeasurable (by fun_prop : Continuous fun φ : Fin L × Fin L → ℝ =>
        Real.cos (∑ j, φ j * markedDensity ξ ρ₀ (satellite L C T) j)))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    refine (hcP.const_mul ((1 / 2) ^ C.card * ∏ m ∈ C, K m)).congr
      (ae_of_all _ fun φ => ?_)
    ring
  have hI : ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
      ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ =
      ∑ C ∈ markedClusters boundary L ρ₀ N, ∑ T ∈ C.powerset,
        ((1 / 2) ^ C.card * ∏ m ∈ C, K m) * J C T := by
    have hpt : ∀ φ : Fin L × Fin L → ℝ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) *
        ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) =
        ∑ C ∈ markedClusters boundary L ρ₀ N, ∑ T ∈ C.powerset,
          ((1 / 2) ^ C.card * ∏ m ∈ C, K m) *
            Real.cos (∑ j, φ j * markedDensity ξ ρ₀ (satellite L C T) j) *
            ∏ m ∈ R C, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) := fun φ =>
      markedExpansion (dipoleMark_ne_zero hox) N K ξ φ
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
  · -- a neutral cluster
    have hRN : R C ⊆ N := remainder_subset _ _
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
    have hterm := abs_markedTerm_le hL Λ hΛ hdist B h46 centerOf hcenter cover h24 hβ v hens hNa
      hNb hNc K (fun m hm hq a ha => (hz m hm hq a ha).trans (hθ m hm).le) hox hξ0 hξ1 hη hηξ
      hC hCn hT'
    rw [abs_mul, mul_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine hterm.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hRZ (Real.exp_pos _).le
  · -- a charged cluster: every term vanishes
    rw [zero_mul]
    refine le_of_eq (Finset.sum_eq_zero fun T hT => ?_)
    rw [show J C T = 0 from integral_markedTerm_eq_zero_of_charged Λ hΛ β hβ v hNa K
      (sum_univ_dipoleMark o x) ξ hC hCn (Finset.mem_powerset.1 hT), mul_zero, abs_zero]

end Branch

end FroehlichSpencer.BKT.Generic.Marked
