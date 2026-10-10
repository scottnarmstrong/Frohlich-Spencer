/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedInterface
public import FroehlichSpencer.BKT.FiniteGraph.Green
import Mathlib.Tactic

/-!
# Green variational input for rooted marked geometry

The zero-remainder case of a marked term is optimized by the finite-graph Green potential. This
file proves that variational identity and checks the exact empty-cluster scaling on the smallest
nontrivial rooted dipole. It does not supply the logarithmic lower bound uniformly in displacement
or the profile construction for nonempty composites.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Multigraph
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Rotator

/-- The Green potential which maximizes the translation exponent for a neutral source. -/
noncomputable def greenMaximizingWave {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (τ : ℝ) (hG : G.toSimpleGraph.Connected)
    (σ : V → ℝ) : V → ℝ := fun v => -(τ⁻¹ * G.greenOp hG σ v)

/-- The maximum of the Gaussian translation exponent over all waves is the Green quadratic form
scaled by `1 / (2 τ)`. -/
theorem gffTranslationEnergy_greenMaximizingWave {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (τ : ℝ) (hτ : τ ≠ 0)
    (hG : G.toSimpleGraph.Connected) (σ : V → ℝ) (hσ : ∑ v, σ v = 0) :
    gffTranslationEnergy G τ (greenMaximizingWave G τ hG σ) σ =
      Multigraph.pairing σ (-G.greenOp hG σ) / (2 * τ) := by
  let Q := Multigraph.pairing σ (-G.greenOp hG σ)
  have hpair : Multigraph.pairing (greenMaximizingWave G τ hG σ) σ = τ⁻¹ * Q := by
    unfold greenMaximizingWave Multigraph.pairing Q
    calc
      (∑ v, (-(τ⁻¹ * G.greenOp hG σ v)) * σ v) =
          ∑ v, τ⁻¹ * (σ v * -(G.greenOp hG σ v)) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = τ⁻¹ * ∑ v, σ v * -(G.greenOp hG σ v) := by rw [Finset.mul_sum]
  have hgreen : G.energy (G.greenOp hG σ) = Q := by
    exact (G.pairing_eq_energy_greenOp hG σ hσ).symm
  have henergyScale : G.energy (greenMaximizingWave G τ hG σ) =
      (τ⁻¹) ^ 2 * G.energy (G.greenOp hG σ) := by
    unfold greenMaximizingWave Multigraph.energy
    calc
      (∑ e, G.grad (fun v => -(τ⁻¹ * G.greenOp hG σ v)) e ^ 2) =
          ∑ e, (τ⁻¹) ^ 2 * G.grad (G.greenOp hG σ) e ^ 2 := by
            apply Finset.sum_congr rfl
            intro e he
            simp [Multigraph.grad]
            ring
      _ = (τ⁻¹) ^ 2 * ∑ e, G.grad (G.greenOp hG σ) e ^ 2 := by
            rw [Finset.mul_sum]
  have henergy : G.energy (greenMaximizingWave G τ hG σ) = (τ⁻¹) ^ 2 * Q := by
    rw [henergyScale, hgreen]
  calc
    gffTranslationEnergy G τ (greenMaximizingWave G τ hG σ) σ =
        τ⁻¹ * Q - (τ / 2) * ((τ⁻¹) ^ 2 * Q) := by
          simp [gffTranslationEnergy, hpair, henergy]
    _ = Q / (2 * τ) := by field_simp [hτ]; ring

/-- With an empty remainder, the Green potential supplies the exact requested energy as soon as
the source gain is bounded by its Green quadratic form. -/
theorem rootedMarkedTermData_empty_of_green {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (τ : ℝ) (hτ : τ ≠ 0)
    (hG : G.toSimpleGraph.Connected) (K : (V → ℤ) → ℝ) (σ : V → ℝ)
    (hσ : ∑ v, σ v = 0) (gain : ℝ)
    (hgain : gain ≤ Multigraph.pairing σ (-G.greenOp hG σ) / (2 * τ)) :
    RootedMarkedTermData G τ K σ ∅ gain := by
  refine ⟨greenMaximizingWave G τ hG σ, (fun _ => 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · calc
      gain ≤ Multigraph.pairing σ (-G.greenOp hG σ) / (2 * τ) := hgain
      _ = gffTranslationEnergy G τ (greenMaximizingWave G τ hG σ) σ :=
        (gffTranslationEnergy_greenMaximizingWave G τ hτ hG σ hσ).symm

/-- The empty set is always a marked cluster; every monotone adjacency still has to handle its
associated logarithmic term. -/
theorem empty_mem_clusters {ι : Type} [DecidableEq ι]
    (adj : ι → Finset ι → Prop) (N : Finset ι) :
    ∅ ∈ Generic.Marked.clusters adj N := by
  rw [Generic.Marked.mem_clusters]
  exact ⟨Finset.empty_subset _, rfl⟩

/-- The empty-cluster term forced by any branch clause. -/
theorem RootedMarkedBranchClause.emptyTerm {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] {G : Multigraph V E} {τ : ℝ}
    {N : Finset (V → ℤ)} {K : (V → ℤ) → ℝ} {cost : (V → ℤ) → ℝ}
    {ξ : ℝ} {ρ₀ : V → ℤ} {adj : (V → ℤ) → Finset (V → ℤ) → Prop}
    {s₀ Knb γ ℓ : ℝ}
    (h : RootedMarkedBranchClause G τ N K cost ξ ρ₀ adj s₀ Knb γ ℓ) :
    RootedMarkedTermData G τ K (rootedMarkedComposite ξ ρ₀ ∅ ∅)
      (Generic.Marked.remainder adj N ∅) (γ * ℓ) := by
  simpa using h.term ∅ (empty_mem_clusters adj N) ∅ Finset.Subset.rfl

/-- The rooted dipole has total charge zero whenever its two sites are distinct. -/
theorem rootedDipoleMark_sum_zero {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n) :
    ∑ j, rootedDipoleMark R n hn j = 0 := by
  classical
  have hsites : center R ≠ axialSite R n hn := by
    intro h
    have hf := congrArg Prod.fst h
    simp [center, axialSite] at hf
    omega
  have hsome : ∑ j : Site R,
      (if j = center R then (1 : ℤ) else if j = axialSite R n hn then -1 else 0) = 0 := by
    have hpoint (j : Site R) :
      (if j = center R then (1 : ℤ) else if j = axialSite R n hn then -1 else 0) =
          (if j = center R then 1 else 0) + (if j = axialSite R n hn then -1 else 0) := by
      by_cases hc : j = center R
      · subst j
        simp [hsites]
      · by_cases ha : j = axialSite R n hn
        · subst j
          simp [hsites.symm]
        · simp [hc, ha]
    calc
      _ = ∑ j : Site R, ((if j = center R then (1 : ℤ) else 0) +
          (if j = axialSite R n hn then -1 else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hpoint j
      _ = (∑ j : Site R, if j = center R then (1 : ℤ) else 0) +
          ∑ j : Site R, if j = axialSite R n hn then -1 else 0 := Finset.sum_add_distrib
      _ = 1 + -1 := by simp
      _ = 0 := by ring
  rw [Fintype.sum_option]
  simp only [rootedDipoleMark]
  simp [hsome]

/-- A signed integer satellite preserves neutrality of a neutral root mark. -/
theorem rootedMarkedComposite_sum_zero {V : Type} [Fintype V] [DecidableEq V]
    (ξ : ℝ) (ρ₀ : V → ℤ) (C T : Finset (V → ℤ))
    (hρ₀ : ∑ j, ρ₀ j = 0) (hC : ∀ m ∈ C, ∑ j, m j = 0) (hTC : T ⊆ C) :
    ∑ j, rootedMarkedComposite ξ ρ₀ C T j = 0 := by
  classical
  unfold rootedMarkedComposite
  have hρ₀' : ∑ j, (ρ₀ j : ℝ) = 0 := by exact_mod_cast hρ₀
  have hTsum : ∑ j, ∑ m ∈ T, (m j : ℝ) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro m hm
    have hm0 : ∑ j, (m j : ℝ) = 0 := by exact_mod_cast hC m (hTC hm)
    simp [hm0]
  have hCT : ∑ j, ∑ m ∈ C \ T, (m j : ℝ) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro m hm
    have hm0 : ∑ j, (m j : ℝ) = 0 := by
      exact_mod_cast hC m (Finset.mem_sdiff.mp hm).1
    simp [hm0]
  calc
    ∑ j, (ξ * (ρ₀ j : ℝ) + ∑ m ∈ T, (m j : ℝ) - ∑ m ∈ C \ T, (m j : ℝ)) =
        ξ * (∑ j, (ρ₀ j : ℝ)) + (∑ j, ∑ m ∈ T, (m j : ℝ)) -
          ∑ j, ∑ m ∈ C \ T, (m j : ℝ) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 0 := by rw [hρ₀', hTsum, hCT]; ring

/-- The fractional rooted composite remains at least `min (ξ,1-ξ)` away from zero at the
positive endpoint of its dipole, independently of the integer satellite. -/
theorem rootedMarkedComposite_gap_center {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n)
    (ξ : ℝ) (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    dipoleGap ξ ≤ |rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
      (some (center R))| := by
  classical
  have hsites : center R ≠ axialSite R n hn := by
    intro h
    have hf := congrArg Prod.fst h
    simp [center, axialSite] at hf
    omega
  have hmark : rootedDipoleMark R n hn (some (center R)) = 1 := by
    simp [rootedDipoleMark]
  let z : ℤ := (∑ m ∈ T, m (some (center R))) -
    ∑ m ∈ C \ T, m (some (center R))
  have hz : (z : ℝ) =
      (∑ m ∈ T, (m (some (center R)) : ℝ)) -
        ∑ m ∈ C \ T, (m (some (center R)) : ℝ) := by
    dsimp [z]
    push_cast
    rfl
  have hvalue : rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
      (some (center R)) = (1 : ℝ) * ξ + z := by
    simp [rootedMarkedComposite, hmark, hz]
    ring
  have hgap := isGapped_mul_add_int (ξ := ξ) (k := (1 : ℤ)) (Or.inl rfl) z 0
  rw [hvalue]
  simpa using hgap

/-- The fractional rooted composite remains at least `min (ξ,1-ξ)` away from zero at the
negative endpoint of its dipole, independently of the integer satellite. -/
theorem rootedMarkedComposite_gap_axial {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n)
    (ξ : ℝ) (C T : Finset (RotatorDualFace (sideLength R) → ℤ) ) :
    dipoleGap ξ ≤ |rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
      (some (axialSite R n hn))| := by
  classical
  have hsites : center R ≠ axialSite R n hn := by
    intro h
    have hf := congrArg Prod.fst h
    simp [center, axialSite] at hf
    omega
  have hmark : rootedDipoleMark R n hn (some (axialSite R n hn)) = -1 := by
    have hneq : some (axialSite R n hn) ≠ some (center R) := by
      intro h
      exact hsites (Option.some.inj h).symm
    simp [rootedDipoleMark, hneq]
  let z : ℤ := (∑ m ∈ T, m (some (axialSite R n hn))) -
    ∑ m ∈ C \ T, m (some (axialSite R n hn))
  have hz : (z : ℝ) =
      (∑ m ∈ T, (m (some (axialSite R n hn)) : ℝ)) -
        ∑ m ∈ C \ T, (m (some (axialSite R n hn)) : ℝ) := by
    dsimp [z]
    push_cast
    rfl
  have hvalue : rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
      (some (axialSite R n hn)) = (-1 : ℝ) * ξ + z := by
    simp [rootedMarkedComposite, hmark, hz]
    ring
  have hgap := isGapped_mul_add_int (ξ := ξ) (k := (-1 : ℤ)) (Or.inr rfl) z 0
  rw [hvalue]
  simpa using hgap

/-- The smallest rooted dipole mark, at displacement one in the radius-two square. -/
abbrev minimalRootedDipoleMark : RotatorDualFace (sideLength 2) → ℤ :=
  rootedDipoleMark 2 1 (by omega)

/-- The real marked composite for the smallest test: empty satellite and frequency `1/2`. -/
noncomputable def minimalRootedDipoleComposite : Option (Site 2) → ℝ :=
  rootedMarkedComposite (1 / 2 : ℝ) minimalRootedDipoleMark ∅ ∅

theorem minimalRootedDipoleMark_center_ne_axial :
    center 2 ≠ axialSite 2 1 (by omega) := by
  intro h
  have hf := congrArg Prod.fst h
  simp [center, axialSite, sideLength] at hf

theorem minimalRootedDipoleComposite_pointwise (j : Option (Site 2)) :
    minimalRootedDipoleComposite j =
      if j = some (center 2) then (1 / 2 : ℝ)
      else if j = some (axialSite 2 1 (by omega)) then -(1 / 2 : ℝ) else 0 := by
  simp [minimalRootedDipoleComposite, rootedMarkedComposite, minimalRootedDipoleMark,
    rootedDipoleMark]

theorem minimalRootedDipoleComposite_sum :
    ∑ j, minimalRootedDipoleComposite j = 0 := by
  classical
  rw [Fintype.sum_option]
  have hnone : minimalRootedDipoleComposite none = 0 := by
    rw [minimalRootedDipoleComposite_pointwise]
    simp
  have hsite (i : Site 2) :
      minimalRootedDipoleComposite (some i) =
        (if i = center 2 then (1 / 2 : ℝ) else 0) +
          (if i = axialSite 2 1 (by omega) then -(1 / 2 : ℝ) else 0) := by
    rw [minimalRootedDipoleComposite_pointwise]
    simp only [Option.some.injEq]
    by_cases hc : i = center 2
    · subst i
      simp [minimalRootedDipoleMark_center_ne_axial]
    · simp [hc]
  have hcenter :
      (∑ i : Site 2, if i = center 2 then (1 / 2 : ℝ) else 0) = 1 / 2 := by
    exact Finset.sum_ite_eq' (Finset.univ : Finset (Site 2)) (center 2)
      (fun _ => (1 / 2 : ℝ))
  have haxial :
      (∑ i : Site 2, if i = axialSite 2 1 (by omega) then -(1 / 2 : ℝ) else 0) =
        -(1 / 2 : ℝ) := by
    exact Finset.sum_ite_eq' (Finset.univ : Finset (Site 2))
      (axialSite 2 1 (by omega)) (fun _ => -(1 / 2 : ℝ))
  rw [hnone, zero_add]
  calc
    (∑ i : Site 2, minimalRootedDipoleComposite (some i)) =
        (∑ i : Site 2, if i = center 2 then (1 / 2 : ℝ) else 0) +
          ∑ i : Site 2, if i = axialSite 2 1 (by omega) then -(1 / 2 : ℝ) else 0 := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => hsite i
    _ = 0 := by rw [hcenter, haxial]; ring

theorem minimalRootedDipoleComposite_ne_zero :
    minimalRootedDipoleComposite (some (center 2)) ≠ 0 := by
  rw [minimalRootedDipoleComposite_pointwise]
  simp

/-- The empty-cluster term clause is satisfiable in the smallest rooted instance. The chosen local
constant is its Green quadratic form; the uniform-in-displacement lower bound remains a separate
part of the full marked-extension theorem. -/
theorem minimalRootedDipole_empty_cluster_term :
    ∃ γ : ℝ, 0 < γ ∧
      RootedMarkedTermData (graph 2) 1
        (fun _ : RotatorDualFace (sideLength 2) → ℤ => 0)
        minimalRootedDipoleComposite ∅
        (γ * (1 / 4 : ℝ) ^ 2 / 1 * Real.logb 2 (1 + 1)) := by
  classical
  let hG : (graph 2).toSimpleGraph.Connected :=
    squareZero_connected (sideLength 2) (by simp [sideLength])
  let Q : ℝ := Multigraph.pairing minimalRootedDipoleComposite
    (-(graph 2).greenOp hG minimalRootedDipoleComposite)
  have hQ : 0 < Q := by
    have hnonneg := (graph 2).pairing_greenOp_nonneg hG minimalRootedDipoleComposite
      minimalRootedDipoleComposite_sum
    have hne : Q ≠ 0 := by
      intro hzero
      have hiff := (graph 2).pairing_greenOp_eq_zero_iff hG minimalRootedDipoleComposite
        minimalRootedDipoleComposite_sum
      have hz' : Multigraph.pairing minimalRootedDipoleComposite
          (-(graph 2).greenOp hG minimalRootedDipoleComposite) = 0 := hzero
      have hsigma := hiff.mp hz'
      exact minimalRootedDipoleComposite_ne_zero
        (congrFun hsigma (some (center 2)))
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  refine ⟨Q, hQ, ?_⟩
  apply rootedMarkedTermData_empty_of_green (graph 2) 1 (by norm_num) hG
    (fun _ : RotatorDualFace (sideLength 2) → ℤ => 0)
    minimalRootedDipoleComposite minimalRootedDipoleComposite_sum _
  have hlog : Real.logb 2 ((1 : ℝ) + 1) = 1 := by norm_num
  rw [hlog]
  norm_num
  dsimp [Q]
  nlinarith [hQ]

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
