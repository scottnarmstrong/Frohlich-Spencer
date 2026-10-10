/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Multiscale.Singular
public import FroehlichSpencer.Multiscale.Locality
public import FroehlichSpencer.Infra.ProductMeasure
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.IDS.Averaged

/-!
# Measurability of singular-set events

For the product σ-algebra on configurations `Site ν → ℝ`: membership `x ∈ S_i(v)` and the
gentle-cluster events are measurable (both the infinite-volume and the `Λ`-restricted variants).
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.Multiscale

section Aux

variable {Ω α : Type*} [MeasurableSpace Ω]

private theorem measurableSet_forall_finset (T : Finset α) (p : α → Set Ω)
    (h : ∀ a ∈ T, MeasurableSet (p a)) : MeasurableSet {v | ∀ a ∈ T, v ∈ p a} := by
  have := MeasurableSet.biInter T.countable_toSet h
  convert this using 1
  ext v
  simp

private theorem measurableSet_exists_finset (T : Finset α) (p : α → Set Ω)
    (h : ∀ a ∈ T, MeasurableSet (p a)) : MeasurableSet {v | ∃ a ∈ T, v ∈ p a} := by
  have := MeasurableSet.biUnion T.countable_toSet h
  convert this using 1
  ext v
  simp

private theorem measurableSet_imp_const (p : Prop) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurableSet {v | p → v ∈ A} := by
  by_cases hp : p <;> simp [hp, hA]

private theorem measurableSet_and_const (p : Prop) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurableSet {v | p ∧ v ∈ A} := by
  by_cases hp : p <;> simp [hp, hA]

end Aux

theorem measurableSet_forall_le_abs_eigenvalues_sub {ν : ℕ} (B : Finset (Site ν)) (κ E : ℝ) :
    MeasurableSet {v : Site ν → ℝ |
      ∀ j, κ ≤ |(hamiltonian_isHermitian ν B v).eigenvalues j - E|} := by
  classical
  have hH : (fun v : Site ν → ℝ => hamiltonian ν B v) =
      fun v => -dirichletLaplacian ν B +
        Matrix.diagonal (fun x : {x : Site ν // x ∈ B} => (v x.1 : ℂ)) := by
    funext v
    unfold hamiltonian
    congr
  have hm : Measurable fun v : Site ν → ℝ => hamiltonian ν B v := by
    rw [hH]
    exact Infra.measurable_add_diagonal_comp _ Subtype.val
  exact Infra.measurableSet_setOf_forall_le_abs_eigenvalues_sub hm
    (hamiltonian_isHermitian ν B) E κ

section Generic

variable {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν))
  (S₀ : (Site ν → ℝ) → Set (Site ν))

private theorem spectral_congr (i : ℕ) (v : Site ν → ℝ) {F C : Finset (Site ν)} (h : F = C) :
    (∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
      |(hamiltonian_isHermitian ν (blk (thicken F (4 * scaleD P.K₀ i))) v).eigenvalues j
        - P.E|) ↔
    (∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
      |(hamiltonian_isHermitian ν (blk (thicken C (4 * scaleD P.K₀ i))) v).eigenvalues j
        - P.E|) := by
  subst h
  exact Iff.rfl

theorem isGentle_coe_iff (i : ℕ) (v : Site ν → ℝ) (C : Finset (Site ν)) :
    IsGentle P blk i v (C : Set (Site ν)) ↔
      DiamLE (siteDist ν) (C : Set (Site ν)) (scaleD P.K₀ i) ∧
        ∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
          |(hamiltonian_isHermitian ν (blk (thicken C (4 * scaleD P.K₀ i))) v).eigenvalues j
            - P.E| := by
  constructor
  · rintro ⟨hC, hd, hs⟩
    have h : hC.toFinset = C := Finset.coe_injective (by simp)
    exact ⟨hd, (spectral_congr P blk i v h).1 hs⟩
  · rintro ⟨hd, hs⟩
    refine ⟨C.finite_toSet, hd, ?_⟩
    have h : (C.finite_toSet).toFinset = C := Finset.coe_injective (by simp)
    exact (spectral_congr P blk i v h).2 hs

theorem measurableSet_isGentle_coe (i : ℕ) (C : Finset (Site ν)) :
    MeasurableSet {v : Site ν → ℝ | IsGentle P blk i v (C : Set (Site ν))} := by
  have : {v : Site ν → ℝ | IsGentle P blk i v (C : Set (Site ν))} =
      {v | DiamLE (siteDist ν) (C : Set (Site ν)) (scaleD P.K₀ i) ∧ v ∈
        {v : Site ν → ℝ | ∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
          |(hamiltonian_isHermitian ν (blk (thicken C (4 * scaleD P.K₀ i))) v).eigenvalues j
            - P.E|}} := by
    ext v
    exact isGentle_coe_iff P blk i v C
  rw [this]
  exact measurableSet_and_const _ (measurableSet_forall_le_abs_eigenvalues_sub _ _ _)

variable {P S₀}

theorem measurableSet_eq_chainCluster
    (i : ℕ) (hi : ∀ x, MeasurableSet {v : Site ν → ℝ | x ∈ singularSetsGen P blk (S₀ v) v i})
    (C : Finset (Site ν)) (x : Site ν) (hx : x ∈ C) :
    MeasurableSet {v : Site ν → ℝ | (C : Set (Site ν)) =
      chainCluster (siteDist ν) (singularSetsGen P blk (S₀ v) v i) (2 * scaleR P.K₀ i) x} := by
  set ρ := 2 * scaleR P.K₀ i with hρ
  have hxC : x ∈ (C : Set (Site ν)) := hx
  have key : {v : Site ν → ℝ | (C : Set (Site ν)) =
      chainCluster (siteDist ν) (singularSetsGen P blk (S₀ v) v i) ρ x} =
      {v | ∀ c ∈ C, v ∈ {v : Site ν → ℝ | c ∈ singularSetsGen P blk (S₀ v) v i}} ∩
      {v | ∀ c ∈ C, ∀ y ∈ thicken C ρ, v ∈ {v : Site ν → ℝ |
        (y ∉ C ∧ siteDist ν c y < ρ) → y ∉ singularSetsGen P blk (S₀ v) v i}} ∩
      {v | ∀ c ∈ (C : Set (Site ν)),
        Relation.ReflTransGen (chainStep (siteDist ν) (C : Set (Site ν)) ρ) x c} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [eq_chainCluster_iff hxC]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨fun c hc => h1 hc, ?_⟩, h3⟩
      intro c hc y _ ⟨hyC, hcy⟩ hyS
      exact hyC (h2 c hc y hyS hcy)
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun c hc => h1 c hc, ?_, h3⟩
      intro c hc y hyS hcy
      by_contra hyC
      refine h2 c hc y ?_ ⟨hyC, hcy⟩ hyS
      rw [mem_thicken]
      exact ⟨c, hc, by rw [siteDist_comm]; exact hcy.le⟩
  rw [key]
  refine ((measurableSet_forall_finset _ _ fun c _ => hi c).inter ?_).inter
    (MeasurableSet.const _)
  refine measurableSet_forall_finset _ _ fun c _ => measurableSet_forall_finset _ _ fun y _ => ?_
  exact measurableSet_imp_const _ (hi y).compl

theorem measurableSet_chainClusters_isGentle
    (i : ℕ) (hi : ∀ x, MeasurableSet {v : Site ν → ℝ | x ∈ singularSetsGen P blk (S₀ v) v i})
    (C : Finset (Site ν)) :
    MeasurableSet {v : Site ν → ℝ |
      (C : Set (Site ν)) ∈ chainClusters (siteDist ν) (singularSetsGen P blk (S₀ v) v i)
        (2 * scaleR P.K₀ i) ∧ IsGentle P blk i v (C : Set (Site ν))} := by
  have key : {v : Site ν → ℝ |
      (C : Set (Site ν)) ∈ chainClusters (siteDist ν) (singularSetsGen P blk (S₀ v) v i)
        (2 * scaleR P.K₀ i) ∧ IsGentle P blk i v (C : Set (Site ν))} =
      {v | ∃ x ∈ C, v ∈ ({v : Site ν → ℝ | (C : Set (Site ν)) =
        chainCluster (siteDist ν) (singularSetsGen P blk (S₀ v) v i) (2 * scaleR P.K₀ i) x} ∩
        {v | IsGentle P blk i v (C : Set (Site ν))})} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨x, hxS, h⟩, hg⟩
      refine ⟨x, ?_, h, hg⟩
      have : x ∈ chainCluster (siteDist ν) (singularSetsGen P blk (S₀ v) v i)
          (2 * scaleR P.K₀ i) x := mem_chainCluster_self hxS
      rw [← h] at this
      exact this
    · rintro ⟨x, hx, h, hg⟩
      refine ⟨⟨x, ?_, h⟩, hg⟩
      have : x ∈ (C : Set (Site ν)) := hx
      rw [h] at this
      exact chainCluster_subset x this
  rw [key]
  exact measurableSet_exists_finset _ _ fun x hx =>
    (measurableSet_eq_chainCluster blk i hi C x hx).inter (measurableSet_isGentle_coe P blk i C)

theorem measurableSet_mem_singularSetsGen
    (hS₀ : ∀ x, MeasurableSet {v : Site ν → ℝ | x ∈ S₀ v}) (i : ℕ) (x : Site ν) :
    MeasurableSet {v : Site ν → ℝ | x ∈ singularSetsGen P blk (S₀ v) v i} := by
  induction i generalizing x with
  | zero => exact hS₀ x
  | succ i ih =>
    set D := scaleD P.K₀ i
    set B := (finite_setOf_siteDist_le ν x D).toFinset with hB
    have key : {v : Site ν → ℝ | x ∈ singularSetsGen P blk (S₀ v) v (i + 1)} =
        {v | x ∈ singularSetsGen P blk (S₀ v) v i} ∩
        {v | ∃ C ∈ B.powerset, v ∈ {v : Site ν → ℝ | x ∈ C ∧
          (C : Set (Site ν)) = chainCluster (siteDist ν)
            (singularSetsGen P blk (S₀ v) v i) (2 * scaleR P.K₀ i) x ∧
          IsGentle P blk i v (C : Set (Site ν))}}ᶜ := by
      ext v
      simp only [mem_singularSetsGen_succ_iff, Set.mem_ofPred_eq, Set.mem_inter_iff,
        Set.mem_compl_iff]
      refine and_congr_right fun hxS => ?_
      constructor
      · intro hng ⟨C, _, hxC, hC, hg⟩
        exact hng (by rw [← hC]; exact hg)
      · intro hno hg
        obtain ⟨hfin, -⟩ := id hg
        have hxcl := mem_chainCluster_self (d := siteDist ν) (ρ := 2 * scaleR P.K₀ i) hxS
        refine hno ⟨hfin.toFinset, ?_, by simpa using hxcl, by simp, by simpa using hg⟩
        rw [Finset.mem_powerset]
        intro y hy
        rw [hB, Set.Finite.mem_toFinset]
        exact hg.subset_ball P blk v hxcl (by simpa using hy)
    rw [key]
    refine (ih x).inter (MeasurableSet.compl ?_)
    refine measurableSet_exists_finset _ _ fun C _ => ?_
    have : {v : Site ν → ℝ | x ∈ C ∧
          (C : Set (Site ν)) = chainCluster (siteDist ν)
            (singularSetsGen P blk (S₀ v) v i) (2 * scaleR P.K₀ i) x ∧
          IsGentle P blk i v (C : Set (Site ν))} =
        {v | x ∈ C ∧ v ∈ ({v : Site ν → ℝ | (C : Set (Site ν)) = chainCluster (siteDist ν)
            (singularSetsGen P blk (S₀ v) v i) (2 * scaleR P.K₀ i) x} ∩
          {v | IsGentle P blk i v (C : Set (Site ν))})} := by
      ext v; simp
    rw [this]
    by_cases hx : x ∈ C
    · exact measurableSet_and_const _
        ((measurableSet_eq_chainCluster blk i ih C x hx).inter
          (measurableSet_isGentle_coe P blk i C))
    · simp [hx]

end Generic

theorem measurableSet_mem_singularSets {ν : ℕ} (P : Params) (x : Site ν) (i : ℕ) :
    MeasurableSet {v : Site ν → ℝ | x ∈ singularSets P v i} := by
  refine measurableSet_mem_singularSetsGen (S₀ := singular0 P) id ?_ i x
  intro y
  change MeasurableSet {v : Site ν → ℝ | |v y - P.E + 2 * (ν : ℝ)| ≤ P.Nthr}
  exact measurableSet_le (continuous_abs.measurable.comp
    (((measurable_pi_apply y).sub_const _).add_const _)) measurable_const

theorem measurableSet_mem_singularSetsIn {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (x : Site ν) (i : ℕ) : MeasurableSet {v : Site ν → ℝ | x ∈ singularSetsIn P Λ v i} := by
  refine measurableSet_mem_singularSetsGen (S₀ := fun v => singular0 P v ∩ Λ)
    (fun B => B ∩ Λ) ?_ i x
  intro y
  have : {v : Site ν → ℝ | y ∈ singular0 P v ∩ (Λ : Set (Site ν))} =
      {v | y ∈ (Λ : Set (Site ν)) ∧ v ∈ {v : Site ν → ℝ |
        |v y - P.E + 2 * (ν : ℝ)| ≤ P.Nthr}} := by
    ext v
    simp [mem_singular0, and_comm]
  rw [this]
  exact measurableSet_and_const _ (measurableSet_le (continuous_abs.measurable.comp
    (((measurable_pi_apply y).sub_const _).add_const _)) measurable_const)

theorem measurableSet_isGentleClusterIn {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (i : ℕ)
    (C : Finset (Site ν)) :
    MeasurableSet {v : Site ν → ℝ |
      (C : Set (Site ν)) ∈ chainClusters (siteDist ν) (singularSetsIn P Λ v i)
        (2 * scaleR P.K₀ i) ∧ IsGentle P (fun B => B ∩ Λ) i v C} :=
  measurableSet_chainClusters_isGentle (S₀ := fun v => singular0 P v ∩ Λ) (fun B => B ∩ Λ) i
    (measurableSet_mem_singularSetsIn P Λ · i) C

theorem dependsOn_mem_singularSets {ν : ℕ} (P : Params) (x : Site ν) (i : ℕ) :
    Infra.DependsOn {y | siteDist ν x y ≤ localityRadius P.K₀ i}
      {v : Site ν → ℝ | x ∈ singularSets P v i} :=
  Infra.dependsOn_of_measurable_of_invariant (measurableSet_mem_singularSets P x i)
    fun _ _ h => mem_singularSets_congr P (fun y hy => h y hy)

theorem dependsOn_mem_singularSetsIn {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (x : Site ν)
    (i : ℕ) :
    Infra.DependsOn {y | siteDist ν x y ≤ localityRadius P.K₀ i}
      {v : Site ν → ℝ | x ∈ singularSetsIn P Λ v i} :=
  Infra.dependsOn_of_measurable_of_invariant (measurableSet_mem_singularSetsIn P Λ x i)
    fun _ _ h => mem_singularSetsIn_congr P Λ (fun y hy => h y hy)

end FroehlichSpencer.Multiscale

end
