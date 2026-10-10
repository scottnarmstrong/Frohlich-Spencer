/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Events
public import FroehlichSpencer.T12.Resonance
public import FroehlichSpencer.Multiscale.Singular
public import FroehlichSpencer.Infra.Combinatorics.UnionBound
public import FroehlichSpencer.Infra.Wegner.Gaussian

/-!
# Section 5: small nodes
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.T12

open Multiscale


theorem configurationMeasure_biInter_eq_prod {ν : ℕ} (law : Measure ℝ) [IsProbabilityMeasure law]
    {ι : Type*} (T : Finset ι) (F : ι → Finset (Site ν))
    (hF : (T : Set ι).PairwiseDisjoint F) (A : ι → Set (Configuration ν))
    (hA : ∀ t ∈ T, Infra.DependsOn (F t : Set (Site ν)) (A t)) :
    configurationMeasure ν law (⋂ t ∈ T, A t) = ∏ t ∈ T, configurationMeasure ν law (A t) :=
  Infra.productMeasure_biInter_eq_prod law T (fun t => (F t : Set (Site ν)))
    (fun a ha b hb hab => by
      simpa [Function.onFun, Finset.disjoint_coe] using hF ha hb hab) A hA

private theorem singular0_eq_setOf {ν : ℕ} (P : Params) (x : Site ν) :
    {v : Site ν → ℝ | x ∈ singular0 P v} =
      {v | v x ∈ Set.Icc (P.E - 2 * ν - P.Nthr) (P.E - 2 * ν + P.Nthr)} := by
  ext v
  simp only [Set.mem_ofPred_eq, mem_singular0, Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]


theorem configurationMeasure_singular0_le_boundedDensity {ν : ℕ} (law : Measure ℝ)
    [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ) (P : Params)
    (hN : P.Nthr = Real.sqrt δ) (x : Site ν) :
    configurationMeasure ν law {v | x ∈ singular0 P v} ≤ ENNReal.ofReal (2 / Real.sqrt δ) := by
  obtain ⟨hδ, g, -, hlg, hg⟩ := hlaw
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  rw [singular0_eq_setOf]
  change Infra.productMeasure law _ ≤ _
  rw [Infra.productMeasure_setOf_apply_mem law x measurableSet_Icc]
  refine (Infra.measure_Icc_le_boundedDensity law hlg (Filter.Eventually.of_forall hg) _ _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : P.E - 2 * ν + P.Nthr - (P.E - 2 * ν - P.Nthr) = 2 * Real.sqrt δ := by
    rw [hN]; ring
  rw [h2]
  have : δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ.le).symm
  rw [div_eq_mul_inv]
  refine le_of_eq ?_
  calc δ⁻¹ * (2 * Real.sqrt δ) = 2 * (Real.sqrt δ / δ) := by ring
    _ = 2 * (Real.sqrt δ / (Real.sqrt δ * Real.sqrt δ)) := by rw [← this]
    _ = 2 * (Real.sqrt δ)⁻¹ := by field_simp


theorem configurationMeasure_singular0_le_gaussian {ν : ℕ} {γ : ℝ} (hγ : 0 < γ) (P : Params)
    (hN : P.Nthr = |P.E| / 2) (hE : 2 * (ν : ℝ) < |P.E| / 2) (x : Site ν) :
    configurationMeasure ν (gaussianLaw γ hγ) {v | x ∈ singular0 P v} ≤
      ENNReal.ofReal (2 * Real.exp (-(|P.E| / 2 - 2 * ν) ^ 2 / (2 * γ))) := by
  have hR : 0 ≤ |P.E| / 2 - 2 * ν := by linarith only [hE]
  have hsub : {v : Site ν → ℝ | x ∈ singular0 P v} ⊆
      {v | |P.E| / 2 - 2 * ν ≤ |v x|} := by
    intro v hv
    simp only [Set.mem_ofPred_eq, mem_singular0, hN] at hv ⊢
    have h1 : |P.E| ≤ |P.E - 2 * ν| + 2 * ν := by
      calc |P.E| = |(P.E - 2 * ν) + 2 * ν| := by ring_nf
        _ ≤ |P.E - 2 * ν| + |2 * (ν : ℝ)| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ν)]
    have h2 : |P.E - 2 * ν| ≤ |v x| + |v x - P.E + 2 * ν| := by
      calc |P.E - 2 * ν| = |v x - (v x - P.E + 2 * ν)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith only [hv, h1, h2]
  refine (measure_mono hsub).trans ?_
  have := Infra.productMeasure_gaussianReal_le_abs_apply_le (ι := Site ν)
    (γ := ⟨γ, hγ.le⟩) x hR
  exact this


theorem scaleD_mono_of_nonneg {K₀ : ℝ} (hK : 0 ≤ K₀) {a b : ℕ} (h : a ≤ b) :
    scaleD K₀ a ≤ scaleD K₀ b := by
  unfold scaleD
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_left _ hK
  exact pow_le_pow_right₀ (by norm_num) h

private theorem scaleD_rpow_neg {K₀ q : ℝ} (k : ℕ) :
    scaleD K₀ k ^ (-q) = Real.exp (-(q * (K₀ * (5 / 4 : ℝ) ^ k))) := by
  unfold scaleD
  rw [← Real.exp_mul]
  congr 1
  ring


theorem tsum_scaleD_rpow_neg_le {K₀ q : ℝ} (hK : 0 < K₀) (hq : 0 < q) (k : ℕ) :
    ∑' s : ℕ, scaleD K₀ (k + s) ^ (-q) ≤ (1 - Real.exp (-(q * K₀ / 4)))⁻¹ * scaleD K₀ k ^ (-q) := by
  set r : ℝ := Real.exp (-(q * K₀ / 4)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    have := mul_pos hq hK
    exact Real.exp_lt_exp.2 (by linarith only [this])
  have hterm : ∀ s : ℕ, scaleD K₀ (k + s) ^ (-q) ≤ scaleD K₀ k ^ (-q) * r ^ s := by
    intro s
    rw [scaleD_rpow_neg, scaleD_rpow_neg, hr, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hb : (1 : ℝ) + s * (1 / 4) ≤ (1 + 1 / 4) ^ s :=
      one_add_mul_le_pow (by norm_num) s
    have hk1 : (1 : ℝ) ≤ (5 / 4) ^ k := one_le_pow₀ (by norm_num)
    have hpow : (5 / 4 : ℝ) ^ (k + s) = (5 / 4) ^ k * (5 / 4) ^ s := pow_add _ _ _
    have h54 : (1 + 1 / 4 : ℝ) = 5 / 4 := by norm_num
    rw [h54] at hb
    have hKq : 0 < q * K₀ := mul_pos hq hK
    have h1 : (5 / 4 : ℝ) ^ k * (1 + s * (1 / 4)) ≤ (5 / 4) ^ (k + s) := by
      rw [hpow]; exact mul_le_mul_of_nonneg_left hb (by positivity)
    have h2 : (5 / 4 : ℝ) ^ k + s / 4 ≤ (5 / 4) ^ k * (1 + s * (1 / 4)) := by
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      nlinarith only [hk1]
    have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) hKq.le
    nlinarith only [h3]
  have hsum : Summable fun s : ℕ => scaleD K₀ k ^ (-q) * r ^ s :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnn : ∀ s : ℕ, 0 ≤ scaleD K₀ (k + s) ^ (-q) := fun s =>
    Real.rpow_nonneg (scaleD_pos _ _).le _
  have hsum' : Summable fun s : ℕ => scaleD K₀ (k + s) ^ (-q) :=
    Summable.of_nonneg_of_le hnn hterm hsum
  calc ∑' s : ℕ, scaleD K₀ (k + s) ^ (-q) ≤ ∑' s : ℕ, scaleD K₀ k ^ (-q) * r ^ s :=
        hsum'.tsum_le_tsum hterm hsum
    _ = (1 - r)⁻¹ * scaleD K₀ k ^ (-q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, mul_comm]


theorem lt_scaleD_of_maximal {K₀ : ℝ} {l : ℝ} {k : ℕ}
    (hmax : ∀ i, scaleD K₀ i / 5 ≤ l → i ≤ k) (hk : scaleD K₀ k / 5 ≤ l) :
    (5 * l) ^ (4 / 5 : ℝ) < scaleD K₀ k := by
  have h1 : l < scaleD K₀ (k + 1) / 5 := by
    by_contra h
    have := hmax (k + 1) (not_lt.1 h)
    omega
  have hl : 0 < l := lt_of_lt_of_le (by have := scaleD_pos K₀ k; positivity) hk
  have h2 : 5 * l < scaleD K₀ k ^ (5 / 4 : ℝ) := by
    have := scaleR_eq_scaleD_succ K₀ k
    unfold scaleR at this
    rw [this]; linarith only [h1]
  have h3 := Real.rpow_lt_rpow (by positivity) h2 (by norm_num : (0 : ℝ) < 4 / 5)
  rwa [← Real.rpow_mul (scaleD_pos K₀ k).le, show (5 / 4 : ℝ) * (4 / 5) = 1 by norm_num,
    Real.rpow_one] at h3


theorem gentleEventIn_subset_any {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) (j : ℕ) :
    gentleEventIn P Λ D j ⊆ gentleEventAnyIn P Λ D :=
  Set.subset_iUnion (fun i => gentleEventIn P Λ D i) j


theorem gentleEventIn_eq_empty_of_diam {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) (j : ℕ)
    (h : ¬ DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD P.K₀ j)) :
    gentleEventIn P Λ D j = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v hv => h ?_
  obtain ⟨-, -, hd, -⟩ := (mem_gentleEventIn P Λ D j v).1 hv
  exact hd


theorem card_thicken_inter_le {ν : ℕ} (Λ D : Finset (Site ν)) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : DiamLE (siteDist ν) (D : Set (Site ν)) R) :
    ((thicken D (4 * R) ∩ Λ).card : ℝ) ≤ 11 ^ ν * (1 + R) ^ ν := by
  rcases D.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have : thicken (∅ : Finset (Site ν)) (4 * R) = ∅ := by
      ext y; simp [mem_thicken]
    rw [this]; simp only [Finset.empty_inter, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨s, hs, hcard⟩ := Infra.Lattice.exists_latticeBall_finset_sub x₀ (R := 5 * R)
    (by positivity)
  have hsub : thicken D (4 * R) ∩ Λ ⊆ s := by
    intro y hy
    obtain ⟨c, hc, hyc⟩ := mem_thicken.1 (Finset.mem_inter.1 hy).1
    rw [hs, ← siteDist_eq_norm]
    have := siteDist_triangle ν y x₀ c
    have h3 := hdiam c hc x₀ hx₀
    have := siteDist_triangle ν y c x₀
    have h4 := hdiam c hc x₀ hx₀
    linarith [siteDist_comm ν c x₀]
  have h1 : (thicken D (4 * R) ∩ Λ).card ≤ (2 * ⌊5 * R⌋₊ + 1) ^ ν :=
    (Finset.card_le_card hsub).trans hcard
  have h2 : ((2 * ⌊5 * R⌋₊ + 1 : ℕ) : ℝ) ≤ 11 * (1 + R) := by
    have := Nat.floor_le (show 0 ≤ 5 * R by positivity)
    push_cast
    linarith only [this]
  calc ((thicken D (4 * R) ∩ Λ).card : ℝ) ≤ (((2 * ⌊5 * R⌋₊ + 1) ^ ν : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ((2 * ⌊5 * R⌋₊ + 1 : ℕ) : ℝ) ^ ν := by push_cast; rfl
    _ ≤ (11 * (1 + R)) ^ ν := pow_le_pow_left₀ (by positivity) h2 ν
    _ = _ := mul_pow _ _ _

private theorem sqrt_two_mul_exp_neg_sqrt (R : ℝ) :
    Real.sqrt (2 * Real.exp (-Real.sqrt R)) = Real.sqrt 2 * Real.exp (-Real.sqrt R / 2) := by
  rw [Real.sqrt_mul (by norm_num), Real.exp_half]


theorem measure_resonance_thicken_le_boundedDensity {ν : ℕ} (law : Measure ℝ)
    [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ) (E : ℝ)
    (Λ D : Finset (Site ν)) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : DiamLE (siteDist ν) (D : Set (Site ν)) R) :
    configurationMeasure ν law (resonanceEvent ν (thicken D (4 * R) ∩ Λ) E
        (Real.exp (-Real.sqrt R))) ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.sqrt δ⁻¹ * (11 ^ ν * (1 + R) ^ ν) *
        Real.exp (-Real.sqrt R / 2)) := by
  have h := (resonance_bound_boundedDensity ν (thicken D (4 * R) ∩ Λ) law hlaw E
    (Real.exp (-Real.sqrt R))).2
  refine h.trans ?_
  have hc := card_thicken_inter_le Λ D hR hdiam
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [sqrt_two_mul_exp_neg_sqrt]
  calc _ ≤ Real.sqrt 2 * Real.exp (-Real.sqrt R / 2) * Real.sqrt δ⁻¹ *
        (11 ^ ν * (1 + R) ^ ν) := by gcongr
    _ = _ := by ring


theorem measure_resonance_thicken_le_gaussian {ν : ℕ} {γ : ℝ} (hγ : 0 < γ) (E : ℝ)
    (Λ D : Finset (Site ν)) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : DiamLE (siteDist ν) (D : Set (Site ν)) R) :
    configurationMeasure ν (gaussianLaw γ hγ) (resonanceEvent ν (thicken D (4 * R) ∩ Λ) E
        (Real.exp (-Real.sqrt R))) ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
          (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) *
        (11 ^ ν * (1 + R) ^ ν) * Real.exp (-Real.sqrt R / 2)) := by
  have hκ : Real.exp (-Real.sqrt R) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := Real.sqrt_nonneg R; linarith only [this])
  have h := (resonance_bound_gaussian ν (thicken D (4 * R) ∩ Λ) hγ E hκ).2
  refine h.trans ?_
  have hc := card_thicken_inter_le Λ D hR hdiam
  have hT : 0 ≤ 1 / Real.sqrt (2 * Real.pi * γ) *
      (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1} := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [sqrt_two_mul_exp_neg_sqrt]
  calc _ ≤ Real.sqrt 2 * Real.exp (-Real.sqrt R / 2) * Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
          (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) *
        (11 ^ ν * (1 + R) ^ ν) := by gcongr
    _ = _ := by ring


private theorem eq_chainCluster_of_gentle {ν : ℕ} (P : Params) (hK : 0 ≤ P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (i : ℕ) (D : Finset (Site ν))
    (hD : (D : Set (Site ν)) ∈ chainClusters (siteDist ν) (singularSetsIn P Λ v (i + 1))
      (2 * scaleR P.K₀ (i + 1)))
    (hdiam : DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD P.K₀ i)) :
    ∃ x ∈ (D : Set (Site ν)), (D : Set (Site ν)) =
      chainCluster (siteDist ν) (singularSetsIn P Λ v i) (2 * scaleR P.K₀ i) x := by
  obtain ⟨x, hxS, hDx⟩ := hD
  have hxD : x ∈ (D : Set (Site ν)) := hDx ▸ mem_chainCluster_self hxS
  refine ⟨x, hxD, ?_⟩
  have hsub : (D : Set (Site ν)) ⊆ singularSetsIn P Λ v (i + 1) := hDx ▸ chainCluster_subset x
  have hsubi : singularSetsIn P Λ v (i + 1) ⊆ singularSetsIn P Λ v i :=
    singularSetsGen_antitone P _ _ v (Nat.le_succ i)
  have hlt : scaleD P.K₀ i < 2 * scaleR P.K₀ i := by
    have := scaleD_le_scaleR hK i
    have := scaleD_pos P.K₀ i
    linarith
  have hr : scaleR P.K₀ i ≤ scaleR P.K₀ (i + 1) := by
    rw [scaleR_eq_scaleD_succ, scaleR_eq_scaleD_succ]
    exact scaleD_mono_of_nonneg hK (Nat.le_succ _)
  rw [eq_chainCluster_iff hxD]
  refine ⟨hsub.trans hsubi, ?_, ?_⟩
  · intro c hc y hy hcy
    by_cases hyS : y ∈ singularSetsIn P Λ v (i + 1)
    · by_contra hyD
      have := two_mul_scaleR_le_siteDist P (S := singularSetsIn P Λ v (i + 1))
        (C := (D : Set (Site ν))) ⟨x, hxS, hDx⟩ hc hyS hyD
      linarith only [hr, hcy, this]
    · have hg := (mem_singularSetsGen_succ_iff P _ _ v i y).not.1 hyS
      have hyg : IsGentle P (fun B => B ∩ Λ) i v
          (chainCluster (siteDist ν) (singularSetsIn P Λ v i) (2 * scaleR P.K₀ i) y) := by
        by_contra hng
        exact hg ⟨hy, hng⟩
      have hcy' : c ∈ chainCluster (siteDist ν) (singularSetsIn P Λ v i)
          (2 * scaleR P.K₀ i) y :=
        mem_chainCluster_of_lt (mem_chainCluster_self hy) (hsubi (hsub hc))
          (by rw [siteDist_comm]; exact hcy)
      have hcc := chainCluster_eq_of_mem (siteDist_comm ν) hcy'
      have := (mem_singularSetsGen_succ_iff P _ _ v i c).1 (hsub hc)
      exact absurd (hcc ▸ hyg) this.2
  · intro c hc
    exact Relation.ReflTransGen.single ⟨hxD, hc, lt_of_le_of_lt (hdiam x hxD c hc) hlt⟩


theorem gentleEventIn_subset_resonanceEvent {ν : ℕ} (P : Params) (hK : 0 ≤ P.K₀)
    (Λ D : Finset (Site ν)) {j : ℕ} (hj : 1 ≤ j)
    (hdiam : DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD P.K₀ (j - 1))) :
    gentleEventIn P Λ D j ⊆
      resonanceEvent ν (thicken D (4 * scaleD P.K₀ (j - 1)) ∩ Λ) P.E
        (Real.exp (-Real.sqrt (scaleD P.K₀ (j - 1)))) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hdiam ⊢
  intro v hv
  have hD := ((mem_gentleEventIn P Λ D (i + 1) v).1 hv).1
  obtain ⟨x, hxD, hDx⟩ := eq_chainCluster_of_gentle P hK Λ v i D hD hdiam
  have hxS : x ∈ singularSetsIn P Λ v (i + 1) := by
    obtain ⟨y, hy, hyD⟩ := hD
    rw [hyD] at hxD
    exact chainCluster_subset y hxD
  have hng := ((mem_singularSetsGen_succ_iff P _ _ v i x).1 hxS).2
  have hng' : ¬ IsGentle P (fun B => B ∩ Λ) i v (D : Set (Site ν)) := by
    rw [hDx]; exact hng
  by_contra hres
  apply hng'
  have key : ∀ B : Finset (Site ν), B = D →
      (∀ k, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
        |(hamiltonian_isHermitian ν (thicken D (4 * scaleD P.K₀ i) ∩ Λ) v).eigenvalues k -
          P.E|) →
      ∀ k, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
        |(hamiltonian_isHermitian ν (thicken B (4 * scaleD P.K₀ i) ∩ Λ) v).eigenvalues k -
          P.E| := by
    intro B hB h
    subst hB
    exact h
  refine ⟨D.finite_toSet, hdiam, ?_⟩
  refine key _ (Finset.finite_toSet_toFinset D) ?_
  intro k
  by_contra hk
  exact hres ⟨k, (not_le.1 hk).le⟩


theorem measure_gentleEventIn_le_sqrt {ν : ℕ} (law : Measure ℝ) [IsProbabilityMeasure law]
    (P : Params) (hK : 0 ≤ P.K₀) (Λ D : Finset (Site ν)) {j : ℕ} (hj : 1 ≤ j)
    (hdiam : DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD P.K₀ (j - 1))) :
    configurationMeasure ν law (gentleEventIn P Λ D j) ≤
      (configurationMeasure ν law (resonanceEvent ν (thicken D (4 * scaleD P.K₀ (j - 1)) ∩ Λ)
          P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (j - 1))))) *
        configurationMeasure ν law (gentleEventAnyIn P Λ D)) ^ (1 / 2 : ℝ) := by
  set μ := configurationMeasure ν law
  set a := μ (gentleEventIn P Λ D j)
  have h1 : a ≤ μ (resonanceEvent ν (thicken D (4 * scaleD P.K₀ (j - 1)) ∩ Λ)
          P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (j - 1))))) :=
    measure_mono (gentleEventIn_subset_resonanceEvent P hK Λ D hj hdiam)
  have h2 : a ≤ μ (gentleEventAnyIn P Λ D) :=
    measure_mono (gentleEventIn_subset_any P Λ D j)
  have h3 : a ^ (2 : ℝ) ≤ μ (resonanceEvent ν (thicken D (4 * scaleD P.K₀ (j - 1)) ∩ Λ)
          P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (j - 1))))) *
        μ (gentleEventAnyIn P Λ D) := by
    rw [ENNReal.rpow_two, sq]
    exact mul_le_mul' h1 h2
  calc a = (a ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow h3 (by norm_num)

end FroehlichSpencer.T12

end
