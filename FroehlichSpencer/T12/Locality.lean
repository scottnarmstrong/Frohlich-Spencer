/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Multiscale.Measurability
public import FroehlichSpencer.T12.Events

/-!
# Finite-level locality of singular and gentle events

The radius uses `R₀ = 0`, `Rᵢ₊₁ = Rᵢ + ceil(dᵢ + 2 rᵢ + 2)` under `dᵢ ≥ 40`.

Accordingly,
the gentle-part events below use radius `Rᵢ₊₁`, while `Sᵢ` uses `Rᵢ`.
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.T12

open Multiscale


noncomputable def multiscaleLocalityRadius (P : Params) : ℕ → ℝ
  | 0 => 0
  | i + 1 => multiscaleLocalityRadius P i +
      (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ)

theorem multiscaleLocalityRadius_zero (P : Params) :
    multiscaleLocalityRadius P 0 = 0 := rfl

theorem multiscaleLocalityRadius_succ (P : Params) (i : ℕ) :
    multiscaleLocalityRadius P (i + 1) = multiscaleLocalityRadius P i +
      (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) := rfl

theorem multiscaleLocalityRadius_nonneg (P : Params) (i : ℕ) :
    0 ≤ multiscaleLocalityRadius P i := by
  induction i with
  | zero => simp [multiscaleLocalityRadius]
  | succ i ih =>
      rw [multiscaleLocalityRadius_succ]
      exact add_nonneg ih (show (0 : ℝ) ≤
        (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) from by exact_mod_cast
          (Nat.zero_le (Nat.ceil (scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2))))

theorem multiscaleLocalityRadius_mono (P : Params) :
    Monotone (multiscaleLocalityRadius P) :=
  monotone_nat_of_le_succ fun i => by
    rw [multiscaleLocalityRadius_succ]
    exact le_add_of_nonneg_right (show (0 : ℝ) ≤
      (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) from by exact_mod_cast
        (Nat.zero_le (Nat.ceil (scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2))))

private theorem five_scaleD_le_two_scaleR (P : Params) (i : ℕ)
    (hD : 40 ≤ scaleD P.K₀ i) :
    5 * scaleD P.K₀ i ≤ 2 * scaleR P.K₀ i := by
  set d := scaleD P.K₀ i
  have hdpos : 0 < d := scaleD_pos P.K₀ i
  have hquarter : (5 / 2 : ℝ) ^ 4 ≤ d := by norm_num; linarith
  have hroot0 := Real.rpow_le_rpow (by positivity : 0 ≤ (5 / 2 : ℝ) ^ 4)
    hquarter (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hrootEq : ((5 / 2 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = 5 / 2 := by
    rw [show (5 / 2 : ℝ) ^ 4 = (5 / 2 : ℝ) ^ (4 : ℝ) by
      exact (Real.rpow_natCast (5 / 2 : ℝ) 4).symm]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (5 / 2 : ℝ))]
    norm_num
  have hroot : (5 / 2 : ℝ) ≤ d ^ (1 / 4 : ℝ) := by
    rw [← hrootEq]
    exact hroot0
  have hpow : scaleR P.K₀ i = d * d ^ (1 / 4 : ℝ) := by
    unfold scaleR
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hdpos,
      Real.rpow_one]
  rw [hpow]
  nlinarith

private theorem localityRadius_step_bounds (P : Params) (i : ℕ)
    (hD : 40 ≤ scaleD P.K₀ i) :
    5 * scaleD P.K₀ i ≤
        (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) ∧
      scaleD P.K₀ i + 2 * scaleR P.K₀ i <
        (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) := by
  have hgeom := five_scaleD_le_two_scaleR P i hD
  constructor
  · calc
      5 * scaleD P.K₀ i ≤ 2 * scaleR P.K₀ i := hgeom
      _ ≤ scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2 := by linarith [scaleD_pos P.K₀ i]
      _ ≤ (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) := Nat.le_ceil _
  · have hceil : scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2 ≤
        (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) := Nat.le_ceil _
    linarith

private theorem eigenvalues_congr_locality {n : Type*} [Fintype n] [DecidableEq n]
    {A A' : Matrix n n ℂ} (hA : A.IsHermitian) (hA' : A'.IsHermitian) (h : A = A') :
    hA.eigenvalues = hA'.eigenvalues := by
  subst h
  rfl

private theorem isGentle_transfer_locality {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (hblk : ∀ B, blk B ⊆ B)
    (support : Set (Site ν)) (hblkSupport : ∀ B y, y ∈ blk B → y ∈ support) (i : ℕ)
    {v w : Site ν → ℝ} {C : Set (Site ν)} {x : Site ν} (hx : x ∈ C)
    (hR : 5 * scaleD P.K₀ i ≤ multiscaleLocalityRadius P (i + 1))
    (hvw : ∀ y ∈ support,
      siteDist ν x y ≤ multiscaleLocalityRadius P (i + 1) → v y = w y)
    (hg : IsGentle P blk i v C) : IsGentle P blk i w C := by
  obtain ⟨hC, hd, he⟩ := hg
  refine ⟨hC, hd, fun j => ?_⟩
  have hB : ∀ y ∈ blk (thicken hC.toFinset (4 * scaleD P.K₀ i)), v y = w y := by
    intro y hy
    obtain ⟨c, hc, hyc⟩ := mem_thicken.1 (hblk _ hy)
    have hcC : c ∈ C := hC.mem_toFinset.1 hc
    have hxc := hd x hx c hcC
    apply hvw y (hblkSupport _ y hy)
    have htriangle := siteDist_triangle ν x y c
    have hcomm := siteDist_comm ν y c
    rw [multiscaleLocalityRadius_succ] at hR
    have hdist : siteDist ν x y ≤ multiscaleLocalityRadius P i +
        (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) := by
      calc
        siteDist ν x y ≤ siteDist ν x c + siteDist ν c y := htriangle
        _ ≤ scaleD P.K₀ i + 4 * scaleD P.K₀ i := by rw [← hcomm]; linarith
        _ = 5 * scaleD P.K₀ i := by ring
        _ ≤ multiscaleLocalityRadius P i +
            (⌈scaleD P.K₀ i + 2 * scaleR P.K₀ i + 2⌉₊ : ℝ) := hR
    exact hdist
  have heq := hamiltonian_congr (blk (thicken hC.toFinset (4 * scaleD P.K₀ i))) hB
  have heigen := eigenvalues_congr_locality (hamiltonian_isHermitian ν _ v)
    (hamiltonian_isHermitian ν _ w) heq
  exact le_of_le_of_eq (he j) (by rw [congrFun heigen j])

private theorem singularSetsGen_congr_locality {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (hblk : ∀ B, blk B ⊆ B)
    (support : Set (Site ν)) (hblkSupport : ∀ B y, y ∈ blk B → y ∈ support)
    (S₀ S₀' : (Site ν → ℝ) → Set (Site ν))
    (hS₀sub : ∀ v, S₀ v ⊆ support) (hS₀'sub : ∀ v, S₀' v ⊆ support)
    (hS₀ : ∀ y ∈ support, ∀ v w, v y = w y → (y ∈ S₀ v ↔ y ∈ S₀' w))
    (hD : ∀ i, 40 ≤ scaleD P.K₀ i) (i : ℕ) {v w : Site ν → ℝ} {x : Site ν}
    (hvw : ∀ y ∈ support, siteDist ν x y ≤ multiscaleLocalityRadius P i → v y = w y) :
    (x ∈ singularSetsGen P blk (S₀ v) v i ↔
      x ∈ singularSetsGen P blk (S₀' w) w i) := by
  induction i generalizing x with
  | zero =>
      by_cases hx : x ∈ support
      · exact hS₀ x hx v w (hvw x hx (by simp [multiscaleLocalityRadius, siteDist_self]))
      · have h1 : x ∉ S₀ v := fun hxS => hx (hS₀sub v hxS)
        have h2 : x ∉ S₀' w := fun hxS => hx (hS₀'sub w hxS)
        simp [singularSetsGen, h1, h2]
  | succ i ih =>
      have hstep := localityRadius_step_bounds P i (hD i)
      have hprev : x ∈ singularSetsGen P blk (S₀ v) v i ↔
          x ∈ singularSetsGen P blk (S₀' w) w i := by
        by_cases hx : x ∈ support
        · apply ih
          intro y hySupport hy
          apply hvw y hySupport
          rw [multiscaleLocalityRadius_succ]
          exact hy.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
        · have h1 : x ∉ singularSetsGen P blk (S₀ v) v i :=
            fun hxS => hx (hS₀sub v (singularSetsGen_subset_zero P blk (S₀ v) v i hxS))
          have h2 : x ∉ singularSetsGen P blk (S₀' w) w i :=
            fun hxS => hx (hS₀'sub w (singularSetsGen_subset_zero P blk (S₀' w) w i hxS))
          simp [h1, h2]
      let S := singularSetsGen P blk (S₀ v) v i
      let S' := singularSetsGen P blk (S₀' w) w i
      have hgentle : x ∈ S →
          (IsGentle P blk i v (chainCluster (siteDist ν) S (2 * scaleR P.K₀ i) x) ↔
            IsGentle P blk i w (chainCluster (siteDist ν) S' (2 * scaleR P.K₀ i) x)) := by
        intro hx
        have hSS' : ∀ y, siteDist ν x y < scaleD P.K₀ i + 2 * scaleR P.K₀ i →
            (y ∈ S ↔ y ∈ S') := by
          intro y hy
          by_cases hySupport : y ∈ support
          · apply ih
            intro z hzSupport hz
            apply hvw z hzSupport
            rw [multiscaleLocalityRadius_succ]
            have htri := siteDist_triangle ν x z y
            have hsum := add_lt_add_of_lt_of_le hy hz
            linarith [htri, hsum, hstep.2]
          · have h1 : y ∉ S := fun hyS => hySupport
              (hS₀sub v (singularSetsGen_subset_zero P blk (S₀ v) v i hyS))
            have h2 : y ∉ S' := fun hyS => hySupport
              (hS₀'sub w (singularSetsGen_subset_zero P blk (S₀' w) w i hyS))
            simp [S, S', h1, h2]
        have hR : 5 * scaleD P.K₀ i ≤ multiscaleLocalityRadius P (i + 1) := by
          rw [multiscaleLocalityRadius_succ]
          linarith [hstep.1, multiscaleLocalityRadius_nonneg P i]
        constructor
        · intro hg
          rcases hg with ⟨hfinite, hdiam, he⟩
          have hρ : 0 < 2 * scaleR P.K₀ i := mul_pos (by norm_num) (scaleR_pos P.K₀ i)
          have hcluster' := chainCluster_eq_of_eqOn_ball (siteDist_triangle ν)
            (siteDist_self ν) hρ (S' := S') (x := x)
            (D := scaleD P.K₀ i) hx hdiam hSS'
          rw [hcluster']
          exact isGentle_transfer_locality P blk hblk support hblkSupport i
            (mem_chainCluster_self hx) hR hvw ⟨hfinite, hdiam, he⟩
        · intro hg
          rcases hg with ⟨hfinite, hdiam, he⟩
          have hρ : 0 < 2 * scaleR P.K₀ i := mul_pos (by norm_num) (scaleR_pos P.K₀ i)
          have hcluster' := chainCluster_eq_of_eqOn_ball (siteDist_triangle ν)
            (siteDist_self ν) hρ (S' := S) (x := x)
            (D := scaleD P.K₀ i) (hprev.1 hx) hdiam (fun y hy => (hSS' y hy).symm)
          rw [hcluster']
          exact isGentle_transfer_locality P blk hblk support hblkSupport i
            (mem_chainCluster_self (hprev.1 hx)) hR
            (fun y hySupport hyDist => (hvw y hySupport hyDist).symm)
            ⟨hfinite, hdiam, he⟩
      rw [mem_singularSetsGen_succ_iff, mem_singularSetsGen_succ_iff]
      change (x ∈ S ∧ ¬ IsGentle P blk i v
          (chainCluster (siteDist ν) S (2 * scaleR P.K₀ i) x)) ↔
        (x ∈ S' ∧ ¬ IsGentle P blk i w
          (chainCluster (siteDist ν) S' (2 * scaleR P.K₀ i) x))
      constructor
      · rintro ⟨hx, hnot⟩
        exact ⟨hprev.1 hx, (not_congr (hgentle hx)).1 hnot⟩
      · rintro ⟨hx', hnot⟩
        have hx : x ∈ S := hprev.mpr hx'
        exact ⟨hx, (not_congr (hgentle hx)).2 hnot⟩

private theorem mem_gentlePart_iff_cluster {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (S₀ : Set (Site ν)) (v : Site ν → ℝ)
    (i : ℕ) (x : Site ν) :
    x ∈ gentlePart P blk i v (singularSetsGen P blk S₀ v i) ↔
      x ∈ singularSetsGen P blk S₀ v i ∧ IsGentle P blk i v
        (chainCluster (siteDist ν) (singularSetsGen P blk S₀ v i)
          (2 * scaleR P.K₀ i) x) := by
  constructor
  · rintro ⟨C, ⟨⟨y, hy, rfl⟩, hg⟩, hx⟩
    refine ⟨gentlePart_subset P blk v i _ ⟨_, ⟨⟨y, hy, rfl⟩, hg⟩, hx⟩, ?_⟩
    rwa [chainCluster_eq_of_mem (siteDist_comm ν) hx]
  · rintro ⟨hx, hg⟩
    exact ⟨_, ⟨⟨x, hx, rfl⟩, hg⟩, mem_chainCluster_self hx⟩

private theorem mem_gentlePart_iff_singular_difference {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (S₀ : Set (Site ν)) (v : Site ν → ℝ)
    (i : ℕ) (x : Site ν) :
    x ∈ gentlePart P blk i v (singularSetsGen P blk S₀ v i) ↔
      x ∈ singularSetsGen P blk S₀ v i ∧
        x ∉ singularSetsGen P blk S₀ v (i + 1) := by
  rw [mem_gentlePart_iff_cluster, mem_singularSetsGen_succ_iff]
  tauto

private theorem singular0_agree {ν : ℕ} (P : Params) (y : Site ν)
    {v w : Site ν → ℝ} (h : v y = w y) :
    (y ∈ singular0 P v ↔ y ∈ singular0 P w) := by
  simp only [mem_singular0, h]

private theorem singular0In_agree {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (y : Site ν)
    {v w : Site ν → ℝ} (h : v y = w y) :
    (y ∈ singular0 P v ∩ (Λ : Set (Site ν)) ↔
      y ∈ singular0 P w ∩ (Λ : Set (Site ν))) := by
  simp only [Set.mem_inter_iff, mem_singular0, h]

private theorem measurableSet_mem_gentlePart {ν : ℕ} (P : Params) (i : ℕ) (x : Site ν) :
    MeasurableSet {v : Configuration ν |
      x ∈ gentlePart P id i v (singularSets P v i)} := by
  have hEq : {v : Configuration ν | x ∈ gentlePart P id i v (singularSets P v i)} =
      {v | x ∈ singularSets P v i} ∩ {v | x ∈ singularSets P v (i + 1)}ᶜ := by
    ext v
    exact mem_gentlePart_iff_singular_difference P id (singular0 P v) v i x
  rw [hEq]
  exact (measurableSet_mem_singularSets P x i).inter
    (measurableSet_mem_singularSets P x (i + 1)).compl

private theorem measurableSet_mem_gentlePartIn {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (i : ℕ) (x : Site ν) :
    MeasurableSet {v : Configuration ν |
      x ∈ gentlePart P (fun B => B ∩ Λ) i v (singularSetsIn P Λ v i)} := by
  have hEq : {v : Configuration ν |
      x ∈ gentlePart P (fun B => B ∩ Λ) i v (singularSetsIn P Λ v i)} =
      {v | x ∈ singularSetsIn P Λ v i} ∩
        {v | x ∈ singularSetsIn P Λ v (i + 1)}ᶜ := by
    ext v
    exact mem_gentlePart_iff_singular_difference P (fun B => B ∩ Λ)
      (singular0 P v ∩ Λ) v i x
  rw [hEq]
  exact (measurableSet_mem_singularSetsIn P Λ x i).inter
    (measurableSet_mem_singularSetsIn P Λ x (i + 1)).compl


theorem measurableSet_and_dependsOn_mem_singularSets_locality {ν : ℕ} (P : Params)
    (hD : ∀ i, 40 ≤ scaleD P.K₀ i) (i : ℕ) (x : Site ν) :
    MeasurableSet {v : Configuration ν | x ∈ singularSets P v i} ∧
      Infra.DependsOn {y | siteDist ν x y ≤ multiscaleLocalityRadius P i}
        {v : Configuration ν | x ∈ singularSets P v i} := by
  refine ⟨measurableSet_mem_singularSets P x i, ?_⟩
  apply Infra.dependsOn_of_measurable_of_invariant (measurableSet_mem_singularSets P x i)
  intro v w hvw
  exact singularSetsGen_congr_locality P id (fun _ => le_rfl) Set.univ
    (fun _ y _ => Set.mem_univ y)
    (singular0 P) (singular0 P) (fun _ => Set.subset_univ _) (fun _ => Set.subset_univ _)
    (fun y _ v w heq => singular0_agree P y heq) hD i (fun y _ hy => hvw y hy)

/--
The index shift is required by the level-`i` block Hamiltonian test.
-/
theorem measurableSet_and_dependsOn_mem_gentlePart_locality {ν : ℕ} (P : Params)
    (hD : ∀ i, 40 ≤ scaleD P.K₀ i) (i : ℕ) (x : Site ν) :
    MeasurableSet {v : Configuration ν |
      x ∈ gentlePart P id i v (singularSets P v i)} ∧
      Infra.DependsOn {y | siteDist ν x y ≤ multiscaleLocalityRadius P (i + 1)}
        {v : Configuration ν | x ∈ gentlePart P id i v (singularSets P v i)} := by
  refine ⟨measurableSet_mem_gentlePart P i x, ?_⟩
  apply Infra.dependsOn_of_measurable_of_invariant (measurableSet_mem_gentlePart P i x)
  intro v w hvw
  have hi := singularSetsGen_congr_locality P id (fun _ => le_rfl) Set.univ
    (fun _ y _ => Set.mem_univ y)
    (singular0 P) (singular0 P) (fun _ => Set.subset_univ _) (fun _ => Set.subset_univ _)
    (fun y _ v w heq => singular0_agree P y heq) hD i (fun y _ hy => by
      apply hvw y
      exact hy.trans (multiscaleLocalityRadius_mono P (Nat.le_succ i)))
  have hi' := singularSetsGen_congr_locality P id (fun _ => le_rfl) Set.univ
    (fun _ y _ => Set.mem_univ y)
    (singular0 P) (singular0 P) (fun _ => Set.subset_univ _) (fun _ => Set.subset_univ _)
    (fun y _ v w heq => singular0_agree P y heq) hD (i + 1) (fun y _ hy => hvw y hy)
  change (x ∈ gentlePart P id i v (singularSetsGen P id (singular0 P v) v i) ↔
      x ∈ gentlePart P id i w (singularSetsGen P id (singular0 P w) w i))
  rw [mem_gentlePart_iff_singular_difference, mem_gentlePart_iff_singular_difference]
  exact and_congr hi (not_congr hi')


theorem measurableSet_and_dependsOn_mem_singularSetsIn_locality {ν : ℕ} (P : Params)
    (hD : ∀ i, 40 ≤ scaleD P.K₀ i) (Λ : Finset (Site ν)) (i : ℕ) (x : Site ν) :
    MeasurableSet {v : Configuration ν | x ∈ singularSetsIn P Λ v i} ∧
      Infra.DependsOn ({y | siteDist ν x y ≤ multiscaleLocalityRadius P i} ∩
        (Λ : Set (Site ν))) {v : Configuration ν | x ∈ singularSetsIn P Λ v i} := by
  refine ⟨measurableSet_mem_singularSetsIn P Λ x i, ?_⟩
  apply Infra.dependsOn_of_measurable_of_invariant
    (measurableSet_mem_singularSetsIn P Λ x i)
  intro v w hvw
  exact singularSetsGen_congr_locality P (fun B => B ∩ Λ)
    (fun _ => Finset.inter_subset_left) (Λ : Set (Site ν))
    (fun _ y hy => (Finset.mem_inter.1 hy).2)
    (fun v => singular0 P v ∩ Λ) (fun v => singular0 P v ∩ Λ)
    (fun _ => Set.inter_subset_right) (fun _ => Set.inter_subset_right)
    (fun y hyΛ v w heq => singular0In_agree P Λ y heq) hD i
    (fun y hyΛ hyDist => hvw y ⟨hyDist, hyΛ⟩)

/--
The index
shift is required by the level-`i` block Hamiltonian test.
-/
theorem measurableSet_and_dependsOn_mem_gentlePartIn_locality {ν : ℕ} (P : Params)
    (hD : ∀ i, 40 ≤ scaleD P.K₀ i) (Λ : Finset (Site ν)) (i : ℕ) (x : Site ν) :
    MeasurableSet {v : Configuration ν |
      x ∈ gentlePart P (fun B => B ∩ Λ) i v (singularSetsIn P Λ v i)} ∧
      Infra.DependsOn ({y | siteDist ν x y ≤ multiscaleLocalityRadius P (i + 1)} ∩
        (Λ : Set (Site ν)))
        {v : Configuration ν |
          x ∈ gentlePart P (fun B => B ∩ Λ) i v (singularSetsIn P Λ v i)} := by
  refine ⟨measurableSet_mem_gentlePartIn P Λ i x, ?_⟩
  apply Infra.dependsOn_of_measurable_of_invariant
    (measurableSet_mem_gentlePartIn P Λ i x)
  intro v w hvw
  have hS₀sub : ∀ v, (singular0 P v ∩ (Λ : Set (Site ν))) ⊆ (Λ : Set (Site ν)) :=
    fun _ => Set.inter_subset_right
  have hS₀ : ∀ y ∈ (Λ : Set (Site ν)), ∀ v w,
      v y = w y → (y ∈ singular0 P v ∩ (Λ : Set (Site ν)) ↔
        y ∈ singular0 P w ∩ (Λ : Set (Site ν))) :=
    fun y _ v w heq => singular0In_agree P Λ y heq
  have hrec (j : ℕ) (hj : j = i ∨ j = i + 1) :
      (x ∈ singularSetsIn P Λ v j ↔ x ∈ singularSetsIn P Λ w j) := by
    have hrad : multiscaleLocalityRadius P j ≤ multiscaleLocalityRadius P (i + 1) := by
      have hji : j ≤ i + 1 := by omega
      exact multiscaleLocalityRadius_mono P hji
    exact singularSetsGen_congr_locality P (fun B => B ∩ Λ)
      (fun _ => Finset.inter_subset_left) (Λ : Set (Site ν))
      (fun _ y hy => (Finset.mem_inter.1 hy).2)
      (fun v => singular0 P v ∩ Λ) (fun v => singular0 P v ∩ Λ)
      (fun _ => Set.inter_subset_right) (fun _ => Set.inter_subset_right)
      (fun y hyΛ v w heq => hS₀ y hyΛ v w heq) hD j
      (fun y hyΛ hyDist => by
        apply hvw y
        exact ⟨hyDist.trans hrad, hyΛ⟩)
  have hi := hrec i (Or.inl rfl)
  have hi' := hrec (i + 1) (Or.inr rfl)
  change (x ∈ gentlePart P (fun B => B ∩ Λ) i v
      (singularSetsGen P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v i) ↔
    x ∈ gentlePart P (fun B => B ∩ Λ) i w
      (singularSetsGen P (fun B => B ∩ Λ) (singular0 P w ∩ Λ) w i))
  rw [mem_gentlePart_iff_singular_difference, mem_gentlePart_iff_singular_difference]
  exact and_congr hi (not_congr hi')
