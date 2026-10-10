/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Multiscale.Singular

/-!
# Locality of the singular sets

Membership `x ∈ S_i(v)` depends only on `v` on the closed ball of radius `R_i` around `x`,
where `R_0 = 0` and `R_{i+1} = R_i + 5 d_i + 2 r_i`.
-/

@[expose] public section

namespace FroehlichSpencer.Multiscale

/-- Locality radii: `R_0 = 0`, `R_{i+1} = R_i + 5 d_i + 2 r_i`. -/
noncomputable def localityRadius (K₀ : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => localityRadius K₀ i + 5 * scaleD K₀ i + 2 * scaleR K₀ i

theorem localityRadius_nonneg (K₀ : ℝ) (i : ℕ) : 0 ≤ localityRadius K₀ i := by
  induction i with
  | zero => simp [localityRadius]
  | succ i ih =>
    have := scaleD_pos K₀ i
    have := scaleR_pos K₀ i
    simp only [localityRadius]
    linarith

theorem localityRadius_mono (K₀ : ℝ) : Monotone (localityRadius K₀) :=
  monotone_nat_of_le_succ fun i => by
    have := scaleD_pos K₀ i
    have := scaleR_pos K₀ i
    simp only [localityRadius]
    linarith

private theorem sixteen_le_scaleD {K₀ : ℝ} (hK : Real.log 16 ≤ K₀) (i : ℕ) :
    16 ≤ scaleD K₀ i := by
  have h16 : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
  have hp : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  unfold scaleD
  calc (16 : ℝ) = Real.exp (Real.log 16) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (K₀ * (5 / 4 : ℝ) ^ i) := Real.exp_le_exp.mpr (by nlinarith)

private theorem two_mul_scaleD_le_succ {K₀ : ℝ} (hK : Real.log 16 ≤ K₀) (i : ℕ) :
    2 * scaleD K₀ i ≤ scaleD K₀ (i + 1) := by
  have h16 := sixteen_le_scaleD hK i
  have hpos := scaleD_pos K₀ i
  rw [← scaleR_eq_scaleD_succ]
  unfold scaleR
  have h1 : scaleD K₀ i ^ (5 / 4 : ℝ) = scaleD K₀ i * scaleD K₀ i ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hpos, Real.rpow_one]
  have h2 : (2 : ℝ) ≤ scaleD K₀ i ^ (1 / 4 : ℝ) := by
    have : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [this]
    exact Real.rpow_le_rpow (by norm_num) h16 (by norm_num)
  rw [h1]
  nlinarith

theorem localityRadius_le {K₀ : ℝ} (hK : Real.log 16 ≤ K₀) (i : ℕ) :
    localityRadius K₀ i ≤ 9 * scaleD K₀ i := by
  induction i with
  | zero =>
    have := scaleD_pos K₀ 0
    simp only [localityRadius]
    linarith
  | succ i ih =>
    have h2 := two_mul_scaleD_le_succ hK i
    rw [← scaleR_eq_scaleD_succ] at h2 ⊢
    simp only [localityRadius]
    linarith

private theorem eigenvalues_congr {n : Type*} [Fintype n] [DecidableEq n]
    {A A' : Matrix n n ℂ} (hA : A.IsHermitian) (hA' : A'.IsHermitian) (h : A = A') :
    hA.eigenvalues = hA'.eigenvalues := by
  subst h
  rfl

private theorem isGentle_transfer {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (hblk : ∀ B, blk B ⊆ B) (i : ℕ)
    {v w : Site ν → ℝ} {C : Set (Site ν)} {x : Site ν} (hx : x ∈ C) {R : ℝ}
    (hR : 5 * scaleD P.K₀ i ≤ R) (hvw : ∀ y, siteDist ν x y ≤ R → v y = w y)
    (hg : IsGentle P blk i v C) : IsGentle P blk i w C := by
  obtain ⟨hC, hd, he⟩ := hg
  refine ⟨hC, hd, fun j => ?_⟩
  have hB : ∀ y ∈ blk (thicken hC.toFinset (4 * scaleD P.K₀ i)), v y = w y := by
    intro y hy
    obtain ⟨c, hc, hyc⟩ := mem_thicken.1 (hblk _ hy)
    have hcC : c ∈ C := hC.mem_toFinset.1 hc
    have hxc := hd x hx c hcC
    apply hvw
    have := siteDist_triangle ν x y c
    rw [siteDist_comm ν c y] at this
    have h2 := siteDist_triangle ν x y c
    linarith [siteDist_comm ν y c]
  have e := eigenvalues_congr (hamiltonian_isHermitian ν _ v) (hamiltonian_isHermitian ν _ w)
    (hamiltonian_congr _ hB)
  exact le_of_le_of_eq (he j) (by rw [congrFun e j])

private theorem mem_singularSetsGen_congr {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (hblk : ∀ B, blk B ⊆ B) (i : ℕ) :
    ∀ (v w : Site ν → ℝ) (S₀ S₀' : Set (Site ν)),
      (∀ y, v y = w y → (y ∈ S₀ ↔ y ∈ S₀')) → ∀ x : Site ν,
      (∀ y, siteDist ν x y ≤ localityRadius P.K₀ i → v y = w y) →
      (x ∈ singularSetsGen P blk S₀ v i ↔ x ∈ singularSetsGen P blk S₀' w i) := by
  induction i with
  | zero =>
    intro v w S₀ S₀' h0 x h
    exact h0 x (h x (by simp [localityRadius, siteDist_self]))
  | succ i ih =>
    have hd := scaleD_pos P.K₀ i
    have hr := scaleR_pos P.K₀ i
    have hRi := localityRadius_nonneg P.K₀ i
    have dir : ∀ (v w : Site ν → ℝ) (S₀ S₀' : Set (Site ν)),
        (∀ y, v y = w y → (y ∈ S₀ ↔ y ∈ S₀')) → ∀ x : Site ν,
        (∀ y, siteDist ν x y ≤ localityRadius P.K₀ (i + 1) → v y = w y) →
        x ∈ singularSetsGen P blk S₀ v i →
        IsGentle P blk i v (chainCluster (siteDist ν) (singularSetsGen P blk S₀ v i)
          (2 * scaleR P.K₀ i) x) →
        IsGentle P blk i w (chainCluster (siteDist ν) (singularSetsGen P blk S₀' w i)
          (2 * scaleR P.K₀ i) x) := by
      intro v w S₀ S₀' h0 x h hx hg
      have hR : localityRadius P.K₀ (i + 1) =
          localityRadius P.K₀ i + 5 * scaleD P.K₀ i + 2 * scaleR P.K₀ i := rfl
      obtain ⟨hC, hdiam, -⟩ := id hg
      have hdiam' := hdiam
      have heq := chainCluster_eq_of_eqOn_ball (siteDist_triangle ν) (siteDist_self ν)
        (ρ := 2 * scaleR P.K₀ i) (by linarith) (S' := singularSetsGen P blk S₀' w i) hx hdiam
        (fun y hy => by
          apply ih v w S₀ S₀' h0 y
          intro z hz
          apply h
          have := siteDist_triangle ν x z y
          have h3 := siteDist_comm ν z y
          linarith)
      rw [heq]
      exact isGentle_transfer P blk hblk i (mem_chainCluster_self hx) (R :=
        localityRadius P.K₀ (i + 1)) (by linarith) h hg
    intro v w S₀ S₀' h0 x h
    have hx : x ∈ singularSetsGen P blk S₀ v i ↔ x ∈ singularSetsGen P blk S₀' w i :=
      ih v w S₀ S₀' h0 x fun y hy => h y (hy.trans (localityRadius_mono P.K₀ (Nat.le_succ i)))
    rw [mem_singularSetsGen_succ_iff, mem_singularSetsGen_succ_iff]
    by_cases hv : x ∈ singularSetsGen P blk S₀ v i
    · have hw := hx.1 hv
      have hsymm : ∀ y, w y = v y → (y ∈ S₀' ↔ y ∈ S₀) := fun y hy => (h0 y hy.symm).symm
      have hg2 := dir w v S₀' S₀ hsymm x (fun y hy => (h y hy).symm) hw
      simp only [hv, hw, true_and]
      exact not_congr ⟨dir v w S₀ S₀' h0 x h hv, hg2⟩
    · simp [hv, hx.not.1 hv]

theorem mem_singularSets_congr {ν : ℕ} (P : Params) {v w : Site ν → ℝ} {x : Site ν} {i : ℕ}
    (h : ∀ y, siteDist ν x y ≤ localityRadius P.K₀ i → v y = w y) :
    x ∈ singularSets P v i ↔ x ∈ singularSets P w i :=
  mem_singularSetsGen_congr P id (fun _ => le_rfl) i v w (singular0 P v) (singular0 P w)
    (fun y hy => by simp only [mem_singular0, hy]) x h

theorem mem_singularSetsIn_congr {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) {v w : Site ν → ℝ}
    {x : Site ν} {i : ℕ} (h : ∀ y, siteDist ν x y ≤ localityRadius P.K₀ i → v y = w y) :
    x ∈ singularSetsIn P Λ v i ↔ x ∈ singularSetsIn P Λ w i :=
  mem_singularSetsGen_congr P (fun B => B ∩ Λ) (fun _ => Finset.inter_subset_left) i v w
    (singular0 P v ∩ Λ) (singular0 P w ∩ Λ)
    (fun y hy => by simp only [Set.mem_inter_iff, mem_singular0, hy]) x h

end FroehlichSpencer.Multiscale

end
