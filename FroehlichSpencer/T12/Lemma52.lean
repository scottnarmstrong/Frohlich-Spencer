/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Events
public import FroehlichSpencer.T12.Cubes
public import FroehlichSpencer.T12.Resonance
public import FroehlichSpencer.Multiscale.Singular

/-!
# Lemma 5.2: isolated-cube resonance product, and the low/terminal cover levels

An isolated-cube piece of a
gentle component is a whole chain cluster at the lower level `j(n)`, hence must be resonant there.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


noncomputable def isolatedCubes {ν : ℕ} (α M : ℝ) (n : ℕ) (D : Finset (Site ν)) :
    Finset (Site ν) := by
  classical exact (minCover n D).filter fun k =>
    ∀ k' ∈ minCover n D, k' ≠ k → M * 2 ^ (α * n) ≤ cubeDist n k k'


noncomputable def resScale (ν : ℕ) (K₀ : ℝ) (n : ℕ) : ℕ := by
  classical exact
    if h : ∃ j, 2 * Real.sqrt ν * 2 ^ n ≤ scaleD K₀ j then Nat.find h else 0


noncomputable def isolatedVolumeFrom {ν : ℕ} (α M : ℝ) (nstar : ℕ) (D : Finset (Site ν)) : ℕ :=
  ∑ n ∈ Finset.Icc nstar (topScale D), if 2 ≤ coverNumber n D then isolatedCount α M n D else 0


theorem card_isolatedCubes {ν : ℕ} (α M : ℝ) (n : ℕ) (D : Finset (Site ν)) :
    (isolatedCubes α M n D).card = isolatedCount α M n D := by
  unfold isolatedCubes isolatedCount
  rfl

/-! ### Real-arithmetic scale lemmas -/

private theorem exists_scaleD_ge {K₀ : ℝ} (hK : 0 < K₀) (a : ℝ) : ∃ j, a ≤ scaleD K₀ j := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (a / K₀) (by norm_num : (1 : ℝ) < 5 / 4)
  refine ⟨j, ?_⟩
  have h1 : a ≤ K₀ * (5 / 4 : ℝ) ^ j := by
    have := (div_lt_iff₀ hK).1 hj
    linarith only [this]
  unfold scaleD
  linarith only [h1, Real.add_one_le_exp (K₀ * (5 / 4 : ℝ) ^ j)]

private theorem resScale_spec {K₀ : ℝ} (hK : 0 < K₀) (ν n : ℕ) :
    2 * Real.sqrt ν * 2 ^ n ≤ scaleD K₀ (resScale ν K₀ n) := by
  classical
  have h := exists_scaleD_ge hK (2 * Real.sqrt ν * 2 ^ n)
  unfold resScale
  simp only [h, ↓reduceDIte]
  exact Nat.find_spec h

private theorem lt_of_lt_resScale {K₀ : ℝ} (hK : 0 < K₀) {ν n i : ℕ} (hi : i < resScale ν K₀ n) :
    scaleD K₀ i < 2 * Real.sqrt ν * 2 ^ n := by
  classical
  have h := exists_scaleD_ge hK (2 * Real.sqrt ν * 2 ^ n)
  unfold resScale at hi
  simp only [h, ↓reduceDIte] at hi
  exact not_le.1 (Nat.find_min h hi)

private theorem exists_nat_large (B : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B ≤ n := by
  obtain ⟨N, hN⟩ := exists_nat_ge B
  exact ⟨N, fun n hn => hN.trans (by exact_mod_cast hn)⟩


private theorem exists_nstar_scale {K₀ : ℝ} (hK : 0 < K₀) (ν : ℕ) :
    ∃ nstar : ℕ, ∀ n : ℕ, nstar ≤ n →
      scaleD K₀ (resScale ν K₀ n + 1) ≤ (2 : ℝ) ^ ((5 / 3 : ℝ) * n) := by
  set ℓ : ℝ := Real.log 2 with hℓ
  have hℓpos : 0 < ℓ := Real.log_pos (by norm_num)
  set A : ℝ := (25 / 16) * (ℓ + Real.log (Real.sqrt ν)) with hA
  obtain ⟨N, hN⟩ := exists_nat_large ((48 / 5) * (|A| + (5 / 4) * K₀) / ℓ)
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  have hnℓ : (48 / 5) * (|A| + (5 / 4) * K₀) ≤ n * ℓ := by
    have := (div_le_iff₀ hℓpos).1 hn'
    linarith only [this]
  have hrhs : (2 : ℝ) ^ ((5 / 3 : ℝ) * n) = Real.exp ((5 / 3) * n * ℓ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hℓ]; ring
  rw [hrhs]
  unfold scaleD
  apply Real.exp_le_exp.mpr
  have hAabs := le_abs_self A
  rcases Nat.eq_zero_or_pos (resScale ν K₀ n) with h0 | hpos
  · rw [h0]
    have : (5 / 4 : ℝ) ^ (0 + 1) = 5 / 4 := by norm_num
    rw [this]
    nlinarith only [hℓpos, hnℓ, abs_nonneg A]
  · obtain ⟨m, hm⟩ : ∃ m, resScale ν K₀ n = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hlt := lt_of_lt_resScale hK (ν := ν) (n := n) (i := m) (by omega)
    have hapos : 0 < 2 * Real.sqrt ν * 2 ^ n := lt_of_le_of_lt (Real.exp_pos _).le hlt
    have h1 : K₀ * (5 / 4 : ℝ) ^ m < Real.log (2 * Real.sqrt ν * 2 ^ n) :=
      (Real.lt_log_iff_exp_lt hapos).2 hlt
    have hsq : 0 < Real.sqrt ν := by
      have : 0 < 2 * Real.sqrt ν := by
        by_contra h
        have : 2 * Real.sqrt ν * 2 ^ n ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (by positivity)
        linarith only [hapos, this]
      linarith only [this]
    have h2 : Real.log (2 * Real.sqrt ν * 2 ^ n) = ℓ + Real.log (Real.sqrt ν) + n * ℓ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hsq.ne',
        Real.log_pow]
    rw [hm]
    have h3 : K₀ * (5 / 4 : ℝ) ^ (m + 1 + 1) = (25 / 16) * (K₀ * (5 / 4 : ℝ) ^ m) := by
      rw [pow_succ, pow_succ]; ring
    rw [h3]
    have h4 : A + (25 / 16) * (n * ℓ) ≤ (5 / 3) * n * ℓ := by
      nlinarith only [hK, hnℓ, hAabs, abs_nonneg A]
    rw [h2] at h1
    nlinarith only [hA, h1, h4]

/-! ### Cube geometry -/

private theorem two_mul_cubeHalfSide_le (n : ℕ) : 2 * cubeHalfSide n ≤ 2 ^ n := by
  unfold cubeHalfSide
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [hn.ne', ite_false]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]
    linarith only []

/-- Two points of one `n`-cube are at distance at most `√ν 2^n`. -/
private theorem siteDist_le_of_mem_dyCube {ν n : ℕ} {k x y : Site ν} (hx : x ∈ dyCube n k)
    (hy : y ∈ dyCube n k) : siteDist ν x y ≤ Real.sqrt ν * 2 ^ n := by
  rw [mem_dyCube] at hx hy
  have hcoord : ∀ i, (((x - y) i : ℤ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by
    intro i
    have h1 := hx i
    have h2 := hy i
    have h3 := two_mul_cubeHalfSide_le n
    have h4 : |(x - y) i| ≤ 2 ^ n := by
      rw [abs_le]; simp only [Pi.sub_apply]; constructor <;> linarith only [h1, h2, h3]
    have h5 : |(((x - y) i : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n := by
      rw [← Int.cast_abs]; exact_mod_cast h4
    exact sq_le_sq' (abs_le.1 h5).1 (abs_le.1 h5).2
  unfold siteDist latticeLength
  calc Real.sqrt (∑ i : Fin ν, (((x - y) i : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt (ν * ((2 : ℝ) ^ n) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc (∑ i : Fin ν, (((x - y) i : ℤ) : ℝ) ^ 2) ≤ ∑ _i : Fin ν, ((2 : ℝ) ^ n) ^ 2 :=
              Finset.sum_le_sum fun i _ => hcoord i
          _ = ν * ((2 : ℝ) ^ n) ^ 2 := by simp
    _ = Real.sqrt ν * 2 ^ n := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]

private theorem cubeDist_le_siteDist {ν n : ℕ} {k k' x y : Site ν} (hx : x ∈ dyCube n k)
    (hy : y ∈ dyCube n k') : cubeDist n k k' ≤ siteDist ν x y := by
  unfold cubeDist
  have h : (dyCube n k ×ˢ dyCube n k').inf
      (fun p => ENNReal.ofReal (Multiscale.siteDist ν p.1 p.2)) ≤
      ENNReal.ofReal (siteDist ν x y) :=
    Finset.inf_le (f := fun p : Site ν × Site ν => ENNReal.ofReal (siteDist ν p.1 p.2))
      (b := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (siteDist_nonneg ν x y)] at this

/-- Every cube of a minimum cover meets `D` (else it could be removed). -/
private theorem minCover_meets {ν n : ℕ} {D : Finset (Site ν)} {c : Site ν}
    (hc : c ∈ minCover n D) : ∃ p, p ∈ dyCube n c ∧ p ∈ D := by
  classical
  by_contra hne
  push Not at hne
  have hcov : IsCubeCover n D ((minCover n D).erase c) := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := minCover_isCubeCover n D x hx
    refine ⟨k, Finset.mem_erase.2 ⟨?_, hk⟩, hxk⟩
    rintro rfl
    exact hne x hxk hx
  have h1 := coverNumber_le hcov
  rw [Finset.card_erase_of_mem hc, card_minCover] at h1
  have : 0 < coverNumber n D := by rw [← card_minCover]; exact Finset.card_pos.2 ⟨c, hc⟩
  omega

/-! ### Removed levels -/

private theorem exists_removed {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν))
    (S₀ : Set (Site ν)) (v : Site ν → ℝ) {y : Site ν} {j : ℕ}
    (hj : y ∈ singularSetsGen P blk S₀ v j) :
    ∀ k, y ∉ singularSetsGen P blk S₀ v k → ∃ h, j ≤ h ∧ h < k ∧
      y ∈ singularSetsGen P blk S₀ v h ∧ y ∉ singularSetsGen P blk S₀ v (h + 1) := by
  intro k
  induction k with
  | zero => intro hk; exact absurd (singularSetsGen_antitone P blk S₀ v (Nat.zero_le j) hj) hk
  | succ k ih =>
    intro hk
    by_cases hyk : y ∈ singularSetsGen P blk S₀ v k
    · refine ⟨k, ?_, Nat.lt_succ_self k, hyk, hk⟩
      by_contra hlt
      exact hk (singularSetsGen_antitone P blk S₀ v (by omega) hj)
    · obtain ⟨h, h1, h2, h3⟩ := ih hyk
      exact ⟨h, h1, by omega, h3⟩

private theorem two_mul_scaleR_le_of_removed {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (S₀ : Set (Site ν)) (v : Site ν → ℝ)
    {h : ℕ} {y c : Site ν} (hy : y ∈ singularSetsGen P blk S₀ v h)
    (hy' : y ∉ singularSetsGen P blk S₀ v (h + 1)) (hc : c ∈ singularSetsGen P blk S₀ v (h + 1)) :
    2 * scaleR P.K₀ h ≤ siteDist ν c y := by
  have hy1 := (mem_singularSetsGen_succ_iff P blk S₀ v h y).not.1 hy'
  have hyS : y ∈ singularSetsGen P blk S₀ v h := hy
  have hcS : c ∈ singularSetsGen P blk S₀ v h :=
    singularSetsGen_antitone P blk S₀ v (Nat.le_succ h) hc
  have hg : IsGentle P blk h v (chainCluster (siteDist ν) (singularSetsGen P blk S₀ v h)
      (2 * scaleR P.K₀ h) y) := by
    by_contra hng
    exact hy1 ⟨hyS, hng⟩
  have hcn : c ∉ chainCluster (siteDist ν) (singularSetsGen P blk S₀ v h)
      (2 * scaleR P.K₀ h) y := by
    intro hcc
    have hc1 := ((mem_singularSetsGen_succ_iff P blk S₀ v h c).1 hc).2
    rw [chainCluster_eq_of_mem (siteDist_comm ν) hcc] at hc1
    exact hc1 hg
  have := le_of_mem_chainCluster_of_not_mem (mem_chainCluster_self hyS) hcS hcn
  rwa [siteDist_comm] at this

/-! ### The isolated-cube piece is a whole cluster -/

private theorem mem_isolatedCubes {ν : ℕ} {α M : ℝ} {n : ℕ} {D : Finset (Site ν)} {c : Site ν} :
    c ∈ isolatedCubes α M n D ↔ c ∈ minCover n D ∧
      ∀ k' ∈ minCover n D, k' ≠ c → M * 2 ^ (α * n) ≤ cubeDist n c k' := by
  classical
  unfold isolatedCubes
  simp only [Finset.mem_filter]

private theorem resonanceEvent_of_eq {ν : ℕ} {B B' : Finset (Site ν)} (h : B = B')
    {v : Site ν → ℝ} {E κ : ℝ}
    (hjj : ∃ jj, |(hamiltonian_isHermitian ν B v).eigenvalues jj - E| ≤ κ) :
    v ∈ resonanceEvent ν B' E κ := by
  subst h; exact hjj


private theorem resonance_of_isolated {ν : ℕ} (P : Params) (hK : 0 < P.K₀)
    (Λ D : Finset (Site ν)) (k : ℕ) (v : Site ν → ℝ) (hv : v ∈ gentleEventIn P Λ D k)
    (n : ℕ) (hscale : scaleD P.K₀ (resScale ν P.K₀ n + 1) ≤ (2 : ℝ) ^ ((5 / 3 : ℝ) * n))
    (h2 : 2 ≤ coverNumber n D) {c : Site ν} (hc : c ∈ isolatedCubes (5 / 3) 2 n D) :
    v ∈ resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ n)) ∩ Λ)
      P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (resScale ν P.K₀ n)))) := by
  classical
  set j := resScale ν P.K₀ n with hj
  set S := singularSetsIn P Λ v with hS
  set R : ℝ := (2 : ℝ) ^ ((5 / 3 : ℝ) * n) with hR
  have hRpos : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨hDcl, hDg⟩ := (mem_gentleEventIn P Λ D k v).1 hv
  have hDg' := hDg
  obtain ⟨hDfin, hDdiam, -⟩ := hDg'
  have hDsub : (D : Set (Site ν)) ⊆ S k := by
    obtain ⟨x, -, hx⟩ := hDcl
    rw [hx]; exact chainCluster_subset x
  obtain ⟨hcm, hiso⟩ := mem_isolatedCubes.1 hc
  obtain ⟨p, hpc, hpD⟩ := minCover_meets hcm
  -- another cube meets `D`, so `d_k` is large and `j + 1 < k`
  have hcard : 1 < (minCover n D).card := by rw [card_minCover]; omega
  obtain ⟨c2, hc2, hc2ne⟩ := Finset.exists_mem_ne hcard c
  obtain ⟨p2, hp2c, hp2D⟩ := minCover_meets hc2
  have hdk : 2 * R ≤ scaleD P.K₀ k := by
    have h1 := hiso c2 hc2 hc2ne
    have h3 := cubeDist_le_siteDist hpc hp2c
    have h4 := hDdiam p hpD p2 hp2D
    simp only [hR] at h1 ⊢
    linarith only [h1, h3, h4]
  have hjk : j + 1 < k := by
    have : scaleD P.K₀ (j + 1) < scaleD P.K₀ k := by linarith only [hscale, hRpos, hdk]
    exact (scaleD_strictMono hK).lt_iff_lt.1 this
  have hr : scaleR P.K₀ j = scaleD P.K₀ (j + 1) := scaleR_eq_scaleD_succ P.K₀ j
  have hrmono : ∀ h, j ≤ h → scaleR P.K₀ j ≤ scaleR P.K₀ h := by
    intro h hh
    rw [scaleR_eq_scaleD_succ, scaleR_eq_scaleD_succ]
    exact (scaleD_strictMono hK).monotone (by omega)
  -- the piece `Q`
  set Q : Finset (Site ν) := dyCube n c ∩ D with hQ
  have hQD : ∀ q ∈ Q, q ∈ D := fun q hq => (Finset.mem_inter.1 hq).2
  have hQc : ∀ q ∈ Q, q ∈ dyCube n c := fun q hq => (Finset.mem_inter.1 hq).1
  have hpQ : p ∈ Q := Finset.mem_inter.2 ⟨hpc, hpD⟩
  have hQS : (Q : Set (Site ν)) ⊆ S j := fun q hq =>
    singularSetsGen_antitone P _ _ v (by omega : j ≤ k) (hDsub (hQD q hq))
  have hQdist : ∀ a ∈ Q, ∀ b ∈ Q, siteDist ν a b ≤ scaleD P.K₀ j / 2 := by
    intro a ha b hb
    have := siteDist_le_of_mem_dyCube (hQc a ha) (hQc b hb)
    have h5 := resScale_spec hK ν n
    rw [← hj] at h5
    nlinarith only [this, h5]
  have hdr : scaleD P.K₀ j ≤ scaleR P.K₀ j := scaleD_le_scaleR hK.le j
  have hrpos := scaleR_pos P.K₀ j
  have hclosed : ∀ c1 ∈ (Q : Set (Site ν)), ∀ y ∈ S j,
      siteDist ν c1 y < 2 * scaleR P.K₀ j → y ∈ (Q : Set (Site ν)) := by
    intro c1 hc1 y hy hlt
    have hc1D : c1 ∈ D := hQD c1 hc1
    by_cases hySk : y ∈ S k
    · have hyD : y ∈ D := by
        by_contra hyD
        have := two_mul_scaleR_le_siteDist P hDcl (c := c1) (y := y) hc1D hySk hyD
        have := hrmono k (by omega)
        linarith
      have hyc : y ∈ dyCube n c := by
        by_contra hyc
        obtain ⟨c', hc', hyc'⟩ := minCover_isCubeCover n D y hyD
        have hne : c' ≠ c := by rintro rfl; exact hyc hyc'
        have h1 := hiso c' hc' hne
        have h3 := cubeDist_le_siteDist (hQc c1 hc1) hyc'
        simp only [hR] at hscale
        rw [hr] at hlt
        linarith only [hlt, h1, h3, hscale]
      exact Finset.mem_inter.2 ⟨hyc, hyD⟩
    · exfalso
      obtain ⟨h, h1, h2', h3, h4⟩ :=
        exists_removed P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v hy k hySk
      have hc1S : c1 ∈ S (h + 1) := singularSetsGen_antitone P _ _ v (by omega : h + 1 ≤ k)
        (hDsub hc1D)
      have := two_mul_scaleR_le_of_removed P _ _ v h3 h4 hc1S
      have := hrmono h h1
      linarith
  have hchain : ∀ c1 ∈ (Q : Set (Site ν)),
      Relation.ReflTransGen
        (chainStep (siteDist ν) (Q : Set (Site ν)) (2 * scaleR P.K₀ j)) p c1 := by
    intro c1 hc1
    refine Relation.ReflTransGen.single ⟨hpQ, hc1, ?_⟩
    have := hQdist p hpQ c1 hc1
    linarith only [hdr, hrpos, this]
  have hQeq := (eq_chainCluster_iff (d := siteDist ν) (S := S j) (ρ := 2 * scaleR P.K₀ j)
    (C := (Q : Set (Site ν))) (x := p) hpQ).2 ⟨hQS, hclosed, hchain⟩
  have hQcl : (Q : Set (Site ν)) ∈ chainClusters (siteDist ν) (S j) (2 * scaleR P.K₀ j) :=
    ⟨p, hQS hpQ, hQeq⟩
  have hnot : ¬ IsGentle P (fun B => B ∩ Λ) j v (Q : Set (Site ν)) := by
    intro hg
    have hpg : p ∈ gentlePart P (fun B => B ∩ Λ) j v (S j) := ⟨Q, ⟨hQcl, hg⟩, hpQ⟩
    have hpk : p ∈ S (j + 1) := singularSetsGen_antitone P _ _ v (by omega : j + 1 ≤ k)
      (hDsub hpD)
    exact hpk.2 hpg
  by_contra hres
  apply hnot
  refine ⟨Q.finite_toSet, fun a ha b hb => ?_, fun jj => ?_⟩
  · have := hQdist a ha b hb
    linarith only [this, scaleD_pos P.K₀ j]
  · by_contra hlt
    apply hres
    have hB : (fun B => B ∩ Λ) (thicken Q.finite_toSet.toFinset (4 * scaleD P.K₀ j)) =
        thicken Q (4 * scaleD P.K₀ j) ∩ Λ := by
      simp only [Finset.finite_toSet_toFinset]
    exact resonanceEvent_of_eq hB ⟨jj, (not_le.1 hlt).le⟩


theorem exists_gentleEventAnyIn_subset (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) :
    ∃ nstar : ℕ, ∀ (P : Params), P.K₀ = K₀ → ∀ (Λ D : Finset (Site ν)),
      gentleEventAnyIn P Λ D ⊆
        {v | ∀ x ∈ D, x ∈ singular0 P v} ∩
          ⋂ n ∈ Finset.Icc nstar (topScale D), ⋂ (_ : 2 ≤ coverNumber n D),
            ⋂ c ∈ isolatedCubes (5 / 3) 2 n D,
              resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD K₀ (resScale ν K₀ n)) ∩ Λ)
                P.E (Real.exp (-Real.sqrt (scaleD K₀ (resScale ν K₀ n)))) := by
  obtain ⟨nstar, hn⟩ := exists_nstar_scale hK ν
  refine ⟨nstar, fun P hP Λ D v hv => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hv
  subst hP
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨hDcl, -⟩ := (mem_gentleEventIn P Λ D k v).1 hk
    obtain ⟨y, -, hy⟩ := hDcl
    have hxk : x ∈ singularSetsIn P Λ v k := by
      have hx' : x ∈ (D : Set (Site ν)) := hx
      rw [hy] at hx'
      exact chainCluster_subset y hx'
    exact (singularSetsGen_subset_zero P _ _ v k hxk).1
  · simp only [Set.mem_iInter]
    intro n hnn h2 c hc
    exact resonance_of_isolated P hK Λ D k v hk n (hn n (Finset.mem_Icc.1 hnn).1) h2 hc


private theorem isolatedCount_le_coverNumber {ν : ℕ} (α M : ℝ) (n : ℕ) (D : Finset (Site ν)) :
    isolatedCount α M n D ≤ coverNumber n D := by
  classical
  unfold isolatedCount
  exact (Finset.card_filter_le _ _).trans_eq (card_minCover n D)

private theorem coverNumber_le_zero {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) :
    coverNumber n D ≤ coverNumber 0 D := by
  rw [coverNumber_zero]; exact coverNumber_le_card n D

/-- A set covered by a single `n`-cube has diameter at most `√ν 2^n`. -/
private theorem finDiam_le_of_coverNumber_eq_one {ν n : ℕ} {D : Finset (Site ν)}
    (h : coverNumber n D = 1) : finDiam D ≤ Real.sqrt ν * 2 ^ n := by
  classical
  have hcard := card_minCover n D
  rw [h] at hcard
  obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hcard
  have hsub : ∀ x ∈ D, x ∈ dyCube n k := by
    intro x hx
    obtain ⟨k', hk', hxk'⟩ := minCover_isCubeCover n D x hx
    rw [hk, Finset.mem_singleton] at hk'
    rwa [← hk']
  have hb : 0 ≤ Real.sqrt ν * 2 ^ n := by positivity
  unfold finDiam
  have : ((D ×ˢ D).sup fun p => Real.toNNReal (siteDist ν p.1 p.2)) ≤
      (Real.sqrt ν * 2 ^ n).toNNReal := by
    refine Finset.sup_le fun p hp => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact Real.toNNReal_le_toNNReal (siteDist_le_of_mem_dyCube (hsub _ h1) (hsub _ h2))
  have h' := NNReal.coe_le_coe.mpr this
  rwa [Real.coe_toNNReal _ hb] at h'

private theorem card_singleton_scales_le {ν : ℕ} (D : Finset (Site ν)) :
    ((Finset.Icc 1 (topScale D)).filter fun n => coverNumber n D = 1).card ≤ ν + 2 := by
  classical
  have hsub : (Finset.Icc 1 (topScale D)).filter (fun n => coverNumber n D = 1) ⊆
      Finset.Icc (topScale D - (ν + 1)) (topScale D) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
    obtain ⟨hn3, hn4⟩ := Finset.mem_Icc.1 hn1
    refine Finset.mem_Icc.2 ⟨?_, hn4⟩
    by_cases hle : topScale D ≤ n
    · omega
    · push Not at hle
      have hmin : ¬ (2 * finDiam D ≤ 2 ^ (topScale D - 1)) := by
        have := Nat.find_min (exists_two_mul_finDiam_le D) (m := topScale D - 1)
          (by unfold topScale at hle ⊢; omega)
        simpa [topScale] using this
      have hd := finDiam_le_of_coverNumber_eq_one hn2
      have h1 : (2 : ℝ) ^ (topScale D - 1) < 2 * (Real.sqrt ν * 2 ^ n) := by
        by_contra hc
        exact hmin (by linarith only [hd, hc])
      obtain ⟨t, ht⟩ : ∃ t, topScale D - 1 = n + t := ⟨topScale D - 1 - n, by omega⟩
      rw [ht, pow_add] at h1
      have h2 : (2 : ℝ) ^ t < 2 * Real.sqrt ν := by
        have hp : (0 : ℝ) < 2 ^ n := by positivity
        nlinarith only [h1, hp]
      have h3 : 2 * Real.sqrt ν ≤ ν + 1 := by
        nlinarith only [sq_nonneg (Real.sqrt ν - 1), Real.sq_sqrt (Nat.cast_nonneg ν : (0 : ℝ) ≤ ν)]
      have h4 : (2 : ℝ) ^ t < ν + 1 := lt_of_lt_of_le h2 h3
      have h5 : 2 ^ t < ν + 1 := by exact_mod_cast h4
      have h6 := Nat.lt_two_pow_self (n := t)
      omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Nat.card_Icc]
  omega


theorem exists_isolatedVolume_le (ν : ℕ) (α M : ℝ) (nstar : ℕ) :
    ∃ Cstar : ℕ, ∀ D : Finset (Site ν), D.Nonempty →
      isolatedVolume α M D ≤ isolatedVolumeFrom α M nstar D + Cstar * coverNumber 0 D := by
  classical
  refine ⟨nstar + (ν + 2), fun D hD => ?_⟩
  have hV0 : 1 ≤ coverNumber 0 D := one_le_coverNumber 0 hD
  set I := Finset.Icc 1 (topScale D) with hI
  have hpt : ∀ n ∈ I, isolatedCount α M n D ≤
      (if nstar ≤ n then (if 2 ≤ coverNumber n D then isolatedCount α M n D else 0) else 0) +
      (if n < nstar then coverNumber 0 D else 0) +
      (if coverNumber n D = 1 then 1 else 0) := by
    intro n _
    have h1 := isolatedCount_le_coverNumber α M n D
    have h2 := coverNumber_le_zero n D
    have h3 := one_le_coverNumber n hD
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hg : (∑ n ∈ I, if nstar ≤ n then
      (if 2 ≤ coverNumber n D then isolatedCount α M n D else 0) else 0) ≤
      isolatedVolumeFrom α M nstar D := by
    rw [← Finset.sum_filter]
    unfold isolatedVolumeFrom
    apply Finset.sum_le_sum_of_subset
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
    exact Finset.mem_Icc.2 ⟨hn2, (Finset.mem_Icc.1 hn1).2⟩
  have hh : (∑ n ∈ I, if n < nstar then coverNumber 0 D else 0) ≤ nstar * coverNumber 0 D := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    apply Nat.mul_le_mul_right
    calc (I.filter fun n => n < nstar).card ≤ (Finset.range nstar).card := by
          apply Finset.card_le_card
          intro n hn
          exact Finset.mem_range.2 (Finset.mem_filter.1 hn).2
      _ = nstar := Finset.card_range _
  have hk : (∑ n ∈ I, if coverNumber n D = 1 then 1 else 0) ≤ (ν + 2) * coverNumber 0 D := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    exact (card_singleton_scales_le D).trans (Nat.le_mul_of_pos_right _ hV0)
  unfold isolatedVolume
  rw [← hI, add_mul]
  omega

end FroehlichSpencer.T12

end
