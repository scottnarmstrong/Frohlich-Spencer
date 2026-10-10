/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.ResonantBlock
public import FroehlichSpencer.T12.Regions
import FroehlichSpencer.IDS.Green
import FroehlichSpencer.Infra.Green.Iteration


@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

/-- The nearest-neighbour hopping kernel is real symmetric. -/
theorem hoppingKernel_symm_real (ν : ℕ) (x y : Site ν) :
    hoppingKernel ν x y = hoppingKernel ν y x := by
  have h := hoppingKernel_symm ν y x
  rw [h]
  unfold hoppingKernel
  simp only [star_neg, star_sum, star_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1 <;> split_ifs <;> simp


noncomputable def greenEntry {ν : ℕ} (v : Site ν → ℝ) (E ε : ℝ) (A : Finset (Site ν))
    (x y : Site ν) : ℂ :=
  Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) A
    ((E : ℂ) + (ε : ℂ) * Complex.I) y x


theorem greenEntry_eq {ν : ℕ} (A : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0)
    (x y : {x // x ∈ A}) : finiteGreen ν A v E ε hε x y = greenEntry v E ε A x y :=
  finiteGreen_eq_resolventColumn A v E ε hε x y


theorem greenEntry_symm {ν : ℕ} (A : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ)
    (x y : Site ν) : greenEntry v E ε A x y = greenEntry v E ε A y x := by
  classical
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · unfold greenEntry
      rw [Infra.resolventColumn_of_mem _ _ _ hx hy, Infra.resolventColumn_of_mem _ _ _ hy hx]
      set M := Infra.restrictedOp (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) A -
        ((E : ℂ) + (ε : ℂ) * Complex.I) • (1 : Matrix A A ℂ) with hM
      have hMt : M.transpose = M := by
        ext i j
        simp only [hM, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, Infra.restrictedOp_apply, hoppingKernel_symm_real ν j i, smul_eq_mul]
        by_cases hij : i = j
        · subst hij; rfl
        · simp [hij, Ne.symm hij]
      have h : (M⁻¹).transpose = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMt]
      have := congrFun (congrFun h ⟨x, hx⟩) ⟨y, hy⟩
      simpa [Matrix.transpose_apply] using this.symm
    · unfold greenEntry
      rw [Infra.resolventColumn_of_notMem_right _ _ _ _ hy,
        Infra.resolventColumn_of_notMem_left _ _ _ _ hy]
  · unfold greenEntry
    rw [Infra.resolventColumn_of_notMem_left _ _ _ _ hx,
      Infra.resolventColumn_of_notMem_right _ _ _ _ hx]


theorem finiteGreen_symm {ν : ℕ} (B : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0)
    (x y : {x // x ∈ B}) : finiteGreen ν B v E ε hε x y = finiteGreen ν B v E ε hε y x := by
  rw [greenEntry_eq, greenEntry_eq]
  exact greenEntry_symm B v E ε x y


theorem isUnit_greenEntry {ν : ℕ} (A : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ)
    (hε : ε ≠ 0) :
    IsUnit (Infra.restrictedOp (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) A -
      ((E : ℂ) + (ε : ℂ) * Complex.I) • (1 : Matrix A A ℂ)) :=
  FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
    (Infra.isHermitian_restrictedOp (hoppingKernel_symm ν) _ A) _ (by simpa using hε)


theorem greenEntry_neg_sum {ν : ℕ} (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0)
    {A Bs : Finset (Site ν)} (hBA : Bs ⊆ A) {x y : Site ν} (hx : x ∈ Bs) (hy : y ∈ A)
    (hyB : y ∉ Bs) :
    greenEntry v E ε A x y = -∑ k ∈ Bs, ∑ k' ∈ A \ Bs,
      greenEntry v E ε Bs x k * hoppingKernel ν k k' * greenEntry v E ε A k' y :=
  Infra.resolventColumn_eq_neg_sum_coupling _ hBA (isUnit_greenEntry A v E ε hε)
    (isUnit_greenEntry Bs v E ε hε) hx hy hyB


theorem greenEntry_sub_sum {ν : ℕ} (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0)
    {A Bs : Finset (Site ν)} (hBA : Bs ⊆ A) {x y : Site ν} (hx : x ∈ Bs) (hy : y ∈ Bs) :
    greenEntry v E ε A x y = greenEntry v E ε Bs x y - ∑ k ∈ Bs, ∑ k' ∈ A \ Bs,
      greenEntry v E ε Bs x k * hoppingKernel ν k k' * greenEntry v E ε A k' y :=
  resolventColumn_eq_sub_sum_coupling_of_mem (hoppingKernel_symm ν) _ hBA
    (by simpa using hε) hx hy


theorem norm_cross_sum_le {ν : ℕ} (v : Site ν → ℝ) (E ε : ℝ) (Q Bf A : Finset (Site ν))
    (x y : Site ν) {w : Site ν → ℝ} {h : ℝ}
    (hw : ∀ q ∈ Q, ∀ b ∈ Bf, hoppingKernel ν q b ≠ 0 → ‖greenEntry v E ε Q x q‖ ≤ w q)
    (hh : ∀ b ∈ Bf, ‖greenEntry v E ε A b y‖ ≤ h) (hw0 : ∀ q, 0 ≤ w q) :
    ‖∑ q ∈ Q, ∑ b ∈ Bf, greenEntry v E ε Q x q * hoppingKernel ν q b * greenEntry v E ε A b y‖ ≤
      h * ∑ q ∈ Q, ∑ b ∈ Bf, w q * ‖hoppingKernel ν q b‖ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  rw [norm_mul, norm_mul]
  by_cases h0 : hoppingKernel ν q b = 0
  · simp [h0]
  · have h1 := hw q hq b hb h0
    have h2 := hh b hb
    have h3 : 0 ≤ h := (norm_nonneg _).trans h2
    calc ‖greenEntry v E ε Q x q‖ * ‖hoppingKernel ν q b‖ * ‖greenEntry v E ε A b y‖
        ≤ w q * ‖hoppingKernel ν q b‖ * h :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2 (norm_nonneg _)
            (mul_nonneg (hw0 q) (norm_nonneg _))
      _ = h * (w q * ‖hoppingKernel ν q b‖) := by ring

/-- Interface sums with a weight bounded on active links. -/
theorem sum_weighted_le {ν : ℕ} (Q Bf : Finset (Site ν)) (w : Site ν → ℝ) {K : ℝ}
    (hK : ∀ q ∈ Q, ∀ b ∈ Bf, hoppingKernel ν q b ≠ 0 → w q ≤ K) :
    ∑ q ∈ Q, ∑ b ∈ Bf, w q * ‖hoppingKernel ν q b‖ ≤
      K * ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  by_cases h0 : hoppingKernel ν q b = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (hK q hq b hb h0) (norm_nonneg _)


theorem sum_cross_le {ν : ℕ} (Q Bf : Finset (Site ν)) :
    ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖ ≤ 2 * ν * Bf.card := by
  rw [Finset.sum_comm]
  calc ∑ b ∈ Bf, ∑ q ∈ Q, ‖hoppingKernel ν q b‖ = ∑ b ∈ Bf, ∑ q ∈ Q, ‖hoppingKernel ν b q‖ := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun q _ => ?_
        rw [hoppingKernel_symm_real ν q b]
    _ ≤ ∑ _b ∈ Bf, (2 * (ν : ℝ)) := Finset.sum_le_sum fun b _ => sum_norm_hoppingKernel_le ν b Q
    _ = 2 * ν * Bf.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Products of two interface sums with weights bounded on active links. -/
theorem prod_sum_le {ν : ℕ} (Q Bf : Finset (Site ν)) (wx wy : Site ν → ℝ) {K : ℝ}
    (hK : ∀ q ∈ Q, ∀ b ∈ Bf, ∀ q' ∈ Q, ∀ b' ∈ Bf, hoppingKernel ν q b ≠ 0 →
      hoppingKernel ν q' b' ≠ 0 → wx q * wy q' ≤ K) :
    (∑ q ∈ Q, ∑ b ∈ Bf, wx q * ‖hoppingKernel ν q b‖) *
        (∑ q ∈ Q, ∑ b ∈ Bf, wy q * ‖hoppingKernel ν q b‖) ≤
      K * (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) *
        (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun b hb =>
    Finset.sum_le_sum fun q' hq' => Finset.sum_le_sum fun b' hb' => ?_
  by_cases h0 : hoppingKernel ν q b = 0
  · simp [h0]
  by_cases h1 : hoppingKernel ν q' b' = 0
  · simp [h1]
  have := hK q' hq' b' hb' q hq b hb h1 h0
  have h2 := norm_nonneg (hoppingKernel ν q b)
  have h3 := norm_nonneg (hoppingKernel ν q' b')
  calc wx q' * ‖hoppingKernel ν q' b'‖ * (wy q * ‖hoppingKernel ν q b‖)
      = (wx q' * wy q) * (‖hoppingKernel ν q' b'‖ * ‖hoppingKernel ν q b‖) := by ring
    _ ≤ K * (‖hoppingKernel ν q' b'‖ * ‖hoppingKernel ν q b‖) :=
        mul_le_mul_of_nonneg_right this (mul_nonneg h3 h2)
    _ = K * ‖hoppingKernel ν q' b'‖ * ‖hoppingKernel ν q b‖ := by ring

/-- Active hopping links have Euclidean length `1`. -/
theorem siteDist_eq_one_of_hoppingKernel_ne_zero {ν : ℕ} {x w : Site ν}
    (h : hoppingKernel ν x w ≠ 0) : siteDist ν x w = 1 := by
  rw [siteDist_eq_norm]
  obtain ⟨k, rfl | rfl⟩ := hoppingKernel_ne_zero_exists h
  · refine (Infra.Lattice.norm_latticeCast_sub_eq_one_iff _ _).2 ⟨k, Or.inr ?_, ?_⟩
    · simp
    · intro j hj; simp [hj]
  · refine (Infra.Lattice.norm_latticeCast_sub_eq_one_iff _ _).2 ⟨k, Or.inl ?_, ?_⟩
    · simp
    · intro j hj; simp [hj]

private theorem gentle_core {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m : ℝ} (hm : 0 ≤ m)
    (hJ : JPred P Λ v k m) {C : Set (Site ν)} (hC : C ∈ restrictedClasses P Λ v k)
    {R B : Finset (Site ν)} (hCB : C ⊆ B)
    (hBN : (B : Set (Site ν)) ⊆ nbhd C (3 * scaleD P.K₀ k - 1))
    (hCR : nbhd C (4 * scaleD P.K₀ k) ⊆ R)
    (hRC : (R : Set (Site ν)) ⊆ nbhd C (scaleD P.K₀ (k + 1)))
    (hQadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R : Set (Site ν)) \ B))
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hdiamB : ∀ u ∈ B, ∀ w ∈ B, siteDist ν u w ≤ 7 * scaleD P.K₀ k)
    (ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ R ∩ Λ})
    (hxy : scaleD P.K₀ (k + 1) / 5 ≤ siteDist ν x y)
    (hcross : ∀ u ∈ B, ∀ w ∈ R, w ∉ B → siteDist ν u w = 1 →
      scaleD P.K₀ k ≤ siteDist ν x w ∧ scaleD P.K₀ k ≤ siteDist ν y w) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (-m * siteDist ν x y) *
      (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
        Real.exp (Real.sqrt (scaleD P.K₀ k) + m * (7 * scaleD P.K₀ k + 2))) := by
  classical
  obtain ⟨x, hxA⟩ := x
  obtain ⟨y, hyA⟩ := y
  set d := scaleD P.K₀ k with hd
  have hK0 : 0 ≤ P.K₀ := by
    by_contra h
    push Not at h
    have h1 : scaleD P.K₀ 0 < 1 := by
      rw [scaleD_zero]
      exact (Real.exp_lt_exp.2 h).trans_eq Real.exp_zero
    linarith only [h1, hK.1]
  have hd1 : 1 ≤ d := one_le_scaleD hK0 k
  have hdpos : 0 < d := scaleD_pos _ _
  have hd9 : 9 * d < scaleD P.K₀ (k + 1) / 5 := hK.2.2.2.2.2.1 k
  obtain ⟨hfin, hdiam, -⟩ := hC.2
  have hCmem : C ∈ chainClusters (siteDist ν)
      (singularSetsGen P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v k) (2 * scaleR P.K₀ k) := hC.1
  obtain ⟨c₀, hc₀⟩ :=
    (obstacleFamily_gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v).nonempty k C hC
  have hBR : ∀ b ∈ B, b ∈ R := by
    intro b hb
    obtain ⟨c, hcC, hbc⟩ := hBN (Finset.mem_coe.2 hb)
    exact hCR ⟨c, hcC, by linarith only [hdpos, hbc]⟩
  set A : Finset (Site ν) := R ∩ Λ with hA
  set Bf : Finset (Site ν) := B ∩ Λ with hBf
  set Q : Finset (Site ν) := (R \ B) ∩ Λ with hQ
  have hBfA : Bf ⊆ A := fun x hx => by
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hx
    exact Finset.mem_inter.2 ⟨hBR x h1, h2⟩
  have hQeq : Q = A \ Bf := by
    ext x
    simp only [hQ, hA, hBf, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hQA : Q ⊆ A := by
    rw [hQeq]; exact Finset.sdiff_subset
  have hAQ : A \ Q = Bf := by
    rw [hQeq]; exact Finset.sdiff_sdiff_eq_self hBfA
  -- decay on `Q`
  have hadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R \ B : Finset (Site ν)) :
      Set (Site ν)) := by
    rw [Finset.coe_sdiff]
    exact hQadm
  have havoid : ∀ x ∈ (R \ B) ∩ Λ, x ∉ singularSetsIn P Λ v k := by
    intro x hx hxS
    obtain ⟨hxRB, hxΛ⟩ := Finset.mem_inter.1 hx
    obtain ⟨hxR, hxB⟩ := Finset.mem_sdiff.1 hxRB
    obtain ⟨c, hcC, hxc⟩ := hRC (Finset.mem_coe.2 hxR)
    obtain ⟨x₀, -, rfl⟩ := hCmem
    have hlt : siteDist ν c x < 2 * scaleR P.K₀ k := by
      rw [siteDist_comm, scaleR_eq_scaleD_succ]
      have := scaleD_pos P.K₀ (k + 1)
      linarith only [hxc, this]
    exact hxB (hCB (mem_chainCluster_of_lt hcC hxS hlt))
  have hJQ : ∀ s ∈ Q, ∀ q ∈ Q, d / 5 ≤ siteDist ν s q →
      ‖greenEntry v P.E ε Q s q‖ ≤ Real.exp (-m * siteDist ν s q) := by
    intro s hs q hq h
    have := hJ (R \ B) hadm havoid ε hε ⟨s, hs⟩ ⟨q, hq⟩ h
    rwa [greenEntry_eq] at this
  -- the resonant block
  have hresB : ∀ b ∈ Bf, ∀ b' ∈ Bf, ‖greenEntry v P.E ε A b b'‖ ≤ 2 * Real.exp (Real.sqrt d) := by
    intro b hb b' hb'
    have hb1 := Finset.mem_inter.1 hb
    have hb1' := Finset.mem_inter.1 hb'
    have := norm_finiteGreen_resonantBlock_le P hK Λ v k hm hJ hC hCB hBN hCR hRC hQadm hsmall
      ε hε ⟨b, Finset.mem_inter.2 ⟨hBR b hb1.1, hb1.2⟩⟩
      ⟨b', Finset.mem_inter.2 ⟨hBR b' hb1'.1, hb1'.2⟩⟩ hb1.1 hb1'.1
    rwa [greenEntry_eq] at this
  -- counting
  have hcard : (Bf.card : ℝ) ≤ (25 * d) ^ ν := by
    have hsub : Bf ⊆ Λ.filter (fun x => siteDist ν c₀ x ≤ 5 * d) := by
      intro x hx
      obtain ⟨hxB, hxΛ⟩ := Finset.mem_inter.1 hx
      obtain ⟨c, hcC, hxc⟩ := hBN (Finset.mem_coe.2 hxB)
      have h1 := hdiam c₀ hc₀ c hcC
      have h2 := siteDist_triangle ν c₀ x c
      have h3 := siteDist_comm ν c x
      exact Finset.mem_filter.2 ⟨hxΛ, by linarith only [hdpos, hxc, h1, h2, h3]⟩
    have := card_filter_siteDist_le Λ c₀ (R := 5 * d) (by linarith only [hd1])
    calc (Bf.card : ℝ) ≤ ((Λ.filter fun x => siteDist ν c₀ x ≤ 5 * d).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (5 * (5 * d)) ^ ν := this
      _ = (25 * d) ^ ν := by ring_nf
  set N : ℝ := 2 * ν * (25 * d) ^ ν with hN
  have hN0 : 0 ≤ N := by positivity
  have hPN : ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖ ≤ N :=
    (sum_cross_le Q Bf).trans (mul_le_mul_of_nonneg_left hcard (by positivity))
  have hP0 : 0 ≤ ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hN1 : N = 0 ∨ 1 ≤ N := by
    rcases Nat.eq_zero_or_pos ν with h | h
    · left; simp [hN, h]
    · right
      have h1 : (1 : ℝ) ≤ ν := by exact_mod_cast h
      have h2 : 1 ≤ (25 * d) ^ ν := one_le_pow₀ (by linarith only [hd1])
      rw [hN]; nlinarith only [h1, h2]
  set Ξ : ℝ → ℝ := fun L => Real.exp (-m * L) *
    (1 + 2 * N ^ 2 * Real.exp (Real.sqrt d + m * (7 * d + 2))) with hΞ
  -- the main estimate for `s ∉ B`
  have hQany : ∀ s t : Site ν, s ∈ A → s ∉ B → t ∈ A →
      (∀ u ∈ B, ∀ w ∈ R, w ∉ B → siteDist ν u w = 1 →
        d ≤ siteDist ν s w ∧ d ≤ siteDist ν t w) →
      scaleD P.K₀ (k + 1) / 5 ≤ siteDist ν s t →
      ‖greenEntry v P.E ε A s t‖ ≤ Ξ (siteDist ν s t) := by
    intro s t hsA hsB htA hcr hL
    have hsQ : s ∈ Q := Finset.mem_inter.2
      ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hsA).1, hsB⟩, (Finset.mem_inter.1 hsA).2⟩
    set L := siteDist ν s t with hLdef
    have hcr' : ∀ q ∈ Q, ∀ b ∈ Bf, hoppingKernel ν q b ≠ 0 →
        d ≤ siteDist ν s q ∧ d ≤ siteDist ν t q ∧ siteDist ν q b ≤ 1 := by
      intro q hq b hb h0
      obtain ⟨hq1, -⟩ := Finset.mem_inter.1 hq
      obtain ⟨hqR, hqB⟩ := Finset.mem_sdiff.1 hq1
      have h1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
      have h2 := hcr b (Finset.mem_inter.1 hb).1 q hqR hqB (by rw [siteDist_comm, h1])
      exact ⟨h2.1, h2.2, h1.le⟩
    have hQs : ∀ q ∈ Q, ∀ b ∈ Bf, hoppingKernel ν q b ≠ 0 →
        ‖greenEntry v P.E ε Q s q‖ ≤ Real.exp (-m * siteDist ν s q) := fun q hq b hb h0 =>
      hJQ s hsQ q hq (by linarith only [hdpos, (hcr' q hq b hb h0).1])
    have hrow : ∀ b ∈ Bf, ∀ b' ∈ Bf, siteDist ν b b' ≤ 7 * d := fun b hb b' hb' =>
      hdiamB b (Finset.mem_inter.1 hb).1 b' (Finset.mem_inter.1 hb').1
    have hexp0 : (0 : ℝ) < Real.exp (-m * L) := Real.exp_pos _
    by_cases htB : t ∈ B
    · -- `s ∈ Q`, `t ∈ B`
      have htBf : t ∈ Bf := Finset.mem_inter.2 ⟨htB, (Finset.mem_inter.1 htA).2⟩
      have htQ : t ∉ Q := fun h => (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).1).2 htB
      rw [greenEntry_neg_sum v P.E ε hε hQA hsQ htA htQ, hAQ, norm_neg]
      refine (norm_cross_sum_le v P.E ε Q Bf A s t hQs
        (fun b hb => hresB b hb t htBf) (fun _ => (Real.exp_pos _).le)).trans ?_
      set K2 := Real.exp (-m * L) * Real.exp (m * (7 * d + 1)) with hK2
      have hK2' : ∑ q ∈ Q, ∑ b ∈ Bf, Real.exp (-m * siteDist ν s q) *
          ‖hoppingKernel ν q b‖ ≤ K2 * ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖ := by
        refine sum_weighted_le Q Bf _ fun q hq b hb h0 => ?_
        obtain ⟨-, -, h3⟩ := hcr' q hq b hb h0
        have h4 := siteDist_triangle ν s t q
        have h5 := siteDist_triangle ν s q t
        have h6 := siteDist_triangle ν q t b
        have h7 := hrow b hb t htBf
        have h8 : -m * siteDist ν s q ≤ -m * L + m * (7 * d + 1) := by
          have := mul_le_mul_of_nonneg_left (show L ≤ siteDist ν s q + (7 * d + 1) by
            have := siteDist_comm ν q t
            linarith only [h3, h4, h6, h7]) hm
          linarith only [this]
        rw [hK2, ← Real.exp_add]
        exact Real.exp_le_exp.2 h8
      have hK20 : 0 ≤ K2 := by positivity
      have hb1 : Real.exp (m * (7 * d + 1)) ≤ Real.exp (m * (7 * d + 2)) :=
        Real.exp_le_exp.2 (by nlinarith only [hm])
      have hE0 := Real.exp_pos (Real.sqrt d)
      have hE1 := Real.exp_pos (m * (7 * d + 2))
      have hstep : 2 * Real.exp (Real.sqrt d) * (K2 * ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) ≤
          2 * Real.exp (Real.sqrt d) * (K2 * N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPN hK20) (by positivity)
      refine (mul_le_mul_of_nonneg_left hK2' (by positivity)).trans (hstep.trans ?_)
      rw [hΞ]
      show _ ≤ Real.exp (-m * L) * _
      have hK2le : K2 ≤ Real.exp (-m * L) * Real.exp (m * (7 * d + 2)) :=
        mul_le_mul_of_nonneg_left hb1 hexp0.le
      have hN2 : N ≤ N ^ 2 ∨ N = 0 := by
        rcases hN1 with h | h
        · exact Or.inr h
        · exact Or.inl (by nlinarith only [h])
      have hfin : 2 * Real.exp (Real.sqrt d) * (K2 * N) ≤
          Real.exp (-m * L) * (2 * N ^ 2 * Real.exp (Real.sqrt d + m * (7 * d + 2))) := by
        rw [Real.exp_add]
        rcases hN2 with h | h
        · calc 2 * Real.exp (Real.sqrt d) * (K2 * N)
              ≤ 2 * Real.exp (Real.sqrt d) *
                (Real.exp (-m * L) * Real.exp (m * (7 * d + 2)) * N ^ 2) :=
                mul_le_mul_of_nonneg_left (mul_le_mul hK2le h hN0 (by positivity))
                  (by positivity)
            _ = _ := by ring
        · rw [h]; simp
      nlinarith only [hfin, hexp0]
    · -- `s, t ∈ Q`
      have htQ : t ∈ Q := Finset.mem_inter.2
        ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 htA).1, htB⟩, (Finset.mem_inter.1 htA).2⟩
      have hQt : ∀ q ∈ Q, ∀ b ∈ Bf, hoppingKernel ν q b ≠ 0 →
          ‖greenEntry v P.E ε Q t q‖ ≤ Real.exp (-m * siteDist ν t q) := fun q hq b hb h0 =>
        hJQ t htQ q hq (by linarith only [hdpos, (hcr' q hq b hb h0).2.1])
      set Sy := ∑ q ∈ Q, ∑ b ∈ Bf, Real.exp (-m * siteDist ν t q) * ‖hoppingKernel ν q b‖
        with hSy
      set Sx := ∑ q ∈ Q, ∑ b ∈ Bf, Real.exp (-m * siteDist ν s q) * ‖hoppingKernel ν q b‖
        with hSx
      have hSy0 : 0 ≤ Sy := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
      have hH0 : 0 ≤ 2 * Real.exp (Real.sqrt d) * Sy := by positivity
      -- step 2
      have hstep2 : ∀ b ∈ Bf, ‖greenEntry v P.E ε A b t‖ ≤ 2 * Real.exp (Real.sqrt d) * Sy := by
        intro b hb
        have hbA : b ∈ A := hBfA hb
        have hbQ : b ∉ Q := fun h => (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).1).2
          (Finset.mem_inter.1 hb).1
        rw [greenEntry_symm, greenEntry_neg_sum v P.E ε hε hQA htQ hbA hbQ, hAQ, norm_neg]
        exact norm_cross_sum_le v P.E ε Q Bf A t b hQt
          (fun b' hb' => hresB b' hb' b hb) (fun _ => (Real.exp_pos _).le)
      -- step 1
      rw [greenEntry_sub_sum v P.E ε hε hQA hsQ htQ, hAQ]
      refine (norm_sub_le _ _).trans ?_
      have hJst : ‖greenEntry v P.E ε Q s t‖ ≤ Real.exp (-m * L) :=
        hJQ s hsQ t htQ (by linarith only [hdpos, hd9, hL])
      have h1 := norm_cross_sum_le v P.E ε Q Bf A s t hQs hstep2 (fun _ => (Real.exp_pos _).le)
      set K := Real.exp (-m * L) * Real.exp (m * (7 * d + 2)) with hKdef
      have hprod : Sx * Sy ≤ K * (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) *
          (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) := by
        refine prod_sum_le Q Bf _ _ fun q hq b hb q' hq' b' hb' h0 h0' => ?_
        obtain ⟨-, -, h3⟩ := hcr' q hq b hb h0
        obtain ⟨-, -, h3'⟩ := hcr' q' hq' b' hb' h0'
        obtain ⟨h4, -, -⟩ := hcr' q hq b hb h0
        obtain ⟨-, h4', -⟩ := hcr' q' hq' b' hb' h0'
        have h5 := siteDist_triangle ν s t q
        have h6 := siteDist_triangle ν s q t
        have h7 := siteDist_triangle ν q t b
        have h8 := siteDist_triangle ν b t b'
        have h9 := siteDist_triangle ν b' t q'
        have h10 := hrow b hb b' hb'
        have h11 := siteDist_comm ν b' q'
        have h12 := siteDist_comm ν q' t
        have h13 := siteDist_comm ν b' t
        have h14 : L ≤ siteDist ν s q + siteDist ν t q' + (7 * d + 2) := by
          linarith only [h3, h3', h5, h7, h8, h9, h10, h11, h12]
        rw [← Real.exp_add, hKdef, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left h14 hm
        linarith only [this]
      have hK0' : 0 ≤ K := by positivity
      have hE0 := Real.exp_pos (Real.sqrt d)
      have hKPP : K * (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) *
          (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) ≤ K * N * N := by
        gcongr
      have hmain : 2 * Real.exp (Real.sqrt d) * Sy * Sx ≤
          Real.exp (-m * L) * (2 * N ^ 2 * Real.exp (Real.sqrt d + m * (7 * d + 2))) := by
        calc 2 * Real.exp (Real.sqrt d) * Sy * Sx
            = 2 * Real.exp (Real.sqrt d) * (Sx * Sy) := by ring
          _ ≤ 2 * Real.exp (Real.sqrt d) * (K * N * N) :=
              mul_le_mul_of_nonneg_left (hprod.trans hKPP) (by positivity)
          _ = _ := by rw [hKdef, Real.exp_add]; ring
      rw [hΞ]
      show _ ≤ Real.exp (-m * L) * _
      nlinarith only [h1, hmain, hJst]
  -- case analysis on the endpoints
  have key : ‖greenEntry v P.E ε A x y‖ ≤ Ξ (siteDist ν x y) := by
    by_cases hxB : x ∈ B
    · by_cases hyB : y ∈ B
      · exfalso
        have := hdiamB _ hxB _ hyB
        linarith only [hxy, hdpos, hd9, this]
      · rw [greenEntry_symm, siteDist_comm]
        refine hQany y x hyA hyB hxA (fun u hu w hw hwB h1 => ?_) (by rwa [siteDist_comm])
        exact (hcross u hu w hw hwB h1).symm
    · exact hQany x y hxA hxB hyA hcross hxy
  rw [greenEntry_eq]
  exact key


theorem norm_finiteGreen_gentleRegion_le {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m m₀ : ℝ} (hm : 0 ≤ m) (hmm₀ : m ≤ m₀)
    (hJ : JPred P Λ v k m) {C : Set (Site ν)} (hC : C ∈ restrictedClasses P Λ v k)
    {R : Finset (Site ν)}
    (hRconn : ∀ x ∈ (R : Set (Site ν)), ∀ y ∈ (R : Set (Site ν)),
      y ∈ nnComponent (R : Set (Site ν)) x)
    (hRadm : Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) (R : Set (Site ν)))
    (hCR : nbhd C (4 * scaleD P.K₀ k) ⊆ R)
    (hRC : (R : Set (Site ν)) ⊆ nbhd C (scaleD P.K₀ (k + 1)))
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hloss : Real.log (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) + m * (7 * scaleD P.K₀ k + 2))) ≤
        9 * m₀ * scaleD P.K₀ k)
    (ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ R ∩ Λ})
    (hxy : scaleD P.K₀ (k + 1) / 5 ≤ siteDist ν x y) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤
      Real.exp (-(m - 45 * m₀ * scaleD P.K₀ k ^ (-(1 / 4 : ℝ))) * siteDist ν x y) := by
  classical
  set d := scaleD P.K₀ k with hd
  have hdpos : 0 < d := scaleD_pos _ _
  have hxR : (x : Site ν) ∈ (R : Set (Site ν)) := Finset.mem_coe.2 (Finset.mem_inter.1 x.2).1
  have hyR : (y : Site ν) ∈ (R : Set (Site ν)) := Finset.mem_coe.2 (Finset.mem_inter.1 y.2).1
  obtain ⟨B, hCB, hB4, hBN, -, hQadm, hdiam, -, hcross⟩ := exists_radialCut hK
    (obstacleFamily_gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v) k hC hRconn hRadm
    hCR hxR hyR hxy
  have hBfin : B.Finite := R.finite_toSet.subset (hB4.trans hCR)
  obtain ⟨B', rfl⟩ : ∃ B' : Finset (Site ν), (B' : Set (Site ν)) = B :=
    ⟨hBfin.toFinset, hBfin.coe_toFinset⟩
  have hcore := gentle_core P hK Λ v k hm hJ hC hCB hBN hCR hRC hQadm hsmall
    (fun u hu w hw => hdiam u (Finset.mem_coe.2 hu) w (Finset.mem_coe.2 hw)) ε hε x y hxy
    (fun u hu w hw hwB h1 => by
      have := hcross u (Finset.mem_coe.2 hu) w
        ⟨Finset.mem_coe.2 hw, fun h => hwB (Finset.mem_coe.1 h)⟩ h1
      exact ⟨this.2.2.1, this.2.2.2⟩)
  refine hcore.trans ?_
  set L := siteDist ν x y with hL
  set X : ℝ := 2 * (2 * ν * (25 * d) ^ ν) ^ 2 *
    Real.exp (Real.sqrt d + m * (7 * d + 2)) with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : 1 + X ≤ Real.exp (9 * m₀ * d) := by
    have := (Real.log_le_iff_le_exp (by linarith only [hX0])).1 hloss
    exact this
  have hd54 : d ^ (5 / 4 : ℝ) = scaleD P.K₀ (k + 1) := by
    rw [← scaleR_eq_scaleD_succ]; rfl
  have hL0 : d ^ (5 / 4 : ℝ) / 5 ≤ L := by rw [hd54]; exact hxy
  have hpow : d ^ (-(1 / 4 : ℝ)) * d ^ (5 / 4 : ℝ) = d := by
    rw [← Real.rpow_add hdpos]; norm_num
  have hneg : 0 < d ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hdpos _
  have h2 : 9 * m₀ * d ≤ 45 * m₀ * d ^ (-(1 / 4 : ℝ)) * L := by
    have hm0 : 0 ≤ m₀ := hm.trans hmm₀
    have h3 : d ^ (-(1 / 4 : ℝ)) * (d ^ (5 / 4 : ℝ) / 5) ≤ d ^ (-(1 / 4 : ℝ)) * L :=
      mul_le_mul_of_nonneg_left hL0 hneg.le
    have h4 : d ^ (-(1 / 4 : ℝ)) * (d ^ (5 / 4 : ℝ) / 5) = d / 5 := by
      calc d ^ (-(1 / 4 : ℝ)) * (d ^ (5 / 4 : ℝ) / 5)
          = (d ^ (-(1 / 4 : ℝ)) * d ^ (5 / 4 : ℝ)) / 5 := by ring
        _ = d / 5 := by rw [hpow]
    nlinarith only [hm0, h4, mul_le_mul_of_nonneg_left h3 hm0]
  calc Real.exp (-m * L) * (1 + X) ≤ Real.exp (-m * L) * Real.exp (9 * m₀ * d) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-m * L + 9 * m₀ * d) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith only [h2])

end FroehlichSpencer.T12

end
