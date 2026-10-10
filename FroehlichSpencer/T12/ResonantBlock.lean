/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Exterior
public import FroehlichSpencer.T12.InductionDefs
public import FroehlichSpencer.T12.Tails
public import FroehlichSpencer.Infra.Spectral.ResolventNorm
import FroehlichSpencer.IDS.Green
import FroehlichSpencer.Infra.Green.Iteration


@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


theorem norm_finiteGreen_le_of_gap {ν : ℕ} (B : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ)
    (hε : ε ≠ 0) {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ j, κ ≤ |(hamiltonian_isHermitian ν B v).eigenvalues j - E|)
    (u w : {x // x ∈ B}) : ‖finiteGreen ν B v E ε hε u w‖ ≤ 1 / κ := by
  have : Nonempty {x // x ∈ B} := ⟨u⟩
  unfold finiteGreen
  refine (Infra.norm_inv_sub_smul_one_apply_le (hamiltonian_isHermitian ν B v) _ u w).trans ?_
  apply one_div_le_one_div_of_le hκ
  refine Finset.le_inf' _ _ fun j _ => (hgap j).trans ?_
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  exact le_of_eq (by simp)

/--
With `X = max_{b, w ∈ B} ‖G_R(b, w)‖` one gets `X ≤ g + X / 2`, hence `X ≤ 2 g`.
-/
theorem norm_finiteGreen_le_of_twoCut {ν : ℕ} {R Cb B Q : Finset (Site ν)} (hB : B ⊆ Cb)
    (hCb : Cb ⊆ R) (hQ : Q = R \ B) (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0) {g η : ℝ}
    (hg0 : 0 ≤ g) (hη0 : 0 ≤ η)
    (hg : ∀ u w : {x // x ∈ Cb}, ‖finiteGreen ν Cb v E ε hε u w‖ ≤ g)
    (hη : ∀ c' q : {x // x ∈ Q}, (c' : Site ν) ∉ Cb → (∃ c ∈ Cb, hoppingKernel ν c c' ≠ 0) →
      (∃ b ∈ B, hoppingKernel ν q b ≠ 0) → ‖finiteGreen ν Q v E ε hε c' q‖ ≤ η)
    (hsmall : (2 * ν * Cb.card) * (2 * ν * B.card) * g * η ≤ 1 / 2)
    (u w : {x // x ∈ R}) (hu : (u : Site ν) ∈ B) (hw : (w : Site ν) ∈ B) :
    ‖finiteGreen ν R v E ε hε u w‖ ≤ 2 * g := by
  classical
  subst hQ
  set z : ℂ := (E : ℂ) + (ε : ℂ) * Complex.I with hz0
  have hz : z.im ≠ 0 := by simpa [hz0] using hε
  set a := hoppingKernel ν with ha
  set V : Site ν → ℝ := fun x => v x + 2 * (ν : ℝ) with hV
  have hsymm : ∀ x y, a y x = star (a x y) := hoppingKernel_symm ν
  have hBR : B ⊆ R := hB.trans hCb
  have hnorm_symm : ∀ x y, ‖a y x‖ = ‖a x y‖ := fun x y => by rw [hsymm x y, norm_star]
  have hunit : ∀ A : Finset (Site ν),
      IsUnit (Infra.restrictedOp a V A - z • (1 : Matrix A A ℂ)) := fun A =>
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (Infra.isHermitian_restrictedOp hsymm V A) z hz
  have hne : (B ×ˢ B).Nonempty := ⟨(u.1, w.1), Finset.mem_product.2 ⟨hu, hw⟩⟩
  set X := (B ×ˢ B).sup' hne (fun p => ‖Infra.resolventColumn a V R z p.2 p.1‖) with hX
  have hXle : ∀ b ∈ B, ∀ y ∈ B, ‖Infra.resolventColumn a V R z y b‖ ≤ X := fun b hb y hy =>
    Finset.le_sup' (f := fun p => ‖Infra.resolventColumn a V R z p.2 p.1‖) (b := (b, y))
      (Finset.mem_product.2 ⟨hb, hy⟩)
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hXle u.1 hu w.1 hw)
  set S1 : ℝ := 2 * ν * Cb.card with hS1
  set S2 : ℝ := 2 * ν * B.card with hS2
  have hS1_0 : 0 ≤ S1 :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hS2_0 : 0 ≤ S2 :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  -- row sums against the block `B`
  have hrow : ∀ s : Finset (Site ν), ∑ q ∈ s, ∑ b ∈ B, ‖a q b‖ ≤ S2 := fun s => by
    rw [Finset.sum_comm]
    calc ∑ b ∈ B, ∑ q ∈ s, ‖a q b‖ = ∑ b ∈ B, ∑ q ∈ s, ‖a b q‖ := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun q _ => ?_
          exact hnorm_symm b q
      _ ≤ ∑ _b ∈ B, (2 * (ν : ℝ)) :=
          Finset.sum_le_sum fun b _ => sum_norm_hoppingKernel_le ν b s
      _ = S2 := by rw [Finset.sum_const, nsmul_eq_mul, hS2]; ring
  -- the `Q`-cut: entries `G_R(y, c')` for `c' ∈ R \ Cb`
  have hcut : ∀ y ∈ B, ∀ c ∈ Cb, ∀ c' ∈ R \ Cb, a c c' ≠ 0 →
      ‖Infra.resolventColumn a V R z y c'‖ ≤ η * S2 * X := by
    intro y hy c hc c' hc' hcc'
    have hc'R := (Finset.mem_sdiff.1 hc').1
    have hc'Cb := (Finset.mem_sdiff.1 hc').2
    have hc'B : c' ∉ B := fun h => hc'Cb (hB h)
    have hc'Q : c' ∈ R \ B := Finset.mem_sdiff.2 ⟨hc'R, hc'B⟩
    have hyQ : y ∉ R \ B := fun h => (Finset.mem_sdiff.1 h).2 hy
    have hid := Infra.resolventColumn_eq_neg_sum_coupling (a := a) V Finset.sdiff_subset
      (hunit R) (hunit (R \ B)) hc'Q (hBR hy) hyQ
    rw [Finset.sdiff_sdiff_eq_self hBR] at hid
    rw [hid, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ R \ B, ‖∑ k' ∈ B, Infra.resolventColumn a V (R \ B) z k c' * a k k' *
            Infra.resolventColumn a V R z y k'‖
        ≤ ∑ k ∈ R \ B, ∑ k' ∈ B, η * ‖a k k'‖ * X := by
          refine Finset.sum_le_sum fun k hk => ?_
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
          rw [norm_mul, norm_mul]
          by_cases h0 : a k k' = 0
          · simp [h0]
          · have hkΛ : (k : Site ν) ∈ R \ B := hk
            have h1 := hη ⟨c', hc'Q⟩ ⟨k, hk⟩ hc'Cb ⟨c, hc, hcc'⟩ ⟨k', hk', h0⟩
            rw [finiteGreen_eq_resolventColumn] at h1
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
              (hXle k' hk' y hy) (norm_nonneg _) (mul_nonneg hη0 (norm_nonneg _))
      _ = η * X * ∑ k ∈ R \ B, ∑ k' ∈ B, ‖a k k'‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k' _ => by ring
      _ ≤ η * X * S2 := mul_le_mul_of_nonneg_left (hrow _) (mul_nonneg hη0 hX0)
      _ = η * S2 * X := by ring
  -- the `C̄`-cut
  have key : ∀ x ∈ B, ∀ y ∈ B, ‖Infra.resolventColumn a V R z y x‖ ≤ g + X / 2 := by
    intro x hx y hy
    have hxCb := hB hx
    have hyCb := hB hy
    have hid := resolventColumn_eq_sub_sum_coupling_of_mem (a := a) hsymm V hCb hz hxCb hyCb
    rw [hid]
    refine (norm_sub_le _ _).trans ?_
    have hg1 : ‖Infra.resolventColumn a V Cb z y x‖ ≤ g := by
      have := hg ⟨x, hxCb⟩ ⟨y, hyCb⟩
      rwa [finiteGreen_eq_resolventColumn] at this
    have hrest : ‖∑ k ∈ Cb, ∑ k' ∈ R \ Cb, Infra.resolventColumn a V Cb z k x * a k k' *
        Infra.resolventColumn a V R z y k'‖ ≤ X / 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Cb, ‖∑ k' ∈ R \ Cb, Infra.resolventColumn a V Cb z k x * a k k' *
            Infra.resolventColumn a V R z y k'‖
          ≤ ∑ k ∈ Cb, ∑ k' ∈ R \ Cb, g * ‖a k k'‖ * (η * S2 * X) := by
            refine Finset.sum_le_sum fun k hk => ?_
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
            rw [norm_mul, norm_mul]
            by_cases h0 : a k k' = 0
            · simp [h0]
            · have h1 := hg ⟨x, hxCb⟩ ⟨k, hk⟩
              rw [finiteGreen_eq_resolventColumn] at h1
              exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
                (hcut y hy k hk k' hk' h0) (norm_nonneg _) (mul_nonneg hg0 (norm_nonneg _))
        _ = g * (η * S2 * X) * ∑ k ∈ Cb, ∑ k' ∈ R \ Cb, ‖a k k'‖ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k' _ => by ring
        _ ≤ g * (η * S2 * X) * S1 := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg hg0 (mul_nonneg (mul_nonneg hη0 hS2_0) hX0))
            calc ∑ k ∈ Cb, ∑ k' ∈ R \ Cb, ‖a k k'‖ ≤ ∑ _k ∈ Cb, (2 * (ν : ℝ)) :=
                  Finset.sum_le_sum fun k _ => sum_norm_hoppingKernel_le ν k _
              _ = S1 := by rw [Finset.sum_const, nsmul_eq_mul, hS1]; ring
        _ = (S1 * S2 * g * η) * X := by ring
        _ ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right hsmall hX0
        _ = X / 2 := by ring
    linarith
  have hX2 : X ≤ g + X / 2 :=
    Finset.sup'_le _ _ fun p hp => by
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      exact key p.1 h1 p.2 h2
  rw [finiteGreen_eq_resolventColumn]
  have := hXle u.1 hu w.1 hw
  linarith


theorem norm_finiteGreen_resonantBlock_le_of_avoid {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m : ℝ} (hm : 0 ≤ m)
    (hJ : JPred P Λ v k m) {C : Set (Site ν)} (hC : C ∈ restrictedClasses P Λ v k)
    {R B : Finset (Site ν)}
    (hBN : (B : Set (Site ν)) ⊆ nbhd C (3 * scaleD P.K₀ k - 1))
    (hCR : nbhd C (4 * scaleD P.K₀ k) ⊆ R)
    (hQS : ∀ x ∈ (R \ B) ∩ Λ, x ∉ singularSetsIn P Λ v k)
    (hQadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R : Set (Site ν)) \ B))
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (ε : ℝ) (hε : ε ≠ 0) (u w : {x // x ∈ R ∩ Λ}) (hu : (u : Site ν) ∈ B)
    (hw : (w : Site ν) ∈ B) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε u w‖ ≤ 2 * Real.exp (Real.sqrt (scaleD P.K₀ k)) := by
  classical
  set d := scaleD P.K₀ k with hd
  have hK0 : 0 ≤ P.K₀ := by
    by_contra h
    push Not at h
    have h1 : scaleD P.K₀ 0 < 1 := by
      rw [scaleD_zero]
      exact (Real.exp_lt_exp.2 h).trans_eq Real.exp_zero
    linarith [hK.1]
  have hd1 : 1 ≤ d := one_le_scaleD hK0 k
  have hdpos : 0 < d := scaleD_pos _ _
  obtain ⟨hfin, hdiam, hgap⟩ := hC.2
  obtain ⟨c₀, hc₀⟩ :=
    (obstacleFamily_gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v).nonempty k C hC
  set Cb : Finset (Site ν) := thicken hfin.toFinset (4 * d) ∩ Λ with hCbdef
  have hBCb : B ∩ Λ ⊆ Cb := by
    intro x hx
    obtain ⟨hxB, hxΛ⟩ := Finset.mem_inter.1 hx
    obtain ⟨c, hcC, hxc⟩ := hBN (Finset.mem_coe.2 hxB)
    exact Finset.mem_inter.2 ⟨mem_thicken.2 ⟨c, hfin.mem_toFinset.2 hcC, by linarith⟩, hxΛ⟩
  have hCbR : Cb ⊆ R ∩ Λ := by
    intro x hx
    obtain ⟨hx1, hxΛ⟩ := Finset.mem_inter.1 hx
    obtain ⟨c, hc, hxc⟩ := mem_thicken.1 hx1
    exact Finset.mem_inter.2 ⟨hCR ⟨c, hfin.mem_toFinset.1 hc, hxc⟩, hxΛ⟩
  have hQeq : (R \ B) ∩ Λ = (R ∩ Λ) \ (B ∩ Λ) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  -- the gap estimate on the block `C̄`
  have hgap' : ∀ j, Real.exp (-Real.sqrt d) ≤
      |(hamiltonian_isHermitian ν Cb v).eigenvalues j - P.E| := hgap
  have hg : ∀ u w : {x // x ∈ Cb},
      ‖finiteGreen ν Cb v P.E ε hε u w‖ ≤ Real.exp (Real.sqrt d) := by
    intro u w
    have := norm_finiteGreen_le_of_gap Cb v P.E ε hε (Real.exp_pos _) hgap' u w
    rwa [one_div, ← Real.exp_neg, neg_neg] at this
  -- the decay estimate on the outer block `Q`
  have hadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R \ B : Finset (Site ν)) :
      Set (Site ν)) := by
    rw [Finset.coe_sdiff]
    exact hQadm
  have havoid := hQS
  have hη : ∀ c' q : {x // x ∈ (R \ B) ∩ Λ}, (c' : Site ν) ∉ Cb →
      (∃ c ∈ Cb, hoppingKernel ν c c' ≠ 0) → (∃ b ∈ B ∩ Λ, hoppingKernel ν q b ≠ 0) →
      ‖finiteGreen ν ((R \ B) ∩ Λ) v P.E ε hε c' q‖ ≤ Real.exp (-m * d) := by
    intro c' q hc' _ hex
    obtain ⟨b, hb, hqb⟩ := hex
    have hc'Λ := (Finset.mem_inter.1 c'.2).2
    have hqb1 : siteDist ν q b ≤ 1 := by
      rw [siteDist_eq_norm]
      exact IDS.norm_latticeCast_sub_le_one_of_hoppingKernel_ne_zero hqb
    obtain ⟨c, hcC, hbc⟩ := hBN (Finset.mem_coe.2 (Finset.mem_inter.1 hb).1)
    have hdist : d ≤ siteDist ν c' q := by
      by_contra hlt
      push Not at hlt
      apply hc'
      refine Finset.mem_inter.2 ⟨mem_thicken.2 ⟨c, hfin.mem_toFinset.2 hcC, ?_⟩, hc'Λ⟩
      have h1 := siteDist_triangle ν c' c q
      have h2 := siteDist_triangle ν q c b
      have h3 := siteDist_comm ν q c
      have h4 := siteDist_comm ν c' c
      have h5 := siteDist_comm ν b c
      linarith
    have h := hJ (R \ B) hadm havoid ε hε c' q (by linarith)
    refine h.trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left hdist hm
    linarith
  -- counting
  have hcard : (Cb.card : ℝ) ≤ (25 * d) ^ ν := by
    have hsub : Cb ⊆ Λ.filter (fun x => siteDist ν c₀ x ≤ 5 * d) := by
      intro x hx
      obtain ⟨hx1, hxΛ⟩ := Finset.mem_inter.1 hx
      obtain ⟨c, hc, hxc⟩ := mem_thicken.1 hx1
      have h1 := hdiam c₀ hc₀ c (hfin.mem_toFinset.1 hc)
      have h2 := siteDist_triangle ν c₀ x c
      have h3 := siteDist_comm ν c x
      exact Finset.mem_filter.2 ⟨hxΛ, by linarith⟩
    have := card_filter_siteDist_le Λ c₀ (R := 5 * d) (by linarith)
    calc (Cb.card : ℝ) ≤ ((Λ.filter fun x => siteDist ν c₀ x ≤ 5 * d).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (5 * (5 * d)) ^ ν := this
      _ = (25 * d) ^ ν := by ring_nf
  have hcardB : ((B ∩ Λ).card : ℝ) ≤ (25 * d) ^ ν :=
    (by exact_mod_cast Finset.card_le_card hBCb : ((B ∩ Λ).card : ℝ) ≤ Cb.card).trans hcard
  set N : ℝ := 2 * ν * (25 * d) ^ ν with hN
  have hN0 : 0 ≤ N := by positivity
  have hsmall' : (2 * ν * Cb.card) * (2 * ν * (B ∩ Λ).card) * Real.exp (Real.sqrt d) *
      Real.exp (-m * d) ≤ 1 / 2 := by
    have h1 : (2 * ν * Cb.card : ℝ) ≤ N :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    have h2 : (2 * ν * (B ∩ Λ).card : ℝ) ≤ N :=
      mul_le_mul_of_nonneg_left hcardB (by positivity)
    have h3 : (2 * ν * Cb.card : ℝ) * (2 * ν * (B ∩ Λ).card) ≤ N ^ 2 := by
      rw [sq]
      exact mul_le_mul h1 h2 (by positivity) hN0
    have h4 : Real.exp (Real.sqrt d) * Real.exp (-m * d) =
        Real.exp (Real.sqrt d - m * d) := by
      rw [← Real.exp_add]; ring_nf
    calc (2 * ν * Cb.card : ℝ) * (2 * ν * (B ∩ Λ).card) * Real.exp (Real.sqrt d) *
          Real.exp (-m * d)
        = ((2 * ν * Cb.card : ℝ) * (2 * ν * (B ∩ Λ).card)) *
          (Real.exp (Real.sqrt d) * Real.exp (-m * d)) := by ring
      _ ≤ N ^ 2 * Real.exp (Real.sqrt d - m * d) := by
          rw [h4]
          exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ 1 / 2 := hsmall
  have hu' : (u : Site ν) ∈ B ∩ Λ := Finset.mem_inter.2 ⟨hu, (Finset.mem_inter.1 u.2).2⟩
  have hw' : (w : Site ν) ∈ B ∩ Λ := Finset.mem_inter.2 ⟨hw, (Finset.mem_inter.1 w.2).2⟩
  exact norm_finiteGreen_le_of_twoCut hBCb hCbR hQeq v P.E ε hε (Real.exp_pos _).le
    (Real.exp_pos _).le hg hη hsmall' u w hu' hw'


theorem norm_finiteGreen_resonantBlock_le {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m : ℝ} (hm : 0 ≤ m)
    (hJ : JPred P Λ v k m) {C : Set (Site ν)} (hC : C ∈ restrictedClasses P Λ v k)
    {R B : Finset (Site ν)} (hCB : C ⊆ B)
    (hBN : (B : Set (Site ν)) ⊆ nbhd C (3 * scaleD P.K₀ k - 1))
    (hCR : nbhd C (4 * scaleD P.K₀ k) ⊆ R)
    (hRC : (R : Set (Site ν)) ⊆ nbhd C (scaleD P.K₀ (k + 1)))
    (hQadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R : Set (Site ν)) \ B))
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (ε : ℝ) (hε : ε ≠ 0) (u w : {x // x ∈ R ∩ Λ}) (hu : (u : Site ν) ∈ B)
    (hw : (w : Site ν) ∈ B) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε u w‖ ≤ 2 * Real.exp (Real.sqrt (scaleD P.K₀ k)) := by
  refine norm_finiteGreen_resonantBlock_le_of_avoid P hK Λ v k hm hJ hC hBN hCR ?_ hQadm
    hsmall ε hε u w hu hw
  have hCmem : C ∈ chainClusters (siteDist ν)
      (singularSetsGen P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v k) (2 * scaleR P.K₀ k) := hC.1
  intro x hx hxS
  obtain ⟨hxRB, hxΛ⟩ := Finset.mem_inter.1 hx
  obtain ⟨hxR, hxB⟩ := Finset.mem_sdiff.1 hxRB
  obtain ⟨c, hcC, hxc⟩ := hRC (Finset.mem_coe.2 hxR)
  obtain ⟨x₀, -, rfl⟩ := hCmem
  have hlt : siteDist ν c x < 2 * scaleR P.K₀ k := by
    rw [siteDist_comm, scaleR_eq_scaleD_succ]
    have := scaleD_pos P.K₀ (k + 1)
    linarith
  exact hxB (hCB (mem_chainCluster_of_lt hcC hxS hlt))

end FroehlichSpencer.T12

end
