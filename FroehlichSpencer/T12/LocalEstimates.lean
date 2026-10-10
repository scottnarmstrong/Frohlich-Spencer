/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.GentleRegion
public import FroehlichSpencer.T12.ResonantBlock


@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

private theorem local_facts {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m : ℝ} (hm : 0 ≤ m)
    (hJ : JPred P Λ v k m) {C : Set (Site ν)} (hC : C ∈ restrictedClasses P Λ v k)
    {R B : Finset (Site ν)}
    (hBN : (B : Set (Site ν)) ⊆ nbhd C (scaleD P.K₀ k / 3))
    (hCR : nbhd C (4 * scaleD P.K₀ k) ⊆ R)
    (hQadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R : Set (Site ν)) \ B))
    (hQS : ∀ x ∈ (R \ B) ∩ Λ, x ∉ singularSetsIn P Λ v k)
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (ε : ℝ) (hε : ε ≠ 0) :
    (B ∩ Λ ⊆ R ∩ Λ) ∧ ((R \ B) ∩ Λ ⊆ R ∩ Λ) ∧
    ((R ∩ Λ) \ ((R \ B) ∩ Λ) = B ∩ Λ) ∧
    (∀ Q' : Finset (Site ν), ∑ q ∈ Q', ∑ b ∈ B ∩ Λ, ‖hoppingKernel ν q b‖ ≤
      2 * ν * (25 * scaleD P.K₀ k) ^ ν) ∧
    (∀ b ∈ B ∩ Λ, ∀ b' ∈ B ∩ Λ,
      ‖greenEntry v P.E ε (R ∩ Λ) b b'‖ ≤ 2 * Real.exp (Real.sqrt (scaleD P.K₀ k))) := by
  classical
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
  obtain ⟨hfin, hdiam, -⟩ := hC.2
  obtain ⟨c₀, hc₀⟩ :=
    (obstacleFamily_gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v).nonempty k C hC
  have hBR : ∀ b ∈ B, b ∈ R := by
    intro b hb
    obtain ⟨c, hcC, hbc⟩ := hBN (Finset.mem_coe.2 hb)
    exact hCR ⟨c, hcC, by linarith only [hdpos, hbc]⟩
  have hBfA : B ∩ Λ ⊆ R ∩ Λ := fun x hx => by
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hx
    exact Finset.mem_inter.2 ⟨hBR x h1, h2⟩
  have hQeq : (R \ B) ∩ Λ = (R ∩ Λ) \ (B ∩ Λ) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hQA : (R \ B) ∩ Λ ⊆ R ∩ Λ := by
    rw [hQeq]; exact Finset.sdiff_subset
  have hAQ : (R ∩ Λ) \ ((R \ B) ∩ Λ) = B ∩ Λ := by
    rw [hQeq]; exact Finset.sdiff_sdiff_eq_self hBfA
  have hcard : ((B ∩ Λ).card : ℝ) ≤ (25 * d) ^ ν := by
    have hsub : B ∩ Λ ⊆ Λ.filter (fun x => siteDist ν c₀ x ≤ 5 * d) := by
      intro x hx
      obtain ⟨hxB, hxΛ⟩ := Finset.mem_inter.1 hx
      obtain ⟨c, hcC, hxc⟩ := hBN (Finset.mem_coe.2 hxB)
      have h1 := hdiam c₀ hc₀ c hcC
      have h2 := siteDist_triangle ν c₀ x c
      have h3 := siteDist_comm ν c x
      exact Finset.mem_filter.2 ⟨hxΛ, by linarith only [hdpos, hxc, h1, h2, h3]⟩
    have := card_filter_siteDist_le Λ c₀ (R := 5 * d) (by linarith only [hd1])
    calc ((B ∩ Λ).card : ℝ) ≤ ((Λ.filter fun x => siteDist ν c₀ x ≤ 5 * d).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (5 * (5 * d)) ^ ν := this
      _ = (25 * d) ^ ν := by ring_nf
  refine ⟨hBfA, hQA, hAQ, fun Q' => (sum_cross_le Q' (B ∩ Λ)).trans
    (mul_le_mul_of_nonneg_left hcard (by positivity)), ?_⟩
  intro b hb b' hb'
  have hb1 := Finset.mem_inter.1 hb
  have hb1' := Finset.mem_inter.1 hb'
  have hBN' : (B : Set (Site ν)) ⊆ nbhd C (3 * d - 1) := by
    intro x hx
    obtain ⟨c, hcC, hxc⟩ := hBN hx
    exact ⟨c, hcC, by linarith only [hd1, hxc]⟩
  have := norm_finiteGreen_resonantBlock_le_of_avoid P hK Λ v k hm hJ hC hBN' hCR hQS hQadm
    hsmall ε hε ⟨b, hBfA hb⟩ ⟨b', hBfA hb'⟩ hb1.1 hb1'.1
  rwa [greenEntry_eq] at this

private theorem exp_four_ge {d : ℝ} (hd1 : 1 ≤ d) :
    2 * Real.exp (Real.sqrt d) ≤ Real.exp (4 * Real.sqrt d) := by
  have h1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hd1
  have h2 : (2 : ℝ) ≤ Real.exp (3 * Real.sqrt d) := by
    have := Real.add_one_le_exp (3 * Real.sqrt d); linarith only [h1, this]
  calc 2 * Real.exp (Real.sqrt d) ≤ Real.exp (3 * Real.sqrt d) * Real.exp (Real.sqrt d) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (4 * Real.sqrt d) := by rw [← Real.exp_add]; ring_nf

/--
The hypotheses
`hsmall`, `hloc` are the explicit scale conditions behind "for `d₀` large".
-/
theorem norm_finiteGreen_localEntry_le {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m X : ℝ} (hm : 0 ≤ m) (hX : 1 ≤ X)
    (hJ : JPred P Λ v k m) (hN : NPred P Λ v k X) {C : Set (Site ν)}
    (hC : C ∈ restrictedClasses P Λ v k) {R B : Finset (Site ν)}
    (hBN : (B : Set (Site ν)) ⊆ nbhd C (scaleD P.K₀ k / 3))
    (hCR : nbhd C (4 * scaleD P.K₀ k) ⊆ R)
    (hQadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R : Set (Site ν)) \ B))
    (hQS : ∀ x ∈ (R \ B) ∩ Λ, x ∉ singularSetsIn P Λ v k)
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hloc : X + (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * X ^ 2 *
      (2 * Real.exp (Real.sqrt (scaleD P.K₀ k))) ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)))
    (ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ R ∩ Λ}) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)) := by
  classical
  obtain ⟨x, hxA⟩ := x
  obtain ⟨y, hyA⟩ := y
  obtain ⟨hBfA, hQA, hAQ, hPN', hresB⟩ :=
    local_facts P hK Λ v k hm hJ hC hBN hCR hQadm hQS hsmall ε hε
  have hadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R \ B : Finset (Site ν)) :
      Set (Site ν)) := by
    rw [Finset.coe_sdiff]
    exact hQadm
  have hK0 : 0 ≤ P.K₀ := by
    by_contra h
    push Not at h
    have h1 : scaleD P.K₀ 0 < 1 := by
      rw [scaleD_zero]
      exact (Real.exp_lt_exp.2 h).trans_eq Real.exp_zero
    linarith only [h1, hK.1]
  set d := scaleD P.K₀ k with hd
  have hd1 : 1 ≤ d := one_le_scaleD hK0 k
  have hXQ : ∀ s ∈ (R \ B) ∩ Λ, ∀ q ∈ (R \ B) ∩ Λ,
      ‖greenEntry v P.E ε ((R \ B) ∩ Λ) s q‖ ≤ X := by
    intro s hs q hq
    have := hN (R \ B) hadm hQS ε hε ⟨s, hs⟩ ⟨q, hq⟩
    rwa [greenEntry_eq] at this
  set A : Finset (Site ν) := R ∩ Λ with hA
  set Bf : Finset (Site ν) := B ∩ Λ with hBf
  set Q : Finset (Site ν) := (R \ B) ∩ Λ with hQ
  set N : ℝ := 2 * ν * (25 * d) ^ ν with hNdef
  set L : ℝ := 2 * Real.exp (Real.sqrt d) with hL
  have hN0 : 0 ≤ N := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hX0 : 0 ≤ X := by linarith only [hX]
  have hN1 : N = 0 ∨ 1 ≤ N := by
    rcases Nat.eq_zero_or_pos ν with h | h
    · left; simp [hNdef, h]
    · right
      have h1 : (1 : ℝ) ≤ ν := by exact_mod_cast h
      have h2 : 1 ≤ (25 * d) ^ ν := one_le_pow₀ (by linarith only [hd1])
      rw [hNdef]; nlinarith only [h1, h2]
  set E4 := Real.exp (4 * Real.sqrt d) with hE4
  have hLE : L ≤ E4 := exp_four_ge hd1
  have hbig : N ^ 2 * X ^ 2 * L ≤ E4 := by nlinarith only [hX0, hloc]
  have hLXN : L * (X * N) ≤ E4 := by
    refine le_trans ?_ hbig
    rcases hN1 with h | h
    · rw [h]; simp
    · have h3 : N ≤ N ^ 2 := by nlinarith only [h]
      have h4 : X ≤ X ^ 2 := by nlinarith only [hX]
      calc L * (X * N) ≤ L * (X ^ 2 * N ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h4 h3 hN0 (by positivity)) hL0
        _ = N ^ 2 * X ^ 2 * L := by ring
  have hQnotB : ∀ t ∈ Bf, t ∉ Q := fun t ht h =>
    (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).1).2 (Finset.mem_inter.1 ht).1
  have hQB : ∀ s ∈ Q, ∀ t ∈ Bf, ‖greenEntry v P.E ε A s t‖ ≤ L * (X * N) := by
    intro s hs t ht
    rw [greenEntry_neg_sum v P.E ε hε hQA hs (hBfA ht) (hQnotB t ht), hAQ, norm_neg]
    refine (norm_cross_sum_le v P.E ε Q Bf A s t (w := fun _ => X)
      (fun q hq b _ _ => hXQ s hs q hq) (fun b hb => hresB b hb t ht)
      (fun _ => hX0)).trans ?_
    exact mul_le_mul_of_nonneg_left ((sum_weighted_le Q Bf (fun _ => X)
      (fun _ _ _ _ _ => le_rfl)).trans (mul_le_mul_of_nonneg_left (hPN' Q) hX0)) hL0
  have hcls : ∀ z : Site ν, z ∈ A → z ∈ Bf ∨ z ∈ Q := by
    intro z hz
    obtain ⟨hzR, hzΛ⟩ := Finset.mem_inter.1 hz
    by_cases hzB : z ∈ B
    · exact Or.inl (Finset.mem_inter.2 ⟨hzB, hzΛ⟩)
    · exact Or.inr (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hzR, hzB⟩, hzΛ⟩)
  rw [greenEntry_eq]
  rcases hcls x hxA with hxB | hxQ
  · rcases hcls y hyA with hyB | hyQ
    · exact (hresB x hxB y hyB).trans hLE
    · rw [greenEntry_symm]; exact (hQB y hyQ x hxB).trans hLXN
  · rcases hcls y hyA with hyB | hyQ
    · exact (hQB x hxQ y hyB).trans hLXN
    · rw [greenEntry_sub_sum v P.E ε hε hQA hxQ hyQ, hAQ]
      refine (norm_sub_le _ _).trans ?_
      have h1 := norm_cross_sum_le v P.E ε Q Bf A x y (w := fun _ => X) (h := L * (X * N))
        (fun q hq b _ _ => hXQ x hxQ q hq)
        (fun b hb => by rw [greenEntry_symm]; exact hQB y hyQ b hb) (fun _ => hX0)
      have h2 := (sum_weighted_le Q Bf (fun _ => X) (K := X)
        (fun _ _ _ _ _ => le_rfl)).trans (mul_le_mul_of_nonneg_left (hPN' Q) hX0)
      have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ L * (X * N) by positivity)
      have h4 := hXQ x hxQ y hyQ
      nlinarith only [h1, h3, h4, hloc]

private theorem admissible_mono {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n n' : ℕ}
    {A : Set (Site ν)} (h : Admissible K₀ G n A) (hn : n' ≤ n) : Admissible K₀ G n' A :=
  fun j hj => h j (lt_of_lt_of_le hj hn)


theorem norm_finiteGreen_localEntry_le_of_avoid {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (k : ℕ) {X : ℝ} (hN : NPred P Λ v k X)
    (hX4 : X ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k))) {R : Finset (Site ν)}
    (hRadm : Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) (R : Set (Site ν)))
    (hRS : ∀ x ∈ R ∩ Λ, x ∉ singularSetsIn P Λ v k) (ε : ℝ) (hε : ε ≠ 0)
    (x y : {x // x ∈ R ∩ Λ}) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)) :=
  (hN R (admissible_mono hRadm (Nat.le_succ k)) hRS ε hε x y).trans hX4


theorem norm_finiteGreen_longRange_le_of_avoid {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (k : ℕ) {m τ : ℝ} (hτ0 : 0 ≤ τ) (hJ : JPred P Λ v k m)
    (hd : 1 ≤ scaleD P.K₀ k) {R : Finset (Site ν)}
    (hRadm : Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) (R : Set (Site ν)))
    (hRS : ∀ x ∈ R ∩ Λ, x ∉ singularSetsIn P Λ v k) (ε : ℝ) (hε : ε ≠ 0)
    (x y : {x // x ∈ R ∩ Λ}) (hxy : scaleD P.K₀ k ^ (9 / 8 : ℝ) ≤ siteDist ν x y) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (-(m - τ) * siteDist ν x y) := by
  have h1 : scaleD P.K₀ k ≤ scaleD P.K₀ k ^ (9 / 8 : ℝ) := by
    calc scaleD P.K₀ k = scaleD P.K₀ k ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hd (by norm_num)
  have h0 : 0 ≤ siteDist ν x y := siteDist_nonneg ν _ _
  refine (hJ R (admissible_mono hRadm (Nat.le_succ k)) hRS ε hε x y
    (by linarith only [hxy, h1, h0])).trans (Real.exp_le_exp.2 ?_)
  nlinarith only [mul_nonneg hτ0 h0]

private theorem pure_QB {d m X N D : ℝ} (hm : 0 ≤ m) (hd0 : 0 ≤ d) (hX : 1 ≤ X) (hN0 : 0 ≤ N)
    (hN1 : N = 0 ∨ 1 ≤ N) :
    2 * Real.exp (Real.sqrt d) * (X * Real.exp (m * (d / 5) - m * (D - (2 * d + 1))) * N) ≤
      Real.exp (-m * D) *
        (2 * N ^ 2 * X ^ 2 * Real.exp (Real.sqrt d + m * (2 * d + 2 + 2 * d / 5))) := by
  have h1 : Real.exp (m * (d / 5) - m * (D - (2 * d + 1))) ≤
      Real.exp (-m * D) * Real.exp (m * (2 * d + 2 + 2 * d / 5)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith only [hm, mul_nonneg hm hd0]
  have hXN : X * N ≤ X ^ 2 * N ^ 2 := by
    rcases hN1 with h | h
    · rw [h]; simp
    · have h3 : N ≤ N ^ 2 := by nlinarith only [h]
      have h4 : X ≤ X ^ 2 := by nlinarith only [hX]
      exact mul_le_mul h4 h3 hN0 (by positivity)
  have hE1 := Real.exp_pos (Real.sqrt d)
  have hX0 : 0 ≤ X := by linarith only [hX]
  calc 2 * Real.exp (Real.sqrt d) * (X * Real.exp (m * (d / 5) - m * (D - (2 * d + 1))) * N)
      = 2 * Real.exp (Real.sqrt d) * (X * N) *
        Real.exp (m * (d / 5) - m * (D - (2 * d + 1))) := by ring
    _ ≤ 2 * Real.exp (Real.sqrt d) * (X ^ 2 * N ^ 2) *
        (Real.exp (-m * D) * Real.exp (m * (2 * d + 2 + 2 * d / 5))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXN (by positivity)) h1 (Real.exp_pos _).le
          (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

private theorem pure_QQ {d m X N D : ℝ} :
    2 * Real.exp (Real.sqrt d) *
      (X * X * Real.exp (2 * (m * (d / 5)) - m * (D - (2 * d + 2))) * N * N) =
      Real.exp (-m * D) *
        (2 * N ^ 2 * X ^ 2 * Real.exp (Real.sqrt d + m * (2 * d + 2 + 2 * d / 5))) := by
  have : Real.exp (2 * (m * (d / 5)) - m * (D - (2 * d + 2))) =
      Real.exp (-m * D) * Real.exp (m * (2 * d + 2 + 2 * d / 5)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this, Real.exp_add]; ring

private theorem three_d_le {d : ℝ} (hd : 3 ^ 8 ≤ d) : 3 * d ≤ d ^ (9 / 8 : ℝ) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have h3 : (3 : ℝ) ≤ d ^ (1 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hd (show (0 : ℝ) ≤ 1 / 8 by norm_num)
    have e : ((3 : ℝ) ^ 8) ^ (1 / 8 : ℝ) = 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rwa [e] at h
  have e2 : d ^ (9 / 8 : ℝ) = d * d ^ (1 / 8 : ℝ) := by
    rw [show (9 / 8 : ℝ) = 1 + 1 / 8 by norm_num, Real.rpow_add hdpos, Real.rpow_one]
  rw [e2]; nlinarith only [hdpos, h3]

/--
The hypotheses `hd`, `hsmall`, `hτ` are the explicit scale conditions
behind "for `d₀` large" (`τ ≥ 0` follows from `hτ`).
-/
theorem norm_finiteGreen_longRange_le {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m X τ : ℝ} (hm : 0 ≤ m) (hX : 1 ≤ X)
    (hJ : JPred P Λ v k m) (hN : NPred P Λ v k X) {C : Set (Site ν)}
    (hC : C ∈ restrictedClasses P Λ v k) {R B : Finset (Site ν)}
    (hBN : (B : Set (Site ν)) ⊆ nbhd C (scaleD P.K₀ k / 3))
    (hCR : nbhd C (4 * scaleD P.K₀ k) ⊆ R)
    (hQadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R : Set (Site ν)) \ B))
    (hQS : ∀ x ∈ (R \ B) ∩ Λ, x ∉ singularSetsIn P Λ v k)
    (hBdiam : DiamLE (siteDist ν) (B : Set (Site ν)) (2 * scaleD P.K₀ k))
    (hd : 3 ^ 8 ≤ scaleD P.K₀ k)
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hτ : Real.log (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * X ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) +
        m * (2 * scaleD P.K₀ k + 2 + 2 * scaleD P.K₀ k / 5))) ≤
        τ * scaleD P.K₀ k ^ (9 / 8 : ℝ))
    (ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ R ∩ Λ})
    (hxy : scaleD P.K₀ k ^ (9 / 8 : ℝ) ≤ siteDist ν x y) :
    ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (-(m - τ) * siteDist ν x y) := by
  classical
  obtain ⟨x, hxA⟩ := x
  obtain ⟨y, hyA⟩ := y
  obtain ⟨hBfA, hQA, hAQ, hPN', hresB⟩ :=
    local_facts P hK Λ v k hm hJ hC hBN hCR hQadm hQS hsmall ε hε
  have hadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R \ B : Finset (Site ν)) :
      Set (Site ν)) := by
    rw [Finset.coe_sdiff]
    exact hQadm
  have hK0 : 0 ≤ P.K₀ := by
    by_contra h
    push Not at h
    have h1 : scaleD P.K₀ 0 < 1 := by
      rw [scaleD_zero]
      exact (Real.exp_lt_exp.2 h).trans_eq Real.exp_zero
    linarith only [h1, hK.1]
  set d := scaleD P.K₀ k with hdd
  have hd1 : 1 ≤ d := one_le_scaleD hK0 k
  have hdpos : 0 < d := scaleD_pos _ _
  have hT3 : 3 * d ≤ d ^ (9 / 8 : ℝ) := three_d_le hd
  have hXQ : ∀ s ∈ (R \ B) ∩ Λ, ∀ q ∈ (R \ B) ∩ Λ,
      ‖greenEntry v P.E ε ((R \ B) ∩ Λ) s q‖ ≤ X := by
    intro s hs q hq
    have := hN (R \ B) hadm hQS ε hε ⟨s, hs⟩ ⟨q, hq⟩
    rwa [greenEntry_eq] at this
  have hJQ : ∀ s ∈ (R \ B) ∩ Λ, ∀ q ∈ (R \ B) ∩ Λ, d / 5 ≤ siteDist ν s q →
      ‖greenEntry v P.E ε ((R \ B) ∩ Λ) s q‖ ≤ Real.exp (-m * siteDist ν s q) := by
    intro s hs q hq h
    have := hJ (R \ B) hadm hQS ε hε ⟨s, hs⟩ ⟨q, hq⟩ h
    rwa [greenEntry_eq] at this
  set A : Finset (Site ν) := R ∩ Λ with hA
  set Bf : Finset (Site ν) := B ∩ Λ with hBf
  set Q : Finset (Site ν) := (R \ B) ∩ Λ with hQ
  set N : ℝ := 2 * ν * (25 * d) ^ ν with hNdef
  set L : ℝ := 2 * Real.exp (Real.sqrt d) with hL
  set T : ℝ := d ^ (9 / 8 : ℝ) with hTdef
  have hN0 : 0 ≤ N := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hX0 : 0 ≤ X := by linarith only [hX]
  have hTpos : 0 < T := by linarith only [hdpos, hT3]
  have hN1 : N = 0 ∨ 1 ≤ N := by
    rcases Nat.eq_zero_or_pos ν with h | h
    · left; simp [hNdef, h]
    · right
      have h1 : (1 : ℝ) ≤ ν := by exact_mod_cast h
      have h2 : 1 ≤ (25 * d) ^ ν := one_le_pow₀ (by linarith only [hd1])
      rw [hNdef]; nlinarith only [h1, h2]
  set Y : ℝ := 2 * N ^ 2 * X ^ 2 *
    Real.exp (Real.sqrt d + m * (2 * d + 2 + 2 * d / 5)) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hτT : 0 ≤ τ * T := (Real.log_nonneg (by linarith only [hY0])).trans hτ
  have hτ0 : 0 ≤ τ := (mul_nonneg_iff_of_pos_right hTpos).1 hτT
  have h1Y : 1 + Y ≤ Real.exp (τ * T) := (Real.log_le_iff_le_exp (by linarith only [hY0])).1 hτ
  -- the leg bound
  set Wf : ℝ → ℝ := fun r => X * Real.exp (m * (d / 5) - m * r) with hWf
  have hWf0 : ∀ r, 0 ≤ Wf r := fun r => by positivity
  have hleg : ∀ s ∈ Q, ∀ q ∈ Q, ‖greenEntry v P.E ε Q s q‖ ≤ Wf (siteDist ν s q) := by
    intro s hs q hq
    by_cases h : d / 5 ≤ siteDist ν s q
    · refine (hJQ s hs q hq h).trans ?_
      have h1 : Real.exp (-m * siteDist ν s q) ≤ Real.exp (m * (d / 5) - m * siteDist ν s q) :=
        Real.exp_le_exp.2 (by nlinarith only [mul_nonneg hm hdpos.le])
      have := Real.exp_pos (m * (d / 5) - m * siteDist ν s q)
      show _ ≤ X * _
      nlinarith only [hX, h1, this]
    · push Not at h
      refine (hXQ s hs q hq).trans ?_
      have h1 : 1 ≤ Real.exp (m * (d / 5) - m * siteDist ν s q) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.2 (by nlinarith only [mul_nonneg hm (sub_nonneg.2 h.le)])
      show X ≤ X * _
      nlinarith only [hX0, h1]
  have hQnotB : ∀ t ∈ Bf, t ∉ Q := fun t ht h =>
    (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).1).2 (Finset.mem_inter.1 ht).1
  have hrow : ∀ b ∈ Bf, ∀ b' ∈ Bf, siteDist ν b b' ≤ 2 * d := fun b hb b' hb' =>
    hBdiam b (Finset.mem_coe.2 (Finset.mem_inter.1 hb).1) b'
      (Finset.mem_coe.2 (Finset.mem_inter.1 hb').1)
  -- `s ∈ Q`, `t ∈ A`, far apart
  have hQany : ∀ s t : Site ν, s ∈ Q → t ∈ A → T ≤ siteDist ν s t →
      (t ∈ Bf ∨ t ∈ Q) → ‖greenEntry v P.E ε A s t‖ ≤ Real.exp (-m * siteDist ν s t) * (1 + Y) := by
    intro s t hsQ htA hL5 hcase
    set D := siteDist ν s t with hD
    have hexp0 : (0 : ℝ) < Real.exp (-m * D) := Real.exp_pos _
    have hQs : ∀ q ∈ Q, ‖greenEntry v P.E ε Q s q‖ ≤ Wf (siteDist ν s q) :=
      fun q hq => hleg s hsQ q hq
    rcases hcase with htB | htQ
    · rw [greenEntry_neg_sum v P.E ε hε hQA hsQ htA (hQnotB t htB), hAQ, norm_neg]
      refine (norm_cross_sum_le v P.E ε Q Bf A s t (w := fun q => Wf (siteDist ν s q))
        (fun q hq b _ _ => hQs q hq) (fun b hb => hresB b hb t htB)
        (fun q => hWf0 _)).trans ?_
      set K2 : ℝ := X * Real.exp (m * (d / 5) - m * (D - (2 * d + 1))) with hK2
      have hK2' : ∑ q ∈ Q, ∑ b ∈ Bf, Wf (siteDist ν s q) * ‖hoppingKernel ν q b‖ ≤
          K2 * ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖ := by
        refine sum_weighted_le Q Bf _ fun q hq b hb h0 => ?_
        have h1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
        have h4 := siteDist_triangle ν s t q
        have h5 := siteDist_triangle ν q t b
        have h6 := hrow b hb t htB
        have h7 := siteDist_comm ν q t
        have h8 : D - (2 * d + 1) ≤ siteDist ν s q := by
          have := siteDist_comm ν q t
          have h9 := siteDist_triangle ν s t q
          linarith only [h1, h5, h6, h9]
        show X * _ ≤ X * _
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hX0
        have := mul_le_mul_of_nonneg_left h8 hm
        linarith only [this]
      have hK20 : 0 ≤ K2 := by positivity
      calc L * ∑ q ∈ Q, ∑ b ∈ Bf, Wf (siteDist ν s q) * ‖hoppingKernel ν q b‖
          ≤ L * (K2 * ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) :=
            mul_le_mul_of_nonneg_left hK2' hL0
        _ ≤ L * (K2 * N) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hPN' Q) hK20) hL0
        _ ≤ Real.exp (-m * D) * Y := pure_QB hm hdpos.le hX hN0 hN1
        _ ≤ _ := by nlinarith only [hexp0]
    · have hQt : ∀ q ∈ Q, ‖greenEntry v P.E ε Q t q‖ ≤ Wf (siteDist ν t q) :=
        fun q hq => hleg t htQ q hq
      set Sy := ∑ q ∈ Q, ∑ b ∈ Bf, Wf (siteDist ν t q) * ‖hoppingKernel ν q b‖ with hSy
      set Sx := ∑ q ∈ Q, ∑ b ∈ Bf, Wf (siteDist ν s q) * ‖hoppingKernel ν q b‖ with hSx
      have hSy0 : 0 ≤ Sy := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (hWf0 _) (norm_nonneg _)
      have hstep2 : ∀ b ∈ Bf, ‖greenEntry v P.E ε A b t‖ ≤ L * Sy := by
        intro b hb
        have hbA : b ∈ A := hBfA hb
        rw [greenEntry_symm, greenEntry_neg_sum v P.E ε hε hQA htQ hbA (hQnotB b hb), hAQ,
          norm_neg]
        exact norm_cross_sum_le v P.E ε Q Bf A t b (w := fun q => Wf (siteDist ν t q))
          (fun q hq _ _ _ => hQt q hq)
          (fun b' hb' => hresB b' hb' b hb) (fun q => hWf0 _)
      rw [greenEntry_sub_sum v P.E ε hε hQA hsQ htQ, hAQ]
      refine (norm_sub_le _ _).trans ?_
      have hJst : ‖greenEntry v P.E ε Q s t‖ ≤ Real.exp (-m * D) :=
        hJQ s hsQ t htQ (by linarith only [hT3, hTpos, hL5])
      have h1 := norm_cross_sum_le v P.E ε Q Bf A s t (w := fun q => Wf (siteDist ν s q))
        (fun q hq b _ _ => hQs q hq) hstep2 (fun q => hWf0 _)
      set K : ℝ := X * X * Real.exp (2 * (m * (d / 5)) - m * (D - (2 * d + 2))) with hKdef
      have hprod : Sx * Sy ≤ K * (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) *
          (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) := by
        refine prod_sum_le Q Bf (fun q => Wf (siteDist ν s q))
          (fun q => Wf (siteDist ν t q)) fun q hq b hb q' hq' b' hb' h0 h0' => ?_
        have e1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
        have e2 := siteDist_eq_one_of_hoppingKernel_ne_zero h0'
        have h5 := siteDist_triangle ν s t q
        have h6 := siteDist_triangle ν q t b
        have h7 := siteDist_triangle ν b t b'
        have h8 := siteDist_triangle ν b' t q'
        have h9 := hrow b hb b' hb'
        have h11 := siteDist_comm ν b' q'
        have h12 := siteDist_comm ν q' t
        have h13 := siteDist_comm ν q t
        have h13' := siteDist_comm ν b' t
        have h14 : D - (2 * d + 2) ≤ siteDist ν s q + siteDist ν t q' := by
          linarith only [e1, e2, h5, h6, h7, h8, h9, h11, h12]
        have h15 := mul_le_mul_of_nonneg_left h14 hm
        show X * Real.exp (m * (d / 5) - m * siteDist ν s q) *
          (X * Real.exp (m * (d / 5) - m * siteDist ν t q')) ≤ _
        have e3 : X * Real.exp (m * (d / 5) - m * siteDist ν s q) *
            (X * Real.exp (m * (d / 5) - m * siteDist ν t q')) = X * X *
            Real.exp ((m * (d / 5) - m * siteDist ν s q) +
              (m * (d / 5) - m * siteDist ν t q')) := by rw [Real.exp_add]; ring
        rw [e3]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        linarith only [h15]
      have hK0' : 0 ≤ K := by positivity
      have hP0 : 0 ≤ ∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hKPP : K * (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) *
          (∑ q ∈ Q, ∑ b ∈ Bf, ‖hoppingKernel ν q b‖) ≤ K * N * N := by
        have := hPN' Q
        gcongr
      have hmain : L * Sy * Sx ≤ Real.exp (-m * D) * Y := by
        calc L * Sy * Sx = L * (Sx * Sy) := by ring
          _ ≤ L * (K * N * N) := mul_le_mul_of_nonneg_left (hprod.trans hKPP) hL0
          _ = Real.exp (-m * D) * Y := pure_QQ
      nlinarith only [h1, hmain, hJst]
  have hcls : ∀ z : Site ν, z ∈ A → z ∈ Bf ∨ z ∈ Q := by
    intro z hz
    obtain ⟨hzR, hzΛ⟩ := Finset.mem_inter.1 hz
    by_cases hzB : z ∈ B
    · exact Or.inl (Finset.mem_inter.2 ⟨hzB, hzΛ⟩)
    · exact Or.inr (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hzR, hzB⟩, hzΛ⟩)
  have hkey : ‖greenEntry v P.E ε A x y‖ ≤ Real.exp (-m * siteDist ν x y) * (1 + Y) := by
    rcases hcls x hxA with hxB | hxQ
    · rcases hcls y hyA with hyB | hyQ
      · exfalso
        have := hrow x hxB y hyB
        linarith only [hxy, hT3, hTpos, this]
      · rw [greenEntry_symm, siteDist_comm]
        exact hQany y x hyQ hxA (by rwa [siteDist_comm]) (Or.inl hxB)
    · exact hQany x y hxQ hyA hxy (hcls y hyA)
  rw [greenEntry_eq]
  refine hkey.trans ?_
  have hxy' : τ * T ≤ τ * siteDist ν x y := mul_le_mul_of_nonneg_left hxy hτ0
  calc Real.exp (-m * siteDist ν x y) * (1 + Y)
      ≤ Real.exp (-m * siteDist ν x y) * Real.exp (τ * T) :=
        mul_le_mul_of_nonneg_left h1Y (Real.exp_pos _).le
    _ = Real.exp (-m * siteDist ν x y + τ * T) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith only [hxy'])

end FroehlichSpencer.T12

end
