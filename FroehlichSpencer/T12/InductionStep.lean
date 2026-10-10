/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.LocalEstimates
public import FroehlichSpencer.T12.FirstExitIteration
public import FroehlichSpencer.T12.FirstExit
public import FroehlichSpencer.T12.LowCut
public import FroehlichSpencer.T12.InductionDefs
public import FroehlichSpencer.T12.GentleRegion
public import FroehlichSpencer.T12.Tails

/-!
# The induction step `(J_k, N_k) ⇒ (J_{k+1}, N_{k+1})`

Around each
point of a `k`-admissible parent a first-exit region carries the local estimates (4.1), (4.2);
the decay `J_{k+1}` follows from the weighted-sup first-exit iteration and `N_{k+1}` from one
application of the first-exit identity.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

private theorem one_le_normBound (K₀ : ℝ) (k : ℕ) : 1 ≤ normBound K₀ k := by
  unfold normBound
  split_ifs
  · exact le_rfl
  · exact Real.one_le_exp (by positivity)

private theorem normBound_succ (K₀ : ℝ) (k : ℕ) :
    normBound K₀ (k + 1) = Real.exp (8 * Real.sqrt (scaleD K₀ k)) := by
  simp [normBound]

private theorem scaleD_succ_eq (K₀ : ℝ) (k : ℕ) :
    scaleD K₀ (k + 1) = scaleD K₀ k ^ (5 / 4 : ℝ) := (scaleR_eq_scaleD_succ K₀ k).symm

/-- Scale arithmetic: `3 d ≤ T`, `2 T ≤ D`, `10 ≤ D` for `d = d_k ≥ 3^8`. -/
private theorem scale_facts {d D : ℝ} (hd : 3 ^ 8 ≤ d) (hD : D = d ^ (5 / 4 : ℝ)) :
    3 * d ≤ d ^ (9 / 8 : ℝ) ∧ 2 * d ^ (9 / 8 : ℝ) ≤ D ∧ 10 ≤ D := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have h3 : (3 : ℝ) ≤ d ^ (1 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hd (show (0 : ℝ) ≤ 1 / 8 by norm_num)
    have e : ((3 : ℝ) ^ 8) ^ (1 / 8 : ℝ) = 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rwa [e] at h
  have e2 : d ^ (9 / 8 : ℝ) = d * d ^ (1 / 8 : ℝ) := by
    rw [show (9 / 8 : ℝ) = 1 + 1 / 8 by norm_num, Real.rpow_add hdpos, Real.rpow_one]
  have e3 : D = d * d ^ (1 / 4 : ℝ) := by
    rw [hD, show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hdpos, Real.rpow_one]
  have h4 : d ^ (1 / 8 : ℝ) ≤ d ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hd]) (by norm_num)
  have h4' : d ^ (1 / 8 : ℝ) * d ^ (1 / 8 : ℝ) = d ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hdpos]; norm_num
  have h9 : (9 : ℝ) ≤ d ^ (1 / 4 : ℝ) := by nlinarith only [h3, h4']
  have h5 : 2 * d ^ (1 / 8 : ℝ) ≤ d ^ (1 / 4 : ℝ) := by nlinarith only [h4', h9]
  refine ⟨by rw [e2]; nlinarith only [hdpos, h3], ?_, ?_⟩
  · rw [e2, e3]; nlinarith only [mul_le_mul_of_nonneg_left h5 hdpos.le]
  · rw [e3]; nlinarith only [hd, h9]

/-- The local estimates (4.1) and (4.2) on a first-exit region `R` (finite, `(k+1)`-admissible,
of diameter `≤ 3 d_{k+1}/2`, with active domain avoiding `S_{k+1}^Λ`). -/
private theorem local_est {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (k : ℕ) {m τ : ℝ} (hm : 0 ≤ m) (hJ : JPred P Λ v k m)
    (hN : NPred P Λ v k (normBound P.K₀ k)) (hd : 3 ^ 8 ≤ scaleD P.K₀ k)
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hloc : normBound P.K₀ k + (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      (2 * Real.exp (Real.sqrt (scaleD P.K₀ k))) ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)))
    (hτ : Real.log (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) +
        m * (2 * scaleD P.K₀ k + 2 + 2 * scaleD P.K₀ k / 5))) ≤
        τ * scaleD P.K₀ k ^ (9 / 8 : ℝ))
    {R : Finset (Site ν)}
    (hRadm : Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) (R : Set (Site ν)))
    (hRdiam : DiamLE (siteDist ν) (R : Set (Site ν)) (3 * scaleD P.K₀ (k + 1) / 2))
    (hRS : ∀ x ∈ R ∩ Λ, x ∉ singularSetsIn P Λ v (k + 1)) (ε : ℝ) (hε : ε ≠ 0) :
    (∀ x y : {x // x ∈ R ∩ Λ},
      ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k))) ∧
    (∀ x y : {x // x ∈ R ∩ Λ}, scaleD P.K₀ k ^ (9 / 8 : ℝ) ≤ siteDist ν x y →
      ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (-(m - τ) * siteDist ν x y)) := by
  classical
  have hX := one_le_normBound P.K₀ k
  have hG := obstacleFamily_gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v
  have hdpos := scaleD_pos P.K₀ k
  have hX4 : normBound P.K₀ k ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)) := by
    have : 0 ≤ (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      (2 * Real.exp (Real.sqrt (scaleD P.K₀ k))) := by positivity
    linarith only [hloc, this]
  have hRS' : ∀ x ∈ (R : Set (Site ν)), x ∉ singularSetsIn P Λ v (k + 1) := fun x hx hxS =>
    hRS x (Finset.mem_inter.2 ⟨hx, singularSetsIn_subset (P := P) (v := v) Λ _ hxS⟩) hxS
  rcases firstExit_cases P Λ v k hRadm hRdiam hRS' with hav | ⟨C, hC, hCR, hall⟩
  · have hav' : ∀ x ∈ R ∩ Λ, x ∉ singularSetsIn P Λ v k := fun x hx =>
      hav x (Finset.mem_inter.1 hx).1
    exact ⟨fun x y => norm_finiteGreen_localEntry_le_of_avoid P Λ v k hN hX4 hRadm hav' ε hε x y,
      fun x y hxy => norm_finiteGreen_longRange_le_of_avoid P Λ v k
        (by
          have h := hτ
          have h0 : 0 ≤ Real.log (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
              normBound P.K₀ k ^ 2 * Real.exp (Real.sqrt (scaleD P.K₀ k) +
              m * (2 * scaleD P.K₀ k + 2 + 2 * scaleD P.K₀ k / 5))) :=
            Real.log_nonneg (by
              have : 0 ≤ 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
                Real.exp (Real.sqrt (scaleD P.K₀ k) +
                m * (2 * scaleD P.K₀ k + 2 + 2 * scaleD P.K₀ k / 5)) := by positivity
              linarith only [this])
          have hT : 0 < scaleD P.K₀ k ^ (9 / 8 : ℝ) := Real.rpow_pos_of_pos hdpos _
          by_contra hneg
          push Not at hneg
          nlinarith only [h, h0, hT, hneg]) hJ (by linarith only [hd]) hRadm hav' ε hε x y hxy⟩
  · have hRfin : (R : Set (Site ν)).Finite := R.finite_toSet
    obtain ⟨B, hCB, hBN, hBadm, hRBadm, hBdiam⟩ := exists_lowCut hK hG k hC hRadm
    have hBR : B ⊆ (R : Set (Site ν)) := fun b hb => by
      refine hCR ?_
      obtain ⟨c, hc, hcd⟩ := hBN hb
      exact ⟨c, hc, hcd.trans (by linarith only [hdpos])⟩
    have hBfin : B.Finite := hRfin.subset hBR
    set Bf : Finset (Site ν) := hBfin.toFinset with hBf
    have hBfc : (Bf : Set (Site ν)) = B := by simp [hBf]
    have hQadm : Admissible P.K₀ (restrictedClasses P Λ v) k ((R : Set (Site ν)) \ Bf) := by
      rw [← Finset.coe_sdiff] at *
      simpa [Finset.coe_sdiff, hBfc] using hRBadm
    have hQS : ∀ x ∈ (R \ Bf) ∩ Λ, x ∉ singularSetsIn P Λ v k := by
      intro x hx hxS
      obtain ⟨hx1, -⟩ := Finset.mem_inter.1 hx
      obtain ⟨hxR, hxB⟩ := Finset.mem_sdiff.1 hx1
      exact hxB (by
        rw [← Finset.mem_coe, hBfc]; exact hCB (hall x (Finset.mem_coe.2 hxR) hxS))
    have hBN' : (Bf : Set (Site ν)) ⊆ nbhd C (scaleD P.K₀ k / 3) := by rw [hBfc]; exact hBN
    have hBd' : DiamLE (siteDist ν) (Bf : Set (Site ν)) (2 * scaleD P.K₀ k) := by
      rw [hBfc]; exact hBdiam
    refine ⟨fun x y => norm_finiteGreen_localEntry_le P hK Λ v k hm hX hJ hN hC hBN' hCR hQadm hQS
      hsmall hloc ε hε x y, fun x y hxy => norm_finiteGreen_longRange_le P hK Λ v k hm hX hJ hN hC
      hBN' hCR hQadm hQS hBd' hd hsmall hτ ε hε x y hxy⟩

/-- A first-exit region around `p ∈ A ∩ Λ` inside a `(k+1)`-admissible parent `A`, with the local
estimates (4.1), (4.2), the crossing-edge distance and the ball-count bound. -/
private theorem region_data {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) {m τ : ℝ} (hm : 0 ≤ m)
    (hJ : JPred P Λ v k m) (hN : NPred P Λ v k (normBound P.K₀ k))
    (hd : 3 ^ 8 ≤ scaleD P.K₀ k)
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hloc : normBound P.K₀ k + (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      (2 * Real.exp (Real.sqrt (scaleD P.K₀ k))) ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)))
    (hτ : Real.log (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) +
        m * (2 * scaleD P.K₀ k + 2 + 2 * scaleD P.K₀ k / 5))) ≤
        τ * scaleD P.K₀ k ^ (9 / 8 : ℝ))
    {A : Finset (Site ν)}
    (hAadm : Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) (A : Set (Site ν)))
    (hAS : ∀ x ∈ A ∩ Λ, x ∉ singularSetsIn P Λ v (k + 1)) (ε : ℝ) (hε : ε ≠ 0)
    {p : Site ν} (hp : p ∈ A ∩ Λ) :
    ∃ R : Finset (Site ν), R ⊆ A ∧ p ∈ R ∧
      (∀ u ∈ R, ∀ u' ∈ A \ R, siteDist ν u u' = 1 → scaleD P.K₀ (k + 1) / 2 ≤ siteDist ν p u) ∧
      ((R ∩ Λ).card : ℝ) ≤ (8 * scaleD P.K₀ (k + 1)) ^ ν ∧
      (∀ x y : {x // x ∈ R ∩ Λ},
        ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k))) ∧
      (∀ x y : {x // x ∈ R ∩ Λ}, scaleD P.K₀ k ^ (9 / 8 : ℝ) ≤ siteDist ν x y →
        ‖finiteGreen ν (R ∩ Λ) v P.E ε hε x y‖ ≤ Real.exp (-(m - τ) * siteDist ν x y)) := by
  classical
  have hG := obstacleFamily_gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v
  obtain ⟨hpA, hpΛ⟩ := Finset.mem_inter.1 hp
  obtain ⟨R, hRfin, hRA, hpR, -, hRadm, hRdiam, -, hcross⟩ :=
    exists_firstExitRegion hK hG k A.finite_toSet hAadm (Finset.mem_coe.2 hpA)
  set Rf : Finset (Site ν) := hRfin.toFinset with hRf
  have hRfc : (Rf : Set (Site ν)) = R := by simp [hRf]
  have hRfA : Rf ⊆ A := fun x hx => by
    have : x ∈ R := by rw [← hRfc]; exact hx
    exact Finset.mem_coe.1 (hRA this)
  have hpRf : p ∈ Rf := by rw [← Finset.mem_coe, hRfc]; exact hpR
  obtain ⟨-, hD, hD10⟩ := scale_facts hd (scaleD_succ_eq P.K₀ k)
  have hdiam' : DiamLE (siteDist ν) (Rf : Set (Site ν)) (3 * scaleD P.K₀ (k + 1) / 2) := by
    rw [hRfc]; exact hRdiam
  have hadm' : Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) (Rf : Set (Site ν)) := by
    rw [hRfc]; exact hRadm
  have hRS : ∀ x ∈ Rf ∩ Λ, x ∉ singularSetsIn P Λ v (k + 1) := fun x hx =>
    hAS x (Finset.mem_inter.2 ⟨hRfA (Finset.mem_inter.1 hx).1, (Finset.mem_inter.1 hx).2⟩)
  obtain ⟨h41, h42⟩ := local_est P hK Λ v k hm hJ hN hd hsmall hloc hτ hadm' hdiam' hRS ε hε
  refine ⟨Rf, hRfA, hpRf, ?_, ?_, h41, h42⟩
  · intro u hu u' hu' huu
    have hu'' := Finset.mem_sdiff.1 hu'
    refine hcross u (by rw [← hRfc]; exact hu) u' ⟨Finset.mem_coe.2 hu''.1, ?_⟩ huu
    rw [← hRfc]; exact hu''.2
  · have hsub : Rf ∩ Λ ⊆ Λ.filter (fun x => siteDist ν p x ≤ 3 * scaleD P.K₀ (k + 1) / 2) := by
      intro x hx
      obtain ⟨hxR, hxΛ⟩ := Finset.mem_inter.1 hx
      exact Finset.mem_filter.2 ⟨hxΛ, hdiam' p (Finset.mem_coe.2 hpRf) x (Finset.mem_coe.2 hxR)⟩
    have hc := card_filter_siteDist_le Λ p (R := 3 * scaleD P.K₀ (k + 1) / 2)
      (by linarith only [hD10])
    calc ((Rf ∩ Λ).card : ℝ)
        ≤ ((Λ.filter fun x => siteDist ν p x ≤ 3 * scaleD P.K₀ (k + 1) / 2).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (5 * (3 * scaleD P.K₀ (k + 1) / 2)) ^ ν := hc
      _ ≤ (8 * scaleD P.K₀ (k + 1)) ^ ν :=
          pow_le_pow_left₀ (by linarith only [hD10]) (by linarith only [hD10]) ν

/-- Link multiplicity from the inside: `∑_{b ∈ Bf} ∑_{q ∈ Q} ‖a(b, q)‖ ≤ 2ν |Bf|`. -/
private theorem sum_cross_le' {ν : ℕ} (Q Bf : Finset (Site ν)) :
    ∑ b ∈ Bf, ∑ q ∈ Q, ‖hoppingKernel ν b q‖ ≤ 2 * ν * Bf.card := by
  have h := sum_cross_le Q Bf
  rw [Finset.sum_comm] at h
  simpa only [hoppingKernel_symm_real ν] using h

/-- `exp(-(m-τ) s) exp(μ (s + 1)) ≤ exp(-(m-τ-μ) D/2 + μ)` for `s ≥ D/2`, `0 ≤ μ ≤ m - τ`. -/
private theorem exp_cross_le {m τ μ s D : ℝ} (hμm : μ ≤ m - τ) (hs : D / 2 ≤ s) :
    Real.exp (-(m - τ) * s) * Real.exp (μ * (s + 1)) ≤
      Real.exp (-(m - τ - μ) * (D / 2) + μ) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith only [mul_nonneg (sub_nonneg.2 hμm) (sub_nonneg.2 hs)]


theorem jPred_succ {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (k : ℕ) {m τ μ m' : ℝ} (hJ : JPred P Λ v k m)
    (hN : NPred P Λ v k (normBound P.K₀ k)) (hτ0 : 0 ≤ τ) (hμ : 0 ≤ μ) (hμm : μ ≤ m - τ)
    (hd : 3 ^ 8 ≤ scaleD P.K₀ k)
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hloc : normBound P.K₀ k + (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      (2 * Real.exp (Real.sqrt (scaleD P.K₀ k))) ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)))
    (hτ : Real.log (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) +
        m * (2 * scaleD P.K₀ k + 2 + 2 * scaleD P.K₀ k / 5))) ≤
        τ * scaleD P.K₀ k ^ (9 / 8 : ℝ))
    (hθ : 2 * ν * (8 * scaleD P.K₀ (k + 1)) ^ ν *
      Real.exp (-(m - τ - μ) * (scaleD P.K₀ (k + 1) / 2) + μ) ≤ 1 / 2)
    (hfin : Real.log 2 + (m - τ) * scaleD P.K₀ k ^ (9 / 8 : ℝ) +
      4 * Real.sqrt (scaleD P.K₀ k) ≤ (μ - m') * (scaleD P.K₀ (k + 1) / 5)) :
    JPred P Λ v (k + 1) m' := by
  classical
  intro A hAadm hAS ε hε x y hxy
  have hm : 0 ≤ m := by linarith only [hτ0, hμ, hμm]
  obtain ⟨hT3, hTD, hD10⟩ := scale_facts hd (scaleD_succ_eq P.K₀ k)
  have hdpos := scaleD_pos P.K₀ k
  have hT0 : 0 ≤ scaleD P.K₀ k ^ (9 / 8 : ℝ) := by positivity
  have hex := fun p (hp : p ∈ A ∩ Λ) =>
    region_data P hK Λ v k hm hJ hN hd hsmall hloc hτ hAadm hAS ε hε hp
  choose! R hRA hpR hcr hcard h41 h42 using hex
  set K : ℝ := Real.exp ((m - τ) * scaleD P.K₀ k ^ (9 / 8 : ℝ) +
    4 * Real.sqrt (scaleD P.K₀ k)) with hKdef
  set Eθ : ℝ := Real.exp (-(m - τ - μ) * (scaleD P.K₀ (k + 1) / 2) + μ) with hEθ
  have hK1 : 1 ≤ K := Real.one_le_exp (by
    have := Real.sqrt_nonneg (scaleD P.K₀ k)
    nlinarith only [this, mul_nonneg (sub_nonneg.2 (hμ.trans hμm)) hT0])
  have hRgA : ∀ p ∈ A ∩ Λ, R p ∩ Λ ⊆ A ∩ Λ := fun p hp q hq =>
    Finset.mem_inter.2 ⟨hRA p hp (Finset.mem_inter.1 hq).1, (Finset.mem_inter.1 hq).2⟩
  have hRgp : ∀ p ∈ A ∩ Λ, p ∈ R p ∩ Λ := fun p hp =>
    Finset.mem_inter.2 ⟨hpR p hp, (Finset.mem_inter.1 hp).2⟩
  have hdirect : ∀ (p : Site ν) (hp : p ∈ A ∩ Λ) (hy' : y.1 ∈ R p ∩ Λ),
      ‖finiteGreen ν (R p ∩ Λ) v P.E ε hε ⟨p, hRgp p hp⟩ ⟨y.1, hy'⟩‖ ≤
        K * Real.exp (-μ * siteDist ν p y.1) := by
    intro p hp hy'
    have hKe : K * Real.exp (-μ * siteDist ν p y.1) = Real.exp ((m - τ) *
        scaleD P.K₀ k ^ (9 / 8 : ℝ) + 4 * Real.sqrt (scaleD P.K₀ k) + -μ * siteDist ν p y.1) :=
      (Real.exp_add _ _).symm
    rw [hKe]
    by_cases hs : scaleD P.K₀ k ^ (9 / 8 : ℝ) ≤ siteDist ν p y.1
    · refine (h42 p hp ⟨p, hRgp p hp⟩ ⟨y.1, hy'⟩ hs).trans (Real.exp_le_exp.2 ?_)
      have := Real.sqrt_nonneg (scaleD P.K₀ k)
      nlinarith only [this, mul_nonneg (sub_nonneg.2 hμm) (siteDist_nonneg ν p y.1),
        mul_nonneg (sub_nonneg.2 (hμ.trans hμm)) hT0]
    · push Not at hs
      refine (h41 p hp ⟨p, hRgp p hp⟩ ⟨y.1, hy'⟩).trans (Real.exp_le_exp.2 ?_)
      nlinarith only [mul_le_mul_of_nonneg_left hs.le hμ, mul_le_mul_of_nonneg_right hμm hT0]
  have hcross : ∀ (p : Site ν) (hp : p ∈ A ∩ Λ), ∑ u ∈ (R p ∩ Λ).attach,
      ∑ u' ∈ (A ∩ Λ) \ (R p ∩ Λ),
      ‖finiteGreen ν (R p ∩ Λ) v P.E ε hε ⟨p, hRgp p hp⟩ u‖ * ‖hoppingKernel ν u u'‖ *
        Real.exp (μ * siteDist ν p u') ≤
        2 * ν * (8 * scaleD P.K₀ (k + 1)) ^ ν * Eθ := by
    intro p hp
    have hterm : ∀ u ∈ (R p ∩ Λ).attach, ∀ u' ∈ (A ∩ Λ) \ (R p ∩ Λ),
        ‖finiteGreen ν (R p ∩ Λ) v P.E ε hε ⟨p, hRgp p hp⟩ u‖ * ‖hoppingKernel ν u u'‖ *
          Real.exp (μ * siteDist ν p u') ≤ Eθ * ‖hoppingKernel ν u.1 u'‖ := by
      intro u _ u' hu'
      by_cases h0 : hoppingKernel ν u.1 u' = 0
      · simp [h0]
      have h1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
      obtain ⟨hu'A, hu'R⟩ := Finset.mem_sdiff.1 hu'
      obtain ⟨hu'A1, hu'Λ⟩ := Finset.mem_inter.1 hu'A
      have hu'R' : u' ∉ R p := fun h => hu'R (Finset.mem_inter.2 ⟨h, hu'Λ⟩)
      have huR : u.1 ∈ R p := (Finset.mem_inter.1 u.2).1
      have hs := hcr p hp u.1 huR u' (Finset.mem_sdiff.2 ⟨hu'A1, hu'R'⟩) h1
      have hg := h42 p hp ⟨p, hRgp p hp⟩ u (by linarith only [hTD, hs])
      have htri := siteDist_triangle ν p u' u.1
      have hexp : Real.exp (μ * siteDist ν p u') ≤ Real.exp (μ * (siteDist ν p u.1 + 1)) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hμ)
        linarith only [h1, htri]
      calc _ ≤ Real.exp (-(m - τ) * siteDist ν p u.1) * ‖hoppingKernel ν u.1 u'‖ *
            Real.exp (μ * (siteDist ν p u.1 + 1)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hg (norm_nonneg _)) hexp (Real.exp_pos _).le
              (by positivity)
        _ = (Real.exp (-(m - τ) * siteDist ν p u.1) * Real.exp (μ * (siteDist ν p u.1 + 1))) *
            ‖hoppingKernel ν u.1 u'‖ := by ring
        _ ≤ Eθ * ‖hoppingKernel ν u.1 u'‖ :=
            mul_le_mul_of_nonneg_right (exp_cross_le hμm hs) (norm_nonneg _)
    calc _ ≤ ∑ u ∈ (R p ∩ Λ).attach, ∑ u' ∈ (A ∩ Λ) \ (R p ∩ Λ),
          Eθ * ‖hoppingKernel ν u.1 u'‖ :=
          Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun u' hu' => hterm u hu u' hu'
      _ = Eθ * ∑ u ∈ R p ∩ Λ, ∑ u' ∈ (A ∩ Λ) \ (R p ∩ Λ), ‖hoppingKernel ν u u'‖ := by
          rw [← Finset.sum_attach (R p ∩ Λ), Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]
      _ ≤ Eθ * (2 * ν * (R p ∩ Λ).card) :=
          mul_le_mul_of_nonneg_left (sum_cross_le' _ _) (Real.exp_pos _).le
      _ ≤ Eθ * (2 * ν * (8 * scaleD P.K₀ (k + 1)) ^ ν) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcard p hp) (by positivity))
            (Real.exp_pos _).le
      _ = _ := by ring
  have hmain := norm_finiteGreen_le_of_firstExit (A := A ∩ Λ) v P.E ε hε (fun p => R p ∩ Λ)
    hRgp hRgA hμ (Real.exp_pos _).le hθ y.1 y.2 hdirect hcross x.1 x.2
  have hDpos : 0 < scaleD P.K₀ (k + 1) := by linarith only [hD10]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hμm' : 0 < μ - m' := by
    by_contra hneg
    push Not at hneg
    have := Real.sqrt_nonneg (scaleD P.K₀ k)
    nlinarith only [hμ, hfin, hT0, hlog2, this, mul_nonneg (sub_nonneg.2 hμm) hT0,
      mul_nonneg (neg_nonneg.2 hneg) hDpos.le]
  have h2K : 2 * K = Real.exp (Real.log 2 + ((m - τ) * scaleD P.K₀ k ^ (9 / 8 : ℝ) +
      4 * Real.sqrt (scaleD P.K₀ k))) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  calc ‖finiteGreen ν (A ∩ Λ) v P.E ε hε x y‖
      ≤ 2 * K * Real.exp (-μ * siteDist ν x.1 y.1) := hmain
    _ = Real.exp (Real.log 2 + ((m - τ) * scaleD P.K₀ k ^ (9 / 8 : ℝ) +
        4 * Real.sqrt (scaleD P.K₀ k)) + -μ * siteDist ν x.1 y.1) := by
        rw [h2K, ← Real.exp_add]
    _ ≤ Real.exp (-m' * siteDist ν x.1 y.1) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith only [hfin, mul_le_mul_of_nonneg_left hxy hμm'.le]


theorem nPred_succ {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (k : ℕ) {m τ m' : ℝ} (hJ : JPred P Λ v k m)
    (hN : NPred P Λ v k (normBound P.K₀ k)) (hτ0 : 0 ≤ τ) (hmτ : τ ≤ m)
    (hd : 3 ^ 8 ≤ scaleD P.K₀ k)
    (hsmall : (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) - m * scaleD P.K₀ k) ≤ 1 / 2)
    (hloc : normBound P.K₀ k + (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      (2 * Real.exp (Real.sqrt (scaleD P.K₀ k))) ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)))
    (hτ : Real.log (1 + 2 * (2 * ν * (25 * scaleD P.K₀ k) ^ ν) ^ 2 * normBound P.K₀ k ^ 2 *
      Real.exp (Real.sqrt (scaleD P.K₀ k) +
        m * (2 * scaleD P.K₀ k + 2 + 2 * scaleD P.K₀ k / 5))) ≤
        τ * scaleD P.K₀ k ^ (9 / 8 : ℝ))
    (hcrossN : 2 * ν * (8 * scaleD P.K₀ (k + 1)) ^ ν *
      Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) ≤ 1)
    (hm' : 0 ≤ m') (hJ' : JPred P Λ v (k + 1) m') :
    NPred P Λ v (k + 1) (normBound P.K₀ (k + 1)) := by
  classical
  intro A hAadm hAS ε hε x y
  have hm : 0 ≤ m := by linarith only [hτ0, hmτ]
  obtain ⟨hT3, hTD, hD10⟩ := scale_facts hd (scaleD_succ_eq P.K₀ k)
  have hdpos := scaleD_pos P.K₀ k
  have hT0 : 0 ≤ scaleD P.K₀ k ^ (9 / 8 : ℝ) := by positivity
  have hsq : 1 ≤ Real.sqrt (scaleD P.K₀ k) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith only [hd])
  have ht2 : 2 ≤ Real.exp (4 * Real.sqrt (scaleD P.K₀ k)) := by
    have := Real.add_one_le_exp (4 * Real.sqrt (scaleD P.K₀ k)); linarith only [hsq, this]
  have he8 : Real.exp (4 * Real.sqrt (scaleD P.K₀ k)) + 1 ≤
      Real.exp (8 * Real.sqrt (scaleD P.K₀ k)) := by
    have : Real.exp (8 * Real.sqrt (scaleD P.K₀ k)) =
        Real.exp (4 * Real.sqrt (scaleD P.K₀ k)) * Real.exp (4 * Real.sqrt (scaleD P.K₀ k)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; nlinarith only [ht2]
  rw [normBound_succ]
  by_cases hs : scaleD P.K₀ (k + 1) / 5 ≤ siteDist ν x.1 y.1
  · refine (hJ' A hAadm hAS ε hε x y hs).trans ?_
    have h1 : Real.exp (-m' * siteDist ν x.1 y.1) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith only [hm', siteDist_nonneg ν x.1 y.1])
    linarith only [ht2, he8, h1]
  push Not at hs
  obtain ⟨R, hRA, hxR, hcr, hcard, h41, h42⟩ :=
    region_data P hK Λ v k hm hJ hN hd hsmall hloc hτ hAadm hAS ε hε x.2
  have hxRg : x.1 ∈ R ∩ Λ := Finset.mem_inter.2 ⟨hxR, (Finset.mem_inter.1 x.2).2⟩
  have hBA : R ∩ Λ ⊆ A ∩ Λ := fun q hq =>
    Finset.mem_inter.2 ⟨hRA (Finset.mem_inter.1 hq).1, (Finset.mem_inter.1 hq).2⟩
  set S : ℂ := ∑ q ∈ R ∩ Λ, ∑ b ∈ (A ∩ Λ) \ (R ∩ Λ), greenEntry v P.E ε (R ∩ Λ) x.1 q *
    hoppingKernel ν q b * greenEntry v P.E ε (A ∩ Λ) b y.1 with hS
  have hSb : ‖S‖ ≤ 1 := by
    have hterm : ∀ q ∈ R ∩ Λ, ∀ b ∈ (A ∩ Λ) \ (R ∩ Λ),
        ‖greenEntry v P.E ε (R ∩ Λ) x.1 q * hoppingKernel ν q b *
          greenEntry v P.E ε (A ∩ Λ) b y.1‖ ≤
        Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) * ‖hoppingKernel ν q b‖ := by
      intro q hq b hb
      by_cases h0 : hoppingKernel ν q b = 0
      · simp [h0]
      have h1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
      obtain ⟨hbA, hbR⟩ := Finset.mem_sdiff.1 hb
      obtain ⟨hbA1, hbΛ⟩ := Finset.mem_inter.1 hbA
      have hbR' : b ∉ R := fun h => hbR (Finset.mem_inter.2 ⟨h, hbΛ⟩)
      have hqR : q ∈ R := (Finset.mem_inter.1 hq).1
      have hs2 := hcr q hqR b (Finset.mem_sdiff.2 ⟨hbA1, hbR'⟩) h1
      have hxq : ‖greenEntry v P.E ε (R ∩ Λ) x.1 q‖ ≤
          Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) := by
        have hT : scaleD P.K₀ k ^ (9 / 8 : ℝ) ≤ siteDist ν x.1 q := by linarith only [hTD, hs2]
        have h := h42 ⟨x.1, hxRg⟩ ⟨q, hq⟩ hT
        rw [greenEntry_eq] at h
        refine h.trans (Real.exp_le_exp.2 ?_)
        nlinarith only [mul_nonneg (sub_nonneg.2 hmτ) (sub_nonneg.2 hs2)]
      have hby : scaleD P.K₀ (k + 1) / 5 ≤ siteDist ν b y.1 := by
        have t1 := siteDist_triangle ν x.1 q b
        have t2 := siteDist_triangle ν x.1 b y.1
        have t3 := siteDist_comm ν b q
        have t4 := siteDist_comm ν y.1 b
        linarith only [hD10, hs, h1, hs2, t1, t2, t3, t4]
      have hby1 : ‖greenEntry v P.E ε (A ∩ Λ) b y.1‖ ≤ 1 := by
        have h := hJ' A hAadm hAS ε hε ⟨b, hbA⟩ y hby
        rw [greenEntry_eq] at h
        refine h.trans (Real.exp_le_one_iff.2 ?_)
        nlinarith only [hm', siteDist_nonneg ν b y.1]
      rw [norm_mul, norm_mul]
      calc ‖greenEntry v P.E ε (R ∩ Λ) x.1 q‖ * ‖hoppingKernel ν q b‖ *
            ‖greenEntry v P.E ε (A ∩ Λ) b y.1‖
          ≤ Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) * ‖hoppingKernel ν q b‖ * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hxq (norm_nonneg _)) hby1 (norm_nonneg _)
              (by positivity)
        _ = _ := mul_one _
    calc ‖S‖ ≤ ∑ q ∈ R ∩ Λ, ∑ b ∈ (A ∩ Λ) \ (R ∩ Λ),
          ‖greenEntry v P.E ε (R ∩ Λ) x.1 q * hoppingKernel ν q b *
            greenEntry v P.E ε (A ∩ Λ) b y.1‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => norm_sum_le _ _)
      _ ≤ ∑ q ∈ R ∩ Λ, ∑ b ∈ (A ∩ Λ) \ (R ∩ Λ),
          Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) * ‖hoppingKernel ν q b‖ :=
          Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun b hb => hterm q hq b hb
      _ = Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) *
          ∑ q ∈ R ∩ Λ, ∑ b ∈ (A ∩ Λ) \ (R ∩ Λ), ‖hoppingKernel ν q b‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) * (2 * ν * (R ∩ Λ).card) :=
          mul_le_mul_of_nonneg_left (sum_cross_le' _ _) (Real.exp_pos _).le
      _ ≤ Real.exp (-(m - τ) * (scaleD P.K₀ (k + 1) / 2)) *
          (2 * ν * (8 * scaleD P.K₀ (k + 1)) ^ ν) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard (by positivity))
            (Real.exp_pos _).le
      _ ≤ 1 := by linarith only [hcrossN]
  rw [greenEntry_eq (A ∩ Λ) v P.E ε hε x y]
  by_cases hyR : y.1 ∈ R ∩ Λ
  · have hid := greenEntry_sub_sum v P.E ε hε hBA hxRg hyR
    have hG := h41 ⟨x.1, hxRg⟩ ⟨y.1, hyR⟩
    rw [greenEntry_eq] at hG
    have : ‖greenEntry v P.E ε (A ∩ Λ) x.1 y.1‖ ≤
        ‖greenEntry v P.E ε (R ∩ Λ) x.1 y.1‖ + ‖S‖ := by
      rw [hid]; exact norm_sub_le _ _
    linarith only [he8, hSb, hG, this]
  · have hid := greenEntry_neg_sum v P.E ε hε hBA hxRg y.2 hyR
    have : ‖greenEntry v P.E ε (A ∩ Λ) x.1 y.1‖ = ‖S‖ := by
      rw [hid, norm_neg]
    linarith only [he8, hSb, this, Real.exp_pos (4 * Real.sqrt (scaleD P.K₀ k))]

end FroehlichSpencer.T12

end
