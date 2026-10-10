/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Assembly.Constants
public import FroehlichSpencer.T12.Assembly.SmallDistance
public import FroehlichSpencer.T12.Assembly.LargeDistance
public import FroehlichSpencer.T12.TowerProb
public import FroehlichSpencer.Surface.LatticeLength

/-!
# The finite-volume Green probability estimate

Assemble the multiscale tower estimates into the finite-volume bound (1.30). The disorder threshold is uniform over the single-site law; the Gaussian energy threshold depends on its variance. The probability constants depend on the prescribed exponent and the fixed dimension.
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.T12.Assembly

open Multiscale


theorem measure_greenEvent_compl_le {ν : ℕ} {L₁ : ℝ}
    (hL₁ : ∀ (P : Params),
      ScaleConditions P.K₀ → ∀ (Λ : Finset (Site ν)) (v : Configuration ν) (L M : ℝ), L₁ ≤ L →
      scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) → 0 ≤ M → v ∈ towerEvent P Λ 0 L →
      (∀ k : ℕ, JPred P Λ v (k + 1) M) →
      (∀ j : ℕ, 4 * ν * (5 * (4 ^ j * L)) ^ ν * Real.exp (-M * (4 ^ j * L / 8 - 1)) ≤ 1) →
      ∀ (ε : ℝ) (hε : ε ≠ 0) (s t : Site ν) (hs : s ∈ Λ) (ht : t ∈ Λ),
        siteDist ν 0 s ≤ L / 4 + 1 → siteDist ν 0 t ≤ L / 4 → 3 * L / 16 ≤ siteDist ν s t →
        ‖finiteGreen ν Λ v P.E ε hε ⟨s, hs⟩ ⟨t, ht⟩‖ ≤ 2 * Real.exp (-M * siteDist ν s t / 2))
    (P : Params) (hK : ScaleConditions P.K₀) {Nstar : ℝ} (hNstar : 1 ≤ Nstar)
    (hNL : ∀ L : ℝ, 2 * Nstar ≤ L → L₁ ≤ L ∧ 16 ≤ L ∧ scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ))
    {m M p : ℝ} (hm : 0 < m) (hp : 0 < p) (hM4 : 4 * m ≤ M)
    (hMN : 8 * Real.log 2 ≤ M * Nstar)
    (hpath : ∀ l : ℝ, 16 ≤ l → 4 * ν * (5 * l) ^ ν * Real.exp (-M * (l / 8 - 1)) ≤ 1)
    (hloc : ∀ N : ℝ, 1 ≤ N →
      1 + 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) ≤ Real.exp (m * N / 4))
    (hJ : ∀ (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ), JPred P Λ v (k + 1) M)
    (μ : Measure (Configuration ν)) {C : ℝ} (hC : 0 ≤ C)
    (htow : ∀ (Λ : Finset (Site ν)) (L : ℝ), 2 * Nstar ≤ L →
      μ (towerEvent P Λ 0 L)ᶜ ≤ ENNReal.ofReal (C * L ^ (-p)))
    (Λ : Finset (Site ν))
    (hres : ∀ N : ℝ, Nstar < N →
      μ (resonanceEvent ν (Λ.filter fun z => siteDist ν 0 z ≤ 2 * N) P.E
        (Real.exp (-(m * N / 4)))) ≤ ENNReal.ofReal (N ^ (-p)))
    {x : Site ν} (h0 : (0 : Site ν) ∈ Λ) (hx : x ∈ Λ) {N : ℝ} (hN : Nstar < N) :
    μ {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
        ‖finiteGreen ν Λ v P.E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤
          Real.exp (m * (N - latticeLength ν x))}ᶜ ≤ ENNReal.ofReal ((C + 1) * N ^ (-p)) := by
  have hN1 : 1 ≤ N := by linarith only [hNstar, hN]
  have hN0 : 0 < N := by linarith only [hN1]
  have hM0 : 0 ≤ M := by linarith only [hm, hM4]
  have hMN' : 8 * Real.log 2 ≤ M * N :=
    hMN.trans (mul_le_mul_of_nonneg_left hN.le hM0)
  have hNp : 0 ≤ N ^ (-p) := Real.rpow_nonneg hN0.le _
  have hfinal : ENNReal.ofReal (C * N ^ (-p)) ≤ ENNReal.ofReal ((C + 1) * N ^ (-p)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith only []) hNp)
  -- tower bound at `L ≥ N` turned into `C N^{-p}`
  have htowN : ∀ L : ℝ, 2 * Nstar ≤ L → N ≤ L →
      μ (towerEvent P Λ 0 L)ᶜ ≤ ENNReal.ofReal (C * N ^ (-p)) := by
    intro L hL hNL'
    refine (htow Λ L hL).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hN0 hNL' (by linarith only [hp])) hC
  have hcount : ∀ L : ℝ, 2 * Nstar ≤ L → ∀ j : ℕ,
      4 * ν * (5 * (4 ^ j * L)) ^ ν * Real.exp (-M * (4 ^ j * L / 8 - 1)) ≤ 1 := by
    intro L hL j
    refine hpath _ ?_
    have h16 := (hNL L hL).2.1
    have : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
    nlinarith only [h16, this]
  rw [← siteDist_zero_left]
  by_cases hlarge : N / 2 ≤ siteDist ν 0 x
  ·
    set L : ℝ := 4 * siteDist ν 0 x with hLdef
    have hL2 : 2 * Nstar ≤ L := by linarith only [hN, hlarge]
    obtain ⟨hL₁L, -, hLd⟩ := hNL L hL2
    refine le_trans (measure_mono ?_) ((htowN L hL2 (by linarith only [hN0, hlarge])).trans hfinal)
    intro v hv hv'
    apply hv
    intro ε hε
    have h := hL₁ P hK Λ v L M hL₁L hLd hM0 hv' (hJ Λ v) (hcount L hL2) ε hε 0 x h0 hx
      (by rw [siteDist_self]; linarith only [siteDist_nonneg ν 0 x])
      (by rw [hLdef]; linarith only [])
      (by rw [hLdef]; linarith only [siteDist_nonneg ν 0 x])
    exact h.trans (two_mul_exp_le_exp_of_large hm.le hM4 hMN' hN0.le hlarge)
  ·
    push Not at hlarge
    have hL2 : 2 * Nstar ≤ 8 * N := by linarith only [hN, hN0]
    obtain ⟨hL₁L, -, hLd⟩ := hNL (8 * N) hL2
    set F : Finset (Site ν) := Λ.filter fun z => siteDist ν 0 z ≤ 2 * N with hF
    have hsub : {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
        ‖finiteGreen ν Λ v P.E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤
          Real.exp (m * (N - siteDist ν 0 x))}ᶜ ⊆
        resonanceEvent ν F P.E (Real.exp (-(m * N / 4))) ∪ (towerEvent P Λ 0 (8 * N))ᶜ := by
      intro v hv
      by_contra hcon
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
      apply hv
      intro ε hε
      refine norm_finiteGreen_le_small Λ v P.E hm.le hM0 hN1 hcon.1 h0 hx hlarge ?_
        (hloc N hN1) ε hε
      intro ε' hε' u hu hu1 hu2
      refine hL₁ P hK Λ v (8 * N) M hL₁L hLd hM0 hcon.2 (hJ Λ v) (hcount _ hL2) ε' hε' u x hu hx
        (by linarith only [hu2]) (by linarith only [hN0, hlarge]) ?_
      have h1 := siteDist_triangle ν 0 u x
      have h2 := siteDist_comm ν x u
      linarith only [hlarge, hu1, h1, h2]
    calc _ ≤ μ (resonanceEvent ν F P.E (Real.exp (-(m * N / 4))) ∪
          (towerEvent P Λ 0 (8 * N))ᶜ) := measure_mono hsub
      _ ≤ μ (resonanceEvent ν F P.E (Real.exp (-(m * N / 4)))) +
          μ (towerEvent P Λ 0 (8 * N))ᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (N ^ (-p)) + ENNReal.ofReal (C * N ^ (-p)) :=
          add_le_add (hres N hN) (htowN _ hL2 (by linarith only [hN0]))
      _ = ENNReal.ofReal ((C + 1) * N ^ (-p)) := by
          rw [← ENNReal.ofReal_add hNp (mul_nonneg hC hNp)]
          congr 1; ring


theorem ofReal_one_sub_le_of_failure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S) {p N Nstar C K : ℝ}
    (hp : 0 < p) (hN : 0 < N) (hNstar : 0 ≤ Nstar) (hKs : Nstar ^ p ≤ K) (hKC : C + 1 ≤ K)
    (hfail : Nstar < N → μ Sᶜ ≤ ENNReal.ofReal ((C + 1) * N ^ (-p))) :
    ENNReal.ofReal (1 - K / Real.rpow N p) ≤ μ S := by
  by_cases hNs : N ≤ Nstar
  · rw [ofReal_one_sub_div_rpow_eq_zero hp hN hNs hKs]
    exact bot_le
  · push Not at hNs
    have hNp : 0 < Real.rpow N p := Real.rpow_pos_of_pos hN p
    have hK0 : 0 ≤ K := (Real.rpow_nonneg hNstar p).trans hKs
    refine ofReal_one_sub_le_of_measure_compl_le μ hS (div_nonneg hK0 hNp.le) ?_
    refine (hfail hNs).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_neg hN.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hKC hNp.le

private theorem measure_le_ofReal_mul_of_card_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : Set Ω} {a b : ℝ} (ha : 0 ≤ a) {n : ℕ} (h : μ s ≤ ENNReal.ofReal a * n)
    (hn : (n : ℝ) ≤ b) : μ s ≤ ENNReal.ofReal (a * b) := by
  refine h.trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul ha]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn ha)

private theorem card_ball_le (ν : ℕ) (Λ : Finset (Site ν)) {N : ℝ} (hN : 1 ≤ N) :
    ((Λ.filter fun z => siteDist ν 0 z ≤ 2 * N).card : ℝ) ≤ (10 * N) ^ ν := by
  have := T12.card_filter_siteDist_le Λ 0 (R := 2 * N) (by linarith only [hN])
  rwa [show 5 * (2 * N) = 10 * N by ring] at this


theorem probability_bound_of_T21 (ν : ℕ) (hν : 0 < ν)
    (hT21 : ∃ K₀ : ℝ, ScaleConditions K₀ ∧ ∀ M : ℝ, ∃ N₀ : ℝ, ∀ P : Params, P.K₀ = K₀ →
      N₀ ≤ P.Nthr → ∀ (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ), JPred P Λ v (k + 1) M) :
    ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ) (Λ : Finset (Site ν)) (x : Site ν),
          (h0 : (0 : Site ν) ∈ Λ) → (hx : x ∈ Λ) →
        ∀ (N : ℝ), 0 < N →
          let S : Set (Configuration ν) :=
            {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
              ‖finiteGreen ν Λ v E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤
                Real.exp (m * (N - latticeLength ν x))}
          ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
              MeasurableSet S ∧
                ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤ configurationMeasure ν law S) ∧
            (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
              highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
              MeasurableSet S ∧
                ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                  configurationMeasure ν law S) := by
  obtain ⟨K₀, hK, hT⟩ := hT21
  have hK0 : 0 < K₀ := by
    have h := hK.1
    unfold scaleD at h
    by_contra hn
    push Not at hn
    have : Real.exp (K₀ * (5 / 4 : ℝ) ^ 0) ≤ 1 := by
      rw [Real.exp_le_one_iff]; simpa using hn
    linarith only [h, this]
  obtain ⟨L₁, hL₁⟩ := exists_norm_finiteGreen_le_of_towerEvent ν
  obtain ⟨Mpath, -, hMpath⟩ := exists_rate_path ν
  choose N₀ hN₀ using hT

  set Nstar : ℝ := max (max 16 (L₁ / 2)) ((scaleD K₀ 1 / 5) ^ (4 / 3 : ℝ)) with hNstar
  have hNstar16 : 16 ≤ Nstar := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNstar1 : 1 ≤ Nstar := by linarith only [hNstar16]
  have hNL : ∀ L : ℝ, 2 * Nstar ≤ L →
      L₁ ≤ L ∧ 16 ≤ L ∧ scaleD K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) := by
    intro L hL
    have h1 : L₁ / 2 ≤ Nstar := le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 : (scaleD K₀ 1 / 5) ^ (4 / 3 : ℝ) ≤ Nstar := le_max_right _ _
    refine ⟨by linarith only [hL, h1], by linarith only [hNstar16, hL], ?_⟩
    have hd : 0 ≤ scaleD K₀ 1 / 5 := by have := scaleD_pos K₀ 1; positivity
    have he : scaleD K₀ 1 / 5 = ((scaleD K₀ 1 / 5) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_mul hd]; norm_num
    rw [he]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hd _) (by linarith only [hNstar1, hL, h2])
      (by norm_num)

  have hlocE : ∀ m : ℝ, ∃ Mloc : ℝ, 0 < m → ∀ M : ℝ, Mloc ≤ M → ∀ N : ℝ, 1 ≤ N →
      1 + 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) ≤ Real.exp (m * N / 4) := by
    intro m
    by_cases hm : 0 < m
    · obtain ⟨Mloc, -, h⟩ := exists_rate_local ν hm
      exact ⟨Mloc, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose Mloc hMloc using hlocE
  set Mreq : ℝ → ℝ := fun m =>
    max (max (4 * m) (8 * Real.log 2 / Nstar)) (max Mpath (Mloc m)) with hMreq
  have hMreq4 : ∀ m, 4 * m ≤ Mreq m := fun m => le_trans (le_max_left _ _) (le_max_left _ _)
  have hMreqN : ∀ m, 8 * Real.log 2 ≤ Mreq m * Nstar := fun m => by
    have h : 8 * Real.log 2 / Nstar ≤ Mreq m :=
      (le_max_right (4 * m) (8 * Real.log 2 / Nstar)).trans (le_max_left _ _)
    rw [div_le_iff₀ (by linarith only [hNstar1])] at h
    exact h
  have hMreqP : ∀ m, Mpath ≤ Mreq m := fun m => le_trans (le_max_left _ _) (le_max_right _ _)
  have hMreqL : ∀ m, Mloc m ≤ Mreq m := fun m => le_trans (le_max_right _ _) (le_max_right _ _)

  have hfinE : ∀ p m : ℝ, ∃ Mf : ℝ, 0 < m →
      0 < Mf ∧ ∀ t : ℝ, 1 ≤ t → t ^ (p + ν) * Real.exp (-(m * t / 8)) ≤ Mf := by
    intro p m
    by_cases hm : 0 < m
    · obtain ⟨Mf, h1, h2⟩ := exists_rpow_mul_exp_le (p + ν) hm
      exact ⟨Mf, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hm⟩
  choose Mfin hMfin using hfinE

  have htBD : ∀ p : ℝ, ∃ δ₀ C : ℝ, 0 < p → ∀ (law : Measure ℝ) [IsProbabilityMeasure law]
      (δ : ℝ), HasBoundedDensity law δ → δ₀ ≤ δ → ∀ (P : Params), P.K₀ = K₀ →
      P.Nthr = Real.sqrt δ → ∀ (Λ : Finset (Site ν)) (a : Site ν) (L : ℝ), 1 ≤ L →
      scaleD K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) →
        configurationMeasure ν law (towerEvent P Λ a L)ᶜ ≤ ENNReal.ofReal (C * L ^ (-p)) := by
    intro p
    by_cases hp : 0 < p
    · obtain ⟨δ₀, C, h⟩ := exists_towerEvent_compl_le_boundedDensity ν hK0 hp
      exact ⟨δ₀, C, fun _ law _ δ hl hδ P hP hN Λ a L hL h1 =>
        (h law δ hl hδ P hP hN Λ a a L hL h1).2.1⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose δ₀ Cbd hCbd using htBD
  have htG : ∀ γ p : ℝ, ∃ E₀ C : ℝ, ∀ (hγ : 0 < γ), 0 < p → ∀ (P : Params), P.K₀ = K₀ →
      E₀ ≤ |P.E - 2 * ν| → P.Nthr = |P.E| / 2 → ∀ (Λ : Finset (Site ν)) (a : Site ν) (L : ℝ),
      1 ≤ L → scaleD K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) →
        configurationMeasure ν (gaussianLaw γ hγ) (towerEvent P Λ a L)ᶜ ≤
          ENNReal.ofReal (C * L ^ (-p)) := by
    intro γ p
    by_cases h : 0 < γ ∧ 0 < p
    · obtain ⟨E₀, C, hc⟩ := exists_towerEvent_compl_le_gaussian ν hK0 h.1 h.2
      exact ⟨E₀, C, fun _ _ P hP hE hN Λ a L hL h1 => (hc P hP hE hN Λ a a L hL h1).2.1⟩
    · exact ⟨0, 0, fun hγ hp => absurd ⟨hγ, hp⟩ h⟩
  choose E₀ Cg hCg using htG

  have hcE : ∀ γ η : ℝ, ∃ E₁ : ℝ, ∀ (hγ : 0 < γ), 0 < η → ∀ E : ℝ, E₁ ≤ |E - 2 * ν| →
      Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
        (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) ≤ η := by
    intro γ η
    by_cases h : 0 < γ ∧ 0 < η
    · obtain ⟨E₁, hE⟩ := exists_gaussian_coeff_le ν h.1 h.2
      exact ⟨E₁, fun _ _ => hE⟩
    · exact ⟨0, fun hγ hη => absurd ⟨hγ, hη⟩ h⟩
  choose E₁ hE₁ using hcE
  -- the uniform constants
  set B : ℝ → ℝ → ℝ := fun p m => Real.sqrt 2 * 10 ^ ν * Mfin p m with hB
  have hBpos : ∀ p m, 0 < m → 0 < B p m := fun p m hm => by
    have := (hMfin p m hm).1
    simp only [hB]
    positivity
  set Dbd : ℝ → ℝ → ℝ := fun p m =>
    max (max 1 (δ₀ p)) (max (max (N₀ (Mreq m)) 0 ^ 2) (B p m ^ 2)) with hDbd
  have hDbd1 : ∀ p m, 1 ≤ Dbd p m := fun p m => le_trans (le_max_left _ _) (le_max_left _ _)
  refine ⟨fun p m => 1 / Dbd p m,
    fun γ p m => max (max 1 (E₀ γ p))
      (max (2 * max (N₀ (Mreq m)) 0 + 2 * ν) (E₁ γ (1 / B p m))),
    fun p => max (Nstar ^ p) (max (Cbd p) 0 + 1),
    fun γ p m => max (Nstar ^ p) (max (Cg γ p) 0 + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro p m _ _
    have := hDbd1 p m
    positivity
  · intro γ p m _ _ _
    exact lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro p _
    exact le_trans (Real.rpow_nonneg (by linarith only [hNstar1]) p) (le_max_left _ _)
  · intro γ p m _ _ _
    exact le_trans (Real.rpow_nonneg (by linarith only [hNstar1]) p) (le_max_left _ _)
  intro m p hm hp law _ E Λ x h0 hx N hN S
  have hμ : IsProbabilityMeasure (configurationMeasure ν law) := by
    unfold configurationMeasure; infer_instance
  have hS : MeasurableSet S :=
    measurableSet_forall_norm_finiteGreen_le ν Λ E _ ⟨0, h0⟩ ⟨x, hx⟩
  have hBm := hBpos p m hm
  have hfin := (hMfin p m hm).2
  refine ⟨fun hBD => ⟨hS, ?_⟩, fun γ hγ hlaw hE => ⟨hS, ?_⟩⟩
  · -- bounded-density regime
    obtain ⟨δ, hδ, hδle⟩ := hBD
    have hδ0 : 0 < δ := hδ.1
    have hDδ : Dbd p m ≤ δ := by
      have h1 := hDbd1 p m
      have hδle : δ⁻¹ ≤ 1 / Dbd p m := hδle
      rw [one_div] at hδle
      exact (inv_le_inv₀ hδ0 (by linarith only [h1])).1 hδle
    have hδ₀ : δ₀ p ≤ δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDδ
    have hδN : max (N₀ (Mreq m)) 0 ^ 2 ≤ δ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hDδ
    have hδB : B p m ^ 2 ≤ δ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hDδ
    set P : Params := ⟨E, Real.sqrt δ, K₀⟩ with hP
    have hPN : N₀ (Mreq m) ≤ P.Nthr := by
      have h1 : max (N₀ (Mreq m)) 0 ≤ Real.sqrt δ := by
        rw [← Real.sqrt_sq (le_max_right (N₀ (Mreq m)) 0)]
        exact Real.sqrt_le_sqrt hδN
      exact le_trans (le_max_left _ _) h1
    have hc0 : 0 ≤ Real.sqrt δ⁻¹ := Real.sqrt_nonneg _
    have hcM : Real.sqrt 2 * 10 ^ ν * Real.sqrt δ⁻¹ * Mfin p m ≤ 1 := by
      have hsq : B p m ≤ Real.sqrt δ := by
        rw [← Real.sqrt_sq hBm.le]; exact Real.sqrt_le_sqrt hδB
      have hinv : Real.sqrt δ⁻¹ = (Real.sqrt δ)⁻¹ := Real.sqrt_inv δ
      have e : Real.sqrt 2 * 10 ^ ν * Real.sqrt δ⁻¹ * Mfin p m = B p m * (Real.sqrt δ)⁻¹ := by
        rw [hinv, hB]; ring
      rw [e, ← div_eq_mul_inv, div_le_one (by have := Real.sqrt_pos.2 hδ0; linarith only [this])]
      exact hsq
    refine ofReal_one_sub_le_of_failure _ hS hp hN (by linarith only [hNstar1]) (le_max_left _ _)
      (le_max_right _ _) ?_
    intro hNs
    refine measure_greenEvent_compl_le hL₁ P hK hNstar1 hNL hm hp (hMreq4 m) (hMreqN m)
      (fun l hl => hMpath _ (hMreqP m) l hl) (hMloc m hm _ (hMreqL m))
      (hN₀ (Mreq m) P rfl hPN) _ (le_max_right _ _) ?_ Λ ?_ h0 hx hNs
    · intro Λ' L hL
      have h := hNL L hL
      refine (hCbd p hp law δ hδ hδ₀ P rfl rfl Λ' 0 L (by linarith only [h.2.1]) h.2.2).trans ?_
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith only [h.2.1]) _))
    · intro N' hN'
      have hN'1 : 1 ≤ N' := by linarith only [hNstar1, hN']
      have h := (resonance_bound_boundedDensity ν (Λ.filter fun z => siteDist ν 0 z ≤ 2 * N')
        law hδ E (Real.exp (-(m * N' / 4)))).2
      refine (measure_le_ofReal_mul_of_card_le (by positivity) h (card_ball_le ν Λ hN'1)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      exact resonance_absorb ν hc0 hfin hcM hN'1
  · -- Gaussian regime
    subst hlaw
    have hE₀ : E₀ γ p ≤ |E - 2 * ν| :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE
    have hEN : 2 * max (N₀ (Mreq m)) 0 + 2 * ν ≤ |E - 2 * ν| :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hE
    have hEthr : E₁ γ (1 / B p m) ≤ |E - 2 * ν| :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hE
    set P : Params := ⟨E, |E| / 2, K₀⟩ with hP
    have hPN : N₀ (Mreq m) ≤ P.Nthr := by
      have h1 : |E - 2 * ν| ≤ |E| + 2 * ν := by
        have := abs_sub (E) (2 * (ν : ℝ))
        have h2 : |2 * (ν : ℝ)| = 2 * ν := abs_of_nonneg (by positivity)
        linarith only [this, h2]
      have h3 := le_max_left (N₀ (Mreq m)) 0
      show N₀ (Mreq m) ≤ |E| / 2
      linarith only [hEN, h1, h3]
    have hc := hE₁ γ (1 / B p m) hγ (by positivity) E hEthr
    have hc0 : 0 ≤ Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
        (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) := Real.sqrt_nonneg _
    have hcM : Real.sqrt 2 * 10 ^ ν * Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
        (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) * Mfin p m ≤ 1 := by
      have e : Real.sqrt 2 * 10 ^ ν * Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
          (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) * Mfin p m =
          B p m * Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
          (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) := by
        rw [hB]; ring
      rw [e]
      calc _ ≤ B p m * (1 / B p m) := mul_le_mul_of_nonneg_left hc hBm.le
        _ = 1 := by field_simp
    refine ofReal_one_sub_le_of_failure _ hS hp hN (by linarith only [hNstar1]) (le_max_left _ _)
      (le_max_right _ _) ?_
    intro hNs
    refine measure_greenEvent_compl_le hL₁ P hK hNstar1 hNL hm hp (hMreq4 m) (hMreqN m)
      (fun l hl => hMpath _ (hMreqP m) l hl) (hMloc m hm _ (hMreqL m))
      (hN₀ (Mreq m) P rfl hPN) _ (le_max_right _ _) ?_ Λ ?_ h0 hx hNs
    · intro Λ' L hL
      have h := hNL L hL
      refine (hCg γ p hγ hp P rfl hE₀ rfl Λ' 0 L (by linarith only [h.2.1]) h.2.2).trans ?_
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith only [h.2.1]) _))
    · intro N' hN'
      have hN'1 : 1 ≤ N' := by linarith only [hNstar1, hN']
      have hκ : Real.exp (-(m * N' / 4)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := mul_pos hm (by linarith only [hN'1] : (0 : ℝ) < N')
        linarith only [this]
      have h := (resonance_bound_gaussian ν (Λ.filter fun z => siteDist ν 0 z ≤ 2 * N')
        hγ E hκ).2
      refine (measure_le_ofReal_mul_of_card_le (by positivity) h (card_ball_le ν Λ hN'1)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      exact resonance_absorb ν hc0 hfin hcM hN'1

end FroehlichSpencer.T12.Assembly

end
