/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Resonance
public import FroehlichSpencer.T12.ResonantBlock
public import FroehlichSpencer.T12.Exterior
public import FroehlichSpencer.T12.Tails
import FroehlichSpencer.IDS.Green


@[expose] public section

namespace FroehlichSpencer.T12.Assembly

open Multiscale


theorem norm_finiteGreen_le_of_localBlock {ν : ℕ} {Λ F : Finset (Site ν)} (hF : F ⊆ Λ)
    (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R)
    (hgap : ∀ j, κ ≤ |(hamiltonian_isHermitian ν F v).eigenvalues j - E|)
    {s t : Site ν} (hs : s ∈ F) (ht : t ∈ F)
    (hrem : ∀ u ∈ F, ∀ (u' : Site ν) (hu' : u' ∈ Λ), u' ∉ F → siteDist ν u u' ≤ 1 →
      ‖finiteGreen ν Λ v E ε hε ⟨u', hu'⟩ ⟨t, hF ht⟩‖ ≤ R) :
    ‖finiteGreen ν Λ v E ε hε ⟨s, hF hs⟩ ⟨t, hF ht⟩‖ ≤ 1 / κ * (1 + 2 * ν * F.card * R) := by
  classical
  have hz : ((E : ℂ) + (ε : ℂ) * Complex.I).im ≠ 0 := by simpa using hε
  have hid := T12.resolventColumn_eq_sub_sum_coupling_of_mem (a := hoppingKernel ν)
    (hoppingKernel_symm ν) (fun x => v x + 2 * (ν : ℝ)) hF hz hs ht
  rw [T12.finiteGreen_eq_resolventColumn, hid]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) F
      ((E : ℂ) + (ε : ℂ) * Complex.I) t s‖ ≤ 1 / κ := by
    have := T12.norm_finiteGreen_le_of_gap F v E ε hε hκ hgap ⟨s, hs⟩ ⟨t, ht⟩
    rwa [T12.finiteGreen_eq_resolventColumn] at this
  have hrest : ‖∑ k ∈ F, ∑ k' ∈ Λ \ F,
      Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) F
        ((E : ℂ) + (ε : ℂ) * Complex.I) k s * hoppingKernel ν k k' *
      Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) Λ
        ((E : ℂ) + (ε : ℂ) * Complex.I) t k'‖ ≤ 1 / κ * (2 * ν * F.card * R) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ F, ‖∑ k' ∈ Λ \ F, _‖
        ≤ ∑ k ∈ F, ∑ k' ∈ Λ \ F, 1 / κ * ‖hoppingKernel ν k k'‖ * R := by
          refine Finset.sum_le_sum fun k hk => ?_
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
          rw [norm_mul, norm_mul]
          by_cases h0 : hoppingKernel ν k k' = 0
          · simp [h0]
          · have hk'' := Finset.mem_sdiff.1 hk'
            have hd : siteDist ν k k' ≤ 1 := by
              rw [siteDist_eq_norm]
              exact IDS.norm_latticeCast_sub_le_one_of_hoppingKernel_ne_zero h0
            have hr := hrem k hk k' hk''.1 hk''.2 hd
            have hg := T12.norm_finiteGreen_le_of_gap F v E ε hε hκ hgap ⟨s, hs⟩ ⟨k, hk⟩
            rw [T12.finiteGreen_eq_resolventColumn] at hr hg
            exact mul_le_mul (mul_le_mul_of_nonneg_right hg (norm_nonneg _)) hr
              (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))
      _ = ∑ k ∈ F, 1 / κ * R * ∑ k' ∈ Λ \ F, ‖hoppingKernel ν k k'‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k' _ => by ring
      _ ≤ ∑ _k ∈ F, 1 / κ * R * (2 * (ν : ℝ)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
            (sum_norm_hoppingKernel_le ν k _) (mul_nonneg (by positivity) hR)
      _ = 1 / κ * (2 * ν * F.card * R) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc _ ≤ 1 / κ + 1 / κ * (2 * ν * F.card * R) := add_le_add h1 hrest
    _ = _ := by ring


private theorem small_core {ν : ℕ} {m N M c : ℝ} (hc : c ≤ (10 * N) ^ ν)
    (hloc : 1 + 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) ≤ Real.exp (m * N / 4)) :
    Real.exp (m * N / 4) * (1 + 2 * ν * c * (2 * Real.exp (-(3 * M * N / 4)))) ≤
      Real.exp (m * N / 2) := by
  have hE0 : 0 < Real.exp (m * N / 4) := Real.exp_pos _
  have hX : 0 ≤ Real.exp (-(3 * M * N / 4)) := (Real.exp_pos _).le
  have hν : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
  have h1 : 1 + 2 * ν * c * (2 * Real.exp (-(3 * M * N / 4))) ≤
      1 + 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) := by
    have : ν * c * Real.exp (-(3 * M * N / 4)) ≤
        ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hν) hX
    linarith only [this]
  have h2 : Real.exp (m * N / 2) = Real.exp (m * N / 4) * Real.exp (m * N / 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2]
  exact mul_le_mul_of_nonneg_left (h1.trans hloc) hE0.le


theorem norm_finiteGreen_le_small {ν : ℕ} (Λ : Finset (Site ν)) (v : Site ν → ℝ) (E : ℝ)
    {m M N : ℝ} (hm : 0 ≤ m) (hM : 0 ≤ M) (hN : 1 ≤ N)
    (hres : v ∉ resonanceEvent ν (Λ.filter fun z => siteDist ν 0 z ≤ 2 * N) E
      (Real.exp (-(m * N / 4))))
    {x : Site ν} (h0 : (0 : Site ν) ∈ Λ) (hx : x ∈ Λ) (hxN : siteDist ν 0 x < N / 2)
    (htower : ∀ (ε : ℝ) (hε : ε ≠ 0) (u : Site ν) (hu : u ∈ Λ), 2 * N < siteDist ν 0 u →
      siteDist ν 0 u ≤ 2 * N + 1 →
      ‖finiteGreen ν Λ v E ε hε ⟨u, hu⟩ ⟨x, hx⟩‖ ≤ 2 * Real.exp (-M * siteDist ν u x / 2))
    (hloc : 1 + 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) ≤ Real.exp (m * N / 4))
    (ε : ℝ) (hε : ε ≠ 0) :
    ‖finiteGreen ν Λ v E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤ Real.exp (m * (N - siteDist ν 0 x)) := by
  classical
  set F : Finset (Site ν) := Λ.filter fun z => siteDist ν 0 z ≤ 2 * N with hFdef
  have hF : F ⊆ Λ := Finset.filter_subset _ _
  have hx0 : 0 ≤ siteDist ν 0 x := siteDist_nonneg ν 0 x
  have h0F : (0 : Site ν) ∈ F := by
    rw [hFdef, Finset.mem_filter]
    exact ⟨h0, by rw [siteDist_self]; linarith⟩
  have hxF : x ∈ F := by
    rw [hFdef, Finset.mem_filter]
    exact ⟨hx, by linarith⟩
  have hκ : 0 < Real.exp (-(m * N / 4)) := Real.exp_pos _
  have hgap : ∀ j, Real.exp (-(m * N / 4)) ≤
      |(hamiltonian_isHermitian ν F v).eigenvalues j - E| := by
    intro j
    by_contra hj
    exact hres ⟨j, (not_le.1 hj).le⟩
  have hR0 : 0 ≤ 2 * Real.exp (-(3 * M * N / 4)) := by positivity
  have hrem : ∀ u ∈ F, ∀ (u' : Site ν) (hu' : u' ∈ Λ), u' ∉ F → siteDist ν u u' ≤ 1 →
      ‖finiteGreen ν Λ v E ε hε ⟨u', hu'⟩ ⟨x, hF hxF⟩‖ ≤ 2 * Real.exp (-(3 * M * N / 4)) := by
    intro u hu u' hu' hu'F hd
    have huF := (Finset.mem_filter.1 hu).2
    have hout : 2 * N < siteDist ν 0 u' := by
      by_contra hc
      exact hu'F (Finset.mem_filter.2 ⟨hu', not_lt.1 hc⟩)
    have hup : siteDist ν 0 u' ≤ 2 * N + 1 :=
      (siteDist_triangle ν 0 u' u).trans (by
        have := siteDist_comm ν u' u
        linarith [siteDist_comm ν u u'])
    have hdx : 3 * N / 2 ≤ siteDist ν u' x := by
      have := siteDist_triangle ν 0 u' x
      have h2 := siteDist_comm ν x u'
      linarith
    refine (htower ε hε u' hu' hout hup).trans ?_
    have : -(3 * M * N / 4) ≥ -M * siteDist ν u' x / 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) (by norm_num)
  have key := norm_finiteGreen_le_of_localBlock hF v E ε hε hκ hR0 hgap h0F hxF hrem
  have hcard : (F.card : ℝ) ≤ (10 * N) ^ ν := by
    have := T12.card_filter_siteDist_le Λ 0 (R := 2 * N) (by linarith)
    rwa [show 5 * (2 * N) = 10 * N by ring] at this
  have hcore := small_core (ν := ν) (c := F.card) hcard hloc
  have hinv : 1 / Real.exp (-(m * N / 4)) = Real.exp (m * N / 4) := by
    rw [one_div, ← Real.exp_neg, neg_neg]
  rw [hinv] at key
  refine key.trans (hcore.trans (Real.exp_le_exp.2 ?_))
  nlinarith

end FroehlichSpencer.T12.Assembly

end
