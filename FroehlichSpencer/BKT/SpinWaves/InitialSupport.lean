/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Initial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# KP Lemma 4.5 with the wave supported on the charge support

The construction of `Initial.lean` is `a j = ϱ*(j) / (4 β)` on one color class and `0` elsewhere,
so `a` is supported in `supp ϱ*`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

/-- KP Lemma 4.5 (p. 23) with the support clause `supp a ⊆ supp ϱ*` of its construction. -/
theorem exists_initialSpinWave_support {V : Type*} {E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (B : BipartiteDegreeFour G) (N₀ : Finset (V → ℤ)) (ρstar : V → ℤ)
    (center : V) (centerOf : (V → ℤ) → V) (β : ℝ)
    (hcenter : G.IsDensityCenter ρstar center) (hneutral : ∑ j, ρstar j = 0)
    (hβ : 0 < β)
    (hseparation : InitialWaveSeparation G N₀ ρstar centerOf) :
    ∃ a : V → ℝ,
      (∀ j, a j ≠ 0 → ρstar j ≠ 0) ∧
      (∀ j, a j ≠ 0 → j ∈ G.densityDomain ρstar center) ∧
      (∀ j, G.laplacian a j ≠ 0 → j ∈ G.densityDomain ρstar center) ∧
      (∀ ρ' ∈ G.comparableDensities N₀ ρstar,
        ∀ j ∈ G.densityDomainPlus ρ' (centerOf ρ'), a j = 0) ∧
      (1 / 16 : ℝ) / β * (∑ j, (ρstar j : ℝ) ^ 2) ≤ energyFunctional G β a ρstar := by
  classical
  obtain ⟨b, hbmass, hbdiam⟩ := exists_initialWaveColor G B ρstar center hcenter hneutral
  let a : V → ℝ := fun j => if B.color j = b then (ρstar j : ℝ) / (4 * β) else 0
  have hnear : ∀ k, a k ≠ 0 → B.color k = b := by
    intro k hk
    dsimp [a] at hk
    by_cases hc : B.color k = b
    · exact hc
    · simp [hc] at hk
  have hcenterDist (k : V) (hk : ρstar k ≠ 0) :
      G.toSimpleGraph.dist k center ≤ G.densityDiameter ρstar := by
    unfold Multigraph.densityDiameter
    exact Finset.le_sup (f := fun p : V × V => G.toSimpleGraph.dist p.1 p.2)
      (b := (k, center))
      (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcenter.1⟩⟩)
  have hdensityPositive : 1 ≤ G.densityDiameter ρstar := by
    by_contra hn
    have hd0 : G.densityDiameter ρstar = 0 := by omega
    have hzero : ∀ x, ρstar x ≠ 0 → x = center := by
      intro x hx
      have hdx := hcenterDist x hx
      have heq := (hG.preconnected x center).dist_eq_zero_iff.mp (by simpa [hd0] using hdx)
      exact heq
    have hsum : (∑ x, ρstar x) = ρstar center := by
      apply Finset.sum_eq_single_of_mem center (Finset.mem_univ center)
      intro x hx hxc
      by_contra hxne
      exact hxc (hzero x hxne)
    rw [hsum] at hneutral
    exact hcenter.1 (by exact_mod_cast hneutral)
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · intro j haj
    by_contra hz
    simp [a, hz] at haj
  · intro j haj
    have hρj : ρstar j ≠ 0 := by
      by_contra hz
      simp [a, hz] at haj
    have hdj : G.toSimpleGraph.dist j center ≤ G.densityDiameter ρstar := by
      unfold Multigraph.densityDiameter
      exact Finset.le_sup (f := fun p : V × V => G.toSimpleGraph.dist p.1 p.2)
        (b := (j, center))
        (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρj⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcenter.1⟩⟩)
    have hjcolor : B.color j = b := hnear j haj
    have hjdomain : G.toSimpleGraph.dist j center < 2 * G.densityDiameter ρstar := by
      by_cases hd1 : G.densityDiameter ρstar = 1
      · have hb : b = B.color center := hbdiam hd1
        have heq : j = center := by
          by_contra hne
          have hdist := hcenterDist j hρj
          have hpos : 0 < G.toSimpleGraph.dist j center := hG.pos_dist_of_ne hne
          have hone : G.toSimpleGraph.dist j center = 1 := by omega
          have hadj := SimpleGraph.dist_eq_one_iff_adj.mp hone
          have hadj' := adj_fromSimpleGraph G hadj
          exact not_adj_same_color G B hadj' b hjcolor hb.symm
        subst j
        simp [hd1]
      · omega
    exact hjdomain
  · intro j hΔ
    obtain hja | ⟨k, hka, hadj⟩ := laplacian_ne_zero_has_neighbor G a j hΔ
    · exact (by
        have hρj : ρstar j ≠ 0 := by
          by_contra hz
          simp [a, hz] at hja
        have hdj : G.toSimpleGraph.dist j center ≤ G.densityDiameter ρstar := hcenterDist j hρj
        by_cases hd1 : G.densityDiameter ρstar = 1
        · have heq : j = center := by
            by_contra hne
            have hpos := hG.pos_dist_of_ne hne
            have hone : G.toSimpleGraph.dist j center = 1 := by omega
            have hadj' := adj_fromSimpleGraph G (SimpleGraph.dist_eq_one_iff_adj.mp hone)
            exact not_adj_same_color G B hadj' b (hnear j hja) (hbdiam hd1).symm
          subst j
          simp [Multigraph.densityDomain, hd1]
        · have hgt : 1 < G.densityDiameter ρstar := by omega
          change G.toSimpleGraph.dist j center < 2 * G.densityDiameter ρstar
          omega)
    · have hρk : ρstar k ≠ 0 := by
        by_contra hz
        simp [a, hz] at hka
      have hdk : G.toSimpleGraph.dist k center ≤ G.densityDiameter ρstar := hcenterDist k hρk
      have hjk : G.toSimpleGraph.dist j k ≤ 1 := by
        exact (SimpleGraph.dist_eq_one_iff_adj.mpr (adj_toSimpleGraph G hadj)).le
      by_cases hd1 : G.densityDiameter ρstar = 1
      · have hcenterColor := hbdiam hd1
        have heq : k = center := by
          by_contra hne
          have hpos := hG.pos_dist_of_ne hne
          have hone : G.toSimpleGraph.dist k center = 1 := by omega
          have hadj' := adj_fromSimpleGraph G (SimpleGraph.dist_eq_one_iff_adj.mp hone)
          exact not_adj_same_color G B hadj' b (hnear k hka) hcenterColor.symm
        subst k
        have hdist : G.toSimpleGraph.dist j center ≤ 1 := by simpa using hjk
        change G.toSimpleGraph.dist j center < 2 * G.densityDiameter ρstar
        simp [hd1]
        omega
      · change G.toSimpleGraph.dist j center < 2 * G.densityDiameter ρstar
        have hdist := hG.dist_triangle (u := j) (v := k) (w := center)
        omega
  · intro ρ' hρ' j hj
    by_contra hne
    obtain ⟨k, hk, hEqAdj⟩ := (G.mem_densityDomainPlus).1 hj
    have hadjDist : G.toSimpleGraph.dist j k ≤ 1 := by
      rcases hEqAdj with heq | hadj
      · subst j
        simp
      · exact (SimpleGraph.dist_eq_one_iff_adj.mpr hadj).le
    have hρj : ρstar j ≠ 0 := by
      by_contra hzero
      simp [a, hzero] at hne
    have hfar := hseparation ρ' hρ' k hk j hρj
    have hfar' : 2 < G.toSimpleGraph.dist k j := by
      simpa only [SimpleGraph.dist_comm] using hfar
    have hadjDist' : G.toSimpleGraph.dist k j ≤ 1 := by
      simpa only [SimpleGraph.dist_comm] using hadjDist
    omega
  · let ρone : V → ℝ := fun j => if B.color j = b then (ρstar j : ℝ) else 0
    have hρone_support : ∀ j, ρone j ≠ 0 → B.color j = b := by
      intro j hj
      simp only [ρone] at hj
      split_ifs at hj with hcolor
      · exact hcolor
      · exact (hj rfl).elim
    have ha_formula : ∀ j, a j = ρone j / (4 * β) := by
      intro j
      simp [a, ρone]
      split_ifs <;> simp
    have hpair : Multigraph.pairing a (fun j => (ρstar j : ℝ)) =
        (∑ j, ρone j ^ 2) / (4 * β) := by
      unfold Multigraph.pairing
      calc
        (∑ j, a j * (ρstar j : ℝ)) = ∑ j, ρone j ^ 2 / (4 * β) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ha_formula]
          by_cases hc : B.color j = b
          · simp [ρone, hc]
            ring
          · simp [ρone, hc]
        _ = (∑ j, ρone j ^ 2) / (4 * β) := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    have henergy := energy_le_four_sum_sq_of_one_color G B b a hnear
    have hsquare : ∑ j, a j ^ 2 = (∑ j, ρone j ^ 2) / (16 * β ^ 2) := by
      calc
        (∑ j, a j ^ 2) = ∑ j, ρone j ^ 2 / (16 * β ^ 2) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ha_formula]
          ring
        _ = (∑ j, ρone j ^ 2) / (16 * β ^ 2) := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    have hmass : (1 / 2 : ℝ) * (∑ j, (ρstar j : ℝ) ^ 2) ≤ ∑ j, ρone j ^ 2 := by
      simpa [ρone, colorMass] using hbmass
    have henergy' : G.energy a ≤ (∑ j, ρone j ^ 2) / (4 * β ^ 2) := by
      rw [hsquare] at henergy
      have hbpos : 0 < β ^ 2 := sq_pos_of_pos hβ
      field_simp at henergy ⊢
      nlinarith only [henergy]
    have hmassnonneg : 0 ≤ ∑ j, ρone j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left henergy' (by positivity : 0 ≤ β / 2)
    have henergyBound : (∑ j, ρone j ^ 2) / (8 * β) ≤ energyFunctional G β a ρstar := by
      unfold energyFunctional
      rw [hpair]
      field_simp [hβ.ne'] at hmul ⊢
      nlinarith only [hmul]
    have htarget : ((∑ j, (ρstar j : ℝ) ^ 2) / 2) / (8 * β) ≤
        (∑ j, ρone j ^ 2) / (8 * β) := by
      exact div_le_div_of_nonneg_right (by nlinarith only [hmass]) (by positivity)
    have hfinal : ((1 / 16 : ℝ) / β) * (∑ j, (ρstar j : ℝ) ^ 2) ≤
        ((∑ j, (ρstar j : ℝ) ^ 2) / 2) / (8 * β) := by
      field_simp [hβ.ne']
      nlinarith only
    exact hfinal.trans (htarget.trans henergyBound)

end FroehlichSpencer.BKT.SpinWaves

end
