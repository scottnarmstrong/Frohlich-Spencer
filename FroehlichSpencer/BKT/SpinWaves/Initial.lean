/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Defs
public import FroehlichSpencer.BKT.FiniteGraph.Laplacian
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # KP Lemma 4.5: initial spin wave

This file proves the initial-wave estimate on a bipartite graph of degree at most four. The
remaining finite-square inputs are isolated in `BipartiteDegreeFour`; the separation hypothesis
is precisely the geometric consequence of KP Theorem 2.2(b) used in Lemma 4.5.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

universe u v

variable {V : Type u} {E : Type v}

/-- Squared charge mass carried by one class of the bipartition. -/
noncomputable def colorMass [Fintype V] (color : V → Bool) (ρ : V → ℤ) (b : Bool) : ℝ :=
  ∑ j, (if color j = b then (ρ j : ℝ) ^ 2 else 0)

/-- The graph facts used from the free or even-periodic square geometry in KP Lemma 4.5. -/
structure BipartiteDegreeFour (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] where
  /-- The two classes of the square-lattice bipartition. -/
  color : V → Bool
  /-- Every edge joins opposite classes. -/
  color_edge : ∀ e, color (G.src e) ≠ color (G.tgt e)
  /-- The number of edge ends at each vertex is at most four. -/
  endpointDegree_le_four : ∀ j,
    (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4
  /-- The diameter-one neutrality fact used to select the center's color class in KP (4.21). -/
  neutral_diameter_one_mass : ∀ ρ center, G.IsDensityCenter ρ center →
    (∑ j, ρ j = 0) → G.densityDiameter ρ = 1 →
      colorMass color ρ (color center) = (∑ j, (ρ j : ℝ) ^ 2) / 2

/-- Convert adjacency in the underlying simple graph to the multigraph relation. -/
theorem adj_fromSimpleGraph [DecidableEq V] (G : Multigraph V E) {j k : V}
    (hjk : G.toSimpleGraph.Adj j k) : G.Adj j k := by
  classical
  change (SimpleGraph.fromRel G.Adj).Adj j k at hjk
  have h := (SimpleGraph.fromRel_adj G.Adj j k).mp hjk
  rcases h with ⟨_, hadj | hadj⟩
  · exact hadj
  · exact G.adj_symm hadj

/-- Adjacent vertices cannot lie in the same class of the bipartition. -/
theorem not_adj_same_color (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (B : BipartiteDegreeFour G) {j k : V}
    (hjk : G.Adj j k) (b : Bool) (hj : B.color j = b) (hk : B.color k = b) : False := by
  rcases hjk with ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
  · exact B.color_edge e (by rw [hs, ht, hj, hk])
  · exact B.color_edge e (by rw [hs, ht, hk, hj])

/-- A multigraph edge gives adjacency in the underlying simple graph. -/
theorem adj_toSimpleGraph [DecidableEq V] (G : Multigraph V E) {j k : V}
    (hjk : G.Adj j k) : G.toSimpleGraph.Adj j k := by
  classical
  rcases hjk with ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
  · have hne : j ≠ k := by
      intro heq
      apply G.src_ne_tgt e
      calc
        G.src e = j := hs
        _ = k := heq
        _ = G.tgt e := ht.symm
    exact (SimpleGraph.fromRel_adj G.Adj j k).2 ⟨hne, Or.inl ⟨e, Or.inl ⟨hs, ht⟩⟩⟩
  · have hne : j ≠ k := by
      intro heq
      apply G.src_ne_tgt e
      calc
        G.src e = k := hs
        _ = j := heq.symm
        _ = G.tgt e := ht.symm
    exact (SimpleGraph.fromRel_adj G.Adj j k).2 ⟨hne, Or.inl ⟨e, Or.inr ⟨hs, ht⟩⟩⟩

/-- A nonzero value of the Laplacian has a nonzero value at the vertex or one of its neighbors. -/
theorem laplacian_ne_zero_has_neighbor [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (a : V → ℝ) (j : V) (hΔ : G.laplacian a j ≠ 0) :
    a j ≠ 0 ∨ ∃ k, a k ≠ 0 ∧ G.Adj j k := by
  classical
  by_contra h
  push Not at h
  have hj : a j = 0 := h.1
  have hterm : ∀ e,
      (if G.src e = j then a (G.tgt e) - a j else 0) +
        (if G.tgt e = j then a (G.src e) - a j else 0) = 0 := by
    intro e
    by_cases hs : G.src e = j
    · have ht : a (G.tgt e) = 0 := by
        by_contra hne
        have hadj : G.Adj j (G.tgt e) := ⟨e, Or.inl ⟨hs, rfl⟩⟩
        exact h.2 (G.tgt e) hne hadj
      simp [hs, ht, hj]
    · by_cases ht : G.tgt e = j
      · have hs' : a (G.src e) = 0 := by
          by_contra hne
          have hadj : G.Adj j (G.src e) := ⟨e, Or.inr ⟨rfl, ht⟩⟩
          exact h.2 (G.src e) hne hadj
        simp [hs, ht, hs', hj]
      · simp [hs, ht]
  have : G.laplacian a j = 0 := by
    simp only [Multigraph.laplacian]
    simp_rw [hterm]
    simp
  exact hΔ this

/-- A bound on incident edge ends controls the edge-once energy of a field supported on one
bipartition class. -/
theorem energy_le_four_sum_sq_of_one_color [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (B : BipartiteDegreeFour G) (b : Bool) (a : V → ℝ)
    (ha : ∀ j, a j ≠ 0 → B.color j = b) :
    G.energy a ≤ 4 * ∑ j, a j ^ 2 := by
  classical
  let srcCount : V → ℕ := fun j => (Finset.univ.filter fun e => G.src e = j).card
  let tgtCount : V → ℕ := fun j => (Finset.univ.filter fun e => G.tgt e = j).card
  have hEdge (e : E) :
      (G.grad a e) ^ 2 = a (G.src e) ^ 2 + a (G.tgt e) ^ 2 := by
    have hcolor := B.color_edge e
    by_cases hsrc : a (G.src e) = 0
    · simp [Multigraph.grad, hsrc]
    · have htgt0 : a (G.tgt e) = 0 := by
        by_contra htgt
        have hcs := ha _ hsrc
        have hct := ha _ htgt
        exact hcolor (hcs.trans hct.symm)
      simp [Multigraph.grad, htgt0]
  have hsumSrc : ∑ e, a (G.src e) ^ 2 = ∑ j, (srcCount j : ℝ) * a j ^ 2 := by
    simp only [srcCount]
    calc
      (∑ e, a (G.src e) ^ 2) =
          ∑ e, ∑ j, if G.src e = j then a j ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            simp
      _ = ∑ j, ∑ e, if G.src e = j then a j ^ 2 else 0 := Finset.sum_comm
      _ = ∑ j, (↑(Finset.univ.filter fun e => G.src e = j).card) * a j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_filter]
            simp
  have hsumTgt : ∑ e, a (G.tgt e) ^ 2 = ∑ j, (tgtCount j : ℝ) * a j ^ 2 := by
    simp only [tgtCount]
    calc
      (∑ e, a (G.tgt e) ^ 2) =
          ∑ e, ∑ j, if G.tgt e = j then a j ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            simp
      _ = ∑ j, ∑ e, if G.tgt e = j then a j ^ 2 else 0 := Finset.sum_comm
      _ = ∑ j, (↑(Finset.univ.filter fun e => G.tgt e = j).card) * a j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_filter]
            simp
  rw [Multigraph.energy]
  calc
    (∑ e, (G.grad a e) ^ 2) = ∑ e, (a (G.src e) ^ 2 + a (G.tgt e) ^ 2) := by
          apply Finset.sum_congr rfl
          intro e he
          exact hEdge e
    _ = ∑ j, ((srcCount j + tgtCount j : ℕ) : ℝ) * a j ^ 2 := by
          rw [Finset.sum_add_distrib, hsumSrc, hsumTgt, ← Finset.sum_add_distrib]
          simp_rw [Nat.cast_add, add_mul]
    _ ≤ ∑ j, (4 : ℝ) * a j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hdeg := B.endpointDegree_le_four j
          change srcCount j + tgtCount j ≤ 4 at hdeg
          have hdeg' : ((srcCount j + tgtCount j : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hdeg
          exact mul_le_mul_of_nonneg_right hdeg' (sq_nonneg (a j))
    _ = 4 * ∑ j, a j ^ 2 := by rw [Finset.mul_sum]

/--
Explicit KP Theorem 2.2(b) separation input used in Lemma 4.5: every point of `D(ρ')` is at
distance greater than two from the support of `ρ*`, for each comparable density.
-/
def InitialWaveSeparation [Fintype V] (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (ρstar : V → ℤ) (centerOf : (V → ℤ) → V) : Prop :=
  ∀ ρ' ∈ G.comparableDensities N₀ ρstar, ∀ j ∈ G.densityDomain ρ' (centerOf ρ'),
    ∀ k, ρstar k ≠ 0 → 2 < G.toSimpleGraph.dist j k

/-- The four KP Lemma 4.5 clauses, stated for one common real-valued witness. -/
def InitialSpinWaveSpec [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (ρstar : V → ℤ)
    (center : V) (centerOf : (V → ℤ) → V) (β : ℝ) : Prop :=
  ∃ a : V → ℝ,
    (∀ j, a j ≠ 0 → ∃ k, ρstar k ≠ 0 ∧ G.toSimpleGraph.dist j k ≤ 1) ∧
    (∀ j, a j ≠ 0 → j ∈ G.densityDomain ρstar center) ∧
    (∀ j, G.laplacian a j ≠ 0 → j ∈ G.densityDomain ρstar center) ∧
    (∀ ρ' ∈ G.comparableDensities N₀ ρstar,
      ∀ j ∈ G.densityDomainPlus ρ' (centerOf ρ'),
      a j = 0) ∧
    (1 / 16 : ℝ) / β * (∑ j, (ρstar j : ℝ) ^ 2) ≤ energyFunctional G β a ρstar

/-- The candidate specification is exactly the four clauses of KP Lemma 4.5 on p. 23. -/
theorem initialSpinWaveSpec_characterization [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (ρstar : V → ℤ)
    (center : V) (centerOf : (V → ℤ) → V) (β : ℝ) :
    InitialSpinWaveSpec G N₀ ρstar center centerOf β ↔
      ∃ a : V → ℝ,
        (∀ j, a j ≠ 0 → ∃ k, ρstar k ≠ 0 ∧ G.toSimpleGraph.dist j k ≤ 1) ∧
        (∀ j, a j ≠ 0 → j ∈ G.densityDomain ρstar center) ∧
        (∀ j, G.laplacian a j ≠ 0 → j ∈ G.densityDomain ρstar center) ∧
        (∀ ρ' ∈ G.comparableDensities N₀ ρstar,
          ∀ j ∈ G.densityDomainPlus ρ' (centerOf ρ'), a j = 0) ∧
        (1 / 16 : ℝ) / β * (∑ j, (ρstar j : ℝ) ^ 2) ≤ energyFunctional G β a ρstar := Iff.rfl

/-- Choose a bipartition class carrying at least half the squared charge mass; when the diameter
is one, choose the class containing the selected center. Neutrality makes the two masses equal in
that case (KP (4.21), p. 23). -/
theorem exists_initialWaveColor [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E)
    (B : BipartiteDegreeFour G) (ρ : V → ℤ) (center : V)
    (hcenter : G.IsDensityCenter ρ center) (hneutral : ∑ j, ρ j = 0) :
      ∃ b : Bool,
      (1 / 2 : ℝ) * (∑ j, (ρ j : ℝ) ^ 2) ≤
          ∑ j, (if B.color j = b then (ρ j : ℝ) ^ 2 else 0) ∧
      (G.densityDiameter ρ = 1 → b = B.color center) := by
  classical
  let mass : Bool → ℝ := fun b => colorMass B.color ρ b
  have htotal : (∑ j, (ρ j : ℝ) ^ 2) = mass true + mass false := by
    simp only [mass, colorMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    cases B.color j <;> simp
  have hnonneg (b : Bool) : 0 ≤ mass b := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  have hcenterColorMass :
      G.densityDiameter ρ = 1 → mass (B.color center) = (∑ j, (ρ j : ℝ) ^ 2) / 2 := by
    intro hdiam
    simpa [mass] using B.neutral_diameter_one_mass ρ center hcenter hneutral hdiam
  by_cases hdiam : G.densityDiameter ρ = 1
  · refine ⟨B.color center, ?_, ?_⟩
    · change (1 / 2 : ℝ) * (∑ j, (ρ j : ℝ) ^ 2) ≤ mass (B.color center)
      rw [hcenterColorMass hdiam]
      nlinarith only
    · intro _
      rfl
  ·
    by_cases hmass : mass true ≤ mass false
    · refine ⟨false, ?_, ?_⟩
      · rw [htotal]
        change (1 / 2 : ℝ) * (mass true + mass false) ≤ mass false
        linarith only [hmass]
      · intro hd
        exact (hdiam hd).elim
    · refine ⟨true, ?_, ?_⟩
      · rw [htotal]
        change (1 / 2 : ℝ) * (mass true + mass false) ≤ mass true
        have hmass' : mass false < mass true := lt_of_not_ge hmass
        linarith only [hmass']
      · intro hd
        exact (hdiam hd).elim

/-- KP Lemma 4.5 (p. 23), conditional only on the square degree/bipartition facts and the
separation consequence of Theorem 2.2(b). One witness satisfies all four clauses. -/
theorem exists_initialSpinWave [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (B : BipartiteDegreeFour G) (N₀ : Finset (V → ℤ)) (ρstar : V → ℤ)
    (center : V) (centerOf : (V → ℤ) → V) (β : ℝ)
    (hcenter : G.IsDensityCenter ρstar center) (hneutral : ∑ j, ρstar j = 0)
    (hβ : 0 < β)
    (hseparation : InitialWaveSeparation G N₀ ρstar centerOf) :
    InitialSpinWaveSpec G N₀ ρstar center centerOf β := by
  unfold InitialSpinWaveSpec
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
    simp only [a] at haj
    split_ifs at haj with hcol
    · refine ⟨j, ?_, ?_⟩
      · by_contra hz
        simp [hz] at haj
      · simp
    · exact (haj rfl).elim
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

/-- KP Lemma 4.5 on the free square carrier. Its only geometric inputs are the bipartition and
degree data and the Theorem 2.2(b) separation consequence displayed in the arguments. -/
theorem exists_initialSpinWave_squareFree (L : ℕ) (hL : 1 < L)
    (B : BipartiteDegreeFour (squareFree L)) (N₀ : Finset ((Fin L × Fin L) → ℤ))
    (ρstar : (Fin L × Fin L) → ℤ) (center : Fin L × Fin L)
    (centerOf : ((Fin L × Fin L) → ℤ) → Fin L × Fin L) (β : ℝ)
    (hcenter : (squareFree L).IsDensityCenter ρstar center)
    (hneutral : ∑ j, ρstar j = 0) (hβ : 0 < β)
    (hseparation : InitialWaveSeparation (squareFree L) N₀ ρstar centerOf) :
    InitialSpinWaveSpec (squareFree L) N₀ ρstar center centerOf β :=
  exists_initialSpinWave (squareFree L) (squareFree_connected L hL) B N₀ ρstar center
    centerOf β hcenter hneutral hβ hseparation

/-- KP Lemma 4.5 on an even periodic square carrier. Its only geometric inputs are the
bipartition and degree data and the Theorem 2.2(b) separation consequence displayed in the
arguments. -/
theorem exists_initialSpinWave_squarePeriodic (L : ℕ) (hL : 1 < L) (_hEven : Even L)
    (B : BipartiteDegreeFour (squarePeriodic L)) (N₀ : Finset ((Fin L × Fin L) → ℤ))
    (ρstar : (Fin L × Fin L) → ℤ) (center : Fin L × Fin L)
    (centerOf : ((Fin L × Fin L) → ℤ) → Fin L × Fin L) (β : ℝ)
    (hcenter : (squarePeriodic L).IsDensityCenter ρstar center)
    (hneutral : ∑ j, ρstar j = 0) (hβ : 0 < β)
    (hseparation : InitialWaveSeparation (squarePeriodic L) N₀ ρstar centerOf) :
    InitialSpinWaveSpec (squarePeriodic L) N₀ ρstar center centerOf β :=
  exists_initialSpinWave (squarePeriodic L) (squarePeriodic_connected L hL) B N₀ ρstar center
    centerOf β hcenter hneutral hβ hseparation

end FroehlichSpencer.BKT.SpinWaves

end
