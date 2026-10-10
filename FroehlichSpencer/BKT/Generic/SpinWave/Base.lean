/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.LocalFactor
public import FroehlichSpencer.BKT.Generic.SpinWave.Graded
public import FroehlichSpencer.BKT.SpinWaves.Initial
public import FroehlichSpencer.BKT.SpinWaves.InitialSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

/-! # Sign base waves and cost-energy additivity

The base pieces are the source's unit sign waves at individual sites in the larger bipartition
class.  The selector and half-mass estimate are exactly `exists_initialWaveColor`; a finite family
of these pieces reconstructs the selected charge profile when each wave is multiplied by the
absolute charge at its site.  The additivity lemma is independent of the cost function: it uses
only `c 0 = 0` and disjoint gradient supports.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.SpinWave

universe u v

variable {V : Type u} {E : Type v}

/-- The unit sign of an integer charge, with value zero at zero. -/
def signUnit (q : ℤ) : ℝ := if 0 < q then 1 else if q < 0 then -1 else 0

/-- A unit sign wave supported at one charged vertex. -/
def signBaseWave [DecidableEq V] (ρ : V → ℤ) (m : V) : V → ℝ :=
  fun j => if j = m then signUnit (ρ m) else 0

lemma signUnit_mul_cast (q : ℤ) (hq : q ≠ 0) : signUnit q * (q : ℝ) = |(q : ℝ)| := by
  by_cases hpos : 0 < q
  · have hposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hpos
    simp [signUnit, hpos, abs_of_pos hposR]
  · have hneg : q < 0 := by omega
    have hnegR : (q : ℝ) < 0 := by exact_mod_cast hneg
    simp [signUnit, hpos, hneg, abs_of_neg hnegR]

lemma signBaseWave_at [DecidableEq V] (ρ : V → ℤ) (m : V) (_hρ : ρ m ≠ 0) :
    signBaseWave ρ m m = signUnit (ρ m) := by
  simp [signBaseWave]

lemma signBaseWave_eq_zero_of_ne [DecidableEq V] (ρ : V → ℤ) (m j : V) (hjm : j ≠ m) :
    signBaseWave ρ m j = 0 := by
  simp [signBaseWave, hjm]

/-- Pairing the sign wave with its charge gives the absolute charge at its site. -/
theorem pairing_signBaseWave [Fintype V] [DecidableEq V] (ρ : V → ℤ) (m : V)
    (hρ : ρ m ≠ 0) :
    Multigraph.pairing (signBaseWave ρ m) (fun j => (ρ j : ℝ)) = |(ρ m : ℝ)| := by
  classical
  unfold Multigraph.pairing
  rw [Finset.sum_eq_single m]
  · rw [signBaseWave_at ρ m hρ, signUnit_mul_cast]
    · exact hρ
  · intro j _ hjm
    simp [signBaseWave, hjm]
  · intro hm
    exact (hm (Finset.mem_univ m)).elim

private lemma one_le_abs_cast_of_ne_zero {q : ℤ} (hq : q ≠ 0) : 1 ≤ |(q : ℝ)| := by
  have hcases : q ≤ -1 ∨ 1 ≤ q := by omega
  rcases hcases with hneg | hpos
  · have hnegR : (q : ℝ) ≤ -1 := by exact_mod_cast hneg
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hposR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpos
    rw [abs_of_nonneg (by linarith)]
    exact hposR

private lemma abs_signUnit_of_ne_zero (q : ℤ) (hq : q ≠ 0) : |signUnit q| = 1 := by
  by_cases hpos : 0 < q
  · simp [signUnit, hpos]
  · have hneg : q < 0 := by omega
    simp [signUnit, hpos, hneg]

/-- A sign base wave costs at most four times the square of its paired charge. -/
theorem energy_signBaseWave_le [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (B : SpinWaves.BipartiteDegreeFour G) (ρ : V → ℤ) (m : V)
    (hρ : ρ m ≠ 0) :
    G.energy (signBaseWave ρ m) ≤ 4 * |(ρ m : ℝ)| ^ 2 := by
  classical
  have hcolor : ∀ j, signBaseWave ρ m j ≠ 0 → B.color j = B.color m := by
    intro j hj
    by_cases h : j = m
    · simp [h]
    · simp [signBaseWave, h] at hj
  have hE := SpinWaves.energy_le_four_sum_sq_of_one_color G B (B.color m)
    (signBaseWave ρ m) hcolor
  have hsum : ∑ j, (signBaseWave ρ m j) ^ 2 = 1 := by
    unfold signBaseWave signUnit
    rw [Finset.sum_eq_single m]
    · by_cases hp : 0 < ρ m
      · simp [hp]
      · have hn : ρ m < 0 := by omega
        simp [hp, hn]
    · intro j _ hjm
      simp [hjm]
    · intro hm
      exact (hm (Finset.mem_univ m)).elim
  have hcharge : 1 ≤ |(ρ m : ℝ)| := one_le_abs_cast_of_ne_zero hρ
  nlinarith only [hE, hsum, hcharge]

/-- Distinct sign waves chosen from one bipartition class have disjoint gradient supports. -/
theorem grad_disjoint_signBaseWave [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (B : SpinWaves.BipartiteDegreeFour G) (ρ : V → ℤ)
    {m m' : V} (hm : ρ m ≠ 0) (hm' : ρ m' ≠ 0)
    (hcolor : B.color m = B.color m') (hne : m ≠ m') (e : E) :
    G.grad (signBaseWave ρ m) e = 0 ∨ G.grad (signBaseWave ρ m') e = 0 := by
  by_contra h
  push Not at h
  have hincident (x : V) (hx : ρ x ≠ 0) (hg : G.grad (signBaseWave ρ x) e ≠ 0) :
      G.src e = x ∨ G.tgt e = x := by
    by_contra hc
    push Not at hc
    apply hg
    simp only [Multigraph.grad]
    simp [signBaseWave, hc.1, hc.2]
  obtain hsrc | htgt := hincident m hm h.1
  · obtain hsrc' | htgt' := hincident m' hm' h.2
    · exact hne (hsrc.symm.trans hsrc')
    · exact B.color_edge e (by rw [hsrc, htgt', hcolor])
  · obtain hsrc' | htgt' := hincident m' hm' h.2
    · exact B.color_edge e (by rw [hsrc', htgt, hcolor.symm])
    · exact hne (htgt.symm.trans htgt')

/-- A base wave vanishes throughout every comparable density's enlarged domain when the
Theorem 2.2(b) separation input holds. -/
theorem signBaseWave_eq_zero_on_densityDomainPlus [Fintype V] [DecidableEq V]
    (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    [Fintype E] (ρ : V → ℤ) (m : V) (hm : ρ m ≠ 0)
    (hsep : SpinWaves.InitialWaveSeparation G N₀ ρ centerOf)
    {ρ' : V → ℤ} (hρ' : ρ' ∈ G.comparableDensities N₀ ρ)
    {x : V} (hx : x ∈ G.densityDomainPlus ρ' (centerOf ρ')) :
    signBaseWave ρ m x = 0 := by
  classical
  obtain ⟨y, hy, hxy⟩ := (G.mem_densityDomainPlus).1 hx
  have hfar := hsep ρ' hρ' y hy m hm
  have hxm : x ≠ m := by
    intro hxm
    subst x
    have hnear' : G.toSimpleGraph.dist y m ≤ 1 := by
      rcases hxy with hxy | hxy
      · subst y
        simp
      · exact (SimpleGraph.dist_eq_one_iff_adj.mpr hxy.symm).le
    omega
  exact signBaseWave_eq_zero_of_ne ρ m x hxm

/-- The finite set of charged vertices in the selected bipartition class. -/
def signBaseSites [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E)
    (B : SpinWaves.BipartiteDegreeFour G)
    (ρ : V → ℤ) (b : Bool) : Finset V :=
  Finset.univ.filter fun m => ρ m ≠ 0 ∧ B.color m = b

/-- The large-color choice from KP Lemma 4.5. -/
theorem exists_signBaseColor [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (B : SpinWaves.BipartiteDegreeFour G) (ρ : V → ℤ)
    (center : V) (hcenter : G.IsDensityCenter ρ center) (hneutral : ∑ j, ρ j = 0) :
    ∃ b : Bool,
      (1 / 2 : ℝ) * (∑ j, (ρ j : ℝ) ^ 2) ≤
        ∑ j, (if B.color j = b then (ρ j : ℝ) ^ 2 else 0) ∧
      (G.densityDiameter ρ = 1 → b = B.color center) :=
  SpinWaves.exists_initialWaveColor G B ρ center hcenter hneutral

/-- Each site sign wave has gradient magnitude at most one on every edge. -/
theorem abs_grad_signBaseWave_le [DecidableEq V]
    (G : Multigraph V E) (ρ : V → ℤ) (m : V) (hm : ρ m ≠ 0) (e : E) :
    |G.grad (signBaseWave ρ m) e| ≤ 1 := by
  by_cases hs : G.src e = m
  · have ht : G.tgt e ≠ m := by
      intro heq
      exact G.src_ne_tgt e (hs.trans heq.symm)
    rw [Multigraph.grad]
    simp [signBaseWave, hs, ht, abs_signUnit_of_ne_zero (ρ m) hm]
  · by_cases ht : G.tgt e = m
    · have hs' : G.src e ≠ m := hs
      rw [Multigraph.grad]
      simp [signBaseWave, hs', ht, abs_signUnit_of_ne_zero (ρ m) hm]
    · rw [Multigraph.grad]
      simp [signBaseWave, hs, ht]

/-- The larger-color base family is a graded spin wave: its members are the source sign waves
at the charged sites of the selected class.  The color choice retains at least half of the
squared charge mass, as required by KP Lemma 4.5. -/
theorem exists_gradedSignBaseSpinWave [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (B : SpinWaves.BipartiteDegreeFour G) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (ρ : V → ℤ)
    (hcenter : G.IsDensityCenter ρ (centerOf ρ)) (hneutral : ∑ j, ρ j = 0)
    (hsep : SpinWaves.InitialWaveSeparation G N₀ ρ centerOf) :
    ∃ b : Bool, (1 / 2 : ℝ) * (∑ j, (ρ j : ℝ) ^ 2) ≤
      ∑ j, (if B.color j = b then (ρ j : ℝ) ^ 2 else 0) ∧
      ∃ W : GradedSpinWave.{u, v, u} G N₀ centerOf ρ, W.scale = fun _ => 0 := by
  classical
  obtain ⟨b, hmass, _hdiam⟩ := exists_signBaseColor G B ρ (centerOf ρ) hcenter hneutral
  let S := signBaseSites G B ρ b
  let I := {m : V // m ∈ S}
  let W : GradedSpinWave G N₀ centerOf ρ := {
    ι := I
    finite := inferInstance
    alpha := 7 / 4
    alpha_gt_one := by norm_num
    K₀ := 4
    K₀_nonneg := by norm_num
    K₁ := 1
    K₁_nonneg := by norm_num
    scale := fun _ => 0
    piece := fun t => signBaseWave ρ t.val
    charge := fun t => |(ρ t.val : ℝ)|
    countPerScale := fun k => if k = 0 then (Fintype.card I : ℝ) else 0
    countPerScale_nonneg := by intro k; split_ifs <;> positivity
    count := by
      intro k
      by_cases hk : k = 0
      · subst k
        simp
      · have hnot : ¬ (0 : ℕ) = k := by simpa [eq_comm] using hk
        simp [hk, hnot]
    grad_disjoint := by
      intro t t' hne e
      have ht := (Finset.mem_filter.mp t.property).2
      have ht' := (Finset.mem_filter.mp t'.property).2
      have hne' : t.val ≠ t'.val := by
        intro h
        exact hne (Subtype.ext h)
      exact grad_disjoint_signBaseWave G B ρ ht.1 ht'.1 (ht.2.trans ht'.2.symm) hne' e
    const_plus := by
      intro t ρ' hρ'
      have ht := (Finset.mem_filter.mp t.property).2
      exact ⟨0, fun j' hj' => signBaseWave_eq_zero_on_densityDomainPlus
        G N₀ centerOf ρ t.val ht.1 hsep hρ' hj'⟩
    supp := by
      intro t j hj
      have ht := (Finset.mem_filter.mp t.property).2
      have hjm : j = t.val := by
        by_contra hne
        exact hj (signBaseWave_eq_zero_of_ne ρ t.val j hne)
      subst j
      exact G.mem_densityDomain_of_center hG hneutral hcenter ht.1
    pairing := by
      intro t
      have ht := (Finset.mem_filter.mp t.property).2
      exact pairing_signBaseWave ρ t.val ht.1
    charge_ge_one := by
      intro t
      have ht := (Finset.mem_filter.mp t.property).2
      simpa [abs_abs] using one_le_abs_cast_of_ne_zero ht.1
    energy_le := by
      intro t
      have ht := (Finset.mem_filter.mp t.property).2
      exact (energy_signBaseWave_le G B ρ t.val ht.1)
    grad_le := by
      intro t e
      have ht := (Finset.mem_filter.mp t.property).2
      simpa using abs_grad_signBaseWave_le G ρ t.val ht.1 e
  }
  exact ⟨b, hmass, W, rfl⟩

/-- The sitewise cost-energy translation energy is additive for an arbitrary cost `c` with
`c 0 = 0` across pieces with pairwise disjoint gradient supports. -/
private lemma cost_sum_of_pairwise_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (b : ι → ℝ) (c : ℝ → ℝ) (hc0 : c 0 = 0)
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → b i = 0 ∨ b i' = 0) :
    c (∑ i ∈ s, b i) = ∑ i ∈ s, c (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hc0
  | @insert a s ha ih =>
      have hdisj' : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → b i = 0 ∨ b i' = 0 := by
        intro i hi i' hi' hne
        exact hdisj i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi') hne
      by_cases hzero : b a = 0
      · simp [Finset.sum_insert, ha, hzero, ih hdisj', hc0]
      · have htail : ∀ i ∈ s, b i = 0 := by
          intro i hi
          have hne : a ≠ i := by
            intro heq
            subst i
            exact ha hi
          rcases hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
              hne with h | h
          · exact (hzero h).elim
          · exact h
        have hsumB : ∑ i ∈ s, b i = 0 := Finset.sum_eq_zero htail
        have hsumc : ∑ i ∈ s, c (b i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [htail i hi, hc0]
        simp only [Finset.sum_insert ha]
        rw [hsumB, hsumc]
        simp

theorem translationEnergy_sum_of_grad_disjoint [Fintype V] [Fintype E]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ℝ → ℝ) (hc0 : c 0 = 0)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (a : ι → V → ℝ) (ρ : V → ℝ)
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ∀ e,
      D (a i) e = 0 ∨ D (a i') e = 0) :
    translationEnergy c D (fun j => ∑ i ∈ s, a i j) ρ =
      ∑ i ∈ s, translationEnergy c D (a i) ρ := by
  classical
  have hpair : (∑ j, (∑ i ∈ s, a i j) * ρ j) =
      ∑ i ∈ s, ∑ j, a i j * ρ j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
  have hcost : (∑ e, c (D (fun j => ∑ i ∈ s, a i j) e)) =
      ∑ i ∈ s, ∑ e, c (D (a i) e) := by
    have hlinear (e : E) : D (fun j => ∑ i ∈ s, a i j) e = ∑ i ∈ s, D (a i) e := by
      have hsumFun : (fun j : V => ∑ i ∈ s, a i j) = ∑ i ∈ s, a i := by
        funext j
        simp
      calc
        D (fun j => ∑ i ∈ s, a i j) e = D (∑ i ∈ s, a i) e := by rw [hsumFun]
        _ = (∑ i ∈ s, D (a i)) e := by rw [map_sum]
        _ = ∑ i ∈ s, D (a i) e := by simp
    calc
      _ = ∑ e, ∑ i ∈ s, c (D (a i) e) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hlinear e]
        exact cost_sum_of_pairwise_zero s (fun i => D (a i) e) c hc0
          (fun i hi i' hi' hne => hdisj i hi i' hi' hne e)
      _ = _ := Finset.sum_comm
  unfold translationEnergy
  rw [hpair, hcost]
  simp_rw [Finset.sum_sub_distrib]

end FroehlichSpencer.BKT.Generic.SpinWave

end
