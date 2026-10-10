/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Green
public import FroehlichSpencer.BKT.Potential.Variational
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Nash–Williams cut bounds for finite multigraph Green forms

The proof uses a potential constant on each level, with increments inversely
proportional to the cardinalities of the intervening cutsets.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

namespace Multigraph

universe u v

variable {V : Type u} {E : Type v}

/-- Edges crossing between levels `k` and `k + 1` of a level function. -/
def levelCut (G : Multigraph V E) [Fintype E] (s : V → ℕ) (k : ℕ) : Finset E :=
  Finset.univ.filter fun e =>
    (s (G.src e) = k ∧ s (G.tgt e) = k + 1) ∨
      (s (G.tgt e) = k ∧ s (G.src e) = k + 1)

/-- A cumulative level potential with increments `w k` below level `r`. -/
def levelPotential (s : V → ℕ) (r : ℕ) (w : ℕ → ℝ) (x : V) : ℝ :=
  ∑ k ∈ Finset.range (min (s x) r), w k

/-- The level indices crossed by an edge whose endpoint levels are `a` and `b`. -/
abbrev crossesLevel (a b k : ℕ) : Prop :=
  (a = k ∧ b = k + 1) ∨ (b = k ∧ a = k + 1)

/-- The real unit dipole source at two vertices. -/
def pointDipole {V : Type*} [DecidableEq V] (p q : V) : V → ℝ :=
  fun x => (if x = p then 1 else 0) - (if x = q then 1 else 0)

theorem sum_pointDipole_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (p q : V) : ∑ x, pointDipole p q x = 0 := by
  simp [pointDipole, Finset.sum_sub_distrib]

theorem pairing_levelPotential_pointDipole {V : Type*} [Fintype V]
    [DecidableEq V] (s : V → ℕ) (r : ℕ) (w : ℕ → ℝ) (p q : V) :
    pairing (levelPotential s r w) (pointDipole p q) =
      levelPotential s r w p - levelPotential s r w q := by
  classical
  unfold pairing pointDipole
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp

theorem levelPotential_succ (r n : ℕ) (w : ℕ → ℝ) :
    levelPotential (fun x : ℕ => x) r w (n + 1) =
      levelPotential (fun x : ℕ => x) r w n + if n < r then w n else 0 := by
  by_cases hn : n < r
  · have h₀ : min n r = n := Nat.min_eq_left (by omega)
    simp [levelPotential, h₀, hn, Finset.sum_range_succ]
  · have hr : r ≤ n := by omega
    have h₁ : min (n + 1) r = r := Nat.min_eq_right (by omega)
    have h₀ : min n r = r := Nat.min_eq_right hr
    simp [levelPotential, h₁, h₀, hn]

theorem sum_if_eq_range (r a : ℕ) (g : ℕ → ℝ) :
    (∑ k ∈ Finset.range r, if k = a then g k else 0) =
      if a < r then g a else 0 := by
  classical
  by_cases ha : a < r
  · have hmem : a ∈ Finset.range r := Finset.mem_range.mpr ha
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro k hk hka
      simp [hka]
    · intro hnot
      exact (hnot hmem).elim
  · simp only [ha]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hka : k ≠ a := by omega
    simp [hka]

theorem sum_crossesLevel_succ (r a : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ Finset.range r, if crossesLevel a (a + 1) k then w k ^ 2 else 0) =
      if a < r then w a ^ 2 else 0 := by
  classical
  have hcross : ∀ k, crossesLevel a (a + 1) k ↔ k = a := by
    intro k
    simp only [crossesLevel]
    omega
  simp_rw [hcross]
  exact sum_if_eq_range r a (fun k => w k ^ 2)

theorem levelPotential_edge_sq (r : ℕ) (w : ℕ → ℝ) {a b : ℕ}
    (hab : a ≤ b + 1) (hba : b ≤ a + 1) :
    (levelPotential (fun x : ℕ => x) r w a -
      levelPotential (fun x : ℕ => x) r w b) ^ 2 =
      ∑ k ∈ Finset.range r, if crossesLevel a b k then w k ^ 2 else 0 := by
  by_cases hab' : a ≤ b
  · by_cases heq : a = b
    · subst b
      have hnot : ∀ k, ¬ crossesLevel a a k := by
        intro k h
        rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
      have hpow : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [sub_self, hpow]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hc : crossesLevel a a k
      · exact (hnot k hc).elim
      · exact ite_eq_right hc
    · have hlt : a < b := lt_of_le_of_ne hab' heq
      have hsucc : b = a + 1 := by omega
      subst b
      have hp := levelPotential_succ r a w
      rw [hp, sum_crossesLevel_succ]
      by_cases ha : a < r <;> simp [ha]
  · have hlt : b < a := by omega
    have hsucc : a = b + 1 := by omega
    subst a
    have hp := levelPotential_succ r b w
    rw [hp]
    have hcross : ∀ k, crossesLevel (b + 1) b k ↔ k = b := by
      intro k
      constructor
      · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> omega
      · intro h
        subst k
        exact Or.inr ⟨rfl, rfl⟩
    simp_rw [hcross]
    rw [sum_if_eq_range r b (fun k => w k ^ 2)]
    by_cases hb : b < r <;> simp [hb]

theorem levelPotential_energy (G : Multigraph V E) [Fintype E]
    (s : V → ℕ) (r : ℕ) (w : ℕ → ℝ)
    (hstep : ∀ e, s (G.src e) ≤ s (G.tgt e) + 1 ∧
      s (G.tgt e) ≤ s (G.src e) + 1) :
    G.energy (levelPotential s r w) =
      ∑ k ∈ Finset.range r, (G.levelCut s k).card * w k ^ 2 := by
  classical
  rw [Multigraph.energy]
  calc
    (∑ e, G.grad (levelPotential s r w) e ^ 2) =
        ∑ e, ∑ k ∈ Finset.range r,
          if e ∈ G.levelCut s k then w k ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have heq := levelPotential_edge_sq r w (hstep e).1 (hstep e).2
      simpa [Multigraph.grad, Multigraph.levelPotential, Multigraph.levelCut,
        crossesLevel] using heq
    _ = ∑ k ∈ Finset.range r, ∑ e, if e ∈ G.levelCut s k then w k ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range r, (G.levelCut s k).card * w k ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ e, if e ∈ G.levelCut s k then w k ^ 2 else 0) =
            ∑ e ∈ Finset.univ with e ∈ G.levelCut s k, w k ^ 2 := by
          rw [Finset.sum_filter]
        _ = ∑ _e ∈ G.levelCut s k, w k ^ 2 := by simp
        _ = (G.levelCut s k).card * w k ^ 2 := by simp [nsmul_eq_mul]

/-- Every intermediate level separates the endpoints of a connected graph. -/
theorem levelCut_nonempty (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (s : V → ℕ)
    (hstep : ∀ e, s (G.src e) ≤ s (G.tgt e) + 1 ∧
      s (G.tgt e) ≤ s (G.src e) + 1)
    {p q : V} {r : ℕ} (hp : s p = 0) (hrq : r ≤ s q)
    {k : ℕ} (hk : k < r) : (G.levelCut s k).Nonempty := by
  classical
  by_contra hnonempty
  have hempty : G.levelCut s k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
  have hnotmem : ∀ e, e ∉ G.levelCut s k := by simp [hempty]
  let u : V → ℝ := fun x => if s x ≤ k then 1 else 0
  have hgrad : ∀ e, G.grad u e = 0 := by
    intro e
    by_cases hs : s (G.src e) ≤ k <;> by_cases ht : s (G.tgt e) ≤ k
    · simp [u, Multigraph.grad, hs, ht]
    · have hc : e ∈ G.levelCut s k := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Or.inl ⟨?_, ?_⟩⟩
        · have hstep' := (hstep e).2
          omega
        · have hstep' := (hstep e).2
          omega
      exact (hnotmem e hc).elim
    · have hc : e ∈ G.levelCut s k := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Or.inr ⟨?_, ?_⟩⟩
        · have hstep' := (hstep e).1
          omega
        · have hstep' := (hstep e).1
          omega
      exact (hnotmem e hc).elim
    · simp [u, Multigraph.grad, hs, ht]
  have hE : G.energy u = 0 := by
    rw [Multigraph.energy]
    simp [hgrad]
  obtain ⟨c, hc⟩ := (G.energy_eq_zero_iff_exists_const hG u).mp hE
  have hpu : u p = 1 := by simp [u, hp]
  have hqu : u q = 0 := by
    have hkq : k < s q := lt_of_lt_of_le hk hrq
    simp [u, not_le.mpr hkq]
  have hpc : c = 1 := by simpa [hpu] using (congrFun hc p).symm
  have hqc : c = 0 := by simpa [hqu] using (congrFun hc q).symm
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (hpc.symm.trans hqc)

/-- Nash–Williams' lower bound for a finite graph Green form. The level
potential uses reciprocal cutset sizes, so its Dirichlet energy is exactly the
sum of those reciprocals. -/
theorem pairing_pointDipole_ge_inv_levelCut_sum (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (s : V → ℕ)
    (hstep : ∀ e, s (G.src e) ≤ s (G.tgt e) + 1 ∧
      s (G.tgt e) ≤ s (G.src e) + 1)
    {p q : V} {r : ℕ} (hp : s p = 0) (hrq : r ≤ s q) :
    ∑ k ∈ Finset.range r, 1 / ((G.levelCut s k).card : ℝ) ≤
      pairing (pointDipole p q) (-G.greenOp hG (pointDipole p q)) := by
  classical
  let w : ℕ → ℝ := fun k => 1 / ((G.levelCut s k).card : ℝ)
  let u : V → ℝ := levelPotential s r w
  let S : ℝ := ∑ k ∈ Finset.range r, w k
  let Q : ℝ := pairing (pointDipole p q) (-G.greenOp hG (pointDipole p q))
  have hzero : ∑ x, pointDipole p q x = 0 := sum_pointDipole_eq_zero p q
  by_cases hr : r = 0
  · subst r
    simp only [Finset.range_zero, Finset.sum_empty]
    exact G.pairing_greenOp_nonneg hG (pointDipole p q) hzero
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hcardpos : ∀ k ∈ Finset.range r, 0 < ((G.levelCut s k).card : ℝ) := by
      intro k hk
      have hkn : k < r := Finset.mem_range.mp hk
      have hn : 0 < (G.levelCut s k).card :=
        Finset.card_pos.mpr (G.levelCut_nonempty hG s hstep hp hrq hkn)
      exact_mod_cast hn
    have hwpos : ∀ k ∈ Finset.range r, 0 < w k := by
      intro k hk
      dsimp [w]
      exact one_div_pos.mpr (hcardpos k hk)
    have hSpos : 0 < S := by
      dsimp [S]
      exact Finset.sum_pos hwpos ⟨0, Finset.mem_range.mpr hrpos⟩
    have henergy : G.energy u = S := by
      rw [show u = levelPotential s r w from rfl, G.levelPotential_energy s r w hstep]
      dsimp [S]
      apply Finset.sum_congr rfl
      intro k hk
      have hden : ((G.levelCut s k).card : ℝ) ≠ 0 := ne_of_gt (hcardpos k hk)
      dsimp [w]
      field_simp [hden]
    have hup : u p = 0 := by
      simp [u, levelPotential, hp]
    have huq : u q = S := by
      have hmin : min (s q) r = r := Nat.min_eq_right hrq
      simp [u, S, levelPotential, hmin]
    have hpair : pairing u (pointDipole p q) = -S := by
      calc
        pairing u (pointDipole p q) = u p - u q := by
          simpa [u] using pairing_levelPotential_pointDipole s r w p q
        _ = -S := by rw [hup, huq]; ring
    have hdir := G.dirichlet_principle hG (pointDipole p q) hzero u
    have hmul : S * S ≤ Q * S := by
      rw [hpair, henergy] at hdir
      nlinarith [hdir]
    have hQS : S ≤ Q := by
      have hdiv : (S * S) / S ≤ Q := (div_le_iff₀ hSpos).2 hmul
      have hcancel : (S * S) / S = S := by
        field_simp [ne_of_gt hSpos]
      rw [hcancel] at hdiv
      exact hdiv
    simpa [w, Q, S] using hQS

/-- A linear upper bound on cutset sizes gives a logarithmic lower bound on
the Green dipole form. -/
theorem pairing_pointDipole_ge_log_of_levelCut_bound (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (s : V → ℕ)
    (hstep : ∀ e, s (G.src e) ≤ s (G.tgt e) + 1 ∧
      s (G.tgt e) ≤ s (G.src e) + 1)
    {p q : V} {r : ℕ} (hp : s p = 0) (hrq : r ≤ s q)
    (A : ℝ) (hA : 0 < A)
    (hcount : ∀ k ∈ Finset.range r,
      ((G.levelCut s k).card : ℝ) ≤ A * (↑(k + 1) : ℝ)) :
    (1 / A) * Real.log (↑(r + 1) : ℝ) ≤
      pairing (pointDipole p q) (-G.greenOp hG (pointDipole p q)) := by
  classical
  have hNW := G.pairing_pointDipole_ge_inv_levelCut_sum hG s hstep hp hrq
  have hsum :
      (1 / A) * (∑ k ∈ Finset.range r, 1 / (↑(k + 1) : ℝ)) ≤
        ∑ k ∈ Finset.range r, 1 / ((G.levelCut s k).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k < r := Finset.mem_range.mp hk
    have hN : 0 < ((G.levelCut s k).card : ℝ) := by
      have hpos : 0 < (G.levelCut s k).card :=
        Finset.card_pos.mpr (G.levelCut_nonempty hG s hstep hp hrq hkn)
      exact_mod_cast hpos
    have hK : 0 < (↑(k + 1) : ℝ) := by positivity
    calc
      (1 / A) * (1 / (↑(k + 1) : ℝ)) =
          1 / (A * (↑(k + 1) : ℝ)) := by
        field_simp [ne_of_gt hA, ne_of_gt hK]
      _ ≤ 1 / ((G.levelCut s k).card : ℝ) :=
        one_div_le_one_div_of_le hN (hcount k hk)
  have hharm :
      (∑ k ∈ Finset.range r, 1 / (↑(k + 1) : ℝ)) = (↑(harmonic r) : ℝ) := by
    simp [harmonic, div_eq_mul_inv]
  have hlogharm := log_add_one_le_harmonic r
  have hlog : (1 / A) * Real.log (↑(r + 1) : ℝ) ≤
      (1 / A) * (↑(harmonic r) : ℝ) :=
    mul_le_mul_of_nonneg_left hlogharm (by positivity)
  calc
    (1 / A) * Real.log (↑(r + 1) : ℝ) ≤
        (1 / A) * (↑(harmonic r) : ℝ) := hlog
    _ = (1 / A) * (∑ k ∈ Finset.range r, 1 / (↑(k + 1) : ℝ)) := by rw [hharm]
    _ ≤ ∑ k ∈ Finset.range r, 1 / ((G.levelCut s k).card : ℝ) := hsum
    _ ≤ pairing (pointDipole p q) (-G.greenOp hG (pointDipole p q)) := hNW

end Multigraph

end FroehlichSpencer.BKT

end
