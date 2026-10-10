/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Basic
public import FroehlichSpencer.BKT.Surface.DensityCenter
public import FroehlichSpencer.BKT.Surface.DensityDomain
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Integer routing of a neutral density through its domain (KP Claim 3.2,
-/

@[expose] public section

namespace FroehlichSpencer.BKT

namespace Multigraph

variable {V E : Type*} [Fintype V] (G : Multigraph V E)

/-- On a connected multigraph a nonzero neutral density has diameter at least one. -/
theorem one_le_densityDiameter_of_neutral (hG : G.toSimpleGraph.Connected) (ρ : V → ℤ)
    (hρ : ρ ≠ 0) (hsum : ∑ x, ρ x = 0) : 1 ≤ G.densityDiameter ρ := by
  have hpos : ∃ x, 0 < ρ x := by
    by_contra h
    have h' : ∀ x, ρ x ≤ 0 := fun x => not_lt.mp (fun hx => h ⟨x, hx⟩)
    exact hρ (funext fun x =>
      (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => h' i)).mp hsum x (Finset.mem_univ _))
  have hneg : ∃ y, ρ y < 0 := by
    by_contra h
    have h' : ∀ x, 0 ≤ ρ x := fun x => not_lt.mp (fun hx => h ⟨x, hx⟩)
    exact hρ (funext fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h' i)).mp hsum x (Finset.mem_univ _))
  obtain ⟨x, hx⟩ := hpos
  obtain ⟨y, hy⟩ := hneg
  have hne : x ≠ y := by
    rintro rfl
    exact absurd hx (not_lt.mpr hy.le)
  have h1 : 0 < G.toSimpleGraph.dist x y := hG.pos_dist_of_ne hne
  have h2 : G.toSimpleGraph.dist x y ≤ G.densityDiameter ρ := by
    unfold densityDiameter
    exact Finset.le_sup (f := fun p : V × V => G.toSimpleGraph.dist p.1 p.2) (b := (x, y))
      (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.ne'⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.ne⟩⟩)
  omega

/-- Support points lie within the diameter of an admissible center. -/
theorem dist_le_densityDiameter_of_center (ρ : V → ℤ) (j : V) (hj : G.IsDensityCenter ρ j)
    (x : V) (hx : ρ x ≠ 0) : G.toSimpleGraph.dist x j ≤ G.densityDiameter ρ := by
  unfold densityDiameter
  exact Finset.le_sup (f := fun p : V × V => G.toSimpleGraph.dist p.1 p.2) (b := (x, j))
    (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1⟩⟩)

omit [Fintype V] in
/-- Routing along a path: an integer combination of edge gradients with coefficients in
`{-1, 0, 1}`, supported on edges with both endpoints on the path, telescoping along it. -/
theorem exists_path_coeff [Fintype E] {a b : V} (w : G.toSimpleGraph.Walk a b) (hw : w.IsPath) :
    ∃ p : E → ℤ, (∀ e, |p e| ≤ 1) ∧
      (∀ e, p e ≠ 0 → G.src e ∈ w.support ∧ G.tgt e ∈ w.support) ∧
      ∀ σ : V → ℝ, σ b - σ a = ∑ e, (p e : ℝ) * G.grad σ e := by
  classical
  induction w with
  | nil =>
    refine ⟨fun _ => 0, by simp, by simp, ?_⟩
    intro σ
    simp
  | @cons a a' b h w ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hw
    obtain ⟨p, hp1, hp2, hp3⟩ := ih hw.1
    have hadj := h
    rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, hr⟩ := hadj
    have key : ∃ (e : E) (s : ℤ), (G.src e = a ∧ G.tgt e = a' ∨ G.src e = a' ∧ G.tgt e = a) ∧
        |s| = 1 ∧ ∀ σ : V → ℝ, σ a' - σ a = (s : ℝ) * G.grad σ e := by
      rcases hr with ⟨e, he | he⟩ | ⟨e, he | he⟩
      · exact ⟨e, -1, Or.inl he, by simp, fun σ => by
          simp [Multigraph.grad, he.1, he.2]⟩
      · exact ⟨e, 1, Or.inr ⟨he.1, he.2⟩, by simp, fun σ => by
          simp [Multigraph.grad, he.1, he.2]⟩
      · exact ⟨e, 1, Or.inr ⟨he.1, he.2⟩, by simp, fun σ => by
          simp [Multigraph.grad, he.1, he.2]⟩
      · exact ⟨e, -1, Or.inl he, by simp, fun σ => by
          simp [Multigraph.grad, he.1, he.2]⟩
    obtain ⟨e, s, hend, hs, hσ⟩ := key
    have hep : p e = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := hp2 e hne
      rcases hend with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact hw.2 (h3 ▸ h1)
      · exact hw.2 (h4 ▸ h2)
    have ha' : a' ∈ w.support := w.start_mem_support
    refine ⟨fun e' => p e' + if e' = e then s else 0, ?_, ?_, ?_⟩
    · intro e'
      by_cases hee : e' = e
      · subst hee; simpa [hep] using hs.le
      · simpa [hee] using hp1 e'
    · intro e' hne
      by_cases hee : e' = e
      · subst hee
        rcases hend with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · simp [h3, h4, ha']
        · simp [h3, h4, ha']
      · have : p e' ≠ 0 := by simpa [hee] using hne
        obtain ⟨h1, h2⟩ := hp2 e' this
        simp [h1, h2]
    · intro σ
      have := hp3 σ
      have hsum : ∑ e', ((p e' + if e' = e then s else 0 : ℤ) : ℝ) * G.grad σ e'
          = ∑ e', (p e' : ℝ) * G.grad σ e' + (s : ℝ) * G.grad σ e := by
        simp only [Int.cast_add, add_mul, Finset.sum_add_distrib]
        congr 1
        simp [apply_ite Int.cast, ite_mul]
      rw [hsum, ← this, ← hσ]
      ring

/-- KP Claim 3.2, routing step (: a neutral integer density is an integer combination
of edge gradients supported in its domain `D_j(ρ)`, with coefficients bounded by `‖ρ‖₁`. -/
theorem exists_integer_routing [Fintype E] (hG : G.toSimpleGraph.Connected) (ρ : V → ℤ)
    (hsum : ∑ x, ρ x = 0) (j : V) (hj : G.IsDensityCenter ρ j) :
    ∃ c : E → ℤ,
      (∀ e, c e ≠ 0 → G.src e ∈ G.densityDomain ρ j ∧ G.tgt e ∈ G.densityDomain ρ j) ∧
      (∀ e, |c e| ≤ ∑ x, |ρ x|) ∧
      ∀ σ : V → ℝ, ∑ x, σ x * (ρ x : ℝ) = ∑ e, (c e : ℝ) * G.grad σ e := by
  classical
  have hd : 1 ≤ G.densityDiameter ρ :=
    G.one_le_densityDiameter_of_neutral hG ρ (fun h => hj.1 (by simp [h])) hsum
  have hex : ∀ x, ∃ w : G.toSimpleGraph.Walk j x, w.IsPath ∧ w.length = G.toSimpleGraph.dist j x :=
    fun x => hG.exists_path_of_dist j x
  choose w hwp hwl using hex
  have hco := fun x => G.exists_path_coeff (w x) (hwp x)
  choose p hp1 hp2 hp3 using hco
  refine ⟨fun e => ∑ x, ρ x * p x e, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    have hρx : ρ x ≠ 0 := left_ne_zero_of_mul hx
    have hpx : p x e ≠ 0 := right_ne_zero_of_mul hx
    have hdx := G.dist_le_densityDiameter_of_center ρ j hj x hρx
    have hmem : ∀ u ∈ (w x).support, u ∈ G.densityDomain ρ j := by
      intro u hu
      have h1 : G.toSimpleGraph.dist j u ≤ (w x).length :=
        SimpleGraph.dist_le ((w x).takeUntil u hu) |>.trans
          ((w x).length_takeUntil_le_length hu)
      rw [hwl] at h1
      show G.toSimpleGraph.dist u j < 2 * G.densityDiameter ρ
      have c1 : G.toSimpleGraph.dist u j = G.toSimpleGraph.dist j u := SimpleGraph.dist_comm
      have c2 : G.toSimpleGraph.dist x j = G.toSimpleGraph.dist j x := SimpleGraph.dist_comm
      omega
    obtain ⟨h1, h2⟩ := hp2 x e hpx
    exact ⟨hmem _ h1, hmem _ h2⟩
  · intro e
    calc |∑ x, ρ x * p x e| ≤ ∑ x, |ρ x * p x e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |ρ x| := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hp1 x e)
  · intro σ
    have hsum' : ∑ x, (ρ x : ℝ) = 0 := by exact_mod_cast hsum
    calc ∑ x, σ x * (ρ x : ℝ) = ∑ x, (ρ x : ℝ) * (σ x - σ j) := by
          have : ∑ x, (ρ x : ℝ) * (σ x - σ j) = ∑ x, σ x * (ρ x : ℝ) - σ j * ∑ x, (ρ x : ℝ) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [this, hsum']; ring
      _ = ∑ x, (ρ x : ℝ) * ∑ e, (p x e : ℝ) * G.grad σ e := by
          exact Finset.sum_congr rfl fun x _ => by rw [← hp3 x σ]
      _ = ∑ e, ((∑ x, ρ x * p x e : ℤ) : ℝ) * G.grad σ e := by
          simp only [Finset.mul_sum, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun x _ => by ring

end Multigraph

end FroehlichSpencer.BKT

end
