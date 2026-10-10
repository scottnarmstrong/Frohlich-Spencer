/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.PotentialKernel
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

/-!
# Finitely supported test functions on `ℤ²`

Test functions `g : ℤ² → ℝ` vanishing off a box `[-R, R]²` (`SupportedInBox`), the lattice
Laplacian `Δg(x) = ∑_{|e|=1} (g(x+e) - g(x))`, and the Dirichlet energy
`D(g) = ∑_{edges} (g_x - g_y)²` (a `finsum`). Proved:

* `finsum_mul_neg_laplacian`: summation by parts, `∑ g (-Δg) = D(g)`;
* `sum_laplacian_eq_zero`: `∑ Δg = 0`;
* `sum_potentialKernel_mul_laplacian`: the whole-plane Green identity
  `∑_y a(x - y) Δg(y) = g(x)`, i.e. `C(-Δg) = g` for FS81's free potential `C = -a`, from
  `Δa = δ₀` (`Coulomb/PotentialKernel.lean`).

All sums are finite: unit shifts are handled by `finsum` reindexing (`finsum_shift`) and
converted to sums over boxes containing the supports (`SupportedInBox.finsum_eq_sum`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Finset

/-- The box `[-R, R]² ⊂ ℤ²`. -/
def boxInternal (R : ℕ) : Finset (ℤ × ℤ) :=
  Icc (-(R : ℤ)) R ×ˢ Icc (-(R : ℤ)) R

theorem mem_box_iff {R : ℕ} {x : ℤ × ℤ} :
    x ∈ boxInternal R ↔ |x.1| ≤ R ∧ |x.2| ≤ R := by
  simp only [boxInternal, mem_product, mem_Icc, abs_le]

theorem box_mono {R S : ℕ} (h : R ≤ S) : boxInternal R ⊆ boxInternal S := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  have : (R : ℤ) ≤ S := by exact_mod_cast h
  exact ⟨hx.1.trans this, hx.2.trans this⟩

/-- `g` vanishes off the box `[-R, R]²`. -/
def SupportedInBox (R : ℕ) (g : ℤ × ℤ → ℝ) : Prop :=
  ∀ x, x ∉ boxInternal R → g x = 0

theorem SupportedInBox.mono {R S : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) (h : R ≤ S) :
    SupportedInBox S g := fun x hx => hg x fun hR => hx (box_mono h hR)

theorem SupportedInBox.shift {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) {e : ℤ × ℤ}
    (he : |e.1| ≤ 1 ∧ |e.2| ≤ 1) : SupportedInBox (R + 1) fun x => g (x + e) := by
  intro x hx
  apply hg
  intro hR
  apply hx
  rw [mem_box_iff] at hR ⊢
  simp only [Prod.fst_add, Prod.snd_add] at hR
  push_cast
  constructor
  · calc |x.1| = |(x.1 + e.1) - e.1| := by ring_nf
      _ ≤ |x.1 + e.1| + |e.1| := abs_sub _ _
      _ ≤ R + 1 := by linarith [hR.1, he.1]
  · calc |x.2| = |(x.2 + e.2) - e.2| := by ring_nf
      _ ≤ |x.2 + e.2| + |e.2| := abs_sub _ _
      _ ≤ R + 1 := by linarith [hR.2, he.2]

theorem SupportedInBox.finite_support {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    (Function.support g).Finite :=
  (boxInternal R).finite_toSet.subset fun x hx => by
    by_contra h
    exact hx (hg x h)

theorem SupportedInBox.mul_left {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g)
    (h : ℤ × ℤ → ℝ) : SupportedInBox R fun x => h x * g x := fun x hx => by
  simp [hg x hx]

theorem SupportedInBox.add {R : ℕ} {g h : ℤ × ℤ → ℝ} (hg : SupportedInBox R g)
    (hh : SupportedInBox R h) : SupportedInBox R fun x => g x + h x := fun x hx => by
  simp [hg x hx, hh x hx]

/-- The lattice Laplacian on `ℤ²`, `Δg(x) = ∑_{|e|=1} (g(x+e) - g(x))`. -/
def latticeLaplacianInternal (g : ℤ × ℤ → ℝ) (x : ℤ × ℤ) : ℝ :=
  g (x + (1, 0)) + g (x - (1, 0)) + g (x + (0, 1)) + g (x - (0, 1)) - 4 * g x

/-- The Dirichlet energy `∑_{edges} (g_x - g_y)²` on `ℤ²` (a finite sum for finitely supported
`g`). -/
def latticeDirichletInternal (g : ℤ × ℤ → ℝ) : ℝ :=
  ∑ᶠ x, ((g x - g (x + (1, 0))) ^ 2 + (g x - g (x + (0, 1))) ^ 2)

theorem finsum_shift (F : ℤ × ℤ → ℝ) (e : ℤ × ℤ) : ∑ᶠ x, F (x + e) = ∑ᶠ x, F x :=
  finsum_comp_equiv (Equiv.addRight e)

theorem unit_bounds_e1 : |((1, 0) : ℤ × ℤ).1| ≤ 1 ∧ |((1, 0) : ℤ × ℤ).2| ≤ 1 := by norm_num
theorem unit_bounds_e2 : |((0, 1) : ℤ × ℤ).1| ≤ 1 ∧ |((0, 1) : ℤ × ℤ).2| ≤ 1 := by norm_num
theorem unit_bounds_me1 : |(-(1, 0) : ℤ × ℤ).1| ≤ 1 ∧ |(-(1, 0) : ℤ × ℤ).2| ≤ 1 := by norm_num
theorem unit_bounds_me2 : |(-(0, 1) : ℤ × ℤ).1| ≤ 1 ∧ |(-(0, 1) : ℤ × ℤ).2| ≤ 1 := by norm_num

theorem SupportedInBox.laplacian {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    SupportedInBox (R + 1) (latticeLaplacianInternal g) := by
  intro x hx
  have h1 := hg.shift unit_bounds_e1 x hx
  have h2 := hg.shift unit_bounds_me1 x hx
  have h3 := hg.shift unit_bounds_e2 x hx
  have h4 := hg.shift unit_bounds_me2 x hx
  have h0 := (hg.mono (Nat.le_succ R)) x hx
  simp only [← sub_eq_add_neg] at h2 h4
  simp [latticeLaplacianInternal, h1, h2, h3, h4, h0]

/-- A finitely supported function can be summed over any finset containing its support. -/
theorem SupportedInBox.finsum_eq_sum {R : ℕ} {F : ℤ × ℤ → ℝ} (hF : SupportedInBox R F)
    {s : Finset (ℤ × ℤ)} (hs : boxInternal R ⊆ s) : ∑ᶠ x, F x = ∑ x ∈ s, F x :=
  finsum_eq_sum_of_support_subset F fun x hx => by
    by_contra h
    exact hx (hF x fun hR => h (hs hR))

/-- Telescoping a unit shift over a box containing the shifted support. -/
theorem sum_shift_sub_eq_zero {S : ℕ} {F : ℤ × ℤ → ℝ} (hF : SupportedInBox S F) {e : ℤ × ℤ}
    (he : |e.1| ≤ 1 ∧ |e.2| ≤ 1) {s : Finset (ℤ × ℤ)} (hs : boxInternal (S + 1) ⊆ s) :
    ∑ x ∈ s, (F (x + e) - F x) = 0 := by
  rw [Finset.sum_sub_distrib, ← (hF.shift he).finsum_eq_sum hs,
    ← (hF.mono (Nat.le_succ S)).finsum_eq_sum hs, finsum_shift, sub_self]

/-- Summation by parts on `ℤ²`: `∑ g (-Δ g) = ∑_{edges} (g_x - g_y)²`. -/
theorem finsum_mul_neg_laplacian {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    ∑ᶠ x, g x * -(latticeLaplacianInternal g x) = latticeDirichletInternal g := by
  set B := boxInternal (R + 2)
  have hRB : boxInternal R ⊆ B := box_mono (by omega)
  have hR1B : boxInternal (R + 1) ⊆ B := box_mono (by omega)
  have hL : SupportedInBox R fun x => g x * -(latticeLaplacianInternal g x) :=
    fun x hx => by simp [hg x hx]
  have hD : SupportedInBox (R + 1) fun x =>
      (g x - g (x + (1, 0))) ^ 2 + (g x - g (x + (0, 1))) ^ 2 := by
    intro x hx
    have h0 := (hg.mono (Nat.le_succ R)) x hx
    simp [h0, hg.shift unit_bounds_e1 x hx, hg.shift unit_bounds_e2 x hx]
  rw [hL.finsum_eq_sum hRB, latticeDirichletInternal, hD.finsum_eq_sum hR1B, ← sub_eq_zero,
    ← Finset.sum_sub_distrib]
  have hF1 : SupportedInBox R fun x => g (x - (1, 0)) * g x := hg.mul_left _
  have hF2 : SupportedInBox R fun x => g (x - (0, 1)) * g x := hg.mul_left _
  have hG : SupportedInBox R fun x => g x ^ 2 := fun x hx => by simp [hg x hx]
  have t1 := sum_shift_sub_eq_zero hF1 unit_bounds_e1 hR1B
  have t2 := sum_shift_sub_eq_zero hF2 unit_bounds_e2 hR1B
  have t3 := sum_shift_sub_eq_zero hG unit_bounds_e1 hR1B
  have t4 := sum_shift_sub_eq_zero hG unit_bounds_e2 hR1B
  have key : ∀ x, g x * -(latticeLaplacianInternal g x) -
      ((g x - g (x + (1, 0))) ^ 2 + (g x - g (x + (0, 1))) ^ 2) =
      ((g (x + (1, 0) - (1, 0)) * g (x + (1, 0)) - g (x - (1, 0)) * g x) +
        (g (x + (0, 1) - (0, 1)) * g (x + (0, 1)) - g (x - (0, 1)) * g x)) -
      ((g (x + (1, 0)) ^ 2 - g x ^ 2) + (g (x + (0, 1)) ^ 2 - g x ^ 2)) := by
    intro x
    simp only [add_sub_cancel_right, latticeLaplacianInternal]
    ring
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, t1, t2, t3, t4]
  ring

/-- `∑_x Δg(x) = 0` over any finset containing the support of `Δg`. -/
theorem sum_laplacian_eq_zero {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g)
    {s : Finset (ℤ × ℤ)} (hs : boxInternal (R + 1) ⊆ s) :
    ∑ x ∈ s, latticeLaplacianInternal g x = 0 := by
  rw [← hg.laplacian.finsum_eq_sum hs, hg.laplacian.finsum_eq_sum (box_mono (by omega :
    R + 1 ≤ R + 2))]
  have hR1 : boxInternal (R + 1) ⊆ boxInternal (R + 2) := box_mono (by omega)
  have t1 := sum_shift_sub_eq_zero hg unit_bounds_e1 hR1
  have t2 := sum_shift_sub_eq_zero hg unit_bounds_me1 hR1
  have t3 := sum_shift_sub_eq_zero hg unit_bounds_e2 hR1
  have t4 := sum_shift_sub_eq_zero hg unit_bounds_me2 hR1
  simp only [← sub_eq_add_neg] at t2 t4
  have key : ∀ x, latticeLaplacianInternal g x = (g (x + (1, 0)) - g x) + (g (x - (1, 0)) - g x) +
      (g (x + (0, 1)) - g x) + (g (x - (0, 1)) - g x) := by
    intro x; simp only [latticeLaplacianInternal]; ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, t1, t2, t3, t4]
  ring

/-- **The whole-plane Green identity**: `∑_y a(x - y) Δg(y) = g(x)` for finitely supported `g`
(`C = -a` inverts `-Δ`), from `Δa = δ₀`. -/
theorem sum_potentialKernel_mul_laplacian {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g)
    {s : Finset (ℤ × ℤ)} (hs : boxInternal (R + 1) ⊆ s) (x : ℤ × ℤ) :
    ∑ y ∈ s, potentialKernelInternal (x - y) * latticeLaplacianInternal g y = g x := by
  set B := boxInternal (R + 2)
  have hR1B : boxInternal (R + 1) ⊆ B := box_mono (by omega)
  rw [← (hg.laplacian.mul_left _).finsum_eq_sum hs, (hg.laplacian.mul_left _).finsum_eq_sum hR1B]
  have hshift : ∀ e : ℤ × ℤ, |e.1| ≤ 1 ∧ |e.2| ≤ 1 →
      ∑ y ∈ B, potentialKernelInternal (x - y) * g (y + e) =
        ∑ y ∈ B, potentialKernelInternal (x - y + e) * g y := by
    intro e he
    have hF : SupportedInBox R fun y => potentialKernelInternal (x - y + e) * g y :=
      hg.mul_left _
    have := sum_shift_sub_eq_zero hF he hR1B
    rw [Finset.sum_sub_distrib, sub_eq_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 2
    abel
  have expand : ∀ y, potentialKernelInternal (x - y) * latticeLaplacianInternal g y =
      potentialKernelInternal (x - y) * g (y + (1, 0)) +
        potentialKernelInternal (x - y) * g (y + -(1, 0)) +
        potentialKernelInternal (x - y) * g (y + (0, 1)) +
        potentialKernelInternal (x - y) * g (y + -(0, 1)) -
        4 * (potentialKernelInternal (x - y) * g y) := by
    intro y
    simp only [latticeLaplacianInternal, ← sub_eq_add_neg]
    ring
  simp_rw [expand]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hshift _ unit_bounds_e1, hshift _ unit_bounds_me1,
    hshift _ unit_bounds_e2, hshift _ unit_bounds_me2,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  have hΔa : ∀ y, potentialKernelInternal (x - y + (1, 0)) * g y +
      potentialKernelInternal (x - y + -(1, 0)) * g y +
      potentialKernelInternal (x - y + (0, 1)) * g y +
      potentialKernelInternal (x - y + -(0, 1)) * g y - 4 * (potentialKernelInternal (x - y) * g y) =
      (if x - y = 0 then 1 else 0) * g y := by
    intro y
    rw [← potentialKernel_laplacian (x - y)]
    simp only [← sub_eq_add_neg]
    ring
  simp_rw [hΔa]
  by_cases hx : x ∈ B
  · rw [Finset.sum_eq_single x (fun y _ hy => by simp [sub_eq_zero, Ne.symm hy])
      (fun h => absurd hx h)]
    simp
  · have hx0 : g x = 0 := (hg.mono (by omega : R ≤ R + 2)) x hx
    rw [hx0]
    refine Finset.sum_eq_zero fun y hy => ?_
    have : x ≠ y := fun h => hx (h ▸ hy)
    simp [sub_eq_zero, this]

end FroehlichSpencer.BKT.Coulomb
