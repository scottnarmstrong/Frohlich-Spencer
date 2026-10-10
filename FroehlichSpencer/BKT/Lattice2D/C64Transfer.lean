/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.C64Reflection
public import FroehlichSpencer.BKT.Reduction.T16ImpliesT13
public import FroehlichSpencer.BKT.ExpMoment.ReducedPhase
import Mathlib.Algebra.BigOperators.Fin

/-! # Free-to-periodic Green transfer for KP Claim 6.4 -/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open Multigraph

namespace FroehlichSpencer.BKT.Lattice2D

noncomputable section

/-- The sum over a folded cyclic coordinate counts each free coordinate twice. -/
theorem torusC64FoldIndex_sum (L : ℕ) [NeZero (2 * L)] (H : Fin L → ℝ) :
    (∑ a : ZMod (2 * L), H (torusC64FoldIndex L a)) =
      2 * ∑ i : Fin L, H i := by
  let h : L + L = 2 * L := by omega
  let e : Fin (L + L) ≃ ZMod (2 * L) :=
    { toFun := fun i => (i.val : ZMod (2 * L))
      invFun := fun a => ⟨a.val, by have := a.val_lt; omega⟩
      left_inv := by
        intro i
        apply Fin.ext
        dsimp
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
      right_inv := by
        intro a
        apply ZMod.val_injective (2 * L)
        dsimp
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt a.val_lt }
  rw [← Equiv.sum_comp e (fun a => H (torusC64FoldIndex L a))]
  rw [Fin.sum_univ_add]
  have hlow : ∑ i : Fin L,
      H (torusC64FoldIndex L (e (Fin.castAdd L i))) = ∑ i : Fin L, H i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hv : (e (Fin.castAdd L i)).val = i.val := by
      dsimp [e]
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    have hlt : (e (Fin.castAdd L i)).val < L := by simp [hv]
    rw [torusC64FoldIndex_of_lt L (e (Fin.castAdd L i)) hlt]
    congr 1
    apply Fin.ext
    exact hv
  have hhigh : ∑ i : Fin L,
      H (torusC64FoldIndex L (e (Fin.natAdd L i))) = ∑ i : Fin L, H i := by
    calc
      _ = ∑ i : Fin L, H (Fin.rev i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hv : (e (Fin.natAdd L i)).val = L + i.val := by
          dsimp [e]
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
        have hge : L ≤ (e (Fin.natAdd L i)).val := by omega
        rw [torusC64FoldIndex_of_ge L (e (Fin.natAdd L i)) hge]
        congr 1
        apply Fin.ext
        simp only [Fin.val_rev]
        omega
      _ = ∑ i : Fin L, H i := by
        exact Equiv.sum_comp
          ({ toFun := fun i : Fin L => Fin.rev i, invFun := fun i => Fin.rev i,
             left_inv := Fin.rev_rev, right_inv := Fin.rev_rev } : Fin L ≃ Fin L) H
  rw [hlow, hhigh]
  ring

/-- Folding both coordinates duplicates sums four times. In particular,
`T_fp` preserves zero-sum functions. -/
theorem torusC64Reflection_sum (L : ℕ) [NeZero (2 * L)]
    (f : SquareFreeVertex L → ℝ) :
    (∑ z : TorusVertex (2 * L), torusC64Reflection L f z) =
      4 * ∑ v : SquareFreeVertex L, f v := by
  rw [Fintype.sum_prod_type]
  simp only [torusC64Reflection]
  calc
    _ = ∑ x : ZMod (2 * L),
        2 * ∑ j : Fin L, f (torusC64FoldIndex L x, j) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact torusC64FoldIndex_sum L (fun j => f (torusC64FoldIndex L x, j))
    _ = 2 * ∑ x : ZMod (2 * L), ∑ j : Fin L,
        f (torusC64FoldIndex L x, j) := by rw [Finset.mul_sum]
    _ = 2 * (2 * ∑ i : Fin L, ∑ j : Fin L, f (i, j)) := by
          congr 1
          exact torusC64FoldIndex_sum L (fun i => ∑ j : Fin L, f (i, j))
    _ = 4 * ∑ v : SquareFreeVertex L, f v := by
          rw [Fintype.sum_prod_type]
          ring

/-- The canonical representatives in the free square are fixed by folding. -/
@[simp] theorem torusC64FoldIndex_cast_fin (L : ℕ) [NeZero (2 * L)]
    (i : Fin L) : torusC64FoldIndex L (i.val : ZMod (2 * L)) = i := by
  apply Fin.ext
  rw [torusC64FoldIndex_val]
  have hv : ((i.val : ZMod (2 * L)).val) = i.val := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
  rw [hv]
  simp [i.isLt]

/-- The reflected extension solves the free Laplace equation when restricted
to the free quadrant. -/
theorem torusC64Reflection_laplacian_on_free (L : ℕ) [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : SquareFreeVertex L → ℝ)
    (i j : Fin L) :
    (torusGraph (2 * L) hside).laplacian (torusC64Reflection L f)
        ((i.val : ZMod (2 * L)), (j.val : ZMod (2 * L))) =
      (squareFreeGraph L).laplacian f (i, j) := by
  rw [torusLaplacian_neighbor_formula_real, squareFree_laplacian_neighbor_formula]
  simp only [torusC64Reflection, torusC64FoldIndex_cast_fin]
  have hplus (k : Fin L) :
      torusC64FoldIndex L ((k.val : ZMod (2 * L)) + 1) =
        if hk : k.val + 1 < L then ⟨k.val + 1, hk⟩ else k := by
    by_cases hk : k.val + 1 < L
    · apply Fin.ext
      rw [torusC64FoldIndex_add_one]
      have hcast : ((k.val : ZMod (2 * L)).val) = k.val := by
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
      rw [hcast]
      simp [hk]
    · have hlast : k.val + 1 = L := by have := k.isLt; omega
      apply Fin.ext
      rw [torusC64FoldIndex_add_one]
      have hcast : ((k.val : ZMod (2 * L)).val) = k.val := by
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
      rw [hcast]
      have hbelow : k.val + 1 < 2 * L := by omega
      simp [hk, hbelow]
      omega
  have hminus (k : Fin L) :
      torusC64FoldIndex L ((k.val : ZMod (2 * L)) - 1) =
        if hk : 0 < k.val then ⟨k.val - 1, by have := k.isLt; omega⟩ else k := by
    by_cases hk : 0 < k.val
    · simp only [dite_eq_left hk]
      apply Fin.ext
      rw [torusC64FoldIndex_sub_one]
      have hcast : ((k.val : ZMod (2 * L))).val = k.val := by
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
      rw [hcast]
      have hne : k.val ≠ 0 := by omega
      simp [hne, Nat.le_of_lt k.isLt]
    · have hk0 : k.val = 0 := Nat.eq_zero_of_not_pos hk
      simp only [dite_eq_right hk]
      apply Fin.ext
      have hcast0 : (k.val : ZMod (2 * L)) = 0 := by simp [hk0]
      rw [hcast0]
      have hfold : (torusC64FoldIndex L ((0 : ZMod (2 * L)) - 1)).val = 0 := by
        simpa using (torusC64FoldIndex_sub_one L (0 : ZMod (2 * L)))
      simpa [hk0] using hfold
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    add_zero, sub_zero]
  rw [hplus i, hminus i, hplus j, hminus j]
  by_cases hi1 : i.val + 1 < L <;> by_cases hi0 : 0 < i.val <;>
    by_cases hj1 : j.val + 1 < L <;> by_cases hj0 : 0 < j.val
  all_goals (simp [hi1, hi0, hj1, hj0]; ring)

theorem torusC64FoldIndex_reflect (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    torusC64FoldIndex L (-a - 1) = torusC64FoldIndex L a := by
  apply Fin.ext
  rw [torusC64FoldIndex_val, torusC64FoldIndex_val]
  have hav := a.val_lt
  have hneg : (-a - 1).val = 2 * L - 1 - a.val := by
    rw [show -a - 1 = -(a + 1) by ring, ZMod.neg_val,
      torusC64_add_one_val]
    by_cases h : a.val + 1 < 2 * L
    · have hne : a + 1 ≠ 0 := by
        intro hz
        have hv := congrArg ZMod.val hz
        rw [torusC64_add_one_val] at hv
        simp [h] at hv
      simp [h, hne]
      omega
    · have heq : a.val + 1 = 2 * L := by omega
      have hz : a + 1 = 0 := by
        apply ZMod.val_injective (2 * L)
        rw [torusC64_add_one_val, heq]
        simp
      simp [hz, heq]
  rw [hneg]
  by_cases h : a.val < L
  · have hnot : ¬2 * L - 1 - a.val < L := by omega
    simp only [ite_eq_left h, ite_eq_right hnot]
    have ha : a.val ≤ 2 * L - 1 := by omega
    rw [Nat.sub_sub_self ha]
  · have hlt : 2 * L - 1 - a.val < L := by omega
    simp only [ite_eq_left hlt, ite_eq_right h]

/-- Reflection of the first torus coordinate across the edge between `L-1`
and `L`. -/
def torusC64ReflectFirst (L : ℕ) (z : TorusVertex (2 * L)) : TorusVertex (2 * L) :=
  (-z.1 - 1, z.2)

/-- Reflection of the second torus coordinate across the edge between `L-1`
and `L`. -/
def torusC64ReflectSecond (L : ℕ) (z : TorusVertex (2 * L)) : TorusVertex (2 * L) :=
  (z.1, -z.2 - 1)

theorem torusC64ReflectFirst_involutive (L : ℕ) (z : TorusVertex (2 * L)) :
    torusC64ReflectFirst L (torusC64ReflectFirst L z) = z := by
  rcases z with ⟨x, y⟩
  simp only [torusC64ReflectFirst]
  congr 1; ring

theorem torusC64ReflectSecond_involutive (L : ℕ) (z : TorusVertex (2 * L)) :
    torusC64ReflectSecond L (torusC64ReflectSecond L z) = z := by
  rcases z with ⟨x, y⟩
  change (x, -(-y - 1) - 1) = (x, y)
  apply Prod.ext
  · rfl
  · ring

noncomputable def torusC64ReflectFirstEquiv (L : ℕ) :
    TorusVertex (2 * L) ≃ TorusVertex (2 * L) :=
  { toFun := torusC64ReflectFirst L
    invFun := torusC64ReflectFirst L
    left_inv := torusC64ReflectFirst_involutive L
    right_inv := torusC64ReflectFirst_involutive L }

noncomputable def torusC64ReflectSecondEquiv (L : ℕ) :
    TorusVertex (2 * L) ≃ TorusVertex (2 * L) :=
  { toFun := torusC64ReflectSecond L
    invFun := torusC64ReflectSecond L
    left_inv := torusC64ReflectSecond_involutive L
    right_inv := torusC64ReflectSecond_involutive L }

@[simp] theorem torusC64Reflection_invariant_first (L : ℕ) [NeZero (2 * L)]
    (f : SquareFreeVertex L → ℝ) (z : TorusVertex (2 * L)) :
    torusC64Reflection L f (torusC64ReflectFirst L z) = torusC64Reflection L f z := by
  rcases z with ⟨x, y⟩
  simp only [torusC64Reflection, torusC64ReflectFirst]
  rw [torusC64FoldIndex_reflect]

@[simp] theorem torusC64Reflection_invariant_second (L : ℕ) [NeZero (2 * L)]
    (f : SquareFreeVertex L → ℝ) (z : TorusVertex (2 * L)) :
    torusC64Reflection L f (torusC64ReflectSecond L z) = torusC64Reflection L f z := by
  rcases z with ⟨x, y⟩
  simp only [torusC64Reflection, torusC64ReflectSecond]
  rw [torusC64FoldIndex_reflect]

theorem torusC64ReflectFirst_laplacian_comp {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) :
    (torusGraph (2 * L) hside).laplacian (fun w => f (torusC64ReflectFirst L w)) z =
      (torusGraph (2 * L) hside).laplacian f (torusC64ReflectFirst L z) := by
  rw [torusLaplacian_neighbor_formula_real hside _ z,
    torusLaplacian_neighbor_formula_real hside f (torusC64ReflectFirst L z)]
  have hp : torusC64ReflectFirst L (z + (1, 0)) =
      torusC64ReflectFirst L z - (1, 0) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectFirst, Prod.fst_add, Prod.fst_sub]
      abel
    · simp only [torusC64ReflectFirst, Prod.snd_add, Prod.snd_sub]
      abel
  have hm : torusC64ReflectFirst L (z - (1, 0)) =
      torusC64ReflectFirst L z + (1, 0) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectFirst, Prod.fst_sub, Prod.fst_add]
      abel
    · simp only [torusC64ReflectFirst, Prod.snd_sub, Prod.snd_add]
      abel
  have hpy : torusC64ReflectFirst L (z + (0, 1)) =
      torusC64ReflectFirst L z + (0, 1) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectFirst, Prod.fst_add]
      abel
    · simp only [torusC64ReflectFirst, Prod.snd_add]
  have hmy : torusC64ReflectFirst L (z - (0, 1)) =
      torusC64ReflectFirst L z - (0, 1) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectFirst, Prod.fst_sub]
      abel
    · simp only [torusC64ReflectFirst, Prod.snd_sub]
  rw [hp, hm, hpy, hmy]
  ring

theorem torusC64ReflectSecond_laplacian_comp {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) :
    (torusGraph (2 * L) hside).laplacian (fun w => f (torusC64ReflectSecond L w)) z =
      (torusGraph (2 * L) hside).laplacian f (torusC64ReflectSecond L z) := by
  rw [torusLaplacian_neighbor_formula_real hside _ z,
    torusLaplacian_neighbor_formula_real hside f (torusC64ReflectSecond L z)]
  have hp : torusC64ReflectSecond L (z + (1, 0)) =
      torusC64ReflectSecond L z + (1, 0) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectSecond, Prod.fst_add]
    · simp only [torusC64ReflectSecond, Prod.snd_add]
      abel
  have hm : torusC64ReflectSecond L (z - (1, 0)) =
      torusC64ReflectSecond L z - (1, 0) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectSecond, Prod.fst_sub]
    · simp only [torusC64ReflectSecond, Prod.snd_sub]
      abel
  have hpy : torusC64ReflectSecond L (z + (0, 1)) =
      torusC64ReflectSecond L z - (0, 1) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectSecond, Prod.fst_add, Prod.fst_sub]
      abel
    · simp only [torusC64ReflectSecond, Prod.snd_add, Prod.snd_sub]
      abel
  have hmy : torusC64ReflectSecond L (z - (0, 1)) =
      torusC64ReflectSecond L z + (0, 1) := by
    rcases z with ⟨x, y⟩
    ext
    · simp only [torusC64ReflectSecond, Prod.fst_sub, Prod.fst_add]
      abel
    · simp only [torusC64ReflectSecond, Prod.snd_sub, Prod.snd_add]
      abel
  rw [hp, hm, hpy, hmy]
  ring

/-- The Green potential inherits any involutive symmetry commuting with the
torus Laplacian, by uniqueness of its zero-sum inverse. -/
theorem torusGreenOp_invariant_under_equiv {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hG : (torusGraph (2 * L) hside).Connected)
    (F : TorusVertex (2 * L) → ℝ) (hF : ∑ z, F z = 0)
    (e : TorusVertex (2 * L) ≃ TorusVertex (2 * L))
    (hFsymm : ∀ z, F (e z) = F z)
    (hcomm : ∀ (g : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)),
      (torusGraph (2 * L) hside).laplacian
      (fun w => g (e w)) z = (torusGraph (2 * L) hside).laplacian g (e z)) :
    ∀ z, (torusGraph (2 * L) hside).greenOp hG F (e z) =
      (torusGraph (2 * L) hside).greenOp hG F z := by
  let G := torusGraph (2 * L) hside
  let g := G.greenOp hG F
  have hgLap : G.laplacian g = F := G.laplacian_greenOp_of_sum_eq_zero hG F hF
  have hgsum : ∑ z, g z = 0 := G.greenOp_sum_eq_zero hG F
  let gR : TorusVertex (2 * L) → ℝ := fun z => g (e z)
  have hgRsum : ∑ z, gR z = 0 := by
    dsimp [gR]
    rw [Equiv.sum_comp e]
    exact hgsum
  have hgRlap : G.laplacian gR = F := by
    funext z
    rw [hcomm, hgLap, hFsymm]
  have hright := G.greenOp_laplacian_of_sum_eq_zero hG gR hgRsum
  rw [hgRlap] at hright
  intro z
  have hz := congrFun hright z
  simpa [g, gR] using hz.symm

theorem torusGreenOp_reflection_first {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hG : (torusGraph (2 * L) hside).Connected)
    (f : SquareFreeVertex L → ℝ) (hf : ∑ v, f v = 0) :
    ∀ z, (torusGraph (2 * L) hside).greenOp hG (torusC64Reflection L f)
        (torusC64ReflectFirst L z) =
      (torusGraph (2 * L) hside).greenOp hG (torusC64Reflection L f) z := by
  apply torusGreenOp_invariant_under_equiv hside hG (torusC64Reflection L f)
    (by rw [torusC64Reflection_sum, hf]; ring) (torusC64ReflectFirstEquiv L)
  · intro z
    exact torusC64Reflection_invariant_first L f z
  · intro g z
    exact torusC64ReflectFirst_laplacian_comp hside g z

theorem torusGreenOp_reflection_second {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hG : (torusGraph (2 * L) hside).Connected)
    (f : SquareFreeVertex L → ℝ) (hf : ∑ v, f v = 0) :
    ∀ z, (torusGraph (2 * L) hside).greenOp hG (torusC64Reflection L f)
        (torusC64ReflectSecond L z) =
      (torusGraph (2 * L) hside).greenOp hG (torusC64Reflection L f) z := by
  apply torusGreenOp_invariant_under_equiv hside hG (torusC64Reflection L f)
    (by rw [torusC64Reflection_sum, hf]; ring) (torusC64ReflectSecondEquiv L)
  · intro z
    exact torusC64Reflection_invariant_second L f z
  · intro g z
    exact torusC64ReflectSecond_laplacian_comp hside g z

/-- The canonical free-square vertex inside the periodic square. -/
def torusC64FreeEmbed {L : ℕ} (v : SquareFreeVertex L) : TorusVertex (2 * L) :=
  ((v.1.val : ZMod (2 * L)), (v.2.val : ZMod (2 * L)))

/-- Restrict a periodic field to the free quadrant. -/
def torusC64FreeRestrict {L : ℕ} (g : TorusVertex (2 * L) → ℝ) :
    SquareFreeVertex L → ℝ := fun v => g (torusC64FreeEmbed v)

private theorem torusC64_reflectFirst_upper_boundary {L : ℕ} [NeZero (2 * L)]
    (i j : Fin L) (hi : i.val + 1 = L) :
    torusC64ReflectFirst L
      (((i.val : ZMod (2 * L)) + 1), (j.val : ZMod (2 * L))) =
      torusC64FreeEmbed (i, j) := by
  apply Prod.ext
  · change -((i.val : ZMod (2 * L)) + 1) - 1 = (i.val : ZMod (2 * L))
    have hcast : (i.val : ZMod (2 * L)) + 1 = (L : ZMod (2 * L)) := by
      simpa using congrArg (fun k : ℕ => (k : ZMod (2 * L))) hi
    rw [hcast]
    have hL : (L : ZMod (2 * L)) + (L : ZMod (2 * L)) = 0 := by
      calc
        (L : ZMod (2 * L)) + L = ((2 * L : ℕ) : ZMod (2 * L)) := by norm_num [two_mul]
        _ = 0 := ZMod.natCast_self _
    calc
      -(L : ZMod (2 * L)) - 1 = (L : ZMod (2 * L)) - 1 := by linear_combination -hL
      _ = (i.val : ZMod (2 * L)) := by linear_combination -hcast
  · rfl

private theorem torusC64_reflectFirst_lower_boundary {L : ℕ} [NeZero (2 * L)]
    (i j : Fin L) (hi : i.val = 0) :
    torusC64ReflectFirst L
      (((i.val : ZMod (2 * L)) - 1), (j.val : ZMod (2 * L))) =
      torusC64FreeEmbed (i, j) := by
  apply Prod.ext
  · change -((i.val : ZMod (2 * L)) - 1) - 1 = (i.val : ZMod (2 * L))
    have hi0 : (i.val : ZMod (2 * L)) = 0 := by
      simpa using congrArg (fun k : ℕ => (k : ZMod (2 * L))) hi
    rw [hi0]
    simp
  · rfl

private theorem torusC64_reflectSecond_upper_boundary {L : ℕ} [NeZero (2 * L)]
    (i j : Fin L) (hj : j.val + 1 = L) :
    torusC64ReflectSecond L
      ((i.val : ZMod (2 * L)), ((j.val : ZMod (2 * L)) + 1)) =
      torusC64FreeEmbed (i, j) := by
  apply Prod.ext
  · rfl
  · change -((j.val : ZMod (2 * L)) + 1) - 1 = (j.val : ZMod (2 * L))
    have hcast : (j.val : ZMod (2 * L)) + 1 = (L : ZMod (2 * L)) := by
      simpa using congrArg (fun k : ℕ => (k : ZMod (2 * L))) hj
    rw [hcast]
    have hL : (L : ZMod (2 * L)) + (L : ZMod (2 * L)) = 0 := by
      calc
        (L : ZMod (2 * L)) + L = ((2 * L : ℕ) : ZMod (2 * L)) := by norm_num [two_mul]
        _ = 0 := ZMod.natCast_self _
    calc
      -(L : ZMod (2 * L)) - 1 = (L : ZMod (2 * L)) - 1 := by linear_combination -hL
      _ = (j.val : ZMod (2 * L)) := by linear_combination -hcast

private theorem torusC64_reflectSecond_lower_boundary {L : ℕ} [NeZero (2 * L)]
    (i j : Fin L) (hj : j.val = 0) :
    torusC64ReflectSecond L
      ((i.val : ZMod (2 * L)), ((j.val : ZMod (2 * L)) - 1)) =
      torusC64FreeEmbed (i, j) := by
  apply Prod.ext
  · rfl
  · change -((j.val : ZMod (2 * L)) - 1) - 1 = (j.val : ZMod (2 * L))
    have hj0 : (j.val : ZMod (2 * L)) = 0 := by
      simpa using congrArg (fun k : ℕ => (k : ZMod (2 * L))) hj
    rw [hj0]
    simp

/-- For a field invariant under the two edge reflections, restriction to the
free quadrant intertwines the periodic and free graph Laplacians. At a free
boundary the reflected exterior neighbor has the boundary value. -/
theorem torusC64_laplacian_restrict_symmetric {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (g : TorusVertex (2 * L) → ℝ)
    (hfirst : ∀ z, g (torusC64ReflectFirst L z) = g z)
    (hsecond : ∀ z, g (torusC64ReflectSecond L z) = g z)
    (i j : Fin L) :
    (torusGraph (2 * L) hside).laplacian g (torusC64FreeEmbed (i, j)) =
      (squareFreeGraph L).laplacian (torusC64FreeRestrict g) (i, j) := by
  rw [torusLaplacian_neighbor_formula_real hside,
    squareFree_laplacian_neighbor_formula]
  have hxp : g (torusC64FreeEmbed (i, j) + (1, 0)) =
      if hi : i.val + 1 < L then
        torusC64FreeRestrict g (⟨i.val + 1, hi⟩, j) else
        torusC64FreeRestrict g (i, j) := by
    by_cases hi : i.val + 1 < L
    · simp only [dite_eq_left hi]
      change g (torusC64FreeEmbed (i, j) + (1, 0)) =
        g (torusC64FreeEmbed (⟨i.val + 1, hi⟩, j))
      congr 1
      apply Prod.ext
      · change (i.val : ZMod (2 * L)) + 1 = ((i.val + 1 : ℕ) : ZMod (2 * L))
        simp
      · simp [torusC64FreeEmbed]
    · have heq : i.val + 1 = L := by have := i.isLt; omega
      simp only [dite_eq_right (by omega : ¬ i.val + 1 < L)]
      have hz : torusC64FreeEmbed (i, j) + (1, 0) =
          (((i.val : ZMod (2 * L)) + 1), (j.val : ZMod (2 * L))) := by
        ext <;> simp [torusC64FreeEmbed]
      rw [hz]
      exact (hfirst (((i.val : ZMod (2 * L)) + 1), (j.val : ZMod (2 * L)))).symm.trans
        (congrArg g (torusC64_reflectFirst_upper_boundary i j heq))
  have hxm : g (torusC64FreeEmbed (i, j) - (1, 0)) =
      if hi : 0 < i.val then
        torusC64FreeRestrict g (⟨i.val - 1, by have := i.isLt; omega⟩, j) else
        torusC64FreeRestrict g (i, j) := by
    by_cases hi : 0 < i.val
    · simp only [dite_eq_left hi]
      change g (torusC64FreeEmbed (i, j) - (1, 0)) =
        g (torusC64FreeEmbed (⟨i.val - 1, by have := i.isLt; omega⟩, j))
      congr 1
      apply Prod.ext
      · change (i.val : ZMod (2 * L)) - 1 = ((i.val - 1 : ℕ) : ZMod (2 * L))
        rw [Nat.cast_sub (by omega)]
        simp
      · simp [torusC64FreeEmbed]
    · have heq : i.val = 0 := by omega
      simp only [dite_eq_right (by omega : ¬ 0 < i.val)]
      have hz : torusC64FreeEmbed (i, j) - (1, 0) =
          (((i.val : ZMod (2 * L)) - 1), (j.val : ZMod (2 * L))) := by
        ext <;> simp [torusC64FreeEmbed]
      rw [hz]
      exact (hfirst (((i.val : ZMod (2 * L)) - 1), (j.val : ZMod (2 * L)))).symm.trans
        (congrArg g (torusC64_reflectFirst_lower_boundary i j heq))
  have hyp : g (torusC64FreeEmbed (i, j) + (0, 1)) =
      if hj : j.val + 1 < L then
        torusC64FreeRestrict g (i, ⟨j.val + 1, hj⟩) else
        torusC64FreeRestrict g (i, j) := by
    by_cases hj : j.val + 1 < L
    · simp only [dite_eq_left hj]
      change g (torusC64FreeEmbed (i, j) + (0, 1)) =
        g (torusC64FreeEmbed (i, ⟨j.val + 1, hj⟩))
      congr 1
      apply Prod.ext
      · simp [torusC64FreeEmbed]
      · change (j.val : ZMod (2 * L)) + 1 = ((j.val + 1 : ℕ) : ZMod (2 * L))
        simp
    · have heq : j.val + 1 = L := by have := j.isLt; omega
      simp only [dite_eq_right (by omega : ¬ j.val + 1 < L)]
      have hz : torusC64FreeEmbed (i, j) + (0, 1) =
          ((i.val : ZMod (2 * L)), ((j.val : ZMod (2 * L)) + 1)) := by
        ext <;> simp [torusC64FreeEmbed]
      rw [hz]
      exact (hsecond ((i.val : ZMod (2 * L)), ((j.val : ZMod (2 * L)) + 1))).symm.trans
        (congrArg g (torusC64_reflectSecond_upper_boundary i j heq))
  have hym : g (torusC64FreeEmbed (i, j) - (0, 1)) =
      if hj : 0 < j.val then
        torusC64FreeRestrict g (i, ⟨j.val - 1, by have := j.isLt; omega⟩) else
        torusC64FreeRestrict g (i, j) := by
    by_cases hj : 0 < j.val
    · simp only [dite_eq_left hj]
      change g (torusC64FreeEmbed (i, j) - (0, 1)) =
        g (torusC64FreeEmbed (i, ⟨j.val - 1, by have := j.isLt; omega⟩))
      congr 1
      apply Prod.ext
      · simp [torusC64FreeEmbed]
      · change (j.val : ZMod (2 * L)) - 1 = ((j.val - 1 : ℕ) : ZMod (2 * L))
        rw [Nat.cast_sub (by omega)]
        simp
    · have heq : j.val = 0 := by omega
      simp only [dite_eq_right (by omega : ¬ 0 < j.val)]
      have hz : torusC64FreeEmbed (i, j) - (0, 1) =
          ((i.val : ZMod (2 * L)), ((j.val : ZMod (2 * L)) - 1)) := by
        ext <;> simp [torusC64FreeEmbed]
      rw [hz]
      exact (hsecond ((i.val : ZMod (2 * L)), ((j.val : ZMod (2 * L)) - 1))).symm.trans
        (congrArg g (torusC64_reflectSecond_lower_boundary i j heq))
  rw [hxp, hxm, hyp, hym]
  simp only [torusC64FreeRestrict, torusC64FreeEmbed]
  split_ifs <;> ring

/-- The free mean-zero inverse is the restriction of the periodic mean-zero
inverse, followed by removal of its free-box mean. -/
theorem squareFree_greenOp_reflection_transfer {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hT : (torusGraph (2 * L) hside).Connected)
    (hFgraph : (squareFreeGraph L).Connected)
    (f : SquareFreeVertex L → ℝ) (hf : ∑ v, f v = 0) :
    ∀ v, (squareFreeGraph L).greenOp hFgraph f v =
      torusC64FreeRestrict
        ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v -
        vertexMean (SquareFreeVertex L)
          (torusC64FreeRestrict
            ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f))) := by
  let GT := torusGraph (2 * L) hside
  let GF := squareFreeGraph L
  let F := torusC64Reflection L f
  let g := GT.greenOp hT F
  let h := torusC64FreeRestrict g
  have hFsum : ∑ z, F z = 0 := by
    dsimp [F]
    rw [torusC64Reflection_sum, hf]
    ring
  have hglap : GT.laplacian g = F := by
    exact GT.laplacian_greenOp_of_sum_eq_zero hT F hFsum
  have hgsym1 : ∀ z, g (torusC64ReflectFirst L z) = g z := by
    intro z
    exact torusGreenOp_reflection_first hside hT f hf z
  have hgsym2 : ∀ z, g (torusC64ReflectSecond L z) = g z := by
    intro z
    exact torusGreenOp_reflection_second hside hT f hf z
  have hFfree (v : SquareFreeVertex L) : F (torusC64FreeEmbed v) = f v := by
    rcases v with ⟨i, j⟩
    simp [F, torusC64Reflection, torusC64FreeEmbed,
      torusC64FoldIndex_cast_fin]
  have hhlap : GF.laplacian h = f := by
    funext v
    rcases v with ⟨i, j⟩
    change (squareFreeGraph L).laplacian h (i, j) = f (i, j)
    calc
      _ = (torusGraph (2 * L) hside).laplacian g (torusC64FreeEmbed (i, j)) :=
        (torusC64_laplacian_restrict_symmetric hside g hgsym1 hgsym2 i j).symm
      _ = F (torusC64FreeEmbed (i, j)) := congrFun hglap _
      _ = f (i, j) := hFfree (i, j)
  let hV : Nonempty (SquareFreeVertex L) := hFgraph.nonempty
  let h₀ := zeroSumProjection hV h
  have hh₀sum : ∑ v, (h₀ : SquareFreeVertex L → ℝ) v = 0 := h₀.property
  have hFgraph' : GF.toSimpleGraph.Connected := hFgraph
  have hh₀lap : GF.laplacian (h₀ : SquareFreeVertex L → ℝ) = f := by
    have hform : (h₀ : SquareFreeVertex L → ℝ) =
        h - fun _ => vertexMean (SquareFreeVertex L) h := by
      funext v
      simp [h₀, zeroSumProjection_apply]
    rw [hform]
    funext v
    calc
      GF.laplacian (h - fun _ => vertexMean (SquareFreeVertex L) h) v =
          GF.laplacian h v := by
            change (GF.laplacianₗ ℝ (h - fun _ => vertexMean (SquareFreeVertex L) h)) v =
              (GF.laplacianₗ ℝ h) v
            rw [(GF.laplacianₗ ℝ).map_sub]
            simp [GF.laplacian_const]
      _ = f v := congrFun hhlap v
  have huniq := GF.greenOp_laplacian_of_sum_eq_zero
    hFgraph' (h₀ : SquareFreeVertex L → ℝ) hh₀sum
  rw [hh₀lap] at huniq
  have hconnEq : hFgraph' = hFgraph := Subsingleton.elim _ _
  rw [hconnEq] at huniq
  intro v
  have hv := congrFun huniq v
  change GF.greenOp hFgraph f v =
    torusC64FreeRestrict (GT.greenOp hT F) v -
      vertexMean (SquareFreeVertex L) (torusC64FreeRestrict (GT.greenOp hT F))
  calc
    GF.greenOp hFgraph f v = (h₀ : SquareFreeVertex L → ℝ) v := hv
    _ = torusC64FreeRestrict (GT.greenOp hT F) v -
        vertexMean (SquareFreeVertex L) (torusC64FreeRestrict (GT.greenOp hT F)) := by
          simp [h₀, h, g, F, zeroSumProjection_apply]

/-- The free quadratic form pairs with the restricted periodic solution on the
free quadrant. Since both coordinates are folded, the full reflected pairing
is four times the free pairing. -/
theorem squareFree_greenBilinear_eq_restricted_periodic_pairing
    {L : ℕ} [NeZero (2 * L)] (hside : 2 < 2 * L)
    (hT : (torusGraph (2 * L) hside).Connected)
    (hFgraph : (squareFreeGraph L).Connected)
    (f : SquareFreeVertex L → ℝ) (hf : ∑ v, f v = 0) :
    greenBilinear (squareFreeGraph L) hFgraph f f =
      pairing f (fun v => -torusC64FreeRestrict
        ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v) := by
  have htrans := squareFree_greenOp_reflection_transfer hside hT hFgraph f hf
  let c := vertexMean (SquareFreeVertex L)
    (torusC64FreeRestrict
      ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)))
  have hc : pairing f (fun _ => c) = 0 := by
    rw [pairing_comm, pairing_const_left, hf]
    ring
  have hpoint : (fun v => -((squareFreeGraph L).greenOp hFgraph f v)) =
      (fun v => -torusC64FreeRestrict
        ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v + c) := by
    funext v
    have hv := htrans v
    have hneg := congrArg Neg.neg hv
    calc
      -((squareFreeGraph L).greenOp hFgraph f v) =
          c - torusC64FreeRestrict
            ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v := by
              simpa [c] using hneg
      _ = -torusC64FreeRestrict
          ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v + c := by ring
  unfold greenBilinear
  calc
    pairing f (-( (squareFreeGraph L).greenOp hFgraph f)) =
        pairing f (fun v => -torusC64FreeRestrict
          ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v + c) := by
            exact congrArg (pairing f) hpoint
    _ = pairing f (fun v => -torusC64FreeRestrict
        ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v) +
        pairing f (fun _ => c) := by
          rw [show (fun v => -torusC64FreeRestrict
            ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v + c) =
            (fun v => -torusC64FreeRestrict
              ((torusGraph (2 * L) hside).greenOp hT (torusC64Reflection L f)) v) +
              (fun _ => c) by rfl]
          exact pairing_add_right f _ _
    _ = _ := by rw [hc, add_zero]

/-- The second-coordinate backward difference. -/
def torusC64Backward2 {L : ℕ} [NeZero (2 * L)]
    (F : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) : ℝ :=
  F z - F (z - (0, 1))

/-- The adjoint of the first backward difference for counting measure. -/
def torusC64Adjoint1 {L : ℕ} [NeZero (2 * L)]
    (F : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) : ℝ :=
  F z - F (z + (1, 0))

/-- The adjoint of the second backward difference for counting measure. -/
def torusC64Adjoint2 {L : ℕ} [NeZero (2 * L)]
    (F : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) : ℝ :=
  F z - F (z + (0, 1))

private def torusC64Shift1Equiv (n : ℕ) [NeZero n] :
    TorusVertex n ≃ TorusVertex n where
  toFun z := z + (1, 0)
  invFun z := z - (1, 0)
  left_inv z := by simp
  right_inv z := by simp

private def torusC64Shift2Equiv (n : ℕ) [NeZero n] :
    TorusVertex n ≃ TorusVertex n where
  toFun z := z + (0, 1)
  invFun z := z - (0, 1)
  left_inv z := by simp
  right_inv z := by simp

/-- Summation by parts for the horizontal periodic difference. -/
theorem torusC64_pairing_backward1_adjoint {L : ℕ} [NeZero (2 * L)]
    (f g : TorusVertex (2 * L) → ℝ) :
    pairing (torusC64Backward1 f) g = pairing f (torusC64Adjoint1 g) := by
  unfold Multigraph.pairing torusC64Backward1 torusC64Adjoint1
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hshift : (∑ z : TorusVertex (2 * L), f (z - (1, 0)) * g z) =
      ∑ z, f z * g (z + (1, 0)) := by
    rw [← Equiv.sum_comp (torusC64Shift1Equiv (2 * L))
      (fun z : TorusVertex (2 * L) => f (z - (1, 0)) * g z)]
    simp [torusC64Shift1Equiv]
  rw [hshift]

/-- Summation by parts for the vertical periodic difference. -/
theorem torusC64_pairing_backward2_adjoint {L : ℕ} [NeZero (2 * L)]
    (f g : TorusVertex (2 * L) → ℝ) :
    pairing (torusC64Backward2 f) g = pairing f (torusC64Adjoint2 g) := by
  unfold Multigraph.pairing torusC64Backward2 torusC64Adjoint2
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hshift : (∑ z : TorusVertex (2 * L), f (z - (0, 1)) * g z) =
      ∑ z, f z * g (z + (0, 1)) := by
    rw [← Equiv.sum_comp (torusC64Shift2Equiv (2 * L))
      (fun z : TorusVertex (2 * L) => f (z - (0, 1)) * g z)]
    simp [torusC64Shift2Equiv]
  rw [hshift]

private theorem torusC64_laplacian_shift1 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) :
    (torusGraph (2 * L) hside).laplacian (fun w => f (w + (1, 0))) z =
      (torusGraph (2 * L) hside).laplacian f (z + (1, 0)) := by
  rw [torusLaplacian_neighbor_formula_real hside,
    torusLaplacian_neighbor_formula_real hside]
  simp [add_assoc, sub_eq_add_neg]

private theorem torusC64_laplacian_shift2 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) :
    (torusGraph (2 * L) hside).laplacian (fun w => f (w + (0, 1))) z =
      (torusGraph (2 * L) hside).laplacian f (z + (0, 1)) := by
  rw [torusLaplacian_neighbor_formula_real hside,
    torusLaplacian_neighbor_formula_real hside]
  simp [add_assoc, sub_eq_add_neg]

private theorem torusC64_laplacian_adjoint1 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) :
    (torusGraph (2 * L) hside).laplacian (torusC64Adjoint1 f) =
      torusC64Adjoint1 ((torusGraph (2 * L) hside).laplacian f) := by
  funext z
  change ((torusGraph (2 * L) hside).laplacianₗ ℝ
      (f - fun w => f (w + (1, 0)))) z =
    (torusGraph (2 * L) hside).laplacian f z -
      (torusGraph (2 * L) hside).laplacian f (z + (1, 0))
  rw [((torusGraph (2 * L) hside).laplacianₗ ℝ).map_sub]
  change (torusGraph (2 * L) hside).laplacian f z -
      (torusGraph (2 * L) hside).laplacian (fun w => f (w + (1, 0))) z = _
  rw [torusC64_laplacian_shift1]

private theorem torusC64_laplacian_adjoint2 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) :
    (torusGraph (2 * L) hside).laplacian (torusC64Adjoint2 f) =
      torusC64Adjoint2 ((torusGraph (2 * L) hside).laplacian f) := by
  funext z
  change ((torusGraph (2 * L) hside).laplacianₗ ℝ
      (f - fun w => f (w + (0, 1)))) z =
    (torusGraph (2 * L) hside).laplacian f z -
      (torusGraph (2 * L) hside).laplacian f (z + (0, 1))
  rw [((torusGraph (2 * L) hside).laplacianₗ ℝ).map_sub]
  change (torusGraph (2 * L) hside).laplacian f z -
      (torusGraph (2 * L) hside).laplacian (fun w => f (w + (0, 1))) z = _
  rw [torusC64_laplacian_shift2]

/-- The sum of the two difference-adjoint products is the negative periodic
Laplacian. -/
private theorem torusC64_adjoint_backward_sum {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) :
    torusC64Adjoint1 (torusC64Backward1 f) +
        torusC64Adjoint2 (torusC64Backward2 f) =
      -(torusGraph (2 * L) hside).laplacian f := by
  funext z
  change torusC64Adjoint1 (torusC64Backward1 f) z +
      torusC64Adjoint2 (torusC64Backward2 f) z =
    -(torusGraph (2 * L) hside).laplacian f z
  rw [torusLaplacian_neighbor_formula_real hside]
  simp only [torusC64Adjoint1, torusC64Adjoint2, torusC64Backward1, torusC64Backward2,
    add_sub_cancel_right]
  ring

private theorem torusC64_sum_backward1_eq_zero {L : ℕ} [NeZero (2 * L)]
    (f : TorusVertex (2 * L) → ℝ) :
    ∑ z, torusC64Backward1 f z = 0 := by
  unfold torusC64Backward1
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ z : TorusVertex (2 * L), f (z - (1, 0))) = ∑ z, f z := by
    rw [← Equiv.sum_comp (torusC64Shift1Equiv (2 * L))
      (fun z : TorusVertex (2 * L) => f (z - (1, 0)))]
    simp [torusC64Shift1Equiv]
  rw [hshift]
  ring

private theorem torusC64_sum_backward2_eq_zero {L : ℕ} [NeZero (2 * L)]
    (f : TorusVertex (2 * L) → ℝ) :
    ∑ z, torusC64Backward2 f z = 0 := by
  unfold torusC64Backward2
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ z : TorusVertex (2 * L), f (z - (0, 1))) = ∑ z, f z := by
    rw [← Equiv.sum_comp (torusC64Shift2Equiv (2 * L))
      (fun z : TorusVertex (2 * L) => f (z - (0, 1)))]
    simp [torusC64Shift2Equiv]
  rw [hshift]
  ring

private theorem torusC64_sum_adjoint1_eq_zero {L : ℕ} [NeZero (2 * L)]
    (f : TorusVertex (2 * L) → ℝ) :
    ∑ z, torusC64Adjoint1 f z = 0 := by
  unfold torusC64Adjoint1
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ z : TorusVertex (2 * L), f (z + (1, 0))) = ∑ z, f z := by
    exact Equiv.sum_comp (torusC64Shift1Equiv (2 * L)) f
  rw [hshift]
  ring

private theorem torusC64_sum_adjoint2_eq_zero {L : ℕ} [NeZero (2 * L)]
    (f : TorusVertex (2 * L) → ℝ) :
    ∑ z, torusC64Adjoint2 f z = 0 := by
  unfold torusC64Adjoint2
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ z : TorusVertex (2 * L), f (z + (0, 1))) = ∑ z, f z := by
    exact Equiv.sum_comp (torusC64Shift2Equiv (2 * L)) f
  rw [hshift]
  ring

/-- Periodic Hodge decomposition for a zero-sum source. Its proof uses the
Laplacian equation for the mean-zero Green inverse and uniqueness. -/
theorem torusC64_hodge_identity {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hT : (torusGraph (2 * L) hside).Connected)
    (F : TorusVertex (2 * L) → ℝ) (hF : ∑ z, F z = 0) :
    torusC64Adjoint1
        (-((torusGraph (2 * L) hside).greenOp hT (torusC64Backward1 F))) +
      torusC64Adjoint2
        (-((torusGraph (2 * L) hside).greenOp hT (torusC64Backward2 F))) = F := by
  let G := torusGraph (2 * L) hside
  let d₁ := torusC64Backward1 F
  let d₂ := torusC64Backward2 F
  let u₁ := -G.greenOp hT d₁
  let u₂ := -G.greenOp hT d₂
  let H := torusC64Adjoint1 u₁ + torusC64Adjoint2 u₂
  have hd₁ : ∑ z, d₁ z = 0 := by dsimp [d₁]; exact torusC64_sum_backward1_eq_zero F
  have hd₂ : ∑ z, d₂ z = 0 := by dsimp [d₂]; exact torusC64_sum_backward2_eq_zero F
  have hu₁ : G.laplacian u₁ = -d₁ := by
    have h := G.laplacian_greenOp_of_sum_eq_zero hT d₁ hd₁
    change G.laplacian (-G.greenOp hT d₁) = -d₁
    calc
      _ = -G.laplacian (G.greenOp hT d₁) := by
        change (G.laplacianₗ ℝ (-G.greenOp hT d₁)) = _
        rw [(G.laplacianₗ ℝ).map_neg]
        rfl
      _ = -d₁ := by rw [h]
  have hu₂ : G.laplacian u₂ = -d₂ := by
    have h := G.laplacian_greenOp_of_sum_eq_zero hT d₂ hd₂
    change G.laplacian (-G.greenOp hT d₂) = -d₂
    calc
      _ = -G.laplacian (G.greenOp hT d₂) := by
        change (G.laplacianₗ ℝ (-G.greenOp hT d₂)) = _
        rw [(G.laplacianₗ ℝ).map_neg]
        rfl
      _ = -d₂ := by rw [h]
  have hLapH : G.laplacian H = G.laplacian F := by
    calc
      G.laplacian H = G.laplacian (torusC64Adjoint1 u₁) +
          G.laplacian (torusC64Adjoint2 u₂) := by
            change G.laplacianₗ ℝ
                (torusC64Adjoint1 u₁ + torusC64Adjoint2 u₂) = _
            rw [(G.laplacianₗ ℝ).map_add]
            change G.laplacian (torusC64Adjoint1 u₁) +
              G.laplacian (torusC64Adjoint2 u₂) = _
            rfl
      _ = torusC64Adjoint1 (G.laplacian u₁) +
          torusC64Adjoint2 (G.laplacian u₂) := by
            rw [torusC64_laplacian_adjoint1 hside,
              torusC64_laplacian_adjoint2 hside]
      _ = -(torusC64Adjoint1 d₁ + torusC64Adjoint2 d₂) := by
            rw [hu₁, hu₂]
            funext z
            simp [torusC64Adjoint1, torusC64Adjoint2]
            ring
      _ = G.laplacian F := by
            have hid := torusC64_adjoint_backward_sum hside F
            simpa [d₁, d₂] using congrArg Neg.neg hid
  have hHsum : ∑ z, H z = 0 := by
    dsimp [H]
    rw [Finset.sum_add_distrib, torusC64_sum_adjoint1_eq_zero,
      torusC64_sum_adjoint2_eq_zero, add_zero]
  have hdiffsum : ∑ z, (H z - F z) = 0 := by
    rw [Finset.sum_sub_distrib, hHsum, hF]
    ring
  have hdiffLap : G.laplacian (H - F) = 0 := by
    change G.laplacianₗ ℝ (H - F) = 0
    rw [(G.laplacianₗ ℝ).map_sub]
    change G.laplacian H - G.laplacian F = 0
    rw [hLapH]
    ring
  have huniq := G.greenOp_laplacian_of_sum_eq_zero hT (H - F) hdiffsum
  rw [hdiffLap] at huniq
  have hzero : G.greenOp hT (0 : TorusVertex (2 * L) → ℝ) = 0 := by
    exact (G.greenOp hT).map_zero
  rw [hzero] at huniq
  have hHEqF : H = F := by
    funext z
    have hz := congrFun huniq z
    change 0 = H z - F z at hz
    linarith only [hz]
  simpa [H, u₁, u₂, G, d₁, d₂] using hHEqF

private theorem torusC64_reflectFirst_val {L : ℕ} [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    (-a - 1).val = 2 * L - 1 - a.val := by
  rw [show -a - 1 = -(a + 1) by ring, ZMod.neg_val,
    torusC64_add_one_val]
  by_cases h : a.val + 1 < 2 * L
  · have hne : a + 1 ≠ 0 := by
      intro hz
      have hh := congrArg ZMod.val hz
      rw [torusC64_add_one_val] at hh
      simp [h] at hh
    simp [h, hne]
    omega
  · have heq : a.val + 1 = 2 * L := by have := a.val_lt; omega
    have hz : a + 1 = 0 := by
      apply ZMod.val_injective (2 * L)
      rw [torusC64_add_one_val, heq]
      simp
    simp [hz, heq]

/-- The folded representative, cast back into the torus, is the original
coordinate on the near half and its edge reflection on the far half. -/
theorem torusC64FoldIndex_cast_zmod {L : ℕ} [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    ((torusC64FoldIndex L a).val : ZMod (2 * L)) =
      if a.val < L then a else -a - 1 := by
  by_cases h : a.val < L
  · rw [ite_eq_left h, torusC64FoldIndex_of_lt L a h]
    simp
  · have hge : L ≤ a.val := Nat.le_of_not_gt h
    have hneg : (-a - 1).val = 2 * L - 1 - a.val :=
      torusC64_reflectFirst_val a
    rw [ite_eq_right h, torusC64FoldIndex_of_ge L a hge]
    apply ZMod.val_injective
    simp only [ZMod.val_natCast]
    have hav := a.val_lt
    have hlt : 2 * L - 1 - a.val < 2 * L := by omega
    rw [Nat.mod_eq_of_lt hlt]
    rw [hneg]

/-- A folded coordinate equals a free index exactly at its two reflected
torus representatives. -/
theorem torusC64FoldIndex_eq_fin_iff {L : ℕ} [NeZero (2 * L)]
    (b : Fin L) (a : ZMod (2 * L)) :
    torusC64FoldIndex L a = b ↔
      a = (b.val : ZMod (2 * L)) ∨
        a = ((2 * L - 1 - b.val : ℕ) : ZMod (2 * L)) := by
  constructor
  · intro h
    have hc := congrArg (fun i : Fin L => (i.val : ZMod (2 * L))) h
    rw [torusC64FoldIndex_cast_zmod] at hc
    by_cases ha : a.val < L
    · simp only [ite_eq_left ha] at hc
      exact Or.inl hc
    · simp only [ite_eq_right ha] at hc
      right
      have hneg : a = -(b.val : ZMod (2 * L)) - 1 := by
        have h' : -a = (b.val : ZMod (2 * L)) + 1 := by
          linear_combination hc
        calc
          a = -(-a) := by ring
          _ = -((b.val : ZMod (2 * L)) + 1) := congrArg Neg.neg h'
          _ = -(b.val : ZMod (2 * L)) - 1 := by ring
      have hb : b.val < L := b.isLt
      have hmirror : -(b.val : ZMod (2 * L)) - 1 =
          ((2 * L - 1 - b.val : ℕ) : ZMod (2 * L)) := by
        have hnat : 2 * L - 1 - b.val = 2 * L - (b.val + 1) := by omega
        rw [hnat, Nat.cast_sub (by omega : b.val + 1 ≤ 2 * L)]
        simp only [Nat.cast_add, ZMod.natCast_self, zero_sub]
        ring
      exact hneg.trans hmirror
  · rintro (rfl | h)
    · exact torusC64FoldIndex_cast_fin L b
    · have hmLt : 2 * L - 1 - b.val < 2 * L := by omega
      have hmGe : L ≤ 2 * L - 1 - b.val := by omega
      have hval : (((2 * L - 1 - b.val : ℕ) : ZMod (2 * L)).val) =
          2 * L - 1 - b.val := by
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt hmLt
      rw [h]
      apply Fin.ext
      rw [torusC64FoldIndex_val]
      rw [hval]
      rw [ite_eq_right (by omega : ¬ 2 * L - 1 - b.val < L)]
      omega

private theorem torusC64StripIndicator_eq_fold {L a : ℕ} [NeZero (2 * L)]
    (ha : a < L) (x : ZMod (2 * L)) :
    torusC64StripIndicator L a x =
      if a ≤ (torusC64FoldIndex L x).val then 1 else 0 := by
  by_cases hx : x.val < L
  · have hstrip : (a ≤ x.val ∧ x.val < 2 * L - a) ↔ a ≤ x.val := by
      constructor
      · exact fun h => h.1
      · intro hlow
        exact ⟨hlow, by have := x.val_lt; omega⟩
    simp [torusC64StripIndicator, torusC64FoldIndex_val, hx, hstrip]
  · have hxge : L ≤ x.val := Nat.le_of_not_gt hx
    have hlow : a ≤ x.val := by omega
    have hupper : x.val < 2 * L - a ↔ a ≤ 2 * L - 1 - x.val := by
      have := x.val_lt
      omega
    simp [torusC64StripIndicator, torusC64FoldIndex_val, hx, hlow, hupper]

private theorem torusC64_natCast_ne {n a b : ℕ} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : (a : ZMod n) ≠ (b : ZMod n) := by
  intro h
  have hv := congrArg ZMod.val h
  simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hab hv

private theorem torusC64_two_indicator_sum {α : Type*} [DecidableEq α]
    (y a b : α) (hab : a ≠ b) :
    (if y = a then (1 : ℝ) else 0) + (if y = b then 1 else 0) =
      if y = a ∨ y = b then 1 else 0 := by
  by_cases hya : y = a <;> by_cases hyb : y = b
  · have hab' : a = b := hya.symm.trans hyb
    exact (hab hab').elim
  · have hne : y ≠ b := by intro h; exact hab (hya.symm.trans h)
    rw [ite_eq_left hya, ite_eq_right hne, ite_eq_left (Or.inl hya)]
    norm_num
  · have hne : y ≠ a := by intro h; exact hab (h.symm.trans hyb)
    rw [ite_eq_right hne, ite_eq_left hyb, ite_eq_left (Or.inr hyb)]
    norm_num
  · rw [ite_eq_right hya, ite_eq_right hyb,
      ite_eq_right (not_or.mpr ⟨hya, hyb⟩)]
    norm_num

private theorem torusC64_ite_and (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) =
      (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

private theorem torusC64_vertical_row_difference
    (L y₁ : ℕ) [NeZero (2 * L)] (hy₁ : y₁ + 1 < L)
    (y : ZMod (2 * L)) :
    ((if y = (y₁ : ZMod (2 * L)) then (1 : ℝ) else 0) -
      (if y = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) then 1 else 0)) -
      ((if y - 1 = (y₁ : ZMod (2 * L)) then 1 else 0) -
        (if y - 1 = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) then 1 else 0)) =
      (if (torusC64FoldIndex L y).val = y₁ then 1 else 0) -
        (if (torusC64FoldIndex L y).val = y₁ + 1 then 1 else 0) := by
  let q := 2 * L - 2 - y₁
  have hy₁lt : y₁ < L := by omega
  have hqLo : L ≤ q := by dsimp [q]; omega
  have hqHi : q + 1 < 2 * L := by dsimp [q]; omega
  have hrow1 : 2 * L - 1 - y₁ = q + 1 := by dsimp [q]; omega
  have hrow2 : 2 * L - 1 - (y₁ + 1) = q := by dsimp [q]; omega
  have hprev1 : (if y - 1 = (y₁ : ZMod (2 * L)) then (1 : ℝ) else 0) =
      if y = ((y₁ + 1 : ℕ) : ZMod (2 * L)) then 1 else 0 := by
    have hiff : y - 1 = (y₁ : ZMod (2 * L)) ↔
        y = (y₁ : ZMod (2 * L)) + 1 := by
      constructor
      · intro h
        have ht := congrArg (fun z : ZMod (2 * L) => z + 1) h
        simpa using ht
      · intro h
        have ht := congrArg (fun z : ZMod (2 * L) => z - 1) h
        simpa using ht
    have hcast : (y₁ : ZMod (2 * L)) + 1 =
        ((y₁ + 1 : ℕ) : ZMod (2 * L)) := by push_cast; ring
    rw [if_congr (hiff.trans (by rw [hcast])) rfl rfl]
  have hprevq : (if y - 1 = ((q : ℕ) : ZMod (2 * L)) then (1 : ℝ) else 0) =
      if y = ((q + 1 : ℕ) : ZMod (2 * L)) then 1 else 0 := by
    have hiff : y - 1 = ((q : ℕ) : ZMod (2 * L)) ↔
        y = ((q : ℕ) : ZMod (2 * L)) + 1 := by
      constructor
      · intro h
        have ht := congrArg (fun z : ZMod (2 * L) => z + 1) h
        simpa using ht
      · intro h
        have ht := congrArg (fun z : ZMod (2 * L) => z - 1) h
        simpa using ht
    have hcast : ((q : ℕ) : ZMod (2 * L)) + 1 =
        ((q + 1 : ℕ) : ZMod (2 * L)) := by push_cast; ring
    rw [if_congr (hiff.trans (by rw [hcast])) rfl rfl]
  let b₁ : Fin L := ⟨y₁, hy₁lt⟩
  let b₂ : Fin L := ⟨y₁ + 1, hy₁⟩
  have hfold₁ : torusC64FoldIndex L y = b₁ ↔
      y = (y₁ : ZMod (2 * L)) ∨ y = ((q + 1 : ℕ) : ZMod (2 * L)) := by
    rw [torusC64FoldIndex_eq_fin_iff]
    rw [hrow1]
  have hfold₂ : torusC64FoldIndex L y = b₂ ↔
      y = ((y₁ + 1 : ℕ) : ZMod (2 * L)) ∨ y = ((q : ℕ) : ZMod (2 * L)) := by
    rw [torusC64FoldIndex_eq_fin_iff]
    rw [hrow2]
  have hfold₁' : (torusC64FoldIndex L y).val = y₁ ↔
      y = (y₁ : ZMod (2 * L)) ∨ y = ((q + 1 : ℕ) : ZMod (2 * L)) := by
    constructor
    · intro hv
      apply hfold₁.mp
      apply Fin.ext
      simpa [b₁] using hv
    · intro hr
      have hv := congrArg Fin.val (hfold₁.mpr hr)
      simpa [b₁] using hv
  have hfold₂' : (torusC64FoldIndex L y).val = y₁ + 1 ↔
      y = ((y₁ + 1 : ℕ) : ZMod (2 * L)) ∨ y = ((q : ℕ) : ZMod (2 * L)) := by
    constructor
    · intro hv
      apply hfold₂.mp
      apply Fin.ext
      simpa [b₂] using hv
    · intro hr
      have hv := congrArg Fin.val (hfold₂.mpr hr)
      simpa [b₂] using hv
  have haBound : y₁ < 2 * L := by omega
  have hdBound : y₁ + 1 < 2 * L := by omega
  have hqBound : q < 2 * L := by omega
  have hqpBound : q + 1 < 2 * L := by omega
  have hposDisj := torusC64_natCast_ne haBound hqpBound (by omega)
  have hnegDisj := torusC64_natCast_ne hdBound hqBound (by omega)
  have hcastQ : ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) = (q : ZMod (2 * L)) := rfl
  have hif₁ : (if y = (y₁ : ZMod (2 * L)) ∨
        y = ((q + 1 : ℕ) : ZMod (2 * L)) then (1 : ℝ) else 0) =
      if (torusC64FoldIndex L y).val = y₁ then 1 else 0 :=
    if_congr hfold₁'.symm rfl rfl
  have hif₂ : (if y = ((y₁ + 1 : ℕ) : ZMod (2 * L)) ∨
        y = (q : ZMod (2 * L)) then (1 : ℝ) else 0) =
      if (torusC64FoldIndex L y).val = y₁ + 1 then 1 else 0 :=
    if_congr hfold₂'.symm rfl rfl
  calc
    _ = ((if y = (y₁ : ZMod (2 * L)) then (1 : ℝ) else 0) +
          (if y = ((q + 1 : ℕ) : ZMod (2 * L)) then 1 else 0)) -
        ((if y = ((y₁ + 1 : ℕ) : ZMod (2 * L)) then 1 else 0) +
          (if y = (q : ZMod (2 * L)) then 1 else 0)) := by
            rw [hcastQ, hprev1, hprevq]
            ring
    _ = (if y = (y₁ : ZMod (2 * L)) ∨
            y = ((q + 1 : ℕ) : ZMod (2 * L)) then 1 else 0) -
        (if y = ((y₁ + 1 : ℕ) : ZMod (2 * L)) ∨
            y = (q : ZMod (2 * L)) then 1 else 0) := by
            rw [torusC64_two_indicator_sum y (y₁ : ZMod (2 * L))
                ((q + 1 : ℕ) : ZMod (2 * L)) hposDisj,
              torusC64_two_indicator_sum y ((y₁ + 1 : ℕ) : ZMod (2 * L))
                (q : ZMod (2 * L)) hnegDisj]
    _ = (if (torusC64FoldIndex L y).val = y₁ then 1 else 0) -
        (if (torusC64FoldIndex L y).val = y₁ + 1 then 1 else 0) := by
            rw [hif₁, hif₂]

/-- KP (6.14): the reflected strip potential has vertical difference equal
to the folded free source. -/
theorem torusC64Backward2_reflectedPotential_eq_reflection_source
    (L y₀ y₁ : ℕ) [NeZero (2 * L)]
    (hy₀ : y₀ < L) (hy₁ : y₁ + 1 < L) :
    ∀ z, torusC64Backward2 (torusC64ReflectedPotential L y₀ y₁) z =
      torusC64Reflection L (squareFreeLineSource L y₀ y₁) z := by
  intro z
  rcases z with ⟨x, y⟩
  have hshift : (x, y) - (0, 1) = (x, y - 1) := by ext <;> simp
  change torusC64ReflectedPotential L y₀ y₁ (x, y) -
      torusC64ReflectedPotential L y₀ y₁ ((x, y) - (0, 1)) = _
  rw [hshift]
  have hstrip := torusC64StripIndicator_eq_fold (L := L) (a := y₀) hy₀ x
  have hrow := torusC64_vertical_row_difference L y₁ hy₁ y
  simp only [torusC64ReflectedPotential, torusC64Reflection, squareFreeLineSource]
  rw [hstrip]
  calc
    _ = (if y₀ ≤ (torusC64FoldIndex L x).val then 1 else 0) *
          (((if y = (y₁ : ZMod (2 * L)) then (1 : ℝ) else 0) -
              (if y = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) then 1 else 0)) -
            ((if y - 1 = (y₁ : ZMod (2 * L)) then 1 else 0) -
              (if y - 1 = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) then 1 else 0))) := by ring
    _ = (if y₀ ≤ (torusC64FoldIndex L x).val then 1 else 0) *
          ((if (torusC64FoldIndex L y).val = y₁ then 1 else 0) -
            (if (torusC64FoldIndex L y).val = y₁ + 1 then 1 else 0)) := by
          rw [hrow]
    _ = (if y₀ ≤ (torusC64FoldIndex L x).val ∧
            (torusC64FoldIndex L y).val = y₁ then 1 else 0) -
        (if y₀ ≤ (torusC64FoldIndex L x).val ∧
            (torusC64FoldIndex L y).val = y₁ + 1 then 1 else 0) := by
          rw [torusC64_ite_and, torusC64_ite_and]
          ring

/-- A function invariant under the two edge reflections agrees everywhere
with its value at the folded free-box representative. -/
theorem torusC64_symmetric_eq_fold {L : ℕ} [NeZero (2 * L)]
    (g : TorusVertex (2 * L) → ℝ)
    (h₁ : ∀ z, g (torusC64ReflectFirst L z) = g z)
    (h₂ : ∀ z, g (torusC64ReflectSecond L z) = g z)
    (z : TorusVertex (2 * L)) :
    g z = g (torusC64FreeEmbed
      (torusC64FoldIndex L z.1, torusC64FoldIndex L z.2)) := by
  rcases z with ⟨x, y⟩
  let z₁ : TorusVertex (2 * L) := ((torusC64FoldIndex L x).val, y)
  let z₂ : TorusVertex (2 * L) :=
    ((torusC64FoldIndex L x).val, (torusC64FoldIndex L y).val)
  have hxCast := torusC64FoldIndex_cast_zmod (L := L) x
  have hyCast := torusC64FoldIndex_cast_zmod (L := L) y
  have hfirst : g (x, y) = g z₁ := by
    by_cases hx : x.val < L
    · have hz : z₁ = (x, y) := by
        apply Prod.ext
        · change ((torusC64FoldIndex L x).val : ZMod (2 * L)) = x
          rw [hxCast]
          simp [hx]
        · rfl
      rw [hz]
    · have hz : z₁ = torusC64ReflectFirst L (x, y) := by
        apply Prod.ext
        · change ((torusC64FoldIndex L x).val : ZMod (2 * L)) = -x - 1
          rw [hxCast]
          simp [hx]
        · rfl
      calc
        g (x, y) = g (torusC64ReflectFirst L (x, y)) := (h₁ (x, y)).symm
        _ = g z₁ := by rw [← hz]
  have hsecond : g z₁ = g z₂ := by
    by_cases hy : y.val < L
    · have hz : z₂ = z₁ := by
        apply Prod.ext
        · rfl
        · change ((torusC64FoldIndex L y).val : ZMod (2 * L)) = y
          rw [hyCast]
          simp [hy]
      rw [hz]
    · have hz : z₂ = torusC64ReflectSecond L z₁ := by
        apply Prod.ext
        · rfl
        · change ((torusC64FoldIndex L y).val : ZMod (2 * L)) = -y - 1
          rw [hyCast]
          simp [hy]
      calc
        g z₁ = g (torusC64ReflectSecond L z₁) := (h₂ z₁).symm
        _ = g z₂ := by rw [← hz]
  simpa [z₁, z₂, torusC64FreeEmbed] using hfirst.trans hsecond

/-- The reflected pairing has multiplicity four: every free vertex has two
preimages in each coordinate. -/
theorem torusC64_pairing_reflection_transfer {L : ℕ} [NeZero (2 * L)]
    (f : SquareFreeVertex L → ℝ) (g : TorusVertex (2 * L) → ℝ)
    (h₁ : ∀ z, g (torusC64ReflectFirst L z) = g z)
    (h₂ : ∀ z, g (torusC64ReflectSecond L z) = g z) :
    pairing (torusC64Reflection L f) g =
      4 * pairing f (torusC64FreeRestrict g) := by
  let H : SquareFreeVertex L → ℝ := fun v => f v * torusC64FreeRestrict g v
  have hpoint (z : TorusVertex (2 * L)) :
      torusC64Reflection L H z = torusC64Reflection L f z * g z := by
    simp only [torusC64Reflection, H, torusC64FreeRestrict]
    rw [torusC64_symmetric_eq_fold (L := L) g h₁ h₂ z]
  unfold pairing
  calc
    _ = ∑ z, torusC64Reflection L H z := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (hpoint z).symm
    _ = 4 * ∑ v, H v := torusC64Reflection_sum L H
    _ = 4 * pairing f (torusC64FreeRestrict g) := by simp [H, pairing]

private theorem torusC64_sum_fin_val_indicator_eq_one {L b : ℕ} (hb : b < L) :
    (∑ j : Fin L, if j.val = b then (1 : ℝ) else 0) = 1 := by
  let b' : Fin L := ⟨b, hb⟩
  have heq (j : Fin L) : j.val = b ↔ j = b' := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      have hv := congrArg Fin.val h
      simpa [b'] using hv
  simp_rw [heq]
  simp

private theorem torusC64_sum_fin_cutoff {L a : ℕ} (ha : a ≤ L) :
    (∑ i : Fin L, if a ≤ i.val then (1 : ℝ) else 0) = (L - a : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if a ≤ i then (1 : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hset : (Finset.range L).filter (fun i => a ≤ i) = Finset.Ico a L := by
    ext i
    simp [and_comm]
  rw [hset]
  simp [Nat.card_Ico, ha]

/-- The free line source is neutral. -/
theorem squareFreeLineSource_sum_eq_zero (L y₀ y₁ : ℕ)
    (hy₁ : y₁ + 1 < L) :
    ∑ v : SquareFreeVertex L, squareFreeLineSource L y₀ y₁ v = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [squareFreeLineSource]
  rw [Finset.sum_sub_distrib]
  by_cases hcut : y₀ ≤ i.val
  · simp only [hcut, true_and]
    rw [torusC64_sum_fin_val_indicator_eq_one (by omega),
      torusC64_sum_fin_val_indicator_eq_one hy₁]
    ring
  · simp [hcut]

/-- The reflected KP strip potential has counting norm squared `4N` with its
two rows and its corrected endpoints. -/
theorem torusC64_reflectedPotential_sq_sum (L y₀ y₁ : ℕ)
    [NeZero (2 * L)] (hy₀ : y₀ < L) (hy₁ : y₁ + 1 < L) :
    ∑ z : TorusVertex (2 * L),
      (torusC64ReflectedPotential L y₀ y₁ z) ^ 2 =
      4 * (L - y₀ : ℝ) := by
  let q := 2 * L - 2 - y₁
  have hqLo : L ≤ q := by dsimp [q]; omega
  have hqHi : q < 2 * L := by dsimp [q]; omega
  have hy₁Hi : y₁ < 2 * L := by omega
  have hrows : (y₁ : ZMod (2 * L)) ≠ (q : ZMod (2 * L)) :=
    torusC64_natCast_ne hy₁Hi hqHi (by omega)
  have hpoint (x : ZMod (2 * L)) (y : ZMod (2 * L)) :
      (torusC64ReflectedPotential L y₀ y₁ (x, y)) ^ 2 =
        torusC64StripIndicator L y₀ x *
          ((if y = (y₁ : ZMod (2 * L)) then (1 : ℝ) else 0) +
            (if y = (q : ZMod (2 * L)) then 1 else 0)) := by
    by_cases hs : y₀ ≤ x.val ∧ x.val < 2 * L - y₀
    · have hsval : torusC64StripIndicator L y₀ x = 1 := by
        simp [torusC64StripIndicator, hs]
      rw [torusC64ReflectedPotential, hsval]
      by_cases hy₁' : y = (y₁ : ZMod (2 * L))
      · by_cases hq' : y = (q : ZMod (2 * L))
        · exact (hrows (hy₁'.symm.trans hq')).elim
        · simp [hy₁', q, hrows]
      · by_cases hq' : y = (q : ZMod (2 * L)) <;>
          simp [hy₁', hq', q, hrows.symm]
    · have hsval : torusC64StripIndicator L y₀ x = 0 := by
        simp [torusC64StripIndicator, hs]
      rw [torusC64ReflectedPotential, hsval]
      ring
  have hrowsum (x : ZMod (2 * L)) :
      ∑ y : ZMod (2 * L),
        ((if y = (y₁ : ZMod (2 * L)) then (1 : ℝ) else 0) +
          (if y = (q : ZMod (2 * L)) then 1 else 0)) = 2 := by
    rw [Finset.sum_add_distrib]
    simp
    norm_num
  have hstripSum :
      ∑ x : ZMod (2 * L), torusC64StripIndicator L y₀ x =
        2 * (L - y₀ : ℝ) := by
    calc
      _ = ∑ x : ZMod (2 * L),
          if y₀ ≤ (torusC64FoldIndex L x).val then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact torusC64StripIndicator_eq_fold hy₀ x
      _ = 2 * ∑ i : Fin L, if y₀ ≤ i.val then (1 : ℝ) else 0 :=
        torusC64FoldIndex_sum L (fun i => if y₀ ≤ i.val then (1 : ℝ) else 0)
      _ = 2 * (L - y₀ : ℝ) := by
        rw [torusC64_sum_fin_cutoff (by omega)]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : ZMod (2 * L),
          torusC64StripIndicator L y₀ x *
            (∑ y : ZMod (2 * L),
              ((if y = (y₁ : ZMod (2 * L)) then (1 : ℝ) else 0) +
                (if y = (q : ZMod (2 * L)) then 1 else 0))) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          exact hpoint x y
    _ = 2 * ∑ x : ZMod (2 * L), torusC64StripIndicator L y₀ x := by
          calc
            _ = ∑ x : ZMod (2 * L),
                torusC64StripIndicator L y₀ x * 2 := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [hrowsum x]
            _ = 2 * ∑ x : ZMod (2 * L), torusC64StripIndicator L y₀ x := by
                  rw [← Finset.sum_mul]
                  ring
    _ = 4 * (L - y₀ : ℝ) := by rw [hstripSum]; ring

/-- Discrete Hodge identity: the norm of a potential is the sum of the Green
energies of its two backward differences. -/
theorem torusC64_greenBilinear_hodge_identity {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hT : (torusGraph (2 * L) hside).Connected)
    (P : TorusVertex (2 * L) → ℝ) (hP : ∑ z, P z = 0) :
    pairing P P =
      greenBilinear (torusGraph (2 * L) hside) hT
        (torusC64Backward1 P) (torusC64Backward1 P) +
      greenBilinear (torusGraph (2 * L) hside) hT
        (torusC64Backward2 P) (torusC64Backward2 P) := by
  let G := torusGraph (2 * L) hside
  let U₁ := -G.greenOp hT (torusC64Backward1 P)
  let U₂ := -G.greenOp hT (torusC64Backward2 P)
  have hhodge := torusC64_hodge_identity hside hT P hP
  have hp := congrArg (fun H => pairing P H) hhodge
  rw [pairing_add_right] at hp
  rw [← torusC64_pairing_backward1_adjoint P U₁,
    ← torusC64_pairing_backward2_adjoint P U₂] at hp
  simpa [greenBilinear, G, U₁, U₂] using hp.symm

private theorem torusC64_laplacian_shift1_neg {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) :
    (torusGraph (2 * L) hside).laplacian (fun w => f (w - (1, 0))) z =
      (torusGraph (2 * L) hside).laplacian f (z - (1, 0)) := by
  rw [torusLaplacian_neighbor_formula_real hside,
    torusLaplacian_neighbor_formula_real hside]
  rw [add_sub_cancel_right, sub_add_cancel, add_sub_right_comm z (0, 1) (1, 0),
    sub_right_comm z (0, 1) (1, 0)]

private theorem torusC64_laplacian_shift2_neg {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) :
    (torusGraph (2 * L) hside).laplacian (fun w => f (w - (0, 1))) z =
      (torusGraph (2 * L) hside).laplacian f (z - (0, 1)) := by
  rw [torusLaplacian_neighbor_formula_real hside,
    torusLaplacian_neighbor_formula_real hside]
  rw [add_sub_cancel_right, sub_add_cancel, add_sub_right_comm z (1, 0) (0, 1),
    sub_right_comm z (1, 0) (0, 1)]

private theorem torusC64_laplacian_backward1 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) :
    (torusGraph (2 * L) hside).laplacian (torusC64Backward1 f) =
      torusC64Backward1 ((torusGraph (2 * L) hside).laplacian f) := by
  funext z
  change ((torusGraph (2 * L) hside).laplacianₗ ℝ
      (f - fun w => f (w - (1, 0)))) z = _
  rw [(torusGraph (2 * L) hside).laplacianₗ ℝ |>.map_sub]
  change (torusGraph (2 * L) hside).laplacian f z -
      (torusGraph (2 * L) hside).laplacian (fun w => f (w - (1, 0))) z = _
  rw [torusC64_laplacian_shift1_neg]
  rfl

private theorem torusC64_laplacian_backward2 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (f : TorusVertex (2 * L) → ℝ) :
    (torusGraph (2 * L) hside).laplacian (torusC64Backward2 f) =
      torusC64Backward2 ((torusGraph (2 * L) hside).laplacian f) := by
  funext z
  change ((torusGraph (2 * L) hside).laplacianₗ ℝ
      (f - fun w => f (w - (0, 1)))) z = _
  rw [(torusGraph (2 * L) hside).laplacianₗ ℝ |>.map_sub]
  change (torusGraph (2 * L) hside).laplacian f z -
      (torusGraph (2 * L) hside).laplacian (fun w => f (w - (0, 1))) z = _
  rw [torusC64_laplacian_shift2_neg]
  rfl

private theorem torusC64_greenOp_backward1 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hT : (torusGraph (2 * L) hside).Connected)
    (f : TorusVertex (2 * L) → ℝ) (hf : ∑ z, f z = 0) :
    torusC64Backward1 ((torusGraph (2 * L) hside).greenOp hT f) =
      (torusGraph (2 * L) hside).greenOp hT (torusC64Backward1 f) := by
  let G := torusGraph (2 * L) hside
  let g := G.greenOp hT f
  have hsum : ∑ z, torusC64Backward1 g z = 0 :=
    torusC64_sum_backward1_eq_zero g
  have huniq := G.greenOp_laplacian_of_sum_eq_zero hT
    (torusC64Backward1 g) hsum
  have hlap := torusC64_laplacian_backward1 hside g
  rw [G.laplacian_greenOp_of_sum_eq_zero hT f hf] at hlap
  rw [hlap] at huniq
  exact huniq.symm

private theorem torusC64_greenOp_backward2 {L : ℕ} [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hT : (torusGraph (2 * L) hside).Connected)
    (f : TorusVertex (2 * L) → ℝ) (hf : ∑ z, f z = 0) :
    torusC64Backward2 ((torusGraph (2 * L) hside).greenOp hT f) =
      (torusGraph (2 * L) hside).greenOp hT (torusC64Backward2 f) := by
  let G := torusGraph (2 * L) hside
  let g := G.greenOp hT f
  have hsum : ∑ z, torusC64Backward2 g z = 0 :=
    torusC64_sum_backward2_eq_zero g
  have huniq := G.greenOp_laplacian_of_sum_eq_zero hT
    (torusC64Backward2 g) hsum
  have hlap := torusC64_laplacian_backward2 hside g
  rw [G.laplacian_greenOp_of_sum_eq_zero hT f hf] at hlap
  rw [hlap] at huniq
  exact huniq.symm

/-- The reflected strip potential is zero-sum because its two rows carry
opposite equal-mass indicators. -/
theorem torusC64_reflectedPotential_sum_eq_zero (L y₀ y₁ : ℕ)
    [NeZero (2 * L)] :
    ∑ z : TorusVertex (2 * L), torusC64ReflectedPotential L y₀ y₁ z = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro x hx
  simp only [torusC64ReflectedPotential]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp

/-- KP Claim 6.4: the free-box line-source Green energy is at least
`N - 164 log(N+1)`. The proof includes `N=1`; the periodic input estimate
uses the corrected `2N` strip endpoints. -/
theorem squareFreeLineSource_energy_lower_bound
    (L y₀ y₁ : ℕ) [NeZero (2 * L)]
    (hL : 1 < L) (hy₀ : y₀ < L) (hy₁ : y₁ + 1 < L)
    (hG : (squareFreeGraph L).Connected) :
    let N := L - y₀
    greenBilinear (squareFreeGraph L) hG
      (squareFreeLineSource L y₀ y₁) (squareFreeLineSource L y₀ y₁) ≥
      N - 164 * Real.log ((N + 1 : ℕ) : ℝ) := by
  let N := L - y₀
  let hside : 2 < 2 * L := by omega
  let hT : (torusGraph (2 * L) hside).Connected := torusGraph_connected (2 * L) hside
  let f : SquareFreeVertex L → ℝ := squareFreeLineSource L y₀ y₁
  let F : TorusVertex (2 * L) → ℝ := torusC64Reflection L f
  let P : TorusVertex (2 * L) → ℝ := torusC64ReflectedPotential L y₀ y₁
  have hf : ∑ v, f v = 0 := by
    exact squareFreeLineSource_sum_eq_zero L y₀ y₁ hy₁
  have hFsum : ∑ z, F z = 0 := by
    dsimp [F]
    rw [torusC64Reflection_sum, hf]
    ring
  have hPsum : ∑ z, P z = 0 := by
    dsimp [P]
    exact torusC64_reflectedPotential_sum_eq_zero L y₀ y₁
  have hD2 : torusC64Backward2 P = F := by
    funext z
    exact torusC64Backward2_reflectedPotential_eq_reflection_source
      L y₀ y₁ hy₀ hy₁ z
  have hGsym₁ : ∀ z, (torusGraph (2 * L) hside).greenOp hT F
      (torusC64ReflectFirst L z) =
        (torusGraph (2 * L) hside).greenOp hT F z := by
    exact torusGreenOp_reflection_first hside hT f hf
  have hGsym₂ : ∀ z, (torusGraph (2 * L) hside).greenOp hT F
      (torusC64ReflectSecond L z) =
        (torusGraph (2 * L) hside).greenOp hT F z := by
    exact torusGreenOp_reflection_second hside hT f hf
  have hGneg₁ : ∀ z, (-(torusGraph (2 * L) hside).greenOp hT F)
      (torusC64ReflectFirst L z) =
        (-(torusGraph (2 * L) hside).greenOp hT F) z := by
    intro z
    exact congrArg Neg.neg (hGsym₁ z)
  have hGneg₂ : ∀ z, (-(torusGraph (2 * L) hside).greenOp hT F)
      (torusC64ReflectSecond L z) =
        (-(torusGraph (2 * L) hside).greenOp hT F) z := by
    intro z
    exact congrArg Neg.neg (hGsym₂ z)
  have hfreePair := squareFree_greenBilinear_eq_restricted_periodic_pairing
    hside hT hG f hf
  have hD2Energy :
      greenBilinear (torusGraph (2 * L) hside) hT
          (torusC64Backward2 P) (torusC64Backward2 P) =
        4 * greenBilinear (squareFreeGraph L) hG f f := by
    rw [hD2]
    calc
      _ = pairing F (-(torusGraph (2 * L) hside).greenOp hT F) := rfl
      _ = 4 * pairing f (torusC64FreeRestrict
          (-(torusGraph (2 * L) hside).greenOp hT F)) :=
        torusC64_pairing_reflection_transfer f
          (-(torusGraph (2 * L) hside).greenOp hT F) hGneg₁ hGneg₂
      _ = 4 * greenBilinear (squareFreeGraph L) hG f f := by
        have hrestrict : torusC64FreeRestrict
            (-(torusGraph (2 * L) hside).greenOp hT F) =
            (fun v => -torusC64FreeRestrict
              ((torusGraph (2 * L) hside).greenOp hT F) v) := rfl
        rw [hrestrict, ← hfreePair]
  have hnorm : pairing P P = 4 * (L - y₀ : ℝ) := by
    unfold pairing
    simpa [pow_two] using torusC64_reflectedPotential_sq_sum
      L y₀ y₁ hy₀ hy₁
  have hdecomp := torusC64_greenBilinear_hodge_identity hside hT P hPsum
  have hE₁ := torusC64_reflectedPotential_backward1_energy_log_upper_bound
    L y₀ y₁ hside hT hy₀
  have htotal : 4 * (L - y₀ : ℝ) =
      greenBilinear (torusGraph (2 * L) hside) hT
        (torusC64Backward1 P) (torusC64Backward1 P) +
      4 * greenBilinear (squareFreeGraph L) hG f f := by
    calc
      _ = pairing P P := hnorm.symm
      _ = greenBilinear (torusGraph (2 * L) hside) hT
          (torusC64Backward1 P) (torusC64Backward1 P) +
          greenBilinear (torusGraph (2 * L) hside) hT
            (torusC64Backward2 P) (torusC64Backward2 P) := hdecomp
      _ = _ := by rw [hD2Energy]
  have hlog : 0 ≤ Real.log (((N + 1 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_pos N
  dsimp [N, f]
  have hfinal :
      4 * greenBilinear (squareFreeGraph L) hG
          (squareFreeLineSource L y₀ y₁) (squareFreeLineSource L y₀ y₁) ≥
        4 * (L - y₀ : ℝ) - 656 * Real.log (((N + 1 : ℕ) : ℝ)) := by
    rw [show (((N + 1 : ℕ) : ℝ)) = (((L - y₀ + 1 : ℕ) : ℝ)) by rfl]
    nlinarith only [htotal, hE₁]
  have hfinal' :
      4 * greenBilinear (squareFreeGraph L) hG
          (squareFreeLineSource L y₀ y₁) (squareFreeLineSource L y₀ y₁) ≥
        4 * (L - y₀ : ℝ) - 656 * Real.log (((L - y₀ + 1 : ℕ) : ℝ)) := by
    simpa [N] using hfinal
  have hNcast : ((L - y₀ : ℕ) : ℝ) = (L : ℝ) - y₀ := by
    rw [Nat.cast_sub (by omega : y₀ ≤ L)]
  rw [← hNcast] at hfinal'
  nlinarith only [hfinal']

/-- Exact C6.4 decomposition with the corrected reflected-strip endpoints:
`Q(f_y) = N - C`, where `C` is one quarter of the periodic Green energy of
the horizontal difference of the reflected strip potential. The endpoint
formula for that difference uses both dipoles of length `2N`. -/
theorem squareFreeLineSource_energy_eq_N_sub_reflectedCorrection
    (L y₀ y₁ : ℕ) [NeZero (2 * L)]
    (hL : 1 < L) (hy₀ : y₀ < L) (hy₁ : y₁ + 1 < L)
    (hG : (squareFreeGraph L).Connected) :
    greenBilinear (squareFreeGraph L) hG
      (squareFreeLineSource L y₀ y₁) (squareFreeLineSource L y₀ y₁) =
      ((L - y₀ : ℕ) : ℝ) - (1 / 4 : ℝ) *
        greenBilinear (torusGraph (2 * L) (by omega))
          (torusGraph_connected (2 * L) (by omega))
          (torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁))
          (torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁)) := by
  let hside : 2 < 2 * L := by omega
  let hT : (torusGraph (2 * L) hside).Connected := torusGraph_connected (2 * L) hside
  let f : SquareFreeVertex L → ℝ := squareFreeLineSource L y₀ y₁
  let F : TorusVertex (2 * L) → ℝ := torusC64Reflection L f
  let P : TorusVertex (2 * L) → ℝ := torusC64ReflectedPotential L y₀ y₁
  have hf : ∑ v, f v = 0 := by
    exact squareFreeLineSource_sum_eq_zero L y₀ y₁ hy₁
  have hFsum : ∑ z, F z = 0 := by
    dsimp [F]
    rw [torusC64Reflection_sum, hf]
    ring
  have hPsum : ∑ z, P z = 0 := by
    dsimp [P]
    exact torusC64_reflectedPotential_sum_eq_zero L y₀ y₁
  have hD2 : torusC64Backward2 P = F := by
    funext z
    exact torusC64Backward2_reflectedPotential_eq_reflection_source
      L y₀ y₁ hy₀ hy₁ z
  have hGsym₁ : ∀ z, (torusGraph (2 * L) hside).greenOp hT F
      (torusC64ReflectFirst L z) =
        (torusGraph (2 * L) hside).greenOp hT F z :=
    torusGreenOp_reflection_first hside hT f hf
  have hGsym₂ : ∀ z, (torusGraph (2 * L) hside).greenOp hT F
      (torusC64ReflectSecond L z) =
        (torusGraph (2 * L) hside).greenOp hT F z :=
    torusGreenOp_reflection_second hside hT f hf
  have hGneg₁ : ∀ z, (-(torusGraph (2 * L) hside).greenOp hT F)
      (torusC64ReflectFirst L z) =
        (-(torusGraph (2 * L) hside).greenOp hT F) z := by
    intro z
    exact congrArg Neg.neg (hGsym₁ z)
  have hGneg₂ : ∀ z, (-(torusGraph (2 * L) hside).greenOp hT F)
      (torusC64ReflectSecond L z) =
        (-(torusGraph (2 * L) hside).greenOp hT F) z := by
    intro z
    exact congrArg Neg.neg (hGsym₂ z)
  have hfreePair := squareFree_greenBilinear_eq_restricted_periodic_pairing
    hside hT hG f hf
  have hD2Energy :
      greenBilinear (torusGraph (2 * L) hside) hT
          (torusC64Backward2 P) (torusC64Backward2 P) =
        4 * greenBilinear (squareFreeGraph L) hG f f := by
    rw [hD2]
    calc
      _ = pairing F (-(torusGraph (2 * L) hside).greenOp hT F) := rfl
      _ = 4 * pairing f (torusC64FreeRestrict
          (-(torusGraph (2 * L) hside).greenOp hT F)) :=
        torusC64_pairing_reflection_transfer f
          (-(torusGraph (2 * L) hside).greenOp hT F) hGneg₁ hGneg₂
      _ = 4 * greenBilinear (squareFreeGraph L) hG f f := by
        have hrestrict : torusC64FreeRestrict
            (-(torusGraph (2 * L) hside).greenOp hT F) =
            (fun v => -torusC64FreeRestrict
              ((torusGraph (2 * L) hside).greenOp hT F) v) := rfl
        rw [hrestrict, ← hfreePair]
  have hnorm : pairing P P = 4 * (L - y₀ : ℝ) := by
    unfold pairing
    simpa [pow_two] using torusC64_reflectedPotential_sq_sum
      L y₀ y₁ hy₀ hy₁
  have hdecomp := torusC64_greenBilinear_hodge_identity hside hT P hPsum
  have htotal : 4 * (L - y₀ : ℝ) =
      greenBilinear (torusGraph (2 * L) hside) hT
        (torusC64Backward1 P) (torusC64Backward1 P) +
      4 * greenBilinear (squareFreeGraph L) hG f f := by
    calc
      _ = pairing P P := hnorm.symm
      _ = greenBilinear (torusGraph (2 * L) hside) hT
          (torusC64Backward1 P) (torusC64Backward1 P) +
          greenBilinear (torusGraph (2 * L) hside) hT
            (torusC64Backward2 P) (torusC64Backward2 P) := hdecomp
      _ = _ := by rw [hD2Energy]
  have hNcast : ((L - y₀ : ℕ) : ℝ) = (L : ℝ) - y₀ := by
    rw [Nat.cast_sub (by omega : y₀ ≤ L)]
  change greenBilinear (squareFreeGraph L) hG
      (squareFreeLineSource L y₀ y₁) (squareFreeLineSource L y₀ y₁) =
      ((L - y₀ : ℕ) : ℝ) - (1 / 4 : ℝ) *
        greenBilinear (torusGraph (2 * L) hside) hT
          (torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁))
          (torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁))
  nlinarith only [htotal, hNcast]

/-- The exact internal-carrier form consumed by the KP Claim 6.4 reduction.
The stronger estimate above uses constant 164, hence implies the requested
constant 656 including the `N = 1` case. -/
theorem c64Statement_656_proof : FroehlichSpencer.BKT.Reduction.c64Statement 656 := by
  intro L y₀ y₁ hF hL hy₀ hy₁
  have hn : NeZero (2 * L) := ⟨by omega⟩
  have h := @squareFreeLineSource_energy_lower_bound L y₀ y₁ hn hL hy₀ hy₁ hF
  have hlog : 0 ≤ Real.log (((L - y₀ + 1 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_pos (L - y₀)
  change ((L - y₀ : ℕ) : ℝ) - 656 * Real.log ((L - y₀ + 1 : ℕ) : ℝ) ≤ _
  nlinarith only [h, hlog]

private theorem torusC64_finCast_injective {L : ℕ} [NeZero (2 * L)]
    (i j : Fin L) (h : (i.val : ZMod (2 * L)) = (j.val : ZMod (2 * L))) : i = j := by
  apply Fin.ext
  have hv := congrArg ZMod.val h
  have hi : i.val < 2 * L := by have := i.isLt; omega
  have hj : j.val < 2 * L := by have := j.isLt; omega
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hv

private def torusC64_freeEdgeInjection {L : ℕ} [NeZero (2 * L)] :
    SquareFreeEdge L → TorusEdge (2 * L)
  | .inl e =>
      (torusC64FreeEmbed (⟨e.1.1.val + 1, e.1.2⟩, e.2) - (0, 1), true)
  | .inr e => (torusC64FreeEmbed (e.1, e.2.1), false)

private theorem torusC64FreeEmbed_horizontal_step {L : ℕ}
    (i : Fin L) (j : Fin L) (hi : i.val + 1 < L) :
    torusC64FreeEmbed (⟨i.val + 1, hi⟩, j) =
      torusC64FreeEmbed (i, j) + (1, 0) := by
  ext <;> simp [torusC64FreeEmbed]

private theorem torusC64FreeEmbed_vertical_step {L : ℕ}
    (i : Fin L) (j : Fin L) (hj : j.val + 1 < L) :
    torusC64FreeEmbed (i, ⟨j.val + 1, hj⟩) =
      torusC64FreeEmbed (i, j) + (0, 1) := by
  ext <;> simp [torusC64FreeEmbed]

private theorem torusC64_freeEdgeInjection_injective {L : ℕ} [NeZero (2 * L)] :
    Function.Injective (torusC64_freeEdgeInjection (L := L)) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hbase := congrArg Prod.fst hab
      have hx := congrArg Prod.fst hbase
      have hy := congrArg Prod.snd hbase
      have hx' : (a.1.1.val + 1 : ZMod (2 * L)) = (b.1.1.val + 1 : ZMod (2 * L)) := by
        simpa [torusC64_freeEdgeInjection, torusC64FreeEmbed] using hx
      have hxi : (a.1.1.val : ZMod (2 * L)) = (b.1.1.val : ZMod (2 * L)) :=
        add_right_cancel hx'
      have hy' : (a.2.val : ZMod (2 * L)) - 1 =
          (b.2.val : ZMod (2 * L)) - 1 := by
        simpa [torusC64_freeEdgeInjection, torusC64FreeEmbed] using hy
      have hyi : (a.2.val : ZMod (2 * L)) = (b.2.val : ZMod (2 * L)) := by
        have := congrArg (fun x : ZMod (2 * L) => x + 1) hy'
        simpa using this
      have hia := torusC64_finCast_injective a.1.1 b.1.1 hxi
      have hja := torusC64_finCast_injective a.2 b.2 hyi
      have hs : a.1 = b.1 := Subtype.ext hia
      have he : a = b := by
        apply Prod.ext
        · exact hs
        · exact hja
      exact congrArg Sum.inl he
    | inr b =>
      have hdir := congrArg Prod.snd hab
      simp [torusC64_freeEdgeInjection] at hdir
  | inr a =>
    cases b with
    | inl b =>
      have hdir := congrArg Prod.snd hab
      simp [torusC64_freeEdgeInjection] at hdir
    | inr b =>
      have hbase := congrArg Prod.fst hab
      have hx := congrArg Prod.fst hbase
      have hy := congrArg Prod.snd hbase
      have hx' : (a.1.val : ZMod (2 * L)) = (b.1.val : ZMod (2 * L)) := by
        simpa [torusC64_freeEdgeInjection, torusC64FreeEmbed] using hx
      have hy' : (a.2.1.val : ZMod (2 * L)) = (b.2.1.val : ZMod (2 * L)) := by
        simpa [torusC64_freeEdgeInjection, torusC64FreeEmbed] using hy
      have hia := torusC64_finCast_injective a.1 b.1 hx'
      have hja := torusC64_finCast_injective a.2.1 b.2.1 hy'
      have he : a = b := by
        apply Prod.ext
        · exact hia
        · exact Subtype.ext hja
      exact congrArg Sum.inr he

private theorem torusC64_modular_square_le (a b : ℝ)
    (hab : toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * a) =
      toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * b)) :
    toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * a) ^ 2 ≤
      (2 * Real.pi) ^ 2 * b ^ 2 := by
  rw [hab]
  have habs := abs_toIcoMod_le_abs (2 * Real.pi * b)
  have hsq : toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * b) ^ 2 ≤
      (2 * Real.pi * b) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 habs
    simpa only [sq_abs] using h
  nlinarith only [hsq]

private theorem torusC64_mod_sub_int_two_pi (t : ℝ) (k : ℤ) :
    toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * (t - k)) =
      toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * t) := by
  calc
    _ = toIcoMod Real.two_pi_pos (-Real.pi)
        (2 * Real.pi * t + ((-k : ℤ) : ℝ) * (2 * Real.pi)) := by
          congr 1
          push_cast
          ring
    _ = _ := toIcoMod_add_intCast_mul_two_pi _ _

private theorem torusC64_reflectedPotential_int (L y₀ y₁ : ℕ)
    [NeZero (2 * L)] (z : TorusVertex (2 * L)) :
    ∃ k : ℤ, torusC64ReflectedPotential L y₀ y₁ z = k := by
  unfold torusC64ReflectedPotential torusC64StripIndicator
  by_cases hs : y₀ ≤ z.1.val ∧ z.1.val < 2 * L - y₀
  · by_cases ha : z.2 = (y₁ : ZMod (2 * L))
    · by_cases hb : z.2 = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L))
      · have hab : (y₁ : ZMod (2 * L)) =
            ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) := ha.symm.trans hb
        exact ⟨0, by simp [hs, ha, hab]⟩
      · have hneq : ¬ ((y₁ : ZMod (2 * L)) =
            ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L))) := by
          intro h
          exact hb (ha.trans h)
        exact ⟨1, by simp [hs, ha, hneq]⟩
    · by_cases hb : z.2 = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L))
      · have hneq : ¬ ((y₁ : ZMod (2 * L)) =
            ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L))) := by
          intro h
          exact ha (hb.trans h.symm)
        have hneq' : ¬ (((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) =
            (y₁ : ZMod (2 * L))) := by
          intro h
          exact hneq h.symm
        exact ⟨-1, by simp [hs, hb, hneq']⟩
      · exact ⟨0, by simp [hs, ha, hb]⟩
  · exact ⟨0, by simp [hs]⟩

/-- KP Claim 6.3's reflected-energy interface on the internal free box. The
horizontal and vertical free edges inject into torus vertical and horizontal
edges respectively; the vertical formula removes the integer strip term
modulo `2π`. -/
theorem c63ReflectedEnergyStatement_proof :
    FroehlichSpencer.BKT.Reduction.c63ReflectedEnergyStatement := by
  intro L y₀ y₁ hNZ hside hT hF hL hy₀ hy₁
  let GF := squareFreeGraph L
  let GT := torusGraph (2 * L) hside
  let f : SquareFreeVertex L → ℝ := squareFreeLineSource L y₀ y₁
  let P : TorusVertex (2 * L) → ℝ := torusC64ReflectedPotential L y₀ y₁
  let g : TorusVertex (2 * L) → ℝ := GT.greenOp hT (torusC64Reflection L f)
  let u : TorusVertex (2 * L) → ℝ := -GT.greenOp hT (torusC64Backward1 P)
  have hf : ∑ v, f v = 0 := by
    dsimp [f]
    exact squareFreeLineSource_sum_eq_zero L y₀ y₁ hy₁
  have hPsum : ∑ z, P z = 0 := by
    dsimp [P]
    exact torusC64_reflectedPotential_sum_eq_zero L y₀ y₁
  have hD2 : torusC64Backward2 P = torusC64Reflection L f := by
    funext z
    dsimp [P, f]
    exact torusC64Backward2_reflectedPotential_eq_reflection_source
      L y₀ y₁ hy₀ hy₁ z
  have hFsum : ∑ z, torusC64Reflection L f z = 0 := by
    dsimp [f]
    rw [torusC64Reflection_sum, hf]
    ring
  have hbackcomm : torusC64Backward1 (torusC64Reflection L f) =
      torusC64Backward2 (torusC64Backward1 P) := by
    calc
      _ = torusC64Backward1 (torusC64Backward2 P) :=
        congrArg torusC64Backward1 hD2.symm
      _ = torusC64Backward2 (torusC64Backward1 P) := by
        funext z
        simp [torusC64Backward1, torusC64Backward2]
        abel_nf
  have hcross : torusC64Backward1 g = -torusC64Backward2 u := by
    calc
      _ = GT.greenOp hT (torusC64Backward1 (torusC64Reflection L f)) :=
        torusC64_greenOp_backward1 hside hT _ hFsum
      _ = GT.greenOp hT (torusC64Backward2 (torusC64Backward1 P)) := by
        rw [hbackcomm]
      _ = torusC64Backward2 (GT.greenOp hT (torusC64Backward1 P)) :=
        (torusC64_greenOp_backward2 hside hT _
          (torusC64_sum_backward1_eq_zero P)).symm
      _ = -torusC64Backward2 u := by
        funext z
        simp only [u, torusC64Backward2, Pi.neg_apply]
        ring
  have hhorizontal (z : TorusVertex (2 * L)) :
      torusC64Adjoint1 g z = torusC64Backward2 u (z + (1, 0)) := by
    have hz := congrFun hcross (z + (1, 0))
    dsimp [torusC64Backward1, torusC64Backward2] at hz
    have hcancel : z + (1, 0) - (1, 0) = z := by ext <;> simp
    rw [hcancel] at hz
    dsimp [torusC64Adjoint1, torusC64Backward2]
    linear_combination -hz
  have hgeq : g = GT.greenOp hT (torusC64Backward2 P) := by
    dsimp [g]
    exact congrArg (GT.greenOp hT) hD2.symm
  have hhodge := torusC64_hodge_identity hside hT P hPsum
  have hvertical (z : TorusVertex (2 * L)) :
      torusC64Adjoint2 g z = torusC64Adjoint1 u z - P z := by
    have hz := congrFun hhodge z
    rw [← hgeq] at hz
    dsimp [torusC64Adjoint1, torusC64Adjoint2, u] at hz ⊢
    linarith only [hz]
  have htransfer := squareFree_greenOp_reflection_transfer
    hside hT hF f hf
  have hfreeGreen (v : SquareFreeVertex L) :
      GF.greenOp hF f v = torusC64FreeRestrict g v -
        vertexMean (SquareFreeVertex L) (torusC64FreeRestrict g) := by
    exact htransfer v
  have hfreeHorizontal (e : SquareFreeHorizontalEdge L) :
      GF.grad (GF.greenOp hF f) (Sum.inl e) =
        torusC64Backward2 u
          (torusC64FreeEmbed (⟨e.1.1.val + 1, e.1.2⟩, e.2)) := by
    rcases e with ⟨⟨i, hi⟩, j⟩
    change GF.greenOp hF f (i, j) -
      GF.greenOp hF f (⟨i.val + 1, hi⟩, j) = _
    rw [hfreeGreen (i, j), hfreeGreen (⟨i.val + 1, hi⟩, j)]
    simp only [torusC64FreeRestrict]
    rw [torusC64FreeEmbed_horizontal_step]
    have hz := hhorizontal (torusC64FreeEmbed (i, j))
    dsimp [torusC64Adjoint1] at hz
    linarith only [hz]
  have hfreeVertical (e : SquareFreeVerticalEdge L) :
      GF.grad (GF.greenOp hF f) (Sum.inr e) =
        torusC64Adjoint1 u (torusC64FreeEmbed (e.1, e.2.1)) -
          P (torusC64FreeEmbed (e.1, e.2.1)) := by
    rcases e with ⟨i, ⟨j, hj⟩⟩
    change GF.greenOp hF f (i, j) -
      GF.greenOp hF f (i, ⟨j.val + 1, hj⟩) = _
    rw [hfreeGreen (i, j), hfreeGreen (i, ⟨j.val + 1, hj⟩)]
    simp only [torusC64FreeRestrict]
    rw [torusC64FreeEmbed_vertical_step]
    have hz := hvertical (torusC64FreeEmbed (i, j))
    dsimp [torusC64Adjoint2] at hz
    linarith only [hz]
  have htorusHorizontal (e : SquareFreeHorizontalEdge L) :
      GT.grad u (torusC64_freeEdgeInjection (Sum.inl e)) =
        -torusC64Backward2 u
          (torusC64FreeEmbed (⟨e.1.1.val + 1, e.1.2⟩, e.2)) := by
    rcases e with ⟨⟨i, hi⟩, j⟩
    simp [Multigraph.grad, GT, torusC64_freeEdgeInjection, torusStep,
      torusC64FreeEmbed, torusC64Backward2]
  have htorusVertical (e : SquareFreeVerticalEdge L) :
      GT.grad u (torusC64_freeEdgeInjection (Sum.inr e)) =
        torusC64Adjoint1 u (torusC64FreeEmbed (e.1, e.2.1)) := by
    rcases e with ⟨i, ⟨j, hj⟩⟩
    simp [Multigraph.grad, GT, torusC64_freeEdgeInjection, torusStep,
      torusC64FreeEmbed, torusC64Adjoint1]
  have hterm (e : SquareFreeEdge L) :
      toIcoMod Real.two_pi_pos (-Real.pi)
          (2 * Real.pi * GF.grad (GF.greenOp hF f) e) ^ 2 ≤
        (2 * Real.pi) ^ 2 * (GT.grad u (torusC64_freeEdgeInjection e)) ^ 2 := by
    cases e with
    | inl e =>
      rw [hfreeHorizontal e]
      have hmod := torusC64_modular_square_le
        (torusC64Backward2 u
          (torusC64FreeEmbed (⟨e.1.1.val + 1, e.1.2⟩, e.2))) _ rfl
      calc
        _ ≤ (2 * Real.pi) ^ 2 * torusC64Backward2 u
            (torusC64FreeEmbed (⟨e.1.1.val + 1, e.1.2⟩, e.2)) ^ 2 := hmod
        _ = _ := by rw [htorusHorizontal]; ring
    | inr e =>
      rcases e with ⟨i, ⟨j, hj⟩⟩
      let z := torusC64FreeEmbed (i, j)
      rw [hfreeVertical ⟨i, ⟨j, hj⟩⟩]
      obtain ⟨k, hk⟩ := torusC64_reflectedPotential_int L y₀ y₁ z
      have hmod : toIcoMod Real.two_pi_pos (-Real.pi)
          (2 * Real.pi * (torusC64Adjoint1 u z - P z)) =
            toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * torusC64Adjoint1 u z) := by
        have hk' : P z = (k : ℝ) := by simpa [P] using hk
        rw [hk']
        exact torusC64_mod_sub_int_two_pi (torusC64Adjoint1 u z) k
      have hbound := torusC64_modular_square_le
        (torusC64Adjoint1 u z - P z) (torusC64Adjoint1 u z) hmod
      calc
        _ ≤ (2 * Real.pi) ^ 2 * torusC64Adjoint1 u z ^ 2 := hbound
        _ = _ := by rw [htorusVertical]
  let q : TorusEdge (2 * L) → ℝ := fun e =>
    (2 * Real.pi) ^ 2 * (GT.grad u e) ^ 2
  have htermSum :
      ∑ e, toIcoMod Real.two_pi_pos (-Real.pi)
          (2 * Real.pi * GF.grad (GF.greenOp hF f) e) ^ 2 ≤
        ∑ e : SquareFreeEdge L, q (torusC64_freeEdgeInjection e) := by
    exact Finset.sum_le_sum fun e he => hterm e
  have hinj := torusC64_freeEdgeInjection_injective (L := L)
  have hsumImage :
      ∑ e : SquareFreeEdge L, q (torusC64_freeEdgeInjection e) =
        ∑ e ∈ Finset.univ.image torusC64_freeEdgeInjection, q e := by
    symm
    apply Finset.sum_image
    intro a ha b hb hab
    exact hinj hab
  have hsumSubset :
      ∑ e ∈ Finset.univ.image torusC64_freeEdgeInjection, q e ≤ ∑ e, q e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro e he hnot
    positivity
  have henergyU : GT.energy u =
      greenBilinear GT hT (torusC64Backward1 P) (torusC64Backward1 P) := by
    have henergy : GT.energy u = GT.energy (GT.greenOp hT (torusC64Backward1 P)) := by
      simp only [u, Multigraph.energy, Multigraph.grad, Pi.neg_apply]
      apply Finset.sum_congr rfl
      intro e he
      ring
    rw [henergy]
    exact (GT.pairing_eq_energy_greenOp hT (torusC64Backward1 P)
      (torusC64_sum_backward1_eq_zero P)).symm
  calc
    _ ≤ ∑ e : SquareFreeEdge L, q (torusC64_freeEdgeInjection e) := htermSum
    _ = ∑ e ∈ Finset.univ.image torusC64_freeEdgeInjection, q e := hsumImage
    _ ≤ ∑ e, q e := hsumSubset
    _ = (2 * Real.pi) ^ 2 * GT.energy u := by
      simp only [q, Multigraph.energy]
      rw [← Finset.mul_sum]
    _ = _ := by rw [henergyU]

end

end FroehlichSpencer.BKT.Lattice2D
