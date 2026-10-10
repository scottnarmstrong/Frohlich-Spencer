/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.C64

/-! # Free-to-periodic reflection for Claim 6.4 -/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D

namespace FroehlichSpencer.BKT.Lattice2D

/-- The real-valued torus Laplacian has the usual four-neighbor formula. -/
theorem torusLaplacian_neighbor_formula_real {n : ℕ} [NeZero n]
    (hn : 2 < n) (f : TorusVertex n → ℝ) (y : TorusVertex n) :
    (torusGraph n hn).laplacian f y =
      f (y + (1, 0)) + f (y - (1, 0)) +
      f (y + (0, 1)) + f (y - (0, 1)) - 4 * f y := by
  let fC : TorusVertex n → ℂ := fun z => (f z : ℂ)
  have h := torusLaplacian_neighbor_formula hn fC y
  have hmap : Complex.ofReal ((torusGraph n hn).laplacian f y) =
      (torusGraph n hn).laplacian fC y := by
    change Complex.ofRealHom (∑ e ∈ (Finset.univ : Finset (TorusEdge n)),
      ((if (torusGraph n hn).src e = y then
        f ((torusGraph n hn).tgt e) - f y else 0) +
       (if (torusGraph n hn).tgt e = y then
        f ((torusGraph n hn).src e) - f y else 0))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [map_add]
    by_cases hsrc : e.1 = y <;>
      by_cases htgt : torusStep n e.2 e.1 = y <;>
      simp [hsrc, htgt, fC, Complex.ofReal_sub]
  have hmre : ((torusGraph n hn).laplacian fC y).re =
      (torusGraph n hn).laplacian f y := by
    have hh := congrArg Complex.re hmap
    simpa using hh.symm
  have hr := congrArg Complex.re h
  calc
    (torusGraph n hn).laplacian f y =
        ((torusGraph n hn).laplacian fC y).re := hmre.symm
    _ = (fC (y + (1, 0)) + fC (y - (1, 0)) +
        fC (y + (0, 1)) + fC (y - (0, 1)) - 4 * fC y).re := hr
    _ = f (y + (1, 0)) + f (y - (1, 0)) +
        f (y + (0, 1)) + f (y - (0, 1)) - 4 * f y := by
      simp [fC]

/-- Sum of the horizontal edge contributions whose source is a fixed vertex. -/
theorem squareFreeHorizontal_source_sum (L : ℕ) (f : SquareFreeVertex L → ℝ) (x y : Fin L) :
    (∑ e : SquareFreeHorizontalEdge L,
      if e.1.1 = x ∧ e.2 = y then
        f (⟨e.1.1.val + 1, e.1.2⟩, e.2) - f (x,y) else 0) =
      if h : x.val + 1 < L then f (⟨x.val + 1, h⟩, y) - f (x,y) else 0 := by
  classical
  by_cases hx : x.val + 1 < L
  · let e₀ : SquareFreeHorizontalEdge L := (⟨x, hx⟩, y)
    have hc : ∀ e : SquareFreeHorizontalEdge L,
        (e.1.1 = x ∧ e.2 = y) = (e = e₀) := by
      intro e
      apply propext
      constructor
      · rintro ⟨h1,h2⟩
        apply Prod.ext
        · apply Subtype.ext
          exact h1
        · exact h2
      · intro h
        rw [h]
        exact ⟨rfl,rfl⟩
    simp_rw [hc]
    simp [e₀, hx]
  · have hzero : ∀ e : SquareFreeHorizontalEdge L,
        ¬ (e.1.1 = x ∧ e.2 = y) := by
      intro e he
      have hxval := congrArg Fin.val he.1
      have hbound := e.1.2
      omega
    simp [hzero, hx]

/-- Sum of the horizontal edge contributions whose target is a fixed vertex. -/
theorem squareFreeHorizontal_target_sum (L : ℕ) (f : SquareFreeVertex L → ℝ) (x y : Fin L) :
    (∑ e : SquareFreeHorizontalEdge L,
      if (⟨e.1.1.val + 1, e.1.2⟩ : Fin L) = x ∧ e.2 = y then
        f (e.1.1,e.2) - f (x,y) else 0) =
      if h : 0 < x.val then
        f (⟨x.val - 1, by have := x.isLt; omega⟩, y) - f (x,y) else 0 := by
  classical
  by_cases hx : 0 < x.val
  · have hxlt := x.isLt
    let xp : Fin L := ⟨x.val-1, by omega⟩
    have hpred : xp.val + 1 = x.val := by
      change x.val - 1 + 1 = x.val
      omega
    have hedge : xp.val + 1 < L := by rw [hpred]; exact hxlt
    let e₀ : SquareFreeHorizontalEdge L := (⟨xp, hedge⟩, y)
    have hc : ∀ e : SquareFreeHorizontalEdge L,
        ((⟨e.1.1.val + 1, e.1.2⟩ : Fin L) = x ∧ e.2 = y) = (e = e₀) := by
      intro e
      apply propext
      constructor
      · rintro ⟨h1,h2⟩
        apply Prod.ext
        · apply Subtype.ext
          have hv := congrArg Fin.val h1
          change e.1.1.val+1=x.val at hv
          apply Fin.ext
          change e.1.1.val = x.val - 1
          omega
        · exact h2
      · intro h
        rw [h]
        exact ⟨by apply Fin.ext; exact hpred, rfl⟩
    simp_rw [hc]
    simp [e₀, xp, hx]
  · have hxlt := x.isLt
    have hzero : ∀ e : SquareFreeHorizontalEdge L,
        ¬ ((⟨e.1.1.val + 1, e.1.2⟩ : Fin L) = x ∧ e.2 = y) := by
      intro e he
      have hv := congrArg Fin.val he.1
      change e.1.1.val+1=x.val at hv
      omega
    simp [hzero, hx]

/-- Sum of the vertical edge contributions whose source is a fixed vertex. -/
theorem squareFreeVertical_source_sum (L : ℕ) (f : SquareFreeVertex L → ℝ) (x y : Fin L) :
    (∑ e : SquareFreeVerticalEdge L,
      if e.1 = x ∧ e.2.1 = y then
        f (e.1, ⟨e.2.1.val + 1, e.2.2⟩) - f (x,y) else 0) =
      if h : y.val + 1 < L then f (x, ⟨y.val + 1, h⟩) - f (x,y) else 0 := by
  have hs := squareFreeHorizontal_source_sum L (fun v => f (v.2, v.1)) y x
  calc
    _ = ∑ e : SquareFreeHorizontalEdge L,
        if e.1.1 = y ∧ e.2 = x then
          (fun v => f (v.2,v.1)) (⟨e.1.1.val + 1, e.1.2⟩,e.2) -
            (fun v => f (v.2,v.1)) (y,x) else 0 := by
      apply Fintype.sum_equiv (Equiv.prodComm _ _)
      intro e
      rcases e with ⟨xidx, yidx⟩
      simp [Equiv.prodComm, and_comm]
    _ = _ := by simpa using hs

/-- Sum of the vertical edge contributions whose target is a fixed vertex. -/
theorem squareFreeVertical_target_sum (L : ℕ) (f : SquareFreeVertex L → ℝ) (x y : Fin L) :
    (∑ e : SquareFreeVerticalEdge L,
      if e.1 = x ∧ (⟨e.2.1.val + 1, e.2.2⟩ : Fin L) = y then
        f (e.1,e.2.1) - f (x,y) else 0) =
      if h : 0 < y.val then f (x, ⟨y.val - 1, by have := y.isLt; omega⟩) - f (x,y) else 0 := by
  have hs := squareFreeHorizontal_target_sum L (fun v => f (v.2, v.1)) y x
  calc
    _ = ∑ e : SquareFreeHorizontalEdge L,
        if (⟨e.1.1.val + 1, e.1.2⟩ : Fin L) = y ∧ e.2 = x then
          (fun v => f (v.2,v.1)) (e.1.1,e.2) -
            (fun v => f (v.2,v.1)) (y,x) else 0 := by
      apply Fintype.sum_equiv (Equiv.prodComm _ _)
      intro e
      rcases e with ⟨xidx, yidx⟩
      simp [Equiv.prodComm, and_comm]
    _ = _ := by simpa using hs

/-- The free-square graph Laplacian is the sum over its existing coordinate neighbors. -/
theorem squareFree_laplacian_neighbor_formula (L : ℕ) (f : SquareFreeVertex L → ℝ)
    (x y : Fin L) :
    (squareFreeGraph L).laplacian f (x, y) =
      (if h : 0 < x.val then f (⟨x.val - 1, by have := x.isLt; omega⟩, y) - f (x, y) else 0) +
      (if h : x.val + 1 < L then f (⟨x.val + 1, h⟩, y) - f (x, y) else 0) +
      (if h : 0 < y.val then f (x, ⟨y.val - 1, by have := y.isLt; omega⟩) - f (x, y) else 0) +
      (if h : y.val + 1 < L then f (x, ⟨y.val + 1, h⟩) - f (x, y) else 0) := by
  classical
  simp only [Multigraph.laplacian, squareFreeGraph, Fintype.sum_sum_type,
    Prod.mk.injEq, Finset.sum_add_distrib]
  rw [squareFreeHorizontal_source_sum, squareFreeHorizontal_target_sum, squareFreeVertical_source_sum, squareFreeVertical_target_sum]
  ring

/-- Fold a cyclic coordinate in the `2L` torus back to the free interval. -/
def torusC64FoldIndex (L : ℕ) [NeZero (2 * L)] (a : ZMod (2 * L)) : Fin L :=
  ⟨min a.val (2 * L - 1 - a.val), by
    have ha := a.val_lt
    by_cases h : a.val ≤ 2 * L - 1 - a.val
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (Nat.le_of_not_ge h)]
      omega⟩

/-- On the first half of the torus, folding is the identity. -/
theorem torusC64FoldIndex_of_lt (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) (ha : a.val < L) :
    torusC64FoldIndex L a = ⟨a.val, ha⟩ := by
  apply Fin.ext
  simp only [torusC64FoldIndex, Fin.val_mk]
  rw [Nat.min_eq_left]
  omega

/-- On the reflected half of the torus, folding reverses the coordinate. -/
theorem torusC64FoldIndex_of_ge (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) (ha : L ≤ a.val) :
    torusC64FoldIndex L a = ⟨2 * L - 1 - a.val, by
      have hav := a.val_lt
      omega⟩ := by
  apply Fin.ext
  have hav := a.val_lt
  simp only [torusC64FoldIndex, Fin.val_mk]
  rw [Nat.min_eq_right (by omega)]

/-- The value of the forward cyclic neighbor in a nontrivial even torus. -/
theorem torusC64_add_one_val (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    (a + 1).val = if a.val + 1 < 2 * L then a.val + 1 else 0 := by
  rw [ZMod.val_add, ZMod.val_one'' (by have := NeZero.pos (2 * L); omega)]
  by_cases h : a.val + 1 < 2 * L
  · simp only [ite_eq_left h]
    exact Nat.mod_eq_of_lt h
  · have heq : a.val + 1 = 2 * L := by have := a.val_lt; omega
    simp [heq, Nat.mod_self]

/-- The value of the backward cyclic neighbor in a nontrivial even torus. -/
theorem torusC64_sub_one_val (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    (a - 1).val = if a.val = 0 then 2 * L - 1 else a.val - 1 := by
  by_cases h : a.val = 0
  · have ha : a = 0 := ZMod.val_injective (2 * L) (by simpa using h)
    subst a
    have hOneNe : (1 : ZMod (2 * L)) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_one'' (by have := NeZero.pos (2 * L); omega)] at hv
      simp at hv
    rw [show (0 : ZMod (2 * L)) - 1 = -(1 : ZMod (2 * L)) by ring]
    rw [ZMod.neg_val]
    simp [ZMod.val_one'', hOneNe]
  · have hpos : 0 < a.val := Nat.pos_of_ne_zero h
    rw [ZMod.val_sub (by rw [ZMod.val_one'' (by have := NeZero.pos (2 * L); omega)]; omega),
      ZMod.val_one'' (by have := NeZero.pos (2 * L); omega)]
    simp [h]

/-- Folding after a forward cyclic step gives the next folded free index. -/
theorem torusC64FoldIndex_add_one (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    (torusC64FoldIndex L (a + 1)).val =
      if a.val + 1 < L then a.val + 1
      else if a.val + 1 < 2 * L then 2 * L - 2 - a.val else 0 := by
  have hav := a.val_lt
  simp only [torusC64FoldIndex, Fin.val_mk]
  rw [torusC64_add_one_val]
  by_cases h : a.val + 1 < L
  · have htop : a.val + 1 < 2 * L := by omega
    simp only [ite_eq_left h, ite_eq_left htop]
    rw [Nat.min_eq_left (by omega)]
  · by_cases htop : a.val + 1 < 2 * L
    · simp only [ite_eq_right h, ite_eq_left htop]
      rw [Nat.min_eq_right (by omega)]
      omega
    · have heq : a.val + 1 = 2 * L := by omega
      simp only [ite_eq_right h, ite_eq_right htop]
      simp

/-- Folding after a backward cyclic step gives the previous folded free
index, with the endpoint `0` wrapping back to itself. -/
theorem torusC64FoldIndex_sub_one (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    (torusC64FoldIndex L (a - 1)).val =
      if a.val = 0 then 0 else if a.val ≤ L then a.val - 1 else 2 * L - a.val := by
  have hav := a.val_lt
  simp only [torusC64FoldIndex, Fin.val_mk]
  rw [torusC64_sub_one_val]
  by_cases hz : a.val = 0
  · simp only [ite_eq_left hz]
    rw [Nat.min_eq_right (by omega)]
    omega
  · simp only [ite_eq_right hz]
    by_cases hle : a.val ≤ L
    · simp only [ite_eq_left hle]
      rw [Nat.min_eq_left (by omega)]
    · simp only [ite_eq_right hle]
      rw [Nat.min_eq_right (by omega)]
      omega

/-- The folded coordinate is the usual triangular wave on the cyclic
representative. -/
theorem torusC64FoldIndex_val (L : ℕ) [NeZero (2 * L)]
    (a : ZMod (2 * L)) :
    (torusC64FoldIndex L a).val =
      if a.val < L then a.val else 2 * L - 1 - a.val := by
  by_cases h : a.val < L
  · rw [ite_eq_left h, torusC64FoldIndex_of_lt L a h]
  · have hL : L ≤ a.val := Nat.le_of_not_gt h
    rw [ite_eq_right h, torusC64FoldIndex_of_ge L a hL]

/-- The free-to-periodic reflection `T_fp` from KP (6.9), using the
edge-centered even extension on each coordinate. -/
def torusC64Reflection (L : ℕ) [NeZero (2 * L)]
    (f : SquareFreeVertex L → ℝ) (z : TorusVertex (2 * L)) : ℝ :=
  f (torusC64FoldIndex L z.1, torusC64FoldIndex L z.2)

/-- The corrected free-square line source in KP (6.8), with `N=L-y₀`. -/
def squareFreeLineSource (L y₀ y₁ : ℕ) (v : SquareFreeVertex L) : ℝ :=
  (if y₀ ≤ v.1.val ∧ v.2.val = y₁ then 1 else 0) -
    (if y₀ ≤ v.1.val ∧ v.2.val = y₁ + 1 then 1 else 0)


end FroehlichSpencer.BKT.Lattice2D

end
