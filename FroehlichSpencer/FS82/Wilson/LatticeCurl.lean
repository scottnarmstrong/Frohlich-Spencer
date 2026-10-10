/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeOperator
public import FroehlichSpencer.FS82.Gaussian.LatticePath

/-!
# Pointwise evaluation of the lattice coboundary

`sourceRealLatticeCoboundary q` evaluated at a cell `p` is the signed sum of the values of `q`
on the faces of `p` (`latticeCurl`). Cells are then parametrized by an axis pattern
`Bool × Bool × Bool × Bool` (which coordinates are intervals) and a base point in `ℤ⁴`, and the
coboundary of a link field with components along the axes 2 and 3 only is computed on every
pattern: it is `∂₂A₃ - ∂₃A₂` on `2–3` plaquettes, `∂ᵢAⱼ` on `i–j` plaquettes with `i ∈ {0,1}`,
`j ∈ {2,3}`, and zero on every other cell.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open Finset

/-- One face term of the lattice coboundary of `F` at the cell `p`. -/
@[expose] noncomputable def latticeCurlTerm (F : LatticeCell 4 → ℝ) (p : LatticeCell 4)
    (i : Fin 4) : ℝ :=
  match p i with
  | Sum.inl _ => 0
  | Sum.inr t =>
      (-1 : ℝ) ^ latticeRankBefore p i *
        (F (latticeUpperFace p i t) - F (latticeLowerFace p i t))

/-- The lattice coboundary of a cell function, evaluated at the cell `p`. -/
@[expose] noncomputable def latticeCurl (F : LatticeCell 4 → ℝ) (p : LatticeCell 4) : ℝ :=
  ∑ i : Fin 4, latticeCurlTerm F p i

theorem latticeCurlTerm_add (F G : LatticeCell 4 → ℝ) (p : LatticeCell 4) (i : Fin 4) :
    latticeCurlTerm (fun c => F c + G c) p i = latticeCurlTerm F p i + latticeCurlTerm G p i := by
  unfold latticeCurlTerm
  cases p i with
  | inl s => simp
  | inr t => simp only; ring

theorem latticeCurl_add (F G : LatticeCell 4 → ℝ) (p : LatticeCell 4) :
    latticeCurl (fun c => F c + G c) p = latticeCurl F p + latticeCurl G p := by
  unfold latticeCurl
  rw [← sum_add_distrib]
  exact sum_congr rfl fun i _ => latticeCurlTerm_add F G p i

theorem latticeCurlTerm_neg (F : LatticeCell 4 → ℝ) (p : LatticeCell 4) (i : Fin 4) :
    latticeCurlTerm (fun c => -F c) p i = -latticeCurlTerm F p i := by
  unfold latticeCurlTerm
  cases p i with
  | inl s => simp
  | inr t => simp only; ring

theorem latticeCurl_neg (F : LatticeCell 4 → ℝ) (p : LatticeCell 4) :
    latticeCurl (fun c => -F c) p = -latticeCurl F p := by
  unfold latticeCurl
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun i _ => latticeCurlTerm_neg F p i

theorem latticeCurl_zero (p : LatticeCell 4) : latticeCurl (fun _ => 0) p = 0 := by
  unfold latticeCurl
  refine sum_eq_zero fun i _ => ?_
  unfold latticeCurlTerm
  cases p i with
  | inl s => rfl
  | inr t => simp

theorem latticeCurl_single (c : LatticeCell 4) (a : ℝ) (p : LatticeCell 4) :
    latticeCurl (fun x => (Finsupp.single c a : RealLatticeChain 4) x) p =
      a * ((latticeBoundaryBasis p c : ℤ) : ℝ) := by
  classical
  have e1 : ∀ x : LatticeCell 4,
      (Finsupp.single x (1 : ℤ) : LatticeChain 4) c = if c = x then 1 else 0 := by
    intro x
    rw [Finsupp.single_apply]
    by_cases h : x = c
    · simp [h]
    · simp [h, Ne.symm h]
  unfold latticeCurl latticeBoundaryBasis
  rw [Finsupp.finsetSum_apply]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  unfold latticeCurlTerm
  cases p i with
  | inl s => simp
  | inr t =>
    simp only [Finsupp.smul_apply, Finsupp.sub_apply, latticeBasis, e1, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring

/-- The real lattice coboundary evaluated at a cell is the signed sum over its faces. -/
theorem sourceRealLatticeCoboundary_apply (q : RealLatticeChain 4) (p : LatticeCell 4) :
    sourceRealLatticeCoboundary q p = latticeCurl (fun c => q c) p := by
  induction q using Finsupp.induction_linear with
  | zero => simp [latticeCurl_zero]
  | add q r hq hr =>
    rw [map_add, Finsupp.add_apply, hq, hr, ← latticeCurl_add]
    rfl
  | single c a =>
    rw [sourceRealLatticeCoboundary_single, latticeCurl_single, Finsupp.smul_apply,
      castLatticeChain_apply, latticeCoboundaryBasis_transpose, smul_eq_mul]

/-! ### Cells by axis pattern and base point -/

/-- The lattice coordinate with base `t`: the interval `[t, t+1]` if `b`, the point `t`
otherwise. -/
@[expose] def latticeCoordOf (b : Bool) (t : ℤ) : LatticeCoord :=
  match b with
  | true => Sum.inr t
  | false => Sum.inl t

/-- The base of a lattice coordinate. -/
@[expose] def latticeCoordBase (x : LatticeCoord) : ℤ := Sum.elim id id x

/-- The lattice cell with axis pattern `a` (which coordinates are intervals) and base `y`. -/
@[expose] def latticeCellOf (a : Bool × Bool × Bool × Bool) (y : ℤ × ℤ × ℤ × ℤ) : LatticeCell 4 :=
  ![latticeCoordOf a.1 y.1, latticeCoordOf a.2.1 y.2.1, latticeCoordOf a.2.2.1 y.2.2.1,
    latticeCoordOf a.2.2.2 y.2.2.2]

theorem latticeCoordOf_isRight_base (x : LatticeCoord) :
    latticeCoordOf x.isRight (latticeCoordBase x) = x := by
  cases x <;> rfl

/-- Every lattice cell is the cell of its axis pattern and base point. -/
theorem latticeCellOf_pattern_base (p : LatticeCell 4) :
    latticeCellOf ((p 0).isRight, (p 1).isRight, (p 2).isRight, (p 3).isRight)
      (latticeCoordBase (p 0), latticeCoordBase (p 1), latticeCoordBase (p 2),
        latticeCoordBase (p 3)) = p := by
  funext i
  fin_cases i <;> simp [latticeCellOf, latticeCoordOf_isRight_base]

/-- A link field with components along the axes 2 and 3 only, as a function on lattice
cells: `A₂` on links along axis 2, `A₃` on links along axis 3, zero on every other cell. -/
@[expose] noncomputable def linkField23 (A₂ A₃ : ℤ → ℤ → ℤ → ℤ → ℝ) (c : LatticeCell 4) : ℝ :=
  match c 0, c 1, c 2, c 3 with
  | Sum.inl y₀, Sum.inl y₁, Sum.inr y₂, Sum.inl y₃ => A₂ y₀ y₁ y₂ y₃
  | Sum.inl y₀, Sum.inl y₁, Sum.inl y₂, Sum.inr y₃ => A₃ y₀ y₁ y₂ y₃
  | _, _, _, _ => 0

/-- A plaquette field supported on `2–3` plaquettes, as a function on lattice cells. -/
@[expose] noncomputable def plaquetteField23 (S : ℤ → ℤ → ℤ → ℤ → ℝ) (c : LatticeCell 4) : ℝ :=
  match c 0, c 1, c 2, c 3 with
  | Sum.inl y₀, Sum.inl y₁, Sum.inr y₂, Sum.inr y₃ => S y₀ y₁ y₂ y₃
  | _, _, _, _ => 0

theorem latticeIsEdge_latticeCoordOf (b : Bool) (t : ℤ) :
    latticeIsEdge (latticeCoordOf b t) ↔ b = true := by
  cases b <;> simp [latticeIsEdge, latticeCoordOf]

/-- The rank of an axis of a pattern cell counts the interval axes before it. -/
theorem latticeRankBefore_latticeCellOf (a₀ a₁ a₂ a₃ : Bool) (y : ℤ × ℤ × ℤ × ℤ) :
    latticeRankBefore (latticeCellOf (a₀, a₁, a₂, a₃) y) 0 = 0 ∧
    latticeRankBefore (latticeCellOf (a₀, a₁, a₂, a₃) y) 1 = a₀.toNat ∧
    latticeRankBefore (latticeCellOf (a₀, a₁, a₂, a₃) y) 2 = a₀.toNat + a₁.toNat ∧
    latticeRankBefore (latticeCellOf (a₀, a₁, a₂, a₃) y) 3 = a₀.toNat + a₁.toNat + a₂.toNat := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold latticeRankBefore
    rw [Finset.card_filter, Fin.sum_univ_four]
    simp only [latticeCellOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      latticeIsEdge_latticeCoordOf]
    cases a₀ <;> cases a₁ <;> cases a₂ <;> cases a₃ <;> simp

/-- The coboundary of a link field along the axes 2 and 3, by axis pattern of the cell. -/
@[expose] noncomputable def curlPattern23 (A₂ A₃ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (a : Bool × Bool × Bool × Bool) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  match a with
  | (false, false, true, true) =>
      (A₃ y₀ y₁ (y₂ + 1) y₃ - A₃ y₀ y₁ y₂ y₃) - (A₂ y₀ y₁ y₂ (y₃ + 1) - A₂ y₀ y₁ y₂ y₃)
  | (true, false, true, false) => A₂ (y₀ + 1) y₁ y₂ y₃ - A₂ y₀ y₁ y₂ y₃
  | (true, false, false, true) => A₃ (y₀ + 1) y₁ y₂ y₃ - A₃ y₀ y₁ y₂ y₃
  | (false, true, true, false) => A₂ y₀ (y₁ + 1) y₂ y₃ - A₂ y₀ y₁ y₂ y₃
  | (false, true, false, true) => A₃ y₀ (y₁ + 1) y₂ y₃ - A₃ y₀ y₁ y₂ y₃
  | _ => 0

/-- The lattice coboundary of `linkField23 A₂ A₃` on the cell with pattern `a` and base `y`. -/
theorem latticeCurl_linkField23 (A₂ A₃ : ℤ → ℤ → ℤ → ℤ → ℝ) (a₀ a₁ a₂ a₃ : Bool)
    (y₀ y₁ y₂ y₃ : ℤ) :
    latticeCurl (linkField23 A₂ A₃) (latticeCellOf (a₀, a₁, a₂, a₃) (y₀, y₁, y₂, y₃)) =
      curlPattern23 A₂ A₃ (a₀, a₁, a₂, a₃) y₀ y₁ y₂ y₃ := by
  obtain ⟨r0, r1, r2, r3⟩ := latticeRankBefore_latticeCellOf a₀ a₁ a₂ a₃ (y₀, y₁, y₂, y₃)
  simp only [latticeCurl, latticeCurlTerm, Fin.sum_univ_four, r0, r1, r2, r3]
  cases a₀ <;> cases a₁ <;> cases a₂ <;> cases a₃
  all_goals
    simp [curlPattern23, latticeCellOf, latticeCoordOf, linkField23, latticeUpperFace,
      latticeLowerFace]
  ring

/-- `linkField23` on the cell with pattern `a` and base `y`. -/
theorem linkField23_latticeCellOf (A₂ A₃ : ℤ → ℤ → ℤ → ℤ → ℝ) (a₀ a₁ a₂ a₃ : Bool)
    (y₀ y₁ y₂ y₃ : ℤ) :
    linkField23 A₂ A₃ (latticeCellOf (a₀, a₁, a₂, a₃) (y₀, y₁, y₂, y₃)) =
      if (a₀, a₁, a₂, a₃) = (false, false, true, false) then A₂ y₀ y₁ y₂ y₃
      else if (a₀, a₁, a₂, a₃) = (false, false, false, true) then A₃ y₀ y₁ y₂ y₃ else 0 := by
  cases a₀ <;> cases a₁ <;> cases a₂ <;> cases a₃ <;>
    simp [latticeCellOf, latticeCoordOf, linkField23]

/-- `plaquetteField23` on the cell with pattern `a` and base `y`. -/
theorem plaquetteField23_latticeCellOf (S : ℤ → ℤ → ℤ → ℤ → ℝ) (a₀ a₁ a₂ a₃ : Bool)
    (y₀ y₁ y₂ y₃ : ℤ) :
    plaquetteField23 S (latticeCellOf (a₀, a₁, a₂, a₃) (y₀, y₁, y₂, y₃)) =
      if (a₀, a₁, a₂, a₃) = (false, false, true, true) then S y₀ y₁ y₂ y₃ else 0 := by
  cases a₀ <;> cases a₁ <;> cases a₂ <;> cases a₃ <;>
    simp [latticeCellOf, latticeCoordOf, plaquetteField23]

/-! ### Axis sets and orientation signs of pattern cells -/

theorem latticeCellAxes_latticeCellOf (a₀ a₁ a₂ a₃ : Bool) (y : ℤ × ℤ × ℤ × ℤ) :
    latticeCellAxes (latticeCellOf (a₀, a₁, a₂, a₃) y) =
      univ.filter fun i : Fin 4 => ![a₀, a₁, a₂, a₃] i = true := by
  ext i
  simp only [latticeCellAxes, mem_filter, mem_univ, true_and]
  fin_cases i <;> simp [latticeCellOf, latticeIsEdge_latticeCoordOf]

theorem latticeCellAxes_link₂ (y : ℤ × ℤ × ℤ × ℤ) :
    latticeCellAxes (latticeCellOf (false, false, true, false) y) = {2} := by
  rw [latticeCellAxes_latticeCellOf]
  decide

theorem latticeCellAxes_link₃ (y : ℤ × ℤ × ℤ × ℤ) :
    latticeCellAxes (latticeCellOf (false, false, false, true) y) = {3} := by
  rw [latticeCellAxes_latticeCellOf]
  decide

theorem latticeCellAxes_plaquette₂₃ (y : ℤ × ℤ × ℤ × ℤ) :
    latticeCellAxes (latticeCellOf (false, false, true, true) y) = {2, 3} := by
  rw [latticeCellAxes_latticeCellOf]
  decide

/-- The C2 orientation sign of a `2–3` plaquette is `-1`. -/
theorem latticeCellOrientationSign_plaquette₂₃ (y : ℤ × ℤ × ℤ × ℤ) :
    latticeCellOrientationSign (latticeCellOf (false, false, true, true) y) = -1 := by
  rw [latticeCellOrientationSign, latticeCellAxes_plaquette₂₃, axisSetOrientationSign]
  norm_num [Finset.sum_pair, Finset.card_pair]

end FroehlichSpencer.FS82.Wilson

end
