/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.Cube
public import FroehlichSpencer.FS82.Wilson.LoopResidual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The loop-field estimate on centred cubes

FS82 asserts without proof, after (2.88), that `(ε_Λ, ε_Λ) ≤ const (L + T)` as `Λ ↑ ℤ⁴`
(Fröhlich–Spencer (1982)), where `ε_Λ` is the residual of the
Wilson sheet `σ` after the Gaussian shift (2.50)–(2.51).

* `loopFieldResidual C σ` is `ε`: the residual of the orthogonal projection of `σ` onto
  `range C.d₁`.

Its squared norm is the minimum of `‖σ - d₁ τ‖²` over all link fields `τ`
  (`loopFieldResidual_normSq_isLeast`), and it is characterized by the two properties FS82 uses
  (`eq_loopFieldResidual`).
* `cubeSheet L T N` is `σ` on the dual plaquettes of the centred cube `cube N`, for the sheet
  `[0,L] × [0,T] × {0}²`; `cubeLoopShift L T N` is the explicit shift restricted to the links of
  the cube (lattice-oriented link values, no C2 twist).
* `cube_loopField_normSq_le`: for `max L T + 1 ≤ N`, `(ε, ε) ≤ 6 (L + T)` in the lattice complex
  `sourceLatticeComplex (B := cube N)`.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Moment.SourceConstructor
open Finset

/-! ### The residual of the Gaussian shift in a finite complex -/

section Residual

variable {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

/-- The loop field `ε` of FS82 (2.51) for a 2-form `σ`: the residual of the orthogonal projection
of `σ` onto the exact 2-forms `range d₁`. -/
@[expose] noncomputable def loopFieldResidual (C : ExactOneComplex V E P)
    (σ : EuclideanSpace ℝ P) : EuclideanSpace ℝ P :=
  σ - (LinearMap.range C.d₁).starProjection σ

/-- `(dα, ε) = 0`, as used in FS82 (2.52). -/
theorem loopFieldResidual_inner_exact (C : ExactOneComplex V E P) (σ : EuclideanSpace ℝ P)
    (α : EuclideanSpace ℝ E) : inner ℝ (loopFieldResidual C σ) (C.d₁ α) = 0 :=
  Submodule.starProjection_inner_eq_zero σ (C.d₁ α) (LinearMap.mem_range_self C.d₁ α)

/-- `dτ = σ - ε` for some link field `τ`, as in FS82 (2.51). -/
theorem exists_shift_eq_sub_loopFieldResidual (C : ExactOneComplex V E P)
    (σ : EuclideanSpace ℝ P) : ∃ τ : EuclideanSpace ℝ E, C.d₁ τ = σ - loopFieldResidual C σ := by
  obtain ⟨τ, hτ⟩ := Submodule.starProjection_apply_mem (LinearMap.range C.d₁) σ
  exact ⟨τ, by rw [hτ, loopFieldResidual]; abel⟩

/-- The two properties used by FS82 determine `ε`. -/
theorem eq_loopFieldResidual (C : ExactOneComplex V E P) (σ ε : EuclideanSpace ℝ P)
    (hshift : ∃ τ : EuclideanSpace ℝ E, C.d₁ τ = σ - ε)
    (horth : ∀ α : EuclideanSpace ℝ E, inner ℝ ε (C.d₁ α) = 0) :
    ε = loopFieldResidual C σ := by
  obtain ⟨τ, hτ⟩ := hshift
  have hproj : (LinearMap.range C.d₁).starProjection σ = σ - ε := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hτ ▸ LinearMap.mem_range_self C.d₁ τ) ?_
    rintro _ ⟨α, rfl⟩
    rw [sub_sub_cancel]
    exact horth α
  rw [loopFieldResidual, hproj, sub_sub_cancel]

/-- The residual is no longer than `σ - d₁ τ` for any link field `τ`. -/
theorem norm_loopFieldResidual_le (C : ExactOneComplex V E P) (σ : EuclideanSpace ℝ P)
    (τ : EuclideanSpace ℝ E) : ‖loopFieldResidual C σ‖ ≤ ‖σ - C.d₁ τ‖ := by
  rw [loopFieldResidual, Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    (⟨C.d₁ τ, LinearMap.mem_range_self C.d₁ τ⟩ : LinearMap.range C.d₁)


end Residual

/-! ### Lattice cells inside the centred cube -/

/-- A lattice coordinate lies in the C1 image of the centred cube `cube N`: points in
`{-N+1, …, N}`, intervals based in `{-N, …, N}`. -/
@[expose] def CubeCoord (N : ℕ) (x : LatticeCoord) : Prop :=
  Sum.elim (fun v : ℤ => -(N : ℤ) + 1 ≤ v ∧ v ≤ (N : ℤ))
    (fun t : ℤ => -(N : ℤ) ≤ t ∧ t ≤ (N : ℤ)) x

theorem exists_dualCoord_of_cubeCoord (N : ℕ) (i : Fin 4) (x : LatticeCoord)
    (hx : CubeCoord N x) :
    ∃ d : DualCoord (cube N) i, dualEmbedCoord (B := cube N) (cubeOrigin N) i d = x := by
  cases x with
  | inl v =>
    have hv : -(N : ℤ) + 1 ≤ v ∧ v ≤ (N : ℤ) := hx
    refine ⟨Sum.inl ⟨(v + N - 1).toNat, by show _ < 2 * N; omega⟩, ?_⟩
    show Sum.inl (cubeOrigin N i + ((v + N - 1).toNat : ℤ) + 1) = Sum.inl v
    simp only [cubeOrigin]
    congr 1
    omega
  | inr t =>
    have ht : -(N : ℤ) ≤ t ∧ t ≤ (N : ℤ) := hx
    refine ⟨Sum.inr ⟨(t + N).toNat, by show _ < 2 * N + 1; omega⟩, ?_⟩
    show Sum.inr (cubeOrigin N i + ((t + N).toNat : ℤ)) = Sum.inr t
    simp only [cubeOrigin]
    congr 1
    omega

theorem exists_dualCell_of_cubeCoord (N : ℕ) (c : LatticeCell 4)
    (hc : ∀ i, CubeCoord N (c i)) :
    ∃ d : DualCell 4 (cube N), dualCellEmbedding (cubeOrigin N) d = c := by
  choose d hd using fun i => exists_dualCoord_of_cubeCoord N i (c i) (hc i)
  exact ⟨d, funext hd⟩

/-- A lattice link with coordinates in the cube is a link of `Λ*`. -/
theorem mem_range_cubeLinks (N : ℕ) (c : LatticeCell 4) (hc : ∀ i, CubeCoord N (c i))
    (hdeg : (latticeCellAxes c).card = 1) :
    c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
  obtain ⟨d, rfl⟩ := exists_dualCell_of_cubeCoord N c hc
  rw [latticeCellAxes_physical] at hdeg
  exact ⟨⟨d, hdeg⟩, rfl⟩


/-- The explicit shift is supported on the links of `cube N` once `max L T ≤ N`. -/
theorem loopShiftCell_support_cube {L T N : ℕ} (hN : max L T ≤ N) {c : LatticeCell 4}
    (h : loopShiftCell L T c ≠ 0) :
    c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
  obtain ⟨y₀, y₁, y₂, y₃, hc, h₀, h₁, h₂, h₃⟩ := loopShiftCell_ne_zero h
  have hL : (L : ℤ) ≤ N := by omega
  have hT : (T : ℤ) ≤ N := by omega
  rcases hc with rfl | rfl
  · refine mem_range_cubeLinks N _ ?_ (by rw [latticeCellAxes_link₂]; rfl)
    intro i
    fin_cases i <;> simp [latticeCellOf, latticeCoordOf, CubeCoord] <;> omega
  · refine mem_range_cubeLinks N _ ?_ (by rw [latticeCellAxes_link₃]; rfl)
    intro i
    fin_cases i <;> simp [latticeCellOf, latticeCoordOf, CubeCoord] <;> omega


/-! ### The sheet and the shift on the cube -/

/-- The Wilson sheet on the dual plaquettes of the centred cube: `σ(p*) = 1` for the plaquettes
`p` of the sheet `[0,L] × [0,T] × {0}²` (FS82 (2.49)). The coordinates are those of the 2-cells
of `sourceLatticeComplex`, which carry the source (star) orientation: `d₁` of a link field is the
orientation sign times the lattice coboundary (`latticeExactOneComplex_d₁_apply`), and that sign
is `-1` on `2–3` plaquettes. Replacing `σ` by `-σ` changes no norm below. -/
@[expose] noncomputable def cubeSheet (L T N : ℕ) :
    EuclideanSpace ℝ (SourceDualTwoCells (cube N)) :=
  WithLp.toLp 2 fun f => sheetCell L T (cubePlaquetteEmbedding N f)

/-- The explicit shift on the links of the centred cube, in the lattice-oriented link
coordinates of `sourceLatticeComplex` (the C1 compression; no C2 twist). The overall sign is the
orientation sign `-1` of `2–3` plaquettes. -/
@[expose] noncomputable def cubeLoopShift (L T N : ℕ) :
    EuclideanSpace ℝ (SourceDualOneCells (cube N)) :=
  WithLp.toLp 2 fun e => -loopShiftCell L T (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e)

/-- The value of `cubeSheet` in the index coordinates of the cube. A dual vertex index `v` on an
axis is the primal interval `[v - N, v - N + 1]` and a dual interval index `e` is the primal
point `e - N`, so the condition says that the dual plaquette is `p*` for the primal plaquette
`p = [x₀, x₀+1] × [x₁, x₁+1] × {0} × {0}` with `0 ≤ x₀ < L`, `0 ≤ x₁ < T`. -/
theorem cubeSheet_apply (L T N : ℕ) (f : SourceDualTwoCells (cube N)) :
    cubeSheet L T N f =
      if (∃ v, f.1 0 = Sum.inl v ∧ N ≤ v.val ∧ v.val < N + L) ∧
          (∃ v, f.1 1 = Sum.inl v ∧ N ≤ v.val ∧ v.val < N + T) ∧
          (∃ e, f.1 2 = Sum.inr e ∧ e.val = N) ∧ (∃ e, f.1 3 = Sum.inr e ∧ e.val = N)
      then 1 else 0 := by
  change sheetCell L T (dualCellEmbedding (cubeOrigin N) f.1) = _
  unfold sheetCell plaquetteField23
  change (match dualEmbedCoord (B := cube N) (cubeOrigin N) 0 (f.1 0),
      dualEmbedCoord (B := cube N) (cubeOrigin N) 1 (f.1 1),
      dualEmbedCoord (B := cube N) (cubeOrigin N) 2 (f.1 2),
      dualEmbedCoord (B := cube N) (cubeOrigin N) 3 (f.1 3) with
    | Sum.inl y₀, Sum.inl y₁, Sum.inr y₂, Sum.inr y₃ => sheetCoeff L T y₀ y₁ y₂ y₃
    | _, _, _, _ => 0) = _
  rcases h0 : f.1 0 with v0 | e0 <;> rcases h1 : f.1 1 with v1 | e1 <;>
    rcases h2 : f.1 2 with v2 | e2 <;> rcases h3 : f.1 3 with v3 | e3 <;>
    simp [dualEmbedCoord, cubeOrigin, sheetCoeff]
  refine if_congr ?_ rfl rfl
  constructor <;> intro h <;> omega


/-! ### The explicit shift as finitely supported chains on `ℤ⁴` -/


/-- `d₁` of the lattice complex, evaluated at a dual plaquette: the orientation sign of the
plaquette times the lattice coboundary of the zero extension of the link field. -/
theorem latticeExactOneComplex_d₁_apply {B : SourceBox} (origin : Fin 4 → ℤ)
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (f : SourceDualTwoCells B) :
    (latticeExactOneComplex (B := B) origin).d₁ τ f =
      dualCellOrientationSign f.1 *
        latticeCurl
          (fun c => lambdaStarRealZeroExtension (B := B) origin (euclideanToFinsupp τ) c)
          (dualCellEmbedding origin f.1) := by
  have hT : sourceDualTMap (euclideanToFinsupp (sourceDualTLinear τ)) = euclideanToFinsupp τ := by
    ext e
    rw [sourceDualTMap_apply, euclideanToFinsupp_apply, sourceDualTLinear_apply,
      euclideanToFinsupp_apply, ← mul_assoc, ← pow_two, dualCellOrientationSign_sq, one_mul]
  change sourceDualD₁ (sourceDualTLinear τ) f = _
  rw [sourceDualD₁_physical_coefficient origin, hT, sourceRealLatticeCoboundary_apply]

/-- The zero extension of the cube shift is minus the explicit shift on all of `ℤ⁴`. -/
theorem cubeLoopShift_zeroExtension {L T N : ℕ} (hN : max L T ≤ N) (c : LatticeCell 4) :
    lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N)
        (euclideanToFinsupp (cubeLoopShift L T N)) c = -loopShiftCell L T c := by
  rw [lambdaStarRealZeroExtension_eq_embDomain]
  by_cases hc : c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N))
  · obtain ⟨e, rfl⟩ := hc
    rw [Finsupp.embDomain_apply_self, euclideanToFinsupp_apply]
    rfl
  · rw [Finsupp.embDomain_of_notMem_range _ _ _ hc]
    have h0 : loopShiftCell L T c = 0 := by
      by_contra h
      exact hc (loopShiftCell_support_cube hN h)
    rw [h0, neg_zero]

/-- Pointwise, the square of `σ - d₁ τ` on the cube is the square of the lattice residual. -/
theorem cubeSheet_sub_d₁_apply_sq {L T N : ℕ} (hN : max L T ≤ N)
    (f : SourceDualTwoCells (cube N)) :
    ((cubeSheet L T N - (sourceLatticeComplex (B := cube N)).d₁ (cubeLoopShift L T N)) f) ^ 2 =
      loopResidualCell L T (cubePlaquetteEmbedding N f) ^ 2 := by
  have hd := latticeExactOneComplex_d₁_apply (B := cube N) (cubeOrigin N)
    (cubeLoopShift L T N) f
  have hfun : (fun c => lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N)
      (euclideanToFinsupp (cubeLoopShift L T N)) c) = fun c => -loopShiftCell L T c :=
    funext (cubeLoopShift_zeroExtension hN)
  rw [hfun, latticeCurl_neg, ← latticeCellOrientationSign_physical (cubeOrigin N) f.1] at hd
  have hval : (cubeSheet L T N -
      (sourceLatticeComplex (B := cube N)).d₁ (cubeLoopShift L T N)) f =
      sheetCell L T (cubePlaquetteEmbedding N f) +
        latticeCellOrientationSign (cubePlaquetteEmbedding N f) *
          latticeCurl (loopShiftCell L T) (cubePlaquetteEmbedding N f) := by
    rw [PiLp.sub_apply]
    change sheetCell L T (cubePlaquetteEmbedding N f) -
      (latticeExactOneComplex (B := cube N) (cubeOrigin N)).d₁ (cubeLoopShift L T N) f = _
    rw [hd]
    change _ - latticeCellOrientationSign (cubePlaquetteEmbedding N f) *
      -latticeCurl (loopShiftCell L T) (cubePlaquetteEmbedding N f) = _
    ring
  rw [hval, loopResidualCell]
  by_cases hs : sheetCell L T (cubePlaquetteEmbedding N f) = 0
  · have hsq := latticeCellOrientationSign_sq (cubePlaquetteEmbedding N f)
    rw [hs, zero_add, zero_sub, mul_pow, hsq, one_mul, neg_sq]
  · rw [(sheetCell_ne_zero_sign hs).2]
    ring

/-- **The explicit shift on the cube**: for `max L T ≤ N`,
`‖σ - d₁ τ‖² ≤ 6 (L + T)` with `τ = cubeLoopShift L T N`. -/
theorem cubeLoopShift_normSq_le {L T N : ℕ} (hN : max L T ≤ N) :
    ‖cubeSheet L T N - (sourceLatticeComplex (B := cube N)).d₁ (cubeLoopShift L T N)‖ ^ 2 ≤
      6 * ((L : ℝ) + T) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc ∑ f, ((cubeSheet L T N -
          (sourceLatticeComplex (B := cube N)).d₁ (cubeLoopShift L T N)) f) ^ 2
      = ∑ f, loopResidualCell L T (cubePlaquetteEmbedding N f) ^ 2 :=
        sum_congr rfl fun f _ => cubeSheet_sub_d₁_apply_sq hN f
    _ = ∑ p ∈ univ.map (cubePlaquetteEmbedding N), loopResidualCell L T p ^ 2 :=
        (sum_map univ (cubePlaquetteEmbedding N) fun p => loopResidualCell L T p ^ 2).symm
    _ ≤ 6 * ((L : ℝ) + T) := sum_loopResidualCell_sq_le L T _


/-- The loop field on the cube has `(ε, ε) ≤ 6 (L + T)` as soon as the cube carries the sheet. -/
theorem cube_loopField_normSq_le_of_le {L T N : ℕ} (hN : max L T ≤ N) :
    ‖loopFieldResidual (sourceLatticeComplex (B := cube N)) (cubeSheet L T N)‖ ^ 2 ≤
      6 * ((L : ℝ) + T) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    (norm_loopFieldResidual_le _ _ (cubeLoopShift L T N)) 2).trans (cubeLoopShift_normSq_le hN)

/-- **The loop-field estimate along cubes** (``, Theorem 6.1; FS82 after (2.88)).
For the sheet `[0,L] × [0,T] × {0}²` strictly inside the centred cube `[-N,N]⁴`, that is for
`max L T + 1 ≤ N`, the loop field `ε = σ - Π_{range d₁} σ` of the lattice complex satisfies
`(ε, ε) ≤ 6 (L + T)`. -/
theorem cube_loopField_normSq_le {L T N : ℕ} (hN : max L T + 1 ≤ N) :
    ‖loopFieldResidual (sourceLatticeComplex (B := cube N)) (cubeSheet L T N)‖ ^ 2 ≤
      6 * ((L : ℝ) + T) :=
  cube_loopField_normSq_le_of_le (by omega)


end FroehlichSpencer.FS82.Wilson

end
