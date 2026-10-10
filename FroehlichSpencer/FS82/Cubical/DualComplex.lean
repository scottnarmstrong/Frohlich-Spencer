/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.RealFilling

/-!
# Dual cells and the finite dual carrier

Complement-coordinate dual cells, the 4D star, the finite dual-link carrier, and zero-extension/compression maps.

Source: FS82 journal (2.17)–(2.18), Fröhlich–Spencer (1982), and (2.32)–(2.35), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

abbrev DualCoord {d : ℕ} (B : Box d) (i : Fin d) := Sum (Fin (B i)) (Fin (B i + 1))

abbrev DualCell (d : ℕ) (B : Box d) := (i : Fin d) → DualCoord B i

abbrev DualRealChain (d : ℕ) (B : Box d) := DualCell d B →₀ ℝ

/-- The orientation-matched cubical star: complement each coordinate direction. -/
@[expose] def primalDualCellEquiv {d : ℕ} {B : Box d} : Cell d B ≃ DualCell d B where
  toFun c i := match c i with
    | Sum.inl v => Sum.inr ⟨v.val, v.isLt⟩
    | Sum.inr e => Sum.inl ⟨e.val, e.isLt⟩
  invFun c i := match c i with
    | Sum.inl e => Sum.inr ⟨e.val, e.isLt⟩
    | Sum.inr v => Sum.inl ⟨v.val, v.isLt⟩
  left_inv c := by
    funext i
    cases h : c i with
    | inl v => simp only [h]
    | inr e => simp only [h]
  right_inv c := by
    funext i
    cases h : c i with
    | inl e => simp only [h]
    | inr v => simp only [h]

@[expose] def starMap {d : ℕ} {B : Box d} :
    RealChain d B →ₗ[ℝ] DualRealChain d B where
  toFun q := Finsupp.equivMapDomain primalDualCellEquiv q
  map_add' q r := by
    ext c
    simp [Finsupp.equivMapDomain_apply]
  map_smul' a q := by
    ext c
    simp [Finsupp.equivMapDomain_apply]

@[expose] def starMapInverse {d : ℕ} {B : Box d} :
    DualRealChain d B →ₗ[ℝ] RealChain d B where
  toFun q := Finsupp.equivMapDomain primalDualCellEquiv.symm q
  map_add' q r := by
    ext c
    simp [Finsupp.equivMapDomain_apply]
  map_smul' a q := by
    ext c
    simp [Finsupp.equivMapDomain_apply]

theorem starMapInverse_starMap {d : ℕ} {B : Box d} (q : RealChain d B) :
    starMapInverse (starMap q) = q := by
  ext c
  simp [starMap, starMapInverse, Finsupp.equivMapDomain_apply]

theorem starMap_starMapInverse {d : ℕ} {B : Box d} (q : DualRealChain d B) :
    starMap (starMapInverse q) = q := by
  ext c
  simp [starMap, starMapInverse, Finsupp.equivMapDomain_apply]

@[expose] def dualCellAxes {d : ℕ} {B : Box d} (c : DualCell d B) : Finset (Fin d) :=
  Finset.univ.filter fun i => (c i).isRight

@[expose] def dualCellDegree {d : ℕ} {B : Box d} (c : DualCell d B) : ℕ :=
  (dualCellAxes c).card

theorem star_complementary_degree {B : Box 4} (c : Cell 4 B) :
    dualCellDegree (primalDualCellEquiv c) + cellDegree c = 4 := by
  have haxes : dualCellAxes (primalDualCellEquiv c) =
      Finset.univ \ cellAxes c := by
    ext i
    cases h : c i with
    | inl v =>
        simp only [dualCellAxes, cellAxes, Finset.mem_filter, Finset.mem_univ,
          Finset.mem_sdiff]
        simp [primalDualCellEquiv, h, coordIsEdge]
    | inr e =>
        simp only [dualCellAxes, cellAxes, Finset.mem_filter, Finset.mem_univ,
          Finset.mem_sdiff]
        simp [primalDualCellEquiv, h, coordIsEdge]
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (cellAxes c))
  simpa [dualCellDegree, cellDegree, haxes] using hcard

abbrev PrimalThreeCells (B : Box 4) := {c : Cell 4 B // cellDegree c = 3}

/-- The finite dual link carrier Λ* is the family of one-cells in the dual
translate of the rectangular box. -/
abbrev LambdaStarLinks (B : Box 4) :=
  {c : DualCell 4 B // dualCellDegree c = 1}

/-- Integer-coordinate labels for the physical embedding of the translated dual
lattice. Dual vertices receive the extra unit shift, while dual interval
indices stay fixed; this is the uniform half-lattice translation on cells. -/
@[expose] def dualEmbedCoord {B : Box 4} (origin : Fin 4 → ℤ) (i : Fin 4) :
    DualCoord B i ↪ LatticeCoord where
  toFun := fun x => match x with
    | Sum.inl v => Sum.inl (origin i + v.val + 1)
    | Sum.inr e => Sum.inr (origin i + e.val)
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [Sum.inl.injEq] at h
        have hv : (x.val : ℤ) = y.val := by omega
        exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hv))
      | inr y => cases h
    | inr x =>
      cases y with
      | inl y => cases h
      | inr y =>
        simp only [Sum.inr.injEq] at h
        have hv : (x.val : ℤ) = y.val := Int.add_left_cancel h
        exact congrArg Sum.inr (Fin.ext (by exact_mod_cast hv))

@[expose] def dualCellEmbedding {B : Box 4} (origin : Fin 4 → ℤ) :
    DualCell 4 B ↪ LatticeCell 4 where
  toFun c i := dualEmbedCoord origin i (c i)
  inj' := by
    intro c₁ c₂ h
    funext i
    exact (dualEmbedCoord origin i).injective (congrFun h i)

@[expose] def lambdaStarEmbedding {B : Box 4} (origin : Fin 4 → ℤ) :
    LambdaStarLinks B ↪ LatticeCell 4 :=
  Function.Embedding.trans (Function.Embedding.subtype _) (dualCellEmbedding (B := B) origin)

/-- Finite real/integer coefficient container carried by J's finite dual
link set. -/
abbrev LambdaStarChain (B : Box 4) := LambdaStarLinks B →₀ ℤ

@[expose] def lambdaStarZeroExtension {B : Box 4} (origin : Fin 4 → ℤ) :
    LambdaStarChain B →ₗ[ℤ] LatticeChain 4 :=
  Finsupp.linearCombination ℤ
    (fun c : LambdaStarLinks B => Finsupp.single (lambdaStarEmbedding (B := B) origin c) 1)

theorem lambdaStarZeroExtension_eq_embDomain {B : Box 4}
    (origin : Fin 4 → ℤ) (q : LambdaStarChain B) :
    lambdaStarZeroExtension (B := B) origin q =
      Finsupp.embDomain (lambdaStarEmbedding (B := B) origin) q := by
  induction q using Finsupp.induction_linear with
  | zero => simp [lambdaStarZeroExtension]
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add]
      have hE : Finsupp.embDomain (lambdaStarEmbedding origin) (q₁ + q₂) =
          Finsupp.embDomain (lambdaStarEmbedding origin) q₁ +
            Finsupp.embDomain (lambdaStarEmbedding origin) q₂ := by
        ext x
        simp [Finsupp.embDomain_apply]
      rw [hE, h₁, h₂]
  | single c z => simp [lambdaStarZeroExtension, Finsupp.embDomain_single]


theorem lambdaStarZeroExtension_vanishes_outside {B : Box 4}
    (origin : Fin 4 → ℤ) (q : LambdaStarChain B) (c : LatticeCell 4)
    (hc : c ∉ Set.range (lambdaStarEmbedding (B := B) origin)) :
    lambdaStarZeroExtension (B := B) origin q c = 0 := by
  rw [lambdaStarZeroExtension_eq_embDomain]
  exact Finsupp.embDomain_of_notMem_range _ _ _ hc


abbrev LambdaStarRealChain (B : Box 4) := LambdaStarLinks B →₀ ℝ

@[expose] def lambdaStarRealZeroExtension {B : Box 4} (origin : Fin 4 → ℤ) :
    LambdaStarRealChain B →ₗ[ℝ] RealLatticeChain 4 :=
  Finsupp.linearCombination ℝ
    (fun c : LambdaStarLinks B => Finsupp.single (lambdaStarEmbedding (B := B) origin c) 1)

theorem lambdaStarRealZeroExtension_eq_embDomain {B : Box 4}
    (origin : Fin 4 → ℤ) (q : LambdaStarRealChain B) :
    lambdaStarRealZeroExtension (B := B) origin q =
      Finsupp.embDomain (lambdaStarEmbedding (B := B) origin) q := by
  induction q using Finsupp.induction_linear with
  | zero => simp [lambdaStarRealZeroExtension]
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add]
      have hE : Finsupp.embDomain (lambdaStarEmbedding (B := B) origin) (q₁ + q₂) =
          Finsupp.embDomain (lambdaStarEmbedding (B := B) origin) q₁ +
            Finsupp.embDomain (lambdaStarEmbedding (B := B) origin) q₂ := by
        ext x
        simp [Finsupp.embDomain_apply]
      rw [hE, h₁, h₂]
  | single c z => simp [lambdaStarRealZeroExtension, Finsupp.embDomain_single]

@[expose] def lambdaStarRealCompression {B : Box 4} (origin : Fin 4 → ℤ) :
    RealLatticeChain 4 →ₗ[ℝ] LambdaStarRealChain B where
  toFun q := Finsupp.comapDomain (lambdaStarEmbedding (B := B) origin) q
    ((lambdaStarEmbedding (B := B) origin).injective.injOn)
  map_add' q₁ q₂ := Finsupp.comapDomain_add_of_injective
    (lambdaStarEmbedding (B := B) origin).injective q₁ q₂
  map_smul' a q := by ext c; simp

theorem lambdaStarRealZeroExtension_vanishes_outside {B : Box 4}
    (origin : Fin 4 → ℤ) (q : LambdaStarRealChain B) (c : LatticeCell 4)
    (hc : c ∉ Set.range (lambdaStarEmbedding (B := B) origin)) :
    lambdaStarRealZeroExtension (B := B) origin q c = 0 := by
  rw [lambdaStarRealZeroExtension_eq_embDomain]
  exact Finsupp.embDomain_of_notMem_range _ _ _ hc

/-- Real finite-volume stencil `Π_{Λ*} δd`, represented as extension by zero,
full-lattice `δd`, and orthogonal restriction back to Λ*. -/
@[expose] def piLambdaStarDeltaDReal {B : Box 4} (origin : Fin 4 → ℤ) :
    LambdaStarRealChain B →ₗ[ℝ] LambdaStarRealChain B :=
  lambdaStarRealCompression (B := B) origin ∘ₗ realLatticeDeltaD ∘ₗ
    lambdaStarRealZeroExtension (B := B) origin


theorem piLambdaStarDeltaDReal_apply {B : Box 4} (origin : Fin 4 → ℤ)
    (q : LambdaStarRealChain B) (c : LambdaStarLinks B) :
    piLambdaStarDeltaDReal (B := B) origin q c =
      realLatticeDeltaD (lambdaStarRealZeroExtension (B := B) origin q)
        (lambdaStarEmbedding (B := B) origin c) := by
  simp [piLambdaStarDeltaDReal, lambdaStarRealCompression, Finsupp.comapDomain_apply]

end
end FroehlichSpencer.FS82.Cubical

end
