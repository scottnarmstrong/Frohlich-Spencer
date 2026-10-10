/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.Cube
public import FroehlichSpencer.FS82.Infinite.GlobalVariational
public import FroehlichSpencer.FS82.Infinite.Variational
public import FroehlichSpencer.FS82.Gaussian.IntegerExactness
public import Mathlib.Topology.Order.Basic
import FroehlichSpencer.FS82.Gaussian.LatticeBridgeHigher

/-!
# Finite support eventually enters the centered C1 cubes

This file records the finite-support part of cube exhaustion. The coordinate
inverse uses the physical C1 shift: dual points map to `origin + v + 1`,
whereas dual intervals map to `origin + e`. The physical finite edge field is
compressed without a second C2 sign transport.
-/

public section

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open Filter

/-- The absolute lattice coordinate underlying a point or interval. -/
@[expose] def cubeCoordMagnitude : LatticeCoord → ℕ
  | Sum.inl z => z.natAbs
  | Sum.inr z => z.natAbs

/-- A convenient finite radius for a lattice cell. -/
@[expose] def cubeCellRadius (c : LatticeCell 4) : ℕ :=
  ∑ i : Fin 4, cubeCoordMagnitude (c i)

@[expose] def cubeCoordValue : LatticeCoord → ℤ
  | Sum.inl z => z
  | Sum.inr z => z

theorem int_bounds_of_natAbs_lt {z : ℤ} {N : ℕ}
    (h : z.natAbs < N) : -(N : ℤ) < z ∧ z < N := by
  cases z with
  | ofNat n =>
      simp at h
      have hcast : (n : ℤ) < (N : ℤ) := by exact_mod_cast h
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
      have hN : 0 < N := by omega
      change -(N : ℤ) < (n : ℤ) ∧ (n : ℤ) < N
      constructor <;> omega
  | negSucc n =>
      simp at h
      have hcast : (n + 1 : ℤ) < (N : ℤ) := by exact_mod_cast h
      constructor <;> omega

/-- Invert the C1 coordinate embedding inside the centered box. -/
@[expose] def cubeDualCoordPreimage (N : ℕ) (i : Fin 4)
    (c : LatticeCoord) (hlo : -(N : ℤ) < cubeCoordValue c)
    (hhi : cubeCoordValue c < N) : DualCoord (cube N) i := by
  cases c with
  | inl z =>
      simp only [cubeCoordValue] at hlo hhi
      have hnonneg : 0 ≤ z + (N : ℤ) - 1 := by omega
      have hlt : (((z + (N : ℤ) - 1).toNat : ℕ) : ℤ) < (2 * N : ℕ) := by
        rw [Int.toNat_of_nonneg hnonneg]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        omega
      exact Sum.inl ⟨(z + (N : ℤ) - 1).toNat, by
        simp only [cube]
        exact_mod_cast hlt⟩
  | inr z =>
      simp only [cubeCoordValue] at hlo hhi
      have hnonneg : 0 ≤ z + (N : ℤ) := by omega
      have hlt : (((z + (N : ℤ)).toNat : ℕ) : ℤ) < (2 * N + 1 : ℕ) := by
        rw [Int.toNat_of_nonneg hnonneg]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        omega
      exact Sum.inr ⟨(z + (N : ℤ)).toNat, by
        simp only [cube]
        exact_mod_cast hlt⟩

theorem cubeDualCoord_embedding_preimage (N : ℕ) (i : Fin 4)
    (c : LatticeCoord) (hlo : -(N : ℤ) < cubeCoordValue c)
    (hhi : cubeCoordValue c < N) :
    dualEmbedCoord (cubeOrigin N) i
      (cubeDualCoordPreimage N i c hlo hhi) = c := by
  cases c with
  | inl z =>
      simp only [cubeCoordValue] at hlo hhi
      have hnonneg : 0 ≤ z + (N : ℤ) - 1 := by omega
      have hsum : (((z + (N : ℤ) - 1).toNat : ℕ) : ℤ) =
          z + (N : ℤ) - 1 := Int.toNat_of_nonneg hnonneg
      change Sum.inl (-(N : ℤ) + ((z + (N : ℤ) - 1).toNat : ℤ) + 1) =
        Sum.inl z
      rw [hsum]
      congr 1
      ring
  | inr z =>
      simp only [cubeCoordValue] at hlo hhi
      have hnonneg : 0 ≤ z + (N : ℤ) := by omega
      have hsum : (((z + (N : ℤ)).toNat : ℕ) : ℤ) =
          z + (N : ℤ) := Int.toNat_of_nonneg hnonneg
      change Sum.inr (-(N : ℤ) + ((z + (N : ℤ)).toNat : ℤ)) =
        Sum.inr z
      rw [hsum]
      congr 1
      ring

theorem cubeCoordMagnitude_eq_natAbs (c : LatticeCoord) :
    cubeCoordMagnitude c = (cubeCoordValue c).natAbs := by
  cases c <;> rfl

theorem cubeCoord_bounds_of_magnitude_lt {c : LatticeCoord} {N : ℕ}
    (h : cubeCoordMagnitude c < N) :
    -(N : ℤ) < cubeCoordValue c ∧ cubeCoordValue c < N := by
  apply int_bounds_of_natAbs_lt
  rw [← cubeCoordMagnitude_eq_natAbs]
  exact h

/-- The C1 preimage of a lattice cell, when every coordinate fits. -/
@[expose] def cubeDualCellPreimage (N : ℕ) (c : LatticeCell 4)
  (h : ∀ i : Fin 4, cubeCoordMagnitude (c i) < N) : DualCell 4 (cube N) :=
  fun i => cubeDualCoordPreimage N i (c i)
    (cubeCoord_bounds_of_magnitude_lt (h i)).1
    (cubeCoord_bounds_of_magnitude_lt (h i)).2

theorem cubeDualCellPreimage_embedding (N : ℕ) (c : LatticeCell 4)
    (h : ∀ i : Fin 4, cubeCoordMagnitude (c i) < N) :
    dualCellEmbedding (cubeOrigin N) (cubeDualCellPreimage N c h) = c := by
  funext i
  exact cubeDualCoord_embedding_preimage N i (c i)
    (cubeCoord_bounds_of_magnitude_lt (h i)).1
    (cubeCoord_bounds_of_magnitude_lt (h i)).2

theorem dualCellDegree_eq_latticeCellDegree_embedding (N : ℕ)
    (c : DualCell 4 (cube N)) :
    dualCellDegree c = latticeCellDegree (dualCellEmbedding (cubeOrigin N) c) := by
  classical
  apply congrArg Finset.card
  ext i
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_filter]
  cases hc : c i <;>
    simp [dualCellEmbedding, dualEmbedCoord, cubeOrigin, latticeIsEdge, hc]

theorem cubeDualCellPreimage_degree (N : ℕ) (c : LatticeCell 4)
    (h : ∀ i : Fin 4, cubeCoordMagnitude (c i) < N) :
    dualCellDegree (cubeDualCellPreimage N c h) = latticeCellDegree c := by
  rw [dualCellDegree_eq_latticeCellDegree_embedding]
  rw [cubeDualCellPreimage_embedding]

theorem cubeCellRadius_coord_le (c : LatticeCell 4) (i : Fin 4) :
    cubeCoordMagnitude (c i) ≤ cubeCellRadius c := by
  simpa [cubeCellRadius] using
    (Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 4 => cubeCoordMagnitude (c j))
      (fun j hj => Nat.zero_le _) (Finset.mem_univ i))

theorem latticeCell_mem_cubeLinkRange_of_radius (N : ℕ)
    (c : LatticeCell 4) (hdegree : latticeCellDegree c = 1)
    (hN : cubeCellRadius c + 2 ≤ N) :
    c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
  have hcoord : ∀ i : Fin 4, cubeCoordMagnitude (c i) < N := by
    intro i
    have hi := cubeCellRadius_coord_le c i
    omega
  let d := cubeDualCellPreimage N c hcoord
  have hd : dualCellDegree d = 1 := by
    dsimp [d]
    rw [cubeDualCellPreimage_degree]
    exact hdegree
  refine ⟨⟨d, hd⟩, ?_⟩
  change dualCellEmbedding (cubeOrigin N) d = c
  exact cubeDualCellPreimage_embedding N c hcoord

/-- A compactly supported global link field has all of its link support in
every centered cube whose side parameter exceeds its support radius by two. -/
theorem cubeLinkSupport_subset_of_radius (μ : GlobalLinkField) (N : ℕ)
    (hN : (∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c) + 2 ≤ N) :
    ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
  intro c hc
  have hcr : cubeCellRadius c ≤
      ∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c := by
    exact Finset.single_le_sum (fun d hd => Nat.zero_le _) hc
  exact latticeCell_mem_cubeLinkRange_of_radius N c (μ.2 c hc) (by omega)

/-! ## Boxing real physical lattice chains -/

/-- Coordinate embedding of an ordinary (non-starred) cell in `cube N`. -/
@[expose] def cubePrimalCoordMap (N : ℕ) (i : Fin 4) :
    Cubical.Coord (cube N) i → LatticeCoord
  | Sum.inl v => Sum.inl (cubeOrigin N i + v.val)
  | Sum.inr e => Sum.inr (cubeOrigin N i + e.val)

@[expose] def cubePrimalCellMap (N : ℕ) :
    Cubical.Cell 4 (cube N) → LatticeCell 4 := fun c i =>
      cubePrimalCoordMap N i (c i)

/-- The ordinary (non-starred) cubical cell in `cube N` represented by a
physical lattice cell. This map preserves point and interval coordinates. -/
@[expose] def cubePrimalCellEmbedding (N : ℕ) :
    Cubical.Cell 4 (cube N) ↪ LatticeCell 4 where
  toFun := cubePrimalCellMap N
  inj' := by
    intro c d h
    funext i
    have hi := congrFun h i
    cases hc : c i <;> cases hd : d i <;>
      simp only [cubePrimalCellMap, cubePrimalCoordMap, hc, hd,
        Sum.inl.injEq, Sum.inr.injEq] at hi
    · apply congrArg Sum.inl
      apply Fin.ext
      exact_mod_cast (Int.add_left_cancel hi)
    · cases hi
    · cases hi
    · apply congrArg Sum.inr
      apply Fin.ext
      exact_mod_cast (Int.add_left_cancel hi)

@[expose] noncomputable def cubePrimalZeroExtension (N : ℕ) :
    Cubical.RealChain 4 (cube N) →ₗ[ℝ] RealLatticeChain 4 :=
  Finsupp.linearCombination ℝ
    (fun c : Cubical.Cell 4 (cube N) =>
      Finsupp.single (cubePrimalCellEmbedding N c) 1)

@[expose] noncomputable def cubePrimalCompression (N : ℕ) :
    RealLatticeChain 4 →ₗ[ℝ] Cubical.RealChain 4 (cube N) where
  toFun q := Finsupp.comapDomain (cubePrimalCellEmbedding N) q
    (cubePrimalCellEmbedding N).injective.injOn
  map_add' q r := Finsupp.comapDomain_add_of_injective
    (cubePrimalCellEmbedding N).injective q r
  map_smul' a q := by ext c; simp

theorem cubePrimalZeroExtension_single (N : ℕ)
    (c : Cubical.Cell 4 (cube N)) (r : ℝ) :
    cubePrimalZeroExtension N (Finsupp.single c r) =
      Finsupp.single (cubePrimalCellEmbedding N c) r := by
  simp [cubePrimalZeroExtension, Finsupp.linearCombination_single]

theorem cubePrimalCellEmbedding_rankBefore (N : ℕ)
    (c : Cubical.Cell 4 (cube N)) (i : Fin 4) :
    Cubical.cellRankBefore c i = latticeRankBefore
      (cubePrimalCellEmbedding N c) i := by
  have hEdge (j : Fin 4) : Cubical.coordIsEdge (c j) =
      latticeIsEdge (cubePrimalCellEmbedding N c j) := by
    cases hcj : c j <;>
      simp [cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap, hcj,
        Cubical.coordIsEdge, latticeIsEdge]
  unfold Cubical.cellRankBefore latticeRankBefore
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hEdge j]

theorem cubeCastLatticeChain_add (q r : LatticeChain 4) :
    Cubical.castLatticeChain (q + r) =
      Cubical.castLatticeChain q + Cubical.castLatticeChain r := by
  ext c
  simp [Cubical.castLatticeChain, Finsupp.mapRange]


@[expose] noncomputable def cubePrimalIntegerZeroExtension (N : ℕ) :
    Cubical.Chain 4 (cube N) →ₗ[ℤ] LatticeChain 4 :=
  Finsupp.linearCombination ℤ
    (fun c : Cubical.Cell 4 (cube N) =>
      Finsupp.single (cubePrimalCellEmbedding N c) 1)


theorem cubePrimalCellEmbedding_upperFace (N : ℕ)
    (c : Cubical.Cell 4 (cube N)) (i : Fin 4) (e : Fin (cube N i)) :
    cubePrimalCellEmbedding N (Cubical.upperFace c i e) =
      Cubical.latticeUpperFace (cubePrimalCellEmbedding N c) i
        (cubeOrigin N i + e.val) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [Cubical.upperFace, Cubical.vertexUpdate,
      cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap,
      Cubical.latticeUpperFace]
    ring
  · simp [Cubical.upperFace, Cubical.vertexUpdate,
      cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap,
      Cubical.latticeUpperFace, hji]

theorem cubePrimalCellEmbedding_lowerFace (N : ℕ)
    (c : Cubical.Cell 4 (cube N)) (i : Fin 4) (e : Fin (cube N i)) :
    cubePrimalCellEmbedding N (Cubical.lowerFace c i e) =
      Cubical.latticeLowerFace (cubePrimalCellEmbedding N c) i
        (cubeOrigin N i + e.val) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [Cubical.lowerFace, Cubical.vertexUpdate,
      cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap,
      Cubical.latticeLowerFace]
  · simp [Cubical.lowerFace, Cubical.vertexUpdate,
      cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap,
      Cubical.latticeLowerFace, hji]

theorem cubePrimalIntegerZeroExtension_boundaryBasis (N : ℕ)
    (c : Cubical.Cell 4 (cube N)) :
    cubePrimalIntegerZeroExtension N (Cubical.boundaryBasis c) =
      Cubical.latticeBoundaryBasis (cubePrimalCellEmbedding N c) := by
  classical
  change Finsupp.linearCombination ℤ
      (fun c : Cubical.Cell 4 (cube N) =>
        Finsupp.single (cubePrimalCellEmbedding N c) 1)
      (Cubical.boundaryBasis c) = _
  simp only [Cubical.boundaryBasis, Cubical.latticeBoundaryBasis]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl v =>
      simp [hci, cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap]
  | inr e =>
      rw [cubePrimalCellEmbedding_rankBefore]
      rw [map_smul, map_sub]
      simp only [Cubical.basisChain, Finsupp.linearCombination_single]
      rw [cubePrimalCellEmbedding_upperFace,
        cubePrimalCellEmbedding_lowerFace]
      simp [cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap,
        hci, Cubical.latticeBasis]

attribute [local instance 2000] instDistribSMul in
theorem cubeCastLatticeChain_zsmul (z : ℤ) (q : LatticeChain 4) :
    Cubical.castLatticeChain (z • q) = (z : ℝ) • Cubical.castLatticeChain q := by
  ext c
  simp [Cubical.castLatticeChain, Finsupp.mapRange]

theorem cubePrimalZeroExtension_cast (N : ℕ)
    (q : Cubical.Chain 4 (cube N)) :
    cubePrimalZeroExtension N (Cubical.castIntegerChain q) =
      Cubical.castLatticeChain (cubePrimalIntegerZeroExtension N q) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [cubePrimalZeroExtension, cubePrimalIntegerZeroExtension,
      Cubical.castIntegerChain, Cubical.castLatticeChain]
  | add q r hq hr =>
      rw [Cubical.castIntegerChain_add, map_add, hq, hr]
      rw [show cubePrimalIntegerZeroExtension N (q + r) =
        cubePrimalIntegerZeroExtension N q + cubePrimalIntegerZeroExtension N r by
          exact map_add (cubePrimalIntegerZeroExtension N) q r]
      rw [cubeCastLatticeChain_add]
  | single c z =>
      have hs : Finsupp.single c z = z • Cubical.basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [Cubical.basisChain, hx]
      rw [hs, Cubical.castIntegerChain_int_smul, map_smul,
        show Cubical.castIntegerChain (Cubical.basisChain c) =
          Finsupp.single c (1 : ℝ) by exact Cubical.castIntegerChain_basis c,
        cubePrimalZeroExtension_single]
      rw [show cubePrimalIntegerZeroExtension N (z • Cubical.basisChain c) =
        z • cubePrimalIntegerZeroExtension N (Cubical.basisChain c) by
          exact map_smul (cubePrimalIntegerZeroExtension N) z (Cubical.basisChain c)]
      rw [show cubePrimalIntegerZeroExtension N (Cubical.basisChain c) =
        Finsupp.single (cubePrimalCellEmbedding N c) (1 : ℤ) by
          simp [cubePrimalIntegerZeroExtension, Cubical.basisChain,
            Finsupp.linearCombination_single]]
      have hcast : Cubical.castLatticeChain
          (Finsupp.single (cubePrimalCellEmbedding N c) (1 : ℤ)) =
        Finsupp.single (cubePrimalCellEmbedding N c) (1 : ℝ) := by
        ext x
        by_cases hx : x = cubePrimalCellEmbedding N c <;>
          simp [Cubical.castLatticeChain, Finsupp.mapRange, hx]
      calc
        (z : ℝ) • Finsupp.single (cubePrimalCellEmbedding N c) (1 : ℝ) =
            (z : ℝ) • Cubical.castLatticeChain
              (Finsupp.single (cubePrimalCellEmbedding N c) (1 : ℤ)) := by
                rw [hcast]
      _ = Cubical.castLatticeChain
            (z • Finsupp.single (cubePrimalCellEmbedding N c) (1 : ℤ)) :=
              (cubeCastLatticeChain_zsmul z
                (Finsupp.single (cubePrimalCellEmbedding N c) (1 : ℤ))).symm

/-- Inverse coordinate map for the ordinary physical box embedding. -/
@[expose] def cubePrimalCoordPreimage (N : ℕ) (i : Fin 4)
    (c : LatticeCoord) (hlo : -(N : ℤ) < cubeCoordValue c)
    (hhi : cubeCoordValue c < N) : Cubical.Coord (cube N) i := by
  cases c with
  | inl z =>
      simp only [cubeCoordValue] at hlo hhi
      have hn : 0 ≤ z + (N : ℤ) := by omega
      have hlt : ((z + (N : ℤ)).toNat : ℤ) < (2 * N + 1 : ℤ) := by
        rw [Int.toNat_of_nonneg hn]
        omega
      exact Sum.inl ⟨(z + (N : ℤ)).toNat, by
        simp only [cube]
        exact_mod_cast hlt⟩
  | inr z =>
      simp only [cubeCoordValue] at hlo hhi
      have hn : 0 ≤ z + (N : ℤ) := by omega
      have hlt : ((z + (N : ℤ)).toNat : ℤ) < (2 * N : ℤ) := by
        rw [Int.toNat_of_nonneg hn]
        omega
      exact Sum.inr ⟨(z + (N : ℤ)).toNat, by
        simp only [cube]
        exact_mod_cast hlt⟩

theorem cubePrimalCoord_embedding_preimage (N : ℕ) (i : Fin 4)
    (c : LatticeCoord) (hlo : -(N : ℤ) < cubeCoordValue c)
    (hhi : cubeCoordValue c < N) :
    cubePrimalCoordMap N i (cubePrimalCoordPreimage N i c hlo hhi) = c := by
  cases c with
  | inl z =>
      simp only [cubeCoordValue] at hlo hhi
      have hn : 0 ≤ z + (N : ℤ) := by omega
      have hto : ((z + (N : ℤ)).toNat : ℤ) = z + (N : ℤ) :=
        Int.toNat_of_nonneg hn
      change Sum.inl (-(N : ℤ) + ((z + (N : ℤ)).toNat : ℤ)) = Sum.inl z
      rw [hto]
      congr 1
      omega
  | inr z =>
      simp only [cubeCoordValue] at hlo hhi
      have hn : 0 ≤ z + (N : ℤ) := by omega
      have hto : ((z + (N : ℤ)).toNat : ℤ) = z + (N : ℤ) :=
        Int.toNat_of_nonneg hn
      change Sum.inr (-(N : ℤ) + ((z + (N : ℤ)).toNat : ℤ)) = Sum.inr z
      rw [hto]
      congr 1
      omega

@[expose] def cubePrimalCellPreimage (N : ℕ) (c : LatticeCell 4)
    (hlo : ∀ i, -(N : ℤ) < cubeCoordValue (c i))
    (hhi : ∀ i, cubeCoordValue (c i) < N) :
    Cubical.Cell 4 (cube N) := fun i =>
      cubePrimalCoordPreimage N i (c i) (hlo i) (hhi i)

theorem cubePrimalCellPreimage_embedding (N : ℕ) (c : LatticeCell 4)
    (hlo : ∀ i, -(N : ℤ) < cubeCoordValue (c i))
    (hhi : ∀ i, cubeCoordValue (c i) < N) :
    cubePrimalCellEmbedding N (cubePrimalCellPreimage N c hlo hhi) = c := by
  funext i
  exact cubePrimalCoord_embedding_preimage N i (c i) (hlo i) (hhi i)

theorem cubePrimalCellEmbedding_degree (N : ℕ)
    (c : Cubical.Cell 4 (cube N)) :
    Cubical.cellDegree c = latticeCellDegree (cubePrimalCellEmbedding N c) := by
  have hEdge (i : Fin 4) : Cubical.coordIsEdge (c i) =
      latticeIsEdge (cubePrimalCellEmbedding N c i) := by
    cases hc : c i <;>
      simp [cubePrimalCellEmbedding, cubePrimalCellMap, cubePrimalCoordMap,
        hc, Cubical.coordIsEdge, latticeIsEdge]
  unfold Cubical.cellDegree Cubical.cellAxes latticeCellDegree
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hEdge i]

theorem latticeCell_mem_cubePrimalRange_of_radius (N : ℕ)
    (c : LatticeCell 4) (hN : cubeCellRadius c + 2 ≤ N) :
    c ∈ Set.range (cubePrimalCellEmbedding N) := by
  have hcoord : ∀ i : Fin 4, cubeCoordMagnitude (c i) < N := by
    intro i
    have hi := cubeCellRadius_coord_le c i
    omega
  have hlo : ∀ i : Fin 4, -(N : ℤ) < cubeCoordValue (c i) := by
    intro i
    exact (cubeCoord_bounds_of_magnitude_lt (hcoord i)).1
  have hhi : ∀ i : Fin 4, cubeCoordValue (c i) < N := by
    intro i
    exact (cubeCoord_bounds_of_magnitude_lt (hcoord i)).2
  exact ⟨cubePrimalCellPreimage N c hlo hhi,
    cubePrimalCellPreimage_embedding N c hlo hhi⟩

theorem cubeGlobalLinkSupport_subset_primalRange (μ : GlobalLinkField) (N : ℕ)
    (hN : (∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c) + 2 ≤ N) :
    ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (cubePrimalCellEmbedding N) := by
  intro c hc
  have hcr : cubeCellRadius c ≤
      ∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c :=
    Finset.single_le_sum (fun d hd => Nat.zero_le _) hc
  exact latticeCell_mem_cubePrimalRange_of_radius N c (by omega)

theorem cubePrimalZeroExtension_eq_embDomain (N : ℕ)
    (q : Cubical.RealChain 4 (cube N)) :
    cubePrimalZeroExtension N q =
      Finsupp.embDomain (cubePrimalCellEmbedding N) q := by
  simpa [cubePrimalZeroExtension] using
    (FroehlichSpencer.FS82.Gaussian.linearCombination_single_eq_embDomain
      (cubePrimalCellEmbedding N) q)

theorem cubePrimalZeroExtension_compression (N : ℕ)
    (q : RealLatticeChain 4)
    (hsupp : ∀ c ∈ q.support, c ∈ Set.range (cubePrimalCellEmbedding N)) :
    cubePrimalZeroExtension N (cubePrimalCompression N q) = q := by
  classical
  rw [cubePrimalZeroExtension_eq_embDomain]
  ext c
  by_cases hc : c ∈ Set.range (cubePrimalCellEmbedding N)
  · rcases hc with ⟨a, rfl⟩
    simp [cubePrimalCompression, Finsupp.embDomain_apply]
  · have hqc : q c = 0 := by
      by_contra hne
      exact hc (hsupp c (Finsupp.mem_support_iff.mpr hne))
    rw [Finsupp.embDomain_of_notMem_range _ _ _ hc, hqc]

theorem cubePrimalZeroExtension_apply (N : ℕ)
    (q : Cubical.RealChain 4 (cube N)) (c : Cubical.Cell 4 (cube N)) :
    cubePrimalZeroExtension N q (cubePrimalCellEmbedding N c) = q c := by
  change Finsupp.linearCombination ℝ
      (fun a : Cubical.Cell 4 (cube N) =>
        Finsupp.single (cubePrimalCellEmbedding N a) 1) q
      (cubePrimalCellEmbedding N c) = q c
  exact FroehlichSpencer.FS82.Gaussian.linearCombination_single_embedding_hits
    (cubePrimalCellEmbedding N) q c

theorem cubePrimalZeroExtension_injective (N : ℕ) :
    Function.Injective (cubePrimalZeroExtension N) := by
  intro q r h
  ext c
  have hc := congrArg (fun z : RealLatticeChain 4 =>
    z (cubePrimalCellEmbedding N c)) h
  rw [cubePrimalZeroExtension_apply, cubePrimalZeroExtension_apply] at hc
  exact hc

theorem cubePrimalZeroExtension_boundary (N : ℕ)
    (q : Cubical.RealChain 4 (cube N)) :
    cubePrimalZeroExtension N (Cubical.realBoundary q) =
      globalBoundary (cubePrimalZeroExtension N q) := by
  have hbasis (c : Cubical.Cell 4 (cube N)) :
      cubePrimalZeroExtension N
          (Cubical.realBoundary (Finsupp.single c (1 : ℝ))) =
        globalBoundary (cubePrimalZeroExtension N
          (Finsupp.single c (1 : ℝ))) := by
    rw [Cubical.realBoundary, Cubical.realifyLinearMap_single]
    simp only [one_smul]
    rw [cubePrimalZeroExtension_cast,
      Cubical.boundary_basis, cubePrimalIntegerZeroExtension_boundaryBasis,
      cubePrimalZeroExtension_single, globalBoundary,
      FroehlichSpencer.FS82.Gaussian.realLatticeBoundary_basis]
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [Cubical.realBoundary, globalBoundary]
  | add q r hq hr =>
      rw [map_add, map_add, hq, hr]
      rw [show cubePrimalZeroExtension N (q + r) =
        cubePrimalZeroExtension N q + cubePrimalZeroExtension N r by
          exact map_add (cubePrimalZeroExtension N) q r]
      exact (map_add globalBoundary
        (cubePrimalZeroExtension N q) (cubePrimalZeroExtension N r)).symm
  | single c a =>
      have hs : Finsupp.single c a = a • Finsupp.single c (1 : ℝ) := by
        ext x
        by_cases hx : x = c <;> simp [hx]
      rw [hs, map_smul, map_smul, hbasis, map_smul]
      exact (map_smul globalBoundary a
        (cubePrimalZeroExtension N (Finsupp.single c (1 : ℝ)))).symm

theorem cubePrimalZeroExtension_support_subset (N : ℕ)
    (q : Cubical.RealChain 4 (cube N)) :
    ∀ c ∈ (cubePrimalZeroExtension N q).support,
      c ∈ Set.range (cubePrimalCellEmbedding N) := by
  intro c hc
  by_contra hnot
  have hz : cubePrimalZeroExtension N q c = 0 := by
    change Finsupp.linearCombination ℝ
      (fun a : Cubical.Cell 4 (cube N) =>
        Finsupp.single (cubePrimalCellEmbedding N a) 1) q c = 0
    exact FroehlichSpencer.FS82.Gaussian.linearCombination_single_embedding_vanishes
      (cubePrimalCellEmbedding N) q c hnot
  exact (Finsupp.mem_support_iff.mp hc) hz

/-! ## Physical gradient identity for the C1 restriction -/

@[expose] noncomputable def cubeSourceVertexPotential (N : ℕ)
    (x : EuclideanSpace ℝ (SourceDualZeroCells (cube N))) :
    RealLatticeChain 4 :=
  sourcePhysicalDualZeroExtension (cubeOrigin N)
    (dualOrientationSignTwist (sourceDualZeroToChain x))

/-- The gradient in the lattice-oriented finite complex is exactly the square-cover
compression of the global lattice gradient of the zero-extended vertex
potential. This is where the output `T` cancels the physical bridge's `S`. -/
theorem latticeExactOneComplex_d₀_physical_gradient (N : ℕ)
    (x : EuclideanSpace ℝ (SourceDualZeroCells (cube N))) :
    (latticeExactOneComplex (B := cube N) (cubeOrigin N)).d₀ x =
      finsuppToEuclidean (lambdaStarRealCompression (B := cube N)
        (cubeOrigin N) (globalCoboundary (cubeSourceVertexPotential N x))) := by
  ext e
  have hbridge := sourceDualD₀_physical_bridge (B := cube N)
    (cubeOrigin N) x
  have hcoeff := congrArg
    (fun q : RealLatticeChain 4 =>
      q (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e)) hbridge
  have hleft :
      sourcePhysicalDualZeroExtension (cubeOrigin N)
          (sourceDualOneToChain (sourceDualD₀ x))
          (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e) =
        sourceDualD₀ x e := by
    rw [show sourceDualOneToChain (sourceDualD₀ x) =
        embedDualSubtype sourceDualOneEmbedding
          (euclideanToFinsupp (sourceDualD₀ x)) by rfl,
      sourcePhysicalDualZeroExtension_embedSourceOne,
      lambdaStarRealZeroExtension_eq_embDomain]
    simp [Finsupp.embDomain_apply, euclideanToFinsupp_apply]
  have hsign : latticeCellOrientationSign
      (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e) =
        dualCellOrientationSign e.1 := by
    change latticeCellOrientationSign
      (dualCellEmbedding (cubeOrigin N) e.1) = _
    exact latticeCellOrientationSign_physical (cubeOrigin N) e.1
  rw [hleft, latticeOrientationSignTwist_apply, hsign] at hcoeff
  change sourceDualTLinear (sourceDualD₀ x) e =
      globalCoboundary (cubeSourceVertexPotential N x)
        (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e)
  rw [sourceDualTLinear_apply]
  rw [hcoeff]
  have hs := dualCellOrientationSign_sq (B := cube N) e
  calc
    dualCellOrientationSign e.1 *
        (dualCellOrientationSign e.1 *
          globalCoboundary (cubeSourceVertexPotential N x)
            (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e)) =
      (dualCellOrientationSign e.1 ^ 2) *
        globalCoboundary (cubeSourceVertexPotential N x)
          (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e) := by ring
    _ = globalCoboundary (cubeSourceVertexPotential N x)
          (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e) := by
      rw [hs]
      ring

theorem lambdaStarRealZeroExtension_compression_of_support (N : ℕ)
    (q : RealLatticeChain 4)
    (hsupp : ∀ c ∈ q.support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N))) :
    lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N)
        (lambdaStarRealCompression (B := cube N) (cubeOrigin N) q) = q := by
  classical
  ext c
  by_cases hc : c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N))
  · obtain ⟨e, rfl⟩ := hc
    simp [lambdaStarRealZeroExtension_eq_embDomain,
      lambdaStarRealCompression, Finsupp.embDomain_apply]
  · have hzero : q c = 0 := by
      by_contra hne
      exact hc (hsupp c (Finsupp.mem_support_iff.mpr hne))
    rw [lambdaStarRealZeroExtension_vanishes_outside _ _ _ hc, hzero]

theorem globalPairing_lambdaStarRealZeroExtension (N : ℕ)
    (q : LambdaStarRealChain (cube N)) (φ : RealLatticeChain 4) :
    globalPairing (lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N) q) φ =
      ∑ e, φ (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e) * q e := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [globalPairing]
  | add q r hq hr =>
      rw [(lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N)).map_add,
        globalPairing_add_left, hq, hr, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      simp only [Finsupp.add_apply]
      ring
  | single e a =>
      have hs : lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N)
          (Finsupp.single e a) =
        a • Finsupp.single (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e) 1 := by
        ext c
        by_cases hc : c = lambdaStarEmbedding (B := cube N) (cubeOrigin N) e
        · subst c
          simp [lambdaStarRealZeroExtension, Finsupp.linearCombination_single]
        · simp [lambdaStarRealZeroExtension, Finsupp.linearCombination_single, hc]
      rw [hs, globalPairing_smul_left]
      simp [globalPairing, Finsupp.single_apply]
      ring

theorem cubeLinkRestriction_inner_eq_globalPairing (μ : GlobalLinkField)
    (N : ℕ)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)))
    (φ : RealLatticeChain 4) :
    inner ℝ (finsuppToEuclidean
        (lambdaStarRealCompression (B := cube N) (cubeOrigin N) φ))
      (cubeLinkRestriction N (μ : RealLatticeChain 4)) =
        globalPairing (μ : RealLatticeChain 4) φ := by
  rw [cubeLinkRestriction, inner_finsuppToEuclidean]
  calc
    (∑ e, (lambdaStarRealCompression (B := cube N) (cubeOrigin N) φ) e *
        (lambdaStarRealCompression (B := cube N) (cubeOrigin N)
          (μ : RealLatticeChain 4)) e) =
      ∑ e, φ (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e) *
        (lambdaStarRealCompression (B := cube N) (cubeOrigin N)
          (μ : RealLatticeChain 4)) e := by
        apply Finset.sum_congr rfl
        intro e he
        simp [lambdaStarRealCompression, Finsupp.comapDomain_apply]
    _ = globalPairing (lambdaStarRealZeroExtension (B := cube N)
          (cubeOrigin N) (lambdaStarRealCompression (B := cube N)
            (cubeOrigin N) (μ : RealLatticeChain 4))) φ := by
        rw [globalPairing_lambdaStarRealZeroExtension]
    _ = globalPairing (μ : RealLatticeChain 4) φ := by
        rw [lambdaStarRealZeroExtension_compression_of_support N
          (μ : RealLatticeChain 4) hsupp]

theorem cubeLinkRestriction_mem_cubeSourceW_of_support (μ : GlobalLinkField)
    (hμ : globallyCoClosed μ) (N : ℕ)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N))) :
    cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N := by
  rw [cubeSourceW, coClosed]
  apply LinearMap.mem_ker.mpr
  ext v
  let C := Moment.SourceConstructor.sourceLatticeComplex (B := cube N)
  have hpair (x : EuclideanSpace ℝ (SourceDualZeroCells (cube N))) :
      inner ℝ (C.d₀ x)
          (cubeLinkRestriction N (μ : RealLatticeChain 4)) = 0 := by
    rw [show C.d₀ =
        (latticeExactOneComplex (B := cube N) (cubeOrigin N)).d₀ by rfl,
      latticeExactOneComplex_d₀_physical_gradient]
    calc
      inner ℝ (finsuppToEuclidean
          (lambdaStarRealCompression (B := cube N) (cubeOrigin N)
            (globalCoboundary (cubeSourceVertexPotential N x))))
          (cubeLinkRestriction N (μ : RealLatticeChain 4)) =
        globalPairing (μ : RealLatticeChain 4)
          (globalCoboundary (cubeSourceVertexPotential N x)) :=
            cubeLinkRestriction_inner_eq_globalPairing μ N hsupp _
      _ = globalPairing (globalBoundary (μ : RealLatticeChain 4))
          (cubeSourceVertexPotential N x) :=
            (globalPairing_boundary_coboundary _ _).symm
      _ = 0 := by rw [hμ]; simp [globalPairing]
  have hsingle := hpair (EuclideanSpace.single v (1 : ℝ))
  have hadj := LinearMap.adjoint_inner_left C.d₀
    (EuclideanSpace.single v (1 : ℝ))
    (cubeLinkRestriction N (μ : RealLatticeChain 4))
  have hswap : inner ℝ (cubeLinkRestriction N (μ : RealLatticeChain 4))
      (C.d₀ (EuclideanSpace.single v (1 : ℝ))) = 0 := by
    rw [real_inner_comm]
    exact hsingle
  rw [hswap] at hadj
  simpa [PiLp.inner_apply] using hadj

theorem eventually_cube_sourceW (μ : GlobalLinkField)
    (hμ : globallyCoClosed μ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N := by
  let N₀ := (∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c) + 2
  refine ⟨N₀, ?_⟩
  intro N hN
  have hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
    exact cubeLinkSupport_subset_of_radius μ N (by simpa [N₀] using hN)
  exact cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp


/-! ## Variational comparison with compact lattice fields -/

private theorem cubeLambdaStarCompression_zeroExtension (N : ℕ)
    (q : LambdaStarRealChain (cube N)) :
    lambdaStarRealCompression (B := cube N) (cubeOrigin N)
      (lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N) q) = q := by
  rw [lambdaStarRealZeroExtension_eq_embDomain]
  exact Finsupp.comapDomain_embDomain _ _

private theorem latticeChainPair_eq_globalPairing
    (q r : RealLatticeChain 4) : latticeChainPair q r = globalPairing q r := by
  unfold latticeChainPair globalPairing
  rfl

private theorem latticeCellDegree_zero_vertex (c : LatticeCell 4)
    (hc : latticeCellDegree c = 0) : Gaussian.sourceLatticeVertex c := by
  classical
  have hcard : (latticeCellAxes c).card = 0 := by
    simpa [latticeCellDegree, latticeCellAxes] using hc
  have haxes : latticeCellAxes c = ∅ := Finset.card_eq_zero.mp hcard
  intro i
  cases hci : c i with
  | inl t => simp
  | inr t =>
      have hi : i ∈ latticeCellAxes c := by
        change i ∈ Finset.univ.filter (fun j => latticeIsEdge (c j))
        rw [Finset.mem_filter]
        constructor
        · simp
        · rw [hci]
          simp [latticeIsEdge]
      rw [haxes] at hi
      simp at hi

private theorem globalPairing_single_right (q : RealLatticeChain 4)
    (v : LatticeCell 4) :
    globalPairing q (Finsupp.single v (1 : ℝ)) = q v := by
  rw [globalPairing_symm]
  simp [globalPairing]

private theorem globalBoundary_support_degree_zero (μ : GlobalLinkField) :
    ∀ c ∈ (globalBoundary (μ : RealLatticeChain 4)).support,
      latticeCellDegree c = 0 := by
  classical
  let R : ℕ :=
    ∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c
  let N : ℕ := R + 2
  have hN : R + 2 ≤ N := by rfl
  have hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (cubePrimalCellEmbedding N) := by
    exact cubeGlobalLinkSupport_subset_primalRange μ N (by simp [R, N])
  let q : Cubical.RealChain 4 (cube N) :=
    cubePrimalCompression N (μ : RealLatticeChain 4)
  have hbox : cubePrimalZeroExtension N q = (μ : RealLatticeChain 4) :=
    cubePrimalZeroExtension_compression N _ hsupp
  have hdegree : Cubical.realHomogeneousSupport q 1 := by
    intro c hc
    have hμc : (μ : RealLatticeChain 4)
        (cubePrimalCellEmbedding N c) ≠ 0 := by
      intro hzero
      have hqc : q c = 0 := by
        change cubePrimalCompression N (μ : RealLatticeChain 4) c = 0
        simp [cubePrimalCompression, Finsupp.comapDomain_apply, hzero]
      exact (Finsupp.mem_support_iff.mp hc) hqc
    have hcμ : cubePrimalCellEmbedding N c ∈
        (μ : RealLatticeChain 4).support :=
      Finsupp.mem_support_iff.mpr hμc
    rw [cubePrimalCellEmbedding_degree]
    exact μ.2 _ hcμ
  have hboundary :
      cubePrimalZeroExtension N (Cubical.realBoundary q) =
        globalBoundary (μ : RealLatticeChain 4) := by
    calc
      cubePrimalZeroExtension N (Cubical.realBoundary q) =
          globalBoundary (cubePrimalZeroExtension N q) :=
        cubePrimalZeroExtension_boundary N q
      _ = globalBoundary (μ : RealLatticeChain 4) := by rw [hbox]
  have hfinite := realBoundary_homogeneousSupport
    q 1 (by norm_num) hdegree
  intro c hc
  have hcExt : c ∈ (cubePrimalZeroExtension N (Cubical.realBoundary q)).support := by
    rw [Finsupp.mem_support_iff] at hc ⊢
    rw [hboundary]
    exact hc
  obtain ⟨d, rfl⟩ := cubePrimalZeroExtension_support_subset N
    (Cubical.realBoundary q) c hcExt
  have hd : d ∈ (Cubical.realBoundary q).support := by
    rw [Finsupp.mem_support_iff] at hcExt ⊢
    rw [cubePrimalZeroExtension_apply] at hcExt
    exact hcExt
  rw [← cubePrimalCellEmbedding_degree N d]
  exact hfinite d hd

/-- A finite source edge vector, extended by zero through the physical C1
embedding, is a compact global link field. -/
@[expose] noncomputable def cubeGlobalLinkExtension (N : ℕ)
    (x : EuclideanSpace ℝ (SourceDualOneCells (cube N))) : GlobalLinkField := by
  let q : LambdaStarRealChain (cube N) := euclideanToFinsupp x
  refine ⟨lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N) q, ?_⟩
  intro c hc
  have hrange : c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
    by_contra hnot
    have hz := lambdaStarRealZeroExtension_vanishes_outside
      (B := cube N) (cubeOrigin N) q c hnot
    exact (Finsupp.mem_support_iff.mp hc) hz
  obtain ⟨e, rfl⟩ := hrange
  exact (dualCellDegree_eq_latticeCellDegree_embedding N e.1).symm.trans e.2

private theorem cubeGlobalLinkExtension_support_in_cube (N : ℕ)
    (x : EuclideanSpace ℝ (SourceDualOneCells (cube N))) :
    ∀ c ∈ (cubeGlobalLinkExtension N x : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
  intro c hc
  by_contra hnot
  have hz := lambdaStarRealZeroExtension_vanishes_outside
    (B := cube N) (cubeOrigin N) (euclideanToFinsupp x) c hnot
  exact (Finsupp.mem_support_iff.mp hc) hz

private theorem cubeGlobalLinkExtension_curl_energy (N : ℕ)
    (x : EuclideanSpace ℝ (SourceDualOneCells (cube N))) :
    ‖(sourceLatticeComplex (B := cube N)).d₁ x‖ ^ 2 =
      globalNormSq (globalCoboundary
        (cubeGlobalLinkExtension N x : RealLatticeChain 4)) := by
  let C := sourceLatticeComplex (B := cube N)
  have hT : sourceDualTMap
      (euclideanToFinsupp (sourceDualTLinear (B := cube N) x)) =
        euclideanToFinsupp x := by
    ext e
    simp only [sourceDualTMap_apply, euclideanToFinsupp_apply,
      sourceDualTLinear_apply]
    calc
      dualCellOrientationSign e.1 *
          (dualCellOrientationSign e.1 * x e) =
        (dualCellOrientationSign e.1 * dualCellOrientationSign e.1) * x e := by ring
      _ = x e := by
        rw [← pow_two, dualCellOrientationSign_sq (B := cube N) e]
        ring
  have hp := sourceDualD₁_pairing_eq_latticeCoboundaryPair
    (B := cube N) (cubeOrigin N) (sourceDualTLinear x) (sourceDualTLinear x)
  have hpair : inner ℝ (C.d₁ x) (C.d₁ x) =
      globalPairing
        (globalCoboundary (cubeGlobalLinkExtension N x : RealLatticeChain 4))
        (globalCoboundary (cubeGlobalLinkExtension N x : RealLatticeChain 4)) := by
    change inner ℝ (sourceDualD₁ (sourceDualTLinear x))
        (sourceDualD₁ (sourceDualTLinear x)) = _
    rw [hp, hT]
    rw [latticeChainPair_eq_globalPairing]
    rfl
  rw [← real_inner_self_eq_norm_sq, hpair]
  rfl

private theorem cubeGlobalLinkExtension_pairing (μ : GlobalLinkField) (N : ℕ)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)))
    (x : EuclideanSpace ℝ (SourceDualOneCells (cube N))) :
    inner ℝ (cubeLinkRestriction N (μ : RealLatticeChain 4)) x =
      globalPairing (μ : RealLatticeChain 4)
        (cubeGlobalLinkExtension N x : RealLatticeChain 4) := by
  let q : LambdaStarRealChain (cube N) := euclideanToFinsupp x
  have hx : finsuppToEuclidean
      (lambdaStarRealCompression (B := cube N) (cubeOrigin N)
        (lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N) q)) = x := by
    rw [cubeLambdaStarCompression_zeroExtension]
    simp [q]
  calc
    inner ℝ (cubeLinkRestriction N (μ : RealLatticeChain 4)) x =
        inner ℝ (cubeLinkRestriction N (μ : RealLatticeChain 4))
          (finsuppToEuclidean
            (lambdaStarRealCompression (B := cube N) (cubeOrigin N)
              (lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N) q))) := by
          rw [← hx]
    _ = inner ℝ
          (finsuppToEuclidean
            (lambdaStarRealCompression (B := cube N) (cubeOrigin N)
              (lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N) q)))
          (cubeLinkRestriction N (μ : RealLatticeChain 4)) := real_inner_comm _ _
    _ = globalPairing (μ : RealLatticeChain 4)
          (lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N) q) :=
        cubeLinkRestriction_inner_eq_globalPairing μ N hsupp _
    _ = globalPairing (μ : RealLatticeChain 4)
          (cubeGlobalLinkExtension N x : RealLatticeChain 4) := by rfl

private theorem cubeFiniteObjective_eq_global (μ : GlobalLinkField) (N : ℕ)
    (hW : cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)))
    (x : EuclideanSpace ℝ (SourceDualOneCells (cube N))) :
    finiteVariationalObjective
        (sourceLatticeComplex (B := cube N))
        ⟨cubeLinkRestriction N (μ : RealLatticeChain 4), hW⟩ x =
      globalVariationalObjective μ (cubeGlobalLinkExtension N x) := by
  unfold finiteVariationalObjective globalVariationalObjective
  rw [cubeGlobalLinkExtension_pairing μ N hsupp x,
    cubeGlobalLinkExtension_curl_energy]

private theorem cubeFiniteTrial_le_globalCovariance (μ : GlobalLinkField)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) = (μ : RealLatticeChain 4))
    (N : ℕ)
    (hW : cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N))) :
    quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N))
        ⟨cubeLinkRestriction N (μ : RealLatticeChain 4), hW⟩ ≤
      globalVariationalCovariance μ := by
  have hbdd := globalVariationalCovariance_le_of_filling μ σ hfill
  have hsetBound : BddAbove {r : ℝ | ∃ φ : GlobalLinkField,
      globalVariationalObjective μ φ = r} := by
    refine ⟨globalNormSq (σ : RealLatticeChain 4), ?_⟩
    rintro r ⟨φ, rfl⟩
    exact globalVariationalObjective_le_of_filling μ φ σ hfill
  have hmax := quotientCovarianceQuadratic_isGreatest_variational
    (sourceLatticeComplex (B := cube N))
    ⟨cubeLinkRestriction N (μ : RealLatticeChain 4), hW⟩
  apply le_of_not_gt
  intro hcontra
  have hglobal : ∀ r ∈ {r : ℝ | ∃ φ : GlobalLinkField,
      globalVariationalObjective μ φ = r}, r ≤ globalVariationalCovariance μ := by
    intro r hr
    exact le_csSup hsetBound hr
  have hfinite : ∀ r ∈ {r : ℝ | ∃ x : EuclideanSpace ℝ (SourceDualOneCells (cube N)),
      finiteVariationalObjective (sourceLatticeComplex (B := cube N))
        ⟨cubeLinkRestriction N (μ : RealLatticeChain 4), hW⟩ x = r},
      r ≤ globalVariationalCovariance μ := by
    intro r hr
    rcases hr with ⟨x, rfl⟩
    apply hglobal
    exact ⟨cubeGlobalLinkExtension N x,
      (cubeFiniteObjective_eq_global μ N hW hsupp x).symm⟩
  have hmem := hmax.1
  rcases hmem with ⟨x, hx⟩
  have hle := hfinite _ ⟨x, hx⟩
  exact (not_lt_of_ge hle hcontra)

theorem cubeCovariance_monotone (μ : GlobalLinkField) (N : ℕ)
    (hW : cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N)
    (hWnext : cubeLinkRestriction (N + 1) (μ : RealLatticeChain 4) ∈
      cubeSourceW (N + 1))
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N))) :
    quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N))
        ⟨cubeLinkRestriction N (μ : RealLatticeChain 4), hW⟩ ≤
      quotientCovarianceQuadratic (sourceLatticeComplex (B := cube (N + 1)))
        ⟨cubeLinkRestriction (N + 1) (μ : RealLatticeChain 4), hWnext⟩ := by
  have hsuppNext : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube (N + 1))
        (cubeOrigin (N + 1))) := by
    intro c hc
    exact cube_links_nested N (hsupp c hc)
  let C := sourceLatticeComplex (B := cube N)
  let Cnext := sourceLatticeComplex (B := cube (N + 1))
  let τ : coClosed C := ⟨cubeLinkRestriction N (μ : RealLatticeChain 4), hW⟩
  let τnext : coClosed Cnext :=
    ⟨cubeLinkRestriction (N + 1) (μ : RealLatticeChain 4), hWnext⟩
  have hmax := quotientCovarianceQuadratic_isGreatest_variational C τ
  obtain ⟨x, hx⟩ := hmax.1
  let φ := cubeGlobalLinkExtension N x
  have hφsupport : ∀ c ∈ (φ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) :=
    cubeGlobalLinkExtension_support_in_cube N x
  have hφsupportNext : ∀ c ∈ (φ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube (N + 1))
        (cubeOrigin (N + 1))) := by
    intro c hc
    exact cube_links_nested N (hφsupport c hc)
  let qnext := lambdaStarRealCompression (B := cube (N + 1))
    (cubeOrigin (N + 1)) (φ : RealLatticeChain 4)
  let ynext : EuclideanSpace ℝ (SourceDualOneCells (cube (N + 1))) :=
    finsuppToEuclidean qnext
  have hynext : euclideanToFinsupp ynext = qnext := by simp [ynext, qnext]
  have hextnext : cubeGlobalLinkExtension (N + 1) ynext = φ := by
    apply Subtype.ext
    change lambdaStarRealZeroExtension (B := cube (N + 1))
        (cubeOrigin (N + 1)) (euclideanToFinsupp ynext) =
      (φ : RealLatticeChain 4)
    rw [hynext]
    exact lambdaStarRealZeroExtension_compression_of_support (N + 1)
      (φ : RealLatticeChain 4) hφsupportNext
  have hobj : finiteVariationalObjective C τ x =
      globalVariationalObjective μ φ :=
    cubeFiniteObjective_eq_global μ N hW hsupp x
  have hobjnext : finiteVariationalObjective Cnext τnext ynext =
      globalVariationalObjective μ φ := by
    calc
      finiteVariationalObjective Cnext τnext ynext =
          globalVariationalObjective μ (cubeGlobalLinkExtension (N + 1) ynext) :=
        cubeFiniteObjective_eq_global μ (N + 1) hWnext hsuppNext ynext
      _ = globalVariationalObjective μ φ :=
        congrArg (globalVariationalObjective μ) hextnext
  have hmaxnext := quotientCovarianceQuadratic_isGreatest_variational Cnext τnext
  calc
    quotientCovarianceQuadratic C τ = finiteVariationalObjective C τ x := hx.symm
    _ = globalVariationalObjective μ φ := hobj
    _ ≤ quotientCovarianceQuadratic Cnext τnext :=
      hmaxnext.2 ⟨ynext, hobjnext⟩

theorem compactFilling_exists (μ : GlobalLinkField)
    (hμ : globallyCoClosed μ) :
    ∃ σ : GlobalPlaquetteField,
      globalBoundary (σ : RealLatticeChain 4) =
        (μ : RealLatticeChain 4) := by
  classical
  let N : ℕ :=
    (∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c) + 2
  have hN :
      (∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c) + 2 ≤ N := by
    rfl
  have hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (cubePrimalCellEmbedding N) :=
    cubeGlobalLinkSupport_subset_primalRange μ N hN
  let q : Cubical.RealChain 4 (cube N) :=
    cubePrimalCompression N (μ : RealLatticeChain 4)
  have hbox : cubePrimalZeroExtension N q = (μ : RealLatticeChain 4) :=
    cubePrimalZeroExtension_compression N _ hsupp
  have hdegree : Cubical.realHomogeneousSupport q 1 := by
    intro c hc
    have hμc : (μ : RealLatticeChain 4)
        (cubePrimalCellEmbedding N c) ≠ 0 := by
      intro hzero
      have hqc : q c = 0 := by
        change cubePrimalCompression N (μ : RealLatticeChain 4) c = 0
        simp [cubePrimalCompression, Finsupp.comapDomain_apply, hzero]
      exact (Finsupp.mem_support_iff.mp hc) hqc
    have hcμ : cubePrimalCellEmbedding N c ∈
        (μ : RealLatticeChain 4).support :=
      Finsupp.mem_support_iff.mpr hμc
    rw [cubePrimalCellEmbedding_degree]
    exact μ.2 _ hcμ
  have hcycleExt :
      cubePrimalZeroExtension N (Cubical.realBoundary q) = 0 := by
    rw [cubePrimalZeroExtension_boundary, hbox]
    exact hμ
  have hcycle : Cubical.realBoundary q = 0 := by
    apply cubePrimalZeroExtension_injective N
    simpa using hcycleExt
  let anchor : Cubical.Anchor 4 (cube N) := fun i =>
    ⟨0, by simp [cube]⟩
  obtain ⟨hfill, hfillDegree⟩ :=
    Cubical.real_positiveDegree_filling anchor q 1 (by omega) hdegree hcycle
  let τ : Cubical.RealChain 4 (cube N) :=
    Cubical.realFillingOperator anchor q
  refine ⟨⟨cubePrimalZeroExtension N τ, ?_⟩, ?_⟩
  · intro c hc
    obtain ⟨d, rfl⟩ := cubePrimalZeroExtension_support_subset N τ c hc
    have hd : d ∈ τ.support := by
      rw [Finsupp.mem_support_iff] at hc ⊢
      rw [cubePrimalZeroExtension_apply] at hc
      exact hc
    rw [← cubePrimalCellEmbedding_degree N d]
    have := hfillDegree d hd
    omega
  · calc
      globalBoundary (cubePrimalZeroExtension N τ) =
          cubePrimalZeroExtension N (Cubical.realBoundary τ) :=
        (cubePrimalZeroExtension_boundary N τ).symm
      _ = cubePrimalZeroExtension N q := by rw [hfill]
      _ = (μ : RealLatticeChain 4) := hbox

private theorem latticeEdgeCell_degree_of_vertex (v : LatticeCell 4)
    (hv : Gaussian.sourceLatticeVertex v) (i : Fin 4) (t : ℤ) :
    latticeCellDegree (Cubical.latticeEdgeCell v i t) = 1 := by
  classical
  unfold latticeCellDegree
  have hfilter :
      Finset.univ.filter (fun j : Fin 4 =>
        latticeIsEdge (Cubical.latticeEdgeCell v i t j)) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    by_cases hji : j = i
    · subst j
      simp [Cubical.latticeEdgeCell, latticeIsEdge]
    · have hleft :
          ¬ latticeIsEdge (Cubical.latticeEdgeCell v i t j) := by
        simpa [Cubical.latticeEdgeCell, hji, latticeIsEdge] using hv j
      simp [hleft, hji]
  rw [hfilter]
  simp

private theorem latticeCoboundaryBasis_support_link (v : LatticeCell 4)
    (hv : Gaussian.sourceLatticeVertex v) (e : LatticeCell 4)
    (he : e ∈ (Cubical.latticeCoboundaryBasis v).support) :
    latticeCellDegree e = 1 := by
  classical
  let term : Fin 4 → Cubical.LatticeChain 4 := fun i =>
    match v i with
    | Sum.inr _ => 0
    | Sum.inl t => ((-1 : ℤ) ^ latticeRankBefore v i) •
        (Cubical.latticeBasis (Cubical.latticeEdgeCell v i (t - 1)) -
          Cubical.latticeBasis (Cubical.latticeEdgeCell v i t))
  have he' : e ∈ (∑ i : Fin 4, term i).support := by
    change e ∈ (Cubical.latticeCoboundaryBasis v).support at he
    exact he
  have hsum := Finsupp.support_finsetSum (s := Finset.univ) (f := term) he'
  rcases Finset.mem_biUnion.mp hsum with ⟨i, hi, htermSupport⟩
  have hiTerm := Finsupp.mem_support_iff.mp htermSupport
  cases hvi : v i with
  | inl t =>
      have hterm :
          (((-1 : ℤ) ^ latticeRankBefore v i) •
            (Cubical.latticeBasis (Cubical.latticeEdgeCell v i (t - 1)) -
              Cubical.latticeBasis (Cubical.latticeEdgeCell v i t))) e ≠ 0 := by
        simpa [term, hvi] using hiTerm
      have hdiff :
          (Cubical.latticeBasis (Cubical.latticeEdgeCell v i (t - 1)) -
            Cubical.latticeBasis (Cubical.latticeEdgeCell v i t)) e ≠ 0 := by
        intro hz
        apply hterm
        change ((-1 : ℤ) ^ latticeRankBefore v i) *
          ((Cubical.latticeBasis (Cubical.latticeEdgeCell v i (t - 1)) -
            Cubical.latticeBasis (Cubical.latticeEdgeCell v i t)) e) = 0
        rw [hz]
        simp
      have hfaces : e = Cubical.latticeEdgeCell v i (t - 1) ∨
          e = Cubical.latticeEdgeCell v i t := by
        by_cases h₁ : e = Cubical.latticeEdgeCell v i (t - 1)
        · exact Or.inl h₁
        · by_cases h₂ : e = Cubical.latticeEdgeCell v i t
          · exact Or.inr h₂
          · have hz :
                (Cubical.latticeBasis (Cubical.latticeEdgeCell v i (t - 1)) -
                  Cubical.latticeBasis (Cubical.latticeEdgeCell v i t)) e = 0 := by
              simp [Cubical.latticeBasis, h₁, h₂]
            exact (hdiff hz).elim
      rcases hfaces with hface | hface
      · rw [hface]
        exact latticeEdgeCell_degree_of_vertex v hv i (t - 1)
      · rw [hface]
        exact latticeEdgeCell_degree_of_vertex v hv i t
  | inr t =>
      simp [term, hvi] at hiTerm

private theorem globalCoboundary_vertex_support_degree_one
    (v : LatticeCell 4) (hv : Gaussian.sourceLatticeVertex v)
    (e : LatticeCell 4)
    (he : e ∈ (globalCoboundary (Finsupp.single v (1 : ℝ))).support) :
    latticeCellDegree e = 1 := by
  have hcast : e ∈ (Cubical.castLatticeChain
      (Cubical.latticeCoboundaryBasis v)).support := by
    rw [globalCoboundary, sourceRealLatticeCoboundary_single] at he
    simpa only [one_smul] using he
  have hbase : e ∈ (Cubical.latticeCoboundaryBasis v).support := by
    rw [Finsupp.mem_support_iff] at hcast ⊢
    intro hz
    apply hcast
    simp [castLatticeChain_apply, hz]
  exact latticeCoboundaryBasis_support_link v hv e hbase

private theorem cubeSourceVertexPotential_single (N : ℕ)
    (v : LatticeCell 4) (hv : latticeCellDegree v = 0)
    (hcoord : ∀ i : Fin 4, cubeCoordMagnitude (v i) < N) :
    cubeSourceVertexPotential N
      (finsuppToEuclidean
        (Finsupp.single
          (⟨cubeDualCellPreimage N v hcoord,
            by simpa [hv] using cubeDualCellPreimage_degree N v hcoord⟩ :
              SourceDualZeroCells (cube N)) (1 : ℝ))) =
      Finsupp.single v (1 : ℝ) := by
  let d := cubeDualCellPreimage N v hcoord
  have hd : dualCellDegree d = 0 := by
    simpa [hv] using cubeDualCellPreimage_degree N v hcoord
  let e : SourceDualZeroCells (cube N) := ⟨d, hd⟩
  let x := finsuppToEuclidean (Finsupp.single e (1 : ℝ))
  have hsource : sourceDualZeroToChain x =
      embedDualSubtype sourceDualZeroEmbedding (Finsupp.single e (1 : ℝ)) := by
    simp [x, sourceDualZeroToChain]
  change sourcePhysicalDualZeroExtension (cubeOrigin N)
      (dualOrientationSignTwist (sourceDualZeroToChain x)) = _
  rw [hsource, dualOrientationSignTwist_embedSourceZero]
  rw [sourcePhysicalDualZeroExtension_embedDualSubtype]
  simp only [one_smul, Finsupp.linearCombination_single,
    Function.Embedding.trans_apply, sourceDualZeroEmbedding]
  change Finsupp.single (dualCellEmbedding (cubeOrigin N) d) (1 : ℝ) =
    Finsupp.single v (1 : ℝ)
  congr 1
  exact cubeDualCellPreimage_embedding N v hcoord

private theorem globallyCoClosed_of_eventual_cubeSourceW (μ : GlobalLinkField)
    (N₀ : ℕ)
    (hW : ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N) :
    globallyCoClosed μ := by
  classical
  let b := globalBoundary (μ : RealLatticeChain 4)
  let Rμ := ∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c
  let Rb := ∑ c ∈ b.support, cubeCellRadius c
  let Rg := ∑ v ∈ b.support,
    ∑ e ∈ (globalCoboundary (Finsupp.single v (1 : ℝ))).support,
      cubeCellRadius e
  let N := max N₀ (max (Rμ + 2) (max (Rb + 2) (Rg + 2)))
  have hN₀ : N₀ ≤ N := by simp [N]
  have hNμ : Rμ + 2 ≤ N := by omega
  have hNb : Rb + 2 ≤ N := by omega
  have hNg : Rg + 2 ≤ N := by omega
  have hμsupport : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) :=
    cubeLinkSupport_subset_of_radius μ N (by simpa [Rμ] using hNμ)
  let C := sourceLatticeComplex (B := cube N)
  have hker : C.d₀.adjoint (cubeLinkRestriction N
      (μ : RealLatticeChain 4)) = 0 := by
    apply LinearMap.mem_ker.mp
    change cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ coClosed C
    exact hW N hN₀
  unfold globallyCoClosed
  ext v
  by_cases hvb : b v = 0
  · exact hvb
  · have hvSupport : v ∈ b.support := Finsupp.mem_support_iff.mpr hvb
    have hvdegree : latticeCellDegree v = 0 :=
      globalBoundary_support_degree_zero μ v hvSupport
    have hvvertex : Gaussian.sourceLatticeVertex v :=
      latticeCellDegree_zero_vertex v hvdegree
    have hvRadius : cubeCellRadius v ≤ Rb := by
      dsimp [Rb, b]
      exact Finset.single_le_sum (fun c hc => Nat.zero_le _) hvSupport
    have hcoord : ∀ i : Fin 4, cubeCoordMagnitude (v i) < N := by
      intro i
      have hi := cubeCellRadius_coord_le v i
      omega
    let e : SourceDualZeroCells (cube N) :=
      ⟨cubeDualCellPreimage N v hcoord, by
        rw [cubeDualCellPreimage_degree]
        exact hvdegree⟩
    let x : EuclideanSpace ℝ (SourceDualZeroCells (cube N)) :=
      finsuppToEuclidean (Finsupp.single e (1 : ℝ))
    have hpotential : cubeSourceVertexPotential N x =
        Finsupp.single v (1 : ℝ) := by
      simpa [x, e] using cubeSourceVertexPotential_single N v hvdegree hcoord
    have hgradientSupport : ∀ c ∈
        (globalCoboundary (Finsupp.single v (1 : ℝ))).support,
        c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
      intro c hc
      have hcdegree := globalCoboundary_vertex_support_degree_one v hvvertex c hc
      have hRinner :
          (∑ e ∈ (globalCoboundary (Finsupp.single v (1 : ℝ))).support,
            cubeCellRadius e) ≤ Rg := by
        dsimp [Rg]
        exact Finset.single_le_sum
          (f := fun w =>
            ∑ e ∈ (globalCoboundary (Finsupp.single w (1 : ℝ))).support,
              cubeCellRadius e)
          (fun w hw => Nat.zero_le _) hvSupport
      have hcr : cubeCellRadius c ≤
          ∑ e ∈ (globalCoboundary (Finsupp.single v (1 : ℝ))).support,
            cubeCellRadius e :=
        Finset.single_le_sum (fun d hd => Nat.zero_le _) hc
      exact latticeCell_mem_cubeLinkRange_of_radius N c hcdegree (by omega)
    have hpair : inner ℝ (C.d₀ x)
        (cubeLinkRestriction N (μ : RealLatticeChain 4)) = 0 := by
      have hadj := LinearMap.adjoint_inner_left C.d₀ x
        (cubeLinkRestriction N (μ : RealLatticeChain 4))
      rw [hker] at hadj
      calc
        inner ℝ (C.d₀ x) (cubeLinkRestriction N (μ : RealLatticeChain 4)) =
            inner ℝ (cubeLinkRestriction N (μ : RealLatticeChain 4)) (C.d₀ x) :=
          real_inner_comm _ _
        _ = 0 := by simpa using hadj.symm
    have hcoeff : b v = 0 := by
      calc
        b v = globalPairing b (Finsupp.single v (1 : ℝ)) :=
          (globalPairing_single_right b v).symm
        _ = globalPairing b (cubeSourceVertexPotential N x) := by
          rw [hpotential]
        _ = globalPairing (μ : RealLatticeChain 4)
              (globalCoboundary (cubeSourceVertexPotential N x)) :=
          globalPairing_boundary_coboundary _ _
        _ = inner ℝ (C.d₀ x)
              (cubeLinkRestriction N (μ : RealLatticeChain 4)) := by
          rw [show C.d₀ =
              (latticeExactOneComplex (B := cube N) (cubeOrigin N)).d₀ by rfl,
            latticeExactOneComplex_d₀_physical_gradient]
          exact (cubeLinkRestriction_inner_eq_globalPairing μ N hμsupport _).symm
        _ = 0 := hpair
    exact (hvb hcoeff).elim

theorem cubeCovariance_tendsto_fourierGreen (μ : GlobalLinkField) (N₀ : ℕ)
    (hW : ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N) :
    Tendsto
      (fun n : {N : ℕ // N₀ ≤ N} =>
        quotientCovarianceQuadratic (sourceLatticeComplex (B := cube n.1))
          ⟨cubeLinkRestriction n.1 (μ : RealLatticeChain 4), hW n.1 n.2⟩)
      atTop (nhds (globalVariationalCovariance μ)) := by
  classical
  have hμ : globallyCoClosed μ :=
    globallyCoClosed_of_eventual_cubeSourceW μ N₀ hW
  obtain ⟨σ, hfill⟩ := compactFilling_exists μ hμ
  let Rμ : ℕ :=
    ∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c
  have hSnonempty :
      {r : ℝ | ∃ φ : GlobalLinkField,
        globalVariationalObjective μ φ = r}.Nonempty := by
    refine ⟨globalVariationalObjective μ ⟨0, by simp [latticeCellDegree]⟩, ?_⟩
    exact ⟨⟨0, by simp [latticeCellDegree]⟩, rfl⟩
  let Q : {N : ℕ // N₀ ≤ N} → ℝ := fun n =>
    quotientCovarianceQuadratic (sourceLatticeComplex (B := cube n.1))
      ⟨cubeLinkRestriction n.1 (μ : RealLatticeChain 4), hW n.1 n.2⟩
  have hmonoStep : ∀ n : {k : ℕ // max N₀ (Rμ + 2) ≤ k},
      Q ⟨n.1, by omega⟩ ≤ Q ⟨n.1 + 1, by omega⟩ := by
    intro n
    have hnμ : Rμ + 2 ≤ n.1 := le_trans (le_max_right N₀ (Rμ + 2)) n.2
    have hn₀ : N₀ ≤ n.1 := le_trans (le_max_left N₀ (Rμ + 2)) n.2
    have hWn : cubeLinkRestriction n (μ : RealLatticeChain 4) ∈
        cubeSourceW n := hW n.1 hn₀
    have hWnext : cubeLinkRestriction (n + 1) (μ : RealLatticeChain 4) ∈
        cubeSourceW (n.1 + 1) := hW (n.1 + 1) (by omega)
    have hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
        c ∈ Set.range (lambdaStarEmbedding (B := cube n.1) (cubeOrigin n.1)) :=
      cubeLinkSupport_subset_of_radius μ n.1 (by simpa [Rμ] using hnμ)
    simpa [Q] using cubeCovariance_monotone μ n.1 hWn hWnext hsupp
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    change a < sSup {r : ℝ | ∃ φ : GlobalLinkField,
      globalVariationalObjective μ φ = r} at ha
    obtain ⟨r, ⟨φ, hφ⟩, har⟩ := exists_lt_of_lt_csSup hSnonempty ha
    subst r
    let Rφ : ℕ :=
      ∑ c ∈ (φ : RealLatticeChain 4).support, cubeCellRadius c
    let M : ℕ := max N₀ (max (Rμ + 2) (Rφ + 2))
    have hM₀ : N₀ ≤ M := by simp [M]
    have hMμ : Rμ + 2 ≤ M := by omega
    have hMφ : Rφ + 2 ≤ M := by omega
    let m : {N : ℕ // N₀ ≤ N} := ⟨M, hM₀⟩
    have hsuppμ : ∀ c ∈ (μ : RealLatticeChain 4).support,
        c ∈ Set.range (lambdaStarEmbedding (B := cube M) (cubeOrigin M)) :=
      cubeLinkSupport_subset_of_radius μ M (by simpa [Rμ] using hMμ)
    have hsuppφ : ∀ c ∈ (φ : RealLatticeChain 4).support,
        c ∈ Set.range (lambdaStarEmbedding (B := cube M) (cubeOrigin M)) :=
      cubeLinkSupport_subset_of_radius φ M (by simpa [Rφ] using hMφ)
    let qφ := lambdaStarRealCompression (B := cube M) (cubeOrigin M)
      (φ : RealLatticeChain 4)
    let x : EuclideanSpace ℝ (SourceDualOneCells (cube M)) :=
      finsuppToEuclidean qφ
    have hx : euclideanToFinsupp x = qφ := by simp [x, qφ]
    have hext : cubeGlobalLinkExtension M x = φ := by
      apply Subtype.ext
      change lambdaStarRealZeroExtension (B := cube M) (cubeOrigin M)
          (euclideanToFinsupp x) = (φ : RealLatticeChain 4)
      rw [hx]
      exact lambdaStarRealZeroExtension_compression_of_support M
        (φ : RealLatticeChain 4) hsuppφ
    have hfiniteObj :
        finiteVariationalObjective (sourceLatticeComplex (B := cube M))
          ⟨cubeLinkRestriction M (μ : RealLatticeChain 4), hW M hM₀⟩ x =
        globalVariationalObjective μ φ := by
      calc
        finiteVariationalObjective (sourceLatticeComplex (B := cube M))
            ⟨cubeLinkRestriction M (μ : RealLatticeChain 4), hW M hM₀⟩ x =
          globalVariationalObjective μ (cubeGlobalLinkExtension M x) :=
            cubeFiniteObjective_eq_global μ M (hW M hM₀) hsuppμ x
        _ = globalVariationalObjective μ φ :=
          congrArg (globalVariationalObjective μ) hext
    have hmax := quotientCovarianceQuadratic_isGreatest_variational
      (sourceLatticeComplex (B := cube M))
      ⟨cubeLinkRestriction M (μ : RealLatticeChain 4), hW M hM₀⟩
    have hMmono : max N₀ (Rμ + 2) ≤ M := by omega
    have hmono : ∀ k : ℕ, ∀ hk : M ≤ k,
        Q m ≤ Q ⟨k, le_trans hM₀ hk⟩ := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hk ih =>
          exact ih.trans (hmonoStep ⟨k, le_trans hMmono hk⟩)
    have hleAtM : globalVariationalObjective μ φ ≤ Q m := by
      have hleM := hmax.2 ⟨x, hfiniteObj⟩
      simpa [Q, m] using hleM
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    have hnval : M ≤ n.1 := by change M ≤ n.1 at hn; exact hn
    have hleLater : Q m ≤ Q n := by
      simpa using hmono n.1 hnval
    exact lt_of_lt_of_le har (hleAtM.trans hleLater)
  · intro a ha
    let M : ℕ := max N₀ (Rμ + 2)
    have hM₀ : N₀ ≤ M := by simp [M]
    have hMμ : Rμ + 2 ≤ M := by omega
    let m : {N : ℕ // N₀ ≤ N} := ⟨M, hM₀⟩
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    have hnval : M ≤ n.1 := by change M ≤ n.1 at hn; exact hn
    have hnμ : Rμ + 2 ≤ n.1 := le_trans hMμ hnval
    have hsuppμ : ∀ c ∈ (μ : RealLatticeChain 4).support,
        c ∈ Set.range (lambdaStarEmbedding (B := cube n.1) (cubeOrigin n.1)) :=
      cubeLinkSupport_subset_of_radius μ n.1 (by simpa [Rμ] using hnμ)
    have hle := cubeFiniteTrial_le_globalCovariance μ σ hfill n.1
      (hW n.1 n.2) hsuppμ
    exact lt_of_le_of_lt hle ha
end FroehlichSpencer.FS82.Infinite

end
