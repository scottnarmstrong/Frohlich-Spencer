/- Signed source-to-lattice incidence identities for FS82 (2.17)–(2.18). -/
module

public import FroehlichSpencer.FS82.Gaussian.IntegerGauge

/-!
# Signed incidence between the source dual cells and lattice cells

The physical embedding is the uniform half-lattice shift C1, and the signs are
explicit axis-set orientation characters C2.

This module proves the chain
incidence bridge at every degree-one source basis cell.

Source: FS82 journal (2.17)–(2.18),
Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open FroehlichSpencer.FS82.Cubical
open scoped InnerProductSpace

/-! ## Coordinate orientation characters -/

@[expose] def dualAxisSum {B : SourceBox} (c : DualCell 4 B) : ℕ :=
  (dualCellAxes c).sum fun i => i.val

@[expose] def axisSetOrientationSign (s : Finset (Fin 4)) : ℝ :=
  (-1 : ℝ) ^ ((s.sum fun i => i.val) + s.card)

@[expose] def dualCellOrientationSign {B : SourceBox} (c : DualCell 4 B) : ℝ :=
  axisSetOrientationSign (dualCellAxes c)

@[expose] noncomputable def latticeCellAxes (c : LatticeCell 4) : Finset (Fin 4) := by
  classical exact Finset.univ.filter fun i => latticeIsEdge (c i)

@[expose] noncomputable def latticeCellOrientationSign (c : LatticeCell 4) : ℝ :=
  axisSetOrientationSign (latticeCellAxes c)

@[expose] def sourceDualT {B : SourceBox} (e : SourceDualOneCells B) : ℤ :=
  (-1 : ℤ) ^ (dualAxisSum e.1 + (dualCellAxes e.1).card)

@[expose] def sourceDualSigma {B : SourceBox} (f : SourceDualTwoCells B) : ℤ :=
  (-1 : ℤ) ^ (dualAxisSum f.1 + (dualCellAxes f.1).card)

theorem sourceDualT_is_pm_one {B : SourceBox} (e : SourceDualOneCells B) :
    sourceDualT e = 1 ∨ sourceDualT e = -1 := by
  simp only [sourceDualT]
  rcases Nat.even_or_odd (dualAxisSum e.1 + (dualCellAxes e.1).card) with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem sourceDualSigma_is_pm_one {B : SourceBox} (f : SourceDualTwoCells B) :
    sourceDualSigma f = 1 ∨ sourceDualSigma f = -1 := by
  simp only [sourceDualSigma]
  rcases Nat.even_or_odd (dualAxisSum f.1 + (dualCellAxes f.1).card) with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem latticeCellAxes_physical {B : SourceBox} (origin : Fin 4 → ℤ)
    (c : DualCell 4 B) :
    latticeCellAxes (Cubical.dualCellEmbedding origin c) = dualCellAxes c := by
  ext i
  simp only [latticeCellAxes, dualCellAxes, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change latticeIsEdge (Cubical.dualEmbedCoord origin i (c i)) ↔
    (c i).isRight
  cases h : c i <;> simp [Cubical.dualEmbedCoord, latticeIsEdge]

theorem latticeCellOrientationSign_physical {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) :
    latticeCellOrientationSign (Cubical.dualCellEmbedding origin c) =
      dualCellOrientationSign c := by
  simp [latticeCellOrientationSign, dualCellOrientationSign,
    axisSetOrientationSign, latticeCellAxes_physical]

theorem axisSetOrientationSign_insert (s : Finset (Fin 4))
    (i : Fin 4) (hi : i ∉ s) :
    axisSetOrientationSign (insert i s) =
      (-1 : ℝ) ^ (i.val + 1) * axisSetOrientationSign s := by
  rw [axisSetOrientationSign, Finset.sum_insert hi,
    Finset.card_insert_of_notMem hi, axisSetOrientationSign]
  rw [show i.val + (s.sum fun j => j.val) + (s.card + 1) =
      (i.val + 1) + ((s.sum fun j => j.val) + s.card) by omega]
  rw [pow_add]

theorem dualVertexRankBefore_add_latticeRankBefore {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) (i : Fin 4) :
    dualVertexRankBefore c i +
      latticeRankBefore (Cubical.dualCellEmbedding origin c) i = i.val := by
  classical
  have hEdge (j : Fin 4) :
      latticeIsEdge (Cubical.dualCellEmbedding origin c j) ↔ (c j).isRight := by
    cases h : c j <;> simp [Cubical.dualCellEmbedding,
      Cubical.dualEmbedCoord, h, latticeIsEdge]
  unfold dualVertexRankBefore latticeRankBefore
  let s : Finset (Fin 4) := Finset.univ.filter fun j => j < i
  have hs : s = Finset.Iio i := by
    ext j
    simp [s]
  have hcard :
      (s.filter fun j => (c j).isRight).card +
        (s.filter fun j => ¬ (c j).isRight).card = s.card := by
    simpa using
      (Finset.card_filter_add_card_filter_not (s := s)
        (p := fun j : Fin 4 => (c j).isRight))
  have hcard' :
      (s.filter fun j => ¬ (c j).isRight).card +
        (s.filter fun j => (c j).isRight).card = i.val := by
    rw [Nat.add_comm, hcard]
    rw [hs, Fin.card_Iio]
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  simp_rw [hEdge]
  simpa only [s] using hcard'

@[expose] noncomputable def latticeOrientationSignTwist : RealLatticeChain 4 →ₗ[ℝ] RealLatticeChain 4 :=
  Finsupp.linearCombination ℝ
    (fun c : LatticeCell 4 => Finsupp.single c (latticeCellOrientationSign c))

theorem latticeOrientationSignTwist_single (c : LatticeCell 4) (r : ℝ) :
    latticeOrientationSignTwist (Finsupp.single c r) =
      Finsupp.single c (latticeCellOrientationSign c * r) := by
  ext x
  by_cases h : x = c <;>
    simp [latticeOrientationSignTwist, Finsupp.linearCombination_single, h,
      mul_comm]

noncomputable def latticeCoboundaryTerm (c : LatticeCell 4) (i : Fin 4) :
    RealLatticeChain 4 :=
  match c i with
  | Sum.inl t =>
      ((-1 : ℝ) ^ latticeRankBefore c i) •
        (Finsupp.single (latticeEdgeCell c i (t - 1)) 1 -
          Finsupp.single (latticeEdgeCell c i t) 1)
  | Sum.inr _ => 0

theorem dualCellAxes_upperFace_insert {B : SourceBox} (c : DualCell 4 B)
    (i : Fin 4) (e : Fin (B i)) :
    dualCellAxes (dualUpperFace c i e) = insert i (dualCellAxes c) := by
  classical
  ext j
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    simp [dualUpperFace]
  · have hnew : dualUpperFace c i e j = c j := by
      simp [dualUpperFace, Function.update_of_ne hji]
    rw [hnew]
    simp [hji]

theorem dualCellAxes_lowerFace_insert {B : SourceBox} (c : DualCell 4 B)
    (i : Fin 4) (e : Fin (B i)) :
    dualCellAxes (dualLowerFace c i e) = insert i (dualCellAxes c) := by
  classical
  ext j
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    simp [dualLowerFace]
  · have hnew : dualLowerFace c i e j = c j := by
      simp [dualLowerFace, Function.update_of_ne hji]
    rw [hnew]
    simp [hji]

theorem Cubical.dualCellEmbedding_upperFace {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) (i : Fin 4) (e : Fin (B i)) :
    Cubical.dualCellEmbedding origin (dualUpperFace c i e) =
      latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
        (origin i + e.val + 1) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [dualUpperFace, Cubical.dualCellEmbedding,
      Cubical.dualEmbedCoord, latticeEdgeCell]
    ring
  · simp [dualUpperFace, Cubical.dualCellEmbedding,
      Cubical.dualEmbedCoord, latticeEdgeCell, Function.update_of_ne hji]

theorem Cubical.dualCellEmbedding_lowerFace {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) (i : Fin 4) (e : Fin (B i)) :
    Cubical.dualCellEmbedding origin (dualLowerFace c i e) =
      latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
        (origin i + e.val) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [dualLowerFace, Cubical.dualCellEmbedding,
      Cubical.dualEmbedCoord, latticeEdgeCell]
  · simp [dualLowerFace, Cubical.dualCellEmbedding,
      Cubical.dualEmbedCoord, latticeEdgeCell, Function.update_of_ne hji]

theorem orientationSign_input_output_mul_upper {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) (i : Fin 4) (e : Fin (B i))
    (hci : c i = Sum.inl e) :
    dualCellOrientationSign (dualUpperFace c i e) *
        dualCellOrientationSign c *
          (-1 : ℝ) ^ (latticeRankBefore
            (Cubical.dualCellEmbedding origin c) i + 1) =
      (-1 : ℝ) ^ dualVertexRankBefore c i := by
  have hi : i ∉ dualCellAxes c := by
    simp [dualCellAxes, hci]
  change axisSetOrientationSign (dualCellAxes (dualUpperFace c i e)) *
    axisSetOrientationSign (dualCellAxes c) *
      (-1 : ℝ) ^ (latticeRankBefore
        (Cubical.dualCellEmbedding origin c) i + 1) = _
  rw [dualCellAxes_upperFace_insert, axisSetOrientationSign_insert _ i hi]
  have hsquare : axisSetOrientationSign (dualCellAxes c) *
      axisSetOrientationSign (dualCellAxes c) = 1 := by
    unfold axisSetOrientationSign
    rw [← pow_add]
    norm_num
  have hrank := dualVertexRankBefore_add_latticeRankBefore origin c i
  have hexp : i.val + 1 + (latticeRankBefore
      (Cubical.dualCellEmbedding origin c) i + 1) =
      dualVertexRankBefore c i +
        2 * (latticeRankBefore (Cubical.dualCellEmbedding origin c) i + 1) := by
    omega
  calc
    _ = (-1 : ℝ) ^ (i.val + 1) *
        (axisSetOrientationSign (dualCellAxes c) * axisSetOrientationSign (dualCellAxes c)) *
        (-1 : ℝ) ^ (latticeRankBefore (Cubical.dualCellEmbedding origin c) i + 1) := by ring
    _ = (-1 : ℝ) ^ (i.val + 1) *
        (-1 : ℝ) ^ (latticeRankBefore (Cubical.dualCellEmbedding origin c) i + 1) := by rw [hsquare]; ring
    _ = (-1 : ℝ) ^ (i.val + 1 +
        (latticeRankBefore (Cubical.dualCellEmbedding origin c) i + 1)) := by rw [← pow_add]
    _ = (-1 : ℝ) ^ (dualVertexRankBefore c i +
        2 * (latticeRankBefore (Cubical.dualCellEmbedding origin c) i + 1)) := by rw [hexp]
    _ = (-1 : ℝ) ^ dualVertexRankBefore c i := by
      rw [pow_add, pow_mul]
      norm_num

theorem orientationSign_input_output_mul_lower {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) (i : Fin 4) (e : Fin (B i))
    (hci : c i = Sum.inl e) :
    dualCellOrientationSign (dualLowerFace c i e) *
        dualCellOrientationSign c *
          (-1 : ℝ) ^ latticeRankBefore
            (Cubical.dualCellEmbedding origin c) i =
      -(-1 : ℝ) ^ dualVertexRankBefore c i := by
  have hi : i ∉ dualCellAxes c := by
    simp [dualCellAxes, hci]
  change axisSetOrientationSign (dualCellAxes (dualLowerFace c i e)) *
    axisSetOrientationSign (dualCellAxes c) *
      (-1 : ℝ) ^ latticeRankBefore
        (Cubical.dualCellEmbedding origin c) i = _
  rw [dualCellAxes_lowerFace_insert, axisSetOrientationSign_insert _ i hi]
  have hsquare : axisSetOrientationSign (dualCellAxes c) *
      axisSetOrientationSign (dualCellAxes c) = 1 := by
    unfold axisSetOrientationSign
    rw [← pow_add]
    norm_num
  have hrank := dualVertexRankBefore_add_latticeRankBefore origin c i
  have hexp : i.val + 1 + latticeRankBefore
      (Cubical.dualCellEmbedding origin c) i =
      dualVertexRankBefore c i +
        2 * latticeRankBefore (Cubical.dualCellEmbedding origin c) i + 1 := by
    omega
  calc
    _ = (-1 : ℝ) ^ (i.val + 1) *
        (axisSetOrientationSign (dualCellAxes c) * axisSetOrientationSign (dualCellAxes c)) *
        (-1 : ℝ) ^ latticeRankBefore (Cubical.dualCellEmbedding origin c) i := by ring
    _ = (-1 : ℝ) ^ (i.val + 1) *
        (-1 : ℝ) ^ latticeRankBefore (Cubical.dualCellEmbedding origin c) i := by rw [hsquare]; ring
    _ = (-1 : ℝ) ^ (i.val + 1 +
        latticeRankBefore (Cubical.dualCellEmbedding origin c) i) := by rw [← pow_add]
    _ = (-1 : ℝ) ^ (dualVertexRankBefore c i +
        2 * latticeRankBefore (Cubical.dualCellEmbedding origin c) i + 1) := by rw [hexp]
    _ = -(-1 : ℝ) ^ dualVertexRankBefore c i := by
      rw [pow_add, pow_add, pow_mul]
      norm_num

theorem sourcePhysicalDualZeroExtension_differentialTerm {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) (i : Fin 4) :
    sourcePhysicalDualZeroExtension origin
        (match c i with
        | Sum.inl e =>
            ((-1 : ℝ) ^ dualVertexRankBefore c i) •
              (Finsupp.single (dualUpperFace c i e) 1 -
                Finsupp.single (dualLowerFace c i e) 1)
        | Sum.inr _ => 0) =
      dualCellOrientationSign c • latticeOrientationSignTwist
        (latticeCoboundaryTerm (Cubical.dualCellEmbedding origin c) i) := by
  classical
  cases hci : c i with
  | inl e =>
      have hcoord : (Cubical.dualCellEmbedding origin c) i =
          Sum.inl (origin i + e.val + 1) := by
        simp [Cubical.dualCellEmbedding, Cubical.dualEmbedCoord, hci]
      have hprev : origin i + e.val + 1 - 1 = origin i + e.val := by omega
      rw [(sourcePhysicalDualZeroExtension origin).map_smul,
        (sourcePhysicalDualZeroExtension origin).map_sub,
        sourcePhysicalDualZeroExtension_single,
        sourcePhysicalDualZeroExtension_single]
      rw [Cubical.dualCellEmbedding_upperFace,
        Cubical.dualCellEmbedding_lowerFace]
      simp only [latticeCoboundaryTerm, hcoord, hprev]
      have htwist : latticeOrientationSignTwist
          ((-1 : ℝ) ^ latticeRankBefore
            (Cubical.dualCellEmbedding origin c) i •
            (Finsupp.single (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
                (origin i + e.val)) 1 -
              Finsupp.single (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
                (origin i + e.val + 1)) 1)) =
        (-1 : ℝ) ^ latticeRankBefore
          (Cubical.dualCellEmbedding origin c) i •
          (Finsupp.single (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
              (origin i + e.val)) (latticeCellOrientationSign
                (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
                  (origin i + e.val))) -
            Finsupp.single (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
              (origin i + e.val + 1)) (latticeCellOrientationSign
                (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
                  (origin i + e.val + 1)))) := by
        rw [map_smul, map_sub, latticeOrientationSignTwist_single,
          latticeOrientationSignTwist_single]
        simp only [mul_one]
      rw [htwist]
      have hsignUpper : latticeCellOrientationSign
          (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
            (origin i + e.val + 1)) =
        dualCellOrientationSign (dualUpperFace c i e) := by
        rw [← Cubical.dualCellEmbedding_upperFace origin c i e]
        exact latticeCellOrientationSign_physical origin (dualUpperFace c i e)
      have hsignLower : latticeCellOrientationSign
          (latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
            (origin i + e.val)) =
        dualCellOrientationSign (dualLowerFace c i e) := by
        rw [← Cubical.dualCellEmbedding_lowerFace origin c i e]
        exact latticeCellOrientationSign_physical origin (dualLowerFace c i e)
      rw [hsignUpper, hsignLower]
      have hupper := orientationSign_input_output_mul_upper origin c i e hci
      have hlower := orientationSign_input_output_mul_lower origin c i e hci
      have hucoeff : dualCellOrientationSign c *
          (-1 : ℝ) ^ latticeRankBefore
            (Cubical.dualCellEmbedding origin c) i *
          -dualCellOrientationSign (dualUpperFace c i e) =
          (-1 : ℝ) ^ dualVertexRankBefore c i := by
        calc
          _ = dualCellOrientationSign (dualUpperFace c i e) *
              dualCellOrientationSign c *
                (-1 : ℝ) ^ (latticeRankBefore
                  (Cubical.dualCellEmbedding origin c) i + 1) := by ring
          _ = _ := hupper
      have hlcoeff : dualCellOrientationSign c *
          (-1 : ℝ) ^ latticeRankBefore
            (Cubical.dualCellEmbedding origin c) i *
          dualCellOrientationSign (dualLowerFace c i e) =
          -(-1 : ℝ) ^ dualVertexRankBefore c i := by
        calc
          _ = dualCellOrientationSign (dualLowerFace c i e) *
              dualCellOrientationSign c *
                (-1 : ℝ) ^ latticeRankBefore
                  (Cubical.dualCellEmbedding origin c) i := by ring
          _ = _ := hlower
      rw [smul_smul, smul_sub]
      have hneq : latticeEdgeCell (Cubical.dualCellEmbedding origin c) i
          (origin i + e.val + 1) ≠ latticeEdgeCell
            (Cubical.dualCellEmbedding origin c) i (origin i + e.val) := by
        intro h
        have hi := congrFun h i
        simp [latticeEdgeCell] at hi
      ext x
      by_cases hu : x = latticeEdgeCell (Cubical.dualCellEmbedding origin c)
          i (origin i + e.val + 1)
      · subst x
        simpa [Finsupp.smul_apply, Finsupp.single_apply, hneq] using hucoeff.symm
      · by_cases hl : x = latticeEdgeCell (Cubical.dualCellEmbedding origin c)
            i (origin i + e.val)
        · subst x
          simpa [Finsupp.smul_apply, Finsupp.single_apply, hneq] using hlcoeff.symm
        · simp [Finsupp.smul_apply, hu, hl]
  | inr e =>
      have hcoord : (Cubical.dualCellEmbedding origin c) i =
          Sum.inr (origin i + e.val) := by
        simp [Cubical.dualCellEmbedding, Cubical.dualEmbedCoord, hci]
      simp only [latticeCoboundaryTerm, hcoord]
      simp

theorem sourceRealLatticeCoboundary_single_eq_sum (c : LatticeCell 4) :
    sourceRealLatticeCoboundary (Finsupp.single c (1 : ℝ)) =
      ∑ i : Fin 4, latticeCoboundaryTerm c i := by
  classical
  rw [sourceRealLatticeCoboundary_single]
  simp only [one_smul]
  ext x
  simp only [castLatticeChain, Finsupp.mapRange_apply,
    latticeCoboundaryBasis, Finset.sum_apply']
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i <;>
    simp [latticeCoboundaryTerm, hci, latticeBasis, Finsupp.single_apply,
      Int.cast_pow, Int.cast_sub]

theorem sourcePhysicalDualZeroExtension_differential_basis {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : DualCell 4 B) :
    sourcePhysicalDualZeroExtension origin
        (dualExteriorDifference (Finsupp.single c (1 : ℝ))) =
      latticeOrientationSignTwist
        (dualCellOrientationSign c • sourceRealLatticeCoboundary
          (Finsupp.single (Cubical.dualCellEmbedding origin c) (1 : ℝ))) := by
  rw [dualExteriorDifference_basis_eq_coordinateStencil]
  unfold dualExteriorDifferenceStencilBasis
  rw [map_sum, sourceRealLatticeCoboundary_single_eq_sum,
    map_smul, map_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl e =>
      have ht := sourcePhysicalDualZeroExtension_differentialTerm origin c i
      rw [hci] at ht
      exact ht
  | inr e =>
      have ht := sourcePhysicalDualZeroExtension_differentialTerm origin c i
      rw [hci] at ht
      exact ht

end FroehlichSpencer.FS82.Gaussian

end
