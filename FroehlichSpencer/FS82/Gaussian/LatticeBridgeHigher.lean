/- Higher signed-incidence and source-Gaussian positivity consequences. -/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeBridge

/-!
# Signed differential bridge on finite dual chains

The chain map identities use the C1 physical embedding and C2 orientation
characters.

The source Hodge inverse positivity lemma is the finite exact
complex result.

Source: FS82 journal (2.17)–(2.18),
Fröhlich–Spencer (1982); Gaussian formula
(2.36), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open FroehlichSpencer.FS82.Cubical

theorem sourceDualT_cast_eq_orientationSign {B : SourceBox}
    (e : SourceDualOneCells B) :
    (sourceDualT e : ℝ) = dualCellOrientationSign e.1 := by
  simp [sourceDualT, dualAxisSum, dualCellOrientationSign,
    axisSetOrientationSign, Int.cast_pow]

theorem sourceIntegerOrientationSign_eq_sourceDualT {B : SourceBox}
    (e : SourceDualOneCells B) :
    sourceIntegerOrientationSign e = sourceDualT e := by
  simp [sourceIntegerOrientationSign, sourceDualT, dualAxisSum]

theorem sourceDualSigma_cast_eq_orientationSign {B : SourceBox}
    (f : SourceDualTwoCells B) :
    (sourceDualSigma f : ℝ) = dualCellOrientationSign f.1 := by
  simp [sourceDualSigma, dualAxisSum, dualCellOrientationSign,
    axisSetOrientationSign, Int.cast_pow]

@[expose] noncomputable def sourceDualTMap {B : SourceBox} :
    LambdaStarRealChain B →ₗ[ℝ] LambdaStarRealChain B :=
  Finsupp.linearCombination ℝ
    (fun e : SourceDualOneCells B => Finsupp.single e
      (dualCellOrientationSign e.1))

theorem sourceDualTMap_apply {B : SourceBox}
    (q : LambdaStarRealChain B) (e : SourceDualOneCells B) :
    sourceDualTMap q e = dualCellOrientationSign e.1 * q e := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [sourceDualTMap]
  | add q r hq hr =>
      rw [map_add, Finsupp.add_apply, hq, hr]
      rw [Finsupp.add_apply]
      ring
  | single a r =>
      by_cases h : a = e
      · subst a
        simp [sourceDualTMap, Finsupp.linearCombination_single,
          mul_comm]
      · simp [sourceDualTMap, Finsupp.linearCombination_single,
          h]

@[expose] noncomputable def dualOrientationSignTwist {B : SourceBox} :
    DualRealChain 4 B →ₗ[ℝ] DualRealChain 4 B :=
  Finsupp.linearCombination ℝ
    (fun c : DualCell 4 B => Finsupp.single c (dualCellOrientationSign c))

theorem linearCombination_single_embedding_vanishes {α β : Type*}
    [DecidableEq β] (e : α ↪ β) (q : α →₀ ℝ) (c : β)
    (hc : c ∉ Set.range e) :
    Finsupp.linearCombination ℝ
      (fun a : α => Finsupp.single (e a) (1 : ℝ)) q c = 0 := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
      rw [map_add]
      change (Finsupp.linearCombination ℝ
        (fun a : α => Finsupp.single (e a) (1 : ℝ)) q) c +
        (Finsupp.linearCombination ℝ
          (fun a : α => Finsupp.single (e a) (1 : ℝ)) r) c = 0
      rw [hq, hr]
      simp
  | single a r =>
      have hne : e a ≠ c := by
        intro h
        exact hc ⟨a, h⟩
      simp [Finsupp.linearCombination_single, hne]

theorem linearCombination_single_embedding_hits {α β : Type*}
    [DecidableEq β] (e : α ↪ β) (q : α →₀ ℝ) (a : α) :
    Finsupp.linearCombination ℝ
      (fun x : α => Finsupp.single (e x) (1 : ℝ)) q (e a) = q a := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
      simp [map_add, Finsupp.add_apply, hq, hr]
  | single x r =>
      by_cases h : x = a
      · subst x
        simp [Finsupp.linearCombination_single]
      · have hne : e x ≠ e a := fun he => h (e.injective he)
        simp [Finsupp.linearCombination_single, hne, h]

theorem dualOrientationSignTwist_single {B : SourceBox}
    (c : DualCell 4 B) (r : ℝ) :
    dualOrientationSignTwist (Finsupp.single c r) =
      Finsupp.single c (dualCellOrientationSign c * r) := by
  simp [dualOrientationSignTwist, Finsupp.linearCombination_single]
  rw [mul_comm]

theorem latticeOrientationSignTwist_apply (q : RealLatticeChain 4)
    (c : LatticeCell 4) :
    latticeOrientationSignTwist q c = latticeCellOrientationSign c * q c := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [latticeOrientationSignTwist]
  | add q r hq hr =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [hq, hr]
      ring
  | single a r =>
      by_cases h : a = c
      · subst c
        simp [latticeOrientationSignTwist, Finsupp.linearCombination_single,
          mul_comm]
      · simp [latticeOrientationSignTwist, Finsupp.linearCombination_single,
          h]

theorem sourcePhysicalDualZeroExtension_comp_dualExteriorDifference
    {B : SourceBox} (origin : Fin 4 → ℤ) :
    (sourcePhysicalDualZeroExtension origin).comp
        (dualExteriorDifference (d := 4) (B := B)) =
      (latticeOrientationSignTwist.comp (sourceRealLatticeCoboundary.comp
        ((sourcePhysicalDualZeroExtension origin).comp dualOrientationSignTwist))) := by
  classical
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp [map_add, hq, hr]
  | single c a =>
      rw [show Finsupp.single c a = a • Finsupp.single c (1 : ℝ) by simp]
      simp only [map_smul, LinearMap.comp_apply]
      rw [sourcePhysicalDualZeroExtension_differential_basis]
      simp [dualOrientationSignTwist_single, sourcePhysicalDualZeroExtension_single,
        sourceRealLatticeCoboundary_single, map_smul, smul_smul,
        mul_comm]

@[expose] def sourcePhysicalDualTwoEmbedding {B : SourceBox} (origin : Fin 4 → ℤ) :
    SourceDualTwoCells B ↪ LatticeCell 4 :=
  Function.Embedding.trans sourceDualTwoEmbedding
    (Cubical.dualCellEmbedding origin)

theorem sourcePhysicalDualZeroExtension_embedDualSubtype {B : SourceBox}
    (origin : Fin 4 → ℤ) {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ↪ DualCell 4 B) (q : α →₀ ℝ) :
    sourcePhysicalDualZeroExtension origin (embedDualSubtype e q) =
      Finsupp.linearCombination ℝ
        (fun a : α => Finsupp.single
          ((Function.Embedding.trans e (Cubical.dualCellEmbedding origin)) a) 1) q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp [map_add, hq, hr]
  | single a r =>
      simp [embedDualSubtype_apply_single, sourcePhysicalDualZeroExtension_single,
        Finsupp.linearCombination_single]

theorem sourceDualD₁_physical_bridge {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourcePhysicalDualZeroExtension origin
        (sourceDualTwoToChain (sourceDualD₁ x)) =
      latticeOrientationSignTwist
        (sourceRealLatticeCoboundary
          (sourcePhysicalDualZeroExtension origin
            (dualOrientationSignTwist (sourceDualOneToChain x)))) := by
  rw [sourceDualD₁_embed_eq_derivative]
  exact LinearMap.congr_fun
    (sourcePhysicalDualZeroExtension_comp_dualExteriorDifference origin)
    (sourceDualOneToChain x)

theorem sourceDualD₀_physical_bridge {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (x : EuclideanSpace ℝ (SourceDualZeroCells B)) :
    sourcePhysicalDualZeroExtension origin
        (sourceDualOneToChain (sourceDualD₀ x)) =
      latticeOrientationSignTwist
        (sourceRealLatticeCoboundary
          (sourcePhysicalDualZeroExtension origin
            (dualOrientationSignTwist (sourceDualZeroToChain x)))) := by
  rw [sourceDualD₀_embed_eq_derivative]
  exact LinearMap.congr_fun
    (sourcePhysicalDualZeroExtension_comp_dualExteriorDifference origin)
    (sourceDualZeroToChain x)


end FroehlichSpencer.FS82.Gaussian

end
