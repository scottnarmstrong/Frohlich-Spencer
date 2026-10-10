/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
import Mathlib.Tactic.Ring

/-!
# Integer gauge relation and physical dual embedding

Integer potentials remain integer-valued and finitely supported, with their
exact shifts supported inside the finite physical dual-link carrier.

Every
embedding is the shared C1 `Cubical.lambdaStarEmbedding` based on
`Cubical.dualEmbedCoord`; no second coordinate map is defined here.

This
lattice-coordinate gauge relation is kept separate from the star-oriented
`sourceDualD₀`/`sourceDualD₁` complex.

Their linkwise integer sign transport is
part of the bridge, not an identity asserted in this module.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open scoped InnerProductSpace
open FroehlichSpencer.FS82.Cubical

@[expose] noncomputable def sourcePhysicalDualZeroExtension {B : SourceBox}
    (origin : Fin 4 → ℤ) :
    Cubical.DualRealChain 4 B →ₗ[ℝ] Cubical.RealLatticeChain 4 :=
  Finsupp.linearCombination ℝ
    (fun c : Cubical.DualCell 4 B =>
      Finsupp.single (Cubical.dualCellEmbedding (B := B) origin c) 1)

@[simp] theorem sourcePhysicalDualZeroExtension_single {B : SourceBox}
    (origin : Fin 4 → ℤ) (c : Cubical.DualCell 4 B) (r : ℝ) :
    sourcePhysicalDualZeroExtension origin (Finsupp.single c r) =
      Finsupp.single (Cubical.dualCellEmbedding (B := B) origin c) r := by
  simp [sourcePhysicalDualZeroExtension, Finsupp.linearCombination_single]

@[expose] noncomputable def sourceRealLatticeCoboundary :
    Cubical.RealLatticeChain 4 →ₗ[ℝ] Cubical.RealLatticeChain 4 :=
  Finsupp.linearCombination ℝ
    (fun c : Cubical.LatticeCell 4 =>
      Cubical.castLatticeChain (Cubical.latticeCoboundaryBasis c))

theorem sourceRealLatticeCoboundary_single (c : Cubical.LatticeCell 4)
    (r : ℝ) : sourceRealLatticeCoboundary (Finsupp.single c r) =
      r • Cubical.castLatticeChain (Cubical.latticeCoboundaryBasis c) := by
  simp [sourceRealLatticeCoboundary, Finsupp.linearCombination_single]

theorem sourceLambdaStarEmbedding_preserves_coefficients {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : Cubical.LambdaStarChain B)
    (e : Cubical.LambdaStarLinks B) :
    Cubical.lambdaStarZeroExtension (B := B) origin q
      (Cubical.lambdaStarEmbedding (B := B) origin e) = q e := by
  rw [Cubical.lambdaStarZeroExtension_eq_embDomain]
  simp [Finsupp.embDomain_apply]

@[expose] def sourceLatticeVertex (c : Cubical.LatticeCell 4) : Prop :=
  ∀ i : Fin 4, (c i).isLeft

abbrev SourceIntegerPotential :=
  {γ : Cubical.LatticeChain 4 // ∀ c, ¬ sourceLatticeVertex c → γ c = 0}

abbrev SourceIntegerGaugeField (B : SourceBox) := SourceDualOneCells B → ℤ

/-- The integral C2 orientation character on a source dual link. -/
@[expose] def sourceIntegerOrientationSign {B : SourceBox}
    (e : SourceDualOneCells B) : ℤ :=
  (-1 : ℤ) ^ (((dualCellAxes e.1).sum fun i => i.val) +
    (dualCellAxes e.1).card)

theorem sourceIntegerOrientationSign_sq {B : SourceBox}
    (e : SourceDualOneCells B) : sourceIntegerOrientationSign e ^ 2 = 1 := by
  rw [pow_two]
  unfold sourceIntegerOrientationSign
  rw [← mul_pow]
  norm_num

/-- C2 transports integer link coefficients between the star orientation and
the physical lattice orientation. -/
@[expose] def sourceIntegerSignTwist {B : SourceBox}
    (A : SourceIntegerGaugeField B) : SourceIntegerGaugeField B :=
  fun e => sourceIntegerOrientationSign e * A e

theorem sourceIntegerSignTwist_involutive {B : SourceBox}
    (A : SourceIntegerGaugeField B) :
    sourceIntegerSignTwist (sourceIntegerSignTwist A) = A := by
  funext e
  simp only [sourceIntegerSignTwist]
  calc
    sourceIntegerOrientationSign e *
        (sourceIntegerOrientationSign e * A e) =
      (sourceIntegerOrientationSign e * sourceIntegerOrientationSign e) * A e := by
        ring
    _ = A e := by
      rw [← pow_two, sourceIntegerOrientationSign_sq]
      simp


@[expose] def sourceSupportedIntegerGaugeEquivalent {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (A Bfield : SourceIntegerGaugeField B) : Prop :=
  ∃ γ : SourceIntegerPotential,
    ((Cubical.latticeCoboundary γ.1).support :
      Set (Cubical.LatticeCell 4)) ⊆
      Set.range (Cubical.lambdaStarEmbedding (B := B) origin) ∧
    ∀ e, A e - Bfield e =
      Cubical.latticeCoboundary γ.1
        (Cubical.lambdaStarEmbedding (B := B) origin e)


/-- The journal's exact-shift relation (2.26), written on star-oriented
integer link fields and with its support restriction retained. -/
@[expose] def sourceExactShiftSupportCondition226 {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (A Bfield : SourceIntegerGaugeField B) : Prop :=
  ∃ γ : SourceIntegerPotential,
    ((Cubical.latticeCoboundary γ.1).support :
      Set (Cubical.LatticeCell 4)) ⊆
      Set.range (Cubical.lambdaStarEmbedding (B := B) origin) ∧
    ∀ e, sourceIntegerOrientationSign e * (A e - Bfield e) =
      Cubical.latticeCoboundary γ.1
        (Cubical.lambdaStarEmbedding (B := B) origin e)

/-- After C2 transport, the exact-shift support condition is precisely the
source equivalence relation (2.26). -/
theorem sourceExactShiftSupportCondition226_iff_sourceRelation
    {B : SourceBox} (origin : Fin 4 → ℤ)
    (A Bfield : SourceIntegerGaugeField B) :
    sourceExactShiftSupportCondition226 origin A Bfield ↔
      sourceSupportedIntegerGaugeEquivalent origin
        (sourceIntegerSignTwist A) (sourceIntegerSignTwist Bfield) := by
  constructor
  · rintro ⟨γ, hsupport, hshift⟩
    refine ⟨γ, hsupport, ?_⟩
    intro e
    calc
      sourceIntegerSignTwist A e - sourceIntegerSignTwist Bfield e =
          sourceIntegerOrientationSign e * (A e - Bfield e) := by
        simp only [sourceIntegerSignTwist]
        ring
      _ = Cubical.latticeCoboundary γ.1
          (Cubical.lambdaStarEmbedding (B := B) origin e) := hshift e
  · rintro ⟨γ, hsupport, hshift⟩
    refine ⟨γ, hsupport, ?_⟩
    intro e
    calc
      sourceIntegerOrientationSign e * (A e - Bfield e) =
          sourceIntegerSignTwist A e - sourceIntegerSignTwist Bfield e := by
        simp only [sourceIntegerSignTwist]
        ring
      _ = Cubical.latticeCoboundary γ.1
          (Cubical.lambdaStarEmbedding (B := B) origin e) := hshift e


end FroehlichSpencer.FS82.Gaussian
end
