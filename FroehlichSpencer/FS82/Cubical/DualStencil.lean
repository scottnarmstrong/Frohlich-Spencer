/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.DualComplex

/-!
# The finite dual `δd` stencil

Local coefficient expansion of the full-lattice `δd` stencil and its finite zero-exterior compression.

Source: FS82 journal (2.32)–(2.35), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

@[expose] def latticeDeltaDLocalExpansion {d : ℕ} (c : LatticeCell d) : LatticeChain d :=
  ∑ i : Fin d, match c i with
    | Sum.inr _ => 0
    | Sum.inl t =>
        ((-1 : ℤ) ^ latticeRankBefore c i) •
          (latticeBoundaryBasis (latticeEdgeCell c i (t - 1)) -
            latticeBoundaryBasis (latticeEdgeCell c i t))

theorem latticeDeltaD_basis_localExpansion {d : ℕ} (c : LatticeCell d) :
    latticeDeltaD (latticeBasis c) = latticeDeltaDLocalExpansion c := by
  change latticeBoundary (latticeCoboundary (latticeBasis c)) = _
  rw [latticeCoboundary_basis]
  unfold latticeDeltaDLocalExpansion latticeCoboundaryBasis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inr t => simp
  | inl t => simp [map_smul, map_sub, latticeBoundary_basis]

/-- The coefficient of one output cell in the signed local incidence
expansion.  Unfolding `latticeBoundaryBasis` gives the four signed sides of
each plaquette containing the input link. -/
@[expose] def latticeDeltaDLocalCoefficient {d : ℕ} (input output : LatticeCell d) : ℤ :=
  latticeDeltaDLocalExpansion input output

theorem latticeDeltaD_basis_localCoefficient {d : ℕ} (input output : LatticeCell d) :
    latticeDeltaD (latticeBasis input) output =
      latticeDeltaDLocalCoefficient input output := by
  rw [latticeDeltaD_basis_localExpansion]
  rfl

theorem realLatticeDeltaD_basis_localCoefficient {d : ℕ}
    (input output : LatticeCell d) :
    realLatticeDeltaD (Finsupp.single input (1 : ℝ)) output =
      (latticeDeltaDLocalCoefficient input output : ℝ) := by
  rw [realLatticeDeltaD, realifyLatticeLinearMap, Finsupp.linearCombination_single]
  simp only [one_smul]
  simp [castLatticeChain, Finsupp.mapRange_apply,
    latticeDeltaD_basis_localCoefficient]

/-- The finite compressed Gaussian operator is the matrix of the full local
incidence coefficients, with input restricted by zero extension and output
restricted to `Λ*`. -/
theorem piLambdaStarDeltaDReal_localCoefficients {B : Box 4}
    (origin : Fin 4 → ℤ) (q : LambdaStarRealChain B) (output : LambdaStarLinks B) :
    piLambdaStarDeltaDReal (B := B) origin q output =
      ∑ input : LambdaStarLinks B,
        q input *
          (latticeDeltaDLocalCoefficient
            (lambdaStarEmbedding (B := B) origin input)
            (lambdaStarEmbedding (B := B) origin output) : ℝ) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
      rw [map_add, Finsupp.add_apply, hq, hr, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro input hi
      simp [Finsupp.add_apply, add_mul]
  | single input a =>
      rw [piLambdaStarDeltaDReal_apply]
      simp only [lambdaStarRealZeroExtension, Finsupp.linearCombination_single,
        map_smul]
      rw [Finsupp.smul_apply, realLatticeDeltaD_basis_localCoefficient]
      simp [Finsupp.single_apply]

theorem piLambdaStarDeltaDReal_single_apply {B : Box 4}
    (origin : Fin 4 → ℤ) (input output : LambdaStarLinks B) (a : ℝ) :
    piLambdaStarDeltaDReal (B := B) origin (Finsupp.single input a) output =
      a * (latticeDeltaDLocalCoefficient
        (lambdaStarEmbedding (B := B) origin input)
        (lambdaStarEmbedding (B := B) origin output) : ℝ) := by
  rw [piLambdaStarDeltaDReal_localCoefficients]
  simp [Finsupp.single_apply]

end
end FroehlichSpencer.FS82.Cubical

end
