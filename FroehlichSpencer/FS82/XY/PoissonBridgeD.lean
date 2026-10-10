/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.IntegerFillingD
public import FroehlichSpencer.FS82.XY.PoissonLatticeD
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Cubical integral cycle lattice in every dimension

The integer degree-three, degree-two, and degree-one chains of a finite box
form an exact complex at degree two. Consequently the integer functionals
co-closed at the degree-two carrier are canonically the character lattice of
the XY bond-cycle lattice. This is the integral, dimension-generic
normalization bridge; the analytic Hodge/Poisson identity is assembled in a
separate layer.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open Module

/-- The integral chains supported in one cubical degree. -/
def degreeChainSubmodule {d : ℕ} {B : Box d} (k : ℕ) :
    Submodule ℤ (Chain d B) where
  carrier := {q | homogeneousSupport q k}
  zero_mem' := by
    intro c hc
    simp at hc
  add_mem' := by
    intro q r hq hr
    exact homogeneousSupport_add hq hr
  smul_mem' := by
    intro z q hq
    exact homogeneousSupport_smul z hq


/-- Degree-one chains that are cycles. -/
def degreeOneCycleSubmodule {d : ℕ} {B : Box d} :
    Submodule ℤ (degreeChainSubmodule (B := B) 1) where
  carrier := {q | boundary q.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro q r hq hr
    change boundary (q.1 + r.1) = 0
    rw [map_add, hq, hr, add_zero]
  smul_mem' := by
    intro z q hq
    change boundary (z • q.1) = 0
    rw [map_smul, hq, smul_zero]


/-- The coefficient of the bond chain attached to a mode field recovers that
mode. -/
theorem xyBondModeChain_coeff {d : ℕ} {B : Box d}
    (m : XYBondModes (B := B)) (b : XYBonds B) :
    xyBondModeChain m b.1 = m b := by
  classical
  unfold xyBondModeChain
  rw [Finsupp.finsetSum_apply]
  calc
    _ = ((m b) • basisChain b.1) b.1 := by
      apply Fintype.sum_eq_single b
      intro b' hne
      have hcell : b'.1 ≠ b.1 := fun heq => hne (Subtype.ext heq)
      simp [basisChain, hcell]
    _ = m b := by simp [basisChain]

/-- A divergence-free bond mode is exactly an integral degree-one cycle. -/
theorem xyBondCycleModes_boundary_zero {d : ℕ} {B : Box d}
    (m : XYBondModes (B := B)) (hm : xyBondModeDivergence m = 0) :
    boundary (xyBondModeChain m) = 0 := by
  apply Finsupp.ext
  intro c
  by_cases hc : cellDegree c = 0
  · let x : XYSites B := ⟨c, hc⟩
    simpa [xyBondModeDivergence, x] using congrFun hm x
  · by_contra hne
    have hcSupport : c ∈ (boundary (xyBondModeChain m)).support :=
      Finsupp.mem_support_iff.mpr hne
    have hdegree := xyIntegerBoundary_homogeneousSupport
      (xyBondModeChain m) 1 (by omega)
      (xyBondModeChain_homogeneousSupport m) c hcSupport
    omega

/-- Reindexing equivalence from the source integer cycle modes to the
degree-one cubical cycle lattice. -/
noncomputable def xyBondCycleModesEquivDegreeOneCycles {d : ℕ} {B : Box d} :
    XYEndpointCycleModes (B := B) ≃ degreeOneCycleSubmodule (B := B) where
  toFun m :=
    ⟨⟨xyBondModeChain m.1, xyBondModeChain_homogeneousSupport m.1⟩,
      xyBondCycleModes_boundary_zero m.1 m.2⟩
  invFun q :=
    ⟨fun b => q.1.1 b.1, by
      funext x
      have hcycle : boundary q.1.1 = 0 := q.2
      have hchain := xyBondModeChain_restrict q.1.1 q.1.2
      change boundary (xyBondModeChain (fun b => q.1.1 b.1)) x.1 = 0
      rw [hchain]
      exact congrArg (fun t : Chain d B => t x.1) hcycle⟩
  left_inv m := by
    apply Subtype.ext
    funext b
    exact xyBondModeChain_coeff m.1 b
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact xyBondModeChain_restrict q.1.1 q.1.2


/-- A finite integral basis for chains supported in any fixed cubical degree. -/
noncomputable def degreeChainBasis {d : ℕ} (B : Box d) (k : ℕ) :
    Σ n : ℕ, Basis (Fin n) ℤ (degreeChainSubmodule (B := B) k) :=
  Submodule.basisOfPid (Finsupp.basisSingleOne (R := ℤ) (ι := Cell d B))
    (degreeChainSubmodule (B := B) k)

/-- A finite integral basis for the degree-one cycle lattice. -/
noncomputable def degreeOneCycleBasis {d : ℕ} (B : Box d) :
    Σ n : ℕ, Basis (Fin n) ℤ (degreeOneCycleSubmodule (B := B)) :=
  Submodule.basisOfPid (degreeChainBasis B 1).2
    (degreeOneCycleSubmodule (B := B))


end FroehlichSpencer.FS82.XY
