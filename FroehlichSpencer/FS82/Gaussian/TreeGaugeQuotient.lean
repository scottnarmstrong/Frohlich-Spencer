/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.TreeGauge
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Real tree-gauge coordinates on the gauge quotient

A rooted spanning tree gives a unique tree-zero representative of each real
edge field modulo exact gradients. Its chord values are linear coordinates on
the quotient. This is the chart layer needed before conditioning selected links.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient

open FroehlichSpencer.FS82.Poisson

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The real edge coboundary associated to a rooted tree gauge. -/
noncomputable def realCoboundaryMap (T : RootedTreeGauge V E) :
    (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun p e := T.coboundary p e
  map_add' p q := by
    funext e
    simp [RootedTreeGauge.coboundary, sub_add_sub_comm]
  map_smul' a p := by
    funext e
    simp [RootedTreeGauge.coboundary, mul_sub]

/-- Real edge fields modulo exact gradients. -/
abbrev RealGaugeQuotient (T : RootedTreeGauge V E) :=
  (E → ℝ) ⧸ LinearMap.range (realCoboundaryMap T)

/-- Integrating an edge field along the rooted tree is linear in that field. -/
theorem treePotential_add (T : RootedTreeGauge V E) (a b : E → ℝ) (x : V) :
    RootedTreeGauge.treePotential T (a + b) x =
      RootedTreeGauge.treePotential T a x + RootedTreeGauge.treePotential T b x := by
  have hdepth : ∀ n, ∀ x, T.depth x = n →
      RootedTreeGauge.treePotential T (a + b) x =
        RootedTreeGauge.treePotential T a x + RootedTreeGauge.treePotential T b x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hroot : x = T.root := by
          by_contra h
          have hp := T.depth_pos h
          omega
        subst x
        simp
    | succ n ih =>
        intro x hx
        by_cases hroot : x = T.root
        · have hzero : T.depth x = 0 := by rw [hroot, T.depth_root]
          omega
        · rw [RootedTreeGauge.treePotential_parent T (a + b) hroot,
            RootedTreeGauge.treePotential_parent T a hroot,
            RootedTreeGauge.treePotential_parent T b hroot]
          have hparent : T.depth (T.parent x) = n := by
            have := T.depth_parent hroot
            omega
          rw [ih (T.parent x) hparent]
          simp only [Pi.add_apply]
          ring
  exact hdepth (T.depth x) x rfl

theorem treePotential_smul (T : RootedTreeGauge V E) (r : ℝ)
    (a : E → ℝ) (x : V) :
    RootedTreeGauge.treePotential T (r • a) x =
      r * RootedTreeGauge.treePotential T a x := by
  have hdepth : ∀ n, ∀ x, T.depth x = n →
      RootedTreeGauge.treePotential T (r • a) x =
        r * RootedTreeGauge.treePotential T a x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hroot : x = T.root := by
          by_contra h
          have hp := T.depth_pos h
          omega
        subst x
        simp
    | succ n ih =>
        intro x hx
        by_cases hroot : x = T.root
        · have hzero : T.depth x = 0 := by rw [hroot, T.depth_root]
          omega
        · rw [RootedTreeGauge.treePotential_parent T (r • a) hroot,
            RootedTreeGauge.treePotential_parent T a hroot]
          have hparent : T.depth (T.parent x) = n := by
            have := T.depth_parent hroot
            omega
          rw [ih (T.parent x) hparent]
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
  exact hdepth (T.depth x) x rfl

/-- The rooted tree potential as a linear map on real edge fields. -/
noncomputable def treePotentialLinear (T : RootedTreeGauge V E) :
    (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun a := RootedTreeGauge.treePotential T a
  map_add' a b := funext (treePotential_add T a b)
  map_smul' r a := funext (treePotential_smul T r a)

/-- Subtract the exact gradient of the tree potential, leaving a tree-zero
representative. -/
noncomputable def treeNormalizeLinear (T : RootedTreeGauge V E) :
    (E → ℝ) →ₗ[ℝ] (E → ℝ) :=
  LinearMap.id - (realCoboundaryMap T).comp (treePotentialLinear T)

/-- Restriction to the chord coordinates of the rooted tree. -/
def restrictChordsLinear (T : RootedTreeGauge V E) :
    (E → ℝ) →ₗ[ℝ] (T.Chord → ℝ) where
  toFun a c := a c.1
  map_add' a b := by funext c; rfl
  map_smul' r a := by funext c; rfl

/-- The chord-coordinate linear map from edge fields. -/
noncomputable def treeChordMap (T : RootedTreeGauge V E) :
    (E → ℝ) →ₗ[ℝ] (T.Chord → ℝ) :=
  (restrictChordsLinear T).comp (treeNormalizeLinear T)

/-- A gradient normalizes to zero in tree gauge. -/
theorem treeNormalize_coboundary (T : RootedTreeGauge V E) (p : V → ℝ) :
    treeNormalizeLinear T (realCoboundaryMap T p) = 0 := by
  funext e
  have hp (x : V) :
      RootedTreeGauge.treePotential T (T.coboundary p) x = p x - p T.root := by
    have hdepth : ∀ n, ∀ x, T.depth x = n →
        RootedTreeGauge.treePotential T (T.coboundary p) x = p x - p T.root := by
      intro n
      induction n with
      | zero =>
          intro x hx
          have hroot : x = T.root := by
            by_contra h
            have hp := T.depth_pos h
            omega
          subst x
          simp
      | succ n ih =>
          intro x hx
          by_cases hroot : x = T.root
          · have hzero : T.depth x = 0 := by rw [hroot, T.depth_root]
            omega
          · rw [RootedTreeGauge.treePotential_parent T (T.coboundary p) hroot]
            have hparent : T.depth (T.parent x) = n := by
              have := T.depth_parent hroot
              omega
            rw [ih (T.parent x) hparent]
            simp only [RootedTreeGauge.coboundary, T.treeEdge_target, T.treeEdge_source]
            ring
    exact hdepth (T.depth x) x rfl
  change p (T.edgeTarget e) - p (T.edgeSource e) -
    (RootedTreeGauge.treePotential T (T.coboundary p) (T.edgeTarget e) -
      RootedTreeGauge.treePotential T (T.coboundary p) (T.edgeSource e)) = 0
  rw [hp (T.edgeTarget e), hp (T.edgeSource e)]
  ring

/-- The tree chord map annihilates every exact gradient. -/
theorem treeChordMap_vanishes_on_gradients (T : RootedTreeGauge V E) :
    LinearMap.range (realCoboundaryMap T) ≤ LinearMap.ker (treeChordMap T) := by
  rintro x ⟨p, rfl⟩
  change treeChordMap T (realCoboundaryMap T p) = 0
  rw [treeChordMap, LinearMap.comp_apply, treeNormalize_coboundary]
  funext c
  rfl


/-- The tree potential vanishes on a tree-zero edge field. -/
theorem treePotential_eq_zero_of_treeGauge (T : RootedTreeGauge V E)
    (a : E → ℝ) (ha : RootedTreeGauge.InTreeGauge T a) (x : V) :
    RootedTreeGauge.treePotential T a x = 0 := by
  have hdepth : ∀ n, ∀ x, T.depth x = n →
      RootedTreeGauge.treePotential T a x = 0 := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hroot : x = T.root := by
          by_contra h
          have hp := T.depth_pos h
          omega
        subst x
        simp
    | succ n ih =>
        intro x hx
        by_cases hroot : x = T.root
        · have hzero : T.depth x = 0 := by rw [hroot, T.depth_root]
          omega
        · rw [RootedTreeGauge.treePotential_parent T a hroot]
          have hparent : T.depth (T.parent x) = n := by
            have := T.depth_parent hroot
            omega
          rw [ih (T.parent x) hparent, ha ⟨x, hroot⟩]
          simp
  exact hdepth (T.depth x) x rfl

/-- Chord data extended by zero on the rooted-tree edges is linear. -/
noncomputable def extendChordsLinear (T : RootedTreeGauge V E) :
    (T.Chord → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := T.extendChord
  map_add' a b := by
    classical
    funext e
    by_cases he : e ∈ Set.range T.treeEdge
    · simp [RootedTreeGauge.extendChord, he]
    · simp [RootedTreeGauge.extendChord, he]
  map_smul' r a := by
    classical
    funext e
    by_cases he : e ∈ Set.range T.treeEdge
    · simp [RootedTreeGauge.extendChord, he]
    · simp [RootedTreeGauge.extendChord, he]

/-- Extending chord coordinates gives a tree-zero field. -/
theorem extendChordsLinear_mem_treeGauge (T : RootedTreeGauge V E)
    (x : T.Chord → ℝ) :
    RootedTreeGauge.InTreeGauge T (extendChordsLinear T x) := by
  intro y
  change T.extendChord x (T.treeEdge y) = 0
  simp [RootedTreeGauge.extendChord]

/-- Normalizing the zero extension of chord data leaves it unchanged. -/
theorem treeNormalize_extendChords (T : RootedTreeGauge V E)
    (x : T.Chord → ℝ) :
    treeNormalizeLinear T (extendChordsLinear T x) = extendChordsLinear T x := by
  have hp := treePotential_eq_zero_of_treeGauge T (extendChordsLinear T x)
    (extendChordsLinear_mem_treeGauge T x)
  funext e
  change extendChordsLinear T x e -
    (RootedTreeGauge.treePotential T (extendChordsLinear T x) (T.edgeTarget e) -
      RootedTreeGauge.treePotential T (extendChordsLinear T x) (T.edgeSource e)) =
      extendChordsLinear T x e
  rw [hp (T.edgeTarget e), hp (T.edgeSource e)]
  simp

/-- Applying the quotient chord map to a zero-extended chord field recovers it. -/
theorem treeChordMap_extendChords (T : RootedTreeGauge V E)
    (x : T.Chord → ℝ) :
    treeChordMap T (extendChordsLinear T x) = x := by
  change restrictChordsLinear T
    (treeNormalizeLinear T (extendChordsLinear T x)) = x
  rw [treeNormalize_extendChords]
  funext c
  change T.extendChord x c.1 = x c
  exact congrFun (RootedTreeGauge.restrict_extendChord T x) c

/-- Extending the chord coordinates of any field returns its normalized
representative. -/
theorem extendChords_treeChordMap (T : RootedTreeGauge V E) (a : E → ℝ) :
    extendChordsLinear T (treeChordMap T a) = treeNormalizeLinear T a := by
  have htree : RootedTreeGauge.InTreeGauge T (treeNormalizeLinear T a) := by
    intro x
    change a (T.treeEdge x) -
      T.coboundary (RootedTreeGauge.treePotential T a) (T.treeEdge x) = 0
    rw [RootedTreeGauge.treePotential_coboundary_treeEdge]
    ring
  change T.extendChord (T.restrictChord (treeNormalizeLinear T a)) =
    treeNormalizeLinear T a
  exact RootedTreeGauge.extend_restrictChord T htree


/-- The quotient map is sent to the unique tree-gauge chord coordinates. -/
noncomputable def quotientChordLinear (T : RootedTreeGauge V E) :
    RealGaugeQuotient T →ₗ[ℝ] (T.Chord → ℝ) :=
  Submodule.liftQ (LinearMap.range (realCoboundaryMap T))
    (treeChordMap T) (treeChordMap_vanishes_on_gradients T)

/-- The inverse chart lifts chord fields back to quotient classes. -/
noncomputable def quotientChordInverseLinear (T : RootedTreeGauge V E) :
    (T.Chord → ℝ) →ₗ[ℝ] RealGaugeQuotient T :=
  (LinearMap.range (realCoboundaryMap T)).mkQ.comp (extendChordsLinear T)

theorem quotientChordLinear_comp_inverse (T : RootedTreeGauge V E)
    (x : T.Chord → ℝ) :
    quotientChordLinear T (quotientChordInverseLinear T x) = x := by
  change (((LinearMap.range (realCoboundaryMap T)).liftQ (treeChordMap T)
      (treeChordMap_vanishes_on_gradients T)).comp
      (LinearMap.range (realCoboundaryMap T)).mkQ)
      (extendChordsLinear T x) = x
  rw [Submodule.liftQ_mkQ]
  exact treeChordMap_extendChords T x

theorem quotientChordInverse_comp_linear (T : RootedTreeGauge V E)
    (q : RealGaugeQuotient T) :
    quotientChordInverseLinear T (quotientChordLinear T q) = q := by
  refine Submodule.Quotient.induction_on
    (p := LinearMap.range (realCoboundaryMap T)) q ?_
  intro a
  change (LinearMap.range (realCoboundaryMap T)).mkQ
      (extendChordsLinear T (treeChordMap T a)) =
    (LinearMap.range (realCoboundaryMap T)).mkQ a
  rw [extendChords_treeChordMap]
  change Submodule.Quotient.mk (treeNormalizeLinear T a) =
    Submodule.Quotient.mk a
  apply (Submodule.Quotient.eq (LinearMap.range (realCoboundaryMap T))).2
  change treeNormalizeLinear T a - a ∈ LinearMap.range (realCoboundaryMap T)
  refine ⟨-treePotentialLinear T a, ?_⟩
  funext e
  change T.coboundary (-treePotentialLinear T a) e =
    (treeNormalizeLinear T a) e - a e
  simp [treeNormalizeLinear, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, treePotentialLinear, realCoboundaryMap,
    RootedTreeGauge.coboundary]
  ring

/-- Linear equivalence between the real gauge quotient and its tree-chord chart. -/
noncomputable def realGaugeQuotientChordEquiv (T : RootedTreeGauge V E) :
    RealGaugeQuotient T ≃ₗ[ℝ] (T.Chord → ℝ) where
  toFun := quotientChordLinear T
  invFun := quotientChordInverseLinear T
  left_inv := quotientChordInverse_comp_linear T
  right_inv := quotientChordLinear_comp_inverse T
  map_add' := (quotientChordLinear T).map_add
  map_smul' := (quotientChordLinear T).map_smul


end FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient

end
