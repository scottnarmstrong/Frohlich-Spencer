/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.IntegerExactness
import Mathlib.Tactic

/-!
# Real cubical filling

Realification of the integer prism and degree-two filling for real degree-one cycles.
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

abbrev RealChain (d : ℕ) (B : Box d) := Cell d B →₀ ℝ

/-- A real chain is homogeneous when every supported cell has the stated degree. -/
@[expose] def realHomogeneousSupport {d : ℕ} {B : Box d} (q : RealChain d B) (k : ℕ) : Prop :=
  ∀ c ∈ q.support, cellDegree c = k

@[expose] def castIntegerChain {d : ℕ} {B : Box d} (q : Chain d B) : RealChain d B :=
  Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q

theorem castIntegerChain_basis {d : ℕ} {B : Box d} (c : Cell d B) :
    castIntegerChain (basisChain c) = Finsupp.single c (1 : ℝ) := by
  ext x
  by_cases hx : x = c <;> simp [castIntegerChain, basisChain, hx]

theorem castIntegerChain_int_smul {d : ℕ} {B : Box d} (z : ℤ) (q : Chain d B) :
    castIntegerChain (z • q) = (z : ℝ) • castIntegerChain q := by
  ext c
  simp [castIntegerChain, Finsupp.mapRange, Int.cast_mul]

theorem castIntegerChain_add {d : ℕ} {B : Box d} (q r : Chain d B) :
    castIntegerChain (q + r) = castIntegerChain q + castIntegerChain r := by
  ext c
  simp [castIntegerChain, Finsupp.mapRange]

theorem castIntegerChain_sub {d : ℕ} {B : Box d} (q r : Chain d B) :
    castIntegerChain (q - r) = castIntegerChain q - castIntegerChain r := by
  ext c
  simp [castIntegerChain, Finsupp.mapRange]

@[expose] def realifyLinearMap {d : ℕ} {B : Box d} (T : Chain d B →ₗ[ℤ] Chain d B) :
    RealChain d B →ₗ[ℝ] RealChain d B :=
  Finsupp.linearCombination ℝ (fun c : Cell d B => castIntegerChain (T (basisChain c)))

theorem realifyLinearMap_cast {d : ℕ} {B : Box d}
    (T : Chain d B →ₗ[ℤ] Chain d B) (q : Chain d B) :
    realifyLinearMap T (castIntegerChain q) = castIntegerChain (T q) := by
  induction q using Finsupp.induction_linear with
  | zero => simp [realifyLinearMap, castIntegerChain]
  | add q₁ q₂ h₁ h₂ =>
      calc
        realifyLinearMap T (castIntegerChain (q₁ + q₂)) =
            realifyLinearMap T (castIntegerChain q₁ + castIntegerChain q₂) := by
              rw [castIntegerChain_add]
        _ = castIntegerChain (T q₁) + castIntegerChain (T q₂) := by
              rw [map_add, h₁, h₂]
        _ = castIntegerChain (T (q₁ + q₂)) := by
              rw [map_add, castIntegerChain_add]
  | single c z =>
      have hs : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [basisChain, hx]
      rw [hs]
      calc
        realifyLinearMap T (castIntegerChain (z • basisChain c)) =
            realifyLinearMap T ((z : ℝ) • castIntegerChain (basisChain c)) := by
              rw [castIntegerChain_int_smul]
        _ = (z : ℝ) • realifyLinearMap T (castIntegerChain (basisChain c)) := by
              rw [map_smul]
        _ = (z : ℝ) • castIntegerChain (T (basisChain c)) := by
              rw [show castIntegerChain (basisChain c) = Finsupp.single c (1 : ℝ) by
                exact castIntegerChain_basis c]
              simp [realifyLinearMap, basisChain]
        _ = castIntegerChain (z • T (basisChain c)) := by
              rw [castIntegerChain_int_smul]
        _ = castIntegerChain (T (z • basisChain c)) := by rw [map_smul]

theorem realifyLinearMap_single {d : ℕ} {B : Box d}
    (T : Chain d B →ₗ[ℤ] Chain d B) (c : Cell d B) (r : ℝ) :
    realifyLinearMap T (Finsupp.single c r) =
      r • castIntegerChain (T (basisChain c)) := by
  have hs : Finsupp.single c r = r • Finsupp.single c 1 := by
    ext x
    by_cases hx : x = c <;> simp [hx]
  rw [hs, map_smul]
  simp [realifyLinearMap, basisChain, Finsupp.linearCombination_single]

theorem realifyLinearMap_mul {d : ℕ} {B : Box d}
    (S T : Chain d B →ₗ[ℤ] Chain d B) :
    realifyLinearMap (S * T) = realifyLinearMap S * realifyLinearMap T := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c r =>
      change realifyLinearMap (S * T) (Finsupp.single c r) =
        realifyLinearMap S (realifyLinearMap T (Finsupp.single c r))
      calc
        realifyLinearMap (S * T) (Finsupp.single c r) =
            r • castIntegerChain ((S * T) (basisChain c)) :=
              realifyLinearMap_single (S * T) c r
        _ = r • castIntegerChain (S (T (basisChain c))) := by rfl
        _ = r • realifyLinearMap S (castIntegerChain (T (basisChain c))) := by
              rw [realifyLinearMap_cast]
        _ = realifyLinearMap S (r • castIntegerChain (T (basisChain c))) := by
              rw [map_smul]
        _ = realifyLinearMap S (realifyLinearMap T (Finsupp.single c r)) := by
              rw [realifyLinearMap_single]

theorem realifyLinearMap_add {d : ℕ} {B : Box d}
    (S T : Chain d B →ₗ[ℤ] Chain d B) :
    realifyLinearMap (S + T) = realifyLinearMap S + realifyLinearMap T := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c r =>
      change realifyLinearMap (S + T) (Finsupp.single c r) =
        realifyLinearMap S (Finsupp.single c r) + realifyLinearMap T (Finsupp.single c r)
      calc
        realifyLinearMap (S + T) (Finsupp.single c r) =
            r • castIntegerChain ((S + T) (basisChain c)) :=
              realifyLinearMap_single (S + T) c r
        _ = r • (castIntegerChain (S (basisChain c)) +
            castIntegerChain (T (basisChain c))) := by
              change r • castIntegerChain (S (basisChain c) + T (basisChain c)) = _
              rw [castIntegerChain_add]
        _ = r • castIntegerChain (S (basisChain c)) +
            r • castIntegerChain (T (basisChain c)) := by rw [smul_add]
        _ = realifyLinearMap S (Finsupp.single c r) +
            realifyLinearMap T (Finsupp.single c r) := by
              rw [realifyLinearMap_single, realifyLinearMap_single]

theorem realifyLinearMap_sub {d : ℕ} {B : Box d}
    (S T : Chain d B →ₗ[ℤ] Chain d B) :
    realifyLinearMap (S - T) = realifyLinearMap S - realifyLinearMap T := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c r =>
      change realifyLinearMap (S - T) (Finsupp.single c r) =
        realifyLinearMap S (Finsupp.single c r) - realifyLinearMap T (Finsupp.single c r)
      calc
        realifyLinearMap (S - T) (Finsupp.single c r) =
            r • castIntegerChain ((S - T) (basisChain c)) :=
              realifyLinearMap_single (S - T) c r
        _ = r • (castIntegerChain (S (basisChain c)) -
            castIntegerChain (T (basisChain c))) := by
              change r • castIntegerChain (S (basisChain c) - T (basisChain c)) = _
              rw [castIntegerChain_sub]
        _ = r • castIntegerChain (S (basisChain c)) -
            r • castIntegerChain (T (basisChain c)) := by rw [smul_sub]
        _ = realifyLinearMap S (Finsupp.single c r) -
            realifyLinearMap T (Finsupp.single c r) := by
              rw [realifyLinearMap_single, realifyLinearMap_single]

theorem realifyLinearMap_id {d : ℕ} {B : Box d} :
    realifyLinearMap (LinearMap.id : Chain d B →ₗ[ℤ] Chain d B) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c r =>
      rw [realifyLinearMap_single]
      change r • castIntegerChain (basisChain c) = Finsupp.single c r
      rw [castIntegerChain_basis]
      simp

@[expose] def realBoundary {d : ℕ} {B : Box d} : RealChain d B →ₗ[ℝ] RealChain d B :=
  realifyLinearMap boundary

@[expose] def realFillingOperator {d : ℕ} {B : Box d} (anchor : Anchor d B) :
    RealChain d B →ₗ[ℝ] RealChain d B := realifyLinearMap (fillingOperator anchor)

private theorem castIntegerChain_homogeneousSupport {d : ℕ} {B : Box d}
    (q : Chain d B) (k : ℕ) (hq : homogeneousSupport q k) :
    realHomogeneousSupport (castIntegerChain q) k := by
  intro c hc
  exact hq c (Finsupp.support_mapRange hc)

/-- Realification preserves the dimension raised by each prism summand. -/
theorem real_filling_homogeneousSupport {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : RealChain d B) (k : ℕ)
    (hq : realHomogeneousSupport q k) :
    realHomogeneousSupport (realFillingOperator anchor q) (k + 1) := by
  change ∀ c ∈ (Finsupp.linearCombination ℝ
    (fun c => castIntegerChain (fillingOperator anchor (basisChain c))) q).support,
      cellDegree c = k + 1
  apply homogeneousSupport_linearCombination_raise cellDegree cellDegree
    (fun c : Cell d B => castIntegerChain (fillingOperator anchor (basisChain c)))
    (by
      intro c x hx
      have hfill := fillingOperator_homogeneousSupport anchor (basisChain c)
        (cellDegree c) (homogeneousSupport_basis c)
      have hcast := castIntegerChain_homogeneousSupport
        (fillingOperator anchor (basisChain c)) (cellDegree c + 1) hfill
      exact hcast x hx) q k hq

/--
The degree-two support conclusion for a controlled filling.
-/
theorem real_degree_one_filling_degree_two_support {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : RealChain d B)
    (hq : realHomogeneousSupport q 1) :
    realHomogeneousSupport (realFillingOperator anchor q) 2 := by
  simpa using real_filling_homogeneousSupport anchor q 1 hq

@[expose] def realFinalProjection {d : ℕ} {B : Box d} (anchor : Anchor d B) :
    RealChain d B →ₗ[ℝ] RealChain d B := realifyLinearMap (finalProjection anchor)

@[expose] def realPositiveDegreeSupport {d : ℕ} {B : Box d} (q : RealChain d B) : Prop :=
  ∀ c ∈ q.support, 0 < cellDegree c

theorem realFinalProjection_kills_positiveSupport {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : RealChain d B) (hq : realPositiveDegreeSupport q) :
    realFinalProjection anchor q = 0 := by
  classical
  rw [← Finsupp.sum_single q]
  unfold Finsupp.sum
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro c hc
  have hsingle : Finsupp.single c (q c) = q c • Finsupp.single c 1 := by
    ext x
    by_cases hx : x = c <;> simp [hx]
  rw [hsingle, map_smul]
  change (q c) • realifyLinearMap (finalProjection anchor) (Finsupp.single c 1) = 0
  rw [realifyLinearMap_single]
  have hkill := orderedPrismProjection_kills_positiveCell anchor c (hq c hc)
  have hcast : castIntegerChain (finalProjection anchor (basisChain c)) = 0 := by
    simpa [finalProjection, castIntegerChain] using congrArg castIntegerChain hkill
  rw [hcast]
  simp

theorem real_degree_one_filling {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : RealChain d B)
    (hone : ∀ c ∈ q.support, cellDegree c = 1)
    (hcycle : realBoundary q = 0) :
    realBoundary (realFillingOperator anchor q) = q := by
  have hpositive : realPositiveDegreeSupport q := by
    intro c hc
    rw [hone c hc]
    omega
  have hprismInt := fillingOperator_prism_identity anchor
  have hprism := congrArg realifyLinearMap hprismInt
  rw [realifyLinearMap_add, realifyLinearMap_mul, realifyLinearMap_mul,
    realifyLinearMap_sub, realifyLinearMap_id] at hprism
  have hprismQ := congrArg (fun T : RealChain d B →ₗ[ℝ] RealChain d B => T q) hprism
  change realBoundary (realFillingOperator anchor q) +
      realFillingOperator anchor (realBoundary q) =
    q - realFinalProjection anchor q at hprismQ
  rw [hcycle, map_zero, realFinalProjection_kills_positiveSupport anchor q hpositive,
    sub_zero, add_zero] at hprismQ
  exact hprismQ

/-- A positive-degree real cycle has a homogeneous filling one degree higher. -/
theorem real_positiveDegree_filling {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : RealChain d B) (k : ℕ) (hk : 0 < k)
    (hq : realHomogeneousSupport q k) (hcycle : realBoundary q = 0) :
    realBoundary (realFillingOperator anchor q) = q ∧
      realHomogeneousSupport (realFillingOperator anchor q) (k + 1) := by
  have hpositive : realPositiveDegreeSupport q := by
    intro c hc
    rw [hq c hc]
    exact hk
  have hprismInt := fillingOperator_prism_identity anchor
  have hprism := congrArg realifyLinearMap hprismInt
  rw [realifyLinearMap_add, realifyLinearMap_mul, realifyLinearMap_mul,
    realifyLinearMap_sub, realifyLinearMap_id] at hprism
  have hprismQ := congrArg (fun T : RealChain d B →ₗ[ℝ] RealChain d B => T q) hprism
  change realBoundary (realFillingOperator anchor q) +
      realFillingOperator anchor (realBoundary q) =
    q - realFinalProjection anchor q at hprismQ
  rw [hcycle, map_zero, realFinalProjection_kills_positiveSupport anchor q hpositive,
    sub_zero, add_zero] at hprismQ
  exact ⟨hprismQ, real_filling_homogeneousSupport anchor q k hq⟩

end
end FroehlichSpencer.FS82.Cubical

end
