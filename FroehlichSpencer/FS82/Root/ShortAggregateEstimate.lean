/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.SourcePackingEstimate
public import FroehlichSpencer.FS82.Currents.ShortComponentPacking

/-!
# FS82 ShortComponentPhase: the short-current aggregate and the root split

`sourceShortAggregate` is the `hShort` premise of `Root.sourcePacking_logThick`
(`Root/SourcePackingEstimate.lean`): for a finite family of co-closed currents with pairwise disjoint
supports, each of support length below a threshold `m ≤ B i`, and a generic amplitude `z`
below the renormalized exponential envelope,

`Σ_short γ(z) θ² ≤ 81 · sourceComponentCpackPrime(a, 50π·10⁴) · Σ_p (dτ'_p)²`,

where `θ` is the C2-oriented physical phase and `dτ'` the source Hodge field.

`sourcePacking_logThick_family` is the root split: a single family of co-closed currents with
pairwise disjoint supports is split by support length into its short and long parts, and
the total generic Jensen error is bounded by `sourceCoefficient` times the field energy.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.Moment.SourceAssembly
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Currents.SourcePacking
open FroehlichSpencer.FS82.Currents.ShortComponentPhase

noncomputable section

variable {B : Cubical.Box 4} {Ensemble : Type*}

/-- A lower corner for the source cube of every incidence component. -/
def componentLowerCorner (j : IntegerCurrent B) (c : CurrentComponentClass j) : Fin 4 → ℕ :=
  open Classical in
  if hc : c ∈ currentComponents j then (exists_component_cube j hc).choose else fun _ => 0

theorem componentLowerCorner_spec (j : IntegerCurrent B) {c : CurrentComponentClass j}
    (hc : c ∈ currentComponents j) :
    (∀ i, componentLowerCorner j c i ≤ B i + 1) ∧
      supportInSourceCube (currentComponentSupport j c) (componentLowerCorner j c)
        (2 * (currentComponentSupport j c).card) := by
  unfold componentLowerCorner
  rw [dite_eq_left hc]
  exact (exists_component_cube j hc).choose_spec

/-- The C2-oriented physical phase is the source phase against the twisted translation. -/
theorem sourcePhysicalTheta_eq_sourceCurrentPhase (beta : ℝ) (μ : SourceW B) (t : ℝ)
    (i : IntegerCurrent B) :
    Root.sourcePhysicalTheta beta μ t i =
      sourceCurrentPhase
        (twistedLinkField (sourceGaussianTranslation (B := B) beta t μ)) i :=
  inner_sourceDualTLinear_physicalCurrent _ i

/-- The energy of the local curvature of the Gaussian translation is the energy of the source
Hodge field. -/
theorem sum_localCurvature_sq_eq_hodgeField (beta : ℝ) (μ : SourceW B) (t : ℝ) :
    (∑ p : SourcePlaquette B,
        (localCurvature (sourceGaussianTranslation (B := B) beta t μ) p) ^ 2) =
      ∑ p, (sourceHodgeField μ (t * beta) p) ^ 2 :=
  sum_chainCoboundary_sq (sourceGaussianTranslation (B := B) beta t μ)

/-- **The short-current aggregate** (`hShort` of `sourcePacking_logThick`). -/
theorem sourceShortAggregate
    (beta beta₁ : ℝ) (m : ℕ) (hmin : ∀ i : Fin 4, m ≤ B i)
    (hRate : 1 ≤ sourceRenormalizedRate beta beta₁)
    (shortCurrents : SourceW B → Ensemble → Finset (IntegerCurrent B))
    (z : SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (hClosed : ∀ μ γ i, i ∈ shortCurrents μ γ → currentDivergence i = 0)
    (hShortLength : ∀ μ γ i, i ∈ shortCurrents μ γ →
      (currentSupport (fun e : Link B => i e)).card < m)
    (hDisjoint : ∀ μ γ,
      (↑(shortCurrents μ γ) : Set (IntegerCurrent B)).PairwiseDisjoint
        (fun i => currentSupport (fun e : Link B => i e)))
    (hAmplitude : ∀ μ γ i, i ∈ shortCurrents μ γ →
      0 ≤ z μ γ i ∧
      z μ γ i ≤ Real.exp (-(sourceRenormalizedRate beta beta₁ *
        (integerCurrentNormSq (fun e : Link B => i e) +
          ((currentSupport (fun e : Link B => i e)).card : ℝ))))) :
    ∀ μ t γ,
      (∑ i ∈ shortCurrents μ γ, genericSourceJensenError beta z μ t γ i) ≤
        81 * sourceComponentCpackPrime (sourceRenormalizedRate beta beta₁)
          (50 * Real.pi * 10000) *
          ∑ p, (sourceHodgeField μ (t * beta) p) ^ 2 := by
  intro μ t γ
  have ha : (0 : ℝ) < sourceRenormalizedRate beta beta₁ := lt_of_lt_of_le one_pos hRate
  have hparent : ∀ i ∈ shortCurrents μ γ,
      genericSourceJensenError beta z μ t γ i ≤
        ∑ c ∈ currentComponents i,
          sourceComponentActivityL5 (sourceRenormalizedRate beta beta₁)
              (50 * Real.pi * 10000) (currentComponentSupport i c).card *
            componentCurvatureMax (sourceGaussianTranslation (B := B) beta t μ)
              (componentLowerCorner i c) (currentComponentSupport i c).card ^ 2 := by
    intro i hi
    have hlen := hShortLength μ γ i hi
    rw [currentSupport_eq_support] at hlen
    have hamp := hAmplitude μ γ i hi
    rw [← currentEnergy_eq_integerCurrentNormSq, ← currentLength_eq_currentSupport_card]
      at hamp
    unfold genericSourceJensenError
    rw [sourcePhysicalTheta_eq_sourceCurrentPhase]
    exact shortParent_jensen_error_le i (hClosed μ γ i hi) m hmin hlen
      (sourceRenormalizedRate beta beta₁) (z μ γ i) hRate hamp.1 hamp.2
      (sourceGaussianTranslation (B := B) beta t μ) (componentLowerCorner i)
      (fun c hc => (componentLowerCorner_spec i hc).1)
      (fun c hc => (componentLowerCorner_spec i hc).2)
  have hdisj : (↑(shortCurrents μ γ) : Set (IntegerCurrent B)).PairwiseDisjoint
      fun j => j.support := by
    intro i hi j hj hij
    have h := hDisjoint μ γ hi hj hij
    simp only [Function.onFun, currentSupport_eq_support] at h
    exact h
  calc (∑ i ∈ shortCurrents μ γ, genericSourceJensenError beta z μ t γ i)
      ≤ ∑ i ∈ shortCurrents μ γ, ∑ c ∈ currentComponents i,
          sourceComponentActivityL5 (sourceRenormalizedRate beta beta₁)
              (50 * Real.pi * 10000) (currentComponentSupport i c).card *
            componentCurvatureMax (sourceGaussianTranslation (B := B) beta t μ)
              (componentLowerCorner i c) (currentComponentSupport i c).card ^ 2 :=
        Finset.sum_le_sum hparent
    _ ≤ 81 * sourceComponentCpackPrime (sourceRenormalizedRate beta beta₁)
          (50 * Real.pi * 10000) *
          ∑ p : SourcePlaquette B,
            (localCurvature (sourceGaussianTranslation (B := B) beta t μ) p) ^ 2 :=
        sum_componentMajorants_le (shortCurrents μ γ) hdisj _ ha _ componentLowerCorner
          (fun j _ c hc => (componentLowerCorner_spec j hc).2)
    _ = 81 * sourceComponentCpackPrime (sourceRenormalizedRate beta beta₁)
          (50 * Real.pi * 10000) *
          ∑ p, (sourceHodgeField μ (t * beta) p) ^ 2 := by
        rw [sum_localCurvature_sq_eq_hodgeField]

/-- **The root split.** A single family of co-closed currents with pairwise disjoint supports
and a generic amplitude below the renormalized envelope is split by support length: the parents
shorter than `m` go through their incidence components (`sourceShortAggregate`), the others
through the long-current estimate of `sourcePacking_logThick`. The total generic Jensen error is
at most `sourceCoefficient` times the energy of the source Hodge field. -/
theorem sourcePacking_logThick_family
    [DecidableEq (IntegerCurrent B)]
    (beta beta₁ : ℝ) (N m : ℕ)
    (hN : 1 ≤ N) (hmLog : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hRate : 8 ≤ sourceRenormalizedRate beta beta₁)
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    (F : SourceW B → Ensemble → Finset (ClosedIntegerCurrent B))
    (z : SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (hDisjoint : ∀ μ γ,
      (↑(F μ γ) : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
        (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hAmplitude : ∀ μ γ i,
      0 ≤ z μ γ i ∧
      z μ γ i ≤ Real.exp (-(sourceRenormalizedRate beta beta₁ *
        (integerCurrentNormSq (fun e : Link B => i e) +
          ((currentSupport (fun e : Link B => i e)).card : ℝ))))) :
    ∀ μ t γ,
      (∑ i ∈ (F μ γ).image (fun j : ClosedIntegerCurrent B => j.1),
        genericSourceJensenError beta z μ t γ i) ≤
        Root.sourceCoefficient beta₁ N m beta *
          ∑ p, (sourceHodgeField μ (t * beta) p) ^ 2 := by
  let Tshort : SourceW B → Ensemble → Finset (ClosedIntegerCurrent B) := fun μ γ =>
    (F μ γ).filter fun j => (currentSupport (fun e : Link B => j.1 e)).card < m
  let Tlong : SourceW B → Ensemble → Finset (ClosedIntegerCurrent B) := fun μ γ =>
    (F μ γ).filter fun j => m ≤ (currentSupport (fun e : Link B => j.1 e)).card
  let shortCurrents : SourceW B → Ensemble → Finset (IntegerCurrent B) := fun μ γ =>
    (Tshort μ γ).image fun j : ClosedIntegerCurrent B => j.1
  have hShort := sourceShortAggregate (Ensemble := Ensemble) beta beta₁ m hmin
    (by linarith) shortCurrents z
    (by
      intro μ γ i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact j.2)
    (by
      intro μ γ i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hj).2)
    (by
      intro μ γ i hi i' hi' hne
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi)
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi')
      exact hDisjoint μ γ (Finset.mem_coe.mpr (Finset.mem_filter.mp hj).1)
        (Finset.mem_coe.mpr (Finset.mem_filter.mp hj').1) (fun h => hne (by rw [h])))
    (fun μ γ i _ => hAmplitude μ γ i)
  have key := sourcePacking_logThick (Ensemble := Ensemble) beta beta₁ N m hN hmLog hRate
    shortCurrents z hShort Tlong
    (fun μ γ => (hDisjoint μ γ).subset (by
      intro j hj
      exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1))
    (fun μ γ j hj => (Finset.mem_filter.mp hj).2)
    hAmplitude hBmax
    (by
      intro μ γ
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j', hj', hjj⟩ := Finset.mem_image.mp hi'
      have hEq : j' = j := Subtype.ext hjj
      subst hEq
      have h1 := (Finset.mem_filter.mp hj).2
      have h2 := (Finset.mem_filter.mp hj').2
      omega)
  intro μ t γ
  have hunion : shortCurrents μ γ ∪
      (Tlong μ γ).image (fun j : ClosedIntegerCurrent B => j.1) =
      (F μ γ).image (fun j : ClosedIntegerCurrent B => j.1) := by
    rw [← Finset.image_union]
    congr 1
    ext j
    simp only [Tshort, Tlong, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases Nat.lt_or_ge (currentSupport (fun e : Link B => j.1 e)).card m with hlt | hge
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨h, hge⟩
  rw [← hunion]
  exact key μ t γ

end

end FroehlichSpencer.FS82.Root
