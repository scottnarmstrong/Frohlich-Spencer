/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.XYCurrent
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox
public import Mathlib.Topology.Sequences

/-!
# Actual subsequential limits of periodic XY correlations

For each fixed pair of lattice points, the even tori define a bounded real correlation sequence.
Compactness supplies a strictly increasing subsequence and its actual limit. The predicate
`IsPeriodicLimitPoint` below is defined by such a subsequence, so its members cannot be arbitrary
values unrelated to the finite-volume models.
-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ}

private theorem spinDensity_pos (β : ℝ) (θ : Angles L) : 0 < spinDensity L β θ := by
  unfold spinDensity
  exact Finset.prod_pos fun e he => Real.exp_pos _

private theorem continuous_spinDensity (β : ℝ) : Continuous (spinDensity L β) := by
  unfold spinDensity
  fun_prop

private theorem spinDensity_le_bound (β : ℝ) (θ : Angles L) :
    spinDensity L β θ ≤ ∏ _e : Bond L, Real.exp |β| := by
  unfold spinDensity
  apply Finset.prod_le_prod₀
  · intro e he
    exact (Real.exp_pos _).le
  · intro e he
    apply Real.exp_le_exp.mpr
    calc
      β * Real.cos (θ ((graph L).src e) - θ ((graph L).tgt e)) ≤
          |β * Real.cos (θ ((graph L).src e) - θ ((graph L).tgt e))| := le_abs_self _
      _ = |β| * |Real.cos (θ ((graph L).src e) - θ ((graph L).tgt e))| := abs_mul _ _
      _ ≤ |β| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |β| := by ring

private theorem spinDensity_integrable (β : ℝ) :
    Integrable (spinDensity L β) (rotatorRawAngleMeasure (Site L)) := by
  let μ := rotatorRawAngleMeasure (Site L)
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ, rotatorRawAngleMeasure]
    infer_instance
  have hcont := continuous_spinDensity (L := L) β
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards with θ
  rw [Real.norm_of_nonneg (spinDensity_pos (L := L) β θ).le]
  exact spinDensity_le_bound (L := L) β θ

private theorem rawAngleMeasure_univ_pos :
    0 < rotatorRawAngleMeasure (Site L) Set.univ := by
  unfold rotatorRawAngleMeasure
  rw [← Set.pi_univ (Set.univ : Set (Site L)), Measure.pi_pi]
  simp [Real.volume_Ico]
  positivity

/-- The normalized Gibbs law of the periodic XY torus. -/
def measure (L : ℕ) (β : ℝ) : Measure (Angles L) :=
  (rotatorRawAngleMeasure (Site L)).withDensity fun θ =>
    ENNReal.ofReal (spinDensity L β θ / partitionIntegral L β)

private theorem partitionIntegral_pos (L : ℕ) (β : ℝ) : 0 < partitionIntegral L β := by
  rw [partitionIntegral,
    integral_pos_iff_support_of_nonneg (fun θ => (spinDensity_pos (L := L) β θ).le)
      (spinDensity_integrable (L := L) β)]
  have hsupp : Function.support (spinDensity L β) = Set.univ := by
    ext θ
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (spinDensity_pos (L := L) β θ)
  rw [hsupp]
  exact rawAngleMeasure_univ_pos (L := L)

/-- The normalized torus law has total mass one. -/
theorem measure_univ (L : ℕ) (β : ℝ) : measure L β Set.univ = 1 := by
  have hZ := partitionIntegral_pos L β
  have hweight := spinDensity_integrable (L := L) β
  have hscaled : Integrable
      (fun θ : Angles L => spinDensity L β θ * (partitionIntegral L β)⁻¹)
      (rotatorRawAngleMeasure (Site L)) := hweight.mul_const _
  have hnonneg : 0 ≤ᵐ[rotatorRawAngleMeasure (Site L)]
      fun θ : Angles L => spinDensity L β θ * (partitionIntegral L β)⁻¹ := by
    filter_upwards with θ
    exact mul_nonneg (spinDensity_pos (L := L) β θ).le (inv_nonneg.mpr hZ.le)
  calc
    measure L β Set.univ =
        ∫⁻ θ, ENNReal.ofReal (spinDensity L β θ / partitionIntegral L β)
          ∂rotatorRawAngleMeasure (Site L) := by
            rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = ENNReal.ofReal
        (∫ θ, spinDensity L β θ / partitionIntegral L β
          ∂rotatorRawAngleMeasure (Site L)) := by
            simpa only [div_eq_mul_inv] using
              (ofReal_integral_eq_lintegral_ofReal hscaled hnonneg).symm
    _ = 1 := by
          have hintegral :
              (∫ θ, spinDensity L β θ / partitionIntegral L β
                ∂rotatorRawAngleMeasure (Site L)) =
                (∫ θ, spinDensity L β θ ∂rotatorRawAngleMeasure (Site L)) *
                  (partitionIntegral L β)⁻¹ := by
            calc
              _ = ∫ θ, spinDensity L β θ * (partitionIntegral L β)⁻¹
                    ∂rotatorRawAngleMeasure (Site L) := by
                      apply integral_congr_ae
                      exact ae_of_all _ fun θ => div_eq_mul_inv _ _
              _ = _ := integral_mul_const _ _
          rw [hintegral, ← partitionIntegral]
          simp [hZ.ne']

instance measure_isProbability (L : ℕ) (β : ℝ) : IsProbabilityMeasure (measure L β) :=
  IsProbabilityMeasure.mk (measure_univ L β)

/-- The normalized cosine two-point function on the periodic torus. -/
def twoPoint (L : ℕ) (β : ℝ) (a x : Site L) (ξ : ℤ) : ℝ :=
  ∫ θ : Angles L, Real.cos (ξ * (θ a - θ x)) ∂measure L β

private theorem spinDensity_eq_cosineWeight (L : ℕ) (β : ℝ) :
    spinDensity L β = Ginibre.cosineWeight (Ginibre.multigraphFrequency (graph L))
      (fun _ => β) := by
  funext θ
  unfold spinDensity Ginibre.cosineWeight Ginibre.cosineEnergy
  rw [← Real.exp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [Ginibre.phase_multigraphFrequency]

/-- The finite torus law is the general finite-graph cosine Gibbs measure, so Ginibre I applies
without a boundary comparison. -/
theorem measure_eq_cosineGibbs (L : ℕ) (β : ℝ) :
    measure L β = Ginibre.cosineGibbs (Ginibre.multigraphFrequency (graph L)) (fun _ => β) := by
  have hZ : partitionIntegral L β =
      Ginibre.cosinePartition (Ginibre.multigraphFrequency (graph L)) (fun _ => β) := by
    unfold partitionIntegral Ginibre.cosinePartition
    rw [spinDensity_eq_cosineWeight]
  rw [measure, Ginibre.cosineGibbs, hZ, spinDensity_eq_cosineWeight]

private theorem phase_twoPointFrequency (a x : Site L) (ξ : ℤ) (θ : Angles L) :
    Ginibre.phase (rotatorTwoPointFrequency a x ξ) θ = ξ * (θ a - θ x) := by
  unfold Ginibre.phase rotatorTwoPointFrequency
  simp only [Int.cast_add, Int.cast_ite, Int.cast_zero, Int.cast_neg]
  calc
    _ = ∑ v : Site L,
        ((if v = a then (ξ : ℝ) else 0) * θ v +
          (if v = x then (-(ξ : ℝ)) else 0) * θ v) := by
          apply Finset.sum_congr rfl
          intro v hv
          ring
    _ = ξ * θ a + (-(ξ : ℝ)) * θ x := by
          rw [Finset.sum_add_distrib]
          simp
    _ = ξ * (θ a - θ x) := by ring

/-- Ginibre I gives nonnegativity of every finite periodic cosine correlation. -/
theorem twoPoint_nonneg {L : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (a x : Site L) (ξ : ℤ) : 0 ≤ twoPoint L β a x ξ := by
  rw [twoPoint, measure_eq_cosineGibbs]
  have hphase : (fun θ : Angles L => Real.cos (ξ * (θ a - θ x))) =
      fun θ => Real.cos (Ginibre.phase (rotatorTwoPointFrequency a x ξ) θ) :=
    funext fun θ => by rw [phase_twoPointFrequency]
  rw [hphase]
  exact Ginibre.integral_cos_cosineGibbs_nonneg
    (Ginibre.multigraphFrequency (graph L)) (fun _ => hβ)
      (rotatorTwoPointFrequency a x ξ)

private theorem twoPointObservable_integrable (L : ℕ) (β : ℝ) (a x : Site L) (ξ : ℤ) :
    Integrable (fun θ : Angles L => Real.cos (ξ * (θ a - θ x))) (measure L β) := by
  have hf : Continuous (fun θ : Angles L => Real.cos (ξ * (θ a - θ x))) := by fun_prop
  refine Integrable.of_bound hf.aestronglyMeasurable 1 ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- Every finite-volume periodic two-point function is a genuine expectation in `[-1,1]`. -/
theorem twoPoint_mem_Icc (L : ℕ) (β : ℝ) (a x : Site L) (ξ : ℤ) :
    twoPoint L β a x ξ ∈ Set.Icc (-1) 1 := by
  let μ := measure L β
  have hf := twoPointObservable_integrable L β a x ξ
  have hlow : (∫ _θ : Angles L, (-1 : ℝ) ∂μ) ≤ twoPoint L β a x ξ := by
    unfold twoPoint
    exact integral_mono (integrable_const _) hf fun θ => Real.neg_one_le_cos _
  have hupp : twoPoint L β a x ξ ≤ (∫ _θ : Angles L, (1 : ℝ) ∂μ) := by
    unfold twoPoint
    exact integral_mono hf (integrable_const _) fun θ => Real.cos_le_one _
  have hconst : ∫ _θ : Angles L, (1 : ℝ) ∂μ = 1 := by
    simp [integral_const]
  have hconstneg : ∫ _θ : Angles L, (-1 : ℝ) ∂μ = -1 := by
    simp [integral_const]
  rw [Set.mem_Icc]
  rw [hconstneg] at hlow
  rw [hconst] at hupp
  exact ⟨hlow, hupp⟩

/-- The even side lengths used for periodic thermodynamic limits. -/
def side (n : ℕ) : ℕ := 2 * n + 4

theorem side_even (n : ℕ) : Even (side n) := ⟨n + 2, by simp [side]; omega⟩

theorem side_gt_two (n : ℕ) : 2 < side n := by simp [side]

private theorem side_pos (n : ℕ) : 0 < side n := by simp [side]

/-- Reduction of an integer coordinate to the canonical representative on an even torus. -/
def coordinate (n : ℕ) (z : ℤ) : Fin (side n) :=
  ⟨(z % (side n : ℤ)).toNat, by
    rw [Int.toNat_lt_of_ne_zero (Nat.ne_of_gt (side_pos n))]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast side_pos n)⟩

/-- The torus image of a fixed lattice point. -/
def siteOfPoint (n : ℕ) (u : ℤ × ℤ) : Site (side n) :=
  (coordinate n u.1, coordinate n u.2)

/-- The periodic correlation sequence for fixed lattice points, along all even `L ≥ 4`. -/
def twoPointSequence (β : ℝ) (ξ : ℤ) (u v : ℤ × ℤ) (n : ℕ) : ℝ :=
  twoPoint (side n) β (siteOfPoint n u) (siteOfPoint n v) ξ

/-- The countable family of all integer-frequency two-point observables on `ℤ²`. -/
abbrev TwoPointObservable := ℤ × ((ℤ × ℤ) × (ℤ × ℤ))

/-- The `n`th even torus correlation profile, with coordinates indexed by all two-point
observables. -/
def twoPointProfile (β : ℝ) (n : ℕ) : TwoPointObservable → ℝ :=
  fun o => twoPointSequence β o.1 o.2.1 o.2.2 n

/-- A joint periodic profile limit uses one strictly increasing torus subsequence for every
two-point observable. -/
def IsPeriodicProfileLimitPoint (β : ℝ) (g : TwoPointObservable → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ o, Tendsto (fun k => twoPointProfile β (φ k) o) atTop (𝓝 (g o))

/-- Compactness gives one actual subsequential limit for the full two-point correlation profile. -/
theorem exists_periodicProfileLimitPoint (β : ℝ) :
    ∃ g : TwoPointObservable → ℝ, IsPeriodicProfileLimitPoint β g := by
  let K : Set (TwoPointObservable → ℝ) :=
    Set.univ.pi fun _ : TwoPointObservable => Set.Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, twoPointProfile β n ∈ K := by
    intro n
    apply Set.mem_univ_pi.2
    intro o
    exact twoPoint_mem_Icc (side n) β (siteOfPoint n o.2.1)
      (siteOfPoint n o.2.2) o.1
  obtain ⟨g, hg, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := twoPointProfile β) hmem
  have hpoint := tendsto_pi_nhds.1 hlim
  exact ⟨g, φ, hφ, fun o => hpoint o⟩

/-- A periodic infinite-volume value means an actual limit along a strictly increasing sequence of
even tori. -/
def IsPeriodicLimitPoint (β : ℝ) (ξ : ℤ) (u v : ℤ × ℤ) (c : ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun k => twoPointSequence β ξ u v (φ k)) atTop (𝓝 c)

/-- Every coordinate of a joint profile limit is also an actual scalar periodic limit point. -/
theorem profileCoordinate_isPeriodicLimitPoint {β : ℝ} {g : TwoPointObservable → ℝ}
    (hg : IsPeriodicProfileLimitPoint β g) (o : TwoPointObservable) :
    IsPeriodicLimitPoint β o.1 o.2.1 o.2.2 (g o) := by
  obtain ⟨φ, hφ, hlim⟩ := hg
  exact ⟨φ, hφ, by simpa [twoPointProfile, twoPointSequence] using hlim o⟩

/-- For every inverse temperature and fixed observable, the even torus correlations have an
actual subsequential limit. -/
theorem exists_periodicLimitPoint (β : ℝ) (ξ : ℤ) (u v : ℤ × ℤ) :
    ∃ c : ℝ, IsPeriodicLimitPoint β ξ u v c := by
  let f : ℕ → ℝ := twoPointSequence β ξ u v
  have hbounded : ∀ n, f n ∈ Set.Icc (-1) 1 := by
    intro n
    exact twoPoint_mem_Icc (side n) β (siteOfPoint n u) (siteOfPoint n v) ξ
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  obtain ⟨c, hc, φ, hφ, hlim⟩ := hcompact.tendsto_subseq (x := f) hbounded
  exact ⟨c, φ, hφ, by simpa [f, Function.comp_def] using hlim⟩

/-- A uniform finite-torus lower bound passes to every actual periodic limit point. -/
theorem periodicLimitPoint_ge_of_uniformBound {β : ℝ} {ξ : ℤ} {u v : ℤ × ℤ} {c a : ℝ}
    (hc : IsPeriodicLimitPoint β ξ u v c)
    (hfinite : ∀ n, a ≤ twoPointSequence β ξ u v n) : a ≤ c := by
  obtain ⟨φ, hφ, hlim⟩ := hc
  exact ge_of_tendsto' hlim fun k => hfinite (φ k)

end FroehlichSpencer.BKT.Rotator.Periodic

end
