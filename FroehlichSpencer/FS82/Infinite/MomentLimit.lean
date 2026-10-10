/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.CubeExhaustion
public import FroehlichSpencer.FS82.Root.SourceMoment
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Ultrafilter

/-!
# Scalar infinite-volume moment limits along centered cubes

This module passes the finite scalar moment comparison to cluster values along
an eventual tail of the centered cube exhaustion. It does not construct an
infinite-volume state.
-/

@[expose] public section

open Filter Topology

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Moment.SourceConstructor

/-- The source moment on cube `N₀ + n`, once the global test has entered the
finite co-closed carrier on every cube in the tail. -/
noncomputable def cubeMomentTail (N₀ : ℕ) (β t : ℝ)
    (μ : GlobalLinkField)
    (hW : ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N) : ℕ → ℝ :=
  fun n => FroehlichSpencer.FS82.Root.sourceDualMoment β
    ⟨cubeLinkRestriction (N₀ + n) (μ : RealLatticeChain 4), hW _ (by omega)⟩ t

/-- The finite covariance on cube `N₀ + n`, paired with the same global test. -/
noncomputable def cubeCovarianceTail (N₀ : ℕ)
    (μ : GlobalLinkField)
    (hW : ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N) : ℕ → ℝ :=
  fun n => quotientCovarianceQuadratic (sourceLatticeComplex (B := cube (N₀ + n)))
    ⟨cubeLinkRestriction (N₀ + n) (μ : RealLatticeChain 4), hW _ (by omega)⟩

/-- A scalar cluster value of the finite-volume moment sequence along the cube
exhaustion tail. -/
def IsCubeMomentClusterPoint (M : ℕ → ℝ) (x : ℝ) : Prop :=
  MapClusterPt x atTop M

private theorem exp_linear_tendsto {ι : Type*} {f : Filter ι} {q : ι → ℝ}
    {qLimit c : ℝ} (hq : Tendsto q f (nhds qLimit)) :
    Tendsto (fun n => Real.exp (c * q n)) f (nhds (Real.exp (c * qLimit))) := by
  have hcont : Continuous (fun x : ℝ => Real.exp (c * x)) := by
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hcont.continuousAt.tendsto.comp hq

/-- A cluster value of a sequence squeezed between exponentials of a convergent
real sequence lies between the limiting exponentials. -/
theorem cubeMoment_cluster_bounds_of_squeeze
    {q M : ℕ → ℝ} {qLimit a b : ℝ}
    (hq : Tendsto q atTop (nhds qLimit))
    (hfinite : ∀ n, Real.exp (a * q n) ≤ M n ∧
      M n ≤ Real.exp (b * q n))
    (x : ℝ) (hx : IsCubeMomentClusterPoint M x) :
    Real.exp (a * qLimit) ≤ x ∧ x ≤ Real.exp (b * qLimit) := by
  rcases mapClusterPt_iff_ultrafilter.mp hx with ⟨U, hU, hM⟩
  have hqU : Tendsto q U (nhds qLimit) := hq.mono_left hU
  have hleft := exp_linear_tendsto (c := a) hqU
  have hright := exp_linear_tendsto (c := b) hqU
  constructor
  · exact le_of_tendsto_of_tendsto' hleft hM fun n => (hfinite n).1
  · exact le_of_tendsto_of_tendsto' hM hright fun n => (hfinite n).2


/-- Squeeze theorem for the cube moment sequence, including existence of a
cluster value and the corresponding `liminf`/`limsup` bounds. -/
theorem cubeMoment_cluster_bounds_and_liminf_limsup
    {q M : ℕ → ℝ} {qLimit a b : ℝ}
    (hq : Tendsto q atTop (nhds qLimit))
    (hfinite : ∀ n, Real.exp (a * q n) ≤ M n ∧
      M n ≤ Real.exp (b * q n)) :
    (∀ x, IsCubeMomentClusterPoint M x →
      Real.exp (a * qLimit) ≤ x ∧ x ≤ Real.exp (b * qLimit)) ∧
    (∃ x, IsCubeMomentClusterPoint M x) ∧
    Real.exp (a * qLimit) ≤ Filter.liminf M atTop ∧
    Filter.limsup M atTop ≤ Real.exp (b * qLimit) := by
  have hupper : Tendsto (fun n => Real.exp (b * q n)) atTop
      (nhds (Real.exp (b * qLimit))) := exp_linear_tendsto (c := b) hq
  obtain ⟨B₀, hB₀⟩ := hupper.bddAbove_range
  let B := max 0 B₀
  have hmem : ∀ n : ℕ, M n ∈ Set.Icc 0 B := by
    intro n
    refine ⟨?_, ?_⟩
    · exact le_trans (Real.exp_pos _).le (hfinite n).1
    · exact le_trans (hfinite n).2
        (le_trans (hB₀ ⟨n, rfl⟩) (le_max_right 0 B₀))
  obtain ⟨x, _, s, hs, hMs⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) B) hmem
  have hsTop : Tendsto s atTop atTop := hs.tendsto_atTop
  have hxCluster : IsCubeMomentClusterPoint M x :=
    MapClusterPt.of_comp hsTop hMs.mapClusterPt
  have hcluster : ∀ y, IsCubeMomentClusterPoint M y →
      Real.exp (a * qLimit) ≤ y ∧ y ≤ Real.exp (b * qLimit) :=
    fun y hy => cubeMoment_cluster_bounds_of_squeeze hq hfinite y hy
  have hupperBounded : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) M := by
    apply Filter.isBoundedUnder_of
    exact ⟨B, fun n => (hmem n).2⟩
  have hlowerBounded : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) M := by
    apply Filter.isBoundedUnder_of
    exact ⟨0, fun n => (hmem n).1⟩
  have hliminfCluster : IsCubeMomentClusterPoint M (Filter.liminf M atTop) := by
    exact MapClusterPt.liminf (hc := hupperBounded.isCoboundedUnder_flip)
      (hb := hlowerBounded)
  have hlimsupCluster : IsCubeMomentClusterPoint M (Filter.limsup M atTop) := by
    exact MapClusterPt.limsup (hc := hlowerBounded.isCoboundedUnder_flip)
      (hb := hupperBounded)
  refine ⟨hcluster, ⟨x, hxCluster⟩, ?_, ?_⟩
  · exact (hcluster _ hliminfCluster).1
  · exact (hcluster _ hlimsupCluster).2


theorem cubeCovarianceTail_tendsto (N₀ : ℕ) (μ : GlobalLinkField)
    (hW : ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N) :
    Tendsto (cubeCovarianceTail N₀ μ hW) atTop
      (nhds (globalVariationalCovariance μ)) := by
  let E : ℕ → {N : ℕ // N₀ ≤ N} := fun n => ⟨N₀ + n, by omega⟩
  have hE : Tendsto E atTop atTop := by
    apply tendsto_atTop_atTop.2
    intro k
    refine ⟨k.1, ?_⟩
    intro n hn
    change k.1 ≤ N₀ + n
    omega
  have hgate := cubeCovariance_tendsto_fourierGreen μ N₀ hW
  have h := hgate.comp hE
  change Tendsto (fun n : ℕ => quotientCovarianceQuadratic
      (sourceLatticeComplex (B := cube (N₀ + n)))
      ⟨cubeLinkRestriction (N₀ + n) (μ : RealLatticeChain 4), hW _ (by omega)⟩)
    atTop (nhds (globalVariationalCovariance μ))
  convert h using 1
  funext n
  rfl

/--
Conditional scalar form of FS82 (2.93) along centered cubes.
-/
theorem cubeMoment_finite_to_infinite
    {N₁ : ℕ} {β β'' : ℝ}
    (N₀ : ℕ) (hN₁ : N₁ ≤ N₀)
    (μ : GlobalLinkField)
    (hW : ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N)
    (hroot : ∀ N, N₁ ≤ N → ∀ μN : cubeSourceW N, ∀ t : ℝ,
      Real.exp ((t ^ 2 * β'' / 2) *
        quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN) ≤
          FroehlichSpencer.FS82.Root.sourceDualMoment β μN t ∧
      FroehlichSpencer.FS82.Root.sourceDualMoment β μN t ≤
        Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN))
    (t : ℝ) :
    let M := cubeMomentTail N₀ β t μ hW
    (∀ x, IsCubeMomentClusterPoint M x →
      Real.exp ((t ^ 2 * β'' / 2) * globalVariationalCovariance μ) ≤ x ∧
      x ≤ Real.exp ((t ^ 2 * β / 2) * globalVariationalCovariance μ)) ∧
    (∃ x, IsCubeMomentClusterPoint M x) ∧
    Real.exp ((t ^ 2 * β'' / 2) * globalVariationalCovariance μ) ≤
      Filter.liminf M atTop ∧
    Filter.limsup M atTop ≤
      Real.exp ((t ^ 2 * β / 2) * globalVariationalCovariance μ) := by
  dsimp
  let M := cubeMomentTail N₀ β t μ hW
  let q := cubeCovarianceTail N₀ μ hW
  have hq : Tendsto q atTop (nhds (globalVariationalCovariance μ)) := by
    simpa [q] using cubeCovarianceTail_tendsto N₀ μ hW
  have hfinite : ∀ n, Real.exp ((t ^ 2 * β'' / 2) * q n) ≤ M n ∧
      M n ≤ Real.exp ((t ^ 2 * β / 2) * q n) := by
    intro n
    have hn : N₁ ≤ N₀ + n := le_trans hN₁ (by omega)
    let μN : cubeSourceW (N₀ + n) :=
      ⟨cubeLinkRestriction (N₀ + n) (μ : RealLatticeChain 4), hW _ (by omega)⟩
    have h := hroot (N₀ + n) hn μN t
    simpa [M, q, cubeMomentTail, cubeCovarianceTail, μN] using h
  simpa [M] using
    cubeMoment_cluster_bounds_and_liminf_limsup hq hfinite


/-- The eventual co-closedness gate supplies a supported cube tail for every
finitely supported globally co-closed test, so the conditional scalar result
applies without adding a support premise to the statement. -/
theorem exists_cubeMoment_finite_to_infinite
    {N₁ : ℕ} {β β'' : ℝ}
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (hroot : ∀ N, N₁ ≤ N → ∀ μN : cubeSourceW N, ∀ t : ℝ,
      Real.exp ((t ^ 2 * β'' / 2) *
        quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN) ≤
          FroehlichSpencer.FS82.Root.sourceDualMoment β μN t ∧
      FroehlichSpencer.FS82.Root.sourceDualMoment β μN t ≤
        Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN))
    (t : ℝ) :
    ∃ N₀, N₁ ≤ N₀ ∧
      ∃ hW : ∀ N ≥ N₀,
        cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N,
        (∀ x, IsCubeMomentClusterPoint (cubeMomentTail N₀ β t μ hW) x →
          Real.exp ((t ^ 2 * β'' / 2) * globalVariationalCovariance μ) ≤ x ∧
          x ≤ Real.exp ((t ^ 2 * β / 2) * globalVariationalCovariance μ)) ∧
        (∃ x, IsCubeMomentClusterPoint (cubeMomentTail N₀ β t μ hW) x) ∧
        Real.exp ((t ^ 2 * β'' / 2) * globalVariationalCovariance μ) ≤
          Filter.liminf (cubeMomentTail N₀ β t μ hW) atTop ∧
        Filter.limsup (cubeMomentTail N₀ β t μ hW) atTop ≤
          Real.exp ((t ^ 2 * β / 2) * globalVariationalCovariance μ) := by
  obtain ⟨NW, hWgate⟩ := eventually_cube_sourceW μ hμ
  let N₀ := max N₁ NW
  have hW : ∀ N ≥ N₀,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N := by
    intro N hN
    exact hWgate N (le_trans (le_max_right N₁ NW) hN)
  refine ⟨N₀, le_max_left _ _, hW, ?_⟩
  simpa [N₀] using cubeMoment_finite_to_infinite N₀ (le_max_left _ _)
    μ hW hroot t


end FroehlichSpencer.FS82.Infinite

end
