/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Norm
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Surface.GreenFunctionSpec
public import FroehlichSpencer.Surface.LatticeLength
public import FroehlichSpencer.Surface.FiniteGreen
public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Infra.Green.EventRegularity
import FroehlichSpencer.Surface.T12Lambda
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.green_probability_bound`

This module contains `FroehlichSpencer.Provider.green_probability_bound`, the proof of the
statement `FroehlichSpencer.green_probability_bound` (file `FroehlichSpencer/Surface/T12.lean`, FS83
Theorem 1.2, (1.22)).

Proof: FS83 (1.28)–(1.29), Fröhlich–Spencer (1983) lines 327–347.

The infinite-volume
Green column is the limit of finite-volume Green entries along a cube exhaustion (resolvent
convergence for the unique `ℓ²` solution, used through `greenFunction_spec`), so the all-`ε`
infinite-volume event contains the `limsup` of the finite-volume events; the uniform-in-`Λ` lower
bound of the T1.2_Λ (`FroehlichSpencer.finiteVolumeGreen_probability_bound`) passes to the
limit.
-/

public section

open MeasureTheory Filter Set Complex Topology

namespace FroehlichSpencer

private theorem memℓp_two_iff_summable (ν : ℕ) (ψ : Site ν → ℂ) :
    Memℓp ψ 2 ↔ Summable (fun x => ‖ψ x‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

private theorem green_kernel_column_data (ν : ℕ) (hν : 0 < ν) (z : ℂ) (hz : z.im ≠ 0)
    (v : Site ν → ℝ) (y : Site ν) :
    Memℓp (fun x => greenFunction ν hν z hz v x y) 2 ∧
      ∀ t, ∑' w, hoppingKernel ν t w * greenFunction ν hν z hz v w y +
        (((v t + 2 * (ν : ℝ) : ℝ) : ℂ) - z) * greenFunction ν hν z hz v t y =
          (Pi.single y 1 : Site ν → ℂ) t := by
  let ψ : Site ν → ℂ := fun x => greenFunction ν hν z hz v x y
  have hsolution' :
      Summable (fun x => ‖ψ x‖ ^ 2) ∧
        ∀ t, -(latticeLaplacian ν ψ t) + ((v t : ℂ) - z) * ψ t =
          if t = y then 1 else 0 :=
    (greenFunction_spec ν hν z hz v y ψ).mpr rfl
  constructor
  · exact (memℓp_two_iff_summable ν ψ).2 hsolution'.1
  · intro t
    have hkernel : ∑' w, hoppingKernel ν t w * ψ w =
        -(latticeLaplacian ν ψ t) - 2 * (ν : ℂ) * ψ t :=
      tsum_hoppingKernel_mul ν ψ t
    calc
      ∑' w, hoppingKernel ν t w * greenFunction ν hν z hz v w y +
          (((v t + 2 * (ν : ℝ) : ℝ) : ℂ) - z) * greenFunction ν hν z hz v t y
        = -(latticeLaplacian ν ψ t) + ((v t : ℂ) - z) * ψ t := by
            rw [hkernel]
            push_cast
            ring
      _ = if t = y then 1 else 0 := hsolution'.2 t
      _ = (Pi.single y 1 : Site ν → ℂ) t := by simp [Pi.single_apply]

private theorem finiteGreen_eq_resolventColumn (ν : ℕ) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0) (x y : Site ν)
    (hx : x ∈ Λ) (hy : y ∈ Λ) :
    finiteGreen ν Λ v E ε hε ⟨x, hx⟩ ⟨y, hy⟩ =
      Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) Λ
        ((E : ℂ) + (ε : ℂ) * I) y x := by
  unfold finiteGreen
  rw [hamiltonian_eq_restrictedOp]
  exact (Infra.resolventColumn_of_mem (hoppingKernel ν)
    (fun w => v w + 2 * (ν : ℝ)) ((E : ℂ) + (ε : ℂ) * I) hx hy).symm

private theorem exists_exhaustive_sequence (ν : ℕ) (x : Site ν) :
    ∃ Λ : ℕ → Finset (Site ν),
      (∀ n, (0 : Site ν) ∈ Λ n ∧ x ∈ Λ n) ∧
        ∀ y, ∀ᶠ n in atTop, y ∈ Λ n := by
  classical
  obtain ⟨f, hf⟩ := exists_surjective_nat (Site ν)
  refine ⟨fun n => (Finset.range n).image f ∪ {0, x}, ?_, ?_⟩
  · intro n
    simp
  · intro y
    obtain ⟨m, rfl⟩ := hf y
    filter_upwards [eventually_gt_atTop m] with n hn
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨m, Finset.mem_range.mpr hn, rfl⟩)

private theorem tendsto_finiteGreen (ν : ℕ) (hν : 0 < ν) (v : Site ν → ℝ)
    (E ε : ℝ) (hε : ε ≠ 0) (x : Site ν) (Λ : ℕ → Finset (Site ν))
    (h0 : ∀ n, (0 : Site ν) ∈ Λ n) (hx : ∀ n, x ∈ Λ n)
    (hΛ : ∀ y, ∀ᶠ n in atTop, y ∈ Λ n) :
    Tendsto (fun n => finiteGreen ν (Λ n) v E ε hε ⟨0, h0 n⟩ ⟨x, hx n⟩)
      atTop (𝓝 (greenFunction ν hν ((E : ℂ) + (ε : ℂ) * I)
        (by simpa using hε) v 0 x)) := by
  let z : ℂ := (E : ℂ) + (ε : ℂ) * I
  have hz : z.im ≠ 0 := by simpa [z] using hε
  have hdata := green_kernel_column_data ν hν z hz v x
  have hconv := Infra.tendsto_resolventColumn_of_eventually_mem
    (a := hoppingKernel ν) (K := 2 * (ν : ℝ)) (hoppingKernel_symm ν)
    (hoppingKernel_finite ν) (sum_norm_hoppingKernel_le ν)
    (fun y => v y + 2 * (ν : ℝ)) hz hΛ (y := x)
    (ψ := fun y => greenFunction ν hν z hz v y x) hdata.1 hdata.2
  have hseq :
      (fun n => finiteGreen ν (Λ n) v E ε hε ⟨0, h0 n⟩ ⟨x, hx n⟩) =
        fun n => Infra.resolventColumn (hoppingKernel ν)
          (fun y => v y + 2 * (ν : ℝ)) (Λ n) z x 0 := by
    funext n
    exact finiteGreen_eq_resolventColumn ν (Λ n) v E ε hε 0 x (h0 n) (hx n)
  rw [hseq]
  simpa [z] using hconv.2 0

private def finiteGreenBoundEvent (ν : ℕ) (Λ : Finset (Site ν)) (E : ℝ)
    (x : Site ν) (c : ℝ) (h0 : (0 : Site ν) ∈ Λ) (hx : x ∈ Λ) :
    Set (Site ν → ℝ) :=
  {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
    ‖finiteGreen ν Λ v E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤
      c}

private def greenBoundEvent (ν : ℕ) (hν : 0 < ν) (E : ℝ) (x : Site ν)
    (c : ℝ) : Set (Site ν → ℝ) :=
  {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
    ‖greenFunction ν hν ((E : ℂ) + (ε : ℂ) * I) (by simpa using hε) v 0 x‖ ≤
      c}

private theorem finite_limsup_subset_infinite (ν : ℕ) (hν : 0 < ν) (E : ℝ)
    (x : Site ν) (c : ℝ) (Λ : ℕ → Finset (Site ν))
    (h0 : ∀ n, (0 : Site ν) ∈ Λ n) (hx : ∀ n, x ∈ Λ n)
    (hΛ : ∀ y, ∀ᶠ n in atTop, y ∈ Λ n) :
    (⋂ n, ⋃ k : {k : ℕ // n ≤ k},
      finiteGreenBoundEvent ν (Λ k) E x c (h0 k) (hx k)) ⊆
      greenBoundEvent ν hν E x c := by
  intro v hv
  change ∀ ε : ℝ, ∀ hε : ε ≠ 0, _
  intro ε hε
  have hconv := tendsto_finiteGreen ν hν v E ε hε x Λ h0 hx hΛ
  have hnorm : Tendsto
      (fun n => ‖finiteGreen ν (Λ n) v E ε hε ⟨0, h0 n⟩ ⟨x, hx n⟩‖)
      atTop (𝓝 ‖greenFunction ν hν ((E : ℂ) + (ε : ℂ) * I)
        (by simpa using hε) v 0 x‖) :=
    (continuous_norm.tendsto _).comp hconv
  by_contra hnot
  have hlt : c < ‖greenFunction ν hν ((E : ℂ) + (ε : ℂ) * I)
        (by simpa using hε) v 0 x‖ := lt_of_not_ge hnot
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hnorm.eventually (Ioi_mem_nhds hlt))
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (Set.mem_iInter.1 hv n₀)
  have hgood :
      ‖finiteGreen ν (Λ k) v E ε hε ⟨0, h0 k⟩ ⟨x, hx k⟩‖ ≤
        c := by
    change v ∈ finiteGreenBoundEvent ν (Λ k) E x c (h0 k) (hx k) at hk
    exact hk ε hε
  exact (not_lt_of_ge hgood) (hn₀ k k.2)

private theorem measurable_greenBoundEvent (ν : ℕ) (hν : 0 < ν) (E : ℝ)
    (x : Site ν) (c : ℝ) : MeasurableSet (greenBoundEvent ν hν E x c) := by
  let shift : (Site ν → ℝ) → Site ν → ℝ := fun v y => v y + 2 * (ν : ℝ)
  let Ψ : (Site ν → ℝ) → ℂ → Site ν → ℂ := fun u z t =>
    if hz : z.im ≠ 0 then greenFunction ν hν z hz (fun y => u y - 2 * (ν : ℝ)) t x else 0
  have hΨ : ∀ v z, z.im ≠ 0 → Memℓp (Ψ v z) 2 ∧
      ∀ t, ∑' w, hoppingKernel ν t w * Ψ v z w +
        ((v t : ℂ) - z) * Ψ v z t =
          (Pi.single x 1 : Site ν → ℂ) t := by
    intro v z hz
    have hdata := green_kernel_column_data ν hν z hz (fun y => v y - 2 * (ν : ℝ)) x
    have hcol : Ψ v z = fun t =>
        greenFunction ν hν z hz (fun y => v y - 2 * (ν : ℝ)) t x := by
      funext t
      simp [Ψ, hz]
    rw [hcol]
    constructor
    · exact hdata.1
    · intro t
      simpa using hdata.2 t
  let U : Set (Site ν → ℝ) := {u | ∀ ε : ℝ, ε ≠ 0 →
    ‖Ψ u ((E : ℂ) + (ε : ℝ) * I) 0‖ ≤ c}
  have hregular : MeasurableSet U := by
    change MeasurableSet {u | ∀ ε : ℝ, ε ≠ 0 →
      ‖Ψ u ((E : ℂ) + (ε : ℝ) * I) 0‖ ≤ c}
    exact (Infra.measurableSet_setOf_forall_norm_le_of_forall_eq_single
      (a := hoppingKernel ν) (K := 2 * (ν : ℝ)) (hoppingKernel_symm ν)
      (hoppingKernel_finite ν) (sum_norm_hoppingKernel_le ν) E x 0 c (Ψ := Ψ) hΨ)
  have hshift : Measurable shift := by
    apply Measurable.of_eval
    intro y
    exact (measurable_pi_apply y).add measurable_const
  have heq : greenBoundEvent ν hν E x c = shift ⁻¹' U := by
    ext v
    constructor
    · intro h ε hε
      simpa [U, Ψ, shift, add_sub_cancel_right, hε] using h ε hε
    · intro h ε hε
      change shift v ∈ U at h
      simpa [U, Ψ, shift, add_sub_cancel_right, hε] using h ε hε
  rw [heq]
  exact hregular.preimage hshift

private theorem measure_lower_bound_of_finite_limsup
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (hμ : IsProbabilityMeasure μ)
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) (q : ENNReal)
    (hq : ∀ n, q ≤ μ (A n)) (B : Set α)
    (hsub : (⋂ n, ⋃ k : {k : ℕ // n ≤ k}, A k) ⊆ B) : q ≤ μ B := by
  let T : ℕ → Set α := fun n => ⋃ k : {k : ℕ // n ≤ k}, A k
  have hTmeas : ∀ n, MeasurableSet (T n) := by
    intro n
    exact MeasurableSet.iUnion fun k => hA k
  have hTanti : Antitone T := by
    intro n m hnm a ha
    rcases mem_iUnion.1 ha with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨⟨k, le_trans hnm k.2⟩, hk⟩
  have hTbound : ∀ n, q ≤ μ (T n) := by
    intro n
    apply le_trans (hq n)
    apply measure_mono
    intro a ha
    exact mem_iUnion.2 ⟨⟨n, le_rfl⟩, ha⟩
  have hμfinite : μ univ ≠ ⊤ := by rw [hμ.measure_univ]; simp
  have hfinite : ∃ n, μ (T n) ≠ ⊤ := by
    refine ⟨0, ne_top_of_le_ne_top hμfinite ?_⟩
    exact measure_mono (subset_univ (T 0))
  have hlim : Tendsto (fun n => μ (T n)) atTop (𝓝 (μ (⋂ n, T n))) :=
    tendsto_measure_iInter_atTop (fun n => (hTmeas n).nullMeasurableSet) hTanti hfinite
  have hqInter : q ≤ μ (⋂ n, T n) :=
    ge_of_tendsto hlim (Eventually.of_forall hTbound)
  exact hqInter.trans (measure_mono hsub)

/--
Conditional FS83 (1.28)–(1.29) reduction: the finite-volume probability estimate implies the
infinite-volume estimate.
-/
theorem green_probability_bound_of_finiteVolumeGreen_probability_bound
    (ν : ℕ) (hν : 0 < ν)
    (hfinite :
      ∃ (largeDisorder : ℝ → ℝ → ℝ)
        (highEnergy : ℝ → ℝ → ℝ → ℝ)
        (Kp : ℝ → ℝ)
        (Kgauss : ℝ → ℝ → ℝ → ℝ),
        (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
        (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
        (∀ p, 0 < p → 0 ≤ Kp p) ∧
        (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
        ∀ (m p : ℝ), 0 < m → 0 < p →
          ∀ (law : Measure ℝ), [IsProbabilityMeasure law] →
          ∀ (E : ℝ) (Λ : Finset (Site ν)) (x : Site ν),
            (h0 : (0 : Site ν) ∈ Λ) → (hx : x ∈ Λ) →
          ∀ (N : ℝ), 0 < N →
            let S : Set (Configuration ν) :=
              {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖finiteGreen ν Λ v E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤
                  Real.exp (m * (N - latticeLength ν x))}
            ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤ configurationMeasure ν law S) ∧
              (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
                highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                    configurationMeasure ν law S)) :
    ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [IsProbabilityMeasure law] →
        ∀ (E : ℝ) (x : Site ν),
          ∀ (N : ℝ), 0 < N →
            let S : Set (Configuration ν) :=
              {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖greenFunction ν hν
                    ((E : ℂ) + (ε : ℂ) * I) (by simpa using hε)
                    v (0 : Site ν) x‖ ≤
                  Real.exp (m * (N - latticeLength ν x))}
            ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤
                    configurationMeasure ν law S) ∧
              (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
                highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                    configurationMeasure ν law S) := by
  rcases hfinite with ⟨largeDisorder, highEnergy, Kp, Kgauss,
    hLargeDisorder, hHighEnergy, hKp, hKgauss, hfiniteBound⟩
  refine ⟨largeDisorder, highEnergy, Kp, Kgauss,
    hLargeDisorder, hHighEnergy, hKp, hKgauss, ?_⟩
  intro m p hm hp law inst E x N hN
  have hconfigProb : IsProbabilityMeasure (configurationMeasure ν law) := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : Site ν => law))
    infer_instance
  let c : ℝ := Real.exp (m * (N - latticeLength ν x))
  let Sinf : Set (Configuration ν) := greenBoundEvent ν hν E x c
  obtain ⟨Λ, hsites, hΛ⟩ := exists_exhaustive_sequence ν x
  have h0 : ∀ n, (0 : Site ν) ∈ Λ n := fun n => (hsites n).1
  have hx : ∀ n, x ∈ Λ n := fun n => (hsites n).2
  have hfiniteAt (n : ℕ) := hfiniteBound m p hm hp law E (Λ n) x (h0 n) (hx n) N hN
  have hmeas : MeasurableSet Sinf := by
    exact measurable_greenBoundEvent ν hν E x c
  constructor
  · intro hdensity
    constructor
    · exact hmeas
    · have hfiniteMeas : ∀ n,
          MeasurableSet (finiteGreenBoundEvent ν (Λ n) E x c (h0 n) (hx n)) := by
        intro n
        have h := (hfiniteAt n).1 hdensity
        exact h.1
      have hfiniteProb : ∀ n,
          ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤
            configurationMeasure ν law
              (finiteGreenBoundEvent ν (Λ n) E x c (h0 n) (hx n)) := by
        intro n
        have h := (hfiniteAt n).1 hdensity
        exact h.2
      have hsubset := finite_limsup_subset_infinite ν hν E x c Λ h0 hx hΛ
      have hprob := measure_lower_bound_of_finite_limsup
        (configurationMeasure ν law) hconfigProb
        (fun n => finiteGreenBoundEvent ν (Λ n) E x c (h0 n) (hx n))
        hfiniteMeas (ENNReal.ofReal (1 - Kp p / Real.rpow N p)) hfiniteProb Sinf hsubset
      simpa [Sinf, greenBoundEvent, c] using hprob
  · intro γ hγ hlaw hEnergy
    constructor
    · exact hmeas
    · have hfiniteMeas : ∀ n,
          MeasurableSet (finiteGreenBoundEvent ν (Λ n) E x c (h0 n) (hx n)) := by
        intro n
        have h := (hfiniteAt n).2 γ hγ hlaw hEnergy
        exact h.1
      have hfiniteProb : ∀ n,
          ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
            configurationMeasure ν law
              (finiteGreenBoundEvent ν (Λ n) E x c (h0 n) (hx n)) := by
        intro n
        have h := (hfiniteAt n).2 γ hγ hlaw hEnergy
        exact h.2
      have hsubset := finite_limsup_subset_infinite ν hν E x c Λ h0 hx hΛ
      have hprob := measure_lower_bound_of_finite_limsup
        (configurationMeasure ν law) hconfigProb
        (fun n => finiteGreenBoundEvent ν (Λ n) E x c (h0 n) (hx n))
        hfiniteMeas (ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p)) hfiniteProb
        Sinf hsubset
      simpa [Sinf, greenBoundEvent, c] using hprob

end FroehlichSpencer

namespace FroehlichSpencer.Provider

/--
FS83 Theorem 1.2 (provider): the statement of `FroehlichSpencer.green_probability_bound`,
proved from the T1.2_Λ by the (1.28)–(1.29) reduction.
-/
theorem green_probability_bound (ν : ℕ) (hν : 0 < ν) :
    ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ) (x : Site ν),
          ∀ (N : ℝ), 0 < N →
            let S : Set (Configuration ν) :=
              {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖greenFunction ν hν
                    ((E : ℂ) + (ε : ℂ) * Complex.I) (by simpa using hε)
                    v (0 : Site ν) x‖ ≤
                  Real.exp (m * (N - latticeLength ν x))}
            ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤
                    configurationMeasure ν law S) ∧
              (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
                highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                    configurationMeasure ν law S) :=
  green_probability_bound_of_finiteVolumeGreen_probability_bound ν hν
    (finiteVolumeGreen_probability_bound ν hν)

end FroehlichSpencer.Provider

end
