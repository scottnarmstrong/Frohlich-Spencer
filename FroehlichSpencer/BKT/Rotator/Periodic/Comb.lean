/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.DualCarrier
public import FroehlichSpencer.BKT.Rotator.TheoremC.BesselWeight
public import FroehlichSpencer.BKT.Rotator.PinnedDensityCombLimit
public import FroehlichSpencer.BKT.Rotator.PinnedDensityPoissonLimit
public import FroehlichSpencer.BKT.Rotator.TheoremC.PinnedAdapter

/-!
# Root-pinned Fourier combs on periodic square carriers

The cutoff used by the rooted KP estimate includes the root coordinate. Its neutral modes are
cofinal with the ordinary frequency boxes on the root-pinned coordinate space. This file starts
the periodic Poisson bridge in those coordinates.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap Real
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.BesselInterp
open FroehlichSpencer.BKT.Rotator

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ}

/-- The chosen root in the coordinate presentation of the periodic square. -/
def periodicRootSite (hL : 1 < L) : Site L :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

/-- The periodic square vertices other than the chosen root. -/
abbrev RootedVertex (L : ℕ) (hL : 1 < L) := {v : Site L // v ≠ periodicRootSite hL}

/-- Extend a root-pinned real coordinate field by zero at the root. -/
def rootField (hL : 1 < L) (x : RootedVertex L hL → ℝ) : Site L → ℝ := fun v =>
  if h : v = periodicRootSite hL then 0 else x ⟨v, h⟩

/-- The root-pinned gradient as a linear map into square-periodic edge fields. -/
def rootGradientLinearMap (hL : 1 < L) :
    (RootedVertex L hL → ℝ) →ₗ[ℝ] (Bond L → ℝ) where
  toFun x := (graph L).grad (rootField hL x)
  map_add' x y := by
    funext e
    have hfield (v : Site L) : rootField hL (x + y) v = rootField hL x v + rootField hL y v := by
      by_cases h : v = periodicRootSite hL <;> simp [rootField, h]
    simp only [Multigraph.grad, hfield, Pi.add_apply]
    ring
  map_smul' c x := by
    funext e
    have hfield (v : Site L) : rootField hL (c • x) v = c * rootField hL x v := by
      by_cases h : v = periodicRootSite hL <;> simp [rootField, h]
    simp only [Multigraph.grad, hfield, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- A zero root-pinned gradient determines its field. -/
theorem rootGradientLinearMap_injective (hL : 1 < L) :
    Function.Injective (rootGradientLinearMap (L := L) hL) := by
  intro x y hxy
  let G := graph L
  let z := x - y
  let φ := rootField hL z
  have hzero : rootGradientLinearMap hL z = 0 := by
    calc
      rootGradientLinearMap hL z = rootGradientLinearMap hL x - rootGradientLinearMap hL y :=
        (rootGradientLinearMap hL).map_sub x y
      _ = 0 := by rw [hxy]; simp
  have hgrad (e : Bond L) : G.grad φ e = 0 := by
    have h := congrFun hzero e
    simpa [G, φ, z, rootGradientLinearMap, Multigraph.grad] using h
  have henergy : G.energy φ = 0 := by
    unfold Multigraph.energy
    apply Finset.sum_eq_zero
    intro e he
    rw [hgrad e]
    simp
  obtain ⟨c, hc⟩ := (G.energy_eq_zero_iff_exists_const
    (squarePeriodic_connected L hL) φ).mp henergy
  have hcroot : c = 0 := by
    have h := congrFun hc (periodicRootSite hL)
    simpa [φ, rootField] using h.symm
  apply funext
  intro v
  have hvne : v.1 ≠ periodicRootSite hL := v.2
  have h := congrFun hc v.1
  have hz : z v = c := by simpa [φ, rootField, hvne] using h
  have hxyv : x v - y v = 0 := by simpa [z, hcroot] using hz
  exact sub_eq_zero.mp hxyv

/-- The interpolated Bessel density on root-pinned periodic real coordinates, with an arbitrary
real edge offset in the angle variable. -/
def periodicDensityCoords {hL : 1 < L} (β : ℝ) (r : Bond L → ℝ)
    (x : RootedVertex L hL → ℝ) : ℂ :=
  ∏ e : Bond L, besselInterp β
    (((((graph L).grad (rootField hL x) e + r e / (2 * Real.pi)) : ℝ) : ℂ))

/-- The periodic offset density is Schwartz in the root-pinned coordinates. -/
theorem exists_periodicDensityCoords_schwartz {hL : 1 < L} {β : ℝ} (hβ : 1 ≤ β)
    (r : Bond L → ℝ) :
    ∃ f : 𝓢(RootedVertex L hL → ℝ, ℂ), ∀ x, f x = periodicDensityCoords β r x := by
  classical
  let bessel : 𝓢(ℝ, ℂ) := besselInterpRealSchwartz β hβ
  obtain ⟨edgeProduct, hedgeProduct⟩ := exists_schwartz_pi_product (ι := Bond L) bessel
  let r' : Bond L → ℝ := fun e => r e / (2 * Real.pi)
  let shifted : 𝓢(Bond L → ℝ, ℂ) :=
    SchwartzMap.compSubConstCLM ℂ (-r') edgeProduct
  let grad : (RootedVertex L hL → ℝ) →L[ℝ] (Bond L → ℝ) :=
    (rootGradientLinearMap hL).toContinuousLinearMap
  obtain ⟨K, -, hanti⟩ :=
    (rootGradientLinearMap hL).injective_iff_antilipschitz.mp
      (rootGradientLinearMap_injective hL)
  have hanti' : AntilipschitzWith K grad := by
    change AntilipschitzWith K (rootGradientLinearMap hL)
    exact hanti
  let f : 𝓢(RootedVertex L hL → ℝ, ℂ) :=
    (SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti') shifted
  refine ⟨f, fun x => ?_⟩
  have hcomp : f x = shifted (grad x) := by
    change ((SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti') shifted) x = _
    simp only [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]
  have hshift : shifted (grad x) = edgeProduct (grad x + r') := by
    calc
      shifted (grad x) = edgeProduct (grad x - -r') :=
        SchwartzMap.compSubConstCLM_apply edgeProduct (-r') (grad x)
      _ = edgeProduct (grad x + r') := by
        congr 1
        funext e
        simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
        ring
  rw [hcomp, hshift, hedgeProduct]
  unfold periodicDensityCoords
  refine Finset.prod_congr rfl fun e _ => ?_
  rfl

/-- The root-pinned periodic density is integrable. -/
theorem integrable_periodicDensityCoords {hL : 1 < L} {β : ℝ} (hβ : 1 ≤ β)
    (r : Bond L → ℝ) : Integrable (periodicDensityCoords (L := L) (hL := hL) β r) := by
  classical
  obtain ⟨f, hf⟩ := exists_periodicDensityCoords_schwartz (hL := hL) hβ r
  refine (integrable_schwartz_pi f).congr ?_
  filter_upwards [] with x
  exact hf x

/-- The root-pinned periodic Fourier coefficients are absolutely summable. -/
theorem summable_periodicDensityCoords_fourier {hL : 1 < L} {β : ℝ} (hβ : 1 ≤ β)
    (r : Bond L → ℝ) :
    Summable (faceFourierCoefficient (periodicDensityCoords (L := L) (hL := hL) β r)) := by
  classical
  obtain ⟨f, hf⟩ := exists_periodicDensityCoords_schwartz (hL := hL) hβ r
  have hs := summable_faceFourierCoefficient_of_schwartz f
  refine hs.congr fun q => ?_
  unfold faceFourierCoefficient
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hf]

/-! ## The root mode and the periodic comb cutoff

The periodic rooted integral uses a comb at every torus vertex. Integrating the root phase forces
the full frequency vector to be neutral. After eliminating the root frequency, the resulting
rootless cutoff consists of frequencies `q` with both `|qᵢ| ≤ N` and `|∑ qᵢ| ≤ N`. These finite
sets exhaust the entire root-pinned frequency lattice.
-/

/-- The total charge of a rootless frequency vector. -/
def periodicFrequencyTotal {ι : Type*} [Fintype ι] (q : FaceFrequency ι) : ℤ :=
  ∑ i : ι, q i (Finset.mem_univ i)

/-- The root-neutral frequency set: the ordinary coordinate box together with the cutoff on the
eliminated root frequency. -/
def periodicNeutralFrequencyBox {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) :
    Finset (FaceFrequency ι) :=
  (faceFrequencyBox N).filter fun q =>
    periodicFrequencyTotal q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- A finite subset of the rootless frequency lattice is eventually contained in the periodic
neutral cutoffs. -/
theorem periodicNeutralFrequencyBox_tendsto_atTop {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    Tendsto (periodicNeutralFrequencyBox (ι := ι)) atTop
      (atTop : Filter (Finset (FaceFrequency ι))) := by
  classical
  apply tendsto_atTop.2
  intro s
  let coordBound : FaceFrequency ι → ℕ := fun q =>
    Finset.univ.sup fun i => (q i (Finset.mem_univ i)).natAbs
  let totalBound : FaceFrequency ι → ℕ := fun q => (periodicFrequencyTotal q).natAbs
  let B := max (s.sup coordBound) (s.sup totalBound)
  have hsubset : s ⊆ periodicNeutralFrequencyBox (ι := ι) B := by
    intro q hq
    apply Finset.mem_filter.mpr
    constructor
    · rw [faceFrequencyBox, Finset.mem_pi]
      intro i hi
      rw [Finset.mem_Icc]
      have hcoord : coordBound q ≤ s.sup coordBound := Finset.le_sup hq
      have hi' : (q i (Finset.mem_univ i)).natAbs ≤ coordBound q :=
        Finset.le_sup (s := Finset.univ) (f := fun i =>
          (q i (Finset.mem_univ i)).natAbs) (Finset.mem_univ i)
      have hnat : (q i (Finset.mem_univ i)).natAbs ≤ B :=
        (hi'.trans hcoord).trans (Nat.le_max_left _ _)
      have hnatZ : ((q i (Finset.mem_univ i)).natAbs : ℤ) ≤ B := by exact_mod_cast hnat
      have hneg : -(q i (Finset.mem_univ i)) ≤
          (q i (Finset.mem_univ i)).natAbs := by
        simpa [Int.natAbs_neg] using
          (Int.le_natAbs (a := -(q i (Finset.mem_univ i))))
      constructor <;> omega
    · have htotal : totalBound q ≤ s.sup totalBound := Finset.le_sup hq
      have hnat : (periodicFrequencyTotal q).natAbs ≤ B :=
        htotal.trans (Nat.le_max_right _ _)
      have hnatZ : ((periodicFrequencyTotal q).natAbs : ℤ) ≤ B := by exact_mod_cast hnat
      have hneg : -(periodicFrequencyTotal q) ≤
          (periodicFrequencyTotal q).natAbs := by
        simpa [Int.natAbs_neg] using
          (Int.le_natAbs (a := -(periodicFrequencyTotal q)))
      rw [Finset.mem_Icc]
      constructor <;> omega
  filter_upwards [eventually_ge_atTop B] with N hBN
  intro q hq
  have hqB := hsubset hq
  rw [periodicNeutralFrequencyBox, Finset.mem_filter] at hqB
  apply Finset.mem_filter.mpr
  constructor
  · rw [faceFrequencyBox, Finset.mem_pi] at hqB ⊢
    intro i hi
    have hiB := hqB.1 i (Finset.mem_univ i)
    rw [Finset.mem_Icc] at hiB ⊢
    constructor <;> omega
  · have hsumB := hqB.2
    rw [Finset.mem_Icc] at hsumB ⊢
    constructor <;> omega

/-- The finite root-neutral comb on the pinned coordinates. -/
def periodicNeutralCombCutoff {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (x : ι → ℝ) : ℂ :=
  ∑ q ∈ periodicNeutralFrequencyBox (ι := ι) N, faceCombMode q x

/-- Pairing the root-neutral comb with an integrable density is its finite Fourier-coefficient
sum. -/
theorem integral_periodicNeutralCombCutoff_mul_eq_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℂ} (hf : Integrable f) (N : ℕ) :
    (∫ x : ι → ℝ, periodicNeutralCombCutoff (ι := ι) N x * f x) =
      ∑ q ∈ periodicNeutralFrequencyBox (ι := ι) N, faceFourierCoefficient f q := by
  classical
  let s := periodicNeutralFrequencyBox (ι := ι) N
  calc
    _ = ∫ x : ι → ℝ, ∑ q ∈ s, faceCombMode q x * f x := by
      congr 1
      funext x
      simp [periodicNeutralCombCutoff, s, Finset.sum_mul]
    _ = ∑ q ∈ s, ∫ x : ι → ℝ, faceCombMode q x * f x := by
      rw [integral_finsetSum (s := s) (f := fun q x => faceCombMode q x * f x)
        (by
          intro q hq
          have hmode : Continuous fun x : ι → ℝ => faceCombMode q x := by
            fun_prop [faceCombMode]
          have hmodeNorm : ∀ x, ‖faceCombMode q x‖ = 1 := by
            intro x
            unfold faceCombMode
            rw [Complex.norm_exp]
            have hre :
                (((( -2 * Real.pi * ∑ i : ι,
                    x i * (q i (Finset.mem_univ i) : ℝ) : ℝ) : ℂ) * Complex.I).re) = 0 := by
              simp [Complex.mul_re]
            rw [hre]
            simp
          refine hf.norm.mono' (hmode.aestronglyMeasurable.mul hf.1) ?_
          filter_upwards [] with x
          rw [norm_mul, hmodeNorm, one_mul])]
    _ = ∑ q ∈ s, faceFourierCoefficient f q := rfl

/-- The root-neutral finite comb pairings converge to the complete Fourier series whenever the
coefficient family is summable. -/
theorem periodicNeutralCombCutoffPairing_tendsto_fourier {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : Integrable f) (hcoeff : Summable (faceFourierCoefficient f)) :
    Tendsto (fun N : ℕ =>
      ∫ x : ι → ℝ, periodicNeutralCombCutoff (ι := ι) N x * f x) atTop
      (𝓝 (∑' q, faceFourierCoefficient f q)) := by
  have hsum : Tendsto (fun N : ℕ =>
      ∑ q ∈ periodicNeutralFrequencyBox (ι := ι) N, faceFourierCoefficient f q) atTop
      (𝓝 (∑' q, faceFourierCoefficient f q)) := by
    have hs := hcoeff.hasSum
    change Tendsto (fun s : Finset (FaceFrequency ι) =>
      ∑ q ∈ s, faceFourierCoefficient f q) atTop
      (𝓝 (∑' q, faceFourierCoefficient f q)) at hs
    exact hs.comp (periodicNeutralFrequencyBox_tendsto_atTop (ι := ι))
  exact hsum.congr' (Filter.Eventually.of_forall fun N =>
    (integral_periodicNeutralCombCutoff_mul_eq_sum hf N).symm)

/-- Poisson summation identifies the complete periodic rootless Fourier series with the density
sampled at pinned integer heights. -/
theorem periodicDensityCoords_fourierSum_eq_pinnedLatticeSum {hL : 1 < L} {β : ℝ}
    (hβ : 1 ≤ β) (r : Bond L → ℝ) :
    (∑' q : FaceFrequency (RootedVertex L hL),
      faceFourierCoefficient (periodicDensityCoords (L := L) (hL := hL) β r) q) =
      ∑' z : RootedVertex L hL → ℤ,
        periodicDensityCoords β r (fun v => (z v : ℝ)) := by
  classical
  let ι := RootedVertex L hL
  obtain ⟨f, hf⟩ := exists_periodicDensityCoords_schwartz (hL := hL) hβ r
  have hcoeff (q : FaceFrequency ι) :
      faceFourierCoefficient (periodicDensityCoords (L := L) (hL := hL) β r) q =
        multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) := by
    rw [faceFourierCoefficient_eq_multiEuclideanFourierCoefficient
      (periodicDensityCoords (L := L) (hL := hL) β r) q]
    rw [show faceFrequencyEquiv ι q = (fun i => q i (Finset.mem_univ i)) by rfl]
    unfold multiEuclideanFourierCoefficient
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hf]
  have hcoeffSum :
      (∑' q : FaceFrequency ι,
        faceFourierCoefficient (periodicDensityCoords (L := L) (hL := hL) β r) q) =
        ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q := by
    calc
      _ = ∑' q : FaceFrequency ι,
            multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) := by
          apply tsum_congr
          exact hcoeff
      _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q :=
        (faceFrequencyEquiv ι).tsum_eq (multiEuclideanFourierCoefficient f)
  have hpoisson := poissonSummation_schwartz_pi_unconditional f
  calc
    _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q := hcoeffSum
    _ = ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := hpoisson
    _ = ∑' z : ι → ℤ, periodicDensityCoords β r (fun i => (z i : ℝ)) := by
      apply tsum_congr
      intro z
      exact hf (fun i => (z i : ℝ))

/-- The root-neutral cutoff pairings of a periodic offset density converge to its complete pinned
integer-height sum. -/
theorem periodicNeutralCombCutoffPairing_tendsto_pinnedLatticeSum {hL : 1 < L}
    {β : ℝ} (hβ : 1 ≤ β) (r : Bond L → ℝ) :
    Tendsto (fun N : ℕ =>
      ∫ x : RootedVertex L hL → ℝ,
        periodicNeutralCombCutoff N x * periodicDensityCoords β r x) atTop
      (𝓝 (∑' z : RootedVertex L hL → ℤ,
        periodicDensityCoords β r (fun v => (z v : ℝ)))) := by
  rw [← periodicDensityCoords_fourierSum_eq_pinnedLatticeSum hβ r]
  exact periodicNeutralCombCutoffPairing_tendsto_fourier
    (integrable_periodicDensityCoords hβ r)
    (summable_periodicDensityCoords_fourier hβ r)

end FroehlichSpencer.BKT.Rotator.Periodic

end
