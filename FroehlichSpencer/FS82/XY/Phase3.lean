/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Endpoint3
public import FroehlichSpencer.FS82.XY.Filling3

/-!
# the residual field and the phase representatives

Let `φ` be the endpoint path as an integer field on the dual plaquettes and `τ = (δd)⁻¹ δφ` its
projected potential.

For a co-closed integer current `J` with an integer
filling `F`, `δF = J`,

`2π ⟨J, τ⟩ = 2π ⟨F, dτ⟩ = 2π ⟨F, φ⟩ − 2π ⟨F, ε⟩ ∈ 2πℤ − 2π ⟨F, ε⟩`.

So `2π ⟨ε, F⟩` is a representative of minus the translated phase modulo `2π`: this is "Lemma 1,
Sect. 2.3, and the periodicity of the cosine" in the passage from (4.33) to (4.35).
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-- The residual field `ε = φ − dτ` of the endpoint path, FS82 (4.34). -/
noncomputable def xy3ResidualField (x y : XYSites B) : EuclideanSpace ℝ (Dual3Plaquettes B) :=
  xyDual3EndpointPathVector x y - (dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1

theorem inner_pathVector_d1_tau (x y : XYSites B) :
    inner ℝ (xyDual3EndpointPathVector x y)
        ((dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1) =
      inner ℝ (xyDual3PathSourceCoClosed x y).1 (xyDual3PathTau x y).1 := by
  change _ = inner ℝ ((dual3ExactOneComplex B).d₁.adjoint (xyDual3EndpointPathVector x y))
    (xyDual3PathTau x y).1
  rw [LinearMap.adjoint_inner_left]

theorem inner_d1_tau_d1_tau (x y : XYSites B) :
    inner ℝ ((dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1)
        ((dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1) =
      inner ℝ (xyDual3PathSourceCoClosed x y).1 (xyDual3PathTau x y).1 := by
  have hspec := dual3HodgeInverse_spec (xyDual3PathSourceCoClosed x y)
  have hval : formLaplacian (dual3ExactOneComplex B) (xyDual3PathTau x y).1 =
      (xyDual3PathSourceCoClosed x y).1 := congrArg Subtype.val hspec
  rw [← hval]
  change _ = inner ℝ ((dual3ExactOneComplex B).d₁.adjoint
    ((dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1)) (xyDual3PathTau x y).1
  rw [LinearMap.adjoint_inner_left]

/-- The squared norm of the residual field is the residual energy. -/
theorem xy3ResidualField_normSq (x y : XYSites B) :
    ∑ p, (xy3ResidualField x y p) ^ 2 = xyDual3ResidualEnergy x y := by
  have hsum : ∑ p, (xy3ResidualField x y p) ^ 2 =
      inner ℝ (xy3ResidualField x y) (xy3ResidualField x y) := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun p _ => by simp [sq]
  rw [hsum]
  unfold xy3ResidualField xyDual3ResidualEnergy
  have hcomm := real_inner_comm (xyDual3EndpointPathVector x y)
    ((dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_pathVector_d1_tau,
    inner_d1_tau_d1_tau, hcomm, inner_pathVector_d1_tau]
  ring

/-- The endpoint path is integer-valued on the dual plaquettes. -/
theorem xyDual3EndpointPathVector_int (x y : XYSites B) (p : Dual3Plaquettes B) :
    ∃ n : ℤ, xyDual3EndpointPathVector x y p = (n : ℝ) := by
  have hq : realHomogeneousSupport (castIntegerChain (xyEndpointPath x y)) 1 := by
    intro c hc
    exact xyEndpointPath_homogeneousSupport x y c (Finsupp.support_mapRange hc)
  have h := xyDual3StarBondVector_apply (castIntegerChain (xyEndpointPath x y))
    (xyDual3BondPlaquetteEquiv.symm p) hq
  rw [Equiv.apply_symm_apply] at h
  exact ⟨xyEndpointPath x y (xyDual3BondPlaquetteEquiv.symm p).1, by
    unfold xyDual3EndpointPathVector
    rw [h]
    simp [castIntegerChain]⟩

/-- **The phase representative of a filled co-closed current.** -/
theorem xy3_phase_representative_of_filling {β : ℝ} (hβ : 0 < β) (x y : XYSites B)
    {J : Dual3Links B → ℤ} (hJ : RootedTreeGauge.CoClosed (xyDual3RootedTree B) J)
    (F : Dual3Plaquettes B → ℤ)
    (hF : (dual3ExactOneComplex B).d₁.adjoint (WithLp.toLp 2 fun p => ((F p : ℤ) : ℝ)) =
      currentVector J) :
    ∃ n : ℤ, linkPairing (xy3PathShift β x y) J +
        2 * Real.pi * ∑ p, xy3ResidualField x y p * ((F p : ℤ) : ℝ) =
      2 * Real.pi * (n : ℝ) := by
  choose m hm using fun p => xyDual3EndpointPathVector_int x y p
  refine ⟨∑ p, m p * F p, ?_⟩
  rw [linkPairing_xy3PathShift hβ x y hJ, ← hF, LinearMap.adjoint_inner_left, PiLp.inner_apply]
  have hterm : ∀ p : Dual3Plaquettes B,
      inner ℝ ((WithLp.toLp 2 fun p => ((F p : ℤ) : ℝ) : EuclideanSpace ℝ (Dual3Plaquettes B)) p)
        (((dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1) p) =
      ((m p * F p : ℤ) : ℝ) - xy3ResidualField x y p * ((F p : ℤ) : ℝ) := by
    intro p
    have hres : xy3ResidualField x y p = (m p : ℝ) -
        ((dual3ExactOneComplex B).d₁ (xyDual3PathTau x y).1) p := by
      unfold xy3ResidualField
      rw [PiLp.sub_apply, hm p]
    rw [hres]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Int.cast_sum]
  ring

end FroehlichSpencer.FS82.XY

end
