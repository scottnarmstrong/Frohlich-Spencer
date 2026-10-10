/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Assembly
import Mathlib.Tactic

/-! # Fejér cutoff removal and the carrier transfer for the Dirichlet marked estimate -/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.VillainDisorder
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

/-- The cutoff marked ratios converge to the squareZero integer-GFF dipole expectation. -/
theorem tendsto_dirichletFejerMarkedRatio_igff {R n : ℕ} (hR : 1 ≤ R) (hn : n ≤ R)
    {β ξ : ℝ} (hβ : 0 < β) (hnpos : 1 ≤ n) :
    Filter.Tendsto (fun N : ℕ => dirichletFejerMarkedRatio R n hR hn β ξ hβ N) atTop
      (𝓝 (igffExpectation (graph R) (graph_connected R hR) β⁻¹ (inv_pos.mpr hβ) none
        (fun h => dipoleCosine R n hn ξ h))) := by
  let βf := dirichletGffParameter β
  have hβf : 0 < βf := dirichletGffParameter_pos hβ
  have h := tendsto_gffFejerCosRatio_igff (graph R) (graph_connected R hR)
    βf hβf none ξ (dirichletDipoleSource R n hn)
  have hobs (m : Height R) :
      Real.cos (2 * Real.pi * ξ * Multigraph.pairing (fun j => (m.1 j : ℝ))
        (dirichletDipoleSource R n hn)) = dipoleCosine R n hn ξ m := by
    rw [pairing_dirichletDipoleSource_eq hn hnpos]
    unfold dipoleCosine
    rw [← Int.cast_sub]
  have hscale : (2 * Real.pi) ^ 2 *
      (β⁻¹ / (2 * Real.pi) ^ 2) = β⁻¹ := by
    field_simp
  simpa only [dirichletFejerMarkedRatio, dirichletFejerDenominator, βf,
    dirichletGffParameter, hscale, hobs] using h

/-- A closed interval bound for every positive cutoff passes to the IGFF limit. -/
theorem rootedDirichletIGFFBoundAt_of_fejerBoundAt {R n : ℕ} (hR : 1 ≤ R) (hn : n ≤ R)
    (β ξ η c : ℝ) (hβ : 0 < β) (hnpos : 1 ≤ n)
    (h : RootedDirichletFejerBoundAt R n hR hn β ξ η c hβ) :
    RootedDirichletIGFFBoundAt R n hR hn β ξ η c hβ := by
  have hlim := tendsto_dirichletFejerMarkedRatio_igff hR hn (ξ := ξ) hβ hnpos
  let B := 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < N :=
    eventually_atTop.2 ⟨1, fun N hN => by omega⟩
  have hEventually : ∀ᶠ N : ℕ in atTop,
      dirichletFejerMarkedRatio R n hR hn β ξ hβ N ∈ Set.Icc 0 B := by
    filter_upwards [hpos] with N hN
    exact ⟨(h N hN).2.1, (h N hN).2.2⟩
  have hlim' := isClosed_Icc.mem_of_tendsto hlim hEventually
  exact hlim'

/-- Global cutoff bounds transfer to the rooted square IGFF, keeping the same constants. -/
theorem rootedDirichletIGFFMarkedBound_of_fejerInput
    (hFejer : RootedDirichletFejerGlobalInput) : RootedDirichletIGFFGlobalBound := by
  rcases hFejer with ⟨c, hc, hη⟩
  refine ⟨c, hc, fun η hηpos hηle => ?_⟩
  rcases hη η hηpos hηle with ⟨β₀, hβ₀, hβ⟩
  refine ⟨β₀, hβ₀, fun β hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos => ?_⟩
  rcases hβ β hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos with ⟨R₀, hnR₀, hR₀⟩
  refine ⟨R₀, hnR₀, fun R hbuffer hn => ?_⟩
  let hβ' : 0 < β := lt_trans hβ₀ hβlarge
  let hR' : 1 ≤ R := Nat.le_trans hnpos (Nat.le_trans hnR₀ hbuffer)
  exact rootedDirichletIGFFBoundAt_of_fejerBoundAt hR' hn β ξ η c hβ' hnpos
    (hR₀ R hbuffer hn)

/-- The carrier identity turns the rooted IGFF bound into the normalized finite law (1.35). -/
theorem rootedDirichletMarkedBound_of_igffInput
    (hIGFF : RootedDirichletIGFFGlobalBound) : RootedDirichletMarkedBound := by
  rcases hIGFF with ⟨c, hc, hη⟩
  refine ⟨c, hc, fun η hηpos hηle => ?_⟩
  rcases hη η hηpos hηle with ⟨β₀, hβ₀, hβ⟩
  refine ⟨β₀, hβ₀, fun β hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos => ?_⟩
  rcases hβ β hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos with ⟨R₀, hnR₀, hR₀⟩
  refine ⟨R₀, hnR₀, fun R hbuffer hn => ?_⟩
  let hR : 1 ≤ R := Nat.le_trans hnpos (Nat.le_trans hnR₀ hbuffer)
  have hβ' : 0 < β := lt_trans hβ₀ hβlarge
  have hbound := hR₀ R hbuffer hn
  have hcarrier := cosineExpectation_eq_igffExpectation (ξ := ξ) hR hn hβ'
  rcases hbound with ⟨hlo, hhi⟩
  change 0 ≤ cosineExpectation R n hn β ξ ∧
    cosineExpectation R n hn β ξ ≤
      2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))
  rw [hcarrier]
  exact ⟨hlo, hhi⟩

/-- Direct assembly from the D2 cutoff hypothesis to the finite zero-exterior carrier bound. -/
theorem rootedDirichletMarkedBound_of_fejerInput
    (hFejer : RootedDirichletFejerGlobalInput) : RootedDirichletMarkedBound :=
  rootedDirichletMarkedBound_of_igffInput
    (rootedDirichletIGFFMarkedBound_of_fejerInput hFejer)

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet
