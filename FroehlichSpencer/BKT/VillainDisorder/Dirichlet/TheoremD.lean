/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.AssemblyVillain
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

/-! # Theorem D for the centered Dirichlet free-box exhaustion

Assuming the marked Fejér estimate, the (1.38) finite-volume identity gives the power bound on every
sufficiently large free primal box. The centered expectations form a bounded real sequence, so
subsequential limits exist and every cluster point inherits the eventual closed-interval bound.
No uniqueness of the thermodynamic limit is asserted.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

/-- The disorder expectation in the centered free primal box of radius `R`; zero is used only
when the fixed string does not fit in the box. -/
def dirichletCenteredDisorder (R n : ℕ) (β ξ : ℝ) (hβ : 0 < β) : ℝ :=
  if hn : n ≤ R then dirichletFreeVillainDisorderExpectation R n hn β ξ hβ else 0

/-- The fixed axial string fits in every sufficiently large centered box. -/
theorem eventually_dirichletStringFits (n : ℕ) : ∀ᶠ R in atTop, n ≤ R := by
  exact eventually_atTop.2 ⟨n, fun R hR => hR⟩

/-- The marked Fejér input implies the rooted Dirichlet marked bound on every sufficiently large
finite free primal box. -/
theorem rootedDirichletFreeBox_bound_of_fejerInput
    (hFejer : RootedDirichletFejerGlobalInput) :
    ∃ c : ℝ, 0 < c ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        ∃ β₀ : ℝ, ∃ hβ₀ : 0 < β₀,
          ∀ β : ℝ, ∀ hβlarge : β₀ < β,
            ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
              ∀ n : ℕ, ∀ _hnpos : 1 ≤ n,
                ∃ R₀ : ℕ, n ≤ R₀ ∧
                  ∀ R : ℕ, ∀ _hbuffer : R₀ ≤ R, ∀ hn : n ≤ R,
                    let hβ' : 0 < β := lt_trans hβ₀ hβlarge
                    0 ≤ dirichletFreeVillainDisorderExpectation R n hn β ξ hβ' ∧
                    dirichletFreeVillainDisorderExpectation R n hn β ξ hβ' ≤
                      2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)) := by
  obtain ⟨c, hc, hmarked⟩ := rootedDirichletMarkedBound_of_fejerInput hFejer
  refine ⟨c, hc, fun η hη hηle => ?_⟩
  obtain ⟨β₀, hβ₀, hmarked_at⟩ := hmarked η hη hηle
  refine ⟨β₀, hβ₀, fun β hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos => ?_⟩
  obtain ⟨R₀, hnR₀, hR₀⟩ := hmarked_at β hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos
  refine ⟨R₀, hnR₀, fun R hbuffer hn => ?_⟩
  let hR : 1 ≤ R := Nat.le_trans hnpos hn
  have hβpos : 0 < β := lt_trans hβ₀ hβlarge
  have hbound := hR₀ R hbuffer hn
  have hdual := dirichletFreeVillainDisorderExpectation_eq_cosineExpectation
    R n hR hn β ξ hβpos
  change 0 ≤ dirichletFreeVillainDisorderExpectation R n hn β ξ hβpos ∧
    dirichletFreeVillainDisorderExpectation R n hn β ξ hβpos ≤
      2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))
  rw [hdual]
  exact hbound

/-- The actual centered finite expectations are bounded in `[-1,1]` whenever the string fits;
non-fitting values are zero. -/
theorem dirichletCenteredDisorder_mem_Icc_one (R n : ℕ) (β ξ : ℝ) (hβ : 0 < β)
    (hnpos : 1 ≤ n) :
    dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc (-1) 1 := by
  unfold dirichletCenteredDisorder
  split_ifs with hn
  · have hR : 1 ≤ R := hnpos.trans hn
    rw [dirichletFreeVillainDisorderExpectation_eq_cosineExpectation R n hR hn β ξ hβ]
    exact cosineExpectation_mem_Icc_one hR hn β ξ hβ
  · norm_num

/-- From the D2 core, the centered free-box disorder expectations obey the FS81 power bound on
all sufficiently large boxes and every cluster point. The bounded sequence has a convergent
subsequence. -/
theorem rootedDirichletTheoremD_thermodynamicLimit
    (hFejer : RootedDirichletFejerGlobalInput) :
    ∃ c : ℝ, 0 < c ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        ∃ β₀ : ℝ, ∃ _hβ₀ : 0 < β₀,
          ∀ β : ℝ, ∀ hβ : 0 < β, ∀ _hβlarge : β₀ < β,
            ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
              ∀ n : ℕ, ∀ _hnpos : 1 ≤ n,
                (∀ᶠ R in atTop, n ≤ R) ∧
                (∀ R : ℕ, dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc (-1) 1) ∧
                (∀ᶠ R in atTop,
                  dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc 0
                    (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)))) ∧
                (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
                  Tendsto (fun k => dirichletCenteredDisorder (φ k) n β ξ hβ)
                    atTop (𝓝 ℓ)) ∧
                ∀ ℓ : ℝ,
                  MapClusterPt ℓ atTop (fun R => dirichletCenteredDisorder R n β ξ hβ) →
                    ℓ ∈ Set.Icc 0
                      (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))) := by
  obtain ⟨c, hc, hfinite⟩ := rootedDirichletFreeBox_bound_of_fejerInput hFejer
  refine ⟨c, hc, fun η hη hηle => ?_⟩
  obtain ⟨β₀, hβ₀, hfinite'⟩ := hfinite η hη hηle
  refine ⟨β₀, hβ₀, fun β hβ hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos => ?_⟩
  obtain ⟨R₀, hnR₀, hbox⟩ := hfinite' β hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos
  let B : ℝ := 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))
  have hfits : ∀ᶠ R in atTop, n ≤ R := eventually_dirichletStringFits n
  have hglobal : ∀ R, dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc (-1) 1 :=
    fun R => dirichletCenteredDisorder_mem_Icc_one R n β ξ hβ hnpos
  have htail : ∀ᶠ R in atTop,
      dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc 0 B := by
    filter_upwards [eventually_atTop.2 ⟨R₀, fun R hR₀ => hR₀⟩] with R hR₀
    have hn : n ≤ R := le_trans hnR₀ hR₀
    have hR : 1 ≤ R := hnpos.trans hn
    have hbound := hbox R hR₀ hn
    have hcenter : dirichletCenteredDisorder R n β ξ hβ =
        dirichletFreeVillainDisorderExpectation R n hn β ξ hβ := by
      simp [dirichletCenteredDisorder, hn]
    rw [hcenter, show B = 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)) by rfl]
    exact hbound
  have hmem : ∀ R, dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc (-1) 1 := hglobal
  have hseq : ∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => dirichletCenteredDisorder (φ k) n β ξ hβ) atTop (𝓝 ℓ) := by
    obtain ⟨ℓ, -, φ, hφ, hT⟩ :=
      tendsto_subseq_of_bounded (Metric.isBounded_Icc (-1 : ℝ) 1) hmem
    exact ⟨ℓ, φ, hφ, hT⟩
  have hcluster (ℓ : ℝ)
      (hℓ : MapClusterPt ℓ atTop (fun R => dirichletCenteredDisorder R n β ξ hβ)) :
      ℓ ∈ Set.Icc 0 B := by
    exact isClosed_Icc.mem_of_mapClusterPt hℓ htail
  refine ⟨hfits, hglobal, ?_, hseq, ?_⟩
  · simpa [B] using htail
  · intro ℓ hℓ
    exact hcluster ℓ hℓ

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet
