/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.FejerLayerSelection
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerWitness
public import FroehlichSpencer.BKT.PlaneRotator.TheoremC

/-!
# The rooted Fejér layer from Appendix D terminals

The Fejér frequency mixture uses the same positive charge assignments as the comb mixture.

Its
triangular activity is bounded by the comb activity, so every Fejér selector path can be replayed
on the comb with unchanged active/ geometry and larger coefficients.

The resulting comb
terminal is the reference for Appendix D's boundary waves, covers, and multi-cluster clauses.

The layer itself retains the Fejér branch coefficients and the actual Fejér terminal activities.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.PlaneRotator

/-- The uniform constants of the Fejér rooted charge layer. -/
def fejerLayerD₁ : ℝ := layerD₁ * (1 + 1 / (1 / 3 : ℝ))

/-- The uniform entropy coefficient inherited from the comb coefficient estimate. -/
def fejerLayerD₂ : ℝ := Real.log 12 + ((coefC₀ + coefC₁ : ℕ) : ℝ) * Real.log 3

/-- A rooted charge layer for the actual Fejér branches, with uniform Appendix D locality data. -/
structure RootedFejerLayerWitness (L N : ℕ) where
  centerOf : (RotatorDualFace L → ℤ) → RotatorDualFace L
  dsc : (RotatorDualFace L → ℤ) → ℕ
  layer : RootedChargeLayerD (squareZero L) none (rootedFejerLam L N)
    centerOf layerA (fun _ => 1) fejerLayerD₁ fejerLayerD₂ (7 / 4 : ℝ) 6400 8
  isLocal : layer.IsLocal dsc routineKv 1

/-- The root-relative product identity for the expanded Fejér branches. -/
theorem prod_rootedFejerLam_eq_branches {L N : ℕ} (hN : 1 ≤ N)
    (ψ : RotatorDualFace L → ℝ) (hψ : ψ none = 0) :
    ∏ k, rootedFejerLam L N k (ψ k) =
      ((fejerBranches L N).map fun b => b.1 *
        ∏ ϱ ∈ b.2.F.image neutralizeAtWiredRoot,
          (1 + b.2.K (siteRestrict ϱ) *
            Real.cos (∑ j, ψ j * (ϱ j : ℝ)))).sum := by
  have hsite : ∏ k, rootedFejerLam L N k (ψ k) =
      ∏ x : Site L, fejerPolynomial N (ψ (some x)) := by
    rw [Fintype.prod_option]
    simp [rootedFejerLam]
  rw [hsite, (fejerBranches_spec hN).2.2 (fun x => ψ (some x))]
  congr 1
  apply List.map_congr_left
  intro b _
  rw [chargeFactorProduct_eq_neutralized _ _ _ hψ]

/-- The Fejér branches carry their own amplitudes together with a same-geometry comb reference. -/
theorem rootedFejerLayer_exists {L N : ℕ} (hL : 2 ≤ L) (hN : 1 ≤ N) :
    Nonempty (RootedFejerLayerWitness L N) := by
  classical
  have hprofiles : PinnedTerminalProfilesW (7 / 4 : ℝ) 6400 8 (1 / 3 : ℝ) 2 := by
    exact pinnedTerminalProfilesW_of_split
      (pinnedTerminalProfilesG_of_supportControl (by norm_num) supportControl_holds)
      badSelectedBound_proof
  have hW₀ := pinnedTerminalWavesW_of_profilesW (by norm_num) hprofiles
  have hW : PinnedTerminalWavesW (7 / 4 : ℝ) 6400 8 (1 / 3 : ℝ) routineKv 1 2 := by
    simpa only [max_eq_right (by norm_num : (4 : ℝ) ≤ 6400),
      max_eq_right (by norm_num : (2 : ℝ) ≤ 8),
      max_eq_right (by norm_num : (2 : ℕ) ≤ 2)] using hW₀
  obtain ⟨centerOf, dsc, hdsc, htermW⟩ := hW L hL
  let B := fejerBranches L N
  have hspec := fejerBranches_spec (L := L) hN
  have hbranch : ∀ i : Fin B.length,
      0 < B[i.1].1 ∧ B[i.1].2.A = ∅ ∧
        HasCombTerminalReference (N := N) B[i.1].2 := by
    intro i
    exact hspec.1 _ (List.getElem_mem _)
  choose Tref href hshape hdom using fun i : Fin B.length => (hbranch i).2.2
  have hterm : ∀ i : Fin B.length, IsCombTerminal N (Tref i) :=
    fun i => href i
  have hF : ∀ i : Fin B.length, B[i.1].2.F = (Tref i).F :=
    fun i => (hshape i).2.2
  have hmemRef : ∀ (i : Fin B.length) (ϱ : RotatorDualFace L → ℤ),
      ϱ ∈ B[i.1].2.F.image neutralizeAtWiredRoot →
        ϱ ∈ (Tref i).F.image neutralizeAtWiredRoot := by
    intro i ϱ hϱ
    simpa [hF i] using hϱ
  have hmemBranch : ∀ (i : Fin B.length) (ϱ : RotatorDualFace L → ℤ),
      ϱ ∈ (Tref i).F.image neutralizeAtWiredRoot →
        ϱ ∈ B[i.1].2.F.image neutralizeAtWiredRoot := by
    intro i ϱ hϱ
    simpa [hF i] using hϱ
  have hne : ∀ i : Fin B.length, ∀ ρ ∈ (Tref i).F, ρ ≠ 0 :=
    fun i => (hterm i).geometry.ensemble.1
  choose S waveData hcl hov using fun i : Fin B.length =>
    htermW N hN (Tref i) (hterm i)
  have hc₁ : 0 ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hc₂ : 0 ≤ ((coefC₀ + coefC₁ : ℕ) : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  let layer : RootedChargeLayerD (squareZero L) none (rootedFejerLam L N) centerOf
      layerA (fun _ => 1) fejerLayerD₁ fejerLayerD₂ (7 / 4 : ℝ) 6400 8 :=
    { n := B.length
      N := fun i => B[i.1].2.F.image neutralizeAtWiredRoot
      c := fun i => B[i.1].1
      K := fun i ϱ => B[i.1].2.K (siteRestrict ϱ)
      S := fun i ϱ => S i ϱ
      c_pos := fun i => (hbranch i).1
      c_sum := by
        rw [Fin.sum_univ_fun_getElem B fun b => b.1]
        exact hspec.2.1
      neutral := fun i ϱ hϱ => by
        obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hϱ
        exact sum_neutralizeAtWiredRoot ρ
      expand := fun ψ hψ => by
        rw [prod_rootedFejerLam_eq_branches hN ψ hψ,
          ← Fin.sum_univ_fun_getElem B fun b => b.1 *
            ∏ ϱ ∈ b.2.F.image neutralizeAtWiredRoot,
              (1 + b.2.K (siteRestrict ϱ) * Real.cos (∑ j, ψ j * (ϱ j : ℝ)))]
      entropy := fun i ϱ hϱ => by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        have hρref : ρ ∈ (Tref i).F := by
          have hρactual : ρ ∈ B[i.1].2.F := hρ
          simpa [hF i] using hρactual
        rw [siteRestrict_neutralize, mul_one]
        have hcomb := combCoefficientBound L N (Tref i) (hterm i) ρ hρref
        have hdomρ := hdom i ρ
        calc
          |B[i.1].2.K ρ| ≤ |(Tref i).K ρ| := hdomρ
          _ ≤ Real.exp (Real.log 12 * (∑ x, |(ρ x : ℝ)|) +
              ((coefC₀ + coefC₁ : ℕ) : ℝ) * Real.log 3 *
                layerCoverSum (neutralizeAtWiredRoot ρ)) := hcomb
          _ ≤ Real.exp (fejerLayerD₂ * layerA (neutralizeAtWiredRoot ρ)) := by
            apply Real.exp_le_exp.mpr
            simpa [fejerLayerD₂] using
              exp_le_of_coefficientBound hc₁ hc₂ ρ
      wv := fun i ϱ hϱ => waveData i ϱ (hmemRef i ϱ hϱ)
      layer := fun i ϱ hϱ => by
        let hϱref := hmemRef i ϱ hϱ
        obtain ⟨hα, hK₀, hK₁, hbase, hedge, -⟩ := (hcl i ϱ hϱref).1
        have hselected := (hcl i ϱ hϱref).2.1
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        have hρref : ρ ∈ (Tref i).F := by
          simpa [hF i] using hρ
        exact ⟨hα, hK₀, hK₁, hbase, hedge,
          layerA_le_piecesW (hterm i).geometry.isolated hρref (hne i ρ hρref)
            (by norm_num : (0 : ℝ) < 1 / 3) (Nat.cast_nonneg _) hselected,
          fun _ _ h => absurd h (Finset.notMem_empty _)⟩
      wv_local := fun i ϱ hϱ t e he => (hcl i ϱ (hmemRef i ϱ hϱ)).2.2.1 t e he
      wv_orth := fun i ϱ hϱ t ϱ' hϱ' hne' =>
        (hcl i ϱ (hmemRef i ϱ hϱ)).2.2.2.1 t ϱ' (hmemRef i ϱ' hϱ') hne'
      wv_disj := fun i ϱ hϱ ϱ' hϱ' hne' t t' e =>
        (hcl i ϱ (hmemRef i ϱ hϱ)).2.2.2.2.1 ϱ' (hmemRef i ϱ' hϱ') hne' t t' e }
  refine ⟨⟨centerOf, dsc, layer, ?_⟩⟩
  refine ⟨fun i ϱ hϱ => ?_, fun i ϱ hϱ => ?_, fun i ϱ hϱ => ?_,
    fun i ϱ hϱ => ?_, fun i k e U hU hk => ?_, fun i ϱ hϱ => ?_⟩
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    intro h0
    exact (hne i ρ (by simpa [hF i] using hρ)) (by
      rw [← siteRestrict_neutralize ρ, h0]
      rfl)
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    exact (hdsc ρ (hne i ρ (by simpa [hF i] using hρ))).1
  · exact (hcl i ϱ (hmemRef i ϱ hϱ)).2.2.2.2.2.1
  · exact (hcl i ϱ (hmemRef i ϱ hϱ)).2.2.2.2.2.2
  · change U ⊆ B[i.1].2.F.image neutralizeAtWiredRoot at hU
    have hUref : U ⊆ (Tref i).F.image neutralizeAtWiredRoot := by
      intro ρ hρ
      simpa [hF i] using hU hρ
    change ∀ ρ ∈ U, 2 ^ k - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (k + 1) - 2 ∧ e ∈ S i ρ at hk
    exact hov i k e U hUref hk
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    exact logb_le_layerA (hne i ρ (by simpa [hF i] using hρ))
      (hdsc ρ (hne i ρ (by simpa [hF i] using hρ))).2

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
