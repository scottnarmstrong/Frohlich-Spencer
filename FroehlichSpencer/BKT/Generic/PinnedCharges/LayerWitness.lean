/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerAssembly

/-!
`pinnedLayerHypothesisD_of_terminalWaves`: `CombCoefficientBound` and `PinnedTerminalWaves` imply
`PinnedLayerHypothesisD`, hence (by `theoremC_of_pinnedLayerD`) FS81 Theorem C and the
Kosterlitz–Thouless transition.

The witness on the box of side `L` at comb cutoff `N` is:

* ensembles: the neutralized terminal ensembles of the comb branches (`combBranches`), with their
  weights and coefficients (`K(ϱ) = K_b(ϱ|_{faces})`);
* `A = layerA`, `Z ≡ 1`, `D₂ = c₁ + c₂`, `a₁ = a₂ = 0`, `D₁ = layerD₁ (1 + 1/c_P)`;
* waves, support sets, sizes and the local clauses from `PinnedTerminalWaves`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

theorem exp_le_of_coefficientBound {L : ℕ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (ρ : ChargeDensity L) :
    c₁ * ∑ x, |(ρ x : ℝ)| + c₂ * layerCoverSum (neutralizeAtWiredRoot ρ) ≤
      (c₁ + c₂) * layerA (neutralizeAtWiredRoot ρ) := by
  have hm := norm_le_norm_neutralize ρ
  have hm0 : 0 ≤ ∑ x, |(ρ x : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcs := layerCoverSum_nonneg (neutralizeAtWiredRoot ρ)
  unfold layerA
  nlinarith

/-- `A ≤ D₁(‖ϱ‖₁ + #pieces)` with `D₁ = layerD₁ (1 + 1/c_P)` when `c_P · #selected ≤ #pieces`. -/
theorem layerA_le_pieces {L : ℕ} {F : Finset (ChargeDensity L)}
    (hiso : HasBoundaryIsolation (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ : ChargeDensity L} (hρ : ρ ∈ F) (hρ0 : ρ ≠ 0) {cP P : ℝ} (hcP : 0 < cP)
    (hP : cP * layerSelectedSum (neutralizeAtWiredRoot ρ) ≤ P) :
    layerA (neutralizeAtWiredRoot ρ) ≤
      layerD₁ * (1 + 1 / cP) * (∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)| + P) := by
  have hsel : layerSelectedSum (neutralizeAtWiredRoot ρ) ≤ P / cP := by
    rw [le_div_iff₀ hcP]
    linarith
  have h := layerA_le hiso hρ hρ0 hsel
  have hm0 : 0 ≤ ∑ k, |(neutralizeAtWiredRoot ρ k : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP0 : 0 ≤ P := le_trans (mul_nonneg hcP.le (layerSelectedSum_nonneg _)) hP
  have hD := layerD₁_pos
  have hinv : 0 < 1 / cP := by positivity
  have hPc : P / cP = (1 / cP) * P := by ring
  refine h.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hD.le
  rw [hPc]
  nlinarith

/-- **The pinned layer hypothesis from the terminal waves and the coefficient bound.** -/
theorem pinnedLayerHypothesisD_of_terminalWaves {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hC : CombCoefficientBound c₁ c₂) {α K₀ K₁ cP Kv : ℝ} {Kov L₀ : ℕ} (hα : 1 < α)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hcP : 0 < cP) (hKv : 0 ≤ Kv)
    (hW : PinnedTerminalWaves α K₀ K₁ cP Kv Kov L₀) :
    PinnedLayerHypothesisD := by
  refine ⟨layerD₁ * (1 + 1 / cP), c₁ + c₂, α, K₀, K₁, Kv, 0, 0, Kov, L₀, hα, hK₀, hK₁,
    by have := layerD₁_pos; positivity, hKv, ?_⟩
  intro L hL N hN
  obtain ⟨centerOf, dsc, hdsc, hT⟩ := hW L hL
  have spec := combBranches_spec (L := L) hN
  have hterm : ∀ i : Fin (combBranches L N).length,
      IsCombTerminal N ((combBranches L N)[i.1]).2 :=
    fun i => (spec.1 _ (List.getElem_mem _)).2
  choose S wv hcl hov using fun i : Fin (combBranches L N).length =>
    hT N hN ((combBranches L N)[i.1]).2 (hterm i)
  have hne : ∀ i : Fin (combBranches L N).length, ∀ ρ ∈ ((combBranches L N)[i.1]).2.F, ρ ≠ 0 :=
    fun i => (hterm i).geometry.ensemble.1
  let layer : RootedChargeLayerD (squareZero L) none (pinnedCombLam L N) centerOf layerA
      (fun _ => 1) (layerD₁ * (1 + 1 / cP)) (c₁ + c₂) α K₀ K₁ :=
    { n := (combBranches L N).length
      N := fun i => ((combBranches L N)[i.1]).2.F.image neutralizeAtWiredRoot
      c := fun i => ((combBranches L N)[i.1]).1
      K := fun i ϱ => ((combBranches L N)[i.1]).2.K (siteRestrict ϱ)
      S := S
      c_pos := fun i => (spec.1 _ (List.getElem_mem _)).1
      c_sum := by
        rw [Fin.sum_univ_fun_getElem (combBranches L N) fun b => b.1]
        exact spec.2.1
      neutral := fun i ϱ hϱ => by
        obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hϱ
        exact sum_neutralizeAtWiredRoot ρ
      expand := fun ψ hψ => by
        rw [prod_pinnedCombLam_eq_branches hN ψ hψ, ← Fin.sum_univ_fun_getElem]
      entropy := fun i ϱ hϱ => by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        rw [siteRestrict_neutralize, mul_one]
        exact (hC L N _ (hterm i) ρ hρ).trans
          (Real.exp_le_exp.mpr (exp_le_of_coefficientBound hc₁ hc₂ ρ))
      wv := wv
      layer := fun i ϱ hϱ => by
        obtain ⟨hα', hK₀', hK₁', hbase, hedge, hsel⟩ := (hcl i ϱ hϱ).1
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        exact ⟨hα', hK₀', hK₁', hbase, hedge,
          layerA_le_pieces (hterm i).geometry.isolated hρ (hne i ρ hρ) hcP hsel,
          fun _ _ h => absurd h (Finset.notMem_empty _)⟩
      wv_local := fun i ϱ hϱ t e he => (hcl i ϱ hϱ).2.1 t e he
      wv_orth := fun i ϱ hϱ t ϱ' hϱ' hne' => (hcl i ϱ hϱ).2.2.1 t ϱ' hϱ' hne'
      wv_disj := fun i ϱ hϱ ϱ' hϱ' hne' t t' e => (hcl i ϱ hϱ).2.2.2.1 ϱ' hϱ' hne' t t' e }
  refine ⟨{
    centerOf := centerOf
    A := layerA
    Zent := fun _ => 1
    layer := layer
    dsc := dsc
    isLocal := ?_
    entropy_exp := fun ϱ => by simp }⟩
  refine ⟨fun i ϱ hϱ => ?_, fun i ϱ hϱ => ?_, fun i ϱ hϱ => (hcl i ϱ hϱ).2.2.2.2.1,
    fun i ϱ hϱ => (hcl i ϱ hϱ).2.2.2.2.2, fun i k e U hU hk => hov i k e U hU hk,
    fun i ϱ hϱ => ?_⟩
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    intro h0
    apply hne i ρ hρ
    rw [← siteRestrict_neutralize ρ, h0]
    rfl
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    exact (hdsc ρ (hne i ρ hρ)).1
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
    exact logb_le_layerA (hne i ρ hρ) (hdsc ρ (hne i ρ hρ)).2

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
