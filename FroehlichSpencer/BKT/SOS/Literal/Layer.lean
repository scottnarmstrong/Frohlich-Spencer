/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.PlaneRotator.TheoremC
public import FroehlichSpencer.BKT.SOS.Literal.CombLimit

/-!
# The pinned comb layer with charges on a sub-region (the finite comb construction)

FS81's state (7.16) has the comb only on the sites of a finite `A ⊆ Ω`.

The Appendix D layer
(`PlaneRotator.pinnedLayerHypothesisD_holds`) is built for the comb on every face: `IsCombTerminal N T`
asks for a start ensemble with a charge at every site, and the waves (`PinnedTerminalWavesW`) and
the coefficient bound (`CombCoefficientBound`) are proved for such terminals.

**The twin trick.** At a site `x ∉ A` replace the factor `1` by the comb `D_N(Nψ_x)`, whose charges
are the multiples `N, 2N, …, N²` of `N` (`combOnLam`).

In the Fourier picture these frequencies run
off to infinity as `N → ∞`, so the continuous sites come out integrated (`Literal/CombLimit.lean`).

The product `∏_{x∈A} D_N(ψ_x) ∏_{x∉A} D_N(Nψ_x)` is a convex combination of single-site charge
products with a charge at **every** site, `f(x) ∈ [1, N²]`, and coefficients `combOnCoeff ≤
combActivity N²` (`prod_combOn_eq`).

The selection steps do not look at the coefficients and update
them monotonically in absolute value (`3K`, `3K·K'`), so every run from these coefficients has a
**twin** run from `combActivity N²` with the same scale, actives and  densities and larger
coefficients (`selReach_twin`).

Its terminal is an `IsCombTerminal N²`; the proved waves and
coefficient bound apply to it, hence to the original terminal (`isCombTerminal_twin`).

`exists_combOnWitness`: for the constants of the Appendix D layer, every box `L ≥ L₀`, every region
`A`, every cutoff `N ≥ 1` carries a rooted D-layer (`CombOnWitness`) of the root-relative observable
`combOnLam L N A`, with local geometry and the exponential entropy bound, uniformly in `L, A, N`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC

variable {L : ℕ}

/-! ## The twin run -/

/-- **Replaying a selection run with larger coefficients.** -/
theorem selReach_twin {M α : ℝ} {S T : SelConfig L} (h : SelReach M α S T)
    (K' : ChargeDensity L → ℝ) (hdom : ∀ ρ, |S.K ρ| ≤ K' ρ) :
    ∃ T' : SelConfig L, SelReach M α ⟨S.j, S.A, S.F, K'⟩ T' ∧ T'.j = T.j ∧ T'.A = T.A ∧
      T'.F = T.F ∧ ∀ ρ, |T.K ρ| ≤ T'.K ρ := by
  induction h with
  | refl => exact ⟨⟨S.j, S.A, S.F, K'⟩, Relation.ReflTransGen.refl, rfl, rfl, rfl, hdom⟩
  | @tail U T hUT hstep ih =>
    obtain ⟨U', hU', hj, hA, hF, hK⟩ := ih
    have hscale : U'.scale = U.scale := by unfold SelConfig.scale; rw [hj]
    have hK0 : ∀ ρ, 0 ≤ U'.K ρ := fun ρ => (abs_nonneg _).trans (hK ρ)
    cases hstep with
    | keepLeft ha hc hne hD =>
      refine ⟨⟨U'.j, U'.A.erase _, U'.F, pairRewriteFirstCoefficient U'.K _⟩,
        hU'.tail (SelStep.keepLeft (hA ▸ ha) (hA ▸ hc) hne (hscale ▸ hD)), hj, by rw [hA], hF,
        fun ρ => ?_⟩
      dsimp only
      unfold pairRewriteFirstCoefficient
      split_ifs with h1
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        exact mul_le_mul_of_nonneg_left (hK _) (by norm_num)
      · exact hK ρ
    | keepRight ha hc hne hD =>
      refine ⟨⟨U'.j, U'.A.erase _, U'.F, pairRewriteSecondCoefficient U'.K _⟩,
        hU'.tail (SelStep.keepRight (hA ▸ ha) (hA ▸ hc) hne (hscale ▸ hD)), hj, by rw [hA], hF,
        fun ρ => ?_⟩
      dsimp only
      unfold pairRewriteSecondCoefficient
      split_ifs with h1
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        exact mul_le_mul_of_nonneg_left (hK _) (by norm_num)
      · exact hK ρ
    | mergeSub ha hc hne hD =>
      refine ⟨⟨U'.j, insert _ ((U'.A.erase _).erase _), U'.F,
        pairRewriteDifferenceCoefficient U'.K _ _⟩,
        hU'.tail (SelStep.mergeSub (hA ▸ ha) (hA ▸ hc) hne (hscale ▸ hD)), hj, by rw [hA], hF,
        fun ρ => ?_⟩
      dsimp only
      unfold pairRewriteDifferenceCoefficient
      split_ifs with h1
      · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hK _) (hK _) (abs_nonneg _) (hK0 _))
          (by norm_num)
      · exact hK ρ
    | mergeAdd ha hc hne hD =>
      refine ⟨⟨U'.j, insert _ ((U'.A.erase _).erase _), U'.F,
        pairRewriteSumCoefficient U'.K _ _⟩,
        hU'.tail (SelStep.mergeAdd (hA ▸ ha) (hA ▸ hc) hne (hscale ▸ hD)), hj, by rw [hA], hF,
        fun ρ => ?_⟩
      dsimp only
      unfold pairRewriteSumCoefficient
      split_ifs with h1
      · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hK _) (hK _) (abs_nonneg _) (hK0 _))
          (by norm_num)
      · exact hK ρ
    | freeze hfar hJ =>
      refine ⟨⟨U'.j + 1, U'.A \ _, U'.F ∪ _, U'.K⟩,
        hU'.tail (SelStep.freeze (hA ▸ hscale ▸ hfar) (hA ▸ hJ)), by rw [hj], by rw [hA],
        by rw [hF], hK⟩

/-! ## The comb on `A`, scaled combs off `A` -/

/-- **The site observables of the comb on `A`**: `D_N` on `A`, the scaled comb `D_N(N·)` off `A`,
and `1` at the wired root. -/
def combOnLam (L N : ℕ) (A : Finset (Site L)) : RotatorDualFace L → ℝ → ℝ :=
  fun k => k.elim (fun _ => 1) (fun x ψ => dirichletComb N ((combMult A N x : ℝ) * ψ))

/-- The scaled charge assignment `x ↦ m(x) g(x)`. -/
def scaledAssignment (A : Finset (Site L)) (N : ℕ) (g : Site L → ℕ) : Site L → ℕ :=
  fun x => combMult A N x * g x

theorem one_le_scaledAssignment {A : Finset (Site L)} {N : ℕ} (hN : 1 ≤ N) {g : Site L → ℕ}
    (hg : ∀ x, 1 ≤ g x) (x : Site L) : 1 ≤ scaledAssignment A N g x :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := one_le_combMult (A := A) hN x; omega)
    (by have := hg x; omega))

/-- The start coefficients `2 Z_N 2^{Σ_x |ρ(x)| / m(x)}`. -/
def combOnCoeff (A : Finset (Site L)) (N : ℕ) (ρ : ChargeDensity L) : ℝ :=
  2 * combNorm N * 2 ^ (∑ x, (ρ x).natAbs / combMult A N x)

theorem combOnCoeff_siteCharge {A : Finset (Site L)} {N : ℕ} (hN : 1 ≤ N) (g : Site L → ℕ)
    (x : Site L) : combOnCoeff A N (siteCharge (scaledAssignment A N g) x) = combCoeff N (g x) := by
  unfold combOnCoeff combCoeff
  congr 2
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [siteCharge_apply, hy]) (by simp)]
  simp only [siteCharge_apply, ↓reduceIte, Int.natAbs_natCast, scaledAssignment]
  exact Nat.mul_div_cancel_left _ (one_le_combMult hN x)

theorem combNorm_le_combNorm_mul {N : ℕ} : combNorm N ≤ combNorm (N * N) := by
  unfold combNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro q hq
  rw [Finset.mem_Icc] at hq ⊢
  exact ⟨hq.1, hq.2.trans (Nat.le_mul_self N)⟩

theorem abs_combOnCoeff_le {A : Finset (Site L)} {N : ℕ} (ρ : ChargeDensity L) :
    |combOnCoeff A N ρ| ≤ combActivity (N * N) ρ := by
  have hZ : 0 ≤ combNorm N := Finset.sum_nonneg fun _ _ => by positivity
  have hZ' : 0 ≤ combNorm (N * N) := Finset.sum_nonneg fun _ _ => by positivity
  have h0 : 0 ≤ combOnCoeff A N ρ := by
    unfold combOnCoeff
    exact mul_nonneg (mul_nonneg (by norm_num) hZ) (by positivity)
  rw [abs_of_nonneg h0]
  unfold combOnCoeff combActivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left combNorm_le_combNorm_mul (by norm_num))
    (pow_le_pow_right₀ (by norm_num) (Finset.sum_le_sum fun x _ => Nat.div_le_self _ _))
    (by positivity) (mul_nonneg (by norm_num) hZ')

/-- **The mixed comb as a single-site mixture.** -/
theorem prod_combOn_eq {A : Finset (Site L)} {N : ℕ} (hN : 1 ≤ N) (φ : Site L → ℝ) :
    ∏ x, dirichletComb N ((combMult A N x : ℝ) * φ x) =
      ∑ g ∈ Fintype.piFinset (fun _ : Site L => Finset.Icc 1 N),
        (∏ x, combWeight N (g x)) *
          chargeFactorProduct (singleSiteEnsemble (scaledAssignment A N g)) (combOnCoeff A N) φ := by
  simp_rw [dirichletComb_eq_mixture hN]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg1 : ∀ x, 1 ≤ g x := fun x => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hg x)).1
  have hf := one_le_scaledAssignment (A := A) hN hg1
  rw [Finset.prod_mul_distrib]
  congr 1
  unfold chargeFactorProduct singleSiteEnsemble
  rw [Finset.prod_image fun x _ y _ h => siteCharge_injective hf h]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [chargeFactor, combOnCoeff_siteCharge hN, chargePhase_siteCharge]
  congr 3
  simp only [scaledAssignment]
  push_cast
  ring

/-- The selection runs of one scaled assignment. -/
def combOnRuns (A : Finset (Site L)) (N : ℕ) (g : Site L → ℕ) : List (ℝ × SelConfig L) :=
  if hf : ∀ x, 1 ≤ scaledAssignment A N g x then
    Classical.choose (exists_runExpansion one_lt_chargeCoverScale one_le_chargeCoverExponent
      (SelConfig.start_valid one_lt_chargeCoverScale one_le_chargeCoverExponent
        (singleSiteEnsemble_pinned hf) (singleSiteEnsemble_card_support hf) (combOnCoeff A N)))
  else []

theorem combOnRuns_spec {A : Finset (Site L)} {N : ℕ} {g : Site L → ℕ}
    (hf : ∀ x, 1 ≤ scaledAssignment A N g x) :
    IsRunExpansion (chargeCoverScale : ℝ) chargeCoverExponent
      (SelConfig.start (singleSiteEnsemble (scaledAssignment A N g)) (combOnCoeff A N))
      (combOnRuns A N g) := by
  unfold combOnRuns
  rw [dite_eq_left hf]
  exact Classical.choose_spec (exists_runExpansion one_lt_chargeCoverScale
    one_le_chargeCoverExponent (SelConfig.start_valid one_lt_chargeCoverScale
      one_le_chargeCoverExponent (singleSiteEnsemble_pinned hf)
        (singleSiteEnsemble_card_support hf) (combOnCoeff A N)))

/-- The weighted branches of the comb on `A`. -/
def combOnBranches (L N : ℕ) (A : Finset (Site L)) : List (ℝ × SelConfig L) :=
  (combAssignments L N).toList.flatMap fun g =>
    scaleRun (∏ x, combWeight N (g x)) (combOnRuns A N g)

/-- A terminal of the comb on `A`. -/
def IsCombOnTerminal (A : Finset (Site L)) (N : ℕ) (T : SelConfig L) : Prop :=
  T.A = ∅ ∧ ∃ g : Site L → ℕ, (∀ x, 1 ≤ g x ∧ g x ≤ N) ∧
    SelReach (chargeCoverScale : ℝ) chargeCoverExponent
      (SelConfig.start (singleSiteEnsemble (scaledAssignment A N g)) (combOnCoeff A N)) T

/-- **The comb branches on `A`.** -/
theorem combOnBranches_spec {A : Finset (Site L)} {N : ℕ} (hN : 1 ≤ N) :
    (∀ b ∈ combOnBranches L N A, 0 < b.1 ∧ IsCombOnTerminal A N b.2) ∧
      ((combOnBranches L N A).map fun b => b.1).sum = 1 ∧
      ∀ φ : Site L → ℝ, ∏ x, dirichletComb N ((combMult A N x : ℝ) * φ x) =
        ((combOnBranches L N A).map fun b => b.1 * chargeFactorProduct b.2.F b.2.K φ).sum := by
  classical
  refine ⟨fun b hb => ?_, ?_, fun φ => ?_⟩
  · obtain ⟨g, hgmem, hb⟩ := List.mem_flatMap.mp hb
    have hg := mem_combAssignments (Finset.mem_toList.mp hgmem)
    have hf := one_le_scaledAssignment (A := A) hN fun x => (hg x).1
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    obtain ⟨hw, hA, hreach⟩ := (combOnRuns_spec hf).1 b' hb'
    exact ⟨mul_pos (Finset.prod_pos fun x _ => combWeight_pos hN _) hw, hA, g, hg, hreach⟩
  · unfold combOnBranches
    rw [sum_map_flatMap]
    have : ∀ g ∈ (combAssignments L N).toList,
        ((scaleRun (∏ x, combWeight N (g x)) (combOnRuns A N g)).map fun b => b.1).sum =
          ∏ x, combWeight N (g x) := by
      intro g hgmem
      have hg := mem_combAssignments (Finset.mem_toList.mp hgmem)
      rw [sum_scaleRun_weight,
        (combOnRuns_spec (one_le_scaledAssignment (A := A) hN fun x => (hg x).1)).2.1, mul_one]
    rw [List.map_congr_left this, Finset.sum_map_toList]
    unfold combAssignments
    rw [← Finset.prod_univ_sum]
    exact Finset.prod_eq_one fun x _ => sum_combWeight hN
  · rw [prod_combOn_eq hN]
    unfold combOnBranches
    rw [sum_map_flatMap]
    have : ∀ g ∈ (combAssignments L N).toList,
        ((scaleRun (∏ x, combWeight N (g x)) (combOnRuns A N g)).map
          fun b => b.1 * chargeFactorProduct b.2.F b.2.K φ).sum =
          (∏ x, combWeight N (g x)) *
            chargeFactorProduct (singleSiteEnsemble (scaledAssignment A N g)) (combOnCoeff A N)
              φ := by
      intro g hgmem
      have hg := mem_combAssignments (Finset.mem_toList.mp hgmem)
      have hspec := combOnRuns_spec (one_le_scaledAssignment (A := A) hN fun x => (hg x).1)
      rw [sum_scaleRun_prod, ← hspec.2.2 φ]
      simp [SelConfig.start]
    rw [List.map_congr_left this, Finset.sum_map_toList]
    rfl

/--
**The twin terminal**: every terminal of the comb on `A` has a comb terminal of cutoff `N²`
with the same  densities and larger coefficients.
-/
theorem isCombTerminal_twin {A : Finset (Site L)} {N : ℕ} (hN : 1 ≤ N) {T : SelConfig L}
    (hT : IsCombOnTerminal A N T) :
    ∃ T'' : SelConfig L, IsCombTerminal (N * N) T'' ∧ T''.F = T.F ∧ ∀ ρ, |T.K ρ| ≤ T''.K ρ := by
  obtain ⟨hA, g, hg, hreach⟩ := hT
  obtain ⟨T'', hreach'', -, hA'', hF'', hK''⟩ :=
    selReach_twin hreach (combActivity (N * N)) fun ρ => abs_combOnCoeff_le ρ
  refine ⟨T'', ⟨by rw [hA'', hA], scaledAssignment A N g, fun x => ⟨?_, ?_⟩, hreach''⟩, hF'', hK''⟩
  · exact one_le_scaledAssignment hN (fun x => (hg x).1) x
  · exact Nat.mul_le_mul (combMult_le hN x) (hg x).2

theorem prod_combOnLam (L N : ℕ) (A : Finset (Site L)) (ψ : RotatorDualFace L → ℝ) :
    ∏ k, combOnLam L N A k (ψ k) =
      ∏ x : Fin L × Fin L, dirichletComb N ((combMult A N x : ℝ) * ψ (some x)) := by
  rw [Fintype.prod_option]
  simp [combOnLam]

/-- **The rooted expansion of the comb on `A`.** -/
theorem prod_combOnLam_eq_branches {A : Finset (Site L)} {N : ℕ} (hN : 1 ≤ N)
    (ψ : RotatorDualFace L → ℝ) (hψ : ψ none = 0) :
    ∏ k, combOnLam L N A k (ψ k) =
      ((combOnBranches L N A).map fun b => b.1 *
        ∏ ϱ ∈ b.2.F.image neutralizeAtWiredRoot,
          (1 + b.2.K (siteRestrict ϱ) * Real.cos (∑ j, ψ j * (ϱ j : ℝ)))).sum := by
  rw [prod_combOnLam, (combOnBranches_spec hN).2.2 (fun x => ψ (some x))]
  congr 1
  apply List.map_congr_left
  intro b _
  rw [chargeFactorProduct_eq_neutralized _ _ _ hψ]

/-! ## The comb layer on `A` -/

/-- **The Appendix D data of the comb on `A`** on one box at cutoff `N` (the analogue of
`PinnedLayerWitnessD` for the observable `combOnLam L N A`). -/
structure CombOnWitness (L N : ℕ) (A : Finset (Site L)) (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ)
    (Kov : ℕ) where
  /-- The density centers. -/
  centerOf : (RotatorDualFace L → ℤ) → RotatorDualFace L
  /-- The cover cost. -/
  cover : (RotatorDualFace L → ℤ) → ℝ
  /-- The entropy factor. -/
  Zent : (RotatorDualFace L → ℤ) → ℝ
  /-- The rooted charge layer of the comb on `A`, D-form. -/
  layer : RootedChargeLayerD (squareZero L) none (combOnLam L N A) centerOf cover Zent
    D₁ D₂ α K₀ K₁
  /-- The density sizes. -/
  dsc : (RotatorDualFace L → ℤ) → ℕ
  /-- The local geometry. -/
  isLocal : layer.IsLocal dsc Kv Kov
  /-- The exponential entropy bound. -/
  entropy_exp : ∀ ϱ : RotatorDualFace L → ℤ,
    Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * cover ϱ)

/-- The comb layer on `A` from the terminal waves and the coefficient bound of the comb on all
faces (through the twin terminals). -/
theorem combOnWitness_of_terminalWavesW {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hC : CombCoefficientBound c₁ c₂) {α K₀ K₁ cP Kv : ℝ} {Kov L₀ : ℕ} (hα : 1 < α)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hcP : 0 < cP) (hKv : 0 ≤ Kv)
    (hW : PinnedTerminalWavesW α K₀ K₁ cP Kv Kov L₀) :
    ∃ (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov L₀ : ℕ), 1 < α ∧ 0 < K₀ ∧ 0 < K₁ ∧ 0 < D₁ ∧ 0 ≤ Kv ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ (A : Finset (Site L)) (N : ℕ), 1 ≤ N →
        Nonempty (CombOnWitness L N A D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov) := by
  refine ⟨layerD₁ * (1 + 1 / cP), c₁ + c₂, α, K₀, K₁, Kv, 0, 0, Kov, L₀, hα, hK₀, hK₁,
    by have := layerD₁_pos; positivity, hKv, ?_⟩
  intro L hL A N hN
  obtain ⟨centerOf, dsc, hdsc, hT⟩ := hW L hL
  have hN2 : 1 ≤ N * N := Nat.one_le_iff_ne_zero.mpr (by have := hN; positivity)
  have spec := combOnBranches_spec (L := L) (A := A) hN
  have hterm : ∀ i : Fin (combOnBranches L N A).length,
      IsCombOnTerminal A N ((combOnBranches L N A)[i.1]).2 :=
    fun i => (spec.1 _ (List.getElem_mem _)).2
  choose T2 hT2 hT2F hT2K using fun i : Fin (combOnBranches L N A).length =>
    isCombTerminal_twin hN (hterm i)
  choose S wv hcl hov using fun i : Fin (combOnBranches L N A).length =>
    hT (N * N) hN2 (T2 i) (hT2 i)
  have hne : ∀ i : Fin (combOnBranches L N A).length, ∀ ρ ∈ (T2 i).F, ρ ≠ 0 :=
    fun i => (hT2 i).geometry.ensemble.1
  let layer : RootedChargeLayerD (squareZero L) none (combOnLam L N A) centerOf layerA
      (fun _ => 1) (layerD₁ * (1 + 1 / cP)) (c₁ + c₂) α K₀ K₁ :=
    { n := (combOnBranches L N A).length
      N := fun i => (T2 i).F.image neutralizeAtWiredRoot
      c := fun i => ((combOnBranches L N A)[i.1]).1
      K := fun i ϱ => ((combOnBranches L N A)[i.1]).2.K (siteRestrict ϱ)
      S := S
      c_pos := fun i => (spec.1 _ (List.getElem_mem _)).1
      c_sum := by
        rw [Fin.sum_univ_fun_getElem (combOnBranches L N A) fun b => b.1]
        exact spec.2.1
      neutral := fun i ϱ hϱ => by
        obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hϱ
        exact sum_neutralizeAtWiredRoot ρ
      expand := fun ψ hψ => by
        rw [prod_combOnLam_eq_branches hN ψ hψ, ← Fin.sum_univ_fun_getElem]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hT2F i]
      entropy := fun i ϱ hϱ => by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        rw [siteRestrict_neutralize, mul_one]
        exact ((hT2K i ρ).trans (le_abs_self _)).trans ((hC L (N * N) _ (hT2 i) ρ hρ).trans
          (Real.exp_le_exp.mpr (exp_le_of_coefficientBound hc₁ hc₂ ρ)))
      wv := wv
      layer := fun i ϱ hϱ => by
        obtain ⟨hα', hK₀', hK₁', hbase, hedge, -⟩ := (hcl i ϱ hϱ).1
        have hsel := (hcl i ϱ hϱ).2.1
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hϱ
        exact ⟨hα', hK₀', hK₁', hbase, hedge,
          layerA_le_piecesW (hT2 i).geometry.isolated hρ (hne i ρ hρ) hcP (Nat.cast_nonneg _)
            hsel,
          fun _ _ h => absurd h (Finset.notMem_empty _)⟩
      wv_local := fun i ϱ hϱ t e he => (hcl i ϱ hϱ).2.2.1 t e he
      wv_orth := fun i ϱ hϱ t ϱ' hϱ' hne' => (hcl i ϱ hϱ).2.2.2.1 t ϱ' hϱ' hne'
      wv_disj := fun i ϱ hϱ ϱ' hϱ' hne' t t' e => (hcl i ϱ hϱ).2.2.2.2.1 ϱ' hϱ' hne' t t' e }
  refine ⟨{
    centerOf := centerOf
    cover := layerA
    Zent := fun _ => 1
    layer := layer
    dsc := dsc
    isLocal := ?_
    entropy_exp := fun ϱ => by simp }⟩
  refine ⟨fun i ϱ hϱ => ?_, fun i ϱ hϱ => ?_, fun i ϱ hϱ => (hcl i ϱ hϱ).2.2.2.2.2.1,
    fun i ϱ hϱ => (hcl i ϱ hϱ).2.2.2.2.2.2, fun i k e U hU hk => hov i k e U hU hk,
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

/-- **The comb layer on `A`, unconditionally**: uniform constants for every box `L ≥ L₀`, every
region `A` and every cutoff. -/
theorem exists_combOnWitness :
    ∃ (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov L₀ : ℕ), 1 < α ∧ 0 < K₀ ∧ 0 < K₁ ∧ 0 < D₁ ∧ 0 ≤ Kv ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ (A : Finset (Site L)) (N : ℕ), 1 ≤ N →
        Nonempty (CombOnWitness L N A D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov) :=
  combOnWitness_of_terminalWavesW
    (Real.log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    combCoefficientBound (α := 7 / 4) (by norm_num) (lt_max_of_lt_left (by norm_num))
    (lt_max_of_lt_left (by norm_num)) (by norm_num : (0 : ℝ) < 1 / 3) routineKv_nonneg
    (pinnedTerminalWavesW_of_profilesW (by norm_num)
      (pinnedTerminalProfilesW_of_split
        (pinnedTerminalProfilesG_of_supportControl (by norm_num) PlaneRotator.supportControl_holds)
        badSelectedBound_proof))

end FroehlichSpencer.BKT.SOS.Literal

end
