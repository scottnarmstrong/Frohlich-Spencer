/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PerimeterLoopPhase
public import FroehlichSpencer.FS82.Wilson.CubeLoopField
public import FroehlichSpencer.FS82.Wilson.DualityInteger
public import FroehlichSpencer.FS82.ZN.Renormalization

/-!
# Jensen errors and packing for `Nℤ` currents with the linear activity

FS82 (3.50) sums the Jensen errors `k_ϱ(ε)² z(β, ϱ)` over a 1-ensemble.

So the packing
of §2, whose envelope `e^{−a(‖j‖₂² + |j|)}` is quadratic, does not apply as stated.

This module
proves it for the `ℓ¹` envelope `e^{−a(‖j‖₁ + |j|)}`.
-/

open scoped BigOperators
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Currents.PackingFamily
open FroehlichSpencer.FS82.Currents.SourcePacking
open FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.ZN.Renormalization

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

variable {B : Box 4}

/-! ### The `ℓ¹` mass -/


theorem sourceCurrentL1Mass_eq_currentL1Norm (j : IntegerCurrent B) :
    sourceCurrentL1Mass j = currentL1Norm j := rfl

theorem currentL1Norm_nonneg (j : IntegerCurrent B) : 0 ≤ currentL1Norm j := by
  unfold currentL1Norm
  exact Finset.sum_nonneg fun e _ => abs_nonneg _

/-- Every supported link carries at least one unit of current. -/
theorem card_support_le_currentL1Norm (j : IntegerCurrent B) :
    (j.support.card : ℝ) ≤ currentL1Norm j := by
  classical
  unfold currentL1Norm
  calc (j.support.card : ℝ) = ∑ _e ∈ j.support, (1 : ℝ) := by simp
    _ ≤ ∑ e ∈ j.support, |((j e : ℤ) : ℝ)| := by
        refine Finset.sum_le_sum fun e he => ?_
        have hne : j e ≠ 0 := Finsupp.mem_support_iff.mp he
        have h1 : (1 : ℤ) ≤ |j e| := Int.one_le_abs hne
        exact_mod_cast h1

/-- The lattice chain of a current has the `ℓ¹` mass of the current. -/
theorem chainL1_sourceCurrentLatticeChain_eq (q : IntegerCurrent B) :
    (chainL1 (sourceCurrentLatticeChain q) : ℝ) = currentL1Norm q := by
  classical
  unfold chainL1 currentL1Norm
  rw [sourceCurrentLatticeChain_support, Finset.sum_map]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  change (((sourceCurrentLatticeChain q (lambdaCellToBumpedBox e.1)).natAbs : ℕ) : ℝ) = _
  rw [sourceCurrentLatticeChain_apply, Int.natAbs_mul]
  have hs : (sourceCurrentOrientationSign e).natAbs = 1 := by
    change (sourceDualT e).natAbs = 1
    rcases sourceDualT_is_pm_one e with h | h <;> simp [h]
  rw [hs, one_mul, Nat.cast_natAbs, Int.cast_abs]

/-! ### Phase representatives with the `ℓ¹` mass -/

/-- **The relative phase representative of a short incidence component**, with the `ℓ¹` mass of
the component: `|θ| ≤ C · (L · max|field|) · ‖component‖₁ · L⁴`. -/
theorem component_relative_phase_l1 (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    {c : CurrentComponentClass j} (hc : c ∈ currentComponents j)
    (m : ℕ) (hmin : ∀ i, m ≤ B i) (hshort : (currentComponentSupport j c).card < m)
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : ℝ,
      (∃ n : ℤ, sourceCurrentPhase (twistedLinkField tau) (currentComponentCurrent j c) + θ =
        2 * Real.pi * (n : ℝ)) ∧
      |θ| ≤ relativeFillingConstant *
        (((currentComponentSupport j c).card : ℝ) *
          sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) *
        currentL1Norm (currentComponentCurrent j c) *
        ((currentComponentSupport j c).card : ℝ) ^ 4 := by
  have hqs := currentComponentCurrent_support j c
  have hco := currentComponentCurrent_divergence_eq_zero_of_divergence_eq_zero j c hdiv
  have hconn : SourceCurrentConnected (currentComponentCurrent j c) := by
    intro u hu v hv
    obtain ⟨n, hn, hpath⟩ := currentComponent_boundary_vertices_connected j c hu hv
    exact ⟨n, by rw [hqs]; exact hn, hpath⟩
  have hL : 1 ≤ (currentComponentCurrent j c).support.card := by
    rw [hqs]
    exact Finset.card_pos.mpr (currentComponentSupport_nonempty j hc)
  have hcube : supportInSourceCube (currentComponentCurrent j c).support
      (componentCubeLower j c) (2 * (currentComponentCurrent j c).support.card) := by
    rw [hqs]
    simpa [componentCubeSide] using componentSupport_in_componentCube j c
  obtain ⟨θ, hn, hbound⟩ := short_current_relative_phase (currentComponentCurrent j c) hco hconn
    m hmin hL (by rw [hqs]; exact hshort) (componentCubeLower j c)
    (componentCubeLower_le j c) hcube tau field sheet hdecomp
  refine ⟨θ, hn, ?_⟩
  rw [hqs, chainL1_sourceCurrentLatticeChain_eq] at hbound
  refine hbound.trans (le_of_eq ?_)
  simp only [componentCubeSide]
  ring

/-- **The phase representative of a co-closed parent, `ℓ¹` envelope.** Each short component gets
its relative filling representative and each long component a representative in `[−π, π]`. If the
activity is below `e^{−a(‖j‖₁ + |j|)}` and the weight is at most five times the activity, the
weighted square of the representative is bounded by the component majorants. -/
theorem exists_relativeParent_phase_l1 (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    (m : ℕ) (hmin : ∀ i, m ≤ B i) (a z gamma : ℝ) (ha : 1 ≤ a)
    (hgamma : j ≠ 0 → gamma ≤ 5 * z)
    (hz : z ≤ Real.exp (-(a * (currentL1Norm j + currentLength j))))
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : ℝ,
      (∃ n : ℤ, sourceCurrentPhase (twistedLinkField tau) j + θ = 2 * Real.pi * (n : ℝ)) ∧
      gamma * θ ^ 2 ≤
        ∑ c ∈ currentComponents j,
          (20 * relativeFillingConstant ^ 2 / a ^ 2) *
            ((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
                relativeComponentMax m j field c ^ 2 := by
  classical
  have hC := relativeFillingConstant_pos
  have hcomp : ∀ c : CurrentComponentClass j, ∃ θ : ℝ, ∃ n : ℤ, c ∈ currentComponents j →
      (sourceCurrentPhase (twistedLinkField tau) (currentComponentCurrent j c) + θ =
          2 * Real.pi * (n : ℝ) ∧
        |θ| ≤ relativeFillingConstant * relativeComponentMax m j field c *
          currentL1Norm (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ) ^ 4) := by
    intro c
    by_cases hc : c ∈ currentComponents j
    · by_cases hshort : (currentComponentSupport j c).card < m
      · obtain ⟨θ, ⟨n, hn⟩, hb⟩ :=
          component_relative_phase_l1 j hdiv hc m hmin hshort tau field sheet hdecomp
        refine ⟨θ, n, fun _ => ⟨hn, ?_⟩⟩
        simpa [relativeComponentMax, hshort] using hb
      · obtain ⟨θ, ⟨n, hn⟩, hb⟩ := exists_phase_representative_abs_le_pi
          (sourceCurrentPhase (twistedLinkField tau) (currentComponentCurrent j c))
        refine ⟨θ, n, fun _ => ⟨hn, hb.trans ?_⟩⟩
        have hne := currentComponentSupport_nonempty j hc
        have hL : (1 : ℝ) ≤ ((currentComponentSupport j c).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hne
        have hE : 1 ≤ currentL1Norm (currentComponentCurrent j c) := by
          have h := card_support_le_currentL1Norm (currentComponentCurrent j c)
          rw [currentComponentCurrent_support] at h
          linarith
        have hL4 : (1 : ℝ) ≤ ((currentComponentSupport j c).card : ℝ) ^ 4 :=
          one_le_pow₀ hL
        have hmax : relativeFillingConstant * relativeComponentMax m j field c = Real.pi := by
          simp only [relativeComponentMax, ite_eq_right hshort]
          field_simp
        rw [hmax]
        have hpi := Real.pi_pos
        nlinarith [mul_le_mul hE hL4 zero_le_one (zero_le_one.trans hE)]
    · exact ⟨0, 0, fun h => (hc h).elim⟩
  choose θc nc hθc using hcomp
  refine ⟨∑ c ∈ currentComponents j, θc c, ⟨∑ c ∈ currentComponents j, nc c, ?_⟩, ?_⟩
  · rw [sourceCurrentPhase_eq_sum_components, ← Finset.sum_add_distrib, Int.cast_sum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c hc => (hθc c hc).1
  · by_cases hzero : j = 0
    · subst hzero
      simp [currentComponents]
    have htotal : currentL1Norm j + currentLength j =
        ∑ c ∈ currentComponents j,
          (currentL1Norm (currentComponentCurrent j c) +
            ((currentComponentSupport j c).card : ℝ)) := by
      rw [currentComponentL1Norm_additive, currentLength_additive, Finset.sum_add_distrib]
    have hsmall : ∀ c ∈ currentComponents j,
        2 ≤ currentL1Norm (currentComponentCurrent j c) +
          ((currentComponentSupport j c).card : ℝ) := by
      intro c hc
      have hne := currentComponentSupport_nonempty j hc
      have hL : (1 : ℝ) ≤ ((currentComponentSupport j c).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hne
      have h := card_support_le_currentL1Norm (currentComponentCurrent j c)
      rw [currentComponentCurrent_support] at h
      linarith
    exact disconnected_jensen_error_le_connected_majorants (currentComponents j) a
      relativeFillingConstant (currentL1Norm j + currentLength j)
      (∑ c ∈ currentComponents j, θc c) gamma z
      (fun c => currentL1Norm (currentComponentCurrent j c))
      (fun c => ((currentComponentSupport j c).card : ℝ)) θc (relativeComponentMax m j field)
      htotal rfl ha hC.le (fun c _ => currentL1Norm_nonneg _)
      (fun c _ => relativeComponentMax_nonneg m j field c) hsmall (hgamma hzero) hz
      (fun c hc => (hθc c hc).2)

/-- **The relative-filling estimate for the `ℓ¹` envelope.** For a family of co-closed currents
with pairwise disjoint supports and activities below `e^{−a(‖j‖₁ + |j|)}`, `a ≥ 7`, in a box with
sides between `m` and `N`: if the curvature of the zero-extended `tau` is an integer sheet minus
`field` on every plaquette, the source phases have representatives modulo `2π` with

`Σ_j w_j θ_j² ≤ 81 c'_pack(a) ‖field‖² + (20π²/a²) · 4(N+1)⁴ · e^{−(a−7)m}`

for every weight `w_j ≤ 5 z_j`. -/
theorem l1_relative_filling_bound (S : Finset (IntegerCurrent B))
    (hclosed : ∀ j ∈ S, currentDivergence j = 0)
    (hdisj : (↑S : Set (IntegerCurrent B)).PairwiseDisjoint fun j => j.support)
    (m N : ℕ) (hmin : ∀ i, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    (a : ℝ) (ha : 7 ≤ a) (w z : IntegerCurrent B → ℝ)
    (hw : ∀ j ∈ S, j ≠ 0 → w j ≤ 5 * z j)
    (hz : ∀ j ∈ S, z j ≤ Real.exp (-(a * (currentL1Norm j + currentLength j))))
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : IntegerCurrent B → ℝ,
      (∀ j ∈ S, ∃ n : ℤ,
        sourceCurrentPhase (twistedLinkField tau) j + θ j = 2 * Real.pi * (n : ℝ)) ∧
      ∑ j ∈ S, w j * θ j ^ 2 ≤
        81 * sourceComponentCpackPrime a relativeFillingConstant *
            ∑ p : SourcePlaquette B, (field p) ^ 2 +
          (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (N + 1) ^ 4 : ℕ) : ℝ) *
            Real.exp (-((a - 7) * (m : ℝ))) := by
  classical
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hC := relativeFillingConstant_pos
  have hpar : ∀ j : IntegerCurrent B, ∃ θ : ℝ, j ∈ S →
      ((∃ n : ℤ, sourceCurrentPhase (twistedLinkField tau) j + θ = 2 * Real.pi * (n : ℝ)) ∧
        w j * θ ^ 2 ≤
          ∑ c ∈ currentComponents j,
            (20 * relativeFillingConstant ^ 2 / a ^ 2) *
              ((currentComponentSupport j c).card : ℝ) ^ 8 *
                Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
                  relativeComponentMax m j field c ^ 2) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨θ, hn, hb⟩ := exists_relativeParent_phase_l1 j (hclosed j hj) m hmin a (z j) (w j)
        ha1 (hw j hj) (hz j hj) tau field sheet hdecomp
      exact ⟨θ, fun _ => ⟨hn, hb⟩⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose θ hθ using hpar
  refine ⟨θ, fun j hj => (hθ j hj).1, ?_⟩
  have hsplit : ∀ j ∈ S, ∀ c ∈ currentComponents j,
      (20 * relativeFillingConstant ^ 2 / a ^ 2) *
          ((currentComponentSupport j c).card : ℝ) ^ 8 *
            Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
              relativeComponentMax m j field c ^ 2 ≤
        sourceComponentActivityL5 a relativeFillingConstant
            (currentComponentSupport j c).card *
          (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2 +
        (20 * Real.pi ^ 2 / a ^ 2) *
          (if (currentComponentSupport j c).card < m then (0 : ℝ) else
            ((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) := by
    intro j _ c _
    by_cases hshort : (currentComponentSupport j c).card < m
    · simp only [relativeComponentMax, ite_eq_left hshort, sourceComponentActivityL5, mul_zero,
        add_zero]
      apply le_of_eq
      ring
    · simp only [relativeComponentMax, ite_eq_right hshort, sourceComponentActivityL5]
      have hnn : 0 ≤ (20 * relativeFillingConstant ^ 2 / a ^ 2) *
          ((currentComponentSupport j c).card : ℝ) ^ 10 *
            Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
          (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2 := by
        positivity
      have heq : (20 * relativeFillingConstant ^ 2 / a ^ 2) *
            ((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
                (Real.pi / relativeFillingConstant) ^ 2 =
          (20 * Real.pi ^ 2 / a ^ 2) *
            (((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) := by
        field_simp
      rw [heq]
      linarith
  calc ∑ j ∈ S, w j * θ j ^ 2
      ≤ ∑ j ∈ S, ∑ c ∈ currentComponents j,
          (sourceComponentActivityL5 a relativeFillingConstant
              (currentComponentSupport j c).card *
            (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2 +
          (20 * Real.pi ^ 2 / a ^ 2) *
            (if (currentComponentSupport j c).card < m then (0 : ℝ) else
              ((currentComponentSupport j c).card : ℝ) ^ 8 *
                Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))))) :=
        Finset.sum_le_sum fun j hj => (hθ j hj).2.trans
          (Finset.sum_le_sum fun c hc => hsplit j hj c hc)
    _ = (∑ j ∈ S, ∑ c ∈ currentComponents j,
          sourceComponentActivityL5 a relativeFillingConstant
              (currentComponentSupport j c).card *
            (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2) +
        (20 * Real.pi ^ 2 / a ^ 2) *
          ∑ j ∈ S, ∑ c ∈ currentComponents j,
            (if (currentComponentSupport j c).card < m then (0 : ℝ) else
              ((currentComponentSupport j c).card : ℝ) ^ 8 *
                Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 81 * sourceComponentCpackPrime a relativeFillingConstant *
            ∑ p : SourcePlaquette B, (field p) ^ 2 +
          (20 * Real.pi ^ 2 / a ^ 2) * (((4 * (N + 1) ^ 4 : ℕ) : ℝ) *
            Real.exp (-((a - 7) * (m : ℝ)))) :=
        add_le_add (sum_relativeMajorants_le S hdisj a ha0 field)
          (mul_le_mul_of_nonneg_left (sum_longMajorants_le S hdisj m N hBmax a ha)
            (by positivity))
    _ = _ := by ring

/-! ### `Nℤ`-valued currents -/

/-- An integer current divided linkwise by `N`. For an `Nℤ`-valued current this is the exact
quotient. -/
def currentDivN (N : ℕ) (ρ : IntegerCurrent B) : IntegerCurrent B :=
  Finsupp.mapRange (fun n : ℤ => n / (N : ℤ)) (by simp) ρ

theorem currentDivN_apply (N : ℕ) (ρ : IntegerCurrent B) (e : Link B) :
    currentDivN N ρ e = ρ e / (N : ℤ) := by
  simp [currentDivN]

theorem zsmul_currentDivN {N : ℕ} {ρ : IntegerCurrent B}
    (hρ : IsNMultipleSourceCurrent N ρ) : (N : ℤ) • currentDivN N ρ = ρ := by
  ext e
  obtain ⟨k, hk⟩ := hρ e
  simp only [Finsupp.smul_apply, currentDivN_apply, smul_eq_mul]
  rw [hk]
  by_cases hN : (N : ℤ) = 0
  · simp [hN]
  · rw [Int.mul_ediv_cancel_left _ hN]

theorem support_natCast_zsmul {N : ℕ} (hN : 0 < N) (j : IntegerCurrent B) :
    ((N : ℤ) • j).support = j.support :=
  Finsupp.support_smul_eq (by exact_mod_cast hN.ne')

theorem currentL1Norm_natCast_zsmul {N : ℕ} (hN : 0 < N) (j : IntegerCurrent B) :
    currentL1Norm ((N : ℤ) • j) = (N : ℝ) * currentL1Norm j := by
  unfold currentL1Norm
  rw [support_natCast_zsmul hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, abs_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]

theorem currentLength_natCast_zsmul {N : ℕ} (hN : 0 < N) (j : IntegerCurrent B) :
    currentLength ((N : ℤ) • j) = currentLength j := by
  unfold currentLength
  rw [support_natCast_zsmul hN]

theorem currentDivergence_intSmul (n : ℤ) (j : IntegerCurrent B)
    (v : SourceDualZeroCells B) :
    currentDivergence (n • j) v = (n : ℝ) * currentDivergence j v := by
  rw [currentDivergence_eq_sum_single (n • j), currentDivergence_eq_sum_single j,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [currentDivergence_single_scale e ((n • j) e), currentDivergence_single_scale e (j e)]
  simp only [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]
  ring

theorem currentDivergence_currentDivN {N : ℕ} (hN : 0 < N) {ρ : IntegerCurrent B}
    (hρ : IsNMultipleSourceCurrent N ρ) (hdiv : currentDivergence ρ = 0) :
    currentDivergence (currentDivN N ρ) = 0 := by
  funext v
  have h := currentDivergence_intSmul (N : ℤ) (currentDivN N ρ) v
  rw [zsmul_currentDivN hρ, hdiv] at h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h0 : (N : ℝ) * currentDivergence (currentDivN N ρ) v = 0 := by simpa using h.symm
  exact (mul_eq_zero.mp h0).resolve_left hN'

theorem sourceCurrentPhase_intSmul (α : Link B → ℝ) (n : ℤ) (j : IntegerCurrent B) :
    sourceCurrentPhase α ((n • j : IntegerCurrent B) : Link B → ℤ) =
      (n : ℝ) * sourceCurrentPhase α j := by
  unfold sourceCurrentPhase
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]
  ring

theorem sourceCurrentPhase_twistedLinkField_smul (c : ℝ)
    (t : EuclideanSpace ℝ (SourceDualOneCells B)) (j : Link B → ℤ) :
    sourceCurrentPhase (twistedLinkField (c • t)) j =
      c * sourceCurrentPhase (twistedLinkField t) j := by
  unfold sourceCurrentPhase twistedLinkField
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- **The relative-filling estimate for `Nℤ`-valued currents.** The activity envelope is
`e^{−a(‖ϱ‖₁/N + |ϱ|)}`, and the phases are those of the quotients `ϱ/N`. -/
theorem nMultiple_relative_filling_bound {N : ℕ} (hN : 0 < N)
    (S : Finset (IntegerCurrent B))
    (hmult : ∀ ρ ∈ S, IsNMultipleSourceCurrent N ρ)
    (hclosed : ∀ ρ ∈ S, currentDivergence ρ = 0)
    (hdisj : (↑S : Set (IntegerCurrent B)).PairwiseDisjoint fun ρ => ρ.support)
    (m M : ℕ) (hmin : ∀ i, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ M)
    (a : ℝ) (ha : 7 ≤ a) (w z : IntegerCurrent B → ℝ)
    (hw : ∀ ρ ∈ S, ρ ≠ 0 → w ρ ≤ 5 * z ρ)
    (hz : ∀ ρ ∈ S,
      z ρ ≤ Real.exp (-(a * (currentL1Norm ρ / (N : ℝ) + currentLength ρ))))
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : IntegerCurrent B → ℝ,
      (∀ ρ ∈ S, ∃ n : ℤ,
        sourceCurrentPhase (twistedLinkField tau) (currentDivN N ρ) + θ ρ =
          2 * Real.pi * (n : ℝ)) ∧
      ∑ ρ ∈ S, w ρ * θ ρ ^ 2 ≤
        81 * sourceComponentCpackPrime a relativeFillingConstant *
            ∑ p : SourcePlaquette B, (field p) ^ 2 +
          (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (M + 1) ^ 4 : ℕ) : ℝ) *
            Real.exp (-((a - 7) * (m : ℝ))) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinj : Set.InjOn (currentDivN (B := B) N) (↑S : Set (IntegerCurrent B)) := by
    intro ρ₁ h₁ ρ₂ h₂ h
    rw [← zsmul_currentDivN (hmult ρ₁ h₁), ← zsmul_currentDivN (hmult ρ₂ h₂), h]
  have hsupp : ∀ ρ ∈ S, (currentDivN N ρ).support = ρ.support := by
    intro ρ hρ
    have h := support_natCast_zsmul hN (currentDivN N ρ)
    rw [zsmul_currentDivN (hmult ρ hρ)] at h
    exact h.symm
  obtain ⟨θ', hθ', hsum⟩ := l1_relative_filling_bound (S.image (currentDivN N))
    (by
      intro j hj
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hj
      exact currentDivergence_currentDivN hN (hmult ρ hρ) (hclosed ρ hρ))
    (by
      intro j₁ hj₁ j₂ hj₂ hne
      obtain ⟨ρ₁, hρ₁, rfl⟩ := Finset.mem_image.mp hj₁
      obtain ⟨ρ₂, hρ₂, rfl⟩ := Finset.mem_image.mp hj₂
      have hne' : ρ₁ ≠ ρ₂ := fun h => hne (by rw [h])
      have h := hdisj hρ₁ hρ₂ hne'
      simpa only [Function.onFun, hsupp ρ₁ hρ₁, hsupp ρ₂ hρ₂] using h)
    m M hmin hBmax a ha (fun j => w ((N : ℤ) • j)) (fun j => z ((N : ℤ) • j))
    (by
      intro j hj hj0
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hj
      simp only [zsmul_currentDivN (hmult ρ hρ)]
      refine hw ρ hρ ?_
      rintro rfl
      exact hj0 (by ext e; simp [currentDivN_apply]))
    (by
      intro j hj
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hj
      simp only [zsmul_currentDivN (hmult ρ hρ)]
      refine (hz ρ hρ).trans (le_of_eq ?_)
      have h1 := currentL1Norm_natCast_zsmul hN (currentDivN N ρ)
      have h2 := currentLength_natCast_zsmul hN (currentDivN N ρ)
      rw [zsmul_currentDivN (hmult ρ hρ)] at h1 h2
      rw [h1, h2]
      congr 3
      field_simp)
    tau field sheet hdecomp
  refine ⟨fun ρ => θ' (currentDivN N ρ), fun ρ hρ => hθ' _ (Finset.mem_image_of_mem _ hρ), ?_⟩
  refine le_trans (le_of_eq ?_) hsum
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  simp only [zsmul_currentDivN (hmult ρ hρ)]

/-! ### The activity rate -/

/--
It depends only on `β` and
`N`.
-/
def znActivityRate (β : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) / 18 - 1 - (sourceKLengthCoefficient + 6 * β * (Real.cosh 1 - 1))) / 2

/--
This is FS82 (3.40).
-/
theorem sourceLocalActivity_le_l1Envelope (β : ℝ) (N : ℕ) (selectedMass K : ℝ)
    (j : IntegerCurrent B) (hβ : 0 ≤ β) (hN : 0 < N) (hrate : 0 ≤ znActivityRate β N)
    (hNmultiple : IsNMultipleSourceCurrent N j)
    (hK : K ≤ sourceFourierKEnvelope (N : ℝ) j)
    (hselection : sourceCurrentL1Mass j / 18 ≤ selectedMass) :
    sourceLocalActivity β (j.support.card : ℝ) K selectedMass ≤
      Real.exp (-(znActivityRate β N * (currentL1Norm j / (N : ℝ) + currentLength j))) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcK := sourceKLengthCoefficient_nonneg
  have hcosh : 0 ≤ Real.cosh 1 - 1 := by linarith [Real.one_le_cosh (1 : ℝ)]
  set c₂ := sourceKLengthCoefficient + 6 * β * (Real.cosh 1 - 1) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hK' : K ≤ Real.exp (sourceKLengthCoefficient * (j.support.card : ℝ) +
      sourceCurrentL1Mass j / (N : ℝ)) :=
    hK.trans (sourceFourierKEnvelope_le_exponential (N : ℝ) j)
  have hlinear := sourceLocalActivity_linearEnvelope β sourceKLengthCoefficient (N : ℝ)
    (j.support.card : ℝ) (sourceCurrentL1Mass j) selectedMass K hβ hNR hK' hselection
  refine hlinear.trans (Real.exp_le_exp.mpr ?_)
  have hmul := sourceCurrentL1Mass_ge_support_mul_N N j hNmultiple
  have hratio : (j.support.card : ℝ) ≤ sourceCurrentL1Mass j / (N : ℝ) := by
    rw [le_div_iff₀ hNR]
    nlinarith [hmul]
  have halg : (((N : ℝ) / 18 - 1) / (N : ℝ)) * sourceCurrentL1Mass j =
      ((N : ℝ) / 18 - 1) * (sourceCurrentL1Mass j / (N : ℝ)) := by
    field_simp
  have hN18 : (N : ℝ) / 18 - 1 = 2 * znActivityRate β N + c₂ := by
    unfold znActivityRate
    ring
  rw [halg, hN18, ← sourceCurrentL1Mass_eq_currentL1Norm]
  unfold currentLength
  nlinarith [mul_nonneg hrate (sub_nonneg.mpr hratio), mul_nonneg hc₂0 (sub_nonneg.mpr hratio)]

/-! ### Centred cubes -/

/-- The coefficient of the `(ξ/N)² (L + T)` bound: the short components contribute
`486 N² c'_pack(a)` and the long ones `40π² N² e^{−4(a−11)}/a²`. -/
def znPackingCoefficient (a : ℝ) (N : ℕ) : ℝ :=
  486 * (N : ℝ) ^ 2 * sourceComponentCpackPrime a relativeFillingConstant +
    40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2

theorem znPackingCoefficient_nonneg {a : ℝ} (ha : 0 < a) (N : ℕ) :
    0 ≤ znPackingCoefficient a N := by
  unfold znPackingCoefficient
  have := sourceComponentCpackPrime_nonneg a relativeFillingConstant ha
  positivity

/-- On the cube of side `2M`, `M ≥ 2`, the long-component term is at most `4 e^{−4(a−11)}` once
the rate is at least `11`. -/
theorem cube_longTerm_le_exp {a : ℝ} (ha : 11 ≤ a) {M : ℕ} (hM : 2 ≤ M) :
    ((4 * (2 * M + 1) ^ 4 : ℕ) : ℝ) * Real.exp (-((a - 7) * ((2 * M : ℕ) : ℝ))) ≤
      4 * Real.exp (-(4 * (a - 11))) := by
  have hx : (4 : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
    have : 4 ≤ 2 * M := by omega
    exact_mod_cast this
  have h1 : ((2 * M : ℕ) : ℝ) + 1 ≤ Real.exp ((2 * M : ℕ) : ℝ) := Real.add_one_le_exp _
  have h4 : (((2 * M : ℕ) : ℝ) + 1) ^ 4 ≤ Real.exp (4 * ((2 * M : ℕ) : ℝ)) := by
    calc (((2 * M : ℕ) : ℝ) + 1) ^ 4 ≤ Real.exp ((2 * M : ℕ) : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) h1 4
      _ = Real.exp (4 * ((2 * M : ℕ) : ℝ)) := by
          rw [← Real.exp_nat_mul]
          norm_num
  have hcast : ((4 * (2 * M + 1) ^ 4 : ℕ) : ℝ) = 4 * (((2 * M : ℕ) : ℝ) + 1) ^ 4 := by
    push_cast
    ring
  rw [hcast]
  calc 4 * (((2 * M : ℕ) : ℝ) + 1) ^ 4 * Real.exp (-((a - 7) * ((2 * M : ℕ) : ℝ)))
      ≤ 4 * Real.exp (4 * ((2 * M : ℕ) : ℝ)) * Real.exp (-((a - 7) * ((2 * M : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num))
          (Real.exp_pos _).le
    _ = 4 * Real.exp (-((a - 11) * ((2 * M : ℕ) : ℝ))) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ 4 * Real.exp (-(4 * (a - 11))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hx)]

/-- **FS82 (3.50) on centred cubes, phase part.** Let `σ` be the `L × T` sheet in the cube of
side `2M`, `r` its loop-field residual and `t` a link field with `d₁ t = σ − r`. For a family of
co-closed `Nℤ`-valued currents with pairwise disjoint supports and activities below
`e^{−a(‖ϱ‖₁/N + |ϱ|)}`, `a ≥ 11`, the phases of the shift `−(ξ/N) t` have representatives modulo
`2π` with

`Σ_ϱ w_ϱ θ_ϱ² ≤ znPackingCoefficient a N · (ξ/N)² · (L + T)`

for every weight `w_ϱ ≤ 5 z_ϱ`. -/
theorem cube_zn_phase_bound {L T M N ξ : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hM : max L T + 1 ≤ M) (hN : 0 < N) (hξ : 1 ≤ ξ) {a : ℝ} (ha : 11 ≤ a)
    (S : Finset (IntegerCurrent (cube M)))
    (hmult : ∀ ρ ∈ S, IsNMultipleSourceCurrent N ρ)
    (hclosed : ∀ ρ ∈ S, currentDivergence ρ = 0)
    (hdisj : (↑S : Set (IntegerCurrent (cube M))).PairwiseDisjoint fun ρ => ρ.support)
    (w z : IntegerCurrent (cube M) → ℝ)
    (hw : ∀ ρ ∈ S, ρ ≠ 0 → w ρ ≤ 5 * z ρ)
    (hz : ∀ ρ ∈ S,
      z ρ ≤ Real.exp (-(a * (currentL1Norm ρ / (N : ℝ) + currentLength ρ))))
    (t : EuclideanSpace ℝ (SourceDualOneCells (cube M)))
    (ht : (sourceLatticeComplex (B := cube M)).d₁ t =
      cubeSheet L T M -
        loopFieldResidual (sourceLatticeComplex (B := cube M)) (cubeSheet L T M)) :
    ∃ θ : IntegerCurrent (cube M) → ℝ,
      (∀ ρ ∈ S, ∃ n : ℤ,
        sourceCurrentPhase (twistedLinkField ((-(ξ : ℝ) / (N : ℝ)) • t)) ρ + θ ρ =
          2 * Real.pi * (n : ℝ)) ∧
      ∑ ρ ∈ S, w ρ * θ ρ ^ 2 ≤
        znPackingCoefficient a N * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ha0 : 0 < a := by linarith
  set C := sourceLatticeComplex (B := cube M) with hC
  set σ := cubeSheet L T M with hσ
  set r := loopFieldResidual C σ with hr
  have hsheet : ∀ f : SourceDualTwoCells (cube M),
      ((sourceIntegerCubeSheet L T M f : ℤ) : ℝ) = σ f := by
    intro f
    have h := congrArg (fun y : EuclideanSpace ℝ (SourceDualTwoCells (cube M)) => y.ofLp f)
      (sourceIntegerCubeSheet_cast_eq_cubeSheet L T M)
    simpa [castIntegerFinsupp, finsuppToEuclidean_apply] using h
  have hshift : C.d₁ ((-(ξ : ℝ)) • t) = (-(ξ : ℝ)) • σ - (-(ξ : ℝ)) • r := by
    rw [map_smul, ht, smul_sub]
  have hdecomp := loopField_plaquette_decomposition ((-(ξ : ℝ)) • t) ((-(ξ : ℝ)) • σ)
    ((-(ξ : ℝ)) • r) (fun f => -(ξ : ℤ) * sourceIntegerCubeSheet L T M f)
    (fun f => by
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast, PiLp.smul_apply, smul_eq_mul]
      rw [hsheet f]) hshift
  obtain ⟨θ, hθ, hsum⟩ := nMultiple_relative_filling_bound hN S hmult hclosed hdisj
    (2 * M) (2 * M) (fun _ => le_rfl) (fun _ => le_rfl) a (by linarith) w z hw hz
    ((-(ξ : ℝ)) • t) _ _ hdecomp
  refine ⟨θ, fun ρ hρ => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hθ ρ hρ
    refine ⟨n, ?_⟩
    rw [← hn]
    congr 1
    have h1 := sourceCurrentPhase_intSmul (twistedLinkField t) (N : ℤ) (currentDivN N ρ)
    rw [zsmul_currentDivN (hmult ρ hρ)] at h1
    rw [sourceCurrentPhase_twistedLinkField_smul, sourceCurrentPhase_twistedLinkField_smul, h1]
    push_cast
    field_simp
  · refine hsum.trans ?_
    rw [sum_controlledOrientedDualField_sq]
    have hnorm : (∑ f : SourceDualTwoCells (cube M), (r f) ^ 2) = ‖r‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    have hfield : (∑ f : SourceDualTwoCells (cube M), (((-(ξ : ℝ)) • r) f) ^ 2) =
        (ξ : ℝ) ^ 2 * ‖r‖ ^ 2 := by
      rw [← hnorm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hfield]
    have hrle : ‖r‖ ^ 2 ≤ 6 * ((L : ℝ) + T) := cube_loopField_normSq_le hM
    have hM2 : 2 ≤ M := by
      have : 1 ≤ max L T := le_max_of_le_left hL
      omega
    have hlong := cube_longTerm_le_exp ha hM2
    have hcp0 := sourceComponentCpackPrime_nonneg a relativeFillingConstant ha0
    have hLT : (2 : ℝ) ≤ (L : ℝ) + T := by
      have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      have h2 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      linarith
    have hξ1 : (1 : ℝ) ≤ (ξ : ℝ) ^ 2 := by
      have h : (1 : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast hξ
      nlinarith
    have hcoef : 0 ≤ 20 * Real.pi ^ 2 / a ^ 2 := by positivity
    have hlong' : (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (2 * M + 1) ^ 4 : ℕ) : ℝ) *
        Real.exp (-((a - 7) * ((2 * M : ℕ) : ℝ))) ≤
          (20 * Real.pi ^ 2 / a ^ 2) * (4 * Real.exp (-(4 * (a - 11)))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hlong hcoef
    have hexp0 : 0 < Real.exp (-(4 * (a - 11))) := Real.exp_pos _
    have hscale : ((ξ : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ) ^ 2 = (ξ : ℝ) ^ 2 := by
      field_simp
    have hmain : 81 * sourceComponentCpackPrime a relativeFillingConstant *
        ((ξ : ℝ) ^ 2 * ‖r‖ ^ 2) ≤
          486 * (N : ℝ) ^ 2 * sourceComponentCpackPrime a relativeFillingConstant *
            ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) := by
      have h1 : 81 * sourceComponentCpackPrime a relativeFillingConstant *
          ((ξ : ℝ) ^ 2 * ‖r‖ ^ 2) ≤
            81 * sourceComponentCpackPrime a relativeFillingConstant *
              ((ξ : ℝ) ^ 2 * (6 * ((L : ℝ) + T))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrle (sq_nonneg _))
          (by positivity)
      refine h1.trans (le_of_eq ?_)
      rw [← hscale]
      ring
    have hlongFinal : (20 * Real.pi ^ 2 / a ^ 2) * (4 * Real.exp (-(4 * (a - 11)))) ≤
        40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2 *
          ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) := by
      have hpos : 0 ≤ 40 * Real.pi ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2 := by positivity
      have h2 : (2 : ℝ) ≤ (ξ : ℝ) ^ 2 * ((L : ℝ) + T) := by nlinarith
      calc (20 * Real.pi ^ 2 / a ^ 2) * (4 * Real.exp (-(4 * (a - 11))))
          = 40 * Real.pi ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2 * 2 := by ring
        _ ≤ 40 * Real.pi ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2 *
              ((ξ : ℝ) ^ 2 * ((L : ℝ) + T)) := mul_le_mul_of_nonneg_left h2 hpos
        _ = _ := by
            rw [← hscale]
            ring
    have hcast : ((2 * M : ℕ) : ℝ) = ((2 * M : ℕ) : ℝ) := rfl
    unfold znPackingCoefficient
    calc 81 * sourceComponentCpackPrime a relativeFillingConstant * ((ξ : ℝ) ^ 2 * ‖r‖ ^ 2) +
          (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (2 * M + 1) ^ 4 : ℕ) : ℝ) *
            Real.exp (-((a - 7) * ((2 * M : ℕ) : ℝ)))
        ≤ 486 * (N : ℝ) ^ 2 * sourceComponentCpackPrime a relativeFillingConstant *
              ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) +
            40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2 *
              ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) :=
          add_le_add hmain (hlong'.trans hlongFinal)
      _ = _ := by ring


/-! ### The coefficient tends to zero -/

theorem znActivityRate_eq (β : ℝ) (N : ℕ) :
    znActivityRate β N =
      (N : ℝ) / 36 - (1 + (sourceKLengthCoefficient + 6 * β * (Real.cosh 1 - 1))) / 2 := by
  unfold znActivityRate
  ring

/-- The threshold above which the rate is at least `11`. It depends only on `β`. -/
def znRateThreshold (β : ℝ) : ℝ :=
  36 * (11 + (1 + (sourceKLengthCoefficient + 6 * β * (Real.cosh 1 - 1))) / 2)

theorem eleven_le_znActivityRate {β : ℝ} {N : ℕ} (hN : znRateThreshold β ≤ (N : ℝ)) :
    11 ≤ znActivityRate β N := by
  rw [znActivityRate_eq]
  unfold znRateThreshold at hN
  linarith

/-- The constant of the exponential bound on the packing coefficient. -/
def znPackingEnvelopeConstant : ℝ :=
  486 * (1280 * relativeFillingConstant ^ 2) * Real.exp 1 * componentPolyTail13 +
    40 * Real.pi ^ 2 * Real.exp 11


/-- For `a ≥ 11` the packing coefficient is at most a constant times `N² e^{−a}`. -/
theorem znPackingCoefficient_le_exp {a : ℝ} (ha : 11 ≤ a) (N : ℕ) :
    znPackingCoefficient a N ≤ znPackingEnvelopeConstant * (N : ℝ) ^ 2 * Real.exp (-a) := by
  have hT := componentPolyTail13_nonneg
  have hcp := sourceComponentCpackPrime_exp_bound a relativeFillingConstant (by linarith)
  have hexp1 : Real.exp (1 - a) = Real.exp 1 * Real.exp (-a) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have h1 : 486 * (N : ℝ) ^ 2 * sourceComponentCpackPrime a relativeFillingConstant ≤
      486 * (1280 * relativeFillingConstant ^ 2) * Real.exp 1 * componentPolyTail13 *
        (N : ℝ) ^ 2 * Real.exp (-a) := by
    have := mul_le_mul_of_nonneg_left hcp (by positivity : (0 : ℝ) ≤ 486 * (N : ℝ) ^ 2)
    refine this.trans (le_of_eq ?_)
    rw [hexp1]
    ring
  have hexp2 : Real.exp (-(4 * (a - 11))) ≤ Real.exp 11 * Real.exp (-a) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have ha2 : (1 : ℝ) ≤ a ^ 2 := by nlinarith
  have h2 : 40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2 ≤
      40 * Real.pi ^ 2 * Real.exp 11 * (N : ℝ) ^ 2 * Real.exp (-a) := by
    have hnum : 0 ≤ 40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * Real.exp (-(4 * (a - 11))) := by
      positivity
    calc 40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * Real.exp (-(4 * (a - 11))) / a ^ 2
        ≤ 40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * Real.exp (-(4 * (a - 11))) :=
          div_le_self hnum ha2
      _ ≤ 40 * Real.pi ^ 2 * (N : ℝ) ^ 2 * (Real.exp 11 * Real.exp (-a)) :=
          mul_le_mul_of_nonneg_left hexp2 (by positivity)
      _ = _ := by ring
  unfold znPackingCoefficient znPackingEnvelopeConstant
  linarith

/-- **The packing coefficient tends to zero as `N → ∞` at fixed `β`** (FS82 after (3.50):
`c(β, N) → 0` exponentially fast). -/
theorem tendsto_znPackingCoefficient (β : ℝ) :
    Filter.Tendsto (fun N : ℕ => znPackingCoefficient (znActivityRate β N) N)
      Filter.atTop (nhds 0) := by
  set c := (1 + (sourceKLengthCoefficient + 6 * β * (Real.cosh 1 - 1))) / 2 with hc
  have hbase : Filter.Tendsto (fun N : ℕ => ((N : ℝ) / 36) ^ 2 * Real.exp (-((N : ℝ) / 36)))
      Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have hdiv : Filter.Tendsto (fun N : ℕ => (N : ℝ) / 36) Filter.atTop Filter.atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num)
    exact h.comp hdiv
  have hg : Filter.Tendsto
      (fun N : ℕ => znPackingEnvelopeConstant * 1296 * Real.exp c *
        (((N : ℝ) / 36) ^ 2 * Real.exp (-((N : ℝ) / 36)))) Filter.atTop (nhds 0) := by
    simpa using hbase.const_mul (znPackingEnvelopeConstant * 1296 * Real.exp c)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, znRateThreshold β ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [hev] with N hN
    exact znPackingCoefficient_nonneg (by linarith [eleven_le_znActivityRate hN]) N
  · filter_upwards [hev] with N hN
    refine (znPackingCoefficient_le_exp (eleven_le_znActivityRate hN) N).trans (le_of_eq ?_)
    rw [znActivityRate_eq, ← hc]
    have hexp : Real.exp (-((N : ℝ) / 36 - c)) = Real.exp c * Real.exp (-((N : ℝ) / 36)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring

end

end FroehlichSpencer.FS82.ZN

end
