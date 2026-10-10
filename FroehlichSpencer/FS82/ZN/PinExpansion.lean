/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.SourceEnsemble
public import FroehlichSpencer.FS82.ZN.AssignmentSum
public import FroehlichSpencer.FS82.ZN.Convergence

/-!
# the pinning factors as a mixture of separated ensembles, and the model bound

On the dual links of a centred cube, for `h > 0`:
-/

open scoped BigOperators
open MeasureTheory
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.CurrentDecay
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.ZN.Torus
open FroehlichSpencer.FS82.ZN.Renormalization

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

local instance pinExpansion_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance pinExpansion_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-! ### The cosine series of the pinning factor -/

/-- FS82 (3.10): `e^{h cos(Nθ)}/I₀(h) = 1 + Σ_{q ≥ 1} λ(q) cos(qNθ)`. -/
theorem normalizedPin_eq_one_add_tsum {N : ℕ} {h θ : ℝ} (hh : 0 ≤ h) :
    Real.exp (h * Real.cos ((N : ℝ) * θ)) / modifiedBesselI 0 h =
      1 + ∑' q : ℕ, wilsonCharacterCoefficient N (q + 1) h *
        Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ)) := by
  obtain ⟨hI0, hsum⟩ := wilsonNormalizedBesselCharacterExpansion (N := N) (h := h) (θ := θ) hh
  have hsm := hsum.summable
  have hl : Summable ((wilsonNormalizedFrequencyTerm N h θ) ∘ Sum.inl) :=
    hsm.comp_injective Sum.inl_injective
  have hr : Summable ((wilsonNormalizedFrequencyTerm N h θ) ∘ Sum.inr) :=
    hsm.comp_injective Sum.inr_injective
  have hl' : Summable fun n : ℕ => wilsonNormalizedFrequencyTerm N h θ (Sum.inl (n + 1)) :=
    hl.comp_injective (add_left_injective 1)
  have hzero : wilsonNormalizedFrequencyTerm N h θ (Sum.inl 0) = 1 := by
    have hI0' : (modifiedBesselI 0 h : ℂ) ≠ 0 := by exact_mod_cast hI0
    change (modifiedBesselI 0 h : ℂ) *
      Complex.exp (((0 : ℕ) : ℂ) * ((((N : ℝ) * θ : ℝ) : ℂ) * Complex.I)) /
        (modifiedBesselI 0 h : ℂ) = 1
    rw [Nat.cast_zero, zero_mul, Complex.exp_zero, mul_one, div_self hI0']
  have hpair : ∀ q : ℕ, wilsonNormalizedFrequencyTerm N h θ (Sum.inl (q + 1)) +
      wilsonNormalizedFrequencyTerm N h θ (Sum.inr q) =
      ((wilsonCharacterCoefficient N (q + 1) h *
        Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ)) : ℝ) : ℂ) := by
    intro q
    have h := wilsonNormalizedCharacterPair_eq_cos (N := N) (q := q + 1) (h := h) (θ := θ)
      (Nat.succ_pos q)
    simp only [Nat.add_sub_cancel] at h
    rw [h]
    push_cast
    rfl
  have hC : (Complex.exp ((h : ℂ) * (Real.cos ((N : ℝ) * θ) : ℂ)) / (modifiedBesselI 0 h : ℂ)) =
      1 + ∑' q : ℕ, ((wilsonCharacterCoefficient N (q + 1) h *
        Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ)) : ℝ) : ℂ) := by
    have hl0 := hl.tsum_eq_zero_add
    simp only [Function.comp_apply] at hl0
    have hr' : Summable fun n : ℕ => wilsonNormalizedFrequencyTerm N h θ (Sum.inr n) := hr
    rw [← hsum.tsum_eq, Summable.tsum_sum hl hr, hl0, hzero, add_assoc,
      ← Summable.tsum_add hl' hr']
    congr 1
    exact tsum_congr hpair
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_tsum, ← hC]
  push_cast
  rfl


theorem znPinningFactor_coe_eq {N : ℕ} (hN : 0 < N) (h : NNReal) (x : ℝ) :
    znPinningFactor N h (x : UnitAddCircle) =
      1 + ∑' q : ℕ, wilsonCharacterCoefficient N (q + 1) (h : ℝ) *
        Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * (2 * Real.pi * x))) := by
  have hser := normalizedPin_eq_one_add_tsum (N := N) (h := (h : ℝ)) (θ := 2 * Real.pi * x) h.2
  rw [← hser]
  unfold znPinningFactor
  rw [pinningNormalization_eq_bessel_inv hN, circleCosCharacter_real]
  rw [show 2 * Real.pi * (N : ℝ) * x = (N : ℝ) * (2 * Real.pi * x) by ring]
  ring

/-! ### The expansion of the product of pinning factors -/

variable {B : Box 4}

/-- The activity of FS82 (3.14) at `ε = 1` satisfies the mode envelope `2 e^{|n|/N}` on the
nonzero multiples of `N`. -/
theorem wilsonIntegerActivity_le_modeEnvelope {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    {n k : ℤ} (hk : k ≠ 0) (hn : n = (N : ℤ) * k) :
    wilsonIntegerActivity 1 N h |n| ≤ 2 * Real.exp (|(n : ℝ)| / (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnat : (|n|).natAbs / N = k.natAbs := by
    rw [Int.natAbs_abs, hn, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hN]
  have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  unfold wilsonIntegerActivity
  rw [hnat, max_eq_right hkpos]
  have hb := (wilsonSourceCoefficientActivity_bound (N := N) (q := k.natAbs) (epsilon := 1)
    (h := h) one_pos hh hkpos).2
  have hexp : |(n : ℝ)| / (N : ℝ) = (k.natAbs : ℝ) := by
    rw [hn]
    push_cast
    rw [abs_mul, abs_of_pos hNR, mul_div_cancel_left₀ _ hNR.ne', Nat.cast_natAbs, Int.cast_abs]
  rw [hexp]
  simpa using hb.le


theorem exists_pinExpansion {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h) :
    ∃ T : (Link B → ℕ) → List (CurrentExpansionTerm B),
      (∀ m, IsFixedFrequencyCurrentExpansion (wilsonModeFrequencyAssignment N m)
        (wilsonIntegerActivity 1 N h) (T m)) ∧
      (∀ m, ∀ t ∈ T m, ∀ a ∈ t.state,
        IsNMultipleCurrent N (lineageCurrent (wilsonModeFrequencyAssignment N m) a)) := by
  have hex : ∀ m : Link B → ℕ, ∃ T : List (CurrentExpansionTerm B),
      IsFixedFrequencyCurrentExpansion (wilsonModeFrequencyAssignment N m)
        (wilsonIntegerActivity 1 N h) T ∧
      (∀ t ∈ T, ∀ a ∈ t.state,
        IsNMultipleCurrent N (lineageCurrent (wilsonModeFrequencyAssignment N m) a)) := by
    intro m
    obtain ⟨T, hT, _, hmult⟩ := exists_wilsonModeFixedAssignmentSeparated (B := B) (N := N) m
      (wilsonIntegerActivity 1 N h) 1 h hN
      (fun n => (wilsonIntegerActivity_pos 1 N h one_pos hh n).le)
      (fun n _ => wilsonIntegerActivity_pos 1 N h one_pos hh n)
      (fun e => wilsonIntegerActivity_frequency_profile 1 h hN m e)
    exact ⟨T, hT, hmult⟩
  choose T hT using hex
  exact ⟨T, fun m => (hT m).1, fun m => (hT m).2⟩

/-- A term of an expansion gives the state hypotheses of `state_lower_bound`. -/
theorem stateHyp_of_expansion {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h) {q : Link B → ℤ}
    {T : List (CurrentExpansionTerm B)}
    (hT : IsFixedFrequencyCurrentExpansion q (wilsonIntegerActivity 1 N h) T)
    (hmult : ∀ t ∈ T, ∀ a ∈ t.state, IsNMultipleCurrent N (lineageCurrent q a))
    {t : CurrentExpansionTerm B} (ht : t ∈ T) :
    StateHyp N q (wilsonIntegerActivity 1 N h) t.state := by
  classical
  obtain ⟨_, hsep, hval, _, _, _, hKpos, hKenv⟩ := hT
  refine ⟨hsep t ht, hval t ht, hKpos t ht, fun a ha => ?_, fun a ha e => ?_⟩
  · refine sourceK_le_sourceFourierKEnvelope (N : ℝ) (lineageJ q a) _
      (fun e => wilsonIntegerActivity 1 N h |lineageCurrent q a e|) ?_ ?_
    · have hk := hKenv t ht a ha
      rw [lineageJ_support]
      exact hk
    · intro e he
      refine ⟨(wilsonIntegerActivity_pos 1 N h one_pos hh _).le, ?_⟩
      obtain ⟨k, hk⟩ := hmult t ht a ha e
      have hne : lineageCurrent q a e ≠ 0 := by
        have := Finsupp.mem_support_iff.mp he
        simpa using this
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hne (by rw [hk, mul_zero])
      rw [lineageJ_apply]
      exact wilsonIntegerActivity_le_modeEnvelope hN hh hk0 hk
  · obtain ⟨k, hk⟩ := hmult t ht a ha e
    exact ⟨k, by rw [lineageJ_apply, hk]⟩

/-- One term of the expansion of `∏_e pin(θ_e)`, as a function on the link torus. -/
def pinTerm (N : ℕ) (h : ℝ) (T : (Link B → ℕ) → List (CurrentExpansionTerm B))
    (γ : Σ m : Link B → ℕ, Fin (T m).length) (θ : Link B → UnitAddCircle) : ℝ :=
  wilsonModeAssignmentCoefficient 1 γ.1 * ((T γ.1).get γ.2).weight *
    ∏ i : {t : ExpansionLineage B // t ∈ ((T γ.1).get γ.2).state},
      cosFactor (lineageCoefficient (wilsonModeFrequencyAssignment N γ.1)
          (wilsonIntegerActivity 1 N h) i.1)
        (lineageCurrent (wilsonModeFrequencyAssignment N γ.1) i.1) 0 θ

theorem continuous_pinTerm (N : ℕ) (h : ℝ) (T : (Link B → ℕ) → List (CurrentExpansionTerm B))
    (γ : Σ m : Link B → ℕ, Fin (T m).length) : Continuous (pinTerm N h T γ) := by
  unfold pinTerm
  exact continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_cosFactor _ _ _)

theorem cosFactor_zero_coe (K : ℝ) (ρ : Link B → ℤ) (x : Link B → ℝ) :
    cosFactor K ρ 0 (fun e => (x e : UnitAddCircle)) =
      1 + K * Real.cos (currentPhase (fun e => 2 * Real.pi * x e) ρ) := by
  unfold cosFactor currentPhase
  rw [pair_coe, AddCircle.coe_zero, add_zero, cosC_coe, Finset.mul_sum]
  congr 3
  exact Finset.sum_congr rfl fun e _ => by ring

theorem pinTerm_coe (N : ℕ) (h : ℝ) (T : (Link B → ℕ) → List (CurrentExpansionTerm B))
    (γ : Σ m : Link B → ℕ, Fin (T m).length) (x : Link B → ℝ) :
    pinTerm N h T γ (fun e => (x e : UnitAddCircle)) =
      wilsonModeAssignmentCurrentTerm N 1 (fun e => 2 * Real.pi * x e) T
        (wilsonIntegerActivity 1 N h) γ := by
  unfold pinTerm wilsonModeAssignmentCurrentTerm currentStateProduct currentFactor
  simp only
  rw [mul_assoc]
  congr 2
  refine (Finset.prod_congr rfl fun i _ => cosFactor_zero_coe _ _ _).trans ?_
  exact Finset.prod_coe_sort _ fun t =>
    1 + lineageCoefficient (wilsonModeFrequencyAssignment N γ.1) (wilsonIntegerActivity 1 N h) t *
      Real.cos (currentPhase (fun e => 2 * Real.pi * x e)
        (lineageCurrent (wilsonModeFrequencyAssignment N γ.1) t))

/-- **The expansion of the product of pinning factors** (FS82 (3.16)–(3.18)). -/
theorem pinTerm_hasSum {N : ℕ} (hN : 0 < N) (h : NNReal)
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B))
    (hT : ∀ m, IsFixedFrequencyCurrentExpansion (wilsonModeFrequencyAssignment N m)
      (wilsonIntegerActivity 1 N (h : ℝ)) (T m))
    (θ : Link B → UnitAddCircle) :
    HasSum (fun γ : Σ m : Link B → ℕ, Fin (T m).length => pinTerm N (h : ℝ) T γ θ)
      (∏ e : Link B, znPinningFactor N h (θ e)) := by
  have hlift : ∀ e, ∃ x : ℝ, (x : UnitAddCircle) = θ e := fun e => exists_real_lift (θ e)
  choose x hx using hlift
  have hθ : θ = fun e => (x e : UnitAddCircle) := funext fun e => (hx e).symm
  have hsum := wilsonModeAssignmentCurrentTerm_hasSum (B := B) (N := N) (epsilon := 1)
    (h := (h : ℝ)) (fun e => 2 * Real.pi * x e) one_pos h.2 T (wilsonIntegerActivity 1 N (h : ℝ))
    (fun m e => wilsonIntegerActivity_frequency_profile 1 (h : ℝ) hN m e) hT
  have hterm : (fun γ : Σ m : Link B → ℕ, Fin (T m).length => pinTerm N (h : ℝ) T γ θ) =
      fun γ => wilsonModeAssignmentCurrentTerm N 1 (fun e => 2 * Real.pi * x e) T
        (wilsonIntegerActivity 1 N (h : ℝ)) γ := by
    funext γ
    rw [hθ, pinTerm_coe]
  have hprod : (∏ e : Link B, znPinningFactor N h (θ e)) =
      ∏ e : Link B, (1 + ∑' q : ℕ, wilsonCharacterCoefficient N (q + 1) (h : ℝ) *
        Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * (2 * Real.pi * x e)))) :=
    Finset.prod_congr rfl fun e _ => by rw [← hx e, znPinningFactor_coe_eq hN]
  rw [hterm, hprod]
  exact hsum

/-- The terms are dominated by their values at the zero configuration. -/
theorem abs_pinTerm_le {N : ℕ} {h : ℝ}
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B))
    (hT : ∀ m, IsFixedFrequencyCurrentExpansion (wilsonModeFrequencyAssignment N m)
      (wilsonIntegerActivity 1 N h) (T m))
    (γ : Σ m : Link B → ℕ, Fin (T m).length) (θ : Link B → UnitAddCircle) :
    |pinTerm N h T γ θ| ≤ pinTerm N h T γ (fun _ => 0) := by
  have hmem : (T γ.1).get γ.2 ∈ T γ.1 := List.get_mem _ _
  obtain ⟨_, _, _, hw, _, _, hKpos, _⟩ := hT γ.1
  have hcoef : 0 ≤ wilsonModeAssignmentCoefficient (B := B) 1 γ.1 := by
    unfold wilsonModeAssignmentCoefficient
    exact Finset.prod_nonneg fun e _ => (inv_pos.mpr (wilsonSplittingWeight_pos one_pos)).le
  have hweight := (hw _ hmem).le
  unfold pinTerm
  rw [abs_mul, abs_of_nonneg (mul_nonneg hcoef hweight), Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hcoef hweight)
  refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  have hK := (hKpos _ hmem i.1 i.2).le
  refine (abs_cosFactor_le hK _ _ θ).trans (le_of_eq ?_)
  have hc0 : cosC (0 : UnitAddCircle) = 1 := by
    have h0 := cosC_coe 0
    simpa using h0
  unfold cosFactor pair
  simp [hc0]

/-! ### The model on the dual links -/

/-- **FS82 (3.51) for the model on the dual links of a centred cube.** With the Wilson weight on
any set `Q` of dual plaquettes, pinning factors on all dual links, and the sheet twist
`φ = (ξ/N) σ`: the twisted integral is at least `e^{−E(β,N)(ξ/N)²(L+T)}` times the untwisted one,
for every `0 ≤ h < ∞`. -/
theorem sourceModel_lower_bound {L T M N ξ : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hM : max L T + 1 ≤ M) (hN : 0 < N) (hξ : 1 ≤ ξ) {β : ℝ} (hβ : 0 ≤ β)
    (ha : 11 ≤ znActivityRate β N) (Q : Finset (SourceDualTwoCells (cube M))) (h : NNReal) :
    Real.exp (-(znStateError β N * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) *
        ∫ θ : Link (cube M) → UnitAddCircle, (∏ e, znPinningFactor N h (θ e)) *
          wilsonWeight β (modelInc Q) (fun _ => 0) θ ≤
      ∫ θ : Link (cube M) → UnitAddCircle, (∏ e, znPinningFactor N h (θ e)) *
        wilsonWeight β (modelInc Q) (fun p => (ξ : ℝ) / (N : ℝ) * cubeSheet L T M p.1) θ := by
  classical
  obtain ⟨t, ht⟩ := exists_shift_eq_sub_loopFieldResidual
    (sourceLatticeComplex (B := cube M)) (cubeSheet L T M)
  by_cases hh : h = 0
  · subst hh
    have hempty : StateHyp N (fun _ : Link (cube M) => (0 : ℤ)) (fun _ => (0 : ℝ))
        (∅ : CurrentState (cube M)) :=
      ⟨fun a ha => absurd ha (Finset.notMem_empty a),
        ⟨fun a ha => absurd ha (Finset.notMem_empty a),
          fun a ha => absurd ha (Finset.notMem_empty a)⟩,
        fun a ha => absurd ha (Finset.notMem_empty a),
        fun a ha => absurd ha (Finset.notMem_empty a),
        fun a ha => absurd ha (Finset.notMem_empty a)⟩
    have hs := state_lower_bound hL hT hM hN hξ hβ ha Q t ht hempty
    have : IsEmpty {h : ExpansionLineage (cube M) // h ∈ (∅ : CurrentState (cube M))} :=
      ⟨fun x => absurd x.2 (Finset.notMem_empty _)⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul] at hs
    simp only [znPinningFactor_zero, Finset.prod_const_one, one_mul]
    exact hs
  · have hhpos : 0 < h := pos_iff_ne_zero.mpr hh
    have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
    obtain ⟨T', hT', hmult⟩ := exists_pinExpansion (B := cube M) hN hhR
    refine mixture_lower_bound (pinTerm N (h : ℝ) T') (continuous_pinTerm N _ T')
      (fun γ => pinTerm N (h : ℝ) T' γ (fun _ => 0)) (abs_pinTerm_le T' hT')
      (pinTerm_hasSum hN h T' hT' (fun _ => 0)).summable
      (fun θ => ∏ e, znPinningFactor N h (θ e)) (pinTerm_hasSum hN h T' hT')
      _ _ (continuous_wilsonWeight β _ _) (continuous_wilsonWeight β _ _) _ ?_
    intro γ
    have hmem : (T' γ.1).get γ.2 ∈ T' γ.1 := List.get_mem _ _
    have hstate := stateHyp_of_expansion hN hhR (hT' γ.1) (hmult γ.1) hmem
    have hs := state_lower_bound hL hT hM hN hξ hβ ha Q t ht hstate
    obtain ⟨_, _, _, hw, _, _, _, _⟩ := hT' γ.1
    have hc : 0 ≤ wilsonModeAssignmentCoefficient (B := cube M) 1 γ.1 *
        ((T' γ.1).get γ.2).weight := by
      refine mul_nonneg ?_ (hw _ hmem).le
      unfold wilsonModeAssignmentCoefficient
      exact Finset.prod_nonneg fun e _ => (inv_pos.mpr (wilsonSplittingWeight_pos one_pos)).le
    have hfac : ∀ V : (Link (cube M) → UnitAddCircle) → ℝ,
        ∫ θ, pinTerm N (h : ℝ) T' γ θ * V θ =
          (wilsonModeAssignmentCoefficient (B := cube M) 1 γ.1 * ((T' γ.1).get γ.2).weight) *
            ∫ θ, (∏ i : {t : ExpansionLineage (cube M) // t ∈ ((T' γ.1).get γ.2).state},
              cosFactor (lineageCoefficient (wilsonModeFrequencyAssignment N γ.1)
                  (wilsonIntegerActivity 1 N (h : ℝ)) i.1)
                (lineageCurrent (wilsonModeFrequencyAssignment N γ.1) i.1) 0 θ) * V θ := by
      intro V
      rw [← integral_const_mul]
      congr 1
      funext θ
      unfold pinTerm
      ring
    rw [hfac, hfac, ← mul_assoc, mul_comm (Real.exp _), mul_assoc]
    exact mul_le_mul_of_nonneg_left hs hc

end

end FroehlichSpencer.FS82.ZN

end
