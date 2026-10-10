/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileACross
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileBCombinatorics

/-!
# Part (A): the terminal profile family from the support control

On a comb terminal `T`, for each neutralized density `ϱ`:

* the scales split by residue mod 3; `profileResidue ϱ` picks a residue class carrying at least a
  third of the charged selected squares (`goodSelectedSum_le_three_mul`);
* one profile per charged selected square `s ∈ P'_j(ρ)` with `j` in that class
  (`profileIndex`): the ramp of a profile potential (`profilePotential`), scale label `j + 3`,
  charge `Q(ρ|_s)`.

* `pinnedTerminalProfilesG_of_supportControl`: `TerminalSupportControl → PinnedTerminalProfilesG`;
* `theoremC_of_supportControl`, `exists_transition_of_supportControl`: **FS81 Theorem C and the
  Kosterlitz–Thouless transition, conditional only on `TerminalSupportControl`** (part (B) is
  the terminal decomposition's `badSelectedBound_proof`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open Filter
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-! ## The index set -/

/-- The charged selected squares at scale `j`. -/
def goodSquares (ϱ : RotatorDualFace L → ℤ) (j : ℕ) : Finset (Finset (Site L)) := by
  classical
  exact (selectedSquares ϱ j).filter fun s => totalCharge (chargeRestriction (siteRestrict ϱ) s) ≠ 0

/-- The number of charged selected squares at scales `≡ r (mod 3)`. -/
def residueSum (ϱ : RotatorDualFace L → ℤ) (r : ℕ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 (layerCutoff ϱ)).filter (fun j => j % 3 = r), ((goodSquares ϱ j).card : ℝ)

/-- A residue class mod 3 with the most charged selected squares. -/
def profileResidue (ϱ : RotatorDualFace L → ℤ) : ℕ :=
  if residueSum ϱ 1 ≤ residueSum ϱ 0 ∧ residueSum ϱ 2 ≤ residueSum ϱ 0 then 0
  else if residueSum ϱ 2 ≤ residueSum ϱ 1 then 1 else 2

theorem goodSelectedSum_eq (ϱ : RotatorDualFace L → ℤ) :
    goodSelectedSum ϱ = ∑ j ∈ Finset.Icc 1 (layerCutoff ϱ), ((goodSquares ϱ j).card : ℝ) := by
  unfold goodSelectedSum goodSquares
  rfl

theorem goodSelectedSum_eq_residueSum (ϱ : RotatorDualFace L → ℤ) :
    goodSelectedSum ϱ = residueSum ϱ 0 + residueSum ϱ 1 + residueSum ϱ 2 := by
  rw [goodSelectedSum_eq, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range 3)
    (g := fun j => j % 3) (fun j _ => Finset.mem_range.mpr (Nat.mod_lt j (by norm_num)))]
  simp [Finset.sum_range_succ, residueSum]

/-- **One residue class carries a third of the charged selected squares.** -/
theorem goodSelectedSum_le_three_mul (ϱ : RotatorDualFace L → ℤ) :
    goodSelectedSum ϱ ≤ 3 * residueSum ϱ (profileResidue ϱ) := by
  rw [goodSelectedSum_eq_residueSum]
  unfold profileResidue
  split_ifs with h1 h2
  · linarith [h1.1, h1.2]
  · push Not at h1
    by_cases h0 : residueSum ϱ 1 ≤ residueSum ϱ 0
    · have := h1 h0; linarith
    · push Not at h0; linarith
  · push Not at h1 h2
    by_cases h0 : residueSum ϱ 1 ≤ residueSum ϱ 0
    · have := h1 h0; linarith
    · push Not at h0; linarith

/-- The profile indices: scale in the chosen residue class, charged selected square. -/
def profileIndex (ϱ : RotatorDualFace L → ℤ) : Finset (Σ _ : ℕ, Finset (Site L)) :=
  ((Finset.Icc 1 (layerCutoff ϱ)).filter (fun j => j % 3 = profileResidue ϱ)).sigma (goodSquares ϱ)

theorem card_profileIndex (ϱ : RotatorDualFace L → ℤ) :
    ((profileIndex ϱ).card : ℝ) = residueSum ϱ (profileResidue ϱ) := by
  unfold profileIndex residueSum
  rw [Finset.card_sigma]
  push_cast
  rfl

/-- The cluster of an index. -/
def profileCluster (ϱ : RotatorDualFace L → ℤ) (t : Σ _ : ℕ, Finset (Site L)) : Finset (Site L) :=
  chargeSupport (chargeRestriction (siteRestrict ϱ) t.2)

/-- The profile of an index. -/
def profileFamilyPiece (F : Finset (ChargeDensity L)) (ϱ : RotatorDualFace L → ℤ)
    (t : Σ _ : ℕ, Finset (Site L)) : RotatorDualFace L → ℝ :=
  profilePiece t.1 (profilePotential F (siteRestrict ϱ) t.1 (profileCluster ϱ t))

theorem neutralize_siteRestrict_of_mem {F : Finset (ChargeDensity L)} {ϱ : RotatorDualFace L → ℤ}
    (h : ϱ ∈ F.image neutralizeAtWiredRoot) :
    siteRestrict ϱ ∈ F ∧ neutralizeAtWiredRoot (siteRestrict ϱ) = ϱ := by
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
  rw [siteRestrict_neutralize]
  exact ⟨hρ, rfl⟩

/-- **The context of every profile of a comb terminal.** -/
theorem profileContext_of_mem {N : ℕ} {T : SelConfig L} (hT : IsCombTerminal N T)
    (hH : TerminalSupportControl) {ϱ : RotatorDualFace L → ℤ}
    (hϱ : ϱ ∈ T.F.image neutralizeAtWiredRoot) {t : Σ _ : ℕ, Finset (Site L)}
    (ht : t ∈ profileIndex ϱ) :
    ProfileContext T.F (siteRestrict ϱ) t.1 t.2
      (profilePotential T.F (siteRestrict ϱ) t.1 (profileCluster ϱ t)) := by
  classical
  obtain ⟨hρ, hϱeq⟩ := neutralize_siteRestrict_of_mem hϱ
  have hgeo := hT.geometry
  obtain ⟨hj, hs⟩ := Finset.mem_sigma.mp ht
  have hj' := (Finset.mem_filter.mp hj).1
  have hs' : t.2 ∈ selectedSquares ϱ t.1 ∧
      totalCharge (chargeRestriction (siteRestrict ϱ) t.2) ≠ 0 := by
    unfold goodSquares at hs
    exact Finset.mem_filter.mp hs
  have hsel : t.2 ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent t.1 (siteRestrict ϱ)
      (boundaryEntropyMinimumCover (siteRestrict ϱ) t.1) := hs'.1
  have hpot := hH L N T hT (siteRestrict ϱ) hρ t.1 (by rw [hϱeq]; exact hj') t.2
    (by rw [hϱeq]; exact hs'.1) hs'.2
  exact ⟨hgeo.separated, hgeo.ensemble.1, hρ, (Finset.mem_Icc.mp hj').1, hsel,
    chargedSelectedSquare_of_mem hsel hs'.2, profilePotential_spec hpot⟩

/-- `2^{-j} ≤ 8·2^{-(1-1/α)(j+3)}` for `α ≥ 0`. -/
theorem inv_two_pow_le (α : ℝ) (hα : 0 ≤ α) (j : ℕ) :
    1 / (2 : ℝ) ^ j ≤ 8 * (2 : ℝ) ^ (-(1 - 1 / α) * ((j + 3 : ℕ) : ℝ)) := by
  have hγ : 1 - 1 / α ≤ 1 := by
    have : 0 ≤ 1 / α := by positivity
    linarith
  have hexp : -((j + 3 : ℕ) : ℝ) ≤ -(1 - 1 / α) * ((j + 3 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((j + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have heq : (2 : ℝ) ^ (-((j + 3 : ℕ) : ℝ)) = 1 / (2 ^ j * 8) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
    congr 1
    ring
  rw [heq] at hmono
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  calc 1 / (2 : ℝ) ^ j = 8 * (1 / (2 ^ j * 8)) := by field_simp
    _ ≤ 8 * (2 : ℝ) ^ (-(1 - 1 / α) * ((j + 3 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)

/-! ## The family -/

/-- **Part (A) on a comb terminal**: the profile family with `K₀ = 6400`, `K₁ = 8`. -/
def terminalProfilesA {N : ℕ} {T : SelConfig L} (hT : IsCombTerminal N T)
    (hH : TerminalSupportControl) (hL : 1 < L) (α : ℝ) (hα : 0 ≤ α) :
    TerminalProfilesG L α 6400 8 T.F where
  ι := fun ϱ => profileIndex ϱ
  fin := fun _ => inferInstance
  scale := fun _ t => t.1.1 + 3
  piece := fun ϱ t => profileFamilyPiece T.F ϱ t.1
  charge := fun ϱ t => (totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2) : ℝ)
  one_le_scale := fun _ _ _ => by omega
  pairing := by
    intro ϱ hϱ t
    have hc := profileContext_of_mem hT hH hϱ t.2
    have hp := hc.pairing_profilePiece
    rw [(neutralize_siteRestrict_of_mem hϱ).2] at hp
    exact hp
  charge_ge_one := by
    intro ϱ hϱ t
    have hc := profileContext_of_mem hT hH hϱ t.2
    have : (1 : ℤ) ≤ |totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2)| :=
      Int.one_le_abs hc.square.charged
    rw [← Int.cast_abs]
    exact_mod_cast this
  energy_le := by
    intro ϱ hϱ t
    have hc := profileContext_of_mem hT hH hϱ t.2
    have he := hc.energy_profilePiece_le hL
    have h1 : (1 : ℝ) ≤ |(totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hc.square.charged
    have h2 : (1 : ℝ) ≤ (totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2) : ℝ) ^ 2 := by
      rw [← sq_abs]; nlinarith
    show (squareZero L).energy (profileFamilyPiece T.F ϱ t.1) ≤ 6400 * _
    unfold profileFamilyPiece
    nlinarith
  grad_le := by
    intro ϱ hϱ t e
    have hc := profileContext_of_mem hT hH hϱ t.2
    exact (hc.abs_grad_profilePiece_le hL e).trans (inv_two_pow_le α hα t.1.1)
  edge_count := by
    intro ϱ hϱ t
    exact (profileContext_of_mem hT hH hϱ t.2).card_grad_profilePiece_ne_zero_le hL
  grad_disjoint := by
    intro ϱ hϱ t t' hne e
    have hc := profileContext_of_mem hT hH hϱ t.2
    have hc' := profileContext_of_mem hT hH hϱ t'.2
    have hr : t.1.1 % 3 = t'.1.1 % 3 := by
      have h1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp t.2).1).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp t'.2).1).2
      rw [h1, h2]
    rcases lt_trichotomy t.1.1 t'.1.1 with hlt | heq | hgt
    · exact (hc'.grad_disjoint_same hc hL (Or.inr (by omega)) e).symm
    · refine hc.grad_disjoint_same hc' hL (Or.inl ⟨heq, fun hss => hne ?_⟩) e
      apply Subtype.ext
      exact Sigma.ext heq (heq_of_eq hss)
    · exact hc.grad_disjoint_same hc' hL (Or.inr (by omega)) e
  supp := by
    intro ϱ hϱ t
    have hc := profileContext_of_mem hT hH hϱ t.2
    have hs := hc.support_profilePiece_subset hL
    rw [(neutralize_siteRestrict_of_mem hϱ).2] at hs
    exact hs
  count := by
    intro ϱ _
    rw [zero_mul]
    exact Nat.cast_nonneg _
  local_ := by
    intro ϱ hϱ t e he
    have hc := profileContext_of_mem hT hH hϱ t.2
    have hm := hc.grad_profilePiece_mem_routineS hL he
    rw [(neutralize_siteRestrict_of_mem hϱ).2] at hm
    exact hm
  avoid := by
    intro ϱ hϱ t σ hσ x hx e hinc
    exact (profileContext_of_mem hT hH hϱ t.2).grad_eq_zero_of_incident hL hσ hx hinc
  orth := by
    intro ϱ hϱ t ϱ' hϱ' hne
    have hc := profileContext_of_mem hT hH hϱ t.2
    obtain ⟨hσ, hσeq⟩ := neutralize_siteRestrict_of_mem hϱ'
    have hσne : siteRestrict ϱ' ≠ siteRestrict ϱ := by
      intro h0
      apply hne
      rw [← hσeq, h0, (neutralize_siteRestrict_of_mem hϱ).2]
    have := hc.sum_profilePiece_mul_neutralize_eq_zero hσ hσne
    rw [hσeq] at this
    exact this
  disj := by
    intro ϱ hϱ ϱ' hϱ' hne t t' e
    have hc := profileContext_of_mem hT hH hϱ t.2
    have hc' := profileContext_of_mem hT hH hϱ' t'.2
    have hσne : siteRestrict ϱ' ≠ siteRestrict ϱ := by
      intro h0
      apply hne
      rw [← (neutralize_siteRestrict_of_mem hϱ).2, ← h0, (neutralize_siteRestrict_of_mem hϱ').2]
    rcases le_total t'.1.1 t.1.1 with hle | hle
    · exact hc.grad_disjoint_cross hc' hL hσne hle e
    · exact (hc'.grad_disjoint_cross hc hL hσne.symm hle e).symm
  countG := by
    intro ϱ _
    have h := goodSelectedSum_le_three_mul ϱ
    rw [← card_profileIndex] at h
    simpa [Fintype.card_coe] using h

/-! ## Part (A) and Theorem C -/

/-- **Part (A) from the support control.** -/
theorem pinnedTerminalProfilesG_of_supportControl {α : ℝ} (hα : 0 ≤ α)
    (hH : TerminalSupportControl) : PinnedTerminalProfilesG α 6400 8 2 :=
  fun _ hL _ _ _ hT => ⟨terminalProfilesA hT hH (by omega) α hα⟩

/-- **FS81 Theorem C, conditional only on the support control.** -/
theorem theoremC_of_supportControl (hH : TerminalSupportControl) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_split (α := 7 / 4) (by norm_num)
    (pinnedTerminalProfilesG_of_supportControl (by norm_num) hH) badSelectedBound_proof

/-- **The Kosterlitz–Thouless transition, conditional only on the support control.** -/
theorem exists_transition_of_supportControl (hH : TerminalSupportControl) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_split (α := 7 / 4) (by norm_num)
    (pinnedTerminalProfilesG_of_supportControl (by norm_num) hH) badSelectedBound_proof

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
