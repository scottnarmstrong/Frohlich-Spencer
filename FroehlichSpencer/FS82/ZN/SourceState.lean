/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.SourceIncidence
public import FroehlichSpencer.FS82.ZN.ErrorBudget
public import FroehlichSpencer.FS82.Root.BranchLineage
public import FroehlichSpencer.FS82.Root.SignedCurrent
public import FroehlichSpencer.FS82.ZN.Renormalization

/-!
# the geometry of one separated ensemble on the dual links

For a separated, valid current state of the §2 expansion on the links of `Λ*`:

* `lineageJ q t`: the integer current of a lineage (in the dual orientation of the links);
* `stateGaugeDir`: for a current that is not co-closed, the gauge direction of a vertex where its
  divergence does not vanish.

It is annihilated by every plaquette row, pairs nontrivially with
  the current, and trivially with the other currents of the state (they share no vertex);
* `linkShift ρ S`: the shift vector `sign(ρ_x)` on a set `S` of selected links (FS82 (3.35) with
  `c₀ = 1`); when no plaquette contains two links of `S`, every plaquette shift has modulus at
  most one and at most `6 |S|` plaquettes are shifted.
-/

open scoped BigOperators
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.CurrentDecay
open FroehlichSpencer.FS82.Root.MomentComparisonAssembly
open FroehlichSpencer.FS82.ZN.Torus
open FroehlichSpencer.FS82.ZN.Renormalization

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

variable {B : Box 4}

/-! ### The currents of a state -/

/-- The integer current of a lineage. -/
def lineageJ (q : Link B → ℤ) (t : ExpansionLineage B) : IntegerCurrent B :=
  integerCurrentOfFunction (lineageCurrent q t)

@[simp] theorem lineageJ_apply (q : Link B → ℤ) (t : ExpansionLineage B) (e : Link B) :
    lineageJ q t e = lineageCurrent q t e := by
  simp [lineageJ]

theorem lineageJ_support (q : Link B → ℤ) (t : ExpansionLineage B) :
    (lineageJ q t).support = currentSupport (lineageCurrent q t) := by
  ext e
  simp [currentSupport]

theorem lineageJ_support_eq_stateCurrent (q : Link B → ℤ) (s : CurrentState B)
    (i : {h : ExpansionLineage B // h ∈ s}) :
    (lineageJ q i.1).support = (stateCurrent q s i).support := by
  rw [lineageJ_support, stateCurrent_support]

/-! ### Gauge directions -/

/-- The gauge direction used to eliminate a lineage current that is not co-closed. -/
def stateGaugeDir (q : Link B → ℤ) (t : ExpansionLineage B) : Link B → ℤ := by
  classical
  exact if h : ∃ v, currentDivergence (lineageJ q t) v ≠ 0 then gaugeDir (Classical.choose h)
    else fun _ => 0

theorem sum_curlInt_stateGaugeDir (q : Link B → ℤ) (t : ExpansionLineage B)
    (p : SourceDualTwoCells B) : ∑ e : Link B, curlInt p e * stateGaugeDir q t e = 0 := by
  classical
  unfold stateGaugeDir
  split_ifs with h
  · exact sum_curlInt_gaugeDir p _
  · simp

theorem sum_mul_stateGaugeDir_ne_zero (q : Link B → ℤ) (t : ExpansionLineage B)
    (hdiv : currentDivergence (lineageJ q t) ≠ 0) :
    ∑ e : Link B, lineageCurrent q t e * stateGaugeDir q t e ≠ 0 := by
  classical
  have h : ∃ v, currentDivergence (lineageJ q t) v ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hdiv (funext hno)
  unfold stateGaugeDir
  rw [dite_eq_left h]
  intro hzero
  have hcast := sum_mul_gaugeDir (lineageJ q t) (Classical.choose h)
  simp only [lineageJ_apply] at hcast
  rw [hzero] at hcast
  exact Classical.choose_spec h (by simpa using hcast.symm)

/-- In a separated state the gauge direction of one current does not see the others. -/
theorem sum_mul_stateGaugeDir_eq_zero {q : Link B → ℤ} {s : CurrentState B}
    (hs : IsSeparatedCurrentState q s) (i j : {h : ExpansionLineage B // h ∈ s}) (hji : j ≠ i) :
    ∑ e : Link B, lineageCurrent q j.1 e * stateGaugeDir q i.1 e = 0 := by
  classical
  unfold stateGaugeDir
  split_ifs with h
  · set v := Classical.choose h with hv
    have hvne : currentDivergence (lineageJ q i.1) v ≠ 0 := Classical.choose_spec h
    have hcast := sum_mul_gaugeDir (lineageJ q j.1) v
    simp only [lineageJ_apply] at hcast
    have hzero : currentDivergence (lineageJ q j.1) v = 0 := by
      by_contra hne
      obtain ⟨e, he, heinc⟩ := exists_incident_support_of_divergence_ne_zero _ v hvne
      obtain ⟨f, hf, hfinc⟩ := exists_incident_support_of_divergence_ne_zero _ v hne
      rw [lineageJ_support_eq_stateCurrent q s] at he hf
      exact state_hvert hs i j (Ne.symm hji) e he f hf ⟨v, heinc, hfinc⟩
    rw [hzero] at hcast
    exact_mod_cast hcast
  · simp

/-! ### Selected links and their shifts -/

/-- The shift vector `sign(ρ_x)` on the selected links `S`, zero elsewhere. -/
def linkShift (ρ : Link B → ℤ) (S : Finset (Link B)) : Link B → ℝ := by
  classical
  exact fun x => if x ∈ S then ((SignType.sign ((ρ x : ℤ) : ℝ) : SignType) : ℝ) else 0

theorem abs_sign_cast_le_one (r : ℝ) : |((SignType.sign r : SignType) : ℝ)| ≤ 1 := by
  rcases lt_trichotomy r 0 with h | h | h
  · simp [sign_neg h]
  · simp [h]
  · simp [sign_pos h]

/-- The pairing of a current with its own shift is the `ℓ¹` mass on the selected links. -/
theorem sum_mul_linkShift (ρ : Link B → ℤ) (S : Finset (Link B)) :
    ∑ x : Link B, (ρ x : ℝ) * linkShift ρ S x = ∑ x ∈ S, |(ρ x : ℝ)| := by
  classical
  unfold linkShift
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl fun x _ => self_mul_sign _

/-- A current that vanishes on `S` does not see the shift on `S`. -/
theorem sum_mul_linkShift_eq_zero (ρ ρ' : Link B → ℤ) (S : Finset (Link B))
    (h : ∀ x ∈ S, ρ' x = 0) : ∑ x : Link B, (ρ' x : ℝ) * linkShift ρ S x = 0 := by
  classical
  unfold linkShift
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x ∈ S
  · simp [h x hx]
  · simp [hx]

variable (Q : Finset (SourceDualTwoCells B))

/-- The plaquette incidence of the model on a set `Q` of dual plaquettes. -/
def modelInc (p : {p : SourceDualTwoCells B // p ∈ Q}) (e : Link B) : ℤ := curlInt p.1 e

theorem plaqShift_modelInc_linkShift (ρ : Link B → ℤ) (S : Finset (Link B))
    (p : {p : SourceDualTwoCells B // p ∈ Q}) :
    plaqShift (modelInc Q) (linkShift ρ S) p =
      ∑ x ∈ S, ((curlInt p.1 x : ℤ) : ℝ) * ((SignType.sign ((ρ x : ℤ) : ℝ) : SignType) : ℝ) := by
  classical
  unfold plaqShift linkShift modelInc
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem exists_incident_of_plaqShift_ne_zero (ρ : Link B → ℤ) (S : Finset (Link B))
    (p : {p : SourceDualTwoCells B // p ∈ Q})
    (h : plaqShift (modelInc Q) (linkShift ρ S) p ≠ 0) :
    ∃ x ∈ S, linkIncidentPlaquette x p.1 := by
  classical
  rw [plaqShift_modelInc_linkShift] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨x, hx, linkIncidentPlaquette_of_curlInt_ne_zero ?_⟩
  intro h0
  apply hne
  rw [h0]
  simp

/-- With at most one selected link per plaquette, every plaquette shift has modulus at most
one. -/
theorem abs_plaqShift_le_one (ρ : Link B → ℤ) (S : Finset (Link B))
    (hS : ∀ e ∈ S, ∀ f ∈ S, ¬ (e ≠ f ∧ ∃ p : SourceDualTwoCells B,
      linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p))
    (p : {p : SourceDualTwoCells B // p ∈ Q}) :
    |plaqShift (modelInc Q) (linkShift ρ S) p| ≤ 1 := by
  classical
  rw [plaqShift_modelInc_linkShift]
  by_cases hall : ∀ x ∈ S, curlInt p.1 x = 0
  · rw [Finset.sum_eq_zero fun x hx => by rw [hall x hx]; simp]
    simp
  · push Not at hall
    obtain ⟨x₀, hx₀, hne⟩ := hall
    have hothers : ∀ y ∈ S, y ≠ x₀ →
        ((curlInt p.1 y : ℤ) : ℝ) * ((SignType.sign ((ρ y : ℤ) : ℝ) : SignType) : ℝ) = 0 := by
      intro y hy hyx
      have hy0 : curlInt p.1 y = 0 := by
        by_contra hyne
        exact hS y hy x₀ hx₀ ⟨hyx, p.1, linkIncidentPlaquette_of_curlInt_ne_zero hyne,
          linkIncidentPlaquette_of_curlInt_ne_zero hne⟩
      rw [hy0]
      simp
    rw [Finset.sum_eq_single_of_mem x₀ hx₀ hothers, abs_mul]
    have h1 : |((curlInt p.1 x₀ : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast abs_curlInt_le_one p.1 x₀
    have h2 := abs_sign_cast_le_one ((ρ x₀ : ℤ) : ℝ)
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- At most `6 |S|` plaquettes are shifted. -/
theorem card_plaqShift_ne_zero_le (ρ : Link B → ℤ) (S : Finset (Link B)) :
    (Finset.univ.filter fun p : {p : SourceDualTwoCells B // p ∈ Q} =>
      plaqShift (modelInc Q) (linkShift ρ S) p ≠ 0).card ≤ 6 * S.card := by
  classical
  have hsub : (Finset.univ.filter fun p : {p : SourceDualTwoCells B // p ∈ Q} =>
      plaqShift (modelInc Q) (linkShift ρ S) p ≠ 0).image Subtype.val ⊆
      S.biUnion fun x => incidentPlaquettes x := by
    intro p' hp'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨x, hx, hinc⟩ :=
      exists_incident_of_plaqShift_ne_zero Q ρ S p (Finset.mem_filter.mp hp).2
    refine Finset.mem_biUnion.mpr ⟨x, hx, ?_⟩
    unfold incidentPlaquettes
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩
  calc (Finset.univ.filter fun p : {p : SourceDualTwoCells B // p ∈ Q} =>
        plaqShift (modelInc Q) (linkShift ρ S) p ≠ 0).card
      = ((Finset.univ.filter fun p : {p : SourceDualTwoCells B // p ∈ Q} =>
        plaqShift (modelInc Q) (linkShift ρ S) p ≠ 0).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (S.biUnion fun x => incidentPlaquettes x).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ S, (incidentPlaquettes x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, 6 := Finset.sum_le_sum fun x _ => incidentPlaquetteCount_le_six x
    _ = 6 * S.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

end

end FroehlichSpencer.FS82.ZN

end
