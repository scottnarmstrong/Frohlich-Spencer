/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.SelectedLinkSelection
public import FroehlichSpencer.FS82.Currents.SourceLinkColoring
public import FroehlichSpencer.FS82.Currents.Current
public import FroehlichSpencer.FS82.Gaussian.SelectedLinkActivity

/-!
# Eight-class selection for a finite source current

The cubical coloring is plaquette-independent. Choosing its largest-mass
class yields the selected links and the source's one-eighteenth capture bound.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Currents.SelectedCurrentLinks

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Currents.SourceLinkColoring

variable {B : SourceBox}

/-- The coefficient of a source current with its physical `2π` normalization. -/
noncomputable def physicalLinkCoefficient (j : IntegerCurrent B) (e : SourceDualOneCells B) : ℝ :=
  (2 * Real.pi) * (j e : ℝ)

/-- The squared physical current mass at one link. -/
noncomputable def physicalLinkMass (j : IntegerCurrent B) (e : SourceDualOneCells B) : ℝ :=
  (physicalLinkCoefficient j e) ^ 2

/-- Select a direction-parity class carrying at least one eighteenth of the
squared physical current mass. Distinct selected links share no source plaquette. -/
theorem selectedCurrentLinks (j : IntegerCurrent B) :
    ∃ c : Fin 8,
      (∑ e ∈ j.support, physicalLinkMass j e) / 18 ≤
          classMass j.support linkColor (physicalLinkMass j) c ∧
      ∀ e ∈ colorClass j.support linkColor c,
        ∀ f ∈ colorClass j.support linkColor c,
          ¬ (e ≠ f ∧ ∃ p : SourceDualTwoCells B,
            linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) := by
  have hcolor : ∀ ⦃e f : SourceDualOneCells B⦄,
      (e ≠ f ∧ ∃ p : SourceDualTwoCells B,
        linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) →
      linkColor e ≠ linkColor f := by
    intro e f h
    exact linkColor_ne_of_sharedPlaquette h.1 h.2
  obtain ⟨c, hmass, hconflict⟩ := selectedClass_noConflict
    j.support linkColor (physicalLinkMass j) _ hcolor
  have htotal : 0 ≤ ∑ e ∈ j.support, physicalLinkMass j e := by
    apply Finset.sum_nonneg
    intro e he
    exact sq_nonneg (physicalLinkCoefficient j e)
  refine ⟨c, ?_, hconflict⟩
  calc
    (∑ e ∈ j.support, physicalLinkMass j e) / 18 ≤
        (∑ e ∈ j.support, physicalLinkMass j e) / 8 := by
          nlinarith
    _ ≤ classMass j.support linkColor (physicalLinkMass j) c := hmass


/-- The source activity exponent follows from the chosen current class once
its actual incident-plaquette counts are supplied. -/
theorem selectedCurrentActivity_le_one216 (j : IntegerCurrent B)
    (β K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K) :
    ∃ c : Fin 8,
      K * Real.exp (-((β / 2) *
        ∑ e ∈ colorClass j.support linkColor c,
          physicalLinkCoefficient j e ^ 2 /
            (incidentPlaquetteCount e : ℝ))) ≤
        K * Real.exp (-((β / 216) *
          ∑ e ∈ j.support, physicalLinkCoefficient j e ^ 2)) := by
  let n : SourceDualOneCells B → ℕ := incidentPlaquetteCount
  have hnpos : ∀ e, 0 < n e := by
    intro e
    have h := incidentPlaquetteCount_bounds e
    dsimp [n]
    omega
  have hnle : ∀ e, n e ≤ 6 := by
    intro e
    exact (incidentPlaquetteCount_bounds e).2
  obtain ⟨c, hcapture, _⟩ := selectedCurrentLinks j
  refine ⟨c, ?_⟩
  have hnposT : ∀ e ∈ colorClass j.support linkColor c, 0 < n e := by
    intro e he
    exact hnpos e
  have hnleT : ∀ e ∈ colorClass j.support linkColor c, n e ≤ 6 := by
    intro e he
    exact hnle e
  have hcapture' :
      (∑ e ∈ j.support, physicalLinkCoefficient j e ^ 2) / 18 ≤
        ∑ e ∈ colorClass j.support linkColor c,
          physicalLinkCoefficient j e ^ 2 := by
    simpa [physicalLinkMass, classMass] using hcapture
  apply FroehlichSpencer.FS82.Gaussian.SelectedLinkActivity.renormalizedActivity_le_one216
    j.support (colorClass j.support linkColor c) β K
    (physicalLinkCoefficient j) n hβ hK
    (Finset.filter_subset _ _) hnposT hnleT hcapture'


end FroehlichSpencer.FS82.Currents.SelectedCurrentLinks

end
