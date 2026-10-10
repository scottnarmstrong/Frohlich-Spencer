/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawEnergy
public import FroehlichSpencer.FS82.Wilson.AreaLawRectangle

/-!
# The rectangular source has area pairing

The coordinate 1-form pairs with the oriented boundary of the rectangular
sheet by exactly the number of its plaquettes.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

 theorem wilsonRectanglePlaquette_axes {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (i : Fin L) (j : Fin T) :
    cellAxes (wilsonRectanglePlaquette hL hT i j) = {0, 1} := by
  classical
  apply Finset.ext
  intro k
  simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases k <;> simp [wilsonRectanglePlaquette, edgeCell, coordIsEdge,
    wilsonRectangleBaseCell]

theorem areaTestPlaquetteCurl_rectangle {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (i : Fin L) (j : Fin T) :
    areaTestPlaquetteCurl (⟨wilsonRectanglePlaquette hL hT i j, by
      rw [cellDegree, wilsonRectanglePlaquette_axes]
      simp
    ⟩ : PrimalPlaquettes B) = 1 := by
  rw [areaTestPlaquetteCurl_eq_axes]
  rw [wilsonRectanglePlaquette_axes]
  simp

theorem integerCellPairing_boundary_sum {B : Box 4} {ι : Type*}
    (s : Finset ι) (q : ι → Chain 4 B) (f : Cell 4 B → ℤ) :
    integerCellPairing f (boundary (∑ x ∈ s, q x)) =
      ∑ x ∈ s, integerCellPairing f (boundary (q x)) := by
  classical
  calc
    integerCellPairing f (boundary (∑ x ∈ s, q x)) =
        integerCellPairingLinear f (boundary (∑ x ∈ s, q x)) := rfl
    _ = integerCellPairingLinear f (∑ x ∈ s, boundary (q x)) := by rw [map_sum]
    _ = ∑ x ∈ s, integerCellPairingLinear f (boundary (q x)) := by rw [map_sum]
    _ = ∑ x ∈ s, integerCellPairing f (boundary (q x)) := rfl

theorem areaTestPotential_pairing_wilsonRectangleLoop {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) :
    integerCellPairing areaTestPotential (wilsonRectangleLoop L T hL hT) =
      (L * T : ℕ) := by
  classical
  rw [wilsonRectangleLoop, wilsonRectangleSheet]
  rw [integerCellPairing_boundary_sum]
  have hterm (x : Fin L × Fin T) :
      integerCellPairing areaTestPotential
        (boundary (basisChain (wilsonRectanglePlaquette hL hT x.1 x.2))) = 1 := by
    let p : PrimalPlaquettes B := ⟨wilsonRectanglePlaquette hL hT x.1 x.2, by
      rw [cellDegree, wilsonRectanglePlaquette_axes]
      simp⟩
    change areaTestPlaquetteCurl p = 1
    exact areaTestPlaquetteCurl_rectangle hL hT x.1 x.2
  simp_rw [hterm]
  simp

theorem integerCellPairing_eq_of_degreeOne_coeff_eq {B : Box 4}
    (f : Cell 4 B → ℤ) (q r : Chain 4 B)
    (hf : ∀ c, cellDegree c ≠ 1 → f c = 0)
    (hqr : ∀ c, cellDegree c = 1 → q c = r c) :
    integerCellPairing f q = integerCellPairing f r := by
  classical
  unfold integerCellPairing
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hdeg : cellDegree c = 1
  · rw [hqr c hdeg]
  · simp [hf c hdeg]

theorem integerCellPairing_boundary_plaquetteModeChain {B : Box 4}
    (f : Cell 4 B → ℤ) (m : PrimalPlaquettes B → ℤ) :
    integerCellPairing f (boundary (plaquetteModeChain m)) =
      ∑ p : PrimalPlaquettes B,
        (m p) * integerCellPairing f (boundary (basisChain p.1)) := by
  classical
  rw [plaquetteModeChain, integerCellPairing_boundary_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hsingle : Finsupp.single p.1 (m p) = (m p) • basisChain p.1 := by
    ext c
    by_cases h : c = p.1
    · subst c
      simp [basisChain]
    · simp [basisChain, h]
  rw [hsingle, map_smul, integerCellPairing_smul]

theorem areaTestPotential_pairing_boundary_eq_of_source {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) (S : Chain 4 B)
    (hsource : plaquetteModeDivergence m = primalSheetLoopFrequency S) :
    integerCellPairing areaTestPotential (boundary (plaquetteModeChain m)) =
      integerCellPairing areaTestPotential (boundary S) := by
  apply integerCellPairing_eq_of_degreeOne_coeff_eq
  · intro c hc
    simp [areaTestPotential, hc]
  · intro c hc
    let l : PrimalLinks B := ⟨c, hc⟩
    have hl := congrFun hsource l
    simpa [plaquetteModeDivergence, primalSheetLoopFrequency] using hl

theorem areaTestPotential_modePairing_eq_rectangleArea {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    ∑ p : PrimalPlaquettes B,
      (m p) * areaTestPlaquetteCurl p = (L * T : ℕ) := by
  have hpair := areaTestPotential_pairing_boundary_eq_of_source m
    (wilsonRectangleSheet L T hL hT) hsource
  rw [integerCellPairing_boundary_plaquetteModeChain] at hpair
  have hArea : integerCellPairing areaTestPotential
      (boundary (wilsonRectangleSheet L T hL hT)) = (L * T : ℕ) := by
    change integerCellPairing areaTestPotential (wilsonRectangleLoop L T hL hT) = _
    exact areaTestPotential_pairing_wilsonRectangleLoop hL hT
  rw [hArea] at hpair
  simpa [areaTestPlaquetteCurl] using hpair

theorem areaTestPotential_modeL1_lower_bound {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    (L * T : ℤ) ≤ ∑ p : PrimalPlaquettes B, |m p| := by
  classical
  have hpair := areaTestPotential_modePairing_eq_rectangleArea hL hT m hsource
  have harea_nonneg : 0 ≤ (L * T : ℤ) := by positivity
  calc
    (L * T : ℤ) =
        |∑ p : PrimalPlaquettes B, m p * areaTestPlaquetteCurl p| := by
      rw [hpair]
      simp [abs_of_nonneg harea_nonneg]
    _ ≤
        ∑ p : PrimalPlaquettes B, |m p * areaTestPlaquetteCurl p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : PrimalPlaquettes B, |m p| := by
      apply Finset.sum_le_sum
      intro p hp
      rw [areaTestPlaquetteCurl_eq_axes]
      split_ifs <;> simp

theorem areaTestPotential_modeRealL1_lower_bound {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    (L * T : ℝ) ≤ ∑ p : PrimalPlaquettes B, |(m p : ℝ)| := by
  have hInt := areaTestPotential_modeL1_lower_bound hL hT m hsource
  exact_mod_cast hInt

@[expose] noncomputable def plaquetteFieldSupport {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) : Finset (PrimalPlaquettes B) :=
  Finset.univ.filter fun p => m p ≠ 0


end FroehlichSpencer.FS82.Wilson

end
