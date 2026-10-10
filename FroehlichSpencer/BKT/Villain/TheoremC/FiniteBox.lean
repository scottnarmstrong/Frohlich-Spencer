/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.TheoremC.GaugeFix
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox

/-! # The rooted Villain character on centered free boxes -/

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

/-- The finite Villain Gibbs law on the internal graph of a square agrees with the lattice model
on the corresponding square of `ℤ²`. -/
theorem integral_villainGraphGibbs_cos_eq_villainModel_twoPoint_squareBox
    (L : ℕ) (β : ℝ) (hβ : 0 < β) (ξ : ℤ) (a b : RotatorSpinSite L) :
    (∫ θ : RotatorSpinSite L → ℝ,
      Real.cos (ξ * (θ a - θ b))
        ∂villainGraphGibbs (rotatorFreeGraph L) β) =
      (villainModel β hβ).twoPoint ξ (squareBoxZ L) (siteToZ a) (siteToZ b) := by
  classical
  let G := rotatorFreeGraph L
  let Λ := squareBoxZ L
  let d : RotatorInternalBond L → Frequency (RotatorSpinSite L) := multigraphFrequency G
  let w : RotatorInternalBond L → ℝ → ℝ := fun _ => villainWeight β
  let d' : (Λ × Λ) → Frequency Λ := bondFrequency Λ
  let w' : (Λ × Λ) → ℝ → ℝ := (villainModel β hβ).bondWeight Λ
  have hw : ∀ e, IsBondWeight (w e) := by
    intro e
    simpa [w] using isBondWeight_villain hβ
  have hw' : ∀ e, IsBondWeight (w' e) :=
    (villainModel β hβ).isBondWeight_bondWeight Λ
  have hW (θ : Λ → ℝ) : pairWeight d' w' θ =
      pairWeight d w (θ ∘ squareBoxEquiv L) := by
    let g : ℤ × ℤ → ℤ × ℤ → ℝ := fun y z =>
      Real.log (villainWeight β (latticeAngle θ y - latticeAngle θ z))
    have hlogs :
        (∑ e : RotatorInternalBond L,
          Real.log (villainWeight β
            (θ (squareBoxEquiv L (G.src e)) - θ (squareBoxEquiv L (G.tgt e))))) =
          ∑ c : Λ × Λ,
            if LatticeStep (c.1 : ℤ × ℤ) (c.2 : ℤ × ℤ) then
              Real.log (villainWeight β (θ c.1 - θ c.2)) else 0 := by
      simpa only [g, G, latticeAngle_siteToZ, latticeAngle_coe] using
        (sum_rotatorInternalBond_eq_sum_latticeStep L g)
    have hlogGraph : Real.log (pairWeight d w (θ ∘ squareBoxEquiv L)) =
        ∑ e : RotatorInternalBond L,
          Real.log (villainWeight β
            (θ (squareBoxEquiv L (G.src e)) - θ (squareBoxEquiv L (G.tgt e)))) := by
      rw [pairWeight, Real.log_prod]
      simp only [w, d, phase_multigraphFrequency, Function.comp_apply]
      · intro e he
        rw [phase_multigraphFrequency]
        exact (VillainWeight.villainWeight_pos hβ _).ne'
    have hlogLattice : Real.log (pairWeight d' w' θ) =
        ∑ c : Λ × Λ,
          if LatticeStep (c.1 : ℤ × ℤ) (c.2 : ℤ × ℤ) then
            Real.log (villainWeight β (θ c.1 - θ c.2)) else 0 := by
      rw [pairWeight, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro c hc
        rw [phase_bondFrequency]
        dsimp [w', FreeModel.bondWeight, villainModel]
        split_ifs with hstep
        · rfl
        · simp
      · intro c hc
        rw [phase_bondFrequency]
        dsimp [w', FreeModel.bondWeight, villainModel]
        split_ifs with hstep
        · exact (VillainWeight.villainWeight_pos hβ _).ne'
        · norm_num
    have hlog : Real.log (pairWeight d w (θ ∘ squareBoxEquiv L)) =
        Real.log (pairWeight d' w' θ) := by
      rw [hlogGraph, hlogLattice]
      exact hlogs
    have hpos₁ : 0 < pairWeight d w (θ ∘ squareBoxEquiv L) :=
      pairWeight_pos hw _
    have hpos₂ : 0 < pairWeight d' w' θ := pairWeight_pos hw' _
    calc
      pairWeight d' w' θ = Real.exp (Real.log (pairWeight d' w' θ)) :=
        (Real.exp_log hpos₂).symm
      _ = Real.exp (Real.log (pairWeight d w (θ ∘ squareBoxEquiv L))) :=
        congrArg Real.exp hlog.symm
      _ = pairWeight d w (θ ∘ squareBoxEquiv L) := Real.exp_log hpos₁
  have htransfer := integral_comp_pairGibbs
    (ν := circleMeasure) (V := RotatorSpinSite L) (E := RotatorInternalBond L)
    (d := d) (w := w) circleMeasure_univ_ne_zero hw hw'
    (d' := d') (w' := w') (ι := squareBoxEquiv L) (squareBoxEquiv L).injective hW
    (f := fun θ => Real.cos (ξ * (θ a - θ b))) (by fun_prop)
  rw [show villainGraphGibbs G β = pairGibbs circleMeasure d w from rfl]
  rw [← htransfer]
  rw [FreeModel.twoPoint, FreeModel.gibbs]
  simp only [latticeAngle_siteToZ]
  change (∫ θ' : Λ → ℝ,
      Real.cos (ξ * (θ' (squareBoxEquiv L a) - θ' (squareBoxEquiv L b)))
        ∂pairGibbs circleMeasure d' w') =
    ∫ θ' : Λ → ℝ,
      Real.cos (ξ * (θ' (squareBoxEquiv L a) - θ' (squareBoxEquiv L b)))
        ∂pairGibbs circleMeasure d' w'
  rfl

/-- For distinct sites in a centered free box, the Villain two-point function is the rooted
Villain character expectation on the translated internal graph. -/
theorem villainModel_twoPoint_eq_rootedFrequency_box
    (L : ℕ) (β : ℝ) (hβ : 0 < β) (ξ : ℤ) (u v : ℤ × ℤ)
    (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) (huv : u ≠ v) :
    (villainModel β hβ).twoPoint ξ (freeBox L) u v =
      (villainFrequencyCharacterExpectation (rotatorFreeGraph (2 * L))
        (boxSite L v) β ⟨boxSite L u, by
          intro h
          apply huv
          have h' := congrArg siteToZ h
          rw [siteToZ_boxSite hv, siteToZ_boxSite hu] at h'
          exact add_right_cancel h'⟩ ξ).re := by
  let root : RotatorSpinSite (2 * L) := boxSite L v
  let site : RotatorSpinSite (2 * L) := boxSite L u
  have hgraph := integral_villainGraphGibbs_cos_eq_villainModel_twoPoint_squareBox
    (2 * L) β hβ ξ site root
  rw [integral_villainGraphGibbs_cos_eq_rootedFrequency
    (rotatorFreeGraph (2 * L)) root β hβ ⟨site, by
      intro h
      have h' := congrArg siteToZ h
      rw [siteToZ_boxSite hv, siteToZ_boxSite hu] at h'
      exact huv (add_right_cancel h')⟩ ξ] at hgraph
  have htrans : (villainModel β hβ).twoPoint ξ (freeBox L) u v =
      (villainModel β hβ).twoPoint ξ (squareBoxZ (2 * L))
        (u + ((L : ℤ), (L : ℤ))) (v + ((L : ℤ), (L : ℤ))) := by
    rw [freeBox_eq_translateDomain L]
    have hcoords (z : ℤ × ℤ) :
        z + ((L : ℤ), (L : ℤ)) + (-(L : ℤ), -(L : ℤ)) = z := by
      apply Prod.ext <;> simp
    have h := (villainModel β hβ).twoPoint_translate ξ (squareBoxZ (2 * L))
      (u + ((L : ℤ), (L : ℤ))) (v + ((L : ℤ), (L : ℤ)))
      (-(L : ℤ), -(L : ℤ))
    rw [hcoords, hcoords] at h
    exact h
  have hsite : siteToZ site = u + ((L : ℤ), (L : ℤ)) := by
    simpa [site] using (siteToZ_boxSite hu)
  have hroot : siteToZ root = v + ((L : ℤ), (L : ℤ)) := by
    simpa [root] using (siteToZ_boxSite hv)
  rw [htrans]
  simpa only [hsite, hroot] using hgraph.symm

end FroehlichSpencer.BKT.Villain.TheoremC

end
