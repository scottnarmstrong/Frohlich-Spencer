/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Transition.L1Distance

/-!
# Degree and distance in the free spin box

Every site of the free spin box is the source of at most two bonds and the target of at most two
bonds, and the two endpoints of a bond are at `ℓ¹` distance one, so the `ℓ¹` distance to a fixed
site changes by at most one along a bond.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Rotator.Transition

open FroehlichSpencer.BKT.Rotator.Ginibre

variable {L : ℕ}

theorem boxDist_self (p : RotatorSpinSite L) : boxDist p p = 0 := by
  simp [boxDist, l1Norm]

theorem boxDist_eq_zero_iff {p q : RotatorSpinSite L} : boxDist p q = 0 ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ boxDist_self p⟩
  have h2 : siteToZ p - siteToZ q = 0 := by
    unfold boxDist l1Norm at h
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    refine Prod.ext ?_ ?_ <;> simp <;> omega
  exact siteToZ_injective L (sub_eq_zero.mp h2)

theorem boxDist_src_le (e : RotatorInternalBond L) (x : RotatorSpinSite L) :
    boxDist ((rotatorFreeGraph L).src e) x ≤ boxDist ((rotatorFreeGraph L).tgt e) x + 1 := by
  rcases e with e | e <;>
    simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, boxDist, l1Norm, siteToZ] <;> simp <;> omega

theorem boxDist_tgt_le (e : RotatorInternalBond L) (x : RotatorSpinSite L) :
    boxDist ((rotatorFreeGraph L).tgt e) x ≤ boxDist ((rotatorFreeGraph L).src e) x + 1 := by
  rcases e with e | e <;>
    simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, boxDist, l1Norm, siteToZ] <;> simp <;> omega

theorem card_filter_src_eq_le (a : RotatorSpinSite L) :
    (Finset.univ.filter fun e : RotatorInternalBond L => (rotatorFreeGraph L).src e = a).card ≤ 2 := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun e : RotatorInternalBond L =>
    (rotatorFreeGraph L).src e = a) (t := (Finset.univ : Finset Bool)) (fun e => e.isLeft)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by
    intro e1 h1 e2 h2 h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h1 h2
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
      simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, Sum.isLeft_inl, Sum.isLeft_inr] at h h1 h2 <;>
      first
      | (exfalso; simp at h)
      | (have := h1.trans h2.symm
         simp only [Prod.mk.injEq, Fin.ext_iff] at this
         simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.ext_iff, Subtype.ext_iff, Fin.ext_iff]
         omega))
  simpa using h

theorem card_filter_tgt_eq_le (a : RotatorSpinSite L) :
    (Finset.univ.filter fun e : RotatorInternalBond L => (rotatorFreeGraph L).tgt e = a).card ≤ 2 := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun e : RotatorInternalBond L =>
    (rotatorFreeGraph L).tgt e = a) (t := (Finset.univ : Finset Bool)) (fun e => e.isLeft)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by
    intro e1 h1 e2 h2 h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h1 h2
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
      simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, Sum.isLeft_inl, Sum.isLeft_inr] at h h1 h2 <;>
      first
      | (exfalso; simp at h)
      | (have := h1.trans h2.symm
         simp only [Prod.mk.injEq, Fin.ext_iff] at this
         simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.ext_iff, Subtype.ext_iff, Fin.ext_iff]
         omega))
  simpa using h

theorem boxDist_boxSite {u v : ℤ × ℤ} (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
    boxDist (boxSite L u) (boxSite L v) = l1Norm (u - v) := by
  unfold boxDist
  rw [siteToZ_boxSite hu, siteToZ_boxSite hv, add_sub_add_right_eq_sub]

end FroehlichSpencer.BKT.Rotator.Transition

end
