/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.LatticeStep

/-!
# The free spin box as a square of `ℤ²`

The sites `{0, …, L}²` of `RotatorSpinSite L` are in bijection with the square `squareBoxZ L` of
`ℤ²`, and the internal bonds of `rotatorFreeGraph L` correspond exactly to the ordered pairs of the
square that are positive nearest-neighbour steps.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

/-- The coordinates of a point of the square `{0, …, L}²` are below `L + 1`. -/
theorem toNat_lt_of_mem_squareBoxZ {L : ℕ} {z : ℤ × ℤ} (h : z ∈ squareBoxZ L) :
    z.1.toNat < L + 1 ∧ z.2.toNat < L + 1 := by
  simp only [squareBoxZ, Finset.mem_product, Finset.mem_Icc] at h
  omega

theorem siteToZ_mem_squareBoxZ {L : ℕ} (p : RotatorSpinSite L) : siteToZ p ∈ squareBoxZ L := by
  simp only [squareBoxZ, siteToZ, Finset.mem_product, Finset.mem_Icc]
  have h1 := p.1.2
  have h2 := p.2.2
  omega

theorem siteToZ_injective (L : ℕ) : Function.Injective (siteToZ (L := L)) := by
  intro p q h
  simp only [siteToZ, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The free spin box and the `ℤ²` square are the same finite set of sites. -/
def squareBoxEquiv (L : ℕ) : RotatorSpinSite L ≃ ↥(squareBoxZ L) where
  toFun p := ⟨siteToZ p, siteToZ_mem_squareBoxZ p⟩
  invFun z := (⟨z.1.1.toNat, (toNat_lt_of_mem_squareBoxZ z.2).1⟩, ⟨z.1.2.toNat, (toNat_lt_of_mem_squareBoxZ z.2).2⟩)
  left_inv p := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [siteToZ]
  right_inv z := by
    have h := z.2
    simp only [squareBoxZ, Finset.mem_product, Finset.mem_Icc] at h
    refine Subtype.ext (Prod.ext ?_ ?_) <;> simp only [siteToZ] <;> omega

theorem squareBoxEquiv_apply_coe {L : ℕ} (p : RotatorSpinSite L) :
    ((squareBoxEquiv L p : ↥(squareBoxZ L)) : ℤ × ℤ) = siteToZ p := rfl

/-- Summing over the internal bonds of the free spin box is summing over the positive
nearest-neighbour ordered pairs of the `ℤ²` square. -/
theorem sum_rotatorInternalBond_eq_sum_latticeStep (L : ℕ) (g : ℤ × ℤ → ℤ × ℤ → ℝ) :
    ∑ e : RotatorInternalBond L,
        g (siteToZ ((rotatorFreeGraph L).src e)) (siteToZ ((rotatorFreeGraph L).tgt e)) =
      ∑ b : ↥(squareBoxZ L) × ↥(squareBoxZ L),
        if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then g b.1 b.2 else 0 := by
  have hcoe : ∀ (p : RotatorSpinSite L), ((squareBoxEquiv L p : ↥(squareBoxZ L)) : ℤ × ℤ) =
      siteToZ p := fun p => squareBoxEquiv_apply_coe p
  have hinj : Function.Injective (fun bond : RotatorInternalBond L =>
      (squareBoxEquiv L ((rotatorFreeGraph L).src bond),
        squareBoxEquiv L ((rotatorFreeGraph L).tgt bond))) := by
    intro b c h
    simp only [Prod.mk.injEq, Equiv.apply_eq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases b with ⟨i, j⟩ | ⟨i, j⟩ <;> rcases c with ⟨i', j'⟩ | ⟨i', j'⟩ <;>
      simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, Prod.mk.injEq, Fin.ext_iff] at h1 h2 <;>
      first
        | (exfalso; omega)
        | (simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.ext_iff, Subtype.ext_iff, Fin.ext_iff]
           omega)
  refine Fintype.sum_of_injective _ hinj _ _ ?_ ?_
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ hb
    rw [ite_eq_right_iff]
    intro hs
    exfalso
    apply hb
    unfold LatticeStep at hs
    simp only [squareBoxZ, Finset.mem_product, Finset.mem_Icc] at hx hy
    rcases hs with hs | hs
    · have hs' : y.1 = x.1 + 1 ∧ y.2 = x.2 := by simpa [Prod.ext_iff] using hs
      refine ⟨.inl (⟨⟨x.1.toNat, by omega⟩, show x.1.toNat + 1 < L + 1 by omega⟩,
        ⟨x.2.toNat, by omega⟩), ?_⟩
      simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, Prod.mk.injEq]
      refine ⟨Subtype.ext (Prod.ext ?_ ?_), Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
        simp only [hcoe, siteToZ] <;> omega
    · have hs' : y.1 = x.1 ∧ y.2 = x.2 + 1 := by simpa [Prod.ext_iff] using hs
      refine ⟨.inr (⟨x.1.toNat, by omega⟩,
        ⟨⟨x.2.toNat, by omega⟩, show x.2.toNat + 1 < L + 1 by omega⟩), ?_⟩
      simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, Prod.mk.injEq]
      refine ⟨Subtype.ext (Prod.ext ?_ ?_), Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
        simp only [hcoe, siteToZ] <;> omega
  · intro bond
    simp only [hcoe]
    split_ifs with hs
    · rfl
    exfalso
    apply hs
    rcases bond with e | e <;>
      simp only [rotatorFreeGraph, Lattice2D.squareFreeGraph, LatticeStep, siteToZ, Prod.ext_iff,
        Prod.fst_add, Prod.snd_add] <;> omega

end FroehlichSpencer.BKT.Rotator.Ginibre

end
