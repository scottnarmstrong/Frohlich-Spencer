/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.TorusDistance
public import FroehlichSpencer.BKT.Surface.DensityDomain
public import Mathlib.Data.Set.Card

/-!
# Graph balls and density domains on the square domains

KP Claim 3.2, pp. 15–16 (Kharash–Peled, first version)
uses that a graph ball of radius `2 d` has at most `C (d + 1)²` vertices.

A graph ball of radius `R` in the free or the periodic square has at most `(2R + 1)²` vertices
(`card_latticeDistance_le_le`), because each coordinate offset lies in `[-R, R]`.

The periodic
case uses the cyclic distance formula of `Charges/TorusDistance.lean`.

Hence the KP domain
`D_j(ϱ) = {ℓ : dist (ℓ, j) < 2 d(ϱ)}` has at most `16 (d(ϱ) + 1)²` vertices in both geometries.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The cyclic distance is symmetric. -/
theorem cyclicDist_comm (L : ℕ) (a b : Fin L) : cyclicDist L a b = cyclicDist L b a := by
  unfold cyclicDist
  exact min_comm _ _

/-- Two residues with congruent representatives are equal. -/
theorem fin_eq_of_val_modEq {L : ℕ} {a b : Fin L} (h : (a.val : ℤ) ≡ b.val [ZMOD L]) :
    a = b := by
  have hL : 0 < L := Fin.pos a
  have ha := periodicCoordinate_finVal L hL a
  have hb := periodicCoordinate_finVal L hL b
  rw [← ha, ← hb]
  exact periodicCoordinate_eq_of_modEq L hL _ _ h

/-- A graph ball of radius `R` in the free or periodic square has at most `(2R + 1)²`
vertices. -/
theorem card_latticeDistance_le_le (boundary : SquareBoundary) (L R : ℕ)
    (j : Fin L × Fin L) :
    (Finset.univ.filter fun ℓ => latticeDistance boundary L ℓ j ≤ R).card ≤ (2 * R + 1) ^ 2 := by
  classical
  set B := Finset.univ.filter fun ℓ => latticeDistance boundary L ℓ j ≤ R with hB
  have hbox : ((Finset.Icc (-(R : ℤ)) R) ×ˢ (Finset.Icc (-(R : ℤ)) R)).card = (2 * R + 1) ^ 2 := by
    rw [Finset.card_product, Int.card_Icc, sq]
    congr 1 <;> omega
  have hL : 0 < L := Fin.pos j.1
  cases boundary with
  | periodic =>
      -- Offsets realizing the cyclic distance in each coordinate.
      have hex : ∀ ℓ : Fin L × Fin L, ∃ t : ℤ × ℤ,
          t.1 ≡ (ℓ.1.val : ℤ) - j.1.val [ZMOD L] ∧ |t.1| = cyclicDist L j.1 ℓ.1 ∧
          t.2 ≡ (ℓ.2.val : ℤ) - j.2.val [ZMOD L] ∧ |t.2| = cyclicDist L j.2 ℓ.2 := by
        intro ℓ
        obtain ⟨t₁, h₁, h₁'⟩ := exists_abs_eq_cyclicDist L hL j.1 ℓ.1
        obtain ⟨t₂, h₂, h₂'⟩ := exists_abs_eq_cyclicDist L hL j.2 ℓ.2
        exact ⟨(t₁, t₂), h₁, h₁', h₂, h₂'⟩
      choose f hf using hex
      rw [← hbox]
      refine Finset.card_le_card_of_injOn f (fun ℓ hℓ => ?_) ?_
      · have hℓ' : (squarePeriodic L).toSimpleGraph.dist ℓ j ≤ R := (Finset.mem_filter.mp hℓ).2
        rw [squarePeriodic_dist_eq_cyclicDist, cyclicDist_comm L ℓ.1, cyclicDist_comm L ℓ.2]
          at hℓ'
        obtain ⟨-, h1, -, h2⟩ := hf ℓ
        have a1 := abs_le.mp (show |(f ℓ).1| ≤ R by rw [h1]; exact_mod_cast (by omega))
        have a2 := abs_le.mp (show |(f ℓ).2| ≤ R by rw [h2]; exact_mod_cast (by omega))
        simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
        exact ⟨a1, a2⟩
      · intro ℓ _ ℓ' _ hff
        obtain ⟨h1, -, h2, -⟩ := hf ℓ
        obtain ⟨h1', -, h2', -⟩ := hf ℓ'
        rw [hff] at h1 h2
        have e1 : (ℓ.1.val : ℤ) ≡ ℓ'.1.val [ZMOD L] := by
          have := (h1.symm.trans h1').add_right (j.1.val : ℤ)
          simpa using this
        have e2 : (ℓ.2.val : ℤ) ≡ ℓ'.2.val [ZMOD L] := by
          have := (h2.symm.trans h2').add_right (j.2.val : ℤ)
          simpa using this
        exact Prod.ext (fin_eq_of_val_modEq e1) (fin_eq_of_val_modEq e2)
  | free =>
      by_cases hL1 : 1 < L
      · let f : Fin L × Fin L → ℤ × ℤ := fun ℓ =>
          ((ℓ.1.val : ℤ) - j.1.val, (ℓ.2.val : ℤ) - j.2.val)
        rw [← hbox]
        refine Finset.card_le_card_of_injOn f (fun ℓ hℓ => ?_) ?_
        · have hℓ' : latticeDistance .free L ℓ j ≤ R := (Finset.mem_filter.mp hℓ).2
          have hsymm : latticeDistance .free L j ℓ = latticeDistance .free L ℓ j := by
            simp only [latticeDistance]
            exact SimpleGraph.dist_comm
          obtain ⟨a1, a2, a3, a4⟩ := freeDistance_coordinate_bound L hL1 j ℓ
          rw [hsymm] at a1 a2 a3 a4
          simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc, f]
          omega
        · intro ℓ _ ℓ' _ hff
          simp only [f, Prod.mk.injEq] at hff
          exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      · have hcard : B.card ≤ 1 := by
          refine (Finset.card_le_univ B).trans ?_
          rw [Fintype.card_prod, Fintype.card_fin]
          have h1 : L ≤ 1 := by omega
          calc L * L ≤ 1 * 1 := Nat.mul_le_mul h1 h1
            _ = 1 := rfl
        exact hcard.trans (Nat.one_le_pow 2 (2 * R + 1) (by omega))

/--
: the KP domain `D_j(ϱ)` of the free square has at most
`16 (d(ϱ) + 1)²` vertices.
-/
theorem ncard_densityDomain_squareFree_le (L : ℕ) (ϱ : Fin L × Fin L → ℤ)
    (j : Fin L × Fin L) :
    ((squareFree L).densityDomain ϱ j).ncard ≤
      16 * ((squareFree L).densityDiameter ϱ + 1) ^ 2 := by
  classical
  set d := (squareFree L).densityDiameter ϱ
  have hsub : (squareFree L).densityDomain ϱ j ⊆
      ↑(Finset.univ.filter fun ℓ => latticeDistance .free L ℓ j ≤ 2 * d) := by
    intro ℓ hℓ
    have hℓ' : (squareFree L).toSimpleGraph.dist ℓ j < 2 * d := hℓ
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [latticeDistance]
    omega
  calc ((squareFree L).densityDomain ϱ j).ncard
      ≤ (↑(Finset.univ.filter fun ℓ => latticeDistance .free L ℓ j ≤ 2 * d) :
          Set (Fin L × Fin L)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.filter fun ℓ => latticeDistance .free L ℓ j ≤ 2 * d).card :=
        Set.ncard_coe_finset _
    _ ≤ (2 * (2 * d) + 1) ^ 2 := card_latticeDistance_le_le .free L (2 * d) j
    _ ≤ (4 * (d + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = 16 * (d + 1) ^ 2 := by ring

/--
: the KP domain `D_j(ϱ)` of the periodic square has at most
`16 (d(ϱ) + 1)²` vertices.
-/
theorem ncard_densityDomain_squarePeriodic_le (L : ℕ) (ϱ : Fin L × Fin L → ℤ)
    (j : Fin L × Fin L) :
    ((squarePeriodic L).densityDomain ϱ j).ncard ≤
      16 * ((squarePeriodic L).densityDiameter ϱ + 1) ^ 2 := by
  classical
  set d := (squarePeriodic L).densityDiameter ϱ
  have hsub : (squarePeriodic L).densityDomain ϱ j ⊆
      ↑(Finset.univ.filter fun ℓ => latticeDistance .periodic L ℓ j ≤ 2 * d) := by
    intro ℓ hℓ
    have hℓ' : (squarePeriodic L).toSimpleGraph.dist ℓ j < 2 * d := hℓ
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [latticeDistance]
    omega
  calc ((squarePeriodic L).densityDomain ϱ j).ncard
      ≤ (↑(Finset.univ.filter fun ℓ => latticeDistance .periodic L ℓ j ≤ 2 * d) :
          Set (Fin L × Fin L)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.filter fun ℓ => latticeDistance .periodic L ℓ j ≤ 2 * d).card :=
        Set.ncard_coe_finset _
    _ ≤ (2 * (2 * d) + 1) ^ 2 := card_latticeDistance_le_le .periodic L (2 * d) j
    _ ≤ (4 * (d + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = 16 * (d + 1) ^ 2 := by ring

end FroehlichSpencer.BKT

end
