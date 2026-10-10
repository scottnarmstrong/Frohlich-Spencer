/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.L41Span

/-! # Graph balls around source squares lie in centered expansions

These are the graph-metric inclusions in  The periodic proof lifts a
distance-realizing walk and then projects its endpoint into the centered
coordinate box. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Projecting a natural integer representative gives its residue in `Fin L`.
This spelling is useful when the centered interval begins at a nonnegative
translate of the source statement. -/
theorem periodicCoordinate_natCast (L : ℕ) (hL : 0 < L) (n : ℕ) :
    periodicCoordinate L hL (n : ℤ) = ⟨n % L, Nat.mod_lt _ hL⟩ := by
  let c : Fin L := ⟨n % L, Nat.mod_lt _ hL⟩
  have hdecomp : (n : ℤ) = (c.val : ℤ) + (L : ℤ) * (n / L) := by
    dsimp [c]
    exact_mod_cast (Nat.mod_add_div n L).symm
  rw [hdecomp, periodicCoordinate_add_period]
  exact periodicCoordinate_finVal L hL c

/-- A free graph-distance ball of radius `ancestorRadius` about an allowed
source square lies in its coordinate-clipped centered expansion. -/
theorem free_graphBall_subset_centeredExpansion
    (L : ℕ) (k : PositiveSquareScale) (j : ParentOffset) (hL : 1 < L)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares .free L k.val)
    (hside : squareSide k.val ≤ L) :
    ∀ x, (∃ y ∈ s,
        latticeDistance .free L x y ≤ ancestorRadius k j) →
      x ∈ centeredExpansion .free L k j
        (squareAnchor .free L k.val (by omega) s) := by
  intro x hx
  obtain ⟨y, hys, hdist⟩ := hx
  have hrepr := kpSquare_eq_of_squareAnchor .free L k.val (by omega) s hs
  have hy : y ∈ kpSquare .free L k.val
      (squareAnchor .free L k.val (by omega) s) := by
    rw [hrepr]
    exact hys
  have hy' := (mem_kpSquare_free_iff L k.val hside
    (squareAnchor .free L k.val (by omega) s) y).1 hy
  have hcomm : latticeDistance .free L y x = latticeDistance .free L x y := by
    change (squareFree L).toSimpleGraph.dist y x =
      (squareFree L).toSimpleGraph.dist x y
    rw [SimpleGraph.dist_comm]
  have hdistYX : latticeDistance .free L y x ≤ ancestorRadius k j := by
    rw [hcomm]
    exact hdist
  have hcoord := freeDistance_coordinate_bound L hL y x
  have hdistR : (latticeDistance .free L y x : ℤ) ≤ ancestorRadius k j := by
    exact_mod_cast hdistYX
  have hdistNeg : -(ancestorRadius k j : ℤ) ≤
      -(latticeDistance .free L y x : ℤ) := by
    omega
  have hcoordXlo : -(ancestorRadius k j : ℤ) ≤ (x.1.val : ℤ) - y.1.val :=
    hdistNeg.trans hcoord.1
  have hcoordXhi : (x.1.val : ℤ) - y.1.val ≤ ancestorRadius k j := by
    exact hcoord.2.1.trans hdistR
  have hcoordYlo : -(ancestorRadius k j : ℤ) ≤ (x.2.val : ℤ) - y.2.val :=
    hdistNeg.trans hcoord.2.2.1
  have hcoordYhi : (x.2.val : ℤ) - y.2.val ≤ ancestorRadius k j := by
    exact hcoord.2.2.2.trans hdistR
  simp only [centeredExpansion, Finset.mem_filter, Finset.mem_univ, true_and]
  change (squareAnchor .free L k.val (by omega) s).1.val ≤
      x.1.val + ancestorRadius k j ∧
    x.1.val < (squareAnchor .free L k.val (by omega) s).1.val +
      squareSide k.val + ancestorRadius k j ∧
    (squareAnchor .free L k.val (by omega) s).2.val ≤
      x.2.val + ancestorRadius k j ∧
    x.2.val < (squareAnchor .free L k.val (by omega) s).2.val +
      squareSide k.val + ancestorRadius k j
  omega

/-- The periodic graph-distance ball around an allowed source square lies in
its quotient centered expansion. The square is lifted with a chosen statement,
the shortest path is lifted from that source point, and the signed endpoint
displacement gives a coordinate in the expanded interval. -/
theorem periodic_graphBall_subset_centeredExpansion
    (L : ℕ) (k : PositiveSquareScale) (j : ParentOffset) (hL : 1 < L)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares .periodic L k.val)
    (_hside : squareSide k.val ≤ L) :
    ∀ x, (∃ y ∈ s,
        latticeDistance .periodic L x y ≤ ancestorRadius k j) →
      x ∈ centeredExpansion .periodic L k j
        (squareAnchor .periodic L k.val (by omega) s) := by
  intro x hx
  obtain ⟨y, hys, hdist⟩ := hx
  let hLpos : 0 < L := by omega
  let a := squareAnchor .periodic L k.val hLpos s
  have hrepr : kpSquare .periodic L k.val a = s :=
    kpSquare_eq_of_squareAnchor .periodic L k.val hLpos s hs
  have hy : y ∈ kpSquare .periodic L k.val a := by
    rw [hrepr]
    exact hys
  have hqside : ancestorSide k j = squareSide k.val + 2 * ancestorRadius k j :=
    ancestorSide_eq k j
  by_cases hq : L ≤ ancestorSide k j
  · simp [centeredExpansion, hq]
  · have hqLt : ancestorSide k j < L := Nat.lt_of_not_ge hq
    have hrpos : 0 < ancestorRadius k j := by
      dsimp [ancestorRadius]
      have hjpow : 2 ≤ 2 ^ j.val := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j.val := Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    have hsourceLt : squareSide k.val < L := by
      rw [hqside] at hqLt
      omega
    let aLift : LiftedPoint :=
      (((a.1.val + L : ℕ) : ℤ), ((a.2.val + L : ℕ) : ℤ))
    have haProj : periodicProjection L hLpos aLift = a := by
      apply Prod.ext
      · have hsum : ((a.1.val + L : ℕ) : ℤ) =
            (a.1.val : ℤ) + (L : ℤ) := by norm_cast
        change periodicCoordinate L hLpos ((a.1.val + L : ℕ) : ℤ) = a.1
        rw [hsum]
        rw [show (a.1.val : ℤ) + (L : ℤ) =
          (a.1.val : ℤ) + (L : ℤ) * 1 by ring]
        rw [periodicCoordinate_add_period]
        exact periodicCoordinate_finVal L hLpos a.1
      · have hsum : ((a.2.val + L : ℕ) : ℤ) =
            (a.2.val : ℤ) + (L : ℤ) := by norm_cast
        change periodicCoordinate L hLpos ((a.2.val + L : ℕ) : ℤ) = a.2
        rw [hsum]
        rw [show (a.2.val : ℤ) + (L : ℤ) =
          (a.2.val : ℤ) + (L : ℤ) * 1 by ring]
        rw [periodicCoordinate_add_period]
        exact periodicCoordinate_finVal L hLpos a.2
    have hy' : y ∈ kpSquare .periodic L k.val
        (periodicProjection L hLpos aLift) := by
      rw [haProj]
      exact hy
    obtain ⟨p, hpBox, hpProj⟩ := periodicSquare_exists_lifted_witness
      L k.val hLpos hsourceLt aLift y hy'
    let d := latticeDistance .periodic L y x
    have hcomm : latticeDistance .periodic L x y = d := by
      change (squarePeriodic L).toSimpleGraph.dist x y =
        (squarePeriodic L).toSimpleGraph.dist y x
      rw [SimpleGraph.dist_comm]
    have hdist' : d ≤ ancestorRadius k j := by
      rw [← hcomm]
      exact hdist
    have hR : d < ancestorRadius k j + 1 := by omega
    obtain ⟨q, hqProj, hxlo, hxhi, hylo, hyhi, -, -, -, -⟩ :=
      periodicDistance_exists_lift L (ancestorRadius k j + 1) hL y x p hpProj hR
    have hpBox' : p ∈ liftedSquare (squareSide k.val) aLift := hpBox
    change aLift.1 ≤ p.1 ∧ p.1 ≤ aLift.1 + (squareSide k.val : ℤ) - 1 ∧
      aLift.2 ≤ p.2 ∧ p.2 ≤ aLift.2 + (squareSide k.val : ℤ) - 1 at hpBox'
    dsimp [aLift] at hpBox'
    have hleftX : ((a.1.val + L : ℕ) : ℤ) - ancestorRadius k j ≤ q.1 := by
      omega
    have hrightX : q.1 ≤ ((a.1.val + L : ℕ) : ℤ) + squareSide k.val - 1 +
        ancestorRadius k j := by
      omega
    have hleftY : ((a.2.val + L : ℕ) : ℤ) - ancestorRadius k j ≤ q.2 := by
      omega
    have hrightY : q.2 ≤ ((a.2.val + L : ℕ) : ℤ) + squareSide k.val - 1 +
        ancestorRadius k j := by
      omega
    let lowerX : ℕ := a.1.val + L - ancestorRadius k j
    let lowerY : ℕ := a.2.val + L - ancestorRadius k j
    have hlowerX : ((lowerX : ℕ) : ℤ) =
        ((a.1.val + L : ℕ) : ℤ) - ancestorRadius k j := by
      dsimp [lowerX]
      have hle : ancestorRadius k j ≤ a.1.val + L := by
        have hrLt : ancestorRadius k j < L := by omega
        omega
      norm_cast
    have hlowerY : ((lowerY : ℕ) : ℤ) =
        ((a.2.val + L : ℕ) : ℤ) - ancestorRadius k j := by
      dsimp [lowerY]
      have hrLt : ancestorRadius k j < L := by omega
      have hle : ancestorRadius k j ≤ a.2.val + L := by omega
      norm_cast
    let ix := (q.1 - (lowerX : ℤ)).toNat
    let iy := (q.2 - (lowerY : ℤ)).toNat
    have hixCast : (ix : ℤ) = q.1 - (lowerX : ℤ) := by
      dsimp [ix]
      exact Int.natCast_toNat_eq_self.mpr (by omega)
    have hiyCast : (iy : ℤ) = q.2 - (lowerY : ℤ) := by
      dsimp [iy]
      exact Int.natCast_toNat_eq_self.mpr (by omega)
    have hixLt : ix < ancestorSide k j := by
      rw [hqside]
      have hix : (ix : ℤ) <
          squareSide k.val + 2 * ancestorRadius k j := by
        rw [hixCast]
        rw [hlowerX]
        omega
      exact_mod_cast hix
    have hiyLt : iy < ancestorSide k j := by
      rw [hqside]
      have hiy : (iy : ℤ) <
          squareSide k.val + 2 * ancestorRadius k j := by
        rw [hiyCast]
        rw [hlowerY]
        omega
      exact_mod_cast hiy
    have hprojX : x.1.val =
        ((a.1.val + L - ancestorRadius k j) % L + ix) % L := by
      have hpX : (periodicProjection L hLpos q).1 = x.1 := congrArg Prod.fst hqProj
      have hpXval :
          (periodicCoordinate L hLpos q.1).val = x.1.val := by
        exact congrArg Fin.val hpX
      have hstart : periodicCoordinate L hLpos (lowerX : ℤ) =
          ⟨(a.1.val + L - ancestorRadius k j) % L, by
            apply Nat.mod_lt
            exact hLpos⟩ := by
        apply Fin.ext
        calc
          (periodicCoordinate L hLpos (lowerX : ℤ)).val = lowerX % L := by
            exact congrArg Fin.val (periodicCoordinate_natCast L hLpos lowerX)
          _ = (a.1.val + L - ancestorRadius k j) % L := rfl
      have hadd := periodicCoordinate_add_nat L hLpos
        (lowerX : ℤ) ix
      have hsum : (lowerX : ℤ) + (ix : ℤ) = q.1 := by
        rw [hixCast]
        omega
      rw [hsum, hstart] at hadd
      exact hpXval.symm.trans hadd
    have hprojY : x.2.val =
        ((a.2.val + L - ancestorRadius k j) % L + iy) % L := by
      have hpY : (periodicProjection L hLpos q).2 = x.2 := congrArg Prod.snd hqProj
      have hpYval :
          (periodicCoordinate L hLpos q.2).val = x.2.val := by
        exact congrArg Fin.val hpY
      have hstart : periodicCoordinate L hLpos (lowerY : ℤ) =
          ⟨(a.2.val + L - ancestorRadius k j) % L, by
            apply Nat.mod_lt
            exact hLpos⟩ := by
        apply Fin.ext
        calc
          (periodicCoordinate L hLpos (lowerY : ℤ)).val = lowerY % L := by
            exact congrArg Fin.val (periodicCoordinate_natCast L hLpos lowerY)
          _ = (a.2.val + L - ancestorRadius k j) % L := rfl
      have hadd := periodicCoordinate_add_nat L hLpos
        (lowerY : ℤ) iy
      have hsum : (lowerY : ℤ) + (iy : ℤ) = q.2 := by
        rw [hiyCast]
        omega
      rw [hsum, hstart] at hadd
      exact hpYval.symm.trans hadd
    have hmem : x ∈ (Finset.univ.filter fun z : Fin L × Fin L =>
        ∃ i ∈ Finset.range (ancestorSide k j),
          ∃ m ∈ Finset.range (ancestorSide k j),
            z.1.val = ((a.1.val + L - ancestorRadius k j) % L + i) % L ∧
            z.2.val = ((a.2.val + L - ancestorRadius k j) % L + m) % L) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ix, Finset.mem_range.mpr hixLt, iy,
        Finset.mem_range.mpr hiyLt, hprojX, hprojY⟩
    simpa [centeredExpansion, a, hq] using hmem

/-- The explicit free parent contains the graph-distance neighborhood used in
, since it contains the clipped centered expansion. -/
theorem free_graphBall_subset_ancestorParent
    (L : ℕ) (k : PositiveSquareScale) (j : ParentOffset)
    (hL : 0 < L) (hLlarge : 1 < L)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares .free L k.val)
    (hside : squareSide k.val ≤ L) :
    ∀ x, (∃ y ∈ s, latticeDistance .free L x y ≤ ancestorRadius k j) →
      x ∈ ancestorParent .free L k j hL s := by
  intro x hx
  have hcenter : x ∈ centeredExpansion .free L k j
      (squareAnchor .free L k.val hL s) := by
    exact free_graphBall_subset_centeredExpansion L k j hLlarge s hs hside x hx
  exact centeredExpansion_subset_ancestorParent .free L k j hL s hcenter

/-- The explicit periodic parent contains the graph-distance neighborhood
used in the cover construction, by the periodic coordinate-lift inclusion. -/
theorem periodic_graphBall_subset_ancestorParent
    (L : ℕ) (k : PositiveSquareScale) (j : ParentOffset)
    (hL : 0 < L) (hLlarge : 1 < L)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares .periodic L k.val)
    (hside : squareSide k.val ≤ L) :
    ∀ x, (∃ y ∈ s, latticeDistance .periodic L x y ≤ ancestorRadius k j) →
      x ∈ ancestorParent .periodic L k j hL s := by
  intro x hx
  have hcenter : x ∈ centeredExpansion .periodic L k j
      (squareAnchor .periodic L k.val hL s) := by
    exact periodic_graphBall_subset_centeredExpansion L k j hLlarge s hs hside x hx
  exact centeredExpansion_subset_ancestorParent .periodic L k j hL s hcenter

end FroehlichSpencer.BKT

end
