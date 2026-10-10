/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ParentBall

/-! # Graph diameter bounds for dyadic squares

The free-boundary bound follows by moving one coordinate at a time along the
square. The periodic target-square bound is added after the quotient path
construction is integrated. -/

@[expose] public section

namespace FroehlichSpencer.BKT

private theorem freeAdj_horizontal_succ (L : ℕ) (a b c : Fin L)
    (hab : b.val = a.val + 1) :
    (squareFree L).toSimpleGraph.Adj (a, c) (b, c) := by
  have hlex : toLex (a, c) < toLex (b, c) := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl (by simp [Fin.lt_def, hab])
  have hdx : |(a.val : ℤ) - b.val| = 1 := by
    rw [hab]
    simp
  have hdy : |(c.val : ℤ) - c.val| = 0 := by simp
  have hshape :
      ({|(a.val : ℤ) - b.val|, |(c.val : ℤ) - c.val|} : Finset ℤ) = {0, 1} := by
    simp [hdx, Finset.pair_comm]
  let e : SquareFreeEdge L := ⟨((a, c), (b, c)), hlex, hshape⟩
  apply (freeAdj_iff_edgeRelation L (a, c) (b, c)).2
  refine ⟨?_, e, Or.inl ⟨rfl, rfl⟩⟩
  intro he
  have hab' := congrArg (fun p : Fin L × Fin L => p.1.val) he
  change a.val = b.val at hab'
  omega

private theorem freeAdj_vertical_succ (L : ℕ) (a b c : Fin L)
    (hab : b.val = a.val + 1) :
    (squareFree L).toSimpleGraph.Adj (c, a) (c, b) := by
  have hlex : toLex (c, a) < toLex (c, b) := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨rfl, by simp [Fin.lt_def, hab]⟩
  have hdx : |(c.val : ℤ) - c.val| = 0 := by simp
  have hdy : |(a.val : ℤ) - b.val| = 1 := by
    rw [hab]
    simp
  have hshape :
      ({|(c.val : ℤ) - c.val|, |(a.val : ℤ) - b.val|} : Finset ℤ) = {0, 1} := by
    simp [hdy, Finset.pair_comm]
  let e : SquareFreeEdge L := ⟨((c, a), (c, b)), hlex, hshape⟩
  apply (freeAdj_iff_edgeRelation L (c, a) (c, b)).2
  refine ⟨?_, e, Or.inl ⟨rfl, rfl⟩⟩
  intro he
  have hab' := congrArg (fun p : Fin L × Fin L => p.2.val) he
  change a.val = b.val at hab'
  omega

private theorem exists_freeHorizontalWalk_aux (L : ℕ) (c : Fin L) :
    ∀ (n : ℕ) (a b : Fin L), b.val = a.val + n →
      ∃ w : (squareFree L).toSimpleGraph.Walk (a, c) (b, c), w.length = n := by
  intro n
  induction n with
  | zero =>
      intro a b hab
      have heq : a = b := Fin.ext (by omega)
      subst b
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
      intro a b hab
      let z : Fin L := ⟨a.val + 1, by omega⟩
      have hstep : (squareFree L).toSimpleGraph.Adj (a, c) (z, c) := by
        apply freeAdj_horizontal_succ
        rfl
      have htail : b.val = z.val + n := by
        dsimp [z]
        omega
      obtain ⟨tail, hlen⟩ := ih z b htail
      refine ⟨SimpleGraph.Walk.cons hstep tail, ?_⟩
      simp [hlen]

private theorem exists_freeVerticalWalk_aux (L : ℕ) (c : Fin L) :
    ∀ (n : ℕ) (a b : Fin L), b.val = a.val + n →
      ∃ w : (squareFree L).toSimpleGraph.Walk (c, a) (c, b), w.length = n := by
  intro n
  induction n with
  | zero =>
      intro a b hab
      have heq : a = b := Fin.ext (by omega)
      subst b
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
      intro a b hab
      let z : Fin L := ⟨a.val + 1, by omega⟩
      have hstep : (squareFree L).toSimpleGraph.Adj (c, a) (c, z) := by
        apply freeAdj_vertical_succ
        rfl
      have htail : b.val = z.val + n := by
        dsimp [z]
        omega
      obtain ⟨tail, hlen⟩ := ih z b htail
      refine ⟨SimpleGraph.Walk.cons hstep tail, ?_⟩
      simp [hlen]

private theorem exists_freeHorizontalWalk (L : ℕ) (a b c : Fin L) :
    ∃ w : (squareFree L).toSimpleGraph.Walk (a, c) (b, c),
      w.length = if a.val ≤ b.val then b.val - a.val else a.val - b.val := by
  by_cases hab : a.val ≤ b.val
  · simpa [hab] using exists_freeHorizontalWalk_aux L c (b.val - a.val) a b (by omega)
  · have hba : b.val ≤ a.val := by omega
    obtain ⟨w, hw⟩ := exists_freeHorizontalWalk_aux L c (a.val - b.val) b a (by omega)
    refine ⟨w.reverse, ?_⟩
    simpa [SimpleGraph.Walk.length_reverse, hba, hab] using hw

private theorem exists_freeVerticalWalk (L : ℕ) (a b c : Fin L) :
    ∃ w : (squareFree L).toSimpleGraph.Walk (c, a) (c, b),
      w.length = if a.val ≤ b.val then b.val - a.val else a.val - b.val := by
  by_cases hab : a.val ≤ b.val
  · simpa [hab] using exists_freeVerticalWalk_aux L c (b.val - a.val) a b (by omega)
  · have hba : b.val ≤ a.val := by omega
    obtain ⟨w, hw⟩ := exists_freeVerticalWalk_aux L c (a.val - b.val) b a (by omega)
    refine ⟨w.reverse, ?_⟩
    simpa [SimpleGraph.Walk.length_reverse, hba, hab] using hw

private theorem periodicUnitRelation_symm_local (L : ℕ) {x y : Fin L × Fin L}
    (h : periodicUnitRelation L x y) : periodicUnitRelation L y x := by
  rcases h with (⟨heq, h | h⟩) | (⟨heq, h | h⟩)
  · exact Or.inl ⟨heq.symm, Or.inr h⟩
  · exact Or.inl ⟨heq.symm, Or.inl h⟩
  · exact Or.inr ⟨heq.symm, Or.inr h⟩
  · exact Or.inr ⟨heq.symm, Or.inl h⟩

private theorem periodicAdj_of_unitRelation_local (L : ℕ)
    (x y : Fin L × Fin L) (hne : x ≠ y)
    (hunit : periodicUnitRelation L x y) :
    (squarePeriodic L).toSimpleGraph.Adj x y := by
  by_cases hlex : toLex x < toLex y
  · let e : SquarePeriodicEdge L := ⟨(x, y), hlex, hunit⟩
    apply (periodicAdj_iff_edgeRelation L x y).2
    exact ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩
  · have hlex' : toLex y < toLex x := by
      apply lt_of_le_of_ne (le_of_not_gt hlex)
      intro he
      exact hne (toLex.injective he.symm)
    let e : SquarePeriodicEdge L :=
      ⟨(y, x), hlex', periodicUnitRelation_symm_local L hunit⟩
    apply (periodicAdj_iff_edgeRelation L x y).2
    exact ⟨hne, e, Or.inr ⟨rfl, rfl⟩⟩

private theorem periodicAdj_horizontal_lift_succ (L : ℕ) (hL : 1 < L)
    (a : ℤ) (c : Fin L) :
    (squarePeriodic L).toSimpleGraph.Adj
      (periodicCoordinate L (by omega) a, c)
      (periodicCoordinate L (by omega) (a + 1), c) := by
  have hLpos : 0 < L := by omega
  have hadd := periodicCoordinate_add_nat L hLpos a 1
  have hne : periodicCoordinate L hLpos a ≠ periodicCoordinate L hLpos (a + 1) := by
    intro heq
    have hv := congrArg Fin.val heq
    have hadd' : (periodicCoordinate L hLpos (a + 1)).val =
        ((periodicCoordinate L hLpos a).val + 1) % L := by
      simpa using hadd
    rw [hadd'] at hv
    have hlt := (periodicCoordinate L hLpos a).isLt
    by_cases hstep : (periodicCoordinate L hLpos a).val + 1 < L
    · rw [Nat.mod_eq_of_lt hstep] at hv
      omega
    · have heqL : (periodicCoordinate L hLpos a).val + 1 = L := by omega
      rw [heqL, Nat.mod_self] at hv
      omega
  have hmodA := periodicCoordinate_modEq L hLpos a
  have hmodB := periodicCoordinate_modEq L hLpos (a + 1)
  have hmod :
      (periodicCoordinate L hLpos (a + 1)).val ≡
        (periodicCoordinate L hLpos a).val + 1 [ZMOD L] := by
    calc
      (periodicCoordinate L hLpos (a + 1)).val ≡ a + 1 [ZMOD L] := hmodB.symm
      _ ≡ (periodicCoordinate L hLpos a).val + 1 [ZMOD L] := hmodA.add_right 1
  exact periodicAdj_of_unitRelation_local L _ _ (by intro h; exact hne (congrArg Prod.fst h))
    (Or.inr ⟨rfl, Or.inr hmod⟩)

private theorem periodicAdj_vertical_lift_succ (L : ℕ) (hL : 1 < L)
    (a : ℤ) (c : Fin L) :
    (squarePeriodic L).toSimpleGraph.Adj
      (c, periodicCoordinate L (by omega) a)
      (c, periodicCoordinate L (by omega) (a + 1)) := by
  have hLpos : 0 < L := by omega
  have hadd := periodicCoordinate_add_nat L hLpos a 1
  have hne : periodicCoordinate L hLpos a ≠ periodicCoordinate L hLpos (a + 1) := by
    intro heq
    have hv := congrArg Fin.val heq
    have hadd' : (periodicCoordinate L hLpos (a + 1)).val =
        ((periodicCoordinate L hLpos a).val + 1) % L := by
      simpa using hadd
    rw [hadd'] at hv
    have hlt := (periodicCoordinate L hLpos a).isLt
    by_cases hstep : (periodicCoordinate L hLpos a).val + 1 < L
    · rw [Nat.mod_eq_of_lt hstep] at hv
      omega
    · have heqL : (periodicCoordinate L hLpos a).val + 1 = L := by omega
      rw [heqL, Nat.mod_self] at hv
      omega
  have hmodA := periodicCoordinate_modEq L hLpos a
  have hmodB := periodicCoordinate_modEq L hLpos (a + 1)
  have hmod :
      (periodicCoordinate L hLpos (a + 1)).val ≡
        (periodicCoordinate L hLpos a).val + 1 [ZMOD L] := by
    calc
      (periodicCoordinate L hLpos (a + 1)).val ≡ a + 1 [ZMOD L] := hmodB.symm
      _ ≡ (periodicCoordinate L hLpos a).val + 1 [ZMOD L] := hmodA.add_right 1
  exact periodicAdj_of_unitRelation_local L _ _ (by intro h; exact hne (congrArg Prod.snd h))
    (Or.inl ⟨rfl, Or.inr hmod⟩)

private theorem exists_periodicHorizontalWalk_aux (L : ℕ) (hL : 1 < L)
    (c : Fin L) : ∀ (n : ℕ) (a : ℤ),
      ∃ w : (squarePeriodic L).toSimpleGraph.Walk
          (periodicCoordinate L (by omega) a, c)
          (periodicCoordinate L (by omega) (a + n), c), w.length = n := by
  intro n
  induction n with
  | zero =>
      intro a
      refine ⟨(SimpleGraph.Walk.nil :
          (squarePeriodic L).toSimpleGraph.Walk
            (periodicCoordinate L (by omega) a, c)
            (periodicCoordinate L (by omega) a, c)).copy rfl (by simp), ?_⟩
      simp
  | succ n ih =>
      intro a
      let z := (periodicCoordinate L (by omega) (a + 1), c)
      have hstep : (squarePeriodic L).toSimpleGraph.Adj
          (periodicCoordinate L (by omega) a, c) z := by
        simpa [z] using periodicAdj_horizontal_lift_succ L hL a c
      obtain ⟨tail, hlen⟩ := ih (a + 1)
      have hend : (a + 1) + (n : ℤ) = a + (n + 1 : ℕ) := by
        push_cast
        ring
      let tail' := tail.copy rfl
        (congrArg (fun t : ℤ => (periodicCoordinate L (by omega) t, c)) hend)
      have hlen' : tail'.length = n := by simp [tail', hlen]
      refine ⟨SimpleGraph.Walk.cons hstep tail', ?_⟩
      simp [hlen']

private theorem exists_periodicVerticalWalk_aux (L : ℕ) (hL : 1 < L)
    (c : Fin L) : ∀ (n : ℕ) (a : ℤ),
      ∃ w : (squarePeriodic L).toSimpleGraph.Walk
          (c, periodicCoordinate L (by omega) a)
          (c, periodicCoordinate L (by omega) (a + n)), w.length = n := by
  intro n
  induction n with
  | zero =>
      intro a
      refine ⟨(SimpleGraph.Walk.nil :
          (squarePeriodic L).toSimpleGraph.Walk
            (c, periodicCoordinate L (by omega) a)
            (c, periodicCoordinate L (by omega) a)).copy rfl (by simp), ?_⟩
      simp
  | succ n ih =>
      intro a
      let z := (c, periodicCoordinate L (by omega) (a + 1))
      have hstep : (squarePeriodic L).toSimpleGraph.Adj
          (c, periodicCoordinate L (by omega) a) z := by
        simpa [z] using periodicAdj_vertical_lift_succ L hL a c
      obtain ⟨tail, hlen⟩ := ih (a + 1)
      have hend : (a + 1) + (n : ℤ) = a + (n + 1 : ℕ) := by
        push_cast
        ring
      let tail' := tail.copy rfl
        (congrArg (fun t : ℤ => (c, periodicCoordinate L (by omega) t)) hend)
      have hlen' : tail'.length = n := by simp [tail', hlen]
      refine ⟨SimpleGraph.Walk.cons hstep tail', ?_⟩
      simp [hlen']

private theorem exists_periodicHorizontalWalk (L : ℕ) (hL : 1 < L)
    (a b : ℤ) (c : Fin L) :
    ∃ w : (squarePeriodic L).toSimpleGraph.Walk
        (periodicCoordinate L (by omega) a, c) (periodicCoordinate L (by omega) b, c),
      w.length = if a ≤ b then (b - a).toNat else (a - b).toNat := by
  by_cases hab : a ≤ b
  · have hcast : ((b - a).toNat : ℤ) = b - a :=
      Int.natCast_toNat_eq_self.mpr (by omega)
    obtain ⟨w, hw⟩ := exists_periodicHorizontalWalk_aux L hL c
      (b - a).toNat a
    have hend : a + ((b - a).toNat : ℤ) = b := by omega
    let w' := w.copy rfl
      (congrArg (fun t : ℤ => (periodicCoordinate L (by omega) t, c)) hend)
    have hw' : w'.length = (b - a).toNat := by simp [w', hw]
    exact ⟨w', by simpa [hab] using hw'⟩
  · have hba : b ≤ a := by omega
    have hcast : ((a - b).toNat : ℤ) = a - b :=
      Int.natCast_toNat_eq_self.mpr (by omega)
    obtain ⟨w, hw⟩ := exists_periodicHorizontalWalk_aux L hL c
      (a - b).toNat b
    have hend : b + ((a - b).toNat : ℤ) = a := by omega
    let w₁ := w.copy rfl
      (congrArg (fun t : ℤ => (periodicCoordinate L (by omega) t, c)) hend)
    let w' := w₁.reverse
    have hw' : w'.length = (a - b).toNat := by
      simp [w', w₁, hw, SimpleGraph.Walk.length_reverse]
    exact ⟨w', by simpa [hab] using hw'⟩

private theorem exists_periodicVerticalWalk (L : ℕ) (hL : 1 < L)
    (a b : ℤ) (c : Fin L) :
    ∃ w : (squarePeriodic L).toSimpleGraph.Walk
        (c, periodicCoordinate L (by omega) a) (c, periodicCoordinate L (by omega) b),
      w.length = if a ≤ b then (b - a).toNat else (a - b).toNat := by
  by_cases hab : a ≤ b
  · have hcast : ((b - a).toNat : ℤ) = b - a :=
      Int.natCast_toNat_eq_self.mpr (by omega)
    obtain ⟨w, hw⟩ := exists_periodicVerticalWalk_aux L hL c
      (b - a).toNat a
    have hend : a + ((b - a).toNat : ℤ) = b := by omega
    let w' := w.copy rfl
      (congrArg (fun t : ℤ => (c, periodicCoordinate L (by omega) t)) hend)
    have hw' : w'.length = (b - a).toNat := by simp [w', hw]
    exact ⟨w', by simpa [hab] using hw'⟩
  · have hba : b ≤ a := by omega
    have hcast : ((a - b).toNat : ℤ) = a - b :=
      Int.natCast_toNat_eq_self.mpr (by omega)
    obtain ⟨w, hw⟩ := exists_periodicVerticalWalk_aux L hL c
      (a - b).toNat b
    have hend : b + ((a - b).toNat : ℤ) = a := by omega
    let w₁ := w.copy rfl
      (congrArg (fun t : ℤ => (c, periodicCoordinate L (by omega) t)) hend)
    let w' := w₁.reverse
    have hw' : w'.length = (a - b).toNat := by
      simp [w', w₁, hw, SimpleGraph.Walk.length_reverse]
    exact ⟨w', by simpa [hab] using hw'⟩

/-- A path in the periodic graph can follow any chosen pair of integer lifts;
its length is the sum of their coordinate displacements. -/
theorem periodicDistance_le_liftedCoordinateSum (L : ℕ) (hL : 1 < L)
    (x y : Fin L × Fin L) (p q : LiftedPoint)
    (hp : periodicProjection L (by omega) p = x)
    (hq : periodicProjection L (by omega) q = y) :
    latticeDistance .periodic L x y ≤
      (if p.1 ≤ q.1 then (q.1 - p.1).toNat else (p.1 - q.1).toNat) +
      (if p.2 ≤ q.2 then (q.2 - p.2).toNat else (p.2 - q.2).toNat) := by
  let hLpos : 0 < L := by omega
  obtain ⟨wx, hwx⟩ := exists_periodicHorizontalWalk L hL p.1 q.1
    (periodicCoordinate L hLpos p.2)
  obtain ⟨wy, hwy⟩ := exists_periodicVerticalWalk L hL p.2 q.2
    (periodicCoordinate L hLpos q.1)
  let w := wx.append wy
  have hlen : w.length = wx.length + wy.length := by simp [w]
  have hdist := SimpleGraph.dist_le w
  change latticeDistance .periodic L
    (periodicProjection L hLpos p) (periodicProjection L hLpos q) ≤ w.length at hdist
  rw [hp, hq] at hdist
  rw [hlen, hwx, hwy] at hdist
  exact hdist

/-- In the free square graph, coordinatewise monotone paths realize the
Manhattan upper bound. -/
theorem freeDistance_le_coordinateSum (L : ℕ) (x y : Fin L × Fin L) :
    latticeDistance .free L x y ≤
      (if x.1.val ≤ y.1.val then y.1.val - x.1.val else x.1.val - y.1.val) +
      (if x.2.val ≤ y.2.val then y.2.val - x.2.val else x.2.val - y.2.val) := by
  obtain ⟨wx, hwx⟩ := exists_freeHorizontalWalk L x.1 y.1 x.2
  obtain ⟨wy, hwy⟩ := exists_freeVerticalWalk L x.2 y.2 y.1
  let w := wx.append wy
  have hlen : w.length = wx.length + wy.length := by
    simp [w]
  have hdist := SimpleGraph.dist_le w
  change latticeDistance .free L x y ≤ w.length at hdist
  rw [hlen, hwx, hwy] at hdist
  exact hdist

/-- Every free-boundary square has graph diameter at most twice its side
minus one. -/
theorem free_squareDiameter_le (L k : ℕ) (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares .free L k) (hside : squareSide k ≤ L) :
    squareDiameter .free L s ≤ 2 * (squareSide k - 1) := by
  classical
  rcases Finset.mem_image.mp hs with ⟨a, -, rfl⟩
  have hmem := mem_kpSquare_free_iff L k hside a
  by_cases hprod : ((kpSquare .free L k a).product (kpSquare .free L k a)).Nonempty
  · unfold squareDiameter
    rw [dite_eq_left hprod]
    apply Finset.max'_le
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
    have hx' := (hmem p.1).1 hx
    have hy' := (hmem p.2).1 hy
    have hdx := freeDistance_le_coordinateSum L p.1 p.2
    have hbound :
        (if p.1.1.val ≤ p.2.1.val then p.2.1.val - p.1.1.val
          else p.1.1.val - p.2.1.val) ≤ squareSide k - 1 := by
      by_cases hxy : p.1.1.val ≤ p.2.1.val <;> simp [hxy] <;> omega
    have hboundY :
        (if p.1.2.val ≤ p.2.2.val then p.2.2.val - p.1.2.val
          else p.1.2.val - p.2.2.val) ≤ squareSide k - 1 := by
      by_cases hxy : p.1.2.val ≤ p.2.2.val <;> simp [hxy] <;> omega
    omega
  · unfold squareDiameter
    rw [dite_eq_right hprod]
    omega

/-- The free-square diameter bound also holds after the side exceeds the
domain, when every allowed square is the full vertex set. -/
theorem free_squareDiameter_le_all (L k : ℕ) (s : Finset (Fin L × Fin L))
    (hs : s ∈ kpSquares .free L k) :
    squareDiameter .free L s ≤ 2 * (squareSide k - 1) := by
  by_cases hside : squareSide k ≤ L
  · exact free_squareDiameter_le L k s hs hside
  · have hlarge : L < squareSide k := by omega
    rcases Finset.mem_image.mp hs with ⟨a, -, rfl⟩
    have ha : a ∈ kpSquare .free L k a := anchor_mem_kpSquare .free L k a
    have hprod :
        ((kpSquare .free L k a).product (kpSquare .free L k a)).Nonempty :=
      ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩⟩
    unfold squareDiameter
    rw [dite_eq_left hprod]
    apply Finset.max'_le
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨-, -⟩
    have hdist := freeDistance_le_coordinateSum L p.1 p.2
    have hdx :
        (if p.1.1.val ≤ p.2.1.val then p.2.1.val - p.1.1.val
          else p.1.1.val - p.2.1.val) ≤ L - 1 := by
      by_cases hxy : p.1.1.val ≤ p.2.1.val <;> simp [hxy] <;> omega
    have hdy :
        (if p.1.2.val ≤ p.2.2.val then p.2.2.val - p.1.2.val
          else p.1.2.val - p.2.2.val) ≤ L - 1 := by
      by_cases hxy : p.1.2.val ≤ p.2.2.val <;> simp [hxy] <;> omega
    have hLside : L - 1 ≤ squareSide k - 1 := by omega
    omega

private theorem periodicDistance_le_coordinateSum (L : ℕ) (hL : 1 < L)
    (x y : Fin L × Fin L) :
    latticeDistance .periodic L x y ≤
      (if x.1.val ≤ y.1.val then y.1.val - x.1.val else x.1.val - y.1.val) +
      (if x.2.val ≤ y.2.val then y.2.val - x.2.val else x.2.val - y.2.val) := by
  let p : LiftedPoint := ((x.1.val : ℤ), (x.2.val : ℤ))
  let q : LiftedPoint := ((y.1.val : ℤ), (y.2.val : ℤ))
  have hp : periodicProjection L (by omega) p = x := by
    apply Prod.ext
    · exact periodicCoordinate_finVal L (by omega) x.1
    · exact periodicCoordinate_finVal L (by omega) x.2
  have hq : periodicProjection L (by omega) q = y := by
    apply Prod.ext
    · exact periodicCoordinate_finVal L (by omega) y.1
    · exact periodicCoordinate_finVal L (by omega) y.2
  simpa [p, q] using periodicDistance_le_liftedCoordinateSum L hL
    x y p q hp hq

private def periodicOffsetLift {L : ℕ} (a : Fin L × Fin L) (i j : ℕ) : LiftedPoint :=
  (((a.1.val + i : ℕ) : ℤ), ((a.2.val + j : ℕ) : ℤ))

private theorem periodicOffsetLift_projects (L : ℕ) (hL : 0 < L)
    (a : Fin L × Fin L) (i j : ℕ) :
    periodicProjection L hL (periodicOffsetLift a i j) =
      (⟨(a.1.val + i) % L, Nat.mod_lt _ hL⟩,
       ⟨(a.2.val + j) % L, Nat.mod_lt _ hL⟩) := by
  apply Prod.ext
  · apply Fin.ext
    change (periodicCoordinate L hL ((a.1.val + i : ℕ) : ℤ)).val = _
    rw [periodicCoordinate_natCast]
  · apply Fin.ext
    change (periodicCoordinate L hL ((a.2.val + j : ℕ) : ℤ)).val = _
    rw [periodicCoordinate_natCast]

private theorem periodicOffsetCoordinate_distance_le_side
    {L : ℕ} (k : ℕ) (a : Fin L × Fin L) (i i' j j' : ℕ)
    (hi : i < squareSide k)
    (hi' : i' < squareSide k) :
    (if (periodicOffsetLift a i j).1 ≤ (periodicOffsetLift a i' j').1 then
      ((periodicOffsetLift a i' j').1 - (periodicOffsetLift a i j).1).toNat
      else ((periodicOffsetLift a i j).1 - (periodicOffsetLift a i' j').1).toNat) ≤
      squareSide k - 1 := by
  by_cases h : (periodicOffsetLift a i j).1 ≤ (periodicOffsetLift a i' j').1
  · rw [ite_eq_left h]
    simp only [periodicOffsetLift]
    have hdiff :
        ((a.1.val + i' : ℕ) : ℤ) - ((a.1.val + i : ℕ) : ℤ) =
          ((i' - i : ℕ) : ℤ) := by
      dsimp [periodicOffsetLift] at h
      omega
    rw [hdiff]
    simp
    omega
  · rw [ite_eq_right h]
    simp only [periodicOffsetLift]
    have hdiff :
        ((a.1.val + i : ℕ) : ℤ) - ((a.1.val + i' : ℕ) : ℤ) =
          ((i - i' : ℕ) : ℤ) := by
      dsimp [periodicOffsetLift] at h
      omega
    rw [hdiff]
    simp
    omega

/-- Every periodic quotient square has graph diameter at most twice its side
minus one. For a proper quotient box, lift both points using offsets from the
same statement; for a collapsed square, use their representatives in one period. -/
theorem periodic_squareDiameter_le (L k : ℕ) (hL : 1 < L)
    (s : Finset (Fin L × Fin L)) (hs : s ∈ kpSquares .periodic L k) :
    squareDiameter .periodic L s ≤ 2 * (squareSide k - 1) := by
  classical
  rcases Finset.mem_image.mp hs with ⟨a, -, rfl⟩
  have ha : a ∈ kpSquare .periodic L k a := anchor_mem_kpSquare .periodic L k a
  have hprod :
      ((kpSquare .periodic L k a).product (kpSquare .periodic L k a)).Nonempty :=
    ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩⟩
  by_cases hside : squareSide k < L
  · have hmem := mem_kpSquare_periodic_iff L k hside a
    unfold squareDiameter
    rw [dite_eq_left hprod]
    apply Finset.max'_le
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
    obtain ⟨i, hi, j, hj, hxy⟩ := (hmem p.1).1 hx
    obtain ⟨i', hi', j', hj', hxy'⟩ := (hmem p.2).1 hy
    let lp := periodicOffsetLift a i j
    let lq := periodicOffsetLift a i' j'
    have hlp : periodicProjection L (by omega) lp = p.1 := by
      rw [periodicOffsetLift_projects L (by omega) a i j]
      apply Prod.ext <;> apply Fin.ext
      · exact hxy.1.symm
      · exact hxy.2.symm
    have hlq : periodicProjection L (by omega) lq = p.2 := by
      rw [periodicOffsetLift_projects L (by omega) a i' j']
      apply Prod.ext <;> apply Fin.ext
      · exact hxy'.1.symm
      · exact hxy'.2.symm
    have hdx := periodicOffsetCoordinate_distance_le_side k a i i' j j'
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hi')
    have hdy := periodicOffsetCoordinate_distance_le_side k (a.2, a.1) j j' i i'
      (Finset.mem_range.mp hj) (Finset.mem_range.mp hj')
    have hdist := periodicDistance_le_liftedCoordinateSum L hL p.1 p.2 lp lq hlp hlq
    have hdy' :
        (if lp.2 ≤ lq.2 then (lq.2 - lp.2).toNat else (lp.2 - lq.2).toNat) ≤
          squareSide k - 1 := by
      change (if (periodicOffsetLift (a.2, a.1) j i).1 ≤
          (periodicOffsetLift (a.2, a.1) j' i').1 then
          ((periodicOffsetLift (a.2, a.1) j' i').1 -
            (periodicOffsetLift (a.2, a.1) j i).1).toNat
        else ((periodicOffsetLift (a.2, a.1) j i).1 -
            (periodicOffsetLift (a.2, a.1) j' i').1).toNat) ≤ squareSide k - 1
      exact hdy
    have hdx' :
        (if lp.1 ≤ lq.1 then (lq.1 - lp.1).toNat else (lp.1 - lq.1).toNat) ≤
          squareSide k - 1 := by
      change (if (periodicOffsetLift a i j).1 ≤
          (periodicOffsetLift a i' j').1 then
          ((periodicOffsetLift a i' j').1 - (periodicOffsetLift a i j).1).toNat
        else ((periodicOffsetLift a i j).1 - (periodicOffsetLift a i' j').1).toNat) ≤
          squareSide k - 1
      exact hdx
    calc
      latticeDistance .periodic L p.1 p.2 ≤
          (if lp.1 ≤ lq.1 then (lq.1 - lp.1).toNat else (lp.1 - lq.1).toNat) +
            (if lp.2 ≤ lq.2 then (lq.2 - lp.2).toNat else (lp.2 - lq.2).toNat) := hdist
      _ ≤ (squareSide k - 1) + (squareSide k - 1) := Nat.add_le_add hdx' hdy'
      _ = 2 * (squareSide k - 1) := by omega
  · have hcollapse : squareSide k ≥ L := Nat.le_of_not_gt hside
    have hwhole : kpSquare .periodic L k a = Finset.univ := by
      simp [kpSquare, hcollapse]
    unfold squareDiameter
    rw [dite_eq_left hprod]
    apply Finset.max'_le
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
    have hdist := periodicDistance_le_coordinateSum L (by omega) p.1 p.2
    have hdx :
        (if p.1.1.val ≤ p.2.1.val then p.2.1.val - p.1.1.val
          else p.1.1.val - p.2.1.val) ≤ L - 1 := by
      by_cases hxy : p.1.1.val ≤ p.2.1.val <;> simp [hxy] <;> omega
    have hdy :
        (if p.1.2.val ≤ p.2.2.val then p.2.2.val - p.1.2.val
          else p.1.2.val - p.2.2.val) ≤ L - 1 := by
      by_cases hxy : p.1.2.val ≤ p.2.2.val <;> simp [hxy] <;> omega
    have hLside : L - 1 ≤ squareSide k - 1 := by omega
    omega

end FroehlichSpencer.BKT

end
