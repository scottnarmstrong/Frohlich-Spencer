/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.L41Span

/-!
# Graph distance on the periodic square

* the minimum ℓ¹ distance between integer lifts (`squarePeriodic_dist_le_liftedL1`,
  `exists_lift_liftedL1_eq_dist`), and
* the sum of the two cyclic coordinate distances (`squarePeriodic_dist_eq_cyclicDist`).

The proof lifts every periodic edge to a unit lattice step, and projects every lattice unit step
to an edge (or a loop when `L = 1`).
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The ℓ¹ distance between two lifted lattice points. -/
def liftedL1 (p q : LiftedPoint) : ℤ := |q.1 - p.1| + |q.2 - p.2|

theorem liftedL1_nonneg (p q : LiftedPoint) : 0 ≤ liftedL1 p q :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem liftedL1_triangle (p q r : LiftedPoint) :
    liftedL1 p r ≤ liftedL1 p q + liftedL1 q r := by
  unfold liftedL1
  have h1 := abs_sub_le r.1 q.1 p.1
  have h2 := abs_sub_le r.2 q.2 p.2
  have h3 : |q.1 - p.1| = |p.1 - q.1| := abs_sub_comm _ _
  have h4 : |q.2 - p.2| = |p.2 - q.2| := abs_sub_comm _ _
  have h5 : |r.1 - q.1| = |q.1 - r.1| := abs_sub_comm _ _
  have h6 : |r.2 - q.2| = |q.2 - r.2| := abs_sub_comm _ _
  have h7 : |r.1 - p.1| = |p.1 - r.1| := abs_sub_comm _ _
  have h8 : |r.2 - p.2| = |p.2 - r.2| := abs_sub_comm _ _
  linarith

/-- A lift of a periodic vertex is congruent to it coordinatewise. -/
theorem periodicProjection_modEq (L : ℕ) (hL : 0 < L) {p : LiftedPoint}
    {x : Fin L × Fin L} (hp : periodicProjection L hL p = x) :
    p.1 ≡ (x.1.val : ℤ) [ZMOD L] ∧ p.2 ≡ (x.2.val : ℤ) [ZMOD L] := by
  subst hp
  exact ⟨periodicCoordinate_modEq L hL p.1, periodicCoordinate_modEq L hL p.2⟩

/-- Congruent lifts project to the same periodic vertex. -/
theorem periodicProjection_eq_of_modEq (L : ℕ) (hL : 0 < L) {q : LiftedPoint}
    {y : Fin L × Fin L} (h1 : q.1 ≡ (y.1.val : ℤ) [ZMOD L])
    (h2 : q.2 ≡ (y.2.val : ℤ) [ZMOD L]) : periodicProjection L hL q = y := by
  simp only [periodicProjection]
  exact Prod.ext ((periodicCoordinate_eq_of_modEq L hL _ _ h1).trans
      (periodicCoordinate_finVal L hL y.1))
    ((periodicCoordinate_eq_of_modEq L hL _ _ h2).trans (periodicCoordinate_finVal L hL y.2))

/-- Every periodic vertex has the lift given by its coordinates. -/
theorem periodicProjection_val (L : ℕ) (hL : 0 < L) (x : Fin L × Fin L) :
    periodicProjection L hL ((x.1.val : ℤ), (x.2.val : ℤ)) = x :=
  periodicProjection_eq_of_modEq L hL (Int.ModEq.refl _) (Int.ModEq.refl _)

/-- One periodic edge lifts to one lattice unit step. -/
theorem periodicAdj_lift_unit (L : ℕ) (hL : 0 < L) (x y : Fin L × Fin L)
    (hxy : (squarePeriodic L).toSimpleGraph.Adj x y) (p : LiftedPoint)
    (hp : periodicProjection L hL p = x) :
    ∃ q : LiftedPoint, periodicProjection L hL q = y ∧ liftedL1 p q ≤ 1 := by
  have hunit : periodicUnitRelation L x y :=
    periodicEdgeRelation_unit L ((periodicAdj_iff_edgeRelation L x y).mp hxy).2
  obtain ⟨hp1, hp2⟩ := periodicProjection_modEq L hL hp
  rcases hunit with (⟨heq, hstep | hstep⟩) | (⟨heq, hstep | hstep⟩)
  · refine ⟨(p.1, p.2 - 1), periodicProjection_eq_of_modEq L hL ?_ ?_, ?_⟩
    · rw [← heq]; exact hp1
    · have h := (hp2.trans hstep).add_right (-1)
      simpa [sub_eq_add_neg] using h
    · simp [liftedL1]
  · refine ⟨(p.1, p.2 + 1), periodicProjection_eq_of_modEq L hL ?_ ?_, ?_⟩
    · rw [← heq]; exact hp1
    · exact (hp2.add_right 1).trans hstep.symm
    · simp [liftedL1]
  · refine ⟨(p.1 - 1, p.2), periodicProjection_eq_of_modEq L hL ?_ ?_, ?_⟩
    · have h := (hp1.trans hstep).add_right (-1)
      simpa [sub_eq_add_neg] using h
    · rw [← heq]; exact hp2
    · simp [liftedL1]
  · refine ⟨(p.1 + 1, p.2), periodicProjection_eq_of_modEq L hL ?_ ?_, ?_⟩
    · exact (hp1.add_right 1).trans hstep.symm
    · rw [← heq]; exact hp2
    · simp [liftedL1]

/-- A periodic walk lifts to a lattice path whose ℓ¹ displacement is at most its length. -/
theorem periodicWalk_lift_liftedL1 (L : ℕ) (hL : 0 < L) {x y : Fin L × Fin L}
    (w : (squarePeriodic L).toSimpleGraph.Walk x y) :
    ∀ p : LiftedPoint, periodicProjection L hL p = x →
      ∃ q : LiftedPoint, periodicProjection L hL q = y ∧ liftedL1 p q ≤ w.length := by
  induction w with
  | nil =>
      intro p hp
      exact ⟨p, hp, by simp [liftedL1]⟩
  | cons hadj w ih =>
      intro p hp
      obtain ⟨p', hp', hstep⟩ := periodicAdj_lift_unit L hL _ _ hadj p hp
      obtain ⟨q, hq, hrest⟩ := ih p' hp'
      refine ⟨q, hq, ?_⟩
      have htri := liftedL1_triangle p p' q
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/--
Two vertices whose coordinates satisfy KP's periodic unit relation, and which are distinct,
are adjacent in the periodic square.
-/
theorem periodicAdj_of_unitRelation (L : ℕ) {x y : Fin L × Fin L}
    (h : periodicUnitRelation L x y) (hne : x ≠ y) :
    (squarePeriodic L).toSimpleGraph.Adj x y := by
  rw [periodicAdj_iff_edgeRelation]
  refine ⟨hne, ?_⟩
  have hsymm : periodicUnitRelation L y x := by
    rcases h with (⟨heq, h | h⟩) | (⟨heq, h | h⟩)
    · exact Or.inl ⟨heq.symm, Or.inr h⟩
    · exact Or.inl ⟨heq.symm, Or.inl h⟩
    · exact Or.inr ⟨heq.symm, Or.inr h⟩
    · exact Or.inr ⟨heq.symm, Or.inl h⟩
  rcases lt_trichotomy (toLex x) (toLex y) with hlt | heq | hgt
  · exact ⟨⟨(x, y), hlt, h⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact absurd (toLex.injective heq) hne
  · exact ⟨⟨(y, x), hgt, hsymm⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- A lattice unit step projects to an edge or to a single vertex. -/
theorem periodicProjection_step (L : ℕ) (hL : 0 < L) (p q : LiftedPoint)
    (hpq : (q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)) ∨
      (q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1))) :
    periodicProjection L hL p = periodicProjection L hL q ∨
      (squarePeriodic L).toSimpleGraph.Adj (periodicProjection L hL p)
        (periodicProjection L hL q) := by
  by_cases hne : periodicProjection L hL p = periodicProjection L hL q
  · exact Or.inl hne
  refine Or.inr (periodicAdj_of_unitRelation L ?_ hne)
  obtain ⟨hp1, hp2⟩ := periodicProjection_modEq L hL (x := periodicProjection L hL p) rfl
  obtain ⟨hq1, hq2⟩ := periodicProjection_modEq L hL (x := periodicProjection L hL q) rfl
  rcases hpq with (⟨h1, h2 | h2⟩) | (⟨h1, h2 | h2⟩)
  · refine Or.inl ⟨by simp only [periodicProjection, h1], Or.inr ?_⟩
    calc ((periodicProjection L hL q).2.val : ℤ) ≡ q.2 [ZMOD L] := hq2.symm
      _ = p.2 + 1 := h2
      _ ≡ ((periodicProjection L hL p).2.val : ℤ) + 1 [ZMOD L] := hp2.add_right 1
  · refine Or.inl ⟨by simp only [periodicProjection, h1], Or.inl ?_⟩
    calc ((periodicProjection L hL p).2.val : ℤ) ≡ p.2 [ZMOD L] := hp2.symm
      _ = q.2 + 1 := h2
      _ ≡ ((periodicProjection L hL q).2.val : ℤ) + 1 [ZMOD L] := hq2.add_right 1
  · refine Or.inr ⟨by simp only [periodicProjection, h1], Or.inr ?_⟩
    calc ((periodicProjection L hL q).1.val : ℤ) ≡ q.1 [ZMOD L] := hq1.symm
      _ = p.1 + 1 := h2
      _ ≡ ((periodicProjection L hL p).1.val : ℤ) + 1 [ZMOD L] := hp1.add_right 1
  · refine Or.inr ⟨by simp only [periodicProjection, h1], Or.inl ?_⟩
    calc ((periodicProjection L hL p).1.val : ℤ) ≡ p.1 [ZMOD L] := hp1.symm
      _ = q.1 + 1 := h2
      _ ≡ ((periodicProjection L hL q).1.val : ℤ) + 1 [ZMOD L] := hq1.add_right 1

/-- Lattice paths project to periodic walks: the projections of two lifts are joined by a walk
of length at most their ℓ¹ distance. -/
theorem exists_periodicWalk_length_le_liftedL1 (L : ℕ) (hL : 0 < L) :
    ∀ n : ℕ, ∀ p q : LiftedPoint, liftedL1 p q = n →
      ∃ w : (squarePeriodic L).toSimpleGraph.Walk (periodicProjection L hL p)
        (periodicProjection L hL q), w.length ≤ n := by
  intro n
  induction n with
  | zero =>
      intro p q hpq
      have h1 : q.1 = p.1 := by
        unfold liftedL1 at hpq
        have := abs_nonneg (q.1 - p.1)
        have := abs_nonneg (q.2 - p.2)
        have : |q.1 - p.1| = 0 := by omega
        simpa [sub_eq_zero] using this
      have h2 : q.2 = p.2 := by
        unfold liftedL1 at hpq
        have := abs_nonneg (q.1 - p.1)
        have := abs_nonneg (q.2 - p.2)
        have : |q.2 - p.2| = 0 := by omega
        simpa [sub_eq_zero] using this
      have hq : q = p := Prod.ext h1 h2
      subst hq
      exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | succ n ih =>
      intro p q hpq
      -- Move one step from `p` toward `q` in a coordinate where they differ.
      obtain ⟨p', hstep, hrest⟩ : ∃ p' : LiftedPoint,
          ((p'.1 = p.1 ∧ (p'.2 = p.2 + 1 ∨ p.2 = p'.2 + 1)) ∨
            (p'.2 = p.2 ∧ (p'.1 = p.1 + 1 ∨ p.1 = p'.1 + 1))) ∧ liftedL1 p' q = n := by
        unfold liftedL1 at hpq ⊢
        rcases lt_trichotomy p.1 q.1 with h | h | h
        · refine ⟨(p.1 + 1, p.2), Or.inr ⟨rfl, Or.inl rfl⟩, ?_⟩
          simp only
          rw [abs_of_pos (by omega : (0 : ℤ) < q.1 - p.1)] at hpq
          rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ q.1 - (p.1 + 1))]
          omega
        · rcases lt_trichotomy p.2 q.2 with h' | h' | h'
          · refine ⟨(p.1, p.2 + 1), Or.inl ⟨rfl, Or.inl rfl⟩, ?_⟩
            simp only
            rw [abs_of_pos (by omega : (0 : ℤ) < q.2 - p.2)] at hpq
            rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ q.2 - (p.2 + 1))]
            omega
          · rw [h, h'] at hpq
            simp at hpq
            omega
          · refine ⟨(p.1, p.2 - 1), Or.inl ⟨rfl, Or.inr (by ring)⟩, ?_⟩
            simp only
            rw [abs_of_neg (by omega : q.2 - p.2 < 0)] at hpq
            rw [abs_of_nonpos (by omega : q.2 - (p.2 - 1) ≤ 0)]
            omega
        · refine ⟨(p.1 - 1, p.2), Or.inr ⟨rfl, Or.inr (by ring)⟩, ?_⟩
          simp only
          rw [abs_of_neg (by omega : q.1 - p.1 < 0)] at hpq
          rw [abs_of_nonpos (by omega : q.1 - (p.1 - 1) ≤ 0)]
          omega
      obtain ⟨w, hw⟩ := ih p' q hrest
      rcases periodicProjection_step L hL p p' hstep with heq | hadj
      · refine ⟨w.copy heq.symm rfl, ?_⟩
        simp only [SimpleGraph.Walk.length_copy]
        omega
      · exact ⟨SimpleGraph.Walk.cons hadj w, by simp only [SimpleGraph.Walk.length_cons]; omega⟩

/-- The periodic graph distance is at most the ℓ¹ distance of any two lifts. -/
theorem squarePeriodic_dist_le_liftedL1 (L : ℕ) (hL : 0 < L) (p q : LiftedPoint) :
    ((squarePeriodic L).toSimpleGraph.dist (periodicProjection L hL p)
      (periodicProjection L hL q) : ℤ) ≤ liftedL1 p q := by
  obtain ⟨w, hw⟩ := exists_periodicWalk_length_le_liftedL1 L hL (liftedL1 p q).toNat p q
    (Int.toNat_of_nonneg (liftedL1_nonneg p q)).symm
  have hd := SimpleGraph.dist_le w
  have := Int.toNat_of_nonneg (liftedL1_nonneg p q)
  omega

/-- Two vertices of the periodic square are joined by a walk (also when `L = 1`). -/
theorem squarePeriodic_reachable (L : ℕ) (x y : Fin L × Fin L) :
    (squarePeriodic L).toSimpleGraph.Reachable x y := by
  have hL : 0 < L := Fin.pos x.1
  obtain ⟨w, -⟩ := exists_periodicWalk_length_le_liftedL1 L hL _
    ((x.1.val : ℤ), (x.2.val : ℤ)) ((y.1.val : ℤ), (y.2.val : ℤ))
    (Int.toNat_of_nonneg (liftedL1_nonneg _ _)).symm
  rw [periodicProjection_val, periodicProjection_val] at w
  exact ⟨w⟩

/-- Every lift of `x` has a lift of `y` at ℓ¹ distance exactly the periodic graph distance. -/
theorem exists_lift_liftedL1_eq_dist (L : ℕ) (hL : 0 < L) (x y : Fin L × Fin L)
    (p : LiftedPoint) (hp : periodicProjection L hL p = x) :
    ∃ q : LiftedPoint, periodicProjection L hL q = y ∧
      liftedL1 p q = (squarePeriodic L).toSimpleGraph.dist x y := by
  obtain ⟨w, hw⟩ := (squarePeriodic_reachable L x y).exists_walk_length_eq_dist
  obtain ⟨q, hq, hle⟩ := periodicWalk_lift_liftedL1 L hL w p hp
  refine ⟨q, hq, le_antisymm (hw ▸ hle) ?_⟩
  have h := squarePeriodic_dist_le_liftedL1 L hL p q
  rwa [hp, hq] at h

/-- The cyclic distance between two residues modulo `L`. -/
def cyclicDist (L : ℕ) (a b : Fin L) : ℕ :=
  min ((((b.val : ℤ) - a.val) % L).toNat) ((((a.val : ℤ) - b.val) % L).toNat)

/-- Every integer representative of `b - a` modulo `L` has absolute value at least the cyclic
distance. -/
theorem cyclicDist_le_abs (L : ℕ) (hL : 0 < L) (a b : Fin L) (t : ℤ)
    (ht : t ≡ (b.val : ℤ) - a.val [ZMOD L]) : (cyclicDist L a b : ℤ) ≤ |t| := by
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  unfold cyclicDist
  rcases le_or_gt 0 t with h | h
  · have hmod : t % L = ((b.val : ℤ) - a.val) % L := ht
    have hle : t % L ≤ t := by
      have h1 := Int.emod_add_mul_ediv t L
      have h2 : 0 ≤ (L : ℤ) * (t / L) := mul_nonneg hLz.le (Int.ediv_nonneg h hLz.le)
      linarith
    have hnn : 0 ≤ ((b.val : ℤ) - a.val) % L := Int.emod_nonneg _ hLz.ne'
    rw [abs_of_nonneg h]
    calc ((min ((((b.val : ℤ) - a.val) % L).toNat) ((((a.val : ℤ) - b.val) % L).toNat) : ℕ) : ℤ)
        ≤ ((((b.val : ℤ) - a.val) % L).toNat : ℤ) := by exact_mod_cast min_le_left _ _
      _ = ((b.val : ℤ) - a.val) % L := Int.toNat_of_nonneg hnn
      _ ≤ t := hmod ▸ hle
  · have ht' : -t ≡ (a.val : ℤ) - b.val [ZMOD L] := by
      have := ht.neg
      simpa [neg_sub] using this
    have hmod : (-t) % L = ((a.val : ℤ) - b.val) % L := ht'
    have hle : (-t) % L ≤ -t := by
      have h1 := Int.emod_add_mul_ediv (-t) L
      have h2 : 0 ≤ (L : ℤ) * ((-t) / L) :=
        mul_nonneg hLz.le (Int.ediv_nonneg (by omega) hLz.le)
      linarith
    have hnn : 0 ≤ ((a.val : ℤ) - b.val) % L := Int.emod_nonneg _ hLz.ne'
    rw [abs_of_neg h]
    calc ((min ((((b.val : ℤ) - a.val) % L).toNat) ((((a.val : ℤ) - b.val) % L).toNat) : ℕ) : ℤ)
        ≤ ((((a.val : ℤ) - b.val) % L).toNat : ℤ) := by exact_mod_cast min_le_right _ _
      _ = ((a.val : ℤ) - b.val) % L := Int.toNat_of_nonneg hnn
      _ ≤ -t := hmod ▸ hle

/-- The cyclic distance is attained by an integer representative of `b - a` modulo `L`. -/
theorem exists_abs_eq_cyclicDist (L : ℕ) (hL : 0 < L) (a b : Fin L) :
    ∃ t : ℤ, t ≡ (b.val : ℤ) - a.val [ZMOD L] ∧ |t| = cyclicDist L a b := by
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hnn1 : 0 ≤ ((b.val : ℤ) - a.val) % L := Int.emod_nonneg _ hLz.ne'
  have hnn2 : 0 ≤ ((a.val : ℤ) - b.val) % L := Int.emod_nonneg _ hLz.ne'
  unfold cyclicDist
  rcases le_total ((((b.val : ℤ) - a.val) % L).toNat) ((((a.val : ℤ) - b.val) % L).toNat)
    with h | h
  · refine ⟨((b.val : ℤ) - a.val) % L, Int.mod_modEq _ _, ?_⟩
    rw [min_eq_left h, abs_of_nonneg hnn1, Int.toNat_of_nonneg hnn1]
  · refine ⟨-(((a.val : ℤ) - b.val) % L), ?_, ?_⟩
    · have h1 : ((a.val : ℤ) - b.val) % L ≡ (a.val : ℤ) - b.val [ZMOD L] := Int.mod_modEq _ _
      have := h1.neg
      simpa [neg_sub] using this
    · rw [min_eq_right h, abs_neg, abs_of_nonneg hnn2, Int.toNat_of_nonneg hnn2]


theorem squarePeriodic_dist_eq_cyclicDist (L : ℕ) (x y : Fin L × Fin L) :
    (squarePeriodic L).toSimpleGraph.dist x y = cyclicDist L x.1 y.1 + cyclicDist L x.2 y.2 := by
  have hL : 0 < L := Fin.pos x.1
  set p : LiftedPoint := ((x.1.val : ℤ), (x.2.val : ℤ)) with hpdef
  have hp : periodicProjection L hL p = x := periodicProjection_val L hL x
  apply le_antisymm
  · obtain ⟨t₁, ht₁, ht₁'⟩ := exists_abs_eq_cyclicDist L hL x.1 y.1
    obtain ⟨t₂, ht₂, ht₂'⟩ := exists_abs_eq_cyclicDist L hL x.2 y.2
    have hq : periodicProjection L hL (p.1 + t₁, p.2 + t₂) = y := by
      apply periodicProjection_eq_of_modEq L hL
      · have := (Int.ModEq.refl (p.1)).add ht₁
        simpa [hpdef] using this
      · have := (Int.ModEq.refl (p.2)).add ht₂
        simpa [hpdef] using this
    have h := squarePeriodic_dist_le_liftedL1 L hL p (p.1 + t₁, p.2 + t₂)
    rw [hp, hq] at h
    simp only [liftedL1, add_sub_cancel_left] at h
    rw [ht₁', ht₂'] at h
    exact_mod_cast h
  · obtain ⟨q, hq, hpq⟩ := exists_lift_liftedL1_eq_dist L hL x y p hp
    obtain ⟨hq1, hq2⟩ := periodicProjection_modEq L hL hq
    have h1 := cyclicDist_le_abs L hL x.1 y.1 (q.1 - p.1)
      (Int.ModEq.sub hq1 (Int.ModEq.refl _))
    have h2 := cyclicDist_le_abs L hL x.2 y.2 (q.2 - p.2)
      (Int.ModEq.sub hq2 (Int.ModEq.refl _))
    have : ((cyclicDist L x.1 y.1 + cyclicDist L x.2 y.2 : ℕ) : ℤ) ≤
        ((squarePeriodic L).toSimpleGraph.dist x y : ℤ) := by
      rw [← hpq]
      unfold liftedL1
      push_cast
      linarith
    exact_mod_cast this

end FroehlichSpencer.BKT

end
