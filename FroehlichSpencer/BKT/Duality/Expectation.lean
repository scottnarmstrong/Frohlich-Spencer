/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Duality.HeightCorrespondence
public import FroehlichSpencer.BKT.Gaussian.IntegerField
public import FroehlichSpencer.BKT.Villain.CosineExpectation

/-!
# Villain current sums as integer-height sums

This module begins the normalization-controlled Villain/IGFF comparison in KP Proposition 6.1,
§6.1, pp. 32–34. The current-height bijections are supplied by
`Duality/HeightCorrespondence.lean`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Duality

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain

variable {L : ℕ}

/-- The dual face pinned at the lower-left corner of the free square. -/
abbrev dualBoxRoot (L : ℕ) : SquareFreeVertex (L + 1) := (0, 0)

/-- Integer heights on the dual box pinned at its lower-left face. -/
abbrev PinnedDualHeight (L : ℕ) :=
  pinnedIntegerField (SquareFreeVertex (L + 1)) (dualBoxRoot L)

/-- Neutral currents on the wired primal box. -/
abbrev NeutralWiredCurrent (L : ℕ) :=
  {q : WiredEdge L → ℤ // neutralAwayFrom (wiredBoxGraph L) none q}

/-- Unit-source currents on the wired primal box at a selected free site. -/
abbrev SourceWiredCurrent (L : ℕ) (site : SquareFreeVertex L) :=
  {q : WiredEdge L → ℤ // characterCurrent (wiredBoxGraph L) none (some site) q}

/-- Change the pinned root of an integer field by subtracting its value at the new root. -/
def pinnedIntegerFieldRebase {V : Type*} (r s : V) :
    pinnedIntegerField V r ≃ pinnedIntegerField V s where
  toFun m := ⟨fun j => m.1 j - m.1 s, by simp⟩
  invFun m := ⟨fun j => m.1 j - m.1 r, by simp⟩
  left_inv := by
    intro m
    apply Subtype.ext
    funext j
    change (m.1 j - m.1 s) - (m.1 r - m.1 s) = m.1 j
    rw [m.2]
    ring
  right_inv := by
    intro m
    apply Subtype.ext
    funext j
    change (m.1 j - m.1 r) - (m.1 s - m.1 r) = m.1 j
    rw [m.2]
    ring

/-- Pointwise formula for rebasing a pinned integer field. -/
@[simp] theorem pinnedIntegerFieldRebase_apply {V : Type*} (r s : V)
    (m : pinnedIntegerField V r) (j : V) :
    (pinnedIntegerFieldRebase r s m).1 j = m.1 j - m.1 s := rfl

/-- Rebasing a pinned height by a constant preserves every edge difference and hence its IGFF
weight. -/
theorem igffWeight_rebase_eq {V E : Type*} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (β : ℝ) (r s : V) (m : pinnedIntegerField V r) :
    igffWeight G β (pinnedIntegerFieldRebase r s m) = igffWeight G β m := by
  have henergy : G.energy (fun j => ((pinnedIntegerFieldRebase r s m).1 j : ℝ)) =
      G.energy (fun j => (m.1 j : ℝ)) := by
    unfold Multigraph.energy Multigraph.grad
    apply Finset.sum_congr rfl
    intro e he
    simp only [pinnedIntegerFieldRebase]
    change (((m.1 (G.src e) - m.1 s : ℤ) : ℝ) -
          ((m.1 (G.tgt e) - m.1 s : ℤ) : ℝ)) ^ 2 = _
    push_cast
    ring
  unfold igffWeight
  rw [henergy]

/-- The rooted IGFF expectation is independent of the chosen pinning vertex whenever the
observable is invariant under adding a constant. -/
theorem igffExpectation_rebase_eq {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (r s : V) (F : pinnedIntegerField V r → ℝ) (F' : pinnedIntegerField V s → ℝ)
    (hF : ∀ m, F m = F' (pinnedIntegerFieldRebase r s m)) :
    igffExpectation G hG β hβ r F = igffExpectation G hG β hβ s F' := by
  let e := pinnedIntegerFieldRebase r s
  have hnum : (∑' m, F m * igffWeight G β m) =
      ∑' m, F' m * igffWeight G β m := by
    calc
      (∑' m, F m * igffWeight G β m) =
          ∑' m, F' (e m) * igffWeight G β (e m) := by
        apply tsum_congr
        intro m
        calc
          F m * igffWeight G β m = F' (e m) * igffWeight G β m := by rw [hF]
          _ = F' (e m) * igffWeight G β (e m) := by
            rw [igffWeight_rebase_eq]
      _ = ∑' m, F' m * igffWeight G β m :=
        Equiv.tsum_eq e (fun m : pinnedIntegerField V s => F' m * igffWeight G β m)
  have hZ : igffPartitionFunction G β r = igffPartitionFunction G β s := by
    unfold igffPartitionFunction
    calc
      (∑' m, igffWeight G β m) = ∑' m, igffWeight G β (e m) := by
        apply tsum_congr
        intro m
        exact (igffWeight_rebase_eq G β r s m).symm
      _ = ∑' m, igffWeight G β m :=
        Equiv.tsum_eq e (fun m : pinnedIntegerField V s => igffWeight G β m)
  unfold igffExpectation
  rw [hnum, hZ]

/-- A pinned height is determined by its oriented edge increments. -/
private theorem pinnedHeight_eq_of_dualHeightGradient_eq
    (m n : PinnedDualHeight L)
    (hgrad : dualHeightGradient m.1 = dualHeightGradient n.1) : m = n := by
  apply Subtype.ext
  funext p
  have hp := congrArg (fun r : WiredEdge L → ℤ => heightPotential r p) hgrad
  rw [heightPotential_dualHeightGradient, heightPotential_dualHeightGradient] at hp
  have hm : m.1 (0, 0) = 0 := by simpa [dualBoxRoot] using m.2
  have hn : n.1 (0, 0) = 0 := by simpa [dualBoxRoot] using n.2
  rw [hm, hn] at hp
  simpa using hp

/-- Send a pinned dual height to its neutral wired current. -/
def neutralHeightCurrentMap (m : PinnedDualHeight L) : NeutralWiredCurrent L :=
  ⟨dualHeightGradient m.1, (wiredNeutral_iff_dualCurl_zero _).2
    (dualCurl_dualHeightGradient m.1)⟩

/-- The neutral-current/height map is a bijection. -/
theorem neutralHeightCurrentMap_bijective :
    Function.Bijective (neutralHeightCurrentMap (L := L)) := by
  constructor
  · intro m n h
    apply pinnedHeight_eq_of_dualHeightGradient_eq m n (congrArg Subtype.val h)
  · intro q
    rcases (wiredNeutral_iff_existsUnique_pinnedHeight q.1).mp q.2 with
      ⟨m, hm, _⟩
    refine ⟨⟨m, hm.1⟩, ?_⟩
    apply Subtype.ext
    exact hm.2

/-- The neutral wired current lattice and the pinned dual-height lattice are equivalent. -/
noncomputable def neutralCurrentHeightEquiv : PinnedDualHeight L ≃ NeutralWiredCurrent L :=
  Equiv.ofBijective (neutralHeightCurrentMap (L := L)) neutralHeightCurrentMap_bijective

/-- Send a pinned dual height in KP's sign convention to its unit-source current. -/
def sourceHeightCurrentMap (site : SquareFreeVertex L) (m : PinnedDualHeight L) :
    SourceWiredCurrent L site :=
  ⟨unitSourceKPHeightCurrent site m.1,
    unitSourceKPHeightCurrent_characterCurrent site m.1⟩

/-- The unit-source current/height map is a bijection. -/
theorem sourceHeightCurrentMap_bijective (site : SquareFreeVertex L) :
    Function.Bijective (sourceHeightCurrentMap (L := L) site) := by
  constructor
  · intro m n h
    apply pinnedHeight_eq_of_dualHeightGradient_eq m n
    have hq : unitSourceKPHeightCurrent site m.1 = unitSourceKPHeightCurrent site n.1 := by
      simpa [sourceHeightCurrentMap] using congrArg Subtype.val h
    funext e
    have he := congrFun hq e
    dsimp [unitSourceKPHeightCurrent] at he
    omega
  · intro q
    rcases (wiredCharacterCurrent_iff_existsUnique_pinnedKPHeight q.1 site).mp q.2 with
      ⟨m, hm, _⟩
    refine ⟨⟨m, hm.1⟩, ?_⟩
    apply Subtype.ext
    exact hm.2.symm

/-- The source-current lattice and the pinned dual-height lattice are equivalent. -/
noncomputable def sourceCurrentHeightEquiv (site : SquareFreeVertex L) :
    PinnedDualHeight L ≃ SourceWiredCurrent L site :=
  Equiv.ofBijective (sourceHeightCurrentMap (L := L) site)
    (sourceHeightCurrentMap_bijective (L := L) site)

/-- A Gaussian sum restricted by a predicate is the same sum over its subtype. -/
private theorem tsum_if_eq_subtype {α : Type*} (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) :
    (∑' a, if P a then f a else 0) = ∑' a : {a // P a}, f a.1 := by
  classical
  calc
    (∑' a, if P a then f a else 0) =
        ∑' a, ({a | P a} : Set α).indicator f a := by
      apply tsum_congr
      intro a
      by_cases ha : P a <;> simp [Set.indicator, ha]
    _ = ∑' a : {a // P a}, f a.1 :=
      (tsum_subtype {a | P a} f).symm

/-- The Villain Gaussian weight of a neutral current is exactly the rooted dual IGFF weight. -/
theorem currentGaussianWeight_dualHeightGradient_eq_igffWeight (β : ℝ)
    (m : PinnedDualHeight L) :
    currentGaussianWeight β (dualHeightGradient m.1) =
      igffWeight (dualBoxGraph L) (1 / β) m := by
  classical
  unfold currentGaussianWeight igffWeight
  rw [← Real.exp_sum]
  apply congrArg Real.exp
  unfold Multigraph.energy Multigraph.grad
  calc
    (∑ e, -((dualHeightGradient m.1 e : ℝ) ^ 2) / (2 * β)) =
        ∑ e, (-(1 / β / 2)) *
          ((m.1 ((dualBoxGraph L).src e) : ℝ) -
            (m.1 ((dualBoxGraph L).tgt e) : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro e he
      dsimp [dualHeightGradient]
      push_cast
      ring
    _ = -(1 / β / 2) * ∑ e,
          ((m.1 ((dualBoxGraph L).src e) : ℝ) -
            (m.1 ((dualBoxGraph L).tgt e) : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]

/-- The neutral Villain current partition sum is the rooted dual IGFF partition function. -/
theorem neutralCurrent_tsum_eq_igffPartitionFunction (β : ℝ) :
    (∑' q : WiredEdge L → ℤ,
      neutralCurrentGaussianWeight (wiredBoxGraph L) none β q) =
      igffPartitionFunction (dualBoxGraph L) (1 / β) (dualBoxRoot L) := by
  classical
  unfold neutralCurrentGaussianWeight
  rw [tsum_if_eq_subtype]
  let e := neutralCurrentHeightEquiv (L := L)
  change
    (∑' q : NeutralWiredCurrent L, currentGaussianWeight β q.1) = _
  calc
    (∑' q : NeutralWiredCurrent L, currentGaussianWeight β q.1) =
        ∑' m : PinnedDualHeight L, currentGaussianWeight β (e m).1 :=
      (Equiv.tsum_eq e (fun q : NeutralWiredCurrent L => currentGaussianWeight β q.1)).symm
    _ = igffPartitionFunction (dualBoxGraph L) (1 / β) (dualBoxRoot L) := by
      rw [igffPartitionFunction]
      apply tsum_congr
      intro m
      exact currentGaussianWeight_dualHeightGradient_eq_igffWeight β m

/-- The line-source exponent in KP's height sign convention, summed over the unit ray to the
wired boundary. -/
def kpLineSourceSum (site : SquareFreeVertex L) (m : PinnedDualHeight L) : ℝ :=
  ∑ e, (unitSourceRay site e : ℝ) *
    (-(dualHeightGradient m.1 e : ℝ) + (1 / 2 : ℝ))

/-- KP's line source written in dual-box coordinates: it crosses the vertical dual edges at
columns strictly to the right of the source. Reindexing the column as `t + 1` gives the printed
sum from `t = x₀` through `L - 1` (KP Proposition 6.1, p. 34, with the endpoint correction). -/
def kpCoordinateLineSourceSum (site : SquareFreeVertex L) (m : PinnedDualHeight L) : ℝ :=
  ∑ i : Fin (L + 1), if site.1.val < i.val then
    (m.1 (i, lowIndex site.2) : ℝ) - (m.1 (i, highIndex site.2) : ℝ) +
      (1 / 2 : ℝ) else 0

/-- KP Proposition 6.1's corrected path sum, indexed by primal columns `t=x₀,…,L−1`. -/
def kpPrintedLineSourceSum (site : SquareFreeVertex L) (m : PinnedDualHeight L) : ℝ :=
  ∑ t : Fin L, if site.1.val ≤ t.val then
    (m.1 (highIndex t, lowIndex site.2) : ℝ) -
      (m.1 (highIndex t, highIndex site.2) : ℝ) + (1 / 2 : ℝ) else 0

/-- The vertical dual edges are indexed bijectively by a dual column and a free row. -/
private def verticalDualEdgeEquiv :
    (Fin (L + 1) × Fin L) ≃ SquareFreeVerticalEdge (L + 1) where
  toFun p := verticalDualEdgeData p.1 p.2
  invFun e := (e.1, verticalFaceY e)
  left_inv := by
    intro p
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [verticalDualEdgeData, verticalFaceY, Fin.val_castLE]
  right_inv := by
    intro e
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Fin.ext
      simp [verticalDualEdgeData, verticalFaceY]

/-- Summing the shift over the ray's edge support is exactly KP's coordinate line-source sum. -/
theorem kpLineSourceSum_eq_coordinateLineSourceSum (site : SquareFreeVertex L)
    (m : PinnedDualHeight L) : kpLineSourceSum site m = kpCoordinateLineSourceSum site m := by
  classical
  let f : SquareFreeVerticalEdge (L + 1) → ℝ := fun e =>
    (unitSourceRay site (.inr e) : ℝ) *
      (-(dualHeightGradient m.1 (.inr e) : ℝ) + (1 / 2 : ℝ))
  have hterm (i : Fin (L + 1)) (j : Fin L) :
      f (verticalDualEdgeEquiv (L := L) (i, j)) =
        if j.val = site.2.val ∧ site.1.val < i.val then
          (m.1 (i, lowIndex j) : ℝ) - (m.1 (i, highIndex j) : ℝ) +
            (1 / 2 : ℝ) else 0 := by
    change (unitSourceRay site (.inr (verticalDualEdgeData i j)) : ℝ) *
      (-(dualHeightGradient m.1 (.inr (verticalDualEdgeData i j)) : ℝ) +
        (1 / 2 : ℝ)) = _
    have hgrad : dualHeightGradient m.1 (.inr (verticalDualEdgeData i j)) =
        m.1 (i, highIndex j) - m.1 (i, lowIndex j) := by
      change verticalCurrent (dualHeightGradient m.1) i j = _
      exact verticalCurrent_dualHeightGradient m.1 i j
    rw [hgrad]
    by_cases hcond : j.val = site.2.val ∧ site.1.val < i.val
    · simp [unitSourceRay, verticalDualEdgeData, hcond]
    · simp [unitSourceRay, verticalDualEdgeData, hcond]
  have hsplit : kpLineSourceSum site m = ∑ e : SquareFreeVerticalEdge (L + 1), f e := by
    unfold kpLineSourceSum
    rw [Fintype.sum_sum_type]
    simp [f, unitSourceRay]
  unfold kpCoordinateLineSourceSum
  calc
    kpLineSourceSum site m = ∑ e : SquareFreeVerticalEdge (L + 1), f e := hsplit
    _ =
        ∑ p : Fin (L + 1) × Fin L, f (verticalDualEdgeEquiv (L := L) p) :=
      (Fintype.sum_equiv (verticalDualEdgeEquiv (L := L))
        (fun p => f (verticalDualEdgeEquiv (L := L) p)) f (by intro p; rfl)).symm
    _ = ∑ i : Fin (L + 1), ∑ j : Fin L,
        if site.2.val = j.val ∧ site.1.val < i.val then
          (m.1 (i, lowIndex j) : ℝ) - (m.1 (i, highIndex j) : ℝ) +
            (1 / 2 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm i j).trans (if_congr (and_congr_left' eq_comm) rfl rfl)
    _ = ∑ i : Fin (L + 1), if site.1.val < i.val then
          (m.1 (i, lowIndex site.2) : ℝ) -
            (m.1 (i, highIndex site.2) : ℝ) + (1 / 2 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hcol : site.1.val < i.val
      · have heq (j : Fin L) : site.2.val = j.val ↔ j = site.2 := by
          constructor
          · intro hj
            exact Fin.ext hj.symm
          · intro hj
            have hj' := congrArg Fin.val hj
            simpa using hj'.symm
        simp_rw [heq]
        simp [hcol]
      · simp [hcol]

/-- Changing column index `i` to `t+1` identifies the ray sum with the corrected KP path from
`x₀` through `L−1`. -/
theorem kpCoordinateLineSourceSum_eq_printed (site : SquareFreeVertex L)
    (m : PinnedDualHeight L) :
    kpCoordinateLineSourceSum site m = kpPrintedLineSourceSum site m := by
  classical
  unfold kpCoordinateLineSourceSum kpPrintedLineSourceSum
  rw [Fin.sum_univ_succ]
  have hzero :
      (if site.1.val < (0 : Fin (L + 1)).val then
        (m.1 (0, lowIndex site.2) : ℝ) -
          (m.1 (0, highIndex site.2) : ℝ) + (1 / 2 : ℝ) else 0) = 0 := by
    simp
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro t ht
  have hi : (Fin.succ t : Fin (L + 1)) = highIndex t := by
    apply Fin.ext
    rfl
  rw [hi]
  have hcond : site.1.val < (highIndex t).val ↔ site.1.val ≤ t.val := by
    simp only [highIndex, Fin.val_mk]
    omega
  simp [hcond]

/-- The corrected KP coordinate path is the same source observable as the ray sum. -/
theorem kpLineSourceSum_eq_printed (site : SquareFreeVertex L)
    (m : PinnedDualHeight L) : kpLineSourceSum site m = kpPrintedLineSourceSum site m := by
  rw [kpLineSourceSum_eq_coordinateLineSourceSum, kpCoordinateLineSourceSum_eq_printed]

/-- The exponential line-source observable at Villain inverse temperature `β`. -/
def kpLineSourceObservable (β : ℝ) (site : SquareFreeVertex L)
    (m : PinnedDualHeight L) : ℝ :=
  Real.exp (-(kpLineSourceSum site m) / β)

/-- The line-source observable written with KP's corrected coordinate path. -/
def kpPrintedLineSourceObservable (β : ℝ) (site : SquareFreeVertex L)
    (m : PinnedDualHeight L) : ℝ :=
  Real.exp (-(kpPrintedLineSourceSum site m) / β)

/-- KP's line-source observable viewed as a function on an unpinned height, so it can be evaluated
under any choice of IGFF root. -/
def kpPrintedLineSourceFieldSum (site : SquareFreeVertex L)
    (m : SquareFreeVertex (L + 1) → ℤ) : ℝ :=
  ∑ t : Fin L, if site.1.val ≤ t.val then
    (m (highIndex t, lowIndex site.2) : ℝ) -
      (m (highIndex t, highIndex site.2) : ℝ) + (1 / 2 : ℝ) else 0

/-- The arbitrary-root form of KP's line-source observable. -/
def kpPrintedLineSourceFieldObservable (β : ℝ) (site : SquareFreeVertex L)
    (m : SquareFreeVertex (L + 1) → ℤ) : ℝ :=
  Real.exp (-(kpPrintedLineSourceFieldSum site m) / β)

/-- The line-source observable is unchanged by adding a constant to all heights. -/
theorem kpPrintedLineSourceFieldObservable_rebase_eq (β : ℝ)
    (site : SquareFreeVertex L) (r s : SquareFreeVertex (L + 1))
    (m : pinnedIntegerField (SquareFreeVertex (L + 1)) r) :
    kpPrintedLineSourceFieldObservable β site
        (pinnedIntegerFieldRebase r s m).1 =
      kpPrintedLineSourceFieldObservable β site m.1 := by
  unfold kpPrintedLineSourceFieldObservable kpPrintedLineSourceFieldSum
  apply congrArg Real.exp
  apply congrArg (fun x : ℝ => -x / β)
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : site.1.val ≤ t.val
  · simp only [h, ↓reduceIte]
    simp only [pinnedIntegerFieldRebase_apply]
    push_cast
    ring
  · simp [h]

/-- The pinned and arbitrary-root line-source observable definitions agree. -/
theorem kpPrintedLineSourceObservable_eq_field (β : ℝ) (site : SquareFreeVertex L)
    (m : PinnedDualHeight L) :
    kpPrintedLineSourceObservable β site m =
      kpPrintedLineSourceFieldObservable β site m.1 := by
  rfl

/-- The ray, dual-column and KP printed path observables agree. -/
theorem kpLineSourceObservable_eq_printed (β : ℝ) (site : SquareFreeVertex L) :
    kpLineSourceObservable β site = kpPrintedLineSourceObservable β site := by
  funext m
  simp [kpLineSourceObservable, kpPrintedLineSourceObservable, kpLineSourceSum_eq_printed]

/-- Every edge of the chosen ray carries either zero or one unit of current. -/
theorem unitSourceRay_sq (site : SquareFreeVertex L) (e : WiredEdge L) :
    unitSourceRay site e ^ 2 = unitSourceRay site e := by
  cases e with
  | inl e => simp [unitSourceRay]
  | inr e => simp only [unitSourceRay]; split_ifs <;> norm_num

/-- Completing the square on the unit ray turns the source-current Gaussian weight into the
rooted IGFF weight times KP's line-source observable. -/
theorem currentGaussianWeight_sourceHeight_eq_igffWeight_mul_lineSource
    (β : ℝ) (site : SquareFreeVertex L) (m : PinnedDualHeight L) :
    currentGaussianWeight β (unitSourceKPHeightCurrent site m.1) =
      igffWeight (dualBoxGraph L) (1 / β) m * kpLineSourceObservable β site m := by
  classical
  have hsum :
      (∑ e, -((unitSourceKPHeightCurrent site m.1 e : ℝ) ^ 2) / (2 * β)) =
        -(1 / β / 2) * ∑ e, (dualHeightGradient m.1 e : ℝ) ^ 2 -
          kpLineSourceSum site m / β := by
    calc
      _ = ∑ e, ((-(1 / β / 2)) * (dualHeightGradient m.1 e : ℝ) ^ 2 +
            (-(1 / β)) * (unitSourceRay site e : ℝ) *
              (-(dualHeightGradient m.1 e : ℝ) + (1 / 2 : ℝ))) := by
        apply Finset.sum_congr rfl
        intro e he
        let r : ℝ := unitSourceRay site e
        let g : ℝ := dualHeightGradient m.1 e
        have hr : r ^ 2 = r := by
          dsimp [r]
          exact_mod_cast unitSourceRay_sq site e
        have hq : (unitSourceKPHeightCurrent site m.1 e : ℝ) = r - g := by
          simp [unitSourceKPHeightCurrent, dualHeightGradient, r, g]
        have hsq : (r - g) ^ 2 = g ^ 2 + 2 * r * (-g + (1 / 2 : ℝ)) := by
          linear_combination hr
        rw [hq, hsq]
        ring
      _ = -(1 / β / 2) * ∑ e, (dualHeightGradient m.1 e : ℝ) ^ 2 +
            (-(1 / β)) * ∑ e, (unitSourceRay site e : ℝ) *
              (-(dualHeightGradient m.1 e : ℝ) + (1 / 2 : ℝ)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.mul_sum]
        · calc
            _ = ∑ e, (-(1 / β)) * ((unitSourceRay site e : ℝ) *
                (-(dualHeightGradient m.1 e : ℝ) + (1 / 2 : ℝ))) := by
              apply Finset.sum_congr rfl
              intro e he
              ring
            _ = (-(1 / β)) * ∑ e, (unitSourceRay site e : ℝ) *
                  (-(dualHeightGradient m.1 e : ℝ) + (1 / 2 : ℝ)) := by
              rw [← Finset.mul_sum]
      _ = -(1 / β / 2) * ∑ e, (dualHeightGradient m.1 e : ℝ) ^ 2 -
            kpLineSourceSum site m / β := by
        simp only [kpLineSourceSum]
        ring
  unfold currentGaussianWeight
  rw [← Real.exp_sum, igffWeight, kpLineSourceObservable, ← Real.exp_add]
  apply congrArg Real.exp
  have henergy : (dualBoxGraph L).energy (fun p => (m.1 p : ℝ)) =
      ∑ e, (dualHeightGradient m.1 e : ℝ) ^ 2 := by
    unfold Multigraph.energy Multigraph.grad
    apply Finset.sum_congr rfl
    intro e he
    dsimp [dualHeightGradient]
    push_cast
    ring
  rw [← henergy] at hsum
  calc
    _ = -(1 / β / 2) * (dualBoxGraph L).energy (fun p => (m.1 p : ℝ)) -
          kpLineSourceSum site m / β := hsum
    _ = -(1 / β / 2) * (dualBoxGraph L).energy (fun p => (m.1 p : ℝ)) +
          (-(kpLineSourceSum site m) / β) := by ring

/-- The dual free square is connected, so its rooted IGFF partition function is well-defined. -/
theorem dualBoxGraph_connected (hL : 0 < L) : (dualBoxGraph L).Connected := by
  rw [dualBoxGraph]
  exact squareFreeGraph_connected (by omega)

/-- The source Villain current sum is the IGFF line-source numerator. -/
theorem sourceCurrent_tsum_eq_igffLineSourceTsum (β : ℝ) (site : SquareFreeVertex L) :
    (∑' q : WiredEdge L → ℤ,
      sourceCurrentGaussianWeight (wiredBoxGraph L) none (some site) β q) =
      ∑' m : PinnedDualHeight L,
        kpLineSourceObservable β site m * igffWeight (dualBoxGraph L) (1 / β) m := by
  classical
  unfold sourceCurrentGaussianWeight
  rw [tsum_if_eq_subtype]
  let e := sourceCurrentHeightEquiv (L := L) site
  change (∑' q : SourceWiredCurrent L site, currentGaussianWeight β q.1) = _
  calc
    (∑' q : SourceWiredCurrent L site, currentGaussianWeight β q.1) =
        ∑' m : PinnedDualHeight L, currentGaussianWeight β (e m).1 :=
      (Equiv.tsum_eq e (fun q : SourceWiredCurrent L site => currentGaussianWeight β q.1)).symm
    _ = ∑' m : PinnedDualHeight L,
          kpLineSourceObservable β site m * igffWeight (dualBoxGraph L) (1 / β) m := by
      apply tsum_congr
      intro m
      change currentGaussianWeight β (unitSourceKPHeightCurrent site m.1) = _
      rw [currentGaussianWeight_sourceHeight_eq_igffWeight_mul_lineSource]
      exact mul_comm _ _

/-- KP Proposition 6.1 with the dual height pinned at the lower-left face and the source path
written as a ray sum over crossed dual edges. -/
theorem villainCosExpectation_eq_igffLineSourceExpectation (hL : 0 < L)
    (β : ℝ) (hβ : 0 < β) (site : SquareFreeVertex L) :
    villainCosExpectation (wiredBoxGraph L) none β
        ⟨some site, Option.some_ne_none _⟩ =
      igffExpectation (dualBoxGraph L) (dualBoxGraph_connected hL) (1 / β)
        (one_div_pos.mpr hβ) (dualBoxRoot L) (kpLineSourceObservable β site) := by
  have hcos := villainCosExpectation_eq_character_and_current_ratio
    (wiredBoxGraph L) none β hβ ⟨some site, Option.some_ne_none _⟩
  rw [hcos.1, sourceCurrent_tsum_eq_igffLineSourceTsum β site,
    neutralCurrent_tsum_eq_igffPartitionFunction β]
  rfl

/-- KP Proposition 6.1 with `t=x₀,…,L−1` and the lower-left dual face pinned. The expectation is
the root-pinned IGFF at inverse temperature `β⁻¹` of the source-to-boundary line observable. -/
theorem villainCosExpectation_eq_kpProposition61 (hL : 1 < L)
    (β : ℝ) (hβ : 0 < β) (site : SquareFreeVertex L) :
    villainCosExpectation (wiredBoxGraph L) none β
        ⟨some site, Option.some_ne_none _⟩ =
      igffExpectation (dualBoxGraph L) (dualBoxGraph_connected (by omega)) (1 / β)
        (one_div_pos.mpr hβ) (dualBoxRoot L) (kpPrintedLineSourceObservable β site) := by
  rw [villainCosExpectation_eq_igffLineSourceExpectation (by omega) β hβ site,
    kpLineSourceObservable_eq_printed]

/-- KP Proposition 6.1 for any chosen dual pinning vertex. The line observable only uses height
differences, so rebasing the IGFF root leaves its expectation unchanged. -/
theorem villainCosExpectation_eq_kpProposition61_atRoot (hL : 1 < L)
    (β : ℝ) (hβ : 0 < β) (site : SquareFreeVertex L)
    (v : SquareFreeVertex (L + 1)) :
    villainCosExpectation (wiredBoxGraph L) none β
        ⟨some site, Option.some_ne_none _⟩ =
      igffExpectation (dualBoxGraph L) (dualBoxGraph_connected (by omega)) (1 / β)
        (one_div_pos.mpr hβ) v
        (fun m => kpPrintedLineSourceFieldObservable β site m.1) := by
  rw [villainCosExpectation_eq_kpProposition61 hL β hβ site]
  exact igffExpectation_rebase_eq (dualBoxGraph L) (dualBoxGraph_connected (by omega))
    (1 / β) (one_div_pos.mpr hβ) (dualBoxRoot L) v
    (kpPrintedLineSourceObservable β site)
    (fun m => kpPrintedLineSourceFieldObservable β site m.1)
    (fun m => (kpPrintedLineSourceFieldObservable_rebase_eq β site
      (dualBoxRoot L) v m).symm)

end FroehlichSpencer.BKT.Duality

end
