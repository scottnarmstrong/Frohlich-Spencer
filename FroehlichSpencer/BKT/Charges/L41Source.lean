/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.L41CarrierFit
public import FroehlichSpencer.BKT.Charges.L41ScaleBounds
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
public import FroehlichSpencer.BKT.Charges.C42PathExtraction
public import FroehlichSpencer.BKT.Charges.SupportCover
public import FroehlichSpencer.BKT.Charges.PatchIsolation
public import FroehlichSpencer.BKT.Charges.Claim42

/-! # Source-facing Lemma 4.1 -/

@[expose] public section

namespace FroehlichSpencer.BKT

/--
The vertex distance is symmetric on either  square carrier.
-/
theorem latticeDistance_comm (boundary : SquareBoundary) (L : ℕ)
    (x y : Fin L × Fin L) :
    latticeDistance boundary L x y = latticeDistance boundary L y x := by
  cases boundary <;> simp [latticeDistance, SimpleGraph.dist_comm]

/-- A nonempty pair of squares has a pair of points realizing its graph
distance. -/
theorem exists_squareDistance_witness (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) (hs : s.Nonempty) (ht : t.Nonempty) :
    ∃ x ∈ s, ∃ y ∈ t,
      latticeDistance boundary L x y = squareDistance boundary L s t := by
  classical
  have hprod : (s.product t).Nonempty := by
    rcases hs with ⟨x, hx⟩
    rcases ht with ⟨y, hy⟩
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  have hmem := Finset.min'_mem
    ((s.product t).image fun p => latticeDistance boundary L p.1 p.2)
    (Finset.image_nonempty.mpr hprod)
  rcases Finset.mem_image.mp hmem with ⟨p, hp, hpd⟩
  rcases Finset.mem_product.mp hp with ⟨hpx, hpy⟩
  refine ⟨p.1, hpx, p.2, hpy, ?_⟩
  unfold squareDistance
  rw [dite_eq_left hprod]
  exact hpd

/-- The distance of two finite squares is symmetric. -/
theorem squareDistance_comm (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) :
    squareDistance boundary L s t = squareDistance boundary L t s := by
  classical
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · obtain ⟨x, hx, y, hy, hxy⟩ :=
        exists_squareDistance_witness boundary L s t hs ht
      obtain ⟨y', hy', x', hx', hyx⟩ :=
        exists_squareDistance_witness boundary L t s ht hs
      apply le_antisymm
      · calc
          squareDistance boundary L s t ≤ latticeDistance boundary L x' y' :=
            squareDistance_le_latticeDistance_of_mem boundary L s t x' y' hx' hy'
          _ = squareDistance boundary L t s := by
            rw [latticeDistance_comm]
            exact hyx
      · calc
          squareDistance boundary L t s ≤ latticeDistance boundary L y x :=
            squareDistance_le_latticeDistance_of_mem boundary L t s y x hy hx
          _ = squareDistance boundary L s t := by
            rw [latticeDistance_comm]
            exact hxy
    · simp [squareDistance, ht]
  · simp [squareDistance, hs]

/-- Triangle inequality on either finite square graph. -/
theorem latticeDistance_triangle (boundary : SquareBoundary) (L : ℕ)
    (hL : 1 < L) (x y z : Fin L × Fin L) :
    latticeDistance boundary L x z ≤
      latticeDistance boundary L x y + latticeDistance boundary L y z := by
  cases boundary with
  | free => exact (squareFree_connected L hL).dist_triangle
  | periodic => exact (squarePeriodic_connected L hL).dist_triangle

/-- A point-pair distance inside a finite square is bounded by its diameter. -/
theorem latticeDistance_le_squareDiameter (boundary : SquareBoundary) (L : ℕ)
    (s : Finset (Fin L × Fin L)) (x y : Fin L × Fin L)
    (hx : x ∈ s) (hy : y ∈ s) :
    latticeDistance boundary L x y ≤ squareDiameter boundary L s := by
  classical
  have hprod : (s.product s).Nonempty :=
    ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  unfold squareDiameter
  rw [dite_eq_left hprod]
  have hmem : latticeDistance boundary L x y ∈
      (s.product s).image (fun p : (Fin L × Fin L) × (Fin L × Fin L) =>
        latticeDistance boundary L p.1 p.2) :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  exact Finset.le_max' _ _ hmem

/-- A square is contained in the same-statement square at every larger scale. -/
theorem kpSquare_subset_of_le (boundary : SquareBoundary) (L k K : ℕ)
    (a : Fin L × Fin L) (hkK : k ≤ K) :
    kpSquare boundary L k a ⊆ kpSquare boundary L K a := by
  have hdecomp : k + (K - k) = K := Nat.add_sub_of_le hkK
  rw [← hdecomp]
  induction K - k with
  | zero => simp
  | succ n ih =>
      change kpSquare boundary L k a ⊆ kpSquare boundary L (k + n + 1) a
      exact ih.trans (kpSquare_subset_succ boundary L (k + n) a)

/-- The graph of scale-`q` cover squares joined when their distance is below
the (2.4) threshold. -/
def l41ConflictGraph (boundary : SquareBoundary) (L : ℕ) (R : ℝ) :
    SimpleGraph (Finset (Fin L × Fin L)) where
  Adj := fun s t => s ≠ t ∧ (squareDistance boundary L s t : ℝ) < R
  symm := by
    constructor
    intro s t h
    exact ⟨h.1.symm, by rw [squareDistance_comm]; exact h.2⟩
  loopless := by
    constructor
    intro s h
    exact h.1 rfl

/-- The coordinate enclosure for one connected Claim 4.2 cluster of lower
cover squares. Pair and triple links are realized by minimizing point pairs;
the two contacts in a middle square are joined using its graph diameter. -/
theorem l41C42Cluster_fit (boundary : SquareBoundary) (L K : ℕ)
    (hL : 1 < L) (hK : 21 ≤ K)
    (ρ : ChargeDensity L)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L (l41LowerScale K) ρ C})
    (U : Finset (Finset (Fin L × Fin L)))
    (hU : U ⊆ C.val)
    (t : Finset {s // s ∈ U})
    (hconn : IsC42Set
      ((l41ConflictGraph boundary L
        (squareSeparationThresholdNat (l41LowerScale K))).induce
          (U : Set (Finset (Fin L × Fin L)))) t) :
    ∃ T ∈ kpSquares boundary L K, ∀ s ∈ t, s.val ⊆ T := by
  classical
  let G := l41ConflictGraph boundary L
    (squareSeparationThresholdNat (l41LowerScale K))
  let H := G.induce (U : Set (Finset (Fin L × Fin L)))
  have hqK : l41LowerScale K < K := by
    obtain ⟨_, hgap⟩ := l41LowerScale_spec K hK
    omega
  rcases exists_c42_path_ordering H t hconn with hpair | htriple
  · obtain ⟨u, v, huv, hset, hadj⟩ := hpair
    have huC : u.val ∈ C.val := hU u.property
    have hvC : v.val ∈ C.val := hU v.property
    have huPatch := supportPatch_nonempty_of_mem_minimumSquareCover
      boundary L (l41LowerScale K) ρ C.val C.property u.val huC
    have hvPatch := supportPatch_nonempty_of_mem_minimumSquareCover
      boundary L (l41LowerScale K) ρ C.val C.property v.val hvC
    obtain ⟨x, hx⟩ := huPatch
    obtain ⟨y, hy⟩ := hvPatch
    have hx' : x ∈ u.val := (Finset.mem_inter.mp hx).1
    have hy' : y ∈ v.val := (Finset.mem_inter.mp hy).1
    have hadjG : G.Adj u.val v.val := SimpleGraph.induce_adj.mp hadj
    have hdR : (squareDistance boundary L u.val v.val : ℝ) <
        squareSeparationThresholdNat (l41LowerScale K) := hadjG.2
    obtain ⟨x0, hx0, y0, hy0, hdist⟩ :=
      exists_squareDistance_witness boundary L u.val v.val
        (by exact ⟨x, hx'⟩) (by exact ⟨y, hy'⟩)
    have hdNat : latticeDistance boundary L x0 y0 =
        squareDistance boundary L u.val v.val := hdist
    have hdReal : (squareDistance boundary L u.val v.val : ℝ) <
        squareSeparationThresholdNat (l41LowerScale K) := hdR
    have hbudget := l41_pair_budget K (squareDistance boundary L u.val v.val)
      hK hdReal
    have hfitBudget : latticeDistance boundary L x0 y0 +
        2 * (squareSide (l41LowerScale K) - 1) < squareSide K := by
      rw [hdNat]
      exact hbudget
    have huSquare : u.val ∈ kpSquares boundary L (l41LowerScale K) :=
      C.property.1.1 huC
    have hvSquare : v.val ∈ kpSquares boundary L (l41LowerScale K) :=
      C.property.1.1 hvC
    let au := squareAnchor boundary L (l41LowerScale K) (by omega) u.val
    let av := squareAnchor boundary L (l41LowerScale K) (by omega) v.val
    have hEqU := kpSquare_eq_of_squareAnchor boundary L (l41LowerScale K)
      (by omega) u.val huSquare
    have hEqV := kpSquare_eq_of_squareAnchor boundary L (l41LowerScale K)
      (by omega) v.val hvSquare
    have hx0' : x0 ∈ kpSquare boundary L (l41LowerScale K) au := by
      change x0 ∈ kpSquare boundary L (l41LowerScale K)
        (squareAnchor boundary L (l41LowerScale K) (by omega) u.val)
      rw [hEqU]
      exact hx0
    have hy0' : y0 ∈ kpSquare boundary L (l41LowerScale K) av := by
      change y0 ∈ kpSquare boundary L (l41LowerScale K)
        (squareAnchor boundary L (l41LowerScale K) (by omega) v.val)
      rw [hEqV]
      exact hy0
    obtain ⟨a, hfit⟩ := pairCarrierSquares_fit boundary L (l41LowerScale K) K
      hL hqK au av x0 y0 hx0' hy0'
      hfitBudget
    refine ⟨kpSquare boundary L K a,
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ?_⟩
    intro s hs
    have hs' : s = u ∨ s = v := by
      rw [hset] at hs
      simpa using hs
    rcases hs' with rfl | rfl
    · intro z hz
      apply hfit
      exact Finset.mem_union.mpr (Or.inl (by rw [hEqU]; exact hz))
    · intro z hz
      apply hfit
      exact Finset.mem_union.mpr (Or.inr (by rw [hEqV]; exact hz))
  · obtain ⟨u, v, w, huv, huw, hvw, hset, hadj₁, hadj₂⟩ := htriple
    have huC : u.val ∈ C.val := hU u.property
    have hvC : v.val ∈ C.val := hU v.property
    have hwC : w.val ∈ C.val := hU w.property
    have huPatch := supportPatch_nonempty_of_mem_minimumSquareCover
      boundary L (l41LowerScale K) ρ C.val C.property u.val huC
    have hvPatch := supportPatch_nonempty_of_mem_minimumSquareCover
      boundary L (l41LowerScale K) ρ C.val C.property v.val hvC
    have hwPatch := supportPatch_nonempty_of_mem_minimumSquareCover
      boundary L (l41LowerScale K) ρ C.val C.property w.val hwC
    obtain ⟨x, hx⟩ := huPatch
    obtain ⟨y₁, hy₁⟩ := hvPatch
    obtain ⟨z, hz⟩ := hwPatch
    have hx' : x ∈ u.val := (Finset.mem_inter.mp hx).1
    have hy₁' : y₁ ∈ v.val := (Finset.mem_inter.mp hy₁).1
    have hz' : z ∈ w.val := (Finset.mem_inter.mp hz).1
    have hvSquare : v.val ∈ kpSquares boundary L (l41LowerScale K) :=
      C.property.1.1 hvC
    have hadj₁G : G.Adj u.val v.val := SimpleGraph.induce_adj.mp hadj₁
    have hadj₂G : G.Adj v.val w.val := SimpleGraph.induce_adj.mp hadj₂
    have hdR₁ : (squareDistance boundary L u.val v.val : ℝ) <
        squareSeparationThresholdNat (l41LowerScale K) := hadj₁G.2
    have hdR₂ : (squareDistance boundary L v.val w.val : ℝ) <
        squareSeparationThresholdNat (l41LowerScale K) := hadj₂G.2
    obtain ⟨x₀, hx₀, y₀, hy₀, hdist₁⟩ :=
      exists_squareDistance_witness boundary L u.val v.val
        ⟨x, hx'⟩ ⟨y₁, hy₁'⟩
    obtain ⟨y₂₀, hy₂₀, z₀, hz₀, hdist₂⟩ :=
      exists_squareDistance_witness boundary L v.val w.val
        ⟨y₁, hy₁'⟩ ⟨z, hz'⟩
    have hdiam : squareDiameter boundary L v.val ≤
        2 * (squareSide (l41LowerScale K) - 1) := by
      cases boundary with
      | free => exact free_squareDiameter_le_all L (l41LowerScale K) v.val hvSquare
      | periodic => exact periodic_squareDiameter_le L (l41LowerScale K) hL v.val hvSquare
    have hmiddle : latticeDistance boundary L y₀ y₂₀ ≤
        2 * (squareSide (l41LowerScale K) - 1) := by
      exact (latticeDistance_le_squareDiameter boundary L v.val y₀ y₂₀ hy₀ hy₂₀).trans hdiam
    have htriangle := latticeDistance_triangle boundary L hL y₀ y₂₀ z₀
    have hsecond : latticeDistance boundary L y₀ z₀ ≤
        squareDistance boundary L v.val w.val +
          2 * (squareSide (l41LowerScale K) - 1) := by
      rw [hdist₂] at htriangle
      omega
    have hbudgetFive := l41_triple_budget_five K
      (squareDistance boundary L u.val v.val)
      (squareDistance boundary L v.val w.val) hK hdR₁ hdR₂
    have hbudget : latticeDistance boundary L x₀ y₀ +
        latticeDistance boundary L y₀ z₀ +
          3 * (squareSide (l41LowerScale K) - 1) < squareSide K := by
      rw [hdist₁]
      omega
    let au := squareAnchor boundary L (l41LowerScale K) (by omega) u.val
    let av := squareAnchor boundary L (l41LowerScale K) (by omega) v.val
    let aw := squareAnchor boundary L (l41LowerScale K) (by omega) w.val
    have hEqU := kpSquare_eq_of_squareAnchor boundary L (l41LowerScale K)
      (by omega) u.val (C.property.1.1 huC)
    have hEqV := kpSquare_eq_of_squareAnchor boundary L (l41LowerScale K)
      (by omega) v.val hvSquare
    have hEqW := kpSquare_eq_of_squareAnchor boundary L (l41LowerScale K)
      (by omega) w.val (C.property.1.1 hwC)
    have hx₀' : x₀ ∈ kpSquare boundary L (l41LowerScale K) au := by
      change x₀ ∈ kpSquare boundary L (l41LowerScale K)
        (squareAnchor boundary L (l41LowerScale K) (by omega) u.val)
      rw [hEqU]
      exact hx₀
    have hy₀' : y₀ ∈ kpSquare boundary L (l41LowerScale K) av := by
      change y₀ ∈ kpSquare boundary L (l41LowerScale K)
        (squareAnchor boundary L (l41LowerScale K) (by omega) v.val)
      rw [hEqV]
      exact hy₀
    have hz₀' : z₀ ∈ kpSquare boundary L (l41LowerScale K) aw := by
      change z₀ ∈ kpSquare boundary L (l41LowerScale K)
        (squareAnchor boundary L (l41LowerScale K) (by omega) w.val)
      rw [hEqW]
      exact hz₀
    obtain ⟨a, hfit⟩ := tripleCarrierSquares_fit boundary L
      (l41LowerScale K) K hL hqK au av aw x₀ y₀ z₀
      hx₀' hy₀' hz₀'
      hbudget
    refine ⟨kpSquare boundary L K a,
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ?_⟩
    intro s hs
    have hs' : s = u ∨ s = v ∨ s = w := by
      rw [hset] at hs
      simpa using hs
    rcases hs' with rfl | rfl | rfl
    · intro p hp
      apply hfit
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (by rw [hEqU]; exact hp))))
    · intro p hp
      apply hfit
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (by rw [hEqV]; exact hp))))
    · intro p hp
      apply hfit
      exact Finset.mem_union.mpr (Or.inr (by rw [hEqW]; exact hp))

/-- The source-facing one-step inequality in Lemma 4.1. The upper-scale
minimum cover is arbitrary; the lower-scale cover is the chosen minimum cover
whose separated family appears in the right-hand side. -/
theorem l41_recurrence_step (boundary : SquareBoundary) (L K : ℕ)
    (hL : 1 < L) (hK : 21 ≤ K) (ρ : ChargeDensity L)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L (l41LowerScale K) ρ C})
    (D : {D : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L K ρ D})
    (hcard : 2 ≤ C.val.card) :
    D.val.card ≤ C.val.card / 2 +
      (separatedSquaresNat boundary L ρ (l41LowerScale K) C).card := by
  classical
  let S := separatedSquaresNat boundary L ρ (l41LowerScale K) C
  let U := C.val \ S
  have hSsub : S ⊆ C.val := by
    intro s hs
    exact (Finset.mem_filter.mp hs).1
  have hUsub : U ⊆ C.val := Finset.sdiff_subset
  have hpartition : U.card + S.card = C.val.card := by
    dsimp [U, S]
    exact Finset.card_sdiff_add_card_eq_card hSsub
  have hScover : ∀ x ∈ chargeSupport ρ,
      ∃ s, (s ∈ S ∧ x ∈ s) ∨ (s ∈ U ∧ x ∈ s) := by
    intro x hx
    obtain ⟨s, hsD, hxs⟩ := C.property.1.2 x hx
    by_cases hs : s ∈ S
    · exact ⟨s, Or.inl ⟨hs, hxs⟩⟩
    · exact ⟨s, Or.inr ⟨Finset.mem_sdiff.mpr ⟨hsD, hs⟩, hxs⟩⟩
  have hqK : l41LowerScale K < K := by
    obtain ⟨_, hg⟩ := l41LowerScale_spec K hK
    omega
  let E := S.image fun s => kpSquare boundary L K
    (squareAnchor boundary L (l41LowerScale K) (by omega) s)
  have hEcard : E.card ≤ S.card := Finset.card_image_le
  have hEallowed : E ⊆ kpSquares boundary L K := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr ⟨squareAnchor boundary L (l41LowerScale K)
      (by omega) s, Finset.mem_univ _, rfl⟩
  have hEenlarges : ∀ s ∈ S, s ⊆ kpSquare boundary L K
      (squareAnchor boundary L (l41LowerScale K) (by omega) s) := by
    intro s hs
    have hsC := hSsub hs
    have hsQ := C.property.1.1 hsC
    calc
      s = kpSquare boundary L (l41LowerScale K)
          (squareAnchor boundary L (l41LowerScale K) (by omega) s) :=
        (kpSquare_eq_of_squareAnchor boundary L (l41LowerScale K) (by omega) s hsQ).symm
      _ ⊆ kpSquare boundary L K
          (squareAnchor boundary L (l41LowerScale K) (by omega) s) :=
        kpSquare_subset_of_le boundary L (l41LowerScale K) K _ (Nat.le_of_lt hqK)
  by_cases hUempty : U = ∅
  · have hCsubsetS : C.val ⊆ S := by
      intro s hs
      by_contra hsS
      have hsU : s ∈ U := Finset.mem_sdiff.mpr ⟨hs, hsS⟩
      rw [hUempty] at hsU
      simp at hsU
    have hEcover : IsSquareCover boundary L K ρ E := by
      refine ⟨hEallowed, ?_⟩
      · intro x hx
        obtain ⟨s, hsC, hxs⟩ := C.property.1.2 x hx
        have hsS := hCsubsetS hsC
        refine ⟨kpSquare boundary L K
          (squareAnchor boundary L (l41LowerScale K) (by omega) s), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨s, hsS, rfl⟩
        · exact hEenlarges s hsS hxs
    have hmin := D.property.2 E hEcover
    calc
      D.val.card ≤ E.card := hmin
      _ ≤ S.card := hEcard
      _ ≤ C.val.card / 2 + S.card := Nat.le_add_left _ _
  · have hUnonempty : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
    let G := l41ConflictGraph boundary L
      (squareSeparationThresholdNat (l41LowerScale K))
    let H := G.induce (U : Set (Finset (Fin L × Fin L)))
    let V := {s // s ∈ U}
    have hVNonempty : Nonempty V := ⟨⟨hUnonempty.choose, hUnonempty.choose_spec⟩⟩
    have hNoIso : ∀ v : V, ∃ w : V, H.Adj v w := by
      intro v
      have hvC : v.val ∈ C.val := hUsub v.property
      have hvNotSep : v.val ∉ S := (Finset.mem_sdiff.mp v.property).2
      have hvSepFalse : ¬ (∀ t ∈ C.val, t ≠ v.val →
          squareSeparationThresholdNat (l41LowerScale K) ≤
            (squareDistance boundary L v.val t : ℝ)) := by
        have hvNotSep' := hvNotSep
        simp only [S, separatedSquaresNat, Finset.mem_filter] at hvNotSep'
        intro hsep
        exact hvNotSep' ⟨hvC, by omega, hsep⟩
      have hbad : ∃ t, t ∈ C.val ∧ t ≠ v.val ∧
          (squareDistance boundary L v.val t : ℝ) <
            squareSeparationThresholdNat (l41LowerScale K) := by
        by_contra hnone
        apply hvSepFalse
        intro t ht hts
        by_contra hnotge
        exact hnone ⟨t, ht, hts, lt_of_not_ge hnotge⟩
      obtain ⟨t, htC, htv, hdist⟩ := hbad
      have htNotSep : t ∉ S := by
        intro htSep
        have hmem := Finset.mem_filter.mp (show t ∈ S by simpa [S] using htSep)
        have hsep := hmem.2.2
        have hrev := hsep v.val hvC htv.symm
        have hcomm := squareDistance_comm boundary L t v.val
        rw [hcomm] at hrev
        exact (not_le_of_gt hdist) hrev
      have htU : t ∈ U := Finset.mem_sdiff.mpr ⟨htC, htNotSep⟩
      refine ⟨⟨t, htU⟩, ?_⟩
      change G.Adj v.val t
      exact ⟨htv.symm, hdist⟩
    obtain ⟨groups, hlen, hnodup, hgroups⟩ :=
      @claim_4_2 V inferInstance H inferInstance hVNonempty inferInstance hNoIso
    let f : Finset V → Finset (Fin L × Fin L) := fun t =>
      if ht : t ∈ groups then Classical.choose
        (l41C42Cluster_fit boundary L K hL hK ρ C U hUsub t
          ((hgroups.1 t ht).1)) else ∅
    have hf : ∀ t ∈ groups, f t ∈ kpSquares boundary L K ∧
        ∀ s ∈ t, s.val ⊆ f t := by
      intro t ht
      dsimp [f]
      rw [dite_eq_left ht]
      exact Classical.choose_spec (l41C42Cluster_fit boundary L K hL hK ρ C U
        hUsub t ((hgroups.1 t ht).1))
    let T := groups.toFinset.image f
    have hTcover : IsSquareCover boundary L K ρ (E ∪ T) := by
      refine ⟨Finset.union_subset_iff.mpr ⟨hEallowed, ?_⟩, ?_⟩
      · intro s hs
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
        exact (hf t (List.mem_toFinset.mp ht)).1
      · intro x hx
        obtain ⟨s, hxsOr⟩ := hScover x hx
        rcases hxsOr with ⟨hsS, hxs⟩ | ⟨hsU, hxs⟩
        · refine ⟨kpSquare boundary L K
            (squareAnchor boundary L (l41LowerScale K) (by omega) s),
            Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨s, hsS, rfl⟩)), ?_⟩
          exact hEenlarges s hsS hxs
        · obtain ⟨t, ht, hst⟩ := hgroups.2 ⟨s, hsU⟩ (by simp)
          have htF := hf t ht
          refine ⟨f t, Finset.mem_union.mpr (Or.inr
            (Finset.mem_image.mpr ⟨t, List.mem_toFinset.mpr ht, rfl⟩)), ?_⟩
          exact htF.2 ⟨s, hsU⟩ hst hxs
    have hcardT : T.card ≤ groups.length := by
      calc
        T.card ≤ groups.toFinset.card := Finset.card_image_le
        _ ≤ groups.length := List.toFinset_card_le _
    have hcardD : D.val.card ≤ (E ∪ T).card := D.property.2 _ hTcover
    have hhalf : groups.length ≤ U.card / 2 := by
      have hlen' : groups.length = U.card / 2 := by simpa [V] using hlen
      omega
    calc
      D.val.card ≤ (E ∪ T).card := hcardD
      _ ≤ E.card + T.card := Finset.card_union_le _ _
      _ ≤ S.card + groups.length := Nat.add_le_add hEcard hcardT
      _ ≤ S.card + U.card / 2 := Nat.add_le_add_left hhalf _
      _ ≤ C.val.card / 2 + S.card := by rw [← hpartition]; omega

end FroehlichSpencer.BKT

end
