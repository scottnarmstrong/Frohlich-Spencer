/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyTerminal
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyOverlap
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryCutGeometry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter

/-! # Linear Euclidean tents for selected charge squares -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

private theorem boundaryEnergy_one_le_two_pow (j : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; nlinarith

/-- Euclidean distance from a site to a finite set, with value zero on the empty set.
Selected squares are nonempty, so only the finite-minimum branch is used below. -/
def boundaryEnergyDistanceToSet (s : Finset (Site L)) (x : Site L) : ℝ :=
  if hs : s.Nonempty then
    (s.image fun y => euclideanSiteDistance y x).min'
      (Finset.image_nonempty.mpr hs)
  else 0

theorem boundaryEnergyDistanceToSet_nonneg (s : Finset (Site L)) (x : Site L) :
    0 ≤ boundaryEnergyDistanceToSet s x := by
  classical
  unfold boundaryEnergyDistanceToSet
  split
  next hs =>
    apply Finset.le_min'
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    unfold euclideanSiteDistance
    exact Real.sqrt_nonneg _
  next _ => norm_num

theorem boundaryEnergyDistanceToSet_le (s : Finset (Site L)) (hs : s.Nonempty)
    {x y : Site L} (hy : y ∈ s) :
    boundaryEnergyDistanceToSet s x ≤ euclideanSiteDistance y x := by
  classical
  rw [boundaryEnergyDistanceToSet, dite_eq_left hs]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

theorem boundaryEnergyDistanceToSet_eq_zero_of_mem (s : Finset (Site L))
    {x : Site L} (hx : x ∈ s) : boundaryEnergyDistanceToSet s x = 0 := by
  have hs : s.Nonempty := ⟨x, hx⟩
  have hnonneg := boundaryEnergyDistanceToSet_nonneg s x
  have hle : boundaryEnergyDistanceToSet s x ≤ euclideanSiteDistance x x :=
    boundaryEnergyDistanceToSet_le s hs hx
  have hxx : euclideanSiteDistance x x = 0 := by
    unfold euclideanSiteDistance
    simp
  rw [hxx] at hle
  exact le_antisymm hle hnonneg

theorem boundaryEnergyDistanceToSet_abs_sub_le (s : Finset (Site L))
    (x y : Site L) :
    |boundaryEnergyDistanceToSet s x - boundaryEnergyDistanceToSet s y| ≤
      euclideanSiteDistance x y := by
  classical
  by_cases hs : s.Nonempty
  · let values := s.image fun z => euclideanSiteDistance z y
    have hvalues : values.Nonempty := Finset.image_nonempty.mpr hs
    obtain ⟨w, hw, hwval⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
    have hDy : boundaryEnergyDistanceToSet s y = euclideanSiteDistance w y := by
      rw [boundaryEnergyDistanceToSet, dite_eq_left hs]
      simpa [values] using hwval.symm
    have hDx : boundaryEnergyDistanceToSet s x ≤ euclideanSiteDistance w x :=
      boundaryEnergyDistanceToSet_le s hs hw
    have hforward : boundaryEnergyDistanceToSet s x ≤
        boundaryEnergyDistanceToSet s y + euclideanSiteDistance x y := by
      rw [hDy]
      have htri := euclideanSiteDistance_triangle w y x
      have hsym := SelectionG.siteDist_comm y x
      rw [hsym] at htri
      exact hDx.trans htri
    let valuesX := s.image fun z => euclideanSiteDistance z x
    have hvaluesX : valuesX.Nonempty := Finset.image_nonempty.mpr hs
    obtain ⟨wX, hwX, hwXval⟩ :=
      Finset.mem_image.mp (Finset.min'_mem valuesX hvaluesX)
    have hDxEq : boundaryEnergyDistanceToSet s x = euclideanSiteDistance wX x := by
      rw [boundaryEnergyDistanceToSet, dite_eq_left hs]
      simpa [valuesX] using hwXval.symm
    have hDyx : boundaryEnergyDistanceToSet s y ≤
        boundaryEnergyDistanceToSet s x + euclideanSiteDistance y x := by
      have hDyLe := boundaryEnergyDistanceToSet_le s hs (x := y) (y := wX) hwX
      have htri := euclideanSiteDistance_triangle wX x y
      rw [SelectionG.siteDist_comm x y] at htri
      rw [hDxEq]
      exact hDyLe.trans htri
    have hsym := SelectionG.siteDist_comm y x
    rw [hsym] at hDyx
    rw [abs_le]
    constructor <;> linarith
  · simp [boundaryEnergyDistanceToSet, hs]
    exact SelectionG.siteDist_nonneg x y

theorem le_boundaryEnergyDistanceToSet_of_forall
    (s : Finset (Site L)) (hs : s.Nonempty) (x : Site L) (r : ℝ)
    (hfar : ∀ y ∈ s, r ≤ euclideanSiteDistance y x) :
    r ≤ boundaryEnergyDistanceToSet s x := by
  classical
  rw [boundaryEnergyDistanceToSet, dite_eq_left hs]
  apply Finset.le_min'
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  exact hfar y hy

/-- The unit-height tent of radius `r` around a nonempty finite site set. -/
def boundaryEnergyTent (s : Finset (Site L)) (r : ℝ) (x : Site L) : ℝ :=
  max 0 (1 - boundaryEnergyDistanceToSet s x / r)

theorem boundaryEnergyTent_eq_one_of_mem (s : Finset (Site L)) (r : ℝ)
    {x : Site L} (hx : x ∈ s) : boundaryEnergyTent s r x = 1 := by
  rw [boundaryEnergyTent, boundaryEnergyDistanceToSet_eq_zero_of_mem s hx]
  norm_num

theorem boundaryEnergyTent_eq_zero_of_far (s : Finset (Site L)) (hs : s.Nonempty)
    (r : ℝ) (hr : 0 < r) (x : Site L)
    (hfar : ∀ y ∈ s, r < euclideanSiteDistance y x) :
    boundaryEnergyTent s r x = 0 := by
  have hdist : r ≤ boundaryEnergyDistanceToSet s x :=
    le_boundaryEnergyDistanceToSet_of_forall s hs x r (fun y hy => (hfar y hy).le)
  have hquot : 1 ≤ boundaryEnergyDistanceToSet s x / r :=
    (le_div_iff₀ hr).2 (by simpa using hdist)
  rw [boundaryEnergyTent, max_eq_left (by linarith)]

private theorem boundaryEnergy_abs_maxZero_sub_maxZero_le (a b : ℝ) :
    |max 0 a - max 0 b| ≤ |a - b| := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · simp [max_eq_right ha, max_eq_right hb]
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [max_eq_right ha, max_eq_left hb']
    simp only [sub_zero, abs_of_nonneg ha]
    have hsub : 0 ≤ a - b := by linarith
    rw [abs_of_nonneg hsub]
    linarith
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_left ha', max_eq_right hb]
    have hleft : 0 - b ≤ 0 := by linarith
    have hsub : a - b ≤ 0 := by linarith
    rw [abs_of_nonpos hleft, abs_of_nonpos hsub]
    linarith
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have hb' : b ≤ 0 := le_of_not_ge hb
    simp [max_eq_left ha', max_eq_left hb']

theorem boundaryEnergyTent_abs_sub_le (s : Finset (Site L)) (r : ℝ) (hr : 0 < r)
    (x y : Site L) :
    |boundaryEnergyTent s r x - boundaryEnergyTent s r y| ≤
      euclideanSiteDistance x y / r := by
  unfold boundaryEnergyTent
  calc
    |max 0 (1 - boundaryEnergyDistanceToSet s x / r) -
        max 0 (1 - boundaryEnergyDistanceToSet s y / r)| ≤
        |(1 - boundaryEnergyDistanceToSet s x / r) -
          (1 - boundaryEnergyDistanceToSet s y / r)| :=
            boundaryEnergy_abs_maxZero_sub_maxZero_le _ _
    _ = |boundaryEnergyDistanceToSet s x - boundaryEnergyDistanceToSet s y| / r := by
      have hnum : (1 - boundaryEnergyDistanceToSet s x / r) -
          (1 - boundaryEnergyDistanceToSet s y / r) =
          (boundaryEnergyDistanceToSet s y - boundaryEnergyDistanceToSet s x) / r := by
        field_simp
        ring_nf
      rw [hnum, abs_div, abs_of_pos hr, abs_sub_comm]
    _ ≤ euclideanSiteDistance x y / r :=
      div_le_div_of_nonneg_right (boundaryEnergyDistanceToSet_abs_sub_le s x y) hr.le

/-- The Euclidean tent realizes the exact plateau and localization conditions
needed by the selected-square charge-pairing lemma. -/
theorem boundaryEnergy_selectedSquare_tent_pairing_abs_ge_one
    (Miso Msel α : ℝ) (hMiso : 0 < Miso) (hαpos : 0 < α)
    (hα : 1 ≤ α) (hMsel : 1 ≤ Msel)
    (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    (j : ℕ) (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L))) (hC : IsMinimumSquareCover .free L j ρ C)
    (s : Finset (Site L)) (hs : s ∈ pinnedPPrime Msel α j ρ C) :
    1 ≤ |∑ x, boundaryEnergyTent s ((2 : ℝ) ^ j) x * (ρ x : ℝ)| := by
  have hsne : s.Nonempty := by
    obtain ⟨x, hxρ, hxs, -⟩ := minimumCover_square_has_private_support_site j ρ C
      hC ((pinnedPPrime_mem_of_minimumCover Msel α j ρ C hC hs).1)
    exact ⟨x, hxs⟩
  apply boundaryEnergy_selectedSquare_pairing_abs_ge_one Miso Msel α
    hMiso hαpos hα hMsel hmargin j ρ N hN hρ C hC s hs
    (boundaryEnergyTent s ((2 : ℝ) ^ j))
    (fun x hx => boundaryEnergyTent_eq_one_of_mem s _ hx)
    (fun x hxs hfar => boundaryEnergyTent_eq_zero_of_far s hsne _ (by positivity) x hfar)

private theorem boundaryEnergy_minimumCover_eq_singleton
    {A : Type} [DecidableEq A] {C : Finset (Finset A)} {s : Finset A}
    (hcard : C.card = 1) (hs : s ∈ C) : C = {s} := by
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  have hts : s = t := by simpa [ht] using hs
  rw [ht, hts]

/-- A tent centered on the actual charge support has a unit pairing after the
selection-dependent orientation. The one-square override is handled by the
fact that the whole parent support then lies in that square. -/
theorem boundaryEnergy_selectedChildTent_pairing_abs_ge_one
    (Miso Msel α : ℝ) (hMiso : 0 < Miso) (hαpos : 0 < α)
    (hα : 1 ≤ α) (hMsel : 1 ≤ Msel)
    (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    (j : ℕ) (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L))) (hC : IsMinimumSquareCover .free L j ρ C)
    (s : Finset (Site L)) (hs : s ∈ pinnedPPrime Msel α j ρ C) :
    1 ≤ |∑ x, boundaryEnergyTent (chargeSupport (chargeRestriction ρ s))
      ((2 : ℝ) ^ j) x * (ρ x : ℝ)| := by
  classical
  let child := chargeRestriction ρ s
  have hsC : s ∈ C := pinnedPPrime_mem_of_minimumCover Msel α j ρ C hC hs |>.1
  have hconst : IsConstituent ρ child := by
    simpa [child] using boundaryEnergy_squareRestriction_isConstituent j ρ C hC hsC
  have hchildne : child ≠ 0 := hconst.1
  have hsupport : (chargeSupport child).Nonempty :=
    chargeSupport_nonempty_of_ne_zero child hchildne
  have hchildsub : chargeSupport child ⊆ s := by
    intro x hx
    exact (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.1
  have hcharge := boundaryEnergy_selectedSquare_charge Miso Msel α hMiso hαpos
    hmargin j ρ N hN hρ C hC s hs
  have hpoint : ∀ x, boundaryEnergyTent (chargeSupport child) ((2 : ℝ) ^ j) x *
      (ρ x : ℝ) = (child x : ℝ) := by
    intro x
    by_cases hxchild : x ∈ chargeSupport child
    · have hxval : child x ≠ 0 := (Finset.mem_filter.mp hxchild).2
      have hparent : ρ x = child x := hconst.2.2 x hxchild
      rw [boundaryEnergyTent_eq_one_of_mem (chargeSupport child) _ hxchild]
      simp [hparent]
    · have hxzero : child x = 0 := by
        by_contra hne
        exact hxchild (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      by_cases hρx : ρ x = 0
      · simp [hρx, hxzero]
      · have hxρ : x ∈ chargeSupport ρ := by simp [chargeSupport, hρx]
        obtain ⟨t, ht, hxt⟩ := hC.1.2 x hxρ
        have hxs : x ∉ s := by
          intro hmem
          have hval : child x = ρ x := by simp [child, chargeRestriction, hmem]
          have hchildx : child x ≠ 0 := by rw [hval]; exact hρx
          exact hchildx hxzero
        have hts : t ≠ s := by
          intro hEq
          subst t
          exact hxs hxt
        by_cases hsingle : C.card = 1
        · have hcard : C = {s} := boundaryEnergy_minimumCover_eq_singleton hsingle hsC
          have hEq : t = s := by
            rw [hcard] at ht
            simpa using ht
          exact (hts hEq).elim
        · have hsdata :=
            (mem_pinnedPPrime_of_cover_card_ne_one Msel α j ρ C hsingle s).mp hs
          rcases hsdata with ⟨_, hsep, _⟩
          have hbase : 1 ≤ (2 : ℝ) ^ j := boundaryEnergy_one_le_two_pow j
          have hpow : (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ α := by
            calc
              (2 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ (1 : ℝ) :=
                (Real.rpow_one _).symm
              _ ≤ ((2 : ℝ) ^ j) ^ α :=
                Real.rpow_le_rpow_of_exponent_le hbase hα
          have hradius : (2 : ℝ) ^ j <
              2 * Msel * ((2 : ℝ) ^ j) ^ α := by
            have hrpos : 0 < (2 : ℝ) ^ j := by positivity
            nlinarith [mul_nonneg (sub_nonneg.mpr hMsel)
              (Real.rpow_nonneg hrpos.le α), hpow]
          have hscale : ((2 : ℝ) ^ j) ^ α =
              (2 : ℝ) ^ (α * (j : ℝ)) := by
            calc
              ((2 : ℝ) ^ j) ^ α = (2 : ℝ) ^ ((j : ℝ) * α) := by
                rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
              _ = (2 : ℝ) ^ (α * (j : ℝ)) := by
                congr 1
                ring
          have hfar : ∀ y ∈ chargeSupport child,
              (2 : ℝ) ^ j < euclideanSiteDistance y x := by
            intro y hy
            have hsep' := hsep t ht hts
            have hdist := setDist_le_siteDist (hchildsub hy) hxt
            have hR : 2 * Msel * ((2 : ℝ) ^ j) ^ α ≤
                euclideanSetDistance s t := by rw [hscale]; exact hsep'
            exact lt_of_lt_of_le hradius (hR.trans hdist)
          have htent := boundaryEnergyTent_eq_zero_of_far (chargeSupport child)
            hsupport ((2 : ℝ) ^ j) (by positivity) x hfar
          simp [htent, hxzero]
  have hsum :
      (∑ x, boundaryEnergyTent (chargeSupport child) ((2 : ℝ) ^ j) x *
        (ρ x : ℝ)) = (totalCharge child : ℝ) := by
    calc
      _ = ∑ x, (child x : ℝ) := Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = (totalCharge child : ℝ) := by
        simp [totalCharge, child]
  have htotal : totalCharge child ≠ 0 := by simpa [child] using hcharge
  have habs : 0 < |totalCharge child| := abs_pos.mpr htotal
  have hInt : (1 : ℤ) ≤ |totalCharge child| := by omega
  have hReal : (1 : ℝ) ≤ ((|totalCharge child| : ℤ) : ℝ) := by exact_mod_cast hInt
  rw [Int.cast_abs] at hReal
  rw [hsum]
  exact hReal

/-- A selected support tent with the Appendix-D boundary margin vanishes on
every face site at boundary depth one. -/
theorem boundaryEnergy_childTent_zero_at_boundary
    (j : ℕ) (s : Finset (Site L)) (hs : s.Nonempty)
    (hmargin : scaleBoundaryMargin j ≤ euclideanBoundaryDistance s)
    (x : Site L) (hxdepth : siteBoundaryDepth x = 1) :
    boundaryEnergyTent s ((2 : ℝ) ^ j) x = 0 := by
  have hscale : 4 * (2 : ℝ) ^ j ≤ euclideanBoundaryDistance s := by
    have hEq : scaleBoundaryMargin j = 4 * (2 : ℝ) ^ j := by
      unfold scaleBoundaryMargin
      rw [pow_add]
      norm_num
      ring
    rw [← hEq]
    exact hmargin
  have hr : 0 < (2 : ℝ) ^ j := by positivity
  have hbase : 1 ≤ (2 : ℝ) ^ j := boundaryEnergy_one_le_two_pow j
  have hfar : ∀ y ∈ s, (2 : ℝ) ^ j < euclideanSiteDistance y x := by
    intro y hy
    have hyDepth : 4 * (2 : ℝ) ^ j ≤ (siteBoundaryDepth y : ℝ) :=
      hscale.trans (euclideanBoundaryDistance_le_siteDepth_of_mem s hs hy)
    have hxDepth : (siteBoundaryDepth x : ℝ) = 1 := by exact_mod_cast hxdepth
    have hLip := siteBoundaryDepth_lipschitz y x
    have hdist : 4 * (2 : ℝ) ^ j - 1 ≤ euclideanSiteDistance y x := by
      have hle := le_abs_self ((siteBoundaryDepth y : ℝ) - 1)
      rw [hxDepth] at hLip
      linarith
    have hstrict : (2 : ℝ) ^ j < 4 * (2 : ℝ) ^ j - 1 := by nlinarith
    exact hstrict.trans_le hdist
  exact boundaryEnergyTent_eq_zero_of_far s hs _ hr x hfar

/-- The real profile lifted to the wired dual carrier, with exterior value zero. -/
def boundaryEnergyPinnedTent (s : Finset (Site L)) (r : ℝ) :
    RotatorDualFace L → ℝ
  | none => 0
  | some x => boundaryEnergyTent s r x

@[simp] theorem boundaryEnergyPinnedTent_root (s : Finset (Site L)) (r : ℝ) :
    boundaryEnergyPinnedTent s r none = 0 := rfl

theorem boundaryEnergyPinnedTent_zero_at_boundary
    (j : ℕ) (s : Finset (Site L)) (hs : s.Nonempty)
    (hmargin : scaleBoundaryMargin j ≤ euclideanBoundaryDistance s)
    (x : Site L) (hxdepth : siteBoundaryDepth x = 1) :
    boundaryEnergyPinnedTent s ((2 : ℝ) ^ j) (some x) = 0 :=
  boundaryEnergy_childTent_zero_at_boundary j s hs hmargin x hxdepth

private theorem boundaryEnergy_squareFreeEdge_l1 {L : ℕ} (e : SquareFreeEdge L) :
    |(e.1.1.1.val : ℤ) - e.1.2.1.val| +
      |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by
  have hshape :
      ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
        |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) = ({0, 1} : Finset ℤ) := by
    simpa using e.property.2
  have hx : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈ ({0, 1} : Finset ℤ) := by
    have h := congrArg (fun t : Finset ℤ =>
      |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈ t) hshape
    have hm : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈
        ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
          |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) := by simp
    exact h.mp hm
  have hy : |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈ ({0, 1} : Finset ℤ) := by
    have h := congrArg (fun t : Finset ℤ =>
      |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈ t) hshape
    have hm : |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈
        ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
          |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) := by simp
    exact h.mp hm
  have hne : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ≠
      |(e.1.1.2.val : ℤ) - e.1.2.2.val| := by
    intro heq
    have hcard := congrArg Finset.card hshape
    simp [heq] at hcard
  rcases Finset.mem_insert.mp hx with hx | hx
  · rcases Finset.mem_insert.mp hy with hy | hy
    · have hx0 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 0 := by simpa using hx
      have hy0 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 0 := by simpa using hy
      exact (hne (hx0.trans hy0.symm)).elim
    · have hx0 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 0 := by simpa using hx
      have hy1 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by simpa using hy
      simp [hx0, hy1]
  · rcases Finset.mem_insert.mp hy with hy | hy
    · have hx1 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 1 := by simpa using hx
      have hy0 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 0 := by simpa using hy
      simp [hx1, hy0]
    · have hx1 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 1 := by simpa using hx
      have hy1 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by simpa using hy
      exact (hne (hx1.trans hy1.symm)).elim

private theorem boundaryEnergy_squareFreeEdge_euclideanDistance {L : ℕ}
    (e : SquareFreeEdge L) :
    euclideanSiteDistance e.1.1 e.1.2 = 1 := by
  have hL1 := boundaryEnergy_squareFreeEdge_l1 e
  have hdx : |((e.1.1.1.val : ℝ) - e.1.2.1.val)| =
      ((|(e.1.1.1.val : ℤ) - e.1.2.1.val| : ℤ) : ℝ) := by
    norm_cast
  have hdy : |((e.1.1.2.val : ℝ) - e.1.2.2.val)| =
      ((|(e.1.1.2.val : ℤ) - e.1.2.2.val| : ℤ) : ℝ) := by
    norm_cast
  have hsum : |((e.1.1.1.val : ℝ) - e.1.2.1.val)| +
      |((e.1.1.2.val : ℝ) - e.1.2.2.val)| = 1 := by
    exact_mod_cast hL1
  have hsquares : ((e.1.1.1.val : ℝ) - e.1.2.1.val) ^ 2 +
      ((e.1.1.2.val : ℝ) - e.1.2.2.val) ^ 2 = 1 := by
    have hshape :
        ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
          |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) = ({0, 1} : Finset ℤ) := by
      simpa using e.property.2
    have hxMem : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈ ({0, 1} : Finset ℤ) := by
      have hh := congrArg (fun t : Finset ℤ =>
        |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈ t) hshape
      have hm : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈
          ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
            |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) := by simp
      exact hh.mp hm
    have hyMem : |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈ ({0, 1} : Finset ℤ) := by
      have hh := congrArg (fun t : Finset ℤ =>
        |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈ t) hshape
      have hm : |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈
          ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
            |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) := by simp
      exact hh.mp hm
    have hx0or1 : |((e.1.1.1.val : ℝ) - e.1.2.1.val)| = 0 ∨
        |((e.1.1.1.val : ℝ) - e.1.2.1.val)| = 1 := by
      rw [hdx]
      have hxInt : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 0 ∨
          |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 1 := by
        simpa using hxMem
      rcases hxInt with hx0 | hx1
      · exact Or.inl (by exact_mod_cast hx0)
      · exact Or.inr (by exact_mod_cast hx1)
    have hy0or1 : |((e.1.1.2.val : ℝ) - e.1.2.2.val)| = 0 ∨
        |((e.1.1.2.val : ℝ) - e.1.2.2.val)| = 1 := by
      rw [hdy]
      have hyInt : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 0 ∨
          |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by
        simpa using hyMem
      rcases hyInt with hy0 | hy1
      · exact Or.inl (by exact_mod_cast hy0)
      · exact Or.inr (by exact_mod_cast hy1)
    rcases hx0or1 with hx0 | hx1 <;> rcases hy0or1 with hy0 | hy1
    · have : |((e.1.1.1.val : ℝ) - e.1.2.1.val)| +
          |((e.1.1.2.val : ℝ) - e.1.2.2.val)| = 0 := by rw [hx0, hy0]; norm_num
      linarith [hsum]
    · have hdx0 : ((e.1.1.1.val : ℝ) - e.1.2.1.val) = 0 := abs_eq_zero.mp hx0
      have hdySq : ((e.1.1.2.val : ℝ) - e.1.2.2.val) ^ 2 = 1 := by
        nlinarith [sq_abs ((e.1.1.2.val : ℝ) - e.1.2.2.val)]
      rw [hdx0]
      simpa using hdySq
    · have hdy0 : ((e.1.1.2.val : ℝ) - e.1.2.2.val) = 0 := abs_eq_zero.mp hy0
      have hdxSq : ((e.1.1.1.val : ℝ) - e.1.2.1.val) ^ 2 = 1 := by
        nlinarith [sq_abs ((e.1.1.1.val : ℝ) - e.1.2.1.val)]
      rw [hdy0]
      simpa using hdxSq
    · have : |((e.1.1.1.val : ℝ) - e.1.2.1.val)| +
          |((e.1.1.2.val : ℝ) - e.1.2.2.val)| = 2 := by rw [hx1, hy1]; norm_num
      linarith [hsum]
  unfold euclideanSiteDistance
  rw [show Real.sqrt (((e.1.1.1.val : ℝ) - e.1.2.1.val) ^ 2 +
      ((e.1.1.2.val : ℝ) - e.1.2.2.val) ^ 2) = Real.sqrt 1 by rw [hsquares]]
  norm_num

theorem boundaryEnergyTent_gradient_le_on_squareFreeEdge
    (s : Finset (Site L)) (r : ℝ) (hr : 0 < r) (e : SquareFreeEdge L) :
    |boundaryEnergyTent s r e.1.1 - boundaryEnergyTent s r e.1.2| ≤ 1 / r := by
  have h := boundaryEnergyTent_abs_sub_le s r hr e.1.1 e.1.2
  rw [boundaryEnergy_squareFreeEdge_euclideanDistance] at h
  exact h

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
