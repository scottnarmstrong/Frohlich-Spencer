/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.SourceCoercivity
public import FroehlichSpencer.FS82.Moment.Packing

set_option autoImplicit false

/-!
# FS82 LongCurrentEstimate: long-current Jensen error bound

The long-current estimate is assembled from the spectral field bound, current
activity decay, and the finite support count on the actual LambdaStar carrier.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Currents.LongCurrentEstimate

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceCoercivity
open FroehlichSpencer.FS82.Moment.Packing

noncomputable section

/-- A finite current together with its co-closedness witness.  Keeping the
certificate in the carrier makes the physical phase available in every sum
term without choosing it outside the finite family. -/
abbrev ClosedIntegerCurrent (B : SourceBox) :=
  {j : IntegerCurrent B // currentDivergence j = 0}

theorem abs_field_coordinate_le_norm {B : SourceBox}
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (e : SourceDualOneCells B) :
    |τ e| ≤ ‖τ‖ := by
  calc
    |τ e| = ‖τ e‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖τ‖ := PiLp.norm_apply_le τ e

/-- The physical-current phase in the C2 lattice orientation. -/
noncomputable def latticeCurrentPhase {B : SourceBox}
    (origin : Fin 4 → ℤ) (j : IntegerCurrent B)
    (hdiv : currentDivergence j = 0)
    (τ : coClosed (latticeExactOneComplex (B := B) origin)) : ℝ :=
  inner ℝ (sourcePhysicalCurrentCoClosed origin j hdiv :
      EuclideanSpace ℝ (SourceDualOneCells B))
    (τ : EuclideanSpace ℝ (SourceDualOneCells B))

private theorem sourcePhysicalCurrentVector_apply' {B : SourceBox}
    (j : IntegerCurrent B) (e : SourceDualOneCells B) :
    sourcePhysicalCurrentVector j e = (2 * Real.pi) * (j e : ℝ) := by
  simp only [sourcePhysicalCurrentVector, finsuppToEuclidean_apply,
    compressDualSubtype_apply, physicalCurrent]
  change Finsupp.embDomain
      (⟨Subtype.val, Subtype.val_injective⟩ : Link B ↪ Cubical.DualCell 4 B)
      _ ((⟨Subtype.val, Subtype.val_injective⟩ :
        Link B ↪ Cubical.DualCell 4 B) e) = _
  rw [Finsupp.embDomain_apply_self]
  simp


theorem latticeCurrentPhase_abs_le
    {B : SourceBox} (origin : Fin 4 → ℤ)
    (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    (τ : coClosed (latticeExactOneComplex (B := B) origin)) :
    |latticeCurrentPhase origin j hdiv τ| ≤
      (2 * Real.pi) * ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ *
        (∑ e : Link B, |(j e : ℝ)|) := by
  let v := sourcePhysicalCurrentVector j
  let tw := sourceDualTLinear v
  have hphase : latticeCurrentPhase origin j hdiv τ =
      inner ℝ tw (τ : EuclideanSpace ℝ (SourceDualOneCells B)) := by
    rfl
  have hinner :
      inner ℝ tw (τ : EuclideanSpace ℝ (SourceDualOneCells B)) =
        ∑ e : SourceDualOneCells B, tw e *
          (τ : EuclideanSpace ℝ (SourceDualOneCells B)) e := by
    rw [PiLp.inner_apply]
    simp [mul_comm]
  have hcoord (e : SourceDualOneCells B) :
      tw e = dualCellOrientationSign e.1 * ((2 * Real.pi) * (j e : ℝ)) := by
    change sourceDualTLinear (sourcePhysicalCurrentVector j) e = _
    rw [sourceDualTLinear_apply, sourcePhysicalCurrentVector_apply']
  have hsign (e : SourceDualOneCells B) :
      |dualCellOrientationSign e.1| = 1 := by
    have hs := dualCellOrientationSign_sq e
    have habs : |dualCellOrientationSign e.1| ^ 2 = 1 := by
      rw [sq_abs]
      exact hs
    nlinarith [abs_nonneg (dualCellOrientationSign e.1)]
  have hpoint (e : Link B) :
      |tw e * (τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| =
        (2 * Real.pi) * |(j e : ℝ)| *
          |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := by
    calc
      |tw e * (τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| =
          |dualCellOrientationSign e.1| * |(2 * Real.pi) * (j e : ℝ)| *
            |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := by
              rw [hcoord e, abs_mul, abs_mul]
      _ = (2 * Real.pi) * |(j e : ℝ)| *
          |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := by
            rw [hsign e, abs_mul,
              abs_of_pos (by positivity : 0 < 2 * Real.pi)]
            ring
  have hsum' :
      (∑ e : SourceDualOneCells B,
        |tw e * (τ : EuclideanSpace ℝ (SourceDualOneCells B)) e|) =
        (2 * Real.pi) *
          ∑ e : Link B, |(j e : ℝ)| *
            |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := by
    calc
      (∑ e : SourceDualOneCells B,
          |tw e * (τ : EuclideanSpace ℝ (SourceDualOneCells B)) e|) =
          ∑ e : Link B, (2 * Real.pi) * |(j e : ℝ)| *
            |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := by
              apply Finset.sum_congr rfl
              intro e he
              exact hpoint e
      _ = (2 * Real.pi) *
          ∑ e : Link B, |(j e : ℝ)| *
            |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e he
              ring
  have hfield :
      (∑ e : Link B, |(j e : ℝ)| *
        |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e|) ≤
        ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ *
          ∑ e : Link B, |(j e : ℝ)| := by
    calc
      (∑ e : Link B, |(j e : ℝ)| *
          |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e|) ≤
          ∑ e : Link B, |(j e : ℝ)| *
            ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ := by
              apply Finset.sum_le_sum
              intro e he
              exact mul_le_mul_of_nonneg_left
                (abs_field_coordinate_le_norm _ e) (abs_nonneg _)
      _ = ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ *
          ∑ e : Link B, |(j e : ℝ)| := by
            simpa [mul_comm] using
              (Finset.sum_mul (Finset.univ : Finset (Link B))
                (fun e => |(j e : ℝ)|)
                ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖).symm
  calc
    |latticeCurrentPhase origin j hdiv τ| =
        |inner ℝ tw (τ : EuclideanSpace ℝ (SourceDualOneCells B))| := by
          rw [hphase]
    _ = |∑ e : SourceDualOneCells B,
          tw e * (τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := by
          rw [hinner]
    _ ≤ ∑ e : SourceDualOneCells B,
          |tw e * (τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = (2 * Real.pi) *
          ∑ e : Link B, |(j e : ℝ)| *
            |(τ : EuclideanSpace ℝ (SourceDualOneCells B)) e| := hsum'
    _ ≤ (2 * Real.pi) *
          (‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ *
            ∑ e : Link B, |(j e : ℝ)|) :=
          mul_le_mul_of_nonneg_left hfield (by positivity)
    _ = (2 * Real.pi) * ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖ *
          (∑ e : Link B, |(j e : ℝ)|) := by ring

/-- The squared current 1-norm is bounded by support length times the
squared 2-norm. -/
theorem integerCurrent_l1_sq_le_support_mul_normSq
    {B : SourceBox} (j : IntegerCurrent B) :
    (∑ e : Link B, |(j e : ℝ)|)^2 ≤
      ((currentSupport (fun e : Link B => j e)).card : ℝ) *
        integerCurrentNormSq (fun e : Link B => j e) := by
  classical
  let S := currentSupport (fun e : Link B => j e)
  have hL1 : (∑ e : Link B, |(j e : ℝ)|) =
      ∑ e ∈ S, |(j e : ℝ)| := by
    exact (Finset.sum_subset (Finset.subset_univ S) (by
      intro e he hnot
      have hz : j e = 0 := by
        by_contra hne
        exact hnot (by simp [S, currentSupport, hne])
      simp [hz])).symm
  have hSq : (∑ e ∈ S, ((j e : ℝ))^2) =
      integerCurrentNormSq (fun e : Link B => j e) := by
    unfold S integerCurrentNormSq
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e he hnot
    have hz : j e = 0 := by
      by_contra hne
      exact hnot (by simp [currentSupport, hne])
    simp [hz]
  rw [hL1]
  calc
    (∑ e ∈ S, |(j e : ℝ)|)^2 ≤
        (∑ e ∈ S, |(j e : ℝ)|^2) * ∑ e ∈ S, (1 : ℝ)^2 := by
          simpa only [mul_one] using Finset.sum_mul_sq_le_sq_mul_sq S
            (fun e => |(j e : ℝ)|) (fun _ => 1)
    _ = ((currentSupport (fun e : Link B => j e)).card : ℝ) *
        integerCurrentNormSq (fun e : Link B => j e) := by
          rw [← hSq]
          simp
          ring

theorem x_mul_exp_neg_le_inv_ae (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    x * Real.exp (-(a * x)) ≤ 1 / (a * Real.exp 1) := by
  let u : ℝ := a * x
  have hu0 : 0 ≤ u := mul_nonneg ha.le hx
  by_cases huZero : u = 0
  · have hxZero : x = 0 := by
      dsimp [u] at huZero
      nlinarith
    simp [hxZero]
    positivity
  have hu : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huZero)
  have hlog := Real.log_le_sub_one_of_pos hu
  have hmajor : u ≤ Real.exp (u - 1) := by
    calc
      u = Real.exp (Real.log u) := (Real.exp_log hu).symm
      _ ≤ Real.exp (u - 1) := (Real.exp_le_exp).2 hlog
  have hbase : u * Real.exp (-u) ≤ 1 / Real.exp 1 := by
    calc
      u * Real.exp (-u) ≤ Real.exp (u - 1) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hmajor (Real.exp_pos _).le
      _ = Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  have hrewrite : x * Real.exp (-(a * x)) =
      (u * Real.exp (-u)) / a := by
    dsimp [u]
    field_simp [ne_of_gt ha]
  rw [hrewrite]
  calc
    (u * Real.exp (-u)) / a ≤ (1 / Real.exp 1) / a :=
      div_le_div_of_nonneg_right hbase ha.le
    _ = 1 / (a * Real.exp 1) := by field_simp [ne_of_gt ha]

/-- For a≥1, the weighted exponential tail decreases on integer lengths
starting at m≥1. -/
theorem natLength_mul_exp_neg_le
    (a : ℝ) (L m : ℕ) (ha : 1 ≤ a) (hm : 1 ≤ m) (hmL : m ≤ L) :
    (L : ℝ) * Real.exp (-(a * L)) ≤
      (m : ℝ) * Real.exp (-(a * m)) := by
  let d : ℝ := (L : ℝ) - m
  have hd : 0 ≤ d := by
    dsimp [d]
    have hcast : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hmL
    linarith
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hL : (L : ℝ) = (m : ℝ) + d := by
    dsimp [d]
    ring
  have hmul : (L : ℝ) ≤ (m : ℝ) * (1 + a * d) := by
    rw [hL]
    have ha0 : 0 ≤ a := by linarith
    nlinarith [mul_nonneg (show 0 ≤ a - 1 by linarith) hd,
      mul_nonneg (sub_nonneg.mpr hmR)
        (mul_nonneg (show 0 ≤ a by linarith) hd)]
  have hexp : 1 + a * d ≤ Real.exp (a * d) := by
    linarith [Real.add_one_le_exp (a * d)]
  have hfirst : (L : ℝ) ≤ (m : ℝ) * Real.exp (a * d) := by
    calc
      (L : ℝ) ≤ (m : ℝ) * (1 + a * d) := hmul
      _ ≤ (m : ℝ) * Real.exp (a * d) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
  calc
    (L : ℝ) * Real.exp (-(a * L)) ≤
        ((m : ℝ) * Real.exp (a * d)) * Real.exp (-(a * L)) :=
      mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
    _ = (m : ℝ) * Real.exp (-(a * m)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      rw [hL]
      ring_nf

/-- On the sharper small-activity range, the exact Jensen coefficient is at
most z. -/
theorem jensenGamma_le_self_of_le_eighth (z : ℝ)
    (hz0 : 0 ≤ z) (hz : z ≤ 1 / 8) :
    jensenGamma z ≤ z := by
  have hden : 0 < 1 - z := by linarith
  have hden1 : 0 < 2 * (1 - z) := by positivity
  have hden2 : 0 < (1 - z)^2 := sq_pos_of_pos hden
  have hlow : (7 / 8 : ℝ) ≤ 1 - z := by linarith
  have hterm1 : z / (2 * (1 - z)) ≤ (4 / 7) * z := by
    apply (div_le_iff₀ hden1).2
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hlow)]
  have hdenSq : (7 / 8 : ℝ)^2 ≤ (1 - z)^2 := by
    exact (sq_le_sq₀ (by norm_num) (by positivity)).2 hlow
  have hterm2 : 2 * z^2 / (1 - z)^2 ≤ (128 / 49) * z^2 := by
    apply (div_le_iff₀ hden2).2
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hdenSq)]
  have hquad : (128 / 49 : ℝ) * z^2 ≤ (16 / 49) * z := by
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz)]
  unfold jensenGamma
  calc
    z / (2 * (1 - z)) + 2 * z^2 / (1 - z)^2 ≤
        (4 / 7) * z + (16 / 49) * z := add_le_add hterm1 (le_trans hterm2 hquad)
    _ ≤ z := by nlinarith [mul_nonneg (sub_nonneg.mpr hz0) (by norm_num : (0 : ℝ) ≤ 5 / 49)]

/-- An exact coarse carrier count from the unique orientation axis and four
coordinate ranges. -/
private def longCurrentLinkAxis {B : SourceBox} (c : Link B) : Fin 4 :=
  Classical.choose (Finset.card_eq_one.mp c.2)

private theorem longCurrentLinkAxes_eq_singleton {B : SourceBox} (c : Link B) :
    dualCellAxes c.1 = {longCurrentLinkAxis c} :=
  Classical.choose_spec (Finset.card_eq_one.mp c.2)

private theorem longCurrentLinkAxis_mem {B : SourceBox} (c : Link B) :
    longCurrentLinkAxis c ∈ dualCellAxes c.1 := by
  rw [longCurrentLinkAxes_eq_singleton]
  simp

private theorem longCurrentLinkCoord_isRight_iff_axis {B : SourceBox}
    (c : Link B) (j : Fin 4) :
    (c.1 j).isRight ↔ j = longCurrentLinkAxis c := by
  constructor
  · intro hj
    have hjmem : j ∈ dualCellAxes c.1 := by
      simpa [dualCellAxes] using hj
    rw [longCurrentLinkAxes_eq_singleton] at hjmem
    simpa using hjmem
  · intro hj
    subst j
    have hmem := longCurrentLinkAxis_mem c
    simpa [dualCellAxes] using hmem

private def longCurrentLinkCoordinateKey {B : SourceBox} {N : ℕ}
    (hB : ∀ i : Fin 4, B i ≤ N) (c : Link B) (j : Fin 4) : Fin (N + 1) :=
  match c.1 j with
  | Sum.inl v => Fin.castLE (Nat.le_succ_of_le (hB j)) v
  | Sum.inr e => Fin.castLE (Nat.succ_le_succ (hB j)) e

private def longCurrentLinkEncode {B : SourceBox} {N : ℕ}
    (hB : ∀ i : Fin 4, B i ≤ N) (c : Link B) :
    Fin 4 × (Fin 4 → Fin (N + 1)) :=
  (longCurrentLinkAxis c, longCurrentLinkCoordinateKey hB c)

private theorem longCurrentLinkEncode_injective {B : SourceBox} {N : ℕ}
    (hB : ∀ i : Fin 4, B i ≤ N) :
    Function.Injective (longCurrentLinkEncode hB) := by
  intro c d h
  apply Subtype.ext
  apply funext
  intro j
  have haxis : longCurrentLinkAxis c = longCurrentLinkAxis d := congrArg Prod.fst h
  have hcoords := congrArg Prod.snd h
  have hcoord := congrFun hcoords j
  by_cases hja : j = longCurrentLinkAxis c
  · subst j
    have hcr : (c.1 (longCurrentLinkAxis c)).isRight :=
      (longCurrentLinkCoord_isRight_iff_axis c (longCurrentLinkAxis c)).2 rfl
    have hdr : (d.1 (longCurrentLinkAxis c)).isRight :=
      (longCurrentLinkCoord_isRight_iff_axis d (longCurrentLinkAxis c)).2 haxis
    cases hcj : c.1 (longCurrentLinkAxis c) with
    | inl v => simp [hcj] at hcr
    | inr e =>
      cases hdj : d.1 (longCurrentLinkAxis c) with
      | inl w => simp [hdj] at hdr
      | inr f =>
        have heq : Fin.castLE (Nat.succ_le_succ (hB (longCurrentLinkAxis c))) e =
            Fin.castLE (Nat.succ_le_succ (hB (longCurrentLinkAxis c))) f := by
          simpa [longCurrentLinkEncode, longCurrentLinkCoordinateKey, hcj, hdj] using hcoord
        have hv := congrArg Fin.val heq
        have hef : e = f := Fin.ext (by simpa using hv)
        exact congrArg Sum.inr hef
  · have hcr : ¬ (c.1 j).isRight := by
      intro hj
      exact hja ((longCurrentLinkCoord_isRight_iff_axis c j).1 hj)
    have hdr : ¬ (d.1 j).isRight := by
      intro hj
      apply hja
      rw [haxis]
      exact (longCurrentLinkCoord_isRight_iff_axis d j).1 hj
    cases hcj : c.1 j with
    | inl v =>
      cases hdj : d.1 j with
      | inl w =>
        have heq : Fin.castLE (Nat.le_succ_of_le (hB j)) v =
            Fin.castLE (Nat.le_succ_of_le (hB j)) w := by
          simpa [longCurrentLinkEncode, longCurrentLinkCoordinateKey, hcj, hdj] using hcoord
        have hv := congrArg Fin.val heq
        have hvw : v = w := Fin.ext (by simpa using hv)
        change Sum.inl v = Sum.inl w
        exact congrArg Sum.inl hvw
      | inr f => simp [hdj] at hdr
    | inr e => simp [hcj] at hcr

/-- Every dual link is encoded by its axis and four bounded coordinates. -/
theorem sourceDualOneCells_card_le_4 {B : SourceBox} {N : ℕ}
    (hB : ∀ i : Fin 4, B i ≤ N) :
    Fintype.card (SourceDualOneCells B) ≤ 4 * (N + 1)^4 := by
  calc
    Fintype.card (SourceDualOneCells B) ≤
        Fintype.card (Fin 4 × (Fin 4 → Fin (N + 1))) :=
      Fintype.card_le_of_injective (longCurrentLinkEncode hB) (longCurrentLinkEncode_injective hB)
    _ = 4 * (N + 1)^4 := by simp [Fintype.card_prod]

/-- One long current contributes at most its length tail times the squared field norm.
This is the explicit Jensen estimate before the finite-family entropy count. -/
theorem longCurrent_single_jensen_error
    {B : SourceBox} (origin : Fin 4 → ℤ)
    (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    (τ : coClosed (latticeExactOneComplex (B := B) origin))
    (a z : ℝ) (hm : 1 ≤ (currentSupport (fun e : Link B => j e)).card)
    (ha : 8 ≤ a) (hz0 : 0 ≤ z)
    (hz : z ≤ Real.exp (-(a *
      (integerCurrentNormSq (fun e : Link B => j e) +
        ((currentSupport (fun e : Link B => j e)).card : ℝ))))) :
    jensenGamma z * (latticeCurrentPhase origin j hdiv τ)^2 ≤
      (4 * Real.pi^2 / (a * Real.exp 1)) *
        ((currentSupport (fun e : Link B => j e)).card : ℝ) *
        Real.exp (-(a * (currentSupport (fun e : Link B => j e)).card)) *
        ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
  let x : ℝ := integerCurrentNormSq (fun e : Link B => j e)
  let L : ℕ := (currentSupport (fun e : Link B => j e)).card
  let M : ℝ := ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hx : 0 ≤ x := by
    dsimp [x, integerCurrentNormSq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL : 1 ≤ (L : ℝ) := by
    dsimp [L]
    exact_mod_cast hm
  have hz' : z ≤ Real.exp (-(a * (x + (L : ℝ)))) := by
    simpa [x, L] using hz
  have harg : -(a * (x + (L : ℝ))) ≤ -8 := by
    have hsum : 1 ≤ x + (L : ℝ) := by linarith
    have hprod : 8 ≤ a * (x + (L : ℝ)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hsum)]
    linarith
  have hexp8 : 8 ≤ Real.exp (8 : ℝ) := by
    linarith [Real.add_one_le_exp (8 : ℝ)]
  have hexpNeg8 : Real.exp (-(8 : ℝ)) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    have hfrac : 1 / Real.exp (8 : ℝ) ≤ 1 / 8 := by
      apply (div_le_iff₀ (Real.exp_pos (8 : ℝ))).2
      nlinarith [hexp8]
    simpa [one_div] using hfrac
  have hsmall : z ≤ 1 / 8 :=
    le_trans hz' (le_trans (Real.exp_le_exp.mpr harg) hexpNeg8)
  have hgamma : jensenGamma z ≤ z :=
    jensenGamma_le_self_of_le_eighth z hz0 hsmall
  have hphase := latticeCurrentPhase_abs_le origin j hdiv τ
  have hL1 := integerCurrent_l1_sq_le_support_mul_normSq j
  have hL1' : (∑ e : Link B, |(j e : ℝ)|)^2 ≤ (L : ℝ) * x := by
    simpa [L, x] using hL1
  have hphaseSq : (latticeCurrentPhase origin j hdiv τ)^2 ≤
      (2 * Real.pi)^2 * M^2 * (∑ e : Link B, |(j e : ℝ)|)^2 := by
    have hbound : 0 ≤ (2 * Real.pi) * M *
        (∑ e : Link B, |(j e : ℝ)|) := by positivity
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hbound).2 hphase
    rw [sq_abs] at hsquare
    dsimp [M]
    nlinarith [hsquare]
  have htail := x_mul_exp_neg_le_inv_ae a x ha0 hx
  have hlength := natLength_mul_exp_neg_le a L 1 ha1 (by norm_num) (by
    dsimp [L]
    exact hm)
  have hexpSplit : Real.exp (-(a * (x + (L : ℝ)))) =
      Real.exp (-(a * x)) * Real.exp (-(a * (L : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hLexp : 0 ≤ (L : ℝ) * Real.exp (-(a * (L : ℝ))) := by positivity
  have hnorm : 0 ≤ M^2 := sq_nonneg M
  have hcalc : jensenGamma z * (latticeCurrentPhase origin j hdiv τ)^2 ≤
      (4 * Real.pi^2 / (a * Real.exp 1)) *
        ((L : ℝ) * Real.exp (-(a * (L : ℝ)))) * M^2 := by
    calc
      jensenGamma z * (latticeCurrentPhase origin j hdiv τ)^2 ≤
          z * (latticeCurrentPhase origin j hdiv τ)^2 :=
            mul_le_mul_of_nonneg_right hgamma (sq_nonneg _)
      _ ≤ z * ((2 * Real.pi)^2 * M^2 *
          (∑ e : Link B, |(j e : ℝ)|)^2) :=
            mul_le_mul_of_nonneg_left hphaseSq (by positivity)
      _ ≤ (4 * Real.pi^2) * M^2 * z * ((L : ℝ) * x) := by
            calc
              z * ((2 * Real.pi)^2 * M^2 *
                  (∑ e : Link B, |(j e : ℝ)|)^2) =
                  (z * (2 * Real.pi)^2 * M^2) *
                    (∑ e : Link B, |(j e : ℝ)|)^2 := by ring
              _ ≤ (z * (2 * Real.pi)^2 * M^2) * ((L : ℝ) * x) :=
                  mul_le_mul_of_nonneg_left hL1' (by positivity)
              _ = (4 * Real.pi^2) * M^2 * z * ((L : ℝ) * x) := by ring
      _ ≤ (4 * Real.pi^2) * M^2 *
            Real.exp (-(a * (x + (L : ℝ)))) * ((L : ℝ) * x) := by
            calc
              (4 * Real.pi^2) * M^2 * z * ((L : ℝ) * x) =
                  ((4 * Real.pi^2) * M^2) * (z * ((L : ℝ) * x)) := by ring
              _ ≤ ((4 * Real.pi^2) * M^2) *
                  (Real.exp (-(a * (x + (L : ℝ)))) * ((L : ℝ) * x)) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hz' (by positivity)) (by positivity)
              _ = (4 * Real.pi^2) * M^2 *
                  Real.exp (-(a * (x + (L : ℝ)))) * ((L : ℝ) * x) := by ring
      _ = (4 * Real.pi^2) * M^2 *
            (x * Real.exp (-(a * x))) *
            ((L : ℝ) * Real.exp (-(a * (L : ℝ)))) := by
              rw [hexpSplit]
              ring
      _ ≤ (4 * Real.pi^2) * M^2 *
            (1 / (a * Real.exp 1)) *
            ((L : ℝ) * Real.exp (-(a * (L : ℝ)))) := by
              have hmul := mul_le_mul_of_nonneg_right htail hLexp
              have hmul' := mul_le_mul_of_nonneg_left hmul
                (by positivity : 0 ≤ (4 * Real.pi^2) * M^2)
              nlinarith [hmul']
      _ = (4 * Real.pi^2 / (a * Real.exp 1)) *
            ((L : ℝ) * Real.exp (-(a * (L : ℝ)))) * M^2 := by ring
  convert hcalc using 1
  ring

/-- Disjoint long-current supports occupy at most the carrier cardinality divided
by their minimum length. -/
theorem longCurrent_family_card_le
    {B : SourceBox} {N m : ℕ}
    (T : Finset (ClosedIntegerCurrent B))
    (hB : ∀ i : Fin 4, B i ≤ N)
    (hm : 1 ≤ m)
    (hdisj : (↑T : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
      (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hlong : ∀ j ∈ T,
      m ≤ (currentSupport (fun e : Link B => j.1 e)).card) :
    (T.card : ℝ) ≤ 4 * (N + 1 : ℝ)^4 / m := by
  classical
  let S : ClosedIntegerCurrent B → Finset (Link B) :=
    fun j => currentSupport (fun e : Link B => j.1 e)
  have hmul : T.card * m ≤ Fintype.card (Link B) := by
    have hunion : (T.biUnion S).card = ∑ j ∈ T, (S j).card := by
      simpa [S] using (Finset.card_biUnion hdisj)
    calc
      T.card * m = ∑ j ∈ T, m := by simp
      _ ≤ ∑ j ∈ T, (S j).card := by
        apply Finset.sum_le_sum
        intro j hj
        exact hlong j hj
      _ = (T.biUnion S).card := hunion.symm
      _ ≤ (Finset.univ : Finset (Link B)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (Link B) := Finset.card_univ
  have hnat : T.card * m ≤ 4 * (N + 1)^4 :=
    le_trans hmul (sourceDualOneCells_card_le_4 hB)
  have hreal : (T.card : ℝ) * m ≤ 4 * (N + 1 : ℝ)^4 := by
    exact_mod_cast hnat
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hm)
  have hdiv := div_le_div_of_nonneg_right hreal (le_of_lt hmpos)
  have hrewrite : (T.card : ℝ) = ((T.card : ℝ) * m) / m := by
    field_simp [ne_of_gt hmpos]
  rw [hrewrite]
  exact hdiv

/-- Sum of long-current errors under a supplied inverse-norm bound.  The
Poincare estimate is an explicit input so this lemma can be assembled with the
box spectral gap. -/
theorem longCurrent_jensen_error_of_poincare
    {B : SourceBox} (origin : Fin 4 → ℤ) (N m : ℕ) (a c : ℝ)
    (T : Finset (ClosedIntegerCurrent B))
    (τ : coClosed (latticeExactOneComplex (B := B) origin))
    (z : IntegerCurrent B → ℝ)
    (hBmax : ∀ i : Fin 4, B i ≤ N)
    (hm : 1 ≤ m) (ha : 8 ≤ a) (hc : 0 < c)
    (hdisj : (↑T : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
      (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hlong : ∀ j ∈ T,
      m ≤ (currentSupport (fun e : Link B => j.1 e)).card)
    (hz0 : ∀ j ∈ T, 0 ≤ z j.1)
    (hz : ∀ j ∈ T,
      z j.1 ≤ Real.exp (-(a *
        (integerCurrentNormSq (fun e : Link B => j.1 e) +
          ((currentSupport (fun e : Link B => j.1 e)).card : ℝ)))))
    (hPoincare :
      ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 ≤
        ((N + 1 : ℝ)^2 / c) *
          ‖(latticeExactOneComplex (B := B) origin).d₁
            (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2) :
    (∑ j ∈ T, jensenGamma (z j.1) *
      (latticeCurrentPhase origin j.1 j.2 τ)^2) ≤
      (16 * Real.pi^2 / (c * a * Real.exp 1)) *
        (N + 1 : ℝ)^6 * Real.exp (-(a * m)) *
        ‖(latticeExactOneComplex (B := B) origin).d₁
          (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
  classical
  let pref : ℝ := (4 * Real.pi^2 / (a * Real.exp 1)) *
    (m : ℝ) * Real.exp (-(a * m))
  have hcount := longCurrent_family_card_le T hBmax hm hdisj hlong
  have hsum :
      (∑ j ∈ T, jensenGamma (z j.1) *
        (latticeCurrentPhase origin j.1 j.2 τ)^2) ≤
        (T.card : ℝ) * pref *
          ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
    calc
      (∑ j ∈ T, jensenGamma (z j.1) *
        (latticeCurrentPhase origin j.1 j.2 τ)^2) ≤
          ∑ j ∈ T, pref *
            ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hL : 1 ≤ (currentSupport (fun e : Link B => j.1 e)).card :=
                le_trans hm (hlong j hj)
              have hloc := longCurrent_single_jensen_error origin j.1 j.2 τ a
                (z j.1) hL ha
                (hz0 j hj) (hz j hj)
              have hlength := natLength_mul_exp_neg_le a
                (currentSupport (fun e : Link B => j.1 e)).card m
                (by linarith) hm (hlong j hj)
              dsimp [pref]
              have hnorm := sq_nonneg
                (‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖)
              have hlength' := mul_le_mul_of_nonneg_left hlength
                (by positivity : 0 ≤ 4 * Real.pi^2 / (a * Real.exp 1))
              nlinarith [hloc, hlength']
      _ = (T.card : ℝ) * (pref *
          ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2) := by simp
      _ = (T.card : ℝ) * pref *
          ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by ring
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hm)
  have ha0 : 0 < a := by linarith
  have hnorm : ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 ≤
      ((N + 1 : ℝ)^2 / c) *
        ‖(latticeExactOneComplex (B := B) origin).d₁
          (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := hPoincare
  have hcoef :
      (4 * (N + 1 : ℝ)^4 / m) *
        ((4 * Real.pi^2 / (a * Real.exp 1)) * (m : ℝ) *
          Real.exp (-(a * m))) =
      (16 * Real.pi^2 / (a * Real.exp 1)) *
        (N + 1 : ℝ)^4 * Real.exp (-(a * m)) := by
    field_simp [ne_of_gt hmpos, ne_of_gt ha0]
    ring
  calc
    (∑ j ∈ T, jensenGamma (z j.1) *
      (latticeCurrentPhase origin j.1 j.2 τ)^2) ≤
        (T.card : ℝ) * pref *
          ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := hsum
    _ ≤ (4 * (N + 1 : ℝ)^4 / m) * pref *
          ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
        dsimp [pref]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcount (by positivity)) (by positivity)
    _ = (16 * Real.pi^2 / (a * Real.exp 1)) *
        (N + 1 : ℝ)^4 * Real.exp (-(a * m)) *
        ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
        rw [← hcoef]
    _ ≤ (16 * Real.pi^2 / (a * Real.exp 1)) *
        (N + 1 : ℝ)^4 * Real.exp (-(a * m)) *
        (((N + 1 : ℝ)^2 / c) *
          ‖(latticeExactOneComplex (B := B) origin).d₁
            (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (16 * Real.pi^2 / (c * a * Real.exp 1)) *
        (N + 1 : ℝ)^6 * Real.exp (-(a * m)) *
        ‖(latticeExactOneComplex (B := B) origin).d₁
          (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
        field_simp [ne_of_gt hc, ne_of_gt ha0]

/-- Ready-to-assemble c=1 form: apply the exported discrete Poincare theorem
to supply `hPoincare`, then this is the long-current Jensen estimate. -/
theorem longCurrent_jensen_error_c1_of_poincare
    {B : SourceBox} (origin : Fin 4 → ℤ) (N m : ℕ) (a : ℝ)
    (T : Finset (ClosedIntegerCurrent B))
    (τ : coClosed (latticeExactOneComplex (B := B) origin))
    (z : IntegerCurrent B → ℝ)
    (hBmax : ∀ i : Fin 4, B i ≤ N)
    (hm : 1 ≤ m) (ha : 8 ≤ a)
    (hdisj : (↑T : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
      (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hlong : ∀ j ∈ T,
      m ≤ (currentSupport (fun e : Link B => j.1 e)).card)
    (hz0 : ∀ j ∈ T, 0 ≤ z j.1)
    (hz : ∀ j ∈ T,
      z j.1 ≤ Real.exp (-(a *
        (integerCurrentNormSq (fun e : Link B => j.1 e) +
          ((currentSupport (fun e : Link B => j.1 e)).card : ℝ)))))
    (hPoincare :
      ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 ≤
        (N + 1 : ℝ)^2 *
          ‖(latticeExactOneComplex (B := B) origin).d₁
            (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2) :
    (∑ j ∈ T, jensenGamma (z j.1) *
      (latticeCurrentPhase origin j.1 j.2 τ)^2) ≤
      (16 * Real.pi^2 / (a * Real.exp 1)) *
        (N + 1 : ℝ)^6 * Real.exp (-(a * m)) *
        ‖(latticeExactOneComplex (B := B) origin).d₁
          (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
  have hP :
      ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 ≤
        ((N + 1 : ℝ)^2 / 1) *
          ‖(latticeExactOneComplex (B := B) origin).d₁
            (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
    simpa using hPoincare
  have h := longCurrent_jensen_error_of_poincare
    (origin := origin) (N := N) (m := m) (a := a) (c := 1)
    T τ z hBmax hm ha (by norm_num) hdisj hlong hz0 hz hP
  simpa using h


end
end FroehlichSpencer.FS82.Currents.LongCurrentEstimate
