/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.SOSLiteralDiffLaw
public import FroehlichSpencer.BKT.Surface.SOSLiteralLimit
public import FroehlichSpencer.BKT.SOS.Literal.LimitTheorem
public import FroehlichSpencer.BKT.SOS.Literal.LimitDomination
public import FroehlichSpencer.BKT.Bridge.SOSDirichlet
public import Mathlib.Probability.Notation
import Mathlib.Tactic

/-!
The (C.1) `sosInterpolation` is the internal `(Interp.sosInterp β t).re`
(`sosInterpolation_eq`).

The one-site box is a probability by hand
,
and the subtype lemmas pass the comb-inserted SOS construction's limits to the limit predicate.

The gate and the root are
proved in `BKT/Provider/`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.SOSLiteral

open FroehlichSpencer.BKT FroehlichSpencer.BKT.SOS.Literal
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site)
open FroehlichSpencer.BKT.SOS.Roughening (pinnedGrad pinnedField)
open FroehlichSpencer.BKT.Bridge.SOSDirichlet (summable_exp_neg_abs_int)

/-! ### The interpolation and the bond weight -/

theorem sosInterpolation_eq {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    sosInterpolation β hβ t = (SOS.Interp.sosInterp β t).re := by
  rw [sosInterp_re_eq hβ.le, Ew_eq]
  rfl

theorem prod_sosInterpolation_eq {L : ℕ} {β : ℝ} (hβ : 0 < β) (φ : Site L → ℝ) :
    ∏ e, sosInterpolation β hβ (((squareZero L).src e).elim 0 φ - ((squareZero L).tgt e).elim 0 φ) =
      boxWeight L β φ := by
  unfold boxWeight
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [sosInterpolation_eq, SOS.Roughening.pinnedGrad_apply]
  rfl

/-! ### The box and the plane -/

/-- The box `[-R, R]²`. -/
abbrev planeBox (R : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R

/-- The plane site of a box site. -/
def plane (R : ℕ) (x : Fin (2 * R + 1) × Fin (2 * R + 1)) : ℤ × ℤ :=
  (((x.1 : ℕ) : ℤ) - R, ((x.2 : ℕ) : ℤ) - R)

theorem half (R : ℕ) : (2 * R + 1) / 2 = R := by omega

theorem centeredSite_plane (R : ℕ) (x : Site (2 * R + 1)) :
    centeredSite (2 * R) (plane R x) = x := by
  have h1 := x.1.isLt
  have h2 := x.2.isLt
  ext
  · simp only [centeredSite, plane, Fin.val_ofNat, half, sub_add_cancel, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt h1
  · simp only [centeredSite, plane, Fin.val_ofNat, half, sub_add_cancel, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt h2

theorem centeredSite_val' (R : ℕ) {z : ℤ × ℤ} (hz : z ∈ planeBox R) :
    ((centeredSite (2 * R) z).1.val : ℤ) = z.1 + R ∧
      ((centeredSite (2 * R) z).2.val : ℤ) = z.2 + R := by
  simp only [Finset.mem_product, Finset.mem_Icc] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  constructor
  · simp only [centeredSite, Fin.val_ofNat, half]
    have h0 : 0 ≤ z.1 + (R : ℕ) := by omega
    have hlt : (z.1 + (R : ℕ)).toNat < 2 * R + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg h0]
  · simp only [centeredSite, Fin.val_ofNat, half]
    have h0 : 0 ≤ z.2 + (R : ℕ) := by omega
    have hlt : (z.2 + (R : ℕ)).toNat < 2 * R + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg h0]

theorem plane_centeredSite (R : ℕ) {z : ℤ × ℤ} (hz : z ∈ planeBox R) :
    plane R (centeredSite (2 * R) z) = z := by
  obtain ⟨h1, h2⟩ := centeredSite_val' R hz
  unfold plane
  ext <;> simp only [h1, h2] <;> ring

theorem mem_centeredRegion_iff (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R)
    (x : Site (2 * R + 1)) : x ∈ centeredRegion (2 * R) A ↔ plane R x ∈ A := by
  unfold centeredRegion
  rw [Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [plane_centeredSite R (hA hz)]
  · intro h
    exact ⟨plane R x, h, centeredSite_plane R x⟩

/-- The plane region `A` and the internal region `centeredRegion (2R) A`. -/
def regionEquiv (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R) :
    {z // z ∈ A} ≃ {x // x ∈ centeredRegion (2 * R) A} where
  toFun z := ⟨centeredSite (2 * R) z, centeredSite_mem z.2⟩
  invFun x := ⟨plane R x, (mem_centeredRegion_iff R hA x).mp x.2⟩
  left_inv z := Subtype.ext (plane_centeredSite R (hA z.2))
  right_inv x := Subtype.ext (centeredSite_plane R x)

/-- The off-region coordinates. -/
def offEquiv (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R) :
    {x : Fin (2 * R + 1) × Fin (2 * R + 1) // plane R x ∉ A} ≃
      {x : Site (2 * R + 1) // x ∉ centeredRegion (2 * R) A} :=
  Equiv.subtypeEquivRight fun x => not_congr (mem_centeredRegion_iff R hA x).symm

/-- The transport of the off-region coordinates, volume preserving. -/
def offTransport (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R) :
    ({x : Fin (2 * R + 1) × Fin (2 * R + 1) // plane R x ∉ A} → ℝ) ≃ᵐ
      ({x : Site (2 * R + 1) // x ∉ centeredRegion (2 * R) A} → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (offEquiv R hA)

theorem offTransport_measurePreserving (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R) :
    MeasurePreserving (offTransport R hA) := by
  have h := measurePreserving_piCongrLeft (fun _ : {x : Site (2 * R + 1) //
    x ∉ centeredRegion (2 * R) A} => (volume : Measure ℝ)) (offEquiv R hA)
  exact h

theorem offTransport_apply (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R)
    (y : {x : Fin (2 * R + 1) × Fin (2 * R + 1) // plane R x ∉ A} → ℝ)
    (x : {x : Site (2 * R + 1) // x ∉ centeredRegion (2 * R) A}) :
    offTransport R hA y x = y ((offEquiv R hA).symm x) := by
  simp [offTransport, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-! ### Both laws as sums over heights -/

/-- The surface field: integer heights `n` on `A`, the continuous heights `y` off `A`. -/
def sField (R : ℕ) (A : Finset (ℤ × ℤ)) (n : {z // z ∈ A} → ℤ)
    (y : {x : Fin (2 * R + 1) × Fin (2 * R + 1) // plane R x ∉ A} → ℝ) :
    Fin (2 * R + 1) × Fin (2 * R + 1) → ℝ :=
  fun x => if h : plane R x ∈ A then (n ⟨plane R x, h⟩ : ℝ) else y ⟨x, h⟩

/-- The surface weight of the heights `n`. -/
def sMass (β : ℝ) (hβ : 0 < β) (R : ℕ) (A : Finset (ℤ × ℤ)) (n : {z // z ∈ A} → ℤ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (∏ e, sosInterpolation β hβ
    (((squareZero (2 * R + 1)).src e).elim 0 (sField R A n y) -
      ((squareZero (2 * R + 1)).tgt e).elim 0 (sField R A n y)))

/-- The differences from the base point. -/
def sDiff {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A) (n : {z // z ∈ A} → ℤ) :
    {z // z ∈ A} → ℤ :=
  fun z => n z - n ⟨w, hw⟩

/-- The unnormalized surface measure. -/
def sMeasure (β : ℝ) (hβ : 0 < β) (R : ℕ) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A) :
    Measure ({z // z ∈ A} → ℤ) :=
  Measure.sum fun n => sMass β hβ R A n • Measure.dirac (sDiff hw n)

theorem sosLiteralDiffLaw_eq {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) (R : ℕ) (hA : A ⊆ planeBox R) :
    sosLiteralDiffLaw β hβ hβ1 A w hw R hA = (sMeasure β hβ R hw Set.univ)⁻¹ • sMeasure β hβ R hw :=
  rfl

theorem lintegral_sMeasure {β : ℝ} (hβ : 0 < β) (R : ℕ) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) (G : ({z // z ∈ A} → ℤ) → ℝ≥0∞) :
    ∫⁻ d, G d ∂sMeasure β hβ R hw = ∑' n, sMass β hβ R A n * G (sDiff hw n) := by
  rw [sMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ (measurable_of_countable G), smul_eq_mul]

theorem sMeasure_univ {β : ℝ} (hβ : 0 < β) (R : ℕ) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) : sMeasure β hβ R hw Set.univ = ∑' n, sMass β hβ R A n := by
  have h := lintegral_sMeasure hβ R hw (fun _ => 1)
  simp only [lintegral_const, mul_one, one_mul] at h
  exact h

theorem literalFiber_univ (L : ℕ) (β : ℝ) (C : Finset (Site L)) (n : {x // x ∈ C} → ℤ) :
    literalFiber L β C n Set.univ =
      ∫⁻ y, ENNReal.ofReal (boxWeight L β (heightField C n y)) := by
  rw [literalFiber, Measure.map_apply (measurable_heightField C n) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The reindexing of the heights. -/
def heightEquiv (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R) :
    ({z // z ∈ A} → ℤ) ≃ ({x // x ∈ centeredRegion (2 * R) A} → ℤ) :=
  (regionEquiv R hA).arrowCongr (Equiv.refl ℤ)

theorem heightField_transport (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R)
    (n : {z // z ∈ A} → ℤ) (y : {x : Fin (2 * R + 1) × Fin (2 * R + 1) // plane R x ∉ A} → ℝ) :
    heightField (centeredRegion (2 * R) A) (heightEquiv R hA n) (offTransport R hA y) =
      sField R A n y := by
  funext x
  simp only [heightField, mergePi, sField]
  by_cases h : plane R x ∈ A
  · have hx : x ∈ centeredRegion (2 * R) A := (mem_centeredRegion_iff R hA x).mpr h
    rw [dite_eq_left hx, dite_eq_left h]
    simp [heightEquiv, regionEquiv, Equiv.arrowCongr_apply]
  · have hx : x ∉ centeredRegion (2 * R) A := fun hx => h ((mem_centeredRegion_iff R hA x).mp hx)
    rw [dite_eq_right hx, dite_eq_right h, offTransport_apply]
    rfl

theorem sMass_eq (β : ℝ) (hβ : 0 < β) (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R)
    (n : {z // z ∈ A} → ℤ) :
    sMass β hβ R A n = literalFiber (2 * R + 1) β (centeredRegion (2 * R) A)
      (heightEquiv R hA n) Set.univ := by
  rw [literalFiber_univ, sMass]
  rw [← (offTransport_measurePreserving R hA).lintegral_comp_emb
    (offTransport R hA).measurableEmbedding]
  refine lintegral_congr fun y => ?_
  rw [heightField_transport, prod_sosInterpolation_eq]

theorem sDiff_eq (R : ℕ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ planeBox R) {w : ℤ × ℤ} (hw : w ∈ A)
    (n : {z // z ∈ A} → ℤ) : sDiff hw n = diffOf (2 * R) A hw (heightEquiv R hA n) := by
  funext z
  simp only [sDiff, diffOf, heightEquiv, regionEquiv, Equiv.arrowCongr_apply,
    Equiv.coe_fn_symm_mk, Equiv.refl_apply, Function.comp_apply]
  congr 2
  · exact Subtype.ext (plane_centeredSite R (hA z.2)).symm
  · exact Subtype.ext (plane_centeredSite R (hA hw)).symm

/-- **The bridge**: the surface law in the box `[-R, R]²` is the internal `diffLaw β A w (2R)`. -/
theorem sosLiteralDiffLaw_eq_diffLaw {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {A : Finset (ℤ × ℤ)}
    {w : ℤ × ℤ} (hw : w ∈ A) (R : ℕ) (hA : A ⊆ planeBox R) :
    sosLiteralDiffLaw β hβ hβ1 A w hw R hA = diffLaw β A w (2 * R) := by
  have hsum : ∀ G : ({z // z ∈ A} → ℤ) → ℝ≥0∞,
      ∑' n, sMass β hβ R A n * G (sDiff hw n) =
        ∑' n', literalFiber (2 * R + 1) β (centeredRegion (2 * R) A) n' Set.univ *
          G (diffOf (2 * R) A hw n') := by
    intro G
    rw [← (heightEquiv R hA).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [sMass_eq β hβ R hA, sDiff_eq R hA hw]
  have hZ : sMeasure β hβ R hw Set.univ =
      literalPartition (2 * R + 1) β (centeredRegion (2 * R) A) := by
    rw [sMeasure_univ]
    have h := hsum (fun _ => 1)
    simp only [mul_one] at h
    rw [h, literalPartition]
  ext s hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, sosLiteralDiffLaw_eq,
    lintegral_smul_measure, lintegral_sMeasure, hsum, hZ, smul_eq_mul,
    lintegral_diffLaw_eq hβ.le hw]
  congr 1
  refine tsum_congr fun n => ?_
  rw [literalFiber_univ]

/-! ### The gate -/

theorem sosInterpolation_pos {β : ℝ} (hβ : 0 < β) (t : ℝ) : 0 < sosInterpolation β hβ t := by
  rw [sosInterpolation_eq]
  exact (SOS.Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ.le t).2

theorem sosInterpolation_intCast {β : ℝ} (hβ : 0 < β) (m : ℤ) :
    sosInterpolation β hβ m = Real.exp (-(β * |(m : ℝ)|)) := by
  rw [sosInterpolation_eq, show ((m : ℝ) : ℂ) = (m : ℂ) by push_cast; rfl,
    SOS.Interp.sosInterp_intCast hβ.le, Complex.ofReal_re]

/-- The one-site box (`R = 0`). -/
theorem isProbabilityMeasure_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {A : Finset (ℤ × ℤ)}
    {w : ℤ × ℤ} (hw : w ∈ A) (hA : A ⊆ planeBox 0) :
    IsProbabilityMeasure (sosLiteralDiffLaw β hβ hβ1 A w hw 0 hA) := by
  have hsub : ∀ a b : Fin (2 * 0 + 1), a = b := fun a b => Fin.ext (by omega)
  have hA0 : ∀ z ∈ A, z = (0, 0) := fun z hz => by
    have := hA hz
    simp only [planeBox, Finset.mem_product, Finset.mem_Icc, Nat.cast_zero, neg_zero] at this
    ext <;> omega
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ A := hA0 w hw ▸ hw
  have hplane : ∀ x : Fin (2 * 0 + 1) × Fin (2 * 0 + 1), plane 0 x = (0, 0) := fun x => by
    simp [plane]
  have hempty : IsEmpty {x : Fin (2 * 0 + 1) × Fin (2 * 0 + 1) // plane 0 x ∉ A} :=
    ⟨fun x => x.2 (hplane x.1 ▸ h00)⟩
  -- the heights determine the field
  let k : ({z // z ∈ A} → ℤ) → ℤ := fun n => n ⟨(0, 0), h00⟩
  have hfield : ∀ n y x, sField 0 A n y x = (k n : ℝ) := fun n y x => by
    simp only [sField]
    rw [dite_eq_left (hplane x ▸ h00 : plane 0 x ∈ A)]
    congr 2
    exact Subtype.ext (hplane x)
  -- the integral over the empty family of coordinates is an evaluation
  have hvol : (volume : Measure ({x : Fin (2 * 0 + 1) × Fin (2 * 0 + 1) // plane 0 x ∉ A} → ℝ)) =
      Measure.dirac (fun x => isEmptyElim x) := Measure.pi_of_empty _ _
  have hmass : ∀ n, sMass β hβ 0 A n = ENNReal.ofReal (∏ e, sosInterpolation β hβ
      (((squareZero (2 * 0 + 1)).src e).elim 0 (fun _ => (k n : ℝ)) -
        ((squareZero (2 * 0 + 1)).tgt e).elim 0 (fun _ => (k n : ℝ)))) := fun n => by
    rw [sMass, hvol, lintegral_dirac]
    congr 3
    funext e
    congr 2 <;> congr 1 <;> funext x <;> exact hfield n _ x
  -- every edge argument is an integer
  have hint : ∀ (n : {z // z ∈ A} → ℤ) (a : Option (Fin (2 * 0 + 1) × Fin (2 * 0 + 1))),
      ∃ m : ℤ, a.elim 0 (fun _ => (k n : ℝ)) = m := fun n a => by
    cases a
    · exact ⟨0, by simp⟩
    · exact ⟨k n, by simp⟩
  have hfac1 : ∀ n e, sosInterpolation β hβ
      (((squareZero (2 * 0 + 1)).src e).elim 0 (fun _ => (k n : ℝ)) -
        ((squareZero (2 * 0 + 1)).tgt e).elim 0 (fun _ => (k n : ℝ))) ≤ 1 := fun n e => by
    obtain ⟨m₁, h₁⟩ := hint n ((squareZero (2 * 0 + 1)).src e)
    obtain ⟨m₂, h₂⟩ := hint n ((squareZero (2 * 0 + 1)).tgt e)
    rw [h₁, h₂, ← Int.cast_sub, sosInterpolation_intCast]
    exact Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg ((m₁ - m₂ : ℤ) : ℝ)])
  -- one boundary edge carries `e^{-β|k|}`
  let x₀ : Fin (2 * 0 + 1) × Fin (2 * 0 + 1) := (0, 0)
  have hcard : (Finset.univ.filter fun e : SquareFreeEdge (2 * 0 + 1) =>
      (squareFree (2 * 0 + 1)).src e = x₀ ∨ (squareFree (2 * 0 + 1)).tgt e = x₀).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _
    have he : e.1.1 = e.1.2 := Prod.ext (hsub _ _) (hsub _ _)
    exact absurd e.2.1 (by rw [he]; exact lt_irrefl _)
  let e₀ : SquareFreeEdge (2 * 0 + 1) ⊕ Σ j : Fin (2 * 0 + 1) × Fin (2 * 0 + 1),
      Fin (4 - (Finset.univ.filter fun e : SquareFreeEdge (2 * 0 + 1) =>
        (squareFree (2 * 0 + 1)).src e = j ∨ (squareFree (2 * 0 + 1)).tgt e = j).card) :=
    Sum.inr ⟨x₀, ⟨0, by rw [hcard]; norm_num⟩⟩
  have hle : ∀ n, sMass β hβ 0 A n ≤ ENNReal.ofReal (Real.exp (-(β * |((k n : ℤ) : ℝ)|))) := by
    intro n
    rw [hmass]
    refine ENNReal.ofReal_le_ofReal ?_
    set f := fun e => sosInterpolation β hβ
      (((squareZero (2 * 0 + 1)).src e).elim 0 (fun _ => (k n : ℝ)) -
        ((squareZero (2 * 0 + 1)).tgt e).elim 0 (fun _ => (k n : ℝ))) with hf
    have hrest : ∏ e ∈ Finset.univ.erase e₀, f e ≤ 1 :=
      Finset.prod_le_one₀ (fun e _ => (sosInterpolation_pos hβ _).le) fun e _ => hfac1 n e
    calc ∏ e, f e = f e₀ * ∏ e ∈ Finset.univ.erase e₀, f e :=
          (Finset.mul_prod_erase _ _ (Finset.mem_univ e₀)).symm
      _ ≤ f e₀ * 1 := mul_le_mul_of_nonneg_left hrest (sosInterpolation_pos hβ _).le
      _ = Real.exp (-(β * |((k n : ℤ) : ℝ)|)) := by
          rw [mul_one, hf]
          simp only [e₀, squareZero, Sum.elim_inr, Option.elim]
          rw [sub_zero, sosInterpolation_intCast]
  have hsum : Summable fun n : {z // z ∈ A} → ℤ => Real.exp (-(β * |((k n : ℤ) : ℝ)|)) :=
    ((summable_exp_neg_abs_int β hβ).comp_injective fun a b hab => by
      funext z
      have hz : z = ⟨(0, 0), h00⟩ := Subtype.ext (hA0 z z.2)
      subst hz
      exact hab).congr fun n => by simp only [Function.comp_apply, neg_mul]; rfl
  have hfin : ∑' n, sMass β hβ 0 A n ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) hsum]
    exact ENNReal.ofReal_ne_top
  have hpos : ∑' n, sMass β hβ 0 A n ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum 0)).ne'
    rw [hmass]
    exact ENNReal.ofReal_pos.mpr (Finset.prod_pos fun e _ => sosInterpolation_pos hβ _)
  rw [sosLiteralDiffLaw_eq]
  constructor
  rw [Measure.smul_apply, smul_eq_mul, sMeasure_univ]
  exact ENNReal.inv_mul_cancel hpos hfin

/-! ### Limit points and the root -/

theorem exists_box (A : Finset (ℤ × ℤ)) : ∃ M : ℕ, ∀ R, M ≤ R → A ⊆ planeBox R := by
  refine ⟨planeRadius A, fun R hR z hz => ?_⟩
  obtain ⟨h1, h2⟩ := coord_le_planeRadius hz
  simp only [planeBox, Finset.mem_product, Finset.mem_Icc]
  omega

theorem tendsto_val_subtype {P : ℕ → Prop} [Nonempty {k // P k}] {K : ℕ} (hK : ∀ k ≥ K, P k) :
    Tendsto (Subtype.val : {k // P k} → ℕ) atTop atTop :=
  tendsto_atTop_atTop.2 fun b =>
    ⟨⟨max b K, hK _ (le_max_right _ _)⟩, fun _a ha => (le_max_left _ _).trans ha⟩

theorem tendsto_of_tendsto_subtype {X : Type*} [TopologicalSpace X] {P : ℕ → Prop}
    [Nonempty {k // P k}] {K : ℕ} (hK : ∀ k ≥ K, P k) {f : ℕ → X} {x : X}
    (h : Tendsto (fun k : {k // P k} => f k) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  rw [tendsto_atTop'] at h ⊢
  intro s hs
  obtain ⟨a, ha⟩ := h s hs
  exact ⟨max K a, fun b hb =>
    ha ⟨b, hK b ((le_max_left _ _).trans hb)⟩ ((le_max_right K a.val).trans hb)⟩

theorem euclid_le_two_planeLinf (v v' : ℤ × ℤ) :
    Real.sqrt (((v.1 - v'.1 : ℤ) : ℝ) ^ 2 + ((v.2 - v'.2 : ℤ) : ℝ) ^ 2) ≤
      2 * (planeLinf v v' : ℝ) := by
  have h1 : (v.1 - v'.1).natAbs ≤ planeLinf v v' := le_max_left _ _
  have h2 : (v.2 - v'.2).natAbs ≤ planeLinf v v' := le_max_right _ _
  have ha : |((v.1 - v'.1 : ℤ) : ℝ)| ≤ (planeLinf v v' : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h1
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hb : |((v.2 - v'.2 : ℤ) : ℝ)| ≤ (planeLinf v v' : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h2
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs ((v.1 - v'.1 : ℤ) : ℝ), sq_abs ((v.2 - v'.2 : ℤ) : ℝ),
    abs_nonneg ((v.1 - v'.1 : ℤ) : ℝ), abs_nonneg ((v.2 - v'.2 : ℤ) : ℝ)]

theorem log_euclid_le (v v' : ℤ × ℤ) :
    Real.log (1 + Real.sqrt (((v.1 - v'.1 : ℤ) : ℝ) ^ 2 + ((v.2 - v'.2 : ℤ) : ℝ) ^ 2)) ≤
      2 * Real.log (1 + (planeLinf v v' : ℝ)) := by
  have hl : (0 : ℝ) ≤ planeLinf v v' := Nat.cast_nonneg _
  have he := euclid_le_two_planeLinf v v'
  have hs : 0 ≤ Real.sqrt (((v.1 - v'.1 : ℤ) : ℝ) ^ 2 + ((v.2 - v'.2 : ℤ) : ℝ) ^ 2) :=
    Real.sqrt_nonneg _
  rw [← Real.log_rpow (by positivity)]
  apply Real.log_le_log (by positivity)
  rw [Real.rpow_two]
  nlinarith

end FroehlichSpencer.BKT.Bridge.SOSLiteral

end
