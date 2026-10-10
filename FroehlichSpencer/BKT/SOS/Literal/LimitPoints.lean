/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitVague
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The laws of the height differences and their vague limit points (the comb-inserted SOS construction)

For a finite plane region `A ∋ w`, the box `Ω_L` of side `L + 1` centred at the origin and the
literal state `⟨·⟩_{Ω_L,A}`, `diffLaw β A w L` is the law of the integer differences
`d(z) = n(z) − n(w)`, `z ∈ A`, a probability measure on `ℤ^A` (`diffMap`).

* `lintegral_diffLaw_eq`: expectations under `diffLaw` are `Z⁻¹ Σ_n w(n) G(d(n))` with
  `w(n) = ∫ ρ(n ⊕ y) dy`.
* `lintegral_diffLaw_pair`: an observable of `d(v) − d(v')` has the expectation of the same
  observable of `φ(v) − φ(v')` in the literal state.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening

/-- Integer configurations on a plane region. -/
abbrev DiffConfig (A : Finset (ℤ × ℤ)) := {z // z ∈ A} → ℤ

/-- The differences `d(z) = ⌊φ(z) − φ(w)⌋` (exact on the integer heights of `A`). -/
def diffMap (L : ℕ) (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (φ : Site (L + 1) → ℝ) : DiffConfig A :=
  fun z => ⌊φ (centeredSite L z) - φ (centeredSite L w)⌋

theorem measurable_diffMap (L : ℕ) (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) :
    Measurable (diffMap L A w) := by
  rw [measurable_pi_iff]
  intro z
  exact Measurable.floor (f := fun φ : Site (L + 1) → ℝ =>
    φ (centeredSite L z) - φ (centeredSite L w)) (by fun_prop)

/-- **The law of the height differences** in the literal state on the centred box of side
`L + 1`. -/
def diffLaw (β : ℝ) (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (L : ℕ) : Measure (DiffConfig A) :=
  (literalState (L + 1) β (centeredRegion L A)).map (diffMap L A w)

theorem isProbabilityMeasure_diffLaw {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (ℤ × ℤ))
    (w : ℤ × ℤ) {L : ℕ} (hL : 1 ≤ L) : IsProbabilityMeasure (diffLaw β A w L) := by
  have := isProbabilityMeasure_literalState (L := L + 1) (by omega) hβ hβ1 (centeredRegion L A)
  unfold diffLaw
  infer_instance

theorem lintegral_diffLaw {β : ℝ} (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (L : ℕ)
    (G : DiffConfig A → ℝ≥0∞) :
    ∫⁻ d, G d ∂diffLaw β A w L =
      ∫⁻ φ, G (diffMap L A w φ) ∂literalState (L + 1) β (centeredRegion L A) :=
  lintegral_map (measurable_of_countable G) (measurable_diffMap L A w)

theorem centeredSite_mem {L : ℕ} {A : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ A) :
    centeredSite L z ∈ centeredRegion L A := Finset.mem_image_of_mem _ hz

/-- The differences of an integer height configuration. -/
def diffOf (L : ℕ) (A : Finset (ℤ × ℤ)) {w : ℤ × ℤ} (hw : w ∈ A)
    (n : {x // x ∈ centeredRegion L A} → ℤ) : DiffConfig A :=
  fun z => n ⟨centeredSite L z, centeredSite_mem z.2⟩ - n ⟨centeredSite L w, centeredSite_mem hw⟩

theorem diffMap_heightField {L : ℕ} {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A)
    (n : {x // x ∈ centeredRegion L A} → ℤ) (y : {x // x ∉ centeredRegion L A} → ℝ) :
    diffMap L A w (heightField (centeredRegion L A) n y) = diffOf L A hw n := by
  funext z
  simp only [diffMap, diffOf, heightField_apply_mem _ n y (centeredSite_mem z.2),
    heightField_apply_mem _ n y (centeredSite_mem hw)]
  rw [← Int.cast_sub, Int.floor_intCast]

/-- **The master formula** `∫ G d(diffLaw) = Z⁻¹ Σ_n w(n) G(d(n))`. -/
theorem lintegral_diffLaw_eq {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) (L : ℕ) (G : DiffConfig A → ℝ≥0∞) :
    ∫⁻ d, G d ∂diffLaw β A w L = (literalPartition (L + 1) β (centeredRegion L A))⁻¹ *
      ∑' n, (∫⁻ y, ENNReal.ofReal (boxWeight (L + 1) β (heightField (centeredRegion L A) n y))) *
        G (diffOf L A hw n) := by
  rw [lintegral_diffLaw, lintegral_literalState hβ _ (F := fun φ => G (diffMap L A w φ))
    ((measurable_of_countable G).comp (measurable_diffMap L A w))]
  congr 1
  refine tsum_congr fun n => ?_
  have hm : Measurable fun y : {x // x ∉ centeredRegion L A} → ℝ =>
      ENNReal.ofReal (boxWeight (L + 1) β (heightField (centeredRegion L A) n y)) :=
    ENNReal.measurable_ofReal.comp ((continuous_boxWeight hβ).measurable.comp
      (measurable_heightField _ n))
  simp_rw [diffMap_heightField hw]
  rw [lintegral_mul_const _ hm]

/-- An observable of `d(v) − d(v')` under `diffLaw` is the same observable of `φ(v) − φ(v')`
in the literal state. -/
theorem lintegral_diffLaw_pair {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w v v' : ℤ × ℤ}
    (hw : w ∈ A) (hv : v ∈ A) (hv' : v' ∈ A) (L : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ d, F ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ∂diffLaw β A w L =
      ∫⁻ φ, F (φ (centeredSite L v) - φ (centeredSite L v'))
        ∂literalState (L + 1) β (centeredRegion L A) := by
  rw [lintegral_diffLaw_eq hβ hw, lintegral_literalState hβ _
    (F := fun φ => F (φ (centeredSite L v) - φ (centeredSite L v')))
    (hF.comp ((measurable_pi_apply _).sub (measurable_pi_apply _)))]
  congr 1
  refine tsum_congr fun n => ?_
  have hm : Measurable fun y : {x // x ∉ centeredRegion L A} → ℝ =>
      ENNReal.ofReal (boxWeight (L + 1) β (heightField (centeredRegion L A) n y)) :=
    ENNReal.measurable_ofReal.comp ((continuous_boxWeight hβ).measurable.comp
      (measurable_heightField _ n))
  rw [← lintegral_mul_const _ hm]
  refine lintegral_congr fun y => ?_
  simp only [diffOf, heightField_apply_mem _ n y (centeredSite_mem hv),
    heightField_apply_mem _ n y (centeredSite_mem hv')]
  push_cast
  ring_nf

/-- The base point has `d(w) = 0` almost surely. -/
theorem diffLaw_base_ne_zero {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) (L : ℕ) :
    ∫⁻ d, {d : DiffConfig A | d ⟨w, hw⟩ ≠ 0}.indicator 1 d ∂diffLaw β A w L = 0 := by
  rw [lintegral_diffLaw_eq hβ hw]
  have : ∀ n : {x // x ∈ centeredRegion L A} → ℤ,
      {d : DiffConfig A | d ⟨w, hw⟩ ≠ 0}.indicator 1 (diffOf L A hw n) = (0 : ℝ≥0∞) :=
    fun n => by simp [diffOf, Set.indicator]
  simp [this]

/-! ## Point masses: evenness and the one-site ratio bound -/

/-- The weight of the heights `n` on the region, `w(n) = ∫ ρ(n ⊕ y) dy`. -/
def regionWeight (L : ℕ) (β : ℝ) (A : Finset (ℤ × ℤ))
    (n : {x // x ∈ centeredRegion L A} → ℤ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (boxWeight (L + 1) β (heightField (centeredRegion L A) n y))

theorem diffLaw_singleton {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A)
    (L : ℕ) (d : DiffConfig A) :
    diffLaw β A w L {d} = (literalPartition (L + 1) β (centeredRegion L A))⁻¹ *
      ∑' n, regionWeight L β A n * ({d} : Set (DiffConfig A)).indicator 1 (diffOf L A hw n) := by
  rw [← lintegral_indicator_one (measurableSet_singleton d), lintegral_diffLaw_eq hβ hw]
  rfl

theorem regionWeight_neg {β : ℝ} (hβ : 0 ≤ β) (L : ℕ) (A : Finset (ℤ × ℤ))
    (n : {x // x ∈ centeredRegion L A} → ℤ) : regionWeight L β A (-n) = regionWeight L β A n := by
  unfold regionWeight
  have h := (FroehlichSpencer.BKT.Generic.measurePreserving_neg_pi).lintegral_comp_emb
    (Homeomorph.neg ({x // x ∉ centeredRegion L A} → ℝ)).measurableEmbedding
    (fun y => ENNReal.ofReal (boxWeight (L + 1) β (heightField (centeredRegion L A) n y)))
  rw [← h]
  refine lintegral_congr fun y => ?_
  have hneg : heightField (centeredRegion L A) (-n) y =
      -heightField (centeredRegion L A) n (-y) := by
    rw [← heightField_neg, neg_neg]
  rw [hneg, boxWeight_neg hβ]

theorem diffOf_neg {L : ℕ} {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A)
    (n : {x // x ∈ centeredRegion L A} → ℤ) : diffOf L A hw (-n) = -diffOf L A hw n := by
  funext z
  simp only [diffOf, Pi.neg_apply]
  ring

/-- **Evenness**: `diffLaw{−d} = diffLaw{d}`. -/
theorem diffLaw_neg {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A)
    (L : ℕ) (d : DiffConfig A) : diffLaw β A w L {-d} = diffLaw β A w L {d} := by
  rw [diffLaw_singleton hβ hw, diffLaw_singleton hβ hw]
  congr 1
  rw [← (Equiv.neg ({x // x ∈ centeredRegion L A} → ℤ)).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply]
  rw [regionWeight_neg hβ, diffOf_neg]
  congr 1
  simp only [Set.indicator, Set.mem_singleton_iff, neg_inj, Pi.one_apply]

theorem diffOf_shift {L : ℕ} {A : Finset (ℤ × ℤ)} {w u : ℤ × ℤ} (hw : w ∈ A) (hu : u ∈ A)
    (hinj : ∀ z ∈ A, centeredSite L z = centeredSite L u → z = u)
    (hwu : centeredSite L w ≠ centeredSite L u) (n : {x // x ∈ centeredRegion L A} → ℤ)
    (k : ℤ) :
    diffOf L A hw (n + k • Pi.single ⟨centeredSite L u, centeredSite_mem hu⟩ 1) =
      diffOf L A hw n + k • Pi.single ⟨u, hu⟩ 1 := by
  funext z
  simp only [diffOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have hw' : (⟨centeredSite L w, centeredSite_mem hw⟩ : {x // x ∈ centeredRegion L A}) ≠
      ⟨centeredSite L u, centeredSite_mem hu⟩ := fun h => hwu (congrArg Subtype.val h)
  have hz : ((⟨centeredSite L z, centeredSite_mem z.2⟩ : {x // x ∈ centeredRegion L A}) =
      ⟨centeredSite L u, centeredSite_mem hu⟩) ↔ z = ⟨u, hu⟩ := by
    constructor
    · intro h
      exact Subtype.ext (hinj z z.2 (congrArg Subtype.val h))
    · intro h; rw [h]
  simp only [hw', ↓reduceIte, mul_zero, hz]
  split_ifs <;> ring

/-- **The one-site ratio bound**: `diffLaw{d + k e_u} ≥ (κ e^{−β|k|})⁴ diffLaw{d}` for `u ≠ w`. -/
theorem diffLaw_shift_ge {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w u : ℤ × ℤ} (hw : w ∈ A)
    (hu : u ∈ A) {L : ℕ} (hinj : ∀ z ∈ A, centeredSite L z = centeredSite L u → z = u)
    (hwu : centeredSite L w ≠ centeredSite L u) (d : DiffConfig A) (k : ℤ) :
    ENNReal.ofReal ((shiftConst β * Real.exp (-(β * |(k : ℝ)|))) ^ 4) * diffLaw β A w L {d} ≤
      diffLaw β A w L {d + k • Pi.single ⟨u, hu⟩ 1} := by
  set δn : {x // x ∈ centeredRegion L A} → ℤ :=
    k • Pi.single ⟨centeredSite L u, centeredSite_mem hu⟩ 1 with hδn
  rw [diffLaw_singleton hβ hw, diffLaw_singleton hβ hw, mul_left_comm]
  refine mul_le_mul_right ?_ _
  set F : ({x // x ∈ centeredRegion L A} → ℤ) → ℝ≥0∞ := fun m => regionWeight L β A m *
    ({d + k • Pi.single (⟨u, hu⟩ : {z // z ∈ A}) 1} : Set (DiffConfig A)).indicator 1
      (diffOf L A hw m) with hF
  have hre : ∑' m, F m = ∑' n, F (n + δn) := ((Equiv.addRight δn).tsum_eq F).symm
  rw [hre, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  simp only [hF]
  rw [hδn, diffOf_shift hw hu hinj hwu]
  have hind : ({d + k • Pi.single ⟨u, hu⟩ 1} : Set (DiffConfig A)).indicator 1
      (diffOf L A hw n + k • Pi.single ⟨u, hu⟩ 1) =
      ({d} : Set (DiffConfig A)).indicator (1 : DiffConfig A → ℝ≥0∞) (diffOf L A hw n) := by
    simp only [Set.indicator, Set.mem_singleton_iff, add_left_inj, Pi.one_apply]
  change _ ≤ regionWeight L β A _ * _
  rw [hind, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  unfold regionWeight
  have hm : Measurable fun y : {x // x ∉ centeredRegion L A} → ℝ =>
      ENNReal.ofReal (boxWeight (L + 1) β (heightField (centeredRegion L A) n y)) :=
    ENNReal.measurable_ofReal.comp ((continuous_boxWeight hβ).measurable.comp
      (measurable_heightField _ n))
  rw [← lintegral_const_mul _ hm]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul (by positivity), heightField_add_single]
  exact ENNReal.ofReal_le_ofReal (boxWeight_shift_ge hβ _ _ _)

/-! ## Tails -/

/-- `e^{at} ≤ B + η e^{bt}` for `t ≥ 0`, `0 ≤ a < b`, `η > 0`. -/
theorem exists_exp_le_add {a b η : ℝ} (ha : 0 ≤ a) (hab : a < b) (hη : 0 < η) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → Real.exp (a * t) ≤ B + η * Real.exp (b * t) := by
  set K := max 0 (Real.log (1 / η) / (b - a)) with hK
  refine ⟨Real.exp (a * K), fun t ht => ?_⟩
  rcases le_or_gt t K with h | h
  · have : Real.exp (a * t) ≤ Real.exp (a * K) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ha)
    have : 0 ≤ η * Real.exp (b * t) := by positivity
    linarith
  · have hK' : Real.log (1 / η) ≤ (b - a) * t := by
      have h1 : Real.log (1 / η) / (b - a) ≤ K := le_max_right _ _
      rw [div_le_iff₀ (by linarith)] at h1
      nlinarith
    have h2 : Real.exp (a * t) ≤ η * Real.exp (b * t) := by
      have h3 : 1 / η ≤ Real.exp ((b - a) * t) := by
        rw [← Real.exp_log (by positivity : 0 < 1 / η)]
        exact Real.exp_le_exp.mpr hK'
      rw [div_le_iff₀ hη] at h3
      calc Real.exp (a * t) = Real.exp (a * t) * 1 := (mul_one _).symm
        _ ≤ Real.exp (a * t) * (Real.exp ((b - a) * t) * η) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = η * Real.exp (b * t) := by rw [← mul_assoc, ← Real.exp_add]; ring_nf
    have : 0 ≤ Real.exp (a * K) := (Real.exp_pos _).le
    linarith

/-- `t² ≤ B + η e^{bt}` for `t ≥ 0`, `b > 0`, `η > 0`. -/
theorem exists_sq_le_add {b η : ℝ} (hb : 0 < b) (hη : 0 < η) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ B + η * Real.exp (b * t) := by
  obtain ⟨B, hB⟩ := exists_exp_le_add (a := b / 2) (b := b) (η := η * b ^ 2 / 8) (by positivity)
    (by linarith) (by positivity)
  refine ⟨8 / b ^ 2 * B, fun t ht => ?_⟩
  have h1 : t ^ 2 ≤ 8 / b ^ 2 * Real.exp (b / 2 * t) := by
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ b / 2 * t)
    have h2 : b ^ 2 * t ^ 2 / 8 ≤ Real.exp (b / 2 * t) := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb 2)]
    linarith
  calc t ^ 2 ≤ 8 / b ^ 2 * Real.exp (b / 2 * t) := h1
    _ ≤ 8 / b ^ 2 * (B + η * b ^ 2 / 8 * Real.exp (b * t)) :=
        mul_le_mul_of_nonneg_left (hB t ht) (by positivity)
    _ = 8 / b ^ 2 * B + η * Real.exp (b * t) := by field_simp

/-- The box `[−M, M]^A` of configurations. -/
def boxConfigs (A : Finset (ℤ × ℤ)) (M : ℕ) : Finset (DiffConfig A) :=
  Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M

/-- **Tightness**: `diffLaw(outside [−M,M]^A) ≤ |A| e^{−cM} C` if `⟨e^{c|d(z) − d(w)|}⟩ ≤ C`. -/
theorem diffLaw_compl_box_le {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) (L : ℕ) {c C : ℝ} (hc : 0 ≤ c)
    (hT : ∀ z : {z // z ∈ A}, ∫⁻ d, ENNReal.ofReal (Real.exp (c * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|))
      ∂diffLaw β A w L ≤ ENNReal.ofReal C) (M : ℕ) :
    diffLaw β A w L (↑(boxConfigs A M))ᶜ ≤
      ENNReal.ofReal (Real.exp (-(c * M))) * (A.card * ENNReal.ofReal C) := by
  classical
  set μ := diffLaw β A w L
  have hpt : ∀ d : DiffConfig A, (↑(boxConfigs A M) : Set (DiffConfig A))ᶜ.indicator 1 d ≤
      {d : DiffConfig A | d ⟨w, hw⟩ ≠ 0}.indicator 1 d + ∑ z : {z // z ∈ A},
        ENNReal.ofReal (Real.exp (-(c * M))) *
          ENNReal.ofReal (Real.exp (c * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|)) := by
    intro d
    by_cases hd : d ∈ boxConfigs A M
    · simp [Set.indicator, hd]
    · simp only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, hd, not_false_eq_true,
        ↓reduceIte, Pi.one_apply]
      by_cases hdw : d ⟨w, hw⟩ = 0
      · simp only [boxConfigs, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hd
        obtain ⟨z, hz⟩ := hd
        have hz' : (M : ℝ) < |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)| := by
          rw [hdw, sub_zero, ← Int.cast_abs]
          have : (M : ℤ) < |d z| := by
            rw [lt_abs]; by_contra h; push Not at h; exact hz ⟨by linarith [h.2], h.1⟩
          exact_mod_cast this
        refine le_trans ?_ (le_add_of_nonneg_left zero_le)
        refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ z))
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by nlinarith))
      · simp [hdw]
  have hm : ∀ z : {z // z ∈ A}, Measurable fun d : DiffConfig A =>
      ENNReal.ofReal (Real.exp (-(c * M))) *
        ENNReal.ofReal (Real.exp (c * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|)) :=
    fun z => measurable_of_countable _
  calc μ (↑(boxConfigs A M))ᶜ
      = ∫⁻ d, (↑(boxConfigs A M) : Set (DiffConfig A))ᶜ.indicator 1 d ∂μ :=
        (lintegral_indicator_one (Finset.measurableSet _).compl).symm
    _ ≤ ∫⁻ d, ({d : DiffConfig A | d ⟨w, hw⟩ ≠ 0}.indicator 1 d + ∑ z : {z // z ∈ A},
          ENNReal.ofReal (Real.exp (-(c * M))) *
            ENNReal.ofReal (Real.exp (c * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|))) ∂μ :=
        lintegral_mono hpt
    _ = ∫⁻ d, {d : DiffConfig A | d ⟨w, hw⟩ ≠ 0}.indicator 1 d ∂μ + ∑ z : {z // z ∈ A},
          ENNReal.ofReal (Real.exp (-(c * M))) *
            ∫⁻ d, ENNReal.ofReal (Real.exp (c * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|)) ∂μ := by
        rw [lintegral_add_left (measurable_of_countable _), lintegral_finsetSum _ fun z _ => hm z]
        congr 1
        exact Finset.sum_congr rfl fun z _ => lintegral_const_mul _ (measurable_of_countable _)
    _ ≤ 0 + ∑ _z : {z // z ∈ A}, ENNReal.ofReal (Real.exp (-(c * M))) * ENNReal.ofReal C := by
        rw [diffLaw_base_ne_zero hβ hw]
        exact add_le_add le_rfl (Finset.sum_le_sum fun z _ => mul_le_mul_right (hT z) _)
    _ = ENNReal.ofReal (Real.exp (-(c * M))) * (A.card * ENNReal.ofReal C) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        ring

/-- **The tail of an observable** outside the box `[−M, M]^A`. -/
theorem tsum_compl_box_le {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) (L : ℕ) {c C CX : ℝ} (hc : 0 ≤ c)
    (hT : ∀ z : {z // z ∈ A}, ∫⁻ d, ENNReal.ofReal (Real.exp (c * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|))
      ∂diffLaw β A w L ≤ ENNReal.ofReal C)
    (X : DiffConfig A → ℝ)
    (hX : ∫⁻ d, ENNReal.ofReal (Real.exp (c * |X d|)) ∂diffLaw β A w L ≤ ENNReal.ofReal CX)
    {g : DiffConfig A → ℝ≥0∞} {B η : ℝ}
    (hg : ∀ d, g d ≤ ENNReal.ofReal B + ENNReal.ofReal η * ENNReal.ofReal (Real.exp (c * |X d|)))
    (M : ℕ) :
    ∑' d, (↑(boxConfigs A M) : Set (DiffConfig A))ᶜ.indicator g d * diffLaw β A w L {d} ≤
      ENNReal.ofReal B * (ENNReal.ofReal (Real.exp (-(c * M))) * (A.card * ENNReal.ofReal C)) +
        ENNReal.ofReal η * ENNReal.ofReal CX := by
  classical
  set μ := diffLaw β A w L
  set F : Set (DiffConfig A) := (↑(boxConfigs A M) : Set (DiffConfig A))ᶜ with hF
  have hpt : ∀ d, F.indicator g d ≤ F.indicator (fun _ => ENNReal.ofReal B) d +
      ENNReal.ofReal η * ENNReal.ofReal (Real.exp (c * |X d|)) := by
    intro d
    by_cases hd : d ∈ F
    · simp only [Set.indicator, hd, ↓reduceIte]; exact hg d
    · simp only [Set.indicator, hd, ↓reduceIte, zero_add]; exact zero_le
  rw [← lintegral_countable']
  calc ∫⁻ d, F.indicator g d ∂μ
      ≤ ∫⁻ d, (F.indicator (fun _ => ENNReal.ofReal B) d +
          ENNReal.ofReal η * ENNReal.ofReal (Real.exp (c * |X d|))) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal B * μ F +
          ENNReal.ofReal η * ∫⁻ d, ENNReal.ofReal (Real.exp (c * |X d|)) ∂μ := by
        rw [lintegral_add_left (measurable_of_countable _), lintegral_indicator
          (Finset.measurableSet _).compl, setLIntegral_const, lintegral_const_mul _
          (measurable_of_countable _)]
    _ ≤ _ := add_le_add (mul_le_mul_right (diffLaw_compl_box_le hβ hw L hc hT M) _)
        (mul_le_mul_right hX _)

/-! ## Limit points -/

/-- **Lower bounds pass to every vague limit point** of the laws, for observables `g` dominated by
`B + η e^{c|X|}` for every `η > 0`, given the uniform exponential bounds (*). -/
theorem le_lintegral_limitPoint {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ}
    (hw : w ∈ A) {Ls : ℕ → ℕ} {ν : Measure (DiffConfig A)}
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d})))
    {c C CX : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCX : 0 ≤ CX)
    (hT : ∀ᶠ j in atTop, ∀ z : {z // z ∈ A}, ∫⁻ d, ENNReal.ofReal
      (Real.exp (c * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|)) ∂diffLaw β A w (Ls j) ≤ ENNReal.ofReal C)
    (X : DiffConfig A → ℝ)
    (hX : ∀ᶠ j in atTop, ∫⁻ d, ENNReal.ofReal (Real.exp (c * |X d|)) ∂diffLaw β A w (Ls j) ≤
      ENNReal.ofReal CX)
    {g : DiffConfig A → ℝ≥0∞} (hgfin : ∀ d, g d ≠ ⊤)
    (hg : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ d, g d ≤ ENNReal.ofReal B +
      ENNReal.ofReal η * ENNReal.ofReal (Real.exp (c * |X d|)))
    {B₀ : ℝ≥0∞} (hB₀ : ∀ᶠ j in atTop, B₀ ≤ ∫⁻ d, g d ∂diffLaw β A w (Ls j)) :
    B₀ ≤ ∫⁻ d, g d ∂ν := by
  refine le_lintegral_of_tendsto_singleton hν g hgfin (fun η' hη' => ?_) hB₀
  by_cases htop : η' = ⊤
  · exact ⟨∅, Eventually.of_forall fun j => by rw [htop]; exact le_top⟩
  set e := η'.toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hη'.ne' htop
  obtain ⟨B, hB0, hB⟩ := hg (e / (2 * (CX + 1))) (by positivity)
  set K := B * A.card * C with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.log (2 * (K + 1) / e) / c)
  have hexp : Real.exp (-(c * M)) * K ≤ e / 2 := by
    have h1 : Real.log (2 * (K + 1) / e) < c * M := by
      rw [div_lt_iff₀ hc] at hM; linarith
    have h2 : 2 * (K + 1) / e < Real.exp (c * M) := by
      rw [← Real.exp_log (by positivity : 0 < 2 * (K + 1) / e)]
      exact Real.exp_lt_exp.mpr h1
    rw [Real.exp_neg]
    rw [div_lt_iff₀ he0] at h2
    rw [inv_mul_le_iff₀ (Real.exp_pos _)]
    nlinarith
  refine ⟨boxConfigs A M, ?_⟩
  filter_upwards [hT, hX] with j hTj hXj
  refine (tsum_compl_box_le hβ hw (Ls j) hc.le hTj X hXj hB M).trans ?_
  have hcard : ((A.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal C = ENNReal.ofReal (A.card * C) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hcard, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hB0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_toReal htop, ← he]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : B * (Real.exp (-(c * M)) * (A.card * C)) ≤ e / 2 := by
    have : B * (Real.exp (-(c * M)) * (A.card * C)) = Real.exp (-(c * M)) * K := by ring
    rw [this]; exact hexp
  have h2 : e / (2 * (CX + 1)) * CX ≤ e / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- **(*) for the laws of the differences.** -/
theorem diffLaw_exp_bound {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hcβ : c < β) {A : Finset (ℤ × ℤ)} {w v v' : ℤ × ℤ} (hw : w ∈ A) (hv : v ∈ A)
    (hv' : v' ∈ A) : ∃ L_A : ℕ, ∀ L, L_A ≤ L →
      ∫⁻ d, ENNReal.ofReal (Real.exp (c * |((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)|))
          ∂diffLaw β A w L ≤
        ENNReal.ofReal (2 * expBoundBase β c ^ (2 * planeLinf v v')) := by
  obtain ⟨L_A, hL⟩ := literal_exp_abs_plane hβ hβ1 hc0 hcβ A v v'
  refine ⟨L_A, fun L hLA => ?_⟩
  rw [lintegral_diffLaw_pair hβ.le hw hv hv' L (F := fun t => ENNReal.ofReal (Real.exp (c * |t|)))
    (ENNReal.measurable_ofReal.comp (by fun_prop))]
  exact hL L hLA

theorem expBoundBase_pos {β c : ℝ} (hβ : 0 < β) (hc0 : 0 ≤ c) (hcβ : c < β) :
    0 < expBoundBase β c := by
  unfold expBoundBase
  have hc2 : 2 * (c ^ 2 / 2) < β ^ 2 := by nlinarith
  exact Real.rpow_pos_of_pos (by linarith [one_le_two_tiltK0 hβ (by positivity) hc2]) _

/-- The uniform bounds at `c = 3β/4` along a sequence of boxes `L_j → ∞`. -/
theorem eventually_diffLaw_bounds {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {A : Finset (ℤ × ℤ)}
    {w : ℤ × ℤ} (hw : w ∈ A) {Ls : ℕ → ℕ} (hLs : Tendsto Ls atTop atTop) {v v' : ℤ × ℤ}
    (hv : v ∈ A) (hv' : v' ∈ A) :
    ∃ C CX : ℝ, 0 ≤ C ∧ 0 ≤ CX ∧
      (∀ᶠ j in atTop, ∀ z : {z // z ∈ A}, ∫⁻ d, ENNReal.ofReal
        (Real.exp (3 * β / 4 * |((d z - d ⟨w, hw⟩ : ℤ) : ℝ)|)) ∂diffLaw β A w (Ls j) ≤
          ENNReal.ofReal C) ∧
      ∀ᶠ j in atTop, ∫⁻ d, ENNReal.ofReal (Real.exp (3 * β / 4 *
        |((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)|)) ∂diffLaw β A w (Ls j) ≤ ENNReal.ofReal CX := by
  have hc0 : (0 : ℝ) ≤ 3 * β / 4 := by positivity
  have hcβ : 3 * β / 4 < β := by linarith
  set bound : ℤ × ℤ → ℝ := fun z => 2 * expBoundBase β (3 * β / 4) ^ (2 * planeLinf z w)
  have hbound : ∀ z, 0 ≤ bound z := fun z => by
    have := expBoundBase_pos hβ hc0 hcβ; positivity
  refine ⟨∑ z ∈ A, bound z, 2 * expBoundBase β (3 * β / 4) ^ (2 * planeLinf v v'),
    Finset.sum_nonneg fun z _ => hbound z, by have := expBoundBase_pos hβ hc0 hcβ; positivity,
    ?_, ?_⟩
  · rw [Filter.eventually_all]
    intro z
    obtain ⟨L_z, hLz⟩ := diffLaw_exp_bound hβ hβ1 hc0 hcβ hw z.2 hw (A := A)
    filter_upwards [hLs.eventually_ge_atTop L_z] with j hj
    refine (hLz (Ls j) hj).trans (ENNReal.ofReal_le_ofReal ?_)
    exact Finset.single_le_sum (fun z _ => hbound z) z.2
  · obtain ⟨L_v, hLv⟩ := diffLaw_exp_bound hβ hβ1 hc0 hcβ hw hv hv'
    filter_upwards [hLs.eventually_ge_atTop L_v] with j hj
    exact hLv (Ls j) hj

/-- **Every vague limit point is a probability measure.** -/
theorem isProbabilityMeasure_limitPoint {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A) {Ls : ℕ → ℕ} (hLs : Tendsto Ls atTop atTop)
    {ν : Measure (DiffConfig A)}
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d}))) :
    IsProbabilityMeasure ν := by
  obtain ⟨C, CX, hC, hCX, hT, hX⟩ := eventually_diffLaw_bounds hβ hβ1 hw hLs hw hw
  have hprob : ∀ᶠ j in atTop, IsProbabilityMeasure (diffLaw β A w (Ls j)) := by
    filter_upwards [hLs.eventually_ge_atTop 1] with j hj
    exact isProbabilityMeasure_diffLaw hβ hβ1 A w hj
  constructor
  refine le_antisymm ?_ ?_
  · have h := lintegral_le_of_tendsto_singleton hν (fun _ => 1) (fun _ => ENNReal.one_ne_top)
      (B := 1) (by filter_upwards [hprob] with j hj; simp)
    simpa using h
  · have h := le_lintegral_limitPoint hβ.le hw hν (by positivity : (0 : ℝ) < 3 * β / 4) hC hCX
      hT (fun d => ((d ⟨w, hw⟩ - d ⟨w, hw⟩ : ℤ) : ℝ)) hX (g := fun _ => 1)
      (fun _ => ENNReal.one_ne_top) (fun η hη => ⟨1, zero_le_one, fun d => by
        rw [ENNReal.ofReal_one]; exact le_self_add⟩) (B₀ := 1)
      (by filter_upwards [hprob] with j hj; simp)
    simpa using h

/-- **(7.17) for `|ε| ≤ β/2` passes to every limit point.** -/
theorem le_lintegral_exp_limitPoint {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (ℤ × ℤ)} {w v v' : ℤ × ℤ} (hw : w ∈ A) (hv : v ∈ A) (hv' : v' ∈ A)
    {Ls : ℕ → ℕ} (hLs : Tendsto Ls atTop atTop) {ν : Measure (DiffConfig A)}
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d})))
    {ε : ℝ} (hε : |ε| ≤ β / 2) {B₀ : ℝ≥0∞}
    (hB₀ : ∀ᶠ j in atTop, B₀ ≤ ∫⁻ d, ENNReal.ofReal
      (Real.exp (ε * ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ))) ∂diffLaw β A w (Ls j)) :
    B₀ ≤ ∫⁻ d, ENNReal.ofReal (Real.exp (ε * ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ))) ∂ν := by
  obtain ⟨C, CX, hC, hCX, hT, hX⟩ := eventually_diffLaw_bounds hβ hβ1 hw hLs hv hv'
  refine le_lintegral_limitPoint hβ.le hw hν (by positivity : (0 : ℝ) < 3 * β / 4) hC hCX hT _ hX
    (fun _ => ENNReal.ofReal_ne_top) (fun η hη => ?_) hB₀
  obtain ⟨B, hB⟩ := exists_exp_le_add (a := β / 2) (b := 3 * β / 4) (η := η) (by positivity)
    (by linarith) hη
  refine ⟨max B 0, le_max_right _ _, fun d => ?_⟩
  set X : ℝ := ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)
  rw [← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_add (le_max_right _ _) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Real.exp (ε * X) ≤ Real.exp (β / 2 * |X|) := Real.exp_le_exp.mpr
    ((le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hε (abs_nonneg _)))
  have h2 := hB |X| (abs_nonneg X)
  have h3 : B ≤ max B 0 := le_max_left _ _
  linarith

/-- **(7.18) passes to every limit point.** -/
theorem le_lintegral_sq_limitPoint {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (ℤ × ℤ)} {w v v' : ℤ × ℤ} (hw : w ∈ A) (hv : v ∈ A) (hv' : v' ∈ A)
    {Ls : ℕ → ℕ} (hLs : Tendsto Ls atTop atTop) {ν : Measure (DiffConfig A)}
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d})))
    {B₀ : ℝ≥0∞}
    (hB₀ : ∀ᶠ j in atTop, B₀ ≤ ∫⁻ d, ENNReal.ofReal
      (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂diffLaw β A w (Ls j)) :
    B₀ ≤ ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂ν := by
  obtain ⟨C, CX, hC, hCX, hT, hX⟩ := eventually_diffLaw_bounds hβ hβ1 hw hLs hv hv'
  refine le_lintegral_limitPoint hβ.le hw hν (by positivity : (0 : ℝ) < 3 * β / 4) hC hCX hT _ hX
    (fun _ => ENNReal.ofReal_ne_top) (fun η hη => ?_) hB₀
  obtain ⟨B, hB⟩ := exists_sq_le_add (b := 3 * β / 4) (η := η) (by positivity) hη
  refine ⟨max B 0, le_max_right _ _, fun d => ?_⟩
  set X : ℝ := ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)
  rw [← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_add (le_max_right _ _) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 := hB |X| (abs_nonneg X)
  rw [sq_abs] at h2
  have h3 : B ≤ max B 0 := le_max_left _ _
  linarith

/-! ## Evenness, the ratio bound and divergence at the limit -/

theorem centeredSite_injOn {L R : ℕ} (hL : 2 * R + 1 ≤ L) {z z' : ℤ × ℤ}
    (hz1 : z.1.natAbs ≤ R) (hz2 : z.2.natAbs ≤ R) (hz1' : z'.1.natAbs ≤ R)
    (hz2' : z'.2.natAbs ≤ R) (h : centeredSite L z = centeredSite L z') : z = z' := by
  obtain ⟨a1, a2⟩ := centeredSite_val hL hz1 hz2
  obtain ⟨b1, b2⟩ := centeredSite_val hL hz1' hz2'
  rw [h] at a1 a2
  exact Prod.ext (by omega) (by omega)

theorem eventually_centeredSite_inj {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (hu : u ∈ A)
    {Ls : ℕ → ℕ} (hLs : Tendsto Ls atTop atTop) :
    ∀ᶠ j in atTop, ∀ z ∈ A, centeredSite (Ls j) z = centeredSite (Ls j) u → z = u := by
  filter_upwards [hLs.eventually_ge_atTop (2 * planeRadius A + 1)] with j hj z hz h
  obtain ⟨hz1, hz2⟩ := coord_le_planeRadius hz
  obtain ⟨hu1, hu2⟩ := coord_le_planeRadius hu
  exact centeredSite_injOn hj hz1 hz2 hu1 hu2 h

/-- **Evenness at the limit.** -/
theorem limitPoint_neg {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w : ℤ × ℤ} (hw : w ∈ A)
    {Ls : ℕ → ℕ} {ν : Measure (DiffConfig A)}
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d})))
    (d : DiffConfig A) : ν {-d} = ν {d} :=
  tendsto_nhds_unique (hν (-d)) ((hν d).congr fun j => (diffLaw_neg hβ hw (Ls j) d).symm)

/-- **The one-site ratio bound at the limit**, for `u ≠ w`. -/
theorem limitPoint_shift_ge {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w u : ℤ × ℤ}
    (hw : w ∈ A) (hu : u ∈ A) (huw : u ≠ w) {Ls : ℕ → ℕ} (hLs : Tendsto Ls atTop atTop)
    {ν : Measure (DiffConfig A)}
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d})))
    (d : DiffConfig A) (k : ℤ) :
    ENNReal.ofReal ((shiftConst β * Real.exp (-(β * |(k : ℝ)|))) ^ 4) * ν {d} ≤
      ν {d + k • Pi.single ⟨u, hu⟩ 1} := by
  refine le_of_tendsto_of_tendsto (ENNReal.Tendsto.const_mul (hν d)
    (Or.inr ENNReal.ofReal_ne_top)) (hν _) ?_
  filter_upwards [eventually_centeredSite_inj hu hLs] with j hj
  have hwu : centeredSite (Ls j) w ≠ centeredSite (Ls j) u := fun h => huw (hj w hw h).symm
  exact diffLaw_shift_ge hβ hw hu hj hwu d k

theorem mgfExt_limitPoint_neg {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w v v' : ℤ × ℤ}
    (hw : w ∈ A) (hv : v ∈ A) (hv' : v' ∈ A) {Ls : ℕ → ℕ} {ν : Measure (DiffConfig A)}
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d}))) (ε : ℝ) :
    mgfExt ν (fun d => ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)) (-ε) =
      mgfExt ν (fun d => ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)) ε := by
  unfold mgfExt
  rw [lintegral_countable', lintegral_countable', ← (Equiv.neg (DiffConfig A)).tsum_eq]
  refine tsum_congr fun d => ?_
  simp only [Equiv.neg_apply, Pi.neg_apply, limitPoint_neg hβ hw hν]
  congr 3
  push_cast
  ring

theorem exists_singleton_ne_zero {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] : ∃ a, ν {a} ≠ 0 := by
  by_contra h
  push Not at h
  have hz : ν = 0 := by
    rw [← Measure.sum_smul_dirac ν]
    simp [h]
  exact IsProbabilityMeasure.ne_zero ν hz

/-- **Divergence at the limit**: for `v ≠ v'` and `|ε| ≥ 4β` the moment of every limit point is
`∞`. -/
theorem mgfExt_limitPoint_eq_top {β : ℝ} (hβ : 0 ≤ β) {A : Finset (ℤ × ℤ)} {w v v' : ℤ × ℤ}
    (hw : w ∈ A) (hv : v ∈ A) (hv' : v' ∈ A) (hvv' : v ≠ v') {Ls : ℕ → ℕ}
    (hLs : Tendsto Ls atTop atTop) {ν : Measure (DiffConfig A)} [IsProbabilityMeasure ν]
    (hν : ∀ d, Tendsto (fun j => diffLaw β A w (Ls j) {d}) atTop (𝓝 (ν {d}))) {ε : ℝ}
    (hε : 4 * β ≤ |ε|) :
    mgfExt ν (fun d => ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ)) ε = ⊤ := by
  classical
  set X : DiffConfig A → ℝ := fun d => ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) with hX
  -- a direction `u ≠ w` that moves `X` by `σ k`
  obtain ⟨u, hu, huw, σ, hσ, hXshift⟩ : ∃ u, ∃ hu : u ∈ A, u ≠ w ∧ ∃ σ : ℤ, σ ^ 2 = 1 ∧
      ∀ (d : DiffConfig A) (k : ℤ),
        X (d + k • Pi.single (⟨u, hu⟩ : {z // z ∈ A}) (1 : ℤ)) = X d + (σ : ℝ) * (k : ℝ) := by
    by_cases hvw : v = w
    · refine ⟨v', hv', fun h => hvv' (hvw.trans h.symm), -1, by norm_num, fun d k => ?_⟩
      have hne : (⟨v, hv⟩ : {z // z ∈ A}) ≠ ⟨v', hv'⟩ := fun h => hvv' (congrArg Subtype.val h)
      simp only [hX, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
        smul_eq_mul, mul_zero, add_zero, mul_one]
      push_cast; ring
    · refine ⟨v, hv, hvw, 1, by norm_num, fun d k => ?_⟩
      have hne : (⟨v', hv'⟩ : {z // z ∈ A}) ≠ ⟨v, hv⟩ := fun h => hvv' (congrArg Subtype.val h).symm
      simp only [hX, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
        smul_eq_mul, mul_zero, add_zero, mul_one]
      push_cast; ring
  obtain ⟨d₀, hd₀⟩ := exists_singleton_ne_zero ν
  -- the sign making `ε σ s = |ε|`
  obtain ⟨s, hs, hεs⟩ : ∃ s : ℤ, s ^ 2 = 1 ∧ ε * (σ * s : ℤ) = |ε| := by
    rcases le_or_gt 0 ε with h | h
    · refine ⟨σ, hσ, ?_⟩
      have : ((σ * σ : ℤ) : ℝ) = 1 := by rw [← sq, hσ]; norm_num
      rw [this, mul_one, abs_of_nonneg h]
    · refine ⟨-σ, by rw [neg_sq, hσ], ?_⟩
      have : ((σ * -σ : ℤ) : ℝ) = -1 := by
        rw [mul_neg, ← sq, hσ]; norm_num
      rw [this, abs_of_neg h]; ring
  set g : ℕ → DiffConfig A := fun m => d₀ + ((s * m : ℤ)) • Pi.single (⟨u, hu⟩ : {z // z ∈ A}) 1
    with hg
  have hginj : Function.Injective g := by
    intro m m' h
    have h' := congrFun h ⟨u, hu⟩
    simp only [hg, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      add_right_inj] at h'
    have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    exact_mod_cast mul_left_cancel₀ hs0 h'
  set κ := shiftConst β
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ε * X d₀) * κ ^ 4) * ν {d₀} with hc₀
  have hc₀0 : c₀ ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr
    (mul_pos (Real.exp_pos _) (pow_pos (shiftConst_pos β) 4))).ne' hd₀
  have hterm : ∀ m : ℕ, c₀ ≤ ENNReal.ofReal (Real.exp (ε * X (g m))) * ν {g m} := by
    intro m
    have hsm : |((s * m : ℤ) : ℝ)| = m := by
      have hs1 : |(s : ℝ)| = 1 := by
        have hu' : IsUnit s := IsUnit.of_mul_eq_one s (by rw [← sq]; exact hs)
        rcases Int.isUnit_iff.mp hu' with h | h <;> simp [h]
      push_cast; rw [abs_mul, hs1, one_mul, Nat.abs_cast]
    have hratio := limitPoint_shift_ge hβ hw hu huw hLs hν d₀ (s * m)
    rw [hsm] at hratio
    have hX' : X (g m) = X d₀ + (σ : ℝ) * ((s * m : ℤ) : ℝ) := hXshift d₀ (s * m)
    calc c₀ = ENNReal.ofReal (Real.exp (ε * X d₀) * κ ^ 4) * ν {d₀} := rfl
      _ ≤ ENNReal.ofReal (Real.exp (ε * X d₀) * Real.exp (|ε| * m)) *
          (ENNReal.ofReal ((κ * Real.exp (-(β * m))) ^ 4) * ν {d₀}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        have hκ : 0 < κ := shiftConst_pos β
        have h1 : Real.exp (-(4 * β * m)) * Real.exp (|ε| * m) ≥ 1 := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
        have h2 : (κ * Real.exp (-(β * m))) ^ 4 = κ ^ 4 * Real.exp (-(4 * β * m)) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
        rw [h2]
        have h3 : 0 < Real.exp (ε * X d₀) * κ ^ 4 := by positivity
        nlinarith
      _ ≤ ENNReal.ofReal (Real.exp (ε * X (g m))) * ν {g m} := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) hratio
        rw [hX', ← Real.exp_add]
        congr 1
        rw [mul_add, show (σ * ((s * m : ℤ) : ℝ)) = ((σ * s : ℤ) : ℝ) * m by push_cast; ring,
          ← mul_assoc, hεs]
  unfold mgfExt
  rw [lintegral_countable', eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ∑' _m : ℕ, c₀ := (ENNReal.tsum_const_eq_top_of_ne_zero hc₀0).symm
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (Real.exp (ε * X (g m))) * ν {g m} := ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' d, ENNReal.ofReal (Real.exp (ε * X d)) * ν {d} :=
        ENNReal.tsum_comp_le_tsum_of_injective hginj
          (fun d => ENNReal.ofReal (Real.exp (ε * X d)) * ν {d})

/-! ## Existence of limit points -/

/-- **Existence of a vague limit point** of the laws along any sequence of boxes. -/
theorem exists_limitPoint_diffLaw {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (ℤ × ℤ))
    (w : ℤ × ℤ) {Ls : ℕ → ℕ} (hLs : Tendsto Ls atTop atTop) :
    ∃ (φs : ℕ → ℕ) (ν : Measure (DiffConfig A)), StrictMono φs ∧
      ∀ d, Tendsto (fun j => diffLaw β A w (Ls (φs j)) {d}) atTop (𝓝 (ν {d})) := by
  classical
  set x : ℕ → DiffConfig A → ℝ := fun j d => min (diffLaw β A w (Ls j) {d}).toReal 1 with hx
  have hS : IsCompact (Set.univ.pi fun _ : DiffConfig A => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hxS : ∀ j, x j ∈ Set.univ.pi fun _ : DiffConfig A => Set.Icc (0 : ℝ) 1 :=
    fun j d _ => ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  obtain ⟨p, -, φs, hφs, hlim⟩ := hS.tendsto_subseq hxS
  refine ⟨φs, Measure.sum fun d => ENNReal.ofReal (p d) • Measure.dirac d, hφs, fun d => ?_⟩
  have hν : (Measure.sum fun d => ENNReal.ofReal (p d) • Measure.dirac d) {d} =
      ENNReal.ofReal (p d) := by
    rw [Measure.sum_apply _ (measurableSet_singleton d)]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton d),
      Set.indicator, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [tsum_ite_eq]
  rw [hν]
  have hd := ENNReal.tendsto_ofReal ((tendsto_pi_nhds.mp hlim) d)
  refine hd.congr' ?_
  have hφ : Tendsto (fun j => Ls (φs j)) atTop atTop := hLs.comp hφs.tendsto_atTop
  filter_upwards [hφ.eventually_ge_atTop 1] with j hj
  have hprob := isProbabilityMeasure_diffLaw hβ hβ1 A w hj
  simp only [Function.comp_apply, hx]
  rw [min_eq_left (ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

end FroehlichSpencer.BKT.SOS.Literal

end
