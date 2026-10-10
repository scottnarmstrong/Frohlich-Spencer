/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.FejerAverage
public import FroehlichSpencer.BKT.Gaussian.ChargeSelection
public import FroehlichSpencer.BKT.Gaussian.IntegerField
public import FroehlichSpencer.BKT.Bridge.IntegerGFFObservable
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-volume Fejér cell limit
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

universe u v

open MeasureTheory Multigraph
open Filter
open scoped ENNReal Topology BoundedContinuousFunction

variable {V : Type u} {E : Type v}

instance countable_pinnedIntegerField [Fintype V] (root : V) :
    Countable (pinnedIntegerField V root) := by
  unfold pinnedIntegerField
  infer_instance

/-- The half-open real translate associated to one integer in the KP §5.1,
p. 4 decomposition into `2π`-period cells. -/
def gffFejerCellInterval (m : ℤ) : Set ℝ :=
  Set.Ico (2 * Real.pi * (m : ℝ) - Real.pi) (2 * Real.pi * (m : ℝ) + Real.pi)

/-- The KP §5.1, p. 4 product cell indexed by an integer field pinned to zero
at the root. -/
def gffFejerCell [Fintype V] (root : V) (m : pinnedIntegerField V root) : Set (V → ℝ) :=
  Set.univ.pi (fun j => gffFejerCellInterval (m.1 j))

/-- The representative cell `[-π,π)^V` in the KP §5.1, p. 4 cell
decomposition. -/
def gffFejerCellBox [Fintype V] : Set (V → ℝ) :=
  Set.univ.pi (fun _ : V => Set.Ico (-Real.pi) Real.pi)

/-- The pinned cell sets are measurable. -/
theorem measurableSet_gffFejerCell [Fintype V] [DecidableEq V]
    (root : V) (m : pinnedIntegerField V root) : MeasurableSet (gffFejerCell root m) := by
  apply MeasurableSet.univ_pi
  intro j
  exact measurableSet_Ico

/-- The compact representative cell is measurable. -/
theorem measurableSet_gffFejerCellBox [Fintype V] [DecidableEq V] :
    MeasurableSet (gffFejerCellBox (V := V)) := by
  apply MeasurableSet.univ_pi
  intro j
  exact measurableSet_Ico

/-- The center `2πm` of a root-pinned cell in the KP §5.1, p. 4
decomposition. -/
def gffFejerCellShift [Fintype V] {root : V} (m : pinnedIntegerField V root) : V → ℝ :=
  fun j => 2 * Real.pi * (m.1 j : ℝ)

/-- The KP §5.1, p. 4 Fejér kernel divided by its cell mass `2π`. -/
def gffNormalizedFejerKernel (N : ℕ) (x : ℝ) : ℝ :=
  fejerPolynomial N x / (2 * Real.pi)

/-- The normalized kernel has mass one on the KP period cell. -/
theorem integral_gffNormalizedFejerKernel (N : ℕ) :
    ∫ x in Set.Ico (-Real.pi) Real.pi, gffNormalizedFejerKernel N x = 1 := by
  have hperiod : -Real.pi ≤ Real.pi := by linarith only [Real.pi_pos]
  have hmass := fejerPolynomial_intervalIntegral N
  rw [intervalIntegral.integral_of_le hperiod,
    ← integral_Ico_eq_integral_Ioc] at hmass
  simp only [gffNormalizedFejerKernel, div_eq_mul_inv]
  rw [integral_mul_const]
  rw [hmass]
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  field_simp [hpi]

/-- Translation by the cell center identifies the representative box with its
period cell. -/
theorem mem_gffFejerCell_iff_mem_box_add_shift [Fintype V] [DecidableEq V]
    (root : V) (m : pinnedIntegerField V root) (t : V → ℝ) :
    (fun j => t j + gffFejerCellShift m j) ∈ gffFejerCell root m ↔
      t ∈ gffFejerCellBox (V := V) := by
  constructor
  · intro ht
    apply Set.mem_pi.mpr
    intro j hj
    have hcoord := (Set.mem_pi.mp ht) j (Set.mem_univ j)
    change t j ∈ Set.Ico (-Real.pi) Real.pi
    change 2 * Real.pi * (m.1 j : ℝ) - Real.pi ≤
        t j + 2 * Real.pi * (m.1 j : ℝ) ∧
      t j + 2 * Real.pi * (m.1 j : ℝ) <
        2 * Real.pi * (m.1 j : ℝ) + Real.pi at hcoord
    rw [Set.mem_Ico]
    exact ⟨by linarith only [hcoord.1], by linarith only [hcoord.2]⟩
  · intro ht
    apply Set.mem_pi.mpr
    intro j hj
    have hcoord := (Set.mem_pi.mp ht) j (Set.mem_univ j)
    change t j + gffFejerCellShift m j ∈ gffFejerCellInterval (m.1 j)
    change -Real.pi ≤ t j ∧ t j < Real.pi at hcoord
    change 2 * Real.pi * (m.1 j : ℝ) - Real.pi ≤
        t j + 2 * Real.pi * (m.1 j : ℝ) ∧
      t j + 2 * Real.pi * (m.1 j : ℝ) <
        2 * Real.pi * (m.1 j : ℝ) + Real.pi
    exact ⟨by linarith only [hcoord.1], by linarith only [hcoord.2]⟩

/-- Translation carries the representative-box integral exactly to the
corresponding period-cell integral. -/
theorem integral_gffFejerCell_eq_integral_box_translate [Fintype V]
    [DecidableEq V] (root : V) (m : pinnedIntegerField V root)
    (f : (V → ℝ) → ℝ) :
    ∫ φ in gffFejerCell root m, f φ =
      ∫ t in gffFejerCellBox (V := V),
        f (fun j => t j + gffFejerCellShift m j) := by
  let a : V → ℝ := gffFejerCellShift m
  let e : (V → ℝ) ≃ᵐ (V → ℝ) := MeasurableEquiv.addRight a
  have hmp : MeasurePreserving e (volume : Measure (V → ℝ))
      (volume : Measure (V → ℝ)) := by
    change MeasurePreserving (fun x : V → ℝ => x + a) _ _
    exact measurePreserving_add_right (volume : Measure (V → ℝ)) a
  calc
    ∫ φ in gffFejerCell root m, f φ =
        ∫ φ, (gffFejerCell root m).indicator f φ := by
          rw [← integral_indicator (measurableSet_gffFejerCell root m)]
    _ = ∫ t, (gffFejerCell root m).indicator f (e t) := by
          symm
          exact hmp.integral_comp e.measurableEmbedding _
    _ = ∫ t, (gffFejerCellBox (V := V)).indicator
        (fun t => f (e t)) t := by
          congr 1
          funext t
          have heq := mem_gffFejerCell_iff_mem_box_add_shift root m t
          change (e t) ∈ gffFejerCell root m ↔ t ∈ gffFejerCellBox (V := V) at heq
          by_cases ht : t ∈ gffFejerCellBox (V := V)
          · rw [Set.indicator_of_mem (heq.mpr ht), Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem (fun hc => ht (heq.mp hc)),
              Set.indicator_of_notMem ht]
    _ = ∫ t in gffFejerCellBox (V := V), f (e t) := by
          rw [integral_indicator (measurableSet_gffFejerCellBox (V := V))]

/-- Integrating a coordinate product over the representative box factors into
the corresponding one-dimensional interval integrals. -/
theorem integral_gffFejerCellBox_prod [Fintype V] [DecidableEq V]
    (f : V → ℝ → ℝ) :
    ∫ t in gffFejerCellBox (V := V), ∏ j, f j (t j) =
      ∏ j, ∫ x in Set.Ico (-Real.pi) Real.pi, f j x := by
  rw [← integral_indicator (measurableSet_gffFejerCellBox (V := V))]
  have hind (t : V → ℝ) :
      (gffFejerCellBox (V := V)).indicator
          (fun t => ∏ j, f j (t j)) t =
        ∏ j, (Set.Ico (-Real.pi) Real.pi).indicator (f j) (t j) := by
    by_cases ht : t ∈ gffFejerCellBox (V := V)
    · have ht' : ∀ j, t j ∈ Set.Ico (-Real.pi) Real.pi :=
        Set.mem_univ_pi.mp ht
      rw [Set.indicator_of_mem ht]
      apply Finset.prod_congr rfl
      intro j hj
      simp [ht' j]
    · have ht' : ¬ ∀ j, t j ∈ Set.Ico (-Real.pi) Real.pi :=
        mt Set.mem_univ_pi.mpr ht
      push Not at ht'
      obtain ⟨j, hj⟩ := ht'
      rw [Set.indicator_of_notMem ht]
      rw [Finset.prod_eq_zero (Finset.mem_univ j)]
      simp [hj]
  simp_rw [hind]
  rw [integral_fintype_prod_volume_eq_prod]
  congr 1
  funext j
  rw [integral_indicator measurableSet_Ico]

/-- The product of the normalized one-dimensional Fejér kernels has unit
mass on the representative cell. -/
theorem integral_gffProductFejerKernel [Fintype V] [DecidableEq V]
    (N : ℕ) :
    ∫ t in gffFejerCellBox (V := V),
      ∏ j, gffNormalizedFejerKernel N (t j) = 1 := by
  rw [integral_gffFejerCellBox_prod]
  simp [integral_gffNormalizedFejerKernel]

/-- The normalized Fejér mass outside a fixed neighborhood of zero vanishes
at rate `1/N`. -/
theorem integral_gffNormalizedFejerKernel_tail (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    ∫ x in Set.Ico (-Real.pi) Real.pi,
      (if δ ≤ |x| then gffNormalizedFejerKernel N x else 0) ≤
        1 / ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
  let I : Set ℝ := Set.Ico (-Real.pi) Real.pi
  let T : Set ℝ := {x | δ ≤ |x|}
  let K : ℝ → ℝ := gffNormalizedFejerKernel N
  let c : ℝ := 1 / ((2 * Real.pi) * (N : ℝ) * Real.sin (δ / 2) ^ 2)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hKcont : Continuous K := by
    change Continuous (fun x => fejerPolynomial N x / (2 * Real.pi))
    unfold fejerPolynomial fejerCosineCoefficient
    fun_prop
  have hKcompact : IntegrableOn K (Set.Icc (-Real.pi) Real.pi) :=
    hKcont.continuousOn.integrableOn_compact isCompact_Icc
  have hKint : IntegrableOn K I := hKcompact.mono_set (by
    intro x hx
    exact ⟨(Set.mem_Ico.mp hx).1, (Set.mem_Ico.mp hx).2.le⟩)
  have hT : MeasurableSet T := measurableSet_le measurable_const
    continuous_abs.measurable
  have hfi : IntegrableOn (T.indicator K) I := hKint.indicator hT
  have hci : IntegrableOn (fun _ : ℝ => c) I :=
    integrableOn_const (measure_Ico_lt_top.ne)
  have hpoint (x : ℝ) (hx : x ∈ I) : (T.indicator K) x ≤ c := by
    by_cases htail : x ∈ T
    · have hxabs : |x| ≤ Real.pi := by
        rcases Set.mem_Ico.mp hx with ⟨hlo, hhi⟩
        rw [abs_le]
        constructor <;> linarith [Real.pi_pos]
      have hpoly := fejerPolynomial_tail_bound N hN δ hδ hδπ x htail hxabs
      have hKbound : K x ≤ c := by
        dsimp [K, c, gffNormalizedFejerKernel]
        have hp : 0 < 2 * Real.pi := by positivity
        have hs : 0 < (N : ℝ) * Real.sin (δ / 2) ^ 2 := by
          have hsin : 0 < Real.sin (δ / 2) := by
            apply Real.sin_pos_of_pos_of_lt_pi
            · linarith only [hδ]
            · linarith only [hδπ, Real.pi_pos]
          exact mul_pos (by exact_mod_cast hN) (sq_pos_of_pos hsin)
        calc
          fejerPolynomial N x / (2 * Real.pi) ≤
              (1 / ((N : ℝ) * Real.sin (δ / 2) ^ 2)) / (2 * Real.pi) :=
            (div_le_div_iff_of_pos_right hp).2 hpoly
          _ = c := by
            dsimp [c]
            ring
      simpa [T, htail] using hKbound
    · simp [Set.indicator_of_notMem htail, hc]
  calc
    ∫ x in I, (if δ ≤ |x| then K x else 0) =
        ∫ x in I, T.indicator K x := by
          rfl
    _ ≤ ∫ x in I, c := setIntegral_mono_on hfi hci measurableSet_Ico hpoint
    _ = 1 / ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
          have hlen : Real.pi - -Real.pi = 2 * Real.pi := by ring
          have hsin : Real.sin (δ / 2) ≠ 0 := by
            exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith only [hδ])
              (by linarith only [hδπ, Real.pi_pos]))
          rw [integral_const]
          simp [Measure.real, I, Real.volume_Ico, hlen, c]
          rw [ENNReal.toReal_ofReal Real.pi_nonneg]
          field_simp [ne_of_gt Real.pi_pos, hsin,
            (by exact_mod_cast Nat.ne_of_gt hN : (N : ℝ) ≠ 0)]

/-- Under the product Fejér kernel, the mass where one specified coordinate
leaves a fixed neighborhood of zero is bounded by the one-dimensional tail. -/
theorem integral_gffProductFejerKernel_coordinate_tail [Fintype V]
    [DecidableEq V] (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ)
    (hδπ : δ ≤ Real.pi) (j : V) :
    ∫ t in gffFejerCellBox (V := V),
      ({x | δ ≤ |x|}).indicator (fun _ : ℝ => 1) (t j) *
        ∏ i, gffNormalizedFejerKernel N (t i) ≤
      1 / ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
  let T : Set ℝ := {x | δ ≤ |x|}
  have hfactor (i : V) :
      ∫ x in Set.Ico (-Real.pi) Real.pi,
        (if i = j then T.indicator (fun _ : ℝ => 1) x *
          gffNormalizedFejerKernel N x else gffNormalizedFejerKernel N x) =
        if i = j then
          ∫ x in Set.Ico (-Real.pi) Real.pi,
            (if δ ≤ |x| then gffNormalizedFejerKernel N x else 0)
      else 1 := by
    split_ifs with hij
    · subst i
      have heq : (fun x : ℝ => T.indicator (fun _ : ℝ => 1) x *
          gffNormalizedFejerKernel N x) =
          fun x => if δ ≤ |x| then gffNormalizedFejerKernel N x else 0 := by
        funext x
        by_cases hx : δ ≤ |x| <;> simp [T, hx]
      rw [heq]
    · simp [integral_gffNormalizedFejerKernel N]
  have hpoint (t : V → ℝ) :
      T.indicator (fun _ : ℝ => 1) (t j) *
          ∏ i, gffNormalizedFejerKernel N (t i) =
        ∏ i, (if i = j then
          T.indicator (fun _ : ℝ => 1) (t i) * gffNormalizedFejerKernel N (t i)
          else gffNormalizedFejerKernel N (t i)) := by
    let q : V → ℝ := fun i => if i = j then
      T.indicator (fun _ : ℝ => 1) (t i) * gffNormalizedFejerKernel N (t i)
      else gffNormalizedFejerKernel N (t i)
    calc
      T.indicator (fun _ : ℝ => 1) (t j) *
          ∏ i, gffNormalizedFejerKernel N (t i) =
          (T.indicator (fun _ : ℝ => 1) (t j) *
            gffNormalizedFejerKernel N (t j)) *
            ∏ i ∈ Finset.univ.erase j, gffNormalizedFejerKernel N (t i) := by
              rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
              ring
      _ = q j * ∏ i ∈ Finset.univ.erase j, q i := by
          congr 1
          · simp [q]
          · apply Finset.prod_congr rfl
            intro i hi
            have hij : i ≠ j := (Finset.mem_erase.mp hi).1
            simp [q, hij]
      _ = ∏ i, q i :=
          Finset.mul_prod_erase Finset.univ q (Finset.mem_univ j)
      _ = ∏ i, (if i = j then T.indicator (fun _ : ℝ => 1) (t i) *
          gffNormalizedFejerKernel N (t i) else gffNormalizedFejerKernel N (t i)) := rfl
  calc
    ∫ t in gffFejerCellBox (V := V), T.indicator (fun _ : ℝ => 1) (t j) *
        ∏ i, gffNormalizedFejerKernel N (t i) =
      ∫ t in gffFejerCellBox (V := V), ∏ i,
        (if i = j then T.indicator (fun _ : ℝ => 1) (t i) *
          gffNormalizedFejerKernel N (t i) else gffNormalizedFejerKernel N (t i)) := by
            apply integral_congr_ae
            filter_upwards with t
            exact hpoint t
    _ = ∏ i, ∫ x in Set.Ico (-Real.pi) Real.pi,
        (if i = j then T.indicator (fun _ : ℝ => 1) x *
          gffNormalizedFejerKernel N x else gffNormalizedFejerKernel N x) := by
            exact integral_gffFejerCellBox_prod
              (fun i x => if i = j then T.indicator (fun _ : ℝ => 1) x *
                gffNormalizedFejerKernel N x else gffNormalizedFejerKernel N x)
    _ ≤ 1 / ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
          simp_rw [hfactor]
          let a := ∫ x in Set.Ico (-Real.pi) Real.pi,
            (if δ ≤ |x| then gffNormalizedFejerKernel N x else 0)
          have hprod : ∏ i, (if i = j then a else 1) = a := by
            rw [← Finset.mul_prod_erase Finset.univ (fun i => if i = j then a else 1)
              (Finset.mem_univ j)]
            simp
          rw [hprod]
          simpa [a] using integral_gffNormalizedFejerKernel_tail N hN δ hδ hδπ

/-- The product Fejér kernels form an approximate identity on the compact
representative cell. -/
theorem tendsto_integral_gffProductFejerKernel [Fintype V] [DecidableEq V]
    (H : (V → ℝ) → ℝ) (hH : Continuous H) :
    Tendsto (fun N : ℕ =>
      ∫ t in gffFejerCellBox (V := V), H t *
        ∏ j, gffNormalizedFejerKernel N (t j)) atTop (𝓝 (H 0)) := by
  classical
  let Cbox : Set (V → ℝ) := Set.univ.pi (fun _ : V => Set.Icc (-Real.pi) Real.pi)
  let K (N : ℕ) (t : V → ℝ) : ℝ :=
    ∏ j, gffNormalizedFejerKernel N (t j)
  let D (t : V → ℝ) : ℝ := H t - H 0
  have hcompact : IsCompact Cbox := isCompact_univ_pi fun _ => isCompact_Icc
  have hboxsub : gffFejerCellBox (V := V) ⊆ Cbox := by
    intro t ht
    apply Set.mem_univ_pi.mpr
    intro j
    rcases (Set.mem_univ_pi.mp ht) j with ⟨hl, hu⟩
    exact ⟨hl, hu.le⟩
  have hDcont : Continuous D := by
    dsimp [D]
    fun_prop
  obtain ⟨M₀, hM₀⟩ := hcompact.exists_bound_of_continuousOn hDcont.continuousOn
  let M : ℝ := max M₀ 0
  have hMnonneg : 0 ≤ M := le_max_right _ _
  have hMbound (t : V → ℝ) (ht : t ∈ Cbox) : |D t| ≤ M := by
    have h := hM₀ t ht
    dsimp [M, D]
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hδcont (ε : ℝ) (hε : 0 < ε) :
      ∃ η > 0, ∀ t, dist t 0 < η → |D t| < ε := by
    obtain ⟨η, hη, hηbound⟩ :=
      (Metric.continuousAt_iff.mp hDcont.continuousAt) ε hε
    refine ⟨η, hη, ?_⟩
    intro t ht
    have h := hηbound ht
    simpa [D, Real.dist_eq] using h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let ε₀ : ℝ := ε / 2
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; linarith only [hε]
  obtain ⟨η, hη, hηbound⟩ := hδcont ε₀ hε₀
  let δ : ℝ := min η (Real.pi / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hη (by positivity)
  have hδη : δ ≤ η := min_le_left _ _
  have hδπ : δ ≤ Real.pi := by
    dsimp [δ]
    have h := min_le_right η (Real.pi / 2)
    linarith only [h, Real.pi_pos]
  have hsin : 0 < Real.sin (δ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith only [hδ]
    · linarith only [hδπ, Real.pi_pos]
  let bad : V → Set (V → ℝ) := fun j => {t | δ ≤ |t j|}
  have hbadMeas (j : V) : MeasurableSet (bad j) := by
    apply measurableSet_le measurable_const
    exact continuous_abs.measurable.comp (measurable_pi_apply j)
  have hKcont (N : ℕ) : Continuous (K N) := by
    have hpoly : Continuous (fejerPolynomial N) := by
      unfold fejerPolynomial fejerCosineCoefficient
      fun_prop
    have hnorm : Continuous (gffNormalizedFejerKernel N) := by
      unfold gffNormalizedFejerKernel
      exact hpoly.div_const (2 * Real.pi)
    dsimp [K]
    exact continuous_finsetProd Finset.univ fun j hj =>
      hnorm.comp (continuous_apply j)
  have hDBoxInt : ∀ N, IntegrableOn (fun t => D t * K N t)
      (gffFejerCellBox (V := V)) := by
    intro N
    have hcont : Continuous (fun t => D t * K N t) := hDcont.mul (hKcont N)
    exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set hboxsub
  have hKBoxInt : ∀ N, IntegrableOn (K N) (gffFejerCellBox (V := V)) := by
    intro N
    exact ((hKcont N).continuousOn.integrableOn_compact hcompact).mono_set hboxsub
  have hHBoxInt : ∀ N, IntegrableOn (fun t => H t * K N t)
      (gffFejerCellBox (V := V)) := by
    intro N
    have hcont : Continuous (fun t => H t * K N t) := hH.mul (hKcont N)
    exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set hboxsub
  have hmass (N : ℕ) :
      ∫ t in gffFejerCellBox (V := V), K N t = 1 := by
    dsimp [K]
    exact integral_gffProductFejerKernel N
  have hRBoxInt (N : ℕ) : IntegrableOn
      (fun t => ε₀ * K N t + M * ∑ j, (bad j).indicator (K N) t)
      (gffFejerCellBox (V := V)) := by
    have hsum : IntegrableOn (fun t => ∑ j, (bad j).indicator (K N) t)
        (gffFejerCellBox (V := V)) := by
      change Integrable (fun t => ∑ j, (bad j).indicator (K N) t)
        (volume.restrict (gffFejerCellBox (V := V)))
      simpa only [← Finset.sum_apply] using
        (integrable_finsetSum Finset.univ (fun j hj =>
          (hKBoxInt N).indicator (hbadMeas j)))
    change Integrable (fun t => ε₀ * K N t + M * ∑ j, (bad j).indicator (K N) t)
      (volume.restrict (gffFejerCellBox (V := V)))
    have hKint : Integrable (K N) (volume.restrict (gffFejerCellBox (V := V))) :=
      hKBoxInt N
    have hsumint : Integrable (fun t => ∑ j, (bad j).indicator (K N) t)
        (volume.restrict (gffFejerCellBox (V := V))) := hsum
    exact (hKint.const_mul ε₀).add (hsumint.const_mul M)
  have hbadmass (N : ℕ) (hN : 0 < N) (j : V) :
      ∫ t in gffFejerCellBox (V := V), (bad j).indicator (K N) t ≤
        1 / ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
    have hfun (t : V → ℝ) : (bad j).indicator (K N) t =
        ({x | δ ≤ |x|}).indicator (fun _ : ℝ => 1) (t j) * K N t := by
      by_cases ht : δ ≤ |t j| <;> simp [bad, K, ht]
    rw [show (fun t => (bad j).indicator (K N) t) =
      fun t => ({x | δ ≤ |x|}).indicator (fun _ : ℝ => 1) (t j) * K N t
      from funext hfun]
    dsimp [K]
    exact integral_gffProductFejerKernel_coordinate_tail N hN δ hδ hδπ j
  have hdiff (N : ℕ) :
      |(∫ t in gffFejerCellBox (V := V), H t * K N t) - H 0| =
        |∫ t in gffFejerCellBox (V := V), D t * K N t| := by
    have hconst : ∫ t in gffFejerCellBox (V := V), H 0 * K N t = H 0 := by
      rw [integral_const_mul, hmass N, mul_one]
    have hsub := integral_sub (hHBoxInt N)
      ((hKBoxInt N).const_mul (H 0))
    have hEq : (∫ t in gffFejerCellBox (V := V), H t * K N t) - H 0 =
        ∫ t in gffFejerCellBox (V := V), D t * K N t := by
      calc
        _ = (∫ t in gffFejerCellBox (V := V), H t * K N t) -
              ∫ t in gffFejerCellBox (V := V), H 0 * K N t :=
                congrArg (fun x : ℝ =>
                  (∫ t in gffFejerCellBox (V := V), H t * K N t) - x) hconst.symm
        _ = ∫ t in gffFejerCellBox (V := V),
              (H t * K N t - H 0 * K N t) := hsub.symm
        _ = ∫ t in gffFejerCellBox (V := V), D t * K N t := by
              congr 1
              funext t
              dsimp [D]
              ring
    rw [hEq]
  have hdeviation (t : V → ℝ) (ht : t ∈ gffFejerCellBox (V := V)) :
      |D t| ≤ ε₀ + M * ∑ j, (bad j).indicator (fun _ : V → ℝ => (1 : ℝ)) t := by
    by_cases hgood : ∀ j, ¬ δ ≤ |t j|
    · have hdist : dist t 0 < η := by
        apply (dist_pi_lt_iff hη).2
        intro j
        have hj : |t j| < δ := lt_of_not_ge (hgood j)
        have : |t j| < η := lt_of_lt_of_le hj hδη
        simpa [Real.dist_eq] using this
      have hsmall := hηbound t hdist
      have hsum : ∑ j, (bad j).indicator (fun _ : V → ℝ => (1 : ℝ)) t = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp [bad, hgood j]
      calc
        |D t| ≤ ε₀ := hsmall.le
        _ = ε₀ + M * 0 := by ring
        _ = ε₀ + M * ∑ j, (bad j).indicator (fun _ : V → ℝ => (1 : ℝ)) t := by
          exact congrArg (fun x : ℝ => ε₀ + M * x) hsum.symm
    · push Not at hgood
      obtain ⟨j, hj⟩ := hgood
      have hclosed : t ∈ Cbox := by
        apply Set.mem_univ_pi.mpr
        intro i
        rcases (Set.mem_univ_pi.mp ht) i with ⟨hl, hu⟩
        exact ⟨hl, hu.le⟩
      have hsum : (1 : ℝ) ≤ ∑ i, (bad i).indicator (fun _ : V → ℝ => (1 : ℝ)) t := by
        have hnonneg (i : V) : 0 ≤ (bad i).indicator (fun _ : V → ℝ => (1 : ℝ)) t := by
          by_cases hi : t ∈ bad i <;> simp [hi]
        have hs := Finset.single_le_sum (s := Finset.univ)
          (fun i hi => hnonneg i) (Finset.mem_univ j)
        have hj' : t ∈ bad j := by simpa [bad] using hj
        have hval : (bad j).indicator (fun _ : V → ℝ => (1 : ℝ)) t = 1 := by
          rw [Set.indicator_of_mem hj']
        rw [hval] at hs
        exact hs
      have hbound := hMbound t hclosed
      have hMsum := mul_le_mul_of_nonneg_left hsum hMnonneg
      have hMsum' : M ≤ M * ∑ i, (bad i).indicator (fun _ : V → ℝ => (1 : ℝ)) t := by
        simpa only [mul_one] using hMsum
      exact hbound.trans (by linarith only [hMsum', hε₀])
  have hprodDeviation (N : ℕ) (hN : 0 < N) (t : V → ℝ)
      (ht : t ∈ gffFejerCellBox (V := V)) :
      |D t * K N t| ≤ ε₀ * K N t +
        M * ∑ j, (bad j).indicator (K N) t := by
    have hKnonneg : 0 ≤ K N t := by
      dsimp [K]
      apply Finset.prod_nonneg
      intro j hj
      dsimp [gffNormalizedFejerKernel]
      exact div_nonneg (fejerPolynomial_nonneg N hN (t j)) (by positivity)
    have hterm (j : V) : (bad j).indicator (fun _ : V → ℝ => (1 : ℝ)) t * K N t =
        (bad j).indicator (K N) t := by
      by_cases hj : t ∈ bad j <;> simp [hj]
    have hsum : (∑ j, (bad j).indicator (fun _ : V → ℝ => (1 : ℝ)) t) * K N t =
        ∑ j, (bad j).indicator (K N) t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j
    rw [abs_mul, abs_of_nonneg hKnonneg]
    have hd := hdeviation t ht
    rw [← hsum]
    nlinarith only [hKnonneg, hd, mul_nonneg hKnonneg (abs_nonneg (D t))]
  have hboundIntegral (N : ℕ) (hN : 0 < N) :
      |(∫ t in gffFejerCellBox (V := V), H t * K N t) - H 0| ≤
        ε₀ + M * (Fintype.card V : ℝ) /
          ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
    rw [hdiff N]
    calc
      |∫ t in gffFejerCellBox (V := V), D t * K N t| ≤
          ∫ t in gffFejerCellBox (V := V), |D t * K N t| :=
            abs_integral_le_integral_abs
      _ ≤ ∫ t in gffFejerCellBox (V := V),
            (ε₀ * K N t + M * ∑ j, (bad j).indicator (K N) t) :=
            setIntegral_mono_on ((hDBoxInt N).norm) (hRBoxInt N)
              (measurableSet_gffFejerCellBox (V := V)) (fun t ht => hprodDeviation N hN t ht)
      _ ≤ ε₀ + M * (Fintype.card V : ℝ) /
          ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
            have hKint : IntegrableOn (K N) (gffFejerCellBox (V := V)) :=
              hKBoxInt N
            have hεint : IntegrableOn (fun t => ε₀ * K N t)
                (gffFejerCellBox (V := V)) := hKint.const_mul ε₀
            have hsumInt : IntegrableOn (fun t => ∑ j,
                (bad j).indicator (K N) t) (gffFejerCellBox (V := V)) := by
              change Integrable (fun t => ∑ j, (bad j).indicator (K N) t)
                (volume.restrict (gffFejerCellBox (V := V)))
              simpa only [← Finset.sum_apply] using
                (integrable_finsetSum Finset.univ (fun j hj =>
                  hKint.indicator (hbadMeas j)))
            have hMInt : IntegrableOn (fun t => M * ∑ j,
                (bad j).indicator (K N) t) (gffFejerCellBox (V := V)) :=
              hsumInt.const_mul M
            have hbadInt (j : V) : IntegrableOn ((bad j).indicator (K N))
                (gffFejerCellBox (V := V)) := hKint.indicator (hbadMeas j)
            have hsumIntegral :
                ∫ t in gffFejerCellBox (V := V),
                  ∑ j, (bad j).indicator (K N) t =
                ∑ j, ∫ t in gffFejerCellBox (V := V), (bad j).indicator (K N) t := by
              simpa only [← Finset.sum_apply] using
                (integral_finsetSum Finset.univ (fun j hj => hbadInt j))
            rw [integral_add hεint hMInt, integral_const_mul, hmass N, mul_one,
              integral_const_mul, hsumIntegral]
            · have htails :
                (∑ j, ∫ t in gffFejerCellBox (V := V),
                  (bad j).indicator (K N) t) ≤
                  (Fintype.card V : ℝ) /
                    ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
                  calc
                    _ ≤ ∑ j, 1 /
                        ((N : ℝ) * Real.sin (δ / 2) ^ 2) :=
                      Finset.sum_le_sum fun j hj => hbadmass N hN j
                    _ = (Fintype.card V : ℝ) /
                        ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
                          have hsin' : Real.sin (δ / 2) ≠ 0 := ne_of_gt hsin
                          have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
                          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                          field_simp [hsin', hN']
              have hmul := mul_le_mul_of_nonneg_left htails hMnonneg
              have hmul' : M * (∑ j, ∫ t in gffFejerCellBox (V := V),
                  (bad j).indicator (K N) t) ≤
                  M * (Fintype.card V : ℝ) /
                    ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
                calc
                  _ ≤ M * ((Fintype.card V : ℝ) /
                      ((N : ℝ) * Real.sin (δ / 2) ^ 2)) := hmul
                  _ = _ := by ring
              nlinarith only [hmul']
  let A : ℝ := M * (Fintype.card V : ℝ)
  let s : ℝ := Real.sin (δ / 2) ^ 2
  have hs : 0 < s := sq_pos_of_pos hsin
  have hden : Tendsto (fun N : ℕ => (N : ℝ) * s) atTop atTop :=
    by simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop hs
  have hfrac : Tendsto (fun N : ℕ => A / ((N : ℝ) * s)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hsmall : ∀ᶠ N : ℕ in atTop, A / ((N : ℝ) * s) < ε / 2 :=
    hfrac.eventually (Iio_mem_nhds (by linarith only [hε]))
  filter_upwards [hsmall, eventually_gt_atTop 0] with N hsmall hN
  have hAeq : M * (Fintype.card V : ℝ) /
      ((N : ℝ) * Real.sin (δ / 2) ^ 2) = A / ((N : ℝ) * s) := by
    rfl
  have hfinal := hboundIntegral N hN
  rw [hAeq] at hfinal
  have htotal : ε₀ + A / ((N : ℝ) * s) < ε := by
    dsimp [ε₀]
    linarith only [hsmall]
  exact lt_of_le_of_lt hfinal htotal

/-- The field `2πm+t` in the KP §5.1, p. 4 translated cell indexed by pinned
`m`. -/
def gffFejerCellField [Fintype V] {root : V} (m : pinnedIntegerField V root)
    (t : V → ℝ) : V → ℝ := fun j => t j + gffFejerCellShift m j

/-- The continuous factor `exp(⟨2πm+t,g⟩ - β Q(2πm+t)/2)` in the KP §5.1,
p. 4 cell integral. -/
noncomputable def gffFejerCellObservable (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (β : ℝ) {root : V}
    (g : V → ℝ) (m : pinnedIntegerField V root) (t : V → ℝ) : ℝ :=
  Real.exp (Multigraph.pairing (gffFejerCellField m t) g -
    (β / 2) * G.energy (gffFejerCellField m t))

/-- The normalized product-Fejér integral on one translated KP §5.1, p. 4
cell. -/
noncomputable def gffFejerCellIntegral (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (β : ℝ) {root : V}
    (g : V → ℝ) (N : ℕ) (m : pinnedIntegerField V root) : ℝ :=
  ∫ t in gffFejerCellBox (V := V),
    gffFejerCellObservable G β g m t *
      ∏ j, gffNormalizedFejerKernel N (t j)

/-- The raw Fejér product is `(2π)^|V|` times the normalized product kernel. -/
theorem gffFejerWeight_eq_two_pi_pow_mul_normalized [Fintype V]
    (N : ℕ) (φ : V → ℝ) :
    gffFejerWeight N φ = (2 * Real.pi) ^ Fintype.card V *
      ∏ j, gffNormalizedFejerKernel N (φ j) := by
  unfold gffFejerWeight
  calc
    (∏ j, fejerPolynomial N (φ j)) =
        ∏ j, ((2 * Real.pi) * gffNormalizedFejerKernel N (φ j)) := by
          apply Finset.prod_congr rfl
          intro j hj
          simp only [gffNormalizedFejerKernel]
          field_simp [ne_of_gt (by positivity : 0 < 2 * Real.pi)]
    _ = (∏ _j : V, (2 * Real.pi)) *
        ∏ j, gffNormalizedFejerKernel N (φ j) := Finset.prod_mul_distrib
    _ = _ := by simp

/-- The translated cell observable is continuous. -/
theorem continuous_gffFejerCellObservable (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (β : ℝ) {root : V}
    (g : V → ℝ) (m : pinnedIntegerField V root) :
    Continuous (gffFejerCellObservable G β g m) := by
  have hc (j : V) : Continuous (fun t : V → ℝ =>
      t j + gffFejerCellShift m j) := (continuous_apply j).add continuous_const
  have hp : Continuous (fun t : V → ℝ =>
      Multigraph.pairing (fun j => t j + gffFejerCellShift m j) g) := by
    unfold Multigraph.pairing
    exact continuous_finsetSum Finset.univ fun j hj =>
      (hc j).mul continuous_const
  have hE : Continuous (fun t : V → ℝ =>
      G.energy (fun j => t j + gffFejerCellShift m j)) := by
    unfold Multigraph.energy Multigraph.grad
    exact continuous_finsetSum Finset.univ fun e he =>
      ((hc (G.src e)).sub (hc (G.tgt e))).pow 2
  unfold gffFejerCellObservable
  exact Real.continuous_exp.comp (hp.sub (continuous_const.mul hE))

/-- Scaling a field by a real scalar scales the edge-once energy quadratically. -/
theorem energy_smul_field (G : Multigraph V E) [Fintype E] (c : ℝ)
    (f : V → ℝ) : G.energy (fun j => c * f j) = c ^ 2 * G.energy f := by
  unfold Multigraph.energy Multigraph.grad
  calc
    (∑ e, (c * f (G.src e) - c * f (G.tgt e)) ^ 2) =
        ∑ e, c ^ 2 * (f (G.src e) - f (G.tgt e)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro e he
          ring
    _ = c ^ 2 * ∑ e, (f (G.src e) - f (G.tgt e)) ^ 2 :=
      (Finset.mul_sum Finset.univ _ _).symm

/-- The cell-center energy is the integer-field energy with the factor `(2π)^2`. -/
theorem energy_gffFejerCellShift (G : Multigraph V E) [Fintype V] [Fintype E]
    {root : V} (m : pinnedIntegerField V root) :
    G.energy (gffFejerCellShift m) = (2 * Real.pi) ^ 2 *
      G.energy (fun j => (m.1 j : ℝ)) := by
  have hshift : gffFejerCellShift m = fun j => (2 * Real.pi) * (m.1 j : ℝ) := by
    funext j
    simp [gffFejerCellShift]
  rw [hshift, energy_smul_field]

/-- The observable at a cell center contributes the factor `2π ⟨m,g⟩`. -/
theorem pairing_gffFejerCellShift [Fintype V]
    {root : V} (m : pinnedIntegerField V root) (g : V → ℝ) :
    Multigraph.pairing (gffFejerCellShift m) g =
      2 * Real.pi * Multigraph.pairing (fun j => (m.1 j : ℝ)) g := by
  unfold Multigraph.pairing gffFejerCellShift
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring


noncomputable def gffFejerCellDecay (V : Type u) [Fintype V] (β : ℝ) : ℝ :=
  gffGaussianRate V β * Real.pi ^ 2 / 2


noncomputable def gffFejerCellTiltConstant (V : Type u) [Fintype V]
    (β : ℝ) (g : V → ℝ) : ℝ :=
  Real.exp (β * (Fintype.card V : ℝ) * Real.pi ^ 2 /
      (2 * gffPoincareConstant V) +
    Real.pi * ∑ j, |g j| +
      Real.pi ^ 2 / gffFejerCellDecay V β * ∑ j, (g j) ^ 2)


noncomputable def gffFejerCellMajorant (V : Type u) [Fintype V]
    (β : ℝ) (g : V → ℝ) (m : V → ℤ) : ℝ :=
  gffFejerCellTiltConstant V β g * intGaussianPiV V (gffFejerCellDecay V β) m

private theorem pi_mul_abs_int_le_abs_period_shift (z : ℤ) (x : ℝ)
    (hx₁ : -Real.pi ≤ x) (hx₂ : x < Real.pi) :
    Real.pi * |(z : ℝ)| ≤ |x + 2 * Real.pi * (z : ℝ)| := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have hz' : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
    have habs : |(z : ℝ)| = -(z : ℝ) := abs_of_nonpos (by linarith only [hz'])
    have hm : Real.pi * (z : ℝ) ≤ -Real.pi := by
      calc
        Real.pi * (z : ℝ) ≤ Real.pi * (-1) :=
          mul_le_mul_of_nonneg_left hz' Real.pi_pos.le
        _ = -Real.pi := by ring
    have hupper : x + 2 * Real.pi * (z : ℝ) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hz'
        (show 0 ≤ 2 * Real.pi by positivity)]
    rw [habs, abs_of_nonpos hupper]
    nlinarith only [hx₂, hm]
  · subst z
    simp
  · have hz' : (1 : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ z by omega)
    have habs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg (by linarith only [hz'])
    have hlower : 0 ≤ x + 2 * Real.pi * (z : ℝ) := by
      nlinarith only [hx₁, hx₂, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hz')]
    rw [habs, abs_of_nonneg hlower]
    nlinarith only [hx₁, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hz')]

private theorem pi_mul_abs_int_sq_le_period_shift_sq (z : ℤ) (x : ℝ)
    (hx₁ : -Real.pi ≤ x) (hx₂ : x < Real.pi) :
    (Real.pi * |(z : ℝ)|) ^ 2 ≤ (x + 2 * Real.pi * (z : ℝ)) ^ 2 := by
  have habs := pi_mul_abs_int_le_abs_period_shift z x hx₁ hx₂
  have hnonneg : 0 ≤ Real.pi * |(z : ℝ)| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
  nlinarith [sq_nonneg (|(x + 2 * Real.pi * (z : ℝ))| -
    Real.pi * |(z : ℝ)|), sq_abs (x + 2 * Real.pi * (z : ℝ)),
    sq_abs (z : ℝ)]

/-- The translated Gaussian and arbitrary real tilt have a summable Gaussian
bound, uniform over the representative cell. -/
theorem gffFejerCellObservable_le_majorant (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) {root : V} (g : V → ℝ)
    (m : pinnedIntegerField V root) (t : V → ℝ)
    (ht : t ∈ gffFejerCellBox (V := V)) :
    gffFejerCellObservable G β g m t ≤
      gffFejerCellMajorant V β g m.1 := by
  classical
  let φ := gffFejerCellField m t
  let a := gffFejerCellDecay V β
  let B := β * (Fintype.card V : ℝ) * Real.pi ^ 2 /
      (2 * gffPoincareConstant V) + Real.pi * ∑ j, |g j| +
      Real.pi ^ 2 / a * ∑ j, (g j) ^ 2
  have hrate : 0 < gffGaussianRate V β := by
    unfold gffGaussianRate
    have hC : 0 < gffPoincareConstant V := by
      unfold gffPoincareConstant
      exact mul_pos (by exact_mod_cast Fintype.card_pos_iff.mpr hG.nonempty)
        (pow_pos (by norm_num) _)
    exact div_pos hβ (mul_pos (by norm_num) hC)
  have ha : 0 < a := by
    dsimp [a, gffFejerCellDecay]
    positivity
  have hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi := by
    have htroot := (Set.mem_univ_pi.mp ht) root
    have hφroot : φ root = t root := by
      simp [φ, gffFejerCellField, gffFejerCellShift, m.2]
    rw [hφroot]
    exact htroot
  have hcoord (j : V) :
      (Real.pi * |(m.1 j : ℝ)|) ^ 2 ≤ (φ j) ^ 2 := by
    have hj := (Set.mem_univ_pi.mp ht) j
    change t j ∈ Set.Ico (-Real.pi) Real.pi at hj
    have h := pi_mul_abs_int_sq_le_period_shift_sq (m.1 j) (t j) hj.1 hj.2
    simpa [φ, gffFejerCellField, gffFejerCellShift, sq_abs] using h
  have hsqsum : Real.pi ^ 2 * (∑ j, (m.1 j : ℝ) ^ 2) ≤ ∑ j, (φ j) ^ 2 := by
    calc
      Real.pi ^ 2 * (∑ j, (m.1 j : ℝ) ^ 2) =
          ∑ j, Real.pi ^ 2 * (m.1 j : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ j, (φ j) ^ 2 := Finset.sum_le_sum fun j _ => by
        have h := hcoord j
        nlinarith only [h, sq_abs (m.1 j : ℝ)]
  have hpairT : Multigraph.pairing t g ≤ Real.pi * ∑ j, |g j| := by
    unfold Multigraph.pairing
    calc
      (∑ j, t j * g j) ≤ ∑ j, (|t j| * |g j|) :=
        Finset.sum_le_sum fun j _ => by
          calc
            t j * g j ≤ |t j * g j| := le_abs_self _
            _ = |t j| * |g j| := abs_mul _ _
      _ ≤ ∑ j, Real.pi * |g j| := Finset.sum_le_sum fun j _ => by
        have hj := (Set.mem_univ_pi.mp ht) j
        change t j ∈ Set.Ico (-Real.pi) Real.pi at hj
        have habs : |t j| ≤ Real.pi := abs_le.mpr ⟨hj.1, le_of_lt hj.2⟩
        exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = Real.pi * ∑ j, |g j| := (Finset.mul_sum _ _ _).symm
  have hpairInt : Multigraph.pairing (fun j => (m.1 j : ℝ)) g ≤
      ∑ j, |(m.1 j : ℝ)| * |g j| := by
    unfold Multigraph.pairing
    exact Finset.sum_le_sum fun j _ => by
      calc
        (m.1 j : ℝ) * g j ≤ |(m.1 j : ℝ) * g j| := le_abs_self _
        _ = |(m.1 j : ℝ)| * |g j| := abs_mul _ _
  have hpairShift : Multigraph.pairing (gffFejerCellShift m) g ≤
      2 * Real.pi * ∑ j, |(m.1 j : ℝ)| * |g j| := by
    rw [pairing_gffFejerCellShift]
    have hpos : 0 ≤ 2 * Real.pi := by positivity
    exact mul_le_mul_of_nonneg_left hpairInt hpos
  have hpair : Multigraph.pairing φ g ≤
      2 * Real.pi * ∑ j, |(m.1 j : ℝ)| * |g j| +
        Real.pi * ∑ j, |g j| := by
    have hfield : φ = t + gffFejerCellShift m := by
      funext j
      simp [φ, gffFejerCellField]
    rw [hfield]
    have hadd : Multigraph.pairing (t + gffFejerCellShift m) g =
        Multigraph.pairing t g + Multigraph.pairing (gffFejerCellShift m) g := by
      unfold Multigraph.pairing
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hadd]
    have hsum := add_le_add hpairT hpairShift
    linarith only [hsum]
  have hYoung (x y : ℝ) :
      2 * Real.pi * x * y ≤ a * x ^ 2 + Real.pi ^ 2 / a * y ^ 2 := by
    have h := (show x * (2 * Real.pi * y) ≤
        a * x ^ 2 + (2 * Real.pi * y) ^ 2 / (4 * a) by
          field_simp [ne_of_gt ha]
          nlinarith only [sq_nonneg (2 * a * x - 2 * Real.pi * y)])
    field_simp [ne_of_gt ha] at h ⊢
    nlinarith only [h]
  have hYoungSum :
      2 * Real.pi * ∑ j, |(m.1 j : ℝ)| * |g j| ≤
        a * ∑ j, (m.1 j : ℝ) ^ 2 +
          Real.pi ^ 2 / a * ∑ j, (g j) ^ 2 := by
    calc
      2 * Real.pi * ∑ j, |(m.1 j : ℝ)| * |g j| =
          ∑ j, 2 * Real.pi * |(m.1 j : ℝ)| * |g j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ ≤ ∑ j, (a * |(m.1 j : ℝ)| ^ 2 +
          Real.pi ^ 2 / a * |g j| ^ 2) :=
        Finset.sum_le_sum fun j _ => hYoung _ _
      _ = a * ∑ j, (m.1 j : ℝ) ^ 2 +
          Real.pi ^ 2 / a * ∑ j, (g j) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp_rw [sq_abs]
  have hgauss :
      -(β / 2) * G.energy φ ≤
        β * (Fintype.card V : ℝ) * Real.pi ^ 2 /
            (2 * gffPoincareConstant V) -
          gffGaussianRate V β * Real.pi ^ 2 *
            (∑ j, (m.1 j : ℝ) ^ 2) := by
    have hbase := gff_exponent_le_majorant G hG β hβ root φ hroot
    have hmul := mul_le_mul_of_nonpos_left hsqsum
      (neg_nonpos.mpr hrate.le)
    have hneg : -gffGaussianRate V β * ∑ j, (φ j) ^ 2 ≤
        -gffGaussianRate V β *
          (Real.pi ^ 2 * ∑ j, (m.1 j : ℝ) ^ 2) := by
      nlinarith only [hmul]
    nlinarith only [hbase, hneg]
  have hlog :
      Multigraph.pairing φ g - (β / 2) * G.energy φ ≤
        B - a * ∑ j, (m.1 j : ℝ) ^ 2 := by
    have hrate : gffGaussianRate V β * Real.pi ^ 2 = 2 * a := by
      dsimp [a, gffFejerCellDecay]
      ring
    rw [hrate] at hgauss
    calc
      Multigraph.pairing φ g - (β / 2) * G.energy φ ≤
          (2 * Real.pi * ∑ j, |(m.1 j : ℝ)| * |g j| +
            Real.pi * ∑ j, |g j|) +
              (β * (Fintype.card V : ℝ) * Real.pi ^ 2 /
                (2 * gffPoincareConstant V) -
                  2 * a * ∑ j, (m.1 j : ℝ) ^ 2) := by
        linarith only [hpair, hgauss]
      _ ≤ B - a * ∑ j, (m.1 j : ℝ) ^ 2 := by
        dsimp [B]
        linarith only [hYoungSum]
  have hmajor : gffFejerCellMajorant V β g m.1 =
      Real.exp (B - a * ∑ j, (m.1 j : ℝ) ^ 2) := by
    unfold gffFejerCellMajorant gffFejerCellTiltConstant intGaussianPiV
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    have hsum : (∑ j, -(a * (m.1 j : ℝ) ^ 2)) =
        -a * ∑ j, (m.1 j : ℝ) ^ 2 := by
      calc
        (∑ j, -(a * (m.1 j : ℝ) ^ 2)) =
            ∑ j, (-a) * (m.1 j : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = -a * ∑ j, (m.1 j : ℝ) ^ 2 := (Finset.mul_sum _ _ _).symm
    rw [hsum]
    dsimp [B]
    ring
  change Real.exp (Multigraph.pairing φ g - (β / 2) * G.energy φ) ≤ _
  rw [hmajor]
  exact Real.exp_le_exp.mpr hlog

/-- For positive inverse temperature, the cell majorant is summable over
pinned integer fields. -/
theorem summable_gffFejerCellMajorant (V : Type u) [Fintype V]
    [Nonempty V] (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) :
    Summable (fun m : pinnedIntegerField V root =>
      gffFejerCellMajorant V β g m.1) := by
  have hrate : 0 < gffGaussianRate V β := by
    unfold gffGaussianRate
    have hC : 0 < gffPoincareConstant V := by
      unfold gffPoincareConstant
      have hcard : 0 < (Fintype.card V : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
      exact mul_pos hcard (pow_pos (by norm_num) _)
    exact div_pos hβ (mul_pos (by norm_num) hC)
  have ha : 0 < gffFejerCellDecay V β := by
    unfold gffFejerCellDecay
    positivity
  have hbase := summable_intGaussianPiV V ha
  have hpin : Summable (fun m : pinnedIntegerField V root =>
      intGaussianPiV V (gffFejerCellDecay V β) m.1) :=
    hbase.comp_injective Subtype.val_injective
  exact hpin.mul_left (gffFejerCellTiltConstant V β g)

/-- Each fixed translated cell converges to its center value under the product
Fejér kernel. -/
theorem tendsto_gffFejerCellIntegral (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (β : ℝ) {root : V}
    (g : V → ℝ) (m : pinnedIntegerField V root) :
    Tendsto (fun N : ℕ => gffFejerCellIntegral G β g N m) atTop
      (𝓝 (gffFejerCellObservable G β g m 0)) := by
  simpa [gffFejerCellIntegral] using
    (tendsto_integral_gffProductFejerKernel
      (H := gffFejerCellObservable G β g m)
      (continuous_gffFejerCellObservable G β g m))

/-- The normalized integral on every translated cell is bounded by the same
summable Gaussian majorant, for every Fejér degree. -/
theorem abs_gffFejerCellIntegral_le_majorant (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) {root : V} (g : V → ℝ) (N : ℕ)
    (m : pinnedIntegerField V root) :
    |gffFejerCellIntegral G β g N m| ≤
      gffFejerCellMajorant V β g m.1 := by
  classical
  let K (t : V → ℝ) := ∏ j, gffNormalizedFejerKernel N (t j)
  let H := gffFejerCellObservable G β g m
  let Cbox : Set (V → ℝ) := Set.univ.pi (fun _ : V => Set.Icc (-Real.pi) Real.pi)
  have hcompact : IsCompact Cbox := isCompact_univ_pi fun _ => isCompact_Icc
  have hboxsub : gffFejerCellBox (V := V) ⊆ Cbox := by
    intro t ht
    apply Set.mem_univ_pi.mpr
    intro j
    rcases (Set.mem_univ_pi.mp ht) j with ⟨hl, hu⟩
    exact ⟨hl, hu.le⟩
  have hKcont : Continuous K := by
    have hp : Continuous (gffNormalizedFejerKernel N) := by
      unfold gffNormalizedFejerKernel fejerPolynomial fejerCosineCoefficient
      fun_prop
    dsimp [K]
    exact continuous_finsetProd Finset.univ fun j hj => hp.comp (continuous_apply j)
  have hHcont : Continuous H := continuous_gffFejerCellObservable G β g m
  have hfi : IntegrableOn (fun t => H t * K t)
      (gffFejerCellBox (V := V)) := by
    exact ((hHcont.mul hKcont).continuousOn.integrableOn_compact hcompact).mono_set hboxsub
  have hmi : IntegrableOn (fun t =>
      gffFejerCellMajorant V β g m.1 * K t)
      (gffFejerCellBox (V := V)) := by
    exact ((continuous_const.mul hKcont).continuousOn.integrableOn_compact hcompact)
      |>.mono_set hboxsub
  have hKnonneg (t : V → ℝ) : 0 ≤ K t := by
    dsimp [K]
    apply Finset.prod_nonneg
    intro j hj
    unfold gffNormalizedFejerKernel
    apply div_nonneg _ (by positivity)
    by_cases hN : N = 0
    · subst N
      simp [fejerPolynomial]
    · exact fejerPolynomial_nonneg N (Nat.pos_of_ne_zero hN) (t j)
  have hHnonneg (t : V → ℝ) : 0 ≤ H t := by
    exact (Real.exp_pos _).le
  have hpoint (t : V → ℝ) (ht : t ∈ gffFejerCellBox (V := V)) :
      H t * K t ≤ gffFejerCellMajorant V β g m.1 * K t := by
    exact mul_le_mul_of_nonneg_right
      (gffFejerCellObservable_le_majorant G hG β hβ g m t ht) (hKnonneg t)
  have hupper : gffFejerCellIntegral G β g N m ≤
      gffFejerCellMajorant V β g m.1 := by
    unfold gffFejerCellIntegral
    calc
      ∫ t in gffFejerCellBox (V := V), H t * K t ≤
          ∫ t in gffFejerCellBox (V := V),
            gffFejerCellMajorant V β g m.1 * K t :=
          setIntegral_mono_on hfi hmi (measurableSet_gffFejerCellBox (V := V)) hpoint
      _ = gffFejerCellMajorant V β g m.1 := by
        rw [integral_const_mul, integral_gffProductFejerKernel]
        ring
  have hlower : 0 ≤ gffFejerCellIntegral G β g N m := by
    unfold gffFejerCellIntegral
    apply integral_nonneg
    intro t
    exact mul_nonneg (hHnonneg t) (hKnonneg t)
  rw [abs_of_nonneg hlower]
  exact hupper

/-- The cell integrals are summable over the pinned integer lattice. -/
theorem summable_gffFejerCellIntegral (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) (N : ℕ) :
    Summable (fun m : pinnedIntegerField V root =>
      gffFejerCellIntegral G β g N m) := by
  have hmajor := @summable_gffFejerCellMajorant V (inferInstance) hG.nonempty
    β hβ root g
  refine hmajor.of_norm_bounded ?_
  intro m
  rw [Real.norm_eq_abs]
  exact abs_gffFejerCellIntegral_le_majorant G hG β hβ g N m

/-- Dominated convergence passes the product Fejér limit through the pinned
cell sum. -/
theorem tendsto_tsum_gffFejerCellIntegral (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) :
    Tendsto (fun N : ℕ => ∑' m : pinnedIntegerField V root,
      gffFejerCellIntegral G β g N m) atTop
      (𝓝 (∑' m : pinnedIntegerField V root,
        gffFejerCellObservable G β g m 0)) := by
  apply tendsto_tsum_of_dominated_convergence
    (@summable_gffFejerCellMajorant V (inferInstance) hG.nonempty β hβ root g)
  · intro m
    exact tendsto_gffFejerCellIntegral G β g m
  · filter_upwards [] with N m
    rw [Real.norm_eq_abs]
    exact abs_gffFejerCellIntegral_le_majorant G hG β hβ g N m

/-- At the center of a cell the continuum weight is exactly the pinned IGFF
weight at inverse temperature `(2π)^2 β`, with tilt `2π g`. -/
theorem gffFejerCellObservable_center_eq_igffTiltedWeight (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (β : ℝ) {root : V}
    (g : V → ℝ) (m : pinnedIntegerField V root) :
    gffFejerCellObservable G β g m 0 =
      igffTiltedWeight G ((2 * Real.pi) ^ 2 * β)
        (fun j => 2 * Real.pi * g j) m := by
  have hpair : 2 * Real.pi *
      Multigraph.pairing (fun j => (m.1 j : ℝ)) g =
        Multigraph.pairing (fun j => (m.1 j : ℝ))
          (fun j => 2 * Real.pi * g j) := by
    unfold Multigraph.pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [gffFejerCellObservable]
  have hfield : gffFejerCellField m 0 = gffFejerCellShift m := by
    funext j
    simp [gffFejerCellField]
  rw [hfield, pairing_gffFejerCellShift, energy_gffFejerCellShift]
  unfold igffTiltedWeight igffWeight
  rw [hpair, ← Real.exp_add]
  congr 1
  ring

/-- The cell-sum limit is the unnormalized KP integer exponential moment. -/
theorem tendsto_tsum_gffFejerCellIntegral_igff (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) :
    Tendsto (fun N : ℕ => ∑' m : pinnedIntegerField V root,
      gffFejerCellIntegral G β g N m) atTop
      (𝓝 (∑' m : pinnedIntegerField V root,
        igffTiltedWeight G ((2 * Real.pi) ^ 2 * β)
          (fun j => 2 * Real.pi * g j) m)) := by
  have h := tendsto_tsum_gffFejerCellIntegral G hG β hβ root g
  have hsum : (∑' m : pinnedIntegerField V root,
      gffFejerCellObservable G β g m 0) =
        ∑' m : pinnedIntegerField V root,
          igffTiltedWeight G ((2 * Real.pi) ^ 2 * β)
            (fun j => 2 * Real.pi * g j) m :=
    tsum_congr fun m => gffFejerCellObservable_center_eq_igffTiltedWeight G β g m
  rw [← hsum]
  exact h

/-- The contribution of one KP cell is `(2π)^|V|` times its normalized
product-Fejér integral. -/
theorem integral_gffFejerDensity_cell (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (β : ℝ) {root : V}
    (g : V → ℝ) (N : ℕ) (m : pinnedIntegerField V root) :
    (∫ φ in gffFejerCell root m,
      Real.exp (Multigraph.pairing φ g) * gffFejerWeight N φ *
        gffDensity G β root φ) =
      (2 * Real.pi) ^ Fintype.card V * gffFejerCellIntegral G β g N m := by
  rw [integral_gffFejerCell_eq_integral_box_translate]
  unfold gffFejerCellIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards
    [ae_restrict_mem (measurableSet_gffFejerCellBox (V := V))] with t ht
  let φ := gffFejerCellField m t
  have hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi := by
    have hcoord := (Set.mem_univ_pi.mp ht) root
    have hrootEq : φ root = t root := by
      simp [φ, gffFejerCellField, gffFejerCellShift, m.2]
    rw [hrootEq]
    exact hcoord
  have hweight : gffFejerWeight N φ = gffFejerWeight N t := by
    change gffFejerWeight N
      (fun j => t j + 2 * Real.pi * (m.1 j : ℝ)) = gffFejerWeight N t
    exact gffFejerWeight_add_two_pi_int N m.1 t
  change Real.exp (Multigraph.pairing φ g) * gffFejerWeight N φ *
      gffDensity G β root φ =
    (2 * Real.pi) ^ Fintype.card V *
      (gffFejerCellObservable G β g m t *
        ∏ j, gffNormalizedFejerKernel N (t j))
  rw [gffDensity_of_root_mem G β root φ hroot, hweight,
    gffFejerWeight_eq_two_pi_pow_mul_normalized]
  calc
    _ = (2 * Real.pi) ^ Fintype.card V *
        ((Real.exp (Multigraph.pairing φ g) *
          Real.exp (-(β / 2) * G.energy φ)) *
            ∏ j, gffNormalizedFejerKernel N (t j)) := by ring
    _ = (2 * Real.pi) ^ Fintype.card V *
        (Real.exp (Multigraph.pairing φ g + (-(β / 2) * G.energy φ)) *
          ∏ j, gffNormalizedFejerKernel N (t j)) := by
          rw [← Real.exp_add]
    _ = (2 * Real.pi) ^ Fintype.card V *
        (Real.exp (Multigraph.pairing φ g - (β / 2) * G.energy φ) *
          ∏ j, gffNormalizedFejerKernel N (t j)) := by
          congr 2
          congr 1
          ring
    _ = (2 * Real.pi) ^ Fintype.card V *
        (gffFejerCellObservable G β g m t *
          ∏ j, gffNormalizedFejerKernel N (t j)) := by
          simp [gffFejerCellObservable, φ]

/-- Flooring `(x + π)/(2π)` selects the unique period cell containing `x`.
-/
theorem gffFejerCellInterval_floor_mem (x : ℝ) :
    x ∈ gffFejerCellInterval (Int.floor ((x + Real.pi) / (2 * Real.pi))) := by
  rw [gffFejerCellInterval, Set.mem_Ico]
  have hp : 0 < 2 * Real.pi := by positivity
  have hflo := Int.floor_le ((x + Real.pi) / (2 * Real.pi))
  have hfhi := Int.lt_floor_add_one ((x + Real.pi) / (2 * Real.pi))
  have hcancel : 2 * Real.pi * ((x + Real.pi) / (2 * Real.pi)) = x + Real.pi :=
    mul_div_cancel₀ _ hp.ne'
  constructor
  · have h := mul_le_mul_of_nonneg_left hflo hp.le
    rw [hcancel] at h
    linarith only [h]
  · have h := mul_lt_mul_of_pos_left hfhi hp
    rw [hcancel] at h
    linarith only [h]

/-- Distinct half-open period cells are disjoint. -/
theorem gffFejerCellInterval_pairwise_disjoint :
    Pairwise (fun m n : ℤ => Disjoint (gffFejerCellInterval m) (gffFejerCellInterval n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [gffFejerCellInterval, Set.mem_Ico] at hx hy
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hmn' : (m : ℝ) + 1 ≤ n := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    have hp : 0 < 2 * Real.pi := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmn' hp.le
    have hleft : 2 * Real.pi * (m : ℝ) + Real.pi ≤
        2 * Real.pi * (n : ℝ) - Real.pi := by
      ring_nf at hmul ⊢
      linarith only [hmul]
    linarith only [hx, hy, hleft]
  · have hnm' : (n : ℝ) + 1 ≤ m := by
      exact_mod_cast (Int.add_one_le_iff.mpr hgt)
    have hp : 0 < 2 * Real.pi := by positivity
    have hmul := mul_le_mul_of_nonneg_left hnm' hp.le
    have hleft : 2 * Real.pi * (n : ℝ) + Real.pi ≤
        2 * Real.pi * (m : ℝ) - Real.pi := by
      ring_nf at hmul ⊢
      linarith only [hmul]
    linarith only [hx, hy, hleft]

/-- The root window is partitioned by the cells indexed by root-pinned integer fields. -/
theorem iUnion_gffFejerCell_eq_gffRootWindow [Fintype V] [DecidableEq V]
    (root : V) :
    (⋃ m : pinnedIntegerField V root, gffFejerCell root m) = gffRootWindow root := by
  classical
  ext φ
  constructor
  · intro hφ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hφ
    have hroot := (Set.mem_pi.mp hm) root (Set.mem_univ root)
    change φ root ∈ Set.Ico (-Real.pi) Real.pi
    simpa [gffFejerCell, gffFejerCellInterval, m.2] using hroot
  · intro hφ
    change φ root ∈ Set.Ico (-Real.pi) Real.pi at hφ
    let m₀ : V → ℤ := fun j => Int.floor ((φ j + Real.pi) / (2 * Real.pi))
    have hmroot : m₀ root = 0 := by
      dsimp [m₀]
      rw [Int.floor_eq_zero_iff]
      have hpi : 0 < 2 * Real.pi := by positivity
      rcases Set.mem_Ico.mp hφ with ⟨hl, hu⟩
      constructor
      · exact div_nonneg (by linarith only [hl]) hpi.le
      · apply (div_lt_one hpi).2
        linarith only [hu]
    let m : pinnedIntegerField V root := ⟨m₀, hmroot⟩
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    apply Set.mem_pi.mpr
    intro j hj
    exact gffFejerCellInterval_floor_mem (φ j)

/-- The product cells are pairwise disjoint. -/
theorem gffFejerCell_pairwise_disjoint [Fintype V] [DecidableEq V] (root : V) :
    Pairwise (fun m n : pinnedIntegerField V root =>
      Disjoint (gffFejerCell root m) (gffFejerCell root n)) := by
  classical
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro φ hφm hφn
  have hfun : m.1 = n.1 := by
    funext j
    have hmj := (Set.mem_pi.mp hφm) j (Set.mem_univ j)
    have hnj := (Set.mem_pi.mp hφn) j (Set.mem_univ j)
    by_contra hne
    exact Set.disjoint_left.mp (gffFejerCellInterval_pairwise_disjoint hne) hmj hnj
  exact hmn (Subtype.ext hfun)

/-- The pinned root window is measurable in the finite product space. -/
theorem measurableSet_gffRootWindow [Fintype V] [DecidableEq V]
    (root : V) : MeasurableSet (gffRootWindow root) := by
  unfold gffRootWindow
  exact measurableSet_Ico.preimage (measurable_pi_apply root)

/-- An integrable function supported in the root window decomposes as the sum
of its integrals over the disjoint pinned period cells. -/
theorem integral_eq_tsum_gffFejerCells [Fintype V] [DecidableEq V]
    {f : (V → ℝ) → ℝ} (root : V) (hf : Integrable f (volume : Measure (V → ℝ)))
    (hzero : ∀ φ, φ ∉ gffRootWindow root → f φ = 0) :
    ∫ φ, f φ = ∑' m : pinnedIntegerField V root,
      ∫ φ in gffFejerCell root m, f φ := by
  classical
  have hroot : MeasurableSet (gffRootWindow root) := measurableSet_gffRootWindow root
  have hcell : ∀ m : pinnedIntegerField V root,
      MeasurableSet (gffFejerCell root m) := fun m => measurableSet_gffFejerCell root m
  have hdisj := gffFejerCell_pairwise_disjoint (V := V) root
  have hIntOn : IntegrableOn f (gffRootWindow root) (volume : Measure (V → ℝ)) :=
    hf.integrableOn.mono_set (Set.subset_univ (gffRootWindow root))
  have hIntUnion : IntegrableOn f
      (⋃ m : pinnedIntegerField V root, gffFejerCell root m)
      (volume : Measure (V → ℝ)) := by
    rw [iUnion_gffFejerCell_eq_gffRootWindow (V := V) root]
    exact hIntOn
  calc
    ∫ φ, f φ = ∫ φ in gffRootWindow root, f φ := by
      rw [← integral_indicator hroot]
      apply integral_congr_ae
      filter_upwards with φ
      by_cases hφ : φ ∈ gffRootWindow root
      · simp [hφ]
      · simp [hφ, hzero φ hφ]
    _ = ∫ φ in ⋃ m : pinnedIntegerField V root, gffFejerCell root m, f φ := by
      rw [iUnion_gffFejerCell_eq_gffRootWindow]
    _ = ∑' m : pinnedIntegerField V root, ∫ φ in gffFejerCell root m, f φ :=
      integral_iUnion hcell hdisj hIntUnion

/-- The full KP numerator integral is the common cell volume times the
countable sum of normalized cell integrals. -/
theorem gffFejerDensityIntegral_eq_scaled_cellSum (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) (N : ℕ) :
    (∫ φ, Real.exp (Multigraph.pairing φ g) * gffFejerWeight N φ *
      gffDensity G β root φ) =
      (2 * Real.pi) ^ Fintype.card V *
        ∑' m : pinnedIntegerField V root,
          gffFejerCellIntegral G β g N m := by
  let f : (V → ℝ) → ℝ := fun φ =>
    Real.exp (Multigraph.pairing φ g) * gffFejerWeight N φ *
      gffDensity G β root φ
  have hfi : Integrable f (volume : Measure (V → ℝ)) := by
    exact integrable_gffFejerDensityIntegrand G hG β hβ root g N
  have hzero (φ : V → ℝ) (hφ : φ ∉ gffRootWindow root) : f φ = 0 := by
    simp [f, gffDensity_of_root_not_mem G β root φ hφ]
  have hsum := summable_gffFejerCellIntegral G hG β hβ root g N
  calc
    (∫ φ, Real.exp (Multigraph.pairing φ g) * gffFejerWeight N φ *
        gffDensity G β root φ) =
      ∑' m : pinnedIntegerField V root,
        ∫ φ in gffFejerCell root m, f φ := by
          simpa only [f] using integral_eq_tsum_gffFejerCells root hfi hzero
    _ = ∑' m : pinnedIntegerField V root,
        (2 * Real.pi) ^ Fintype.card V *
          gffFejerCellIntegral G β g N m := by
          apply tsum_congr
          intro m
          exact integral_gffFejerDensity_cell G β g N m
    _ = (2 * Real.pi) ^ Fintype.card V *
        ∑' m : pinnedIntegerField V root,
          gffFejerCellIntegral G β g N m :=
      hsum.tsum_mul_left _

/-- The KP finite-volume Fejér ratio converges to the pinned IGFF exponential
moment, with the factor `(2π)^2` in the inverse temperature and `2π` in the
observable as in KP §5.1, p. 4. -/
theorem tendsto_gffFejerRatio_igff (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) :
    Tendsto (fun N : ℕ => gffFejerRatio G hG β hβ root g N) atTop
      (𝓝 (gffFejerIGFFTarget G hG β hβ root g)) := by
  let β' := (2 * Real.pi) ^ 2 * β
  let hβ' : 0 < β' := by
    dsimp [β']
    exact mul_pos (sq_pos_of_ne_zero (by positivity)) hβ
  let Sg : ℕ → ℝ := fun N => ∑' m : pinnedIntegerField V root,
    gffFejerCellIntegral G β g N m
  let S0 : ℕ → ℝ := fun N => ∑' m : pinnedIntegerField V root,
    gffFejerCellIntegral G β (fun _ => 0) N m
  let Tg : ℝ := ∑' m : pinnedIntegerField V root,
    igffTiltedWeight G β' (fun j => 2 * Real.pi * g j) m
  have hnum : Tendsto Sg atTop (𝓝 Tg) := by
    simpa [Sg, Tg, β'] using
      tendsto_tsum_gffFejerCellIntegral_igff G hG β hβ root g
  have hden : Tendsto S0 atTop (𝓝 (igffPartitionFunction G β' root)) := by
    have h := tendsto_tsum_gffFejerCellIntegral_igff
      G hG β hβ root (fun _ => 0)
    simpa [S0, β', igffTiltedWeight, Multigraph.pairing,
      igffPartitionFunction] using h
  have hpart : 0 < igffPartitionFunction G β' root :=
    igffPartitionFunction_pos G hG β' hβ' root
  have hquot : Tendsto (fun N => Sg N / S0 N) atTop
      (𝓝 (Tg / igffPartitionFunction G β' root)) :=
    hnum.div hden (ne_of_gt hpart)
  have htarget : Tg / igffPartitionFunction G β' root =
      gffFejerIGFFTarget G hG β hβ root g := by
    dsimp [Tg, β', gffFejerIGFFTarget]
    rw [igffExpectation_eq_normalized_tsum]
    rfl
  have hquotTarget : Tendsto (fun N => Sg N / S0 N) atTop
      (𝓝 (gffFejerIGFFTarget G hG β hβ root g)) := by
    rw [← htarget]
    exact hquot
  have hscale : 0 < (2 * Real.pi) ^ Fintype.card V :=
    pow_pos (by positivity) _
  have hrawg (N : ℕ) :
      (∫ φ, Real.exp (Multigraph.pairing φ g) * gffFejerWeight N φ *
        gffDensity G β root φ) = (2 * Real.pi) ^ Fintype.card V * Sg N := by
    simpa [Sg] using gffFejerDensityIntegral_eq_scaled_cellSum
      G hG β hβ root g N
  have hraw0 (N : ℕ) :
      (∫ φ, gffFejerWeight N φ * gffDensity G β root φ) =
        (2 * Real.pi) ^ Fintype.card V * S0 N := by
    simpa [S0, Multigraph.pairing] using
      gffFejerDensityIntegral_eq_scaled_cellSum
        G hG β hβ root (fun _ => 0) N
  have hraw0pos (N : ℕ) (hN : 0 < N) :
      0 < ∫ φ, gffFejerWeight N φ * gffDensity G β root φ :=
    gffFejerDensityIntegral_pos G hG β hβ root N hN
  have hS0ne (N : ℕ) (hN : 0 < N) : S0 N ≠ 0 := by
    intro hzero
    have hzero' : (∫ φ, gffFejerWeight N φ * gffDensity G β root φ) = 0 := by
      rw [hraw0, hzero]
      ring
    exact (ne_of_gt (hraw0pos N hN)) hzero'
  have hratio (N : ℕ) (hN : 0 < N) :
      gffFejerRatio G hG β hβ root g N = Sg N / S0 N := by
    unfold gffFejerRatio
    rw [gffFejerAverage_eq_densityIntegral_div G hG β hβ root g N,
      gffFejerAverage_eq_densityIntegral_div G hG β hβ root (fun _ => 0) N]
    rw [hrawg]
    simp only [Multigraph.pairing, Finset.sum_const_zero, mul_zero,
      Real.exp_zero, one_mul]
    rw [hraw0]
    field_simp [ne_of_gt (gffPartitionFunction_pos G hG β hβ root),
      hscale.ne', hS0ne N hN]
  apply Tendsto.congr' ?_ hquotTarget
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hratio N hN).symm

/--
The same limiting exponential moment is the integral of the displayed
observable against the integerGFFLaw carrier.
-/
theorem gffFejerSourceTarget_eq_ofReal_igff (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) :
    gffFejerSourceTarget G hG β hβ root g =
      ENNReal.ofReal (gffFejerIGFFTarget G hG β hβ root g) := by
  have hβ' : 0 < (2 * Real.pi) ^ 2 * β :=
    mul_pos (sq_pos_of_ne_zero (by positivity)) hβ
  have hsum : Summable (fun m : pinnedIntegerField V root =>
      igffTiltedWeight G ((2 * Real.pi) ^ 2 * β)
        (fun j => 2 * Real.pi * g j) m) :=
    summable_igffTiltedWeight G hG _ hβ' root (fun j => 2 * Real.pi * g j)
  have hpairScale (m : pinnedIntegerField V root) :
      Multigraph.pairing (fun j => (m.1 j : ℝ))
          (fun j => 2 * Real.pi * g j) =
        2 * Real.pi * Multigraph.pairing (fun j => (m.1 j : ℝ)) g := by
    unfold Multigraph.pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsumF : Summable (fun m : pinnedIntegerField V root =>
      Real.exp (2 * Real.pi *
        Multigraph.pairing (fun j => (m.1 j : ℝ)) g) * igffWeight G
          ((2 * Real.pi) ^ 2 * β) m) := by
    convert hsum using 1
    funext m
    rw [igffTiltedWeight, hpairScale]
  have heq := integerGFFLaw_lintegral_ofReal_eq_igffExpectation
    G hG ((2 * Real.pi) ^ 2 * β) hβ' root
    (fun m => Real.exp (2 * Real.pi *
      Multigraph.pairing (fun j => (m j : ℝ)) g))
    (fun _ => (Real.exp_pos _).le)
    (by
      simpa only [Multigraph.pairing] using hsumF)
  rw [gffFejerSourceTarget_eq_kp, gffFejerIGFFTarget_eq_kp]
  exact heq

end FroehlichSpencer.BKT

end
