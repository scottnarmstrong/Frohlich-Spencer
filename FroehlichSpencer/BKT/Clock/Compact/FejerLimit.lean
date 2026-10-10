/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Law
public import FroehlichSpencer.BKT.Gaussian.FejerCellLimit
public import FroehlichSpencer.BKT.Ginibre.SiteMeasure
import Mathlib.Tactic

/-!
# The Fejér limit of the compact clock law

The clock site measure (point masses at the `n` clock angles) is the limit of Fejér weights on the
compact box. Shifting the Fejér weights by `δ_n` (`π` for even `n`, `0` for odd `n`) puts their
peaks at the centers `c_a = π(1 − n) + 2πa` of an exact decomposition of `(−πn, πn]` into `n`
cells. The cell approximate identity (`tendsto_integral_gffProductFejerKernel`) then
applies cell by cell. No periodic shift of the box is needed.

* `pi_sum_measure`, `pi_dirac`, `integral_siteProduct_clockMeasure`: integrals against the clock
  site product are finite sums.
* `compactAngleBaseMeasure_eq_sum`, `integral_compactAngleBase_eq_sum`: the box is the sum of its
  translated cells.
* **`tendsto_integral_compactAngleBase_fejer`**: `∫ G ∏_j F_M(φ_j − δ_n) dφ → (2π)^d ∑_k G(c_k)`.
* **`tendsto_integral_clockLaw_fejer`**: the same for the clock law on `V`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open MeasureTheory Filter Topology Set
open FroehlichSpencer.BKT.Clock.Periodic

/-! ### Product measures of finite sums -/

section PiSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isFiniteMeasure_finset_sum {A : Type*} (s : Finset A) (μ : A → Measure ℝ)
    [∀ a, IsFiniteMeasure (μ a)] : IsFiniteMeasure (∑ a ∈ s, μ a) := by
  refine ⟨?_⟩
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  exact ENNReal.sum_lt_top.2 fun a _ => measure_lt_top (μ a) _

/-- The product of finite sums of finite measures is the sum, over choices, of the products. -/
theorem pi_sum_measure {A : Type*} [Fintype A] (μ : A → Measure ℝ) [∀ a, IsFiniteMeasure (μ a)] :
    Measure.pi (fun _ : ι => ∑ a, μ a) = ∑ k : ι → A, Measure.pi fun i => μ (k i) := by
  have : IsFiniteMeasure (∑ a, μ a) := isFiniteMeasure_finset_sum _ μ
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.pi_pi]
  rw [Measure.coe_finsetSum]
  simp only [Finset.sum_apply]
  rw [Finset.prod_univ_sum]
  simp

omit [DecidableEq ι] in
/-- A product of Dirac masses is the Dirac mass of the product point. -/
theorem pi_dirac (x : ι → ℝ) : Measure.pi (fun i => Measure.dirac (x i)) = Measure.dirac x := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  by_cases h : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem h]
    rw [Finset.prod_eq_one fun i _ => Set.indicator_of_mem (h i (Set.mem_univ i)) _]
    rfl
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- **Integrals against the clock site product** are finite sums over the clock configurations. -/
theorem integral_siteProduct_clockMeasure (N : ℕ) (f : (ι → ℝ) → ℝ) :
    ∫ θ, f θ ∂Ginibre.siteProduct (Ginibre.clockMeasure N) ι =
      ∑ k : ι → Fin N, f fun i => 2 * Real.pi * (k i : ℝ) / N := by
  have hsp : Ginibre.siteProduct (Ginibre.clockMeasure N) ι =
      ∑ k : ι → Fin N, Measure.dirac (fun i => 2 * Real.pi * (k i : ℝ) / N) := by
    unfold Ginibre.siteProduct Ginibre.clockMeasure
    rw [pi_sum_measure]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact pi_dirac _
  rw [hsp, integral_finsetSum_measure fun k _ => integrable_dirac enorm_lt_top]
  exact Finset.sum_congr rfl fun k _ => integral_dirac _ _

end PiSum

/-! ### The compact box as a union of Fejér cells -/

section Cells

/-- The center `π(1 − n) + 2πa` of the `a`-th cell of the compact box `(−πn, πn]`. -/
def cellCenter (n a : ℕ) : ℝ := Real.pi * (1 - n) + 2 * Real.pi * a

/-- The offset of the clock Fejér weights: `π` for even `n`, `0` for odd `n`, so that every cell
center is a Fejér peak. -/
def clockOffset (n : ℕ) : ℝ := if Even n then Real.pi else 0

theorem exists_cellCenter_sub_clockOffset (n a : ℕ) :
    ∃ m : ℤ, cellCenter n a - clockOffset n = 2 * Real.pi * m := by
  unfold cellCenter clockOffset
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · have he : Even n := ⟨r, hr⟩
    refine ⟨(a : ℤ) - r, ?_⟩
    simp only [he, ↓reduceIte]
    rw [hr]
    push_cast
    ring
  · have hne : ¬Even n := Nat.not_even_iff_odd.2 ⟨r, hr⟩
    refine ⟨(a : ℤ) - r, ?_⟩
    simp only [hne, ↓reduceIte]
    rw [hr]
    push_cast
    ring

/-- The Fejér polynomial is `2π`-periodic. -/
theorem fejerPolynomial_add_two_pi_mul (M : ℕ) (x : ℝ) (m : ℤ) :
    fejerPolynomial M (x + 2 * Real.pi * m) = fejerPolynomial M x := by
  unfold fejerPolynomial
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have : (((r + 1 : ℕ) : ℝ)) * (x + 2 * Real.pi * m) =
      (((r + 1 : ℕ) : ℝ)) * x + (((r + 1 : ℕ) : ℤ) * m : ℤ) * (2 * Real.pi) := by
    push_cast; ring
  rw [this, Real.cos_add_int_mul_two_pi]

theorem abs_fejerPolynomial_le (M : ℕ) (x : ℝ) : |fejerPolynomial M x| ≤ 1 + 2 * M := by
  unfold fejerPolynomial
  refine (abs_add_le _ _).trans ?_
  rw [abs_one]
  have h : |∑ r ∈ Finset.range M, 2 * fejerCosineCoefficient M (r + 1) *
      Real.cos (((r + 1 : ℕ) : ℝ) * x)| ≤ ∑ _r ∈ Finset.range M, (2 : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    have hM : 0 < M := by
      have := Finset.mem_range.1 hr
      omega
    have hc := fejerCosineCoefficient_mem_Icc M (r + 1) hM (Finset.mem_range.1 hr)
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hc.1]
    have := Real.abs_cos_le_one (((r + 1 : ℕ) : ℝ) * x)
    calc 2 * fejerCosineCoefficient M (r + 1) * |Real.cos (((r + 1 : ℕ) : ℝ) * x)|
        ≤ 2 * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hc.2 (by norm_num)) this
          (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith

theorem restrict_Ioc_eq_sum_cells (s P : ℝ) (hP : 0 ≤ P) (n : ℕ) :
    volume.restrict (Ioc s (s + n * P)) =
      ∑ a : Fin n, volume.restrict (Ioc (s + a * P) (s + (a + 1) * P)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    have h1 : s ≤ s + n * P := by have : (0 : ℝ) ≤ n * P := by positivity
                                  linarith
    have h2 : s + n * P ≤ s + ((n : ℝ) + 1) * P := by nlinarith
    rw [← Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc h1 h2]
    push_cast
    ring_nf

theorem restrict_Ioc_cell (c : ℝ) :
    volume.restrict (Ioc (c - Real.pi) (c + Real.pi)) =
      (volume.restrict (Ioc (-Real.pi) Real.pi)).map (fun t => c + t) := by
  have hm : Measurable fun t : ℝ => c + t := measurable_const_add c
  have hv : (volume : Measure ℝ).map (fun t => c + t) = volume :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self c
  have hpre :
      (fun t : ℝ => c + t) ⁻¹' Ioc (c - Real.pi) (c + Real.pi) = Ioc (-Real.pi) Real.pi := by
    ext t
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [← hpre, ← Measure.restrict_map hm measurableSet_Ioc, hv]

end Cells

/-! ### The Fejér limit on the compact box -/

section Limit

variable {d : ℕ}

/-- The compact box measure is the sum over cell choices of translated cell products. -/
theorem compactAngleBaseMeasure_eq_sum {n : ℕ} :
    compactAngleBaseMeasure (d := d) (2 * Real.pi * n) =
      ∑ k : Fin d → Fin n,
        (Measure.pi fun _ : Fin d => volume.restrict (Ioc (-Real.pi) Real.pi)).map
        (fun t j => cellCenter n (k j) + t j) := by
  have h1 : volume.restrict (Ioc (-(2 * Real.pi * n) / 2) ((2 * Real.pi * n) / 2)) =
      ∑ a : Fin n, volume.restrict (Ioc (cellCenter n a - Real.pi) (cellCenter n a + Real.pi)) := by
    have h := restrict_Ioc_eq_sum_cells (-(2 * Real.pi * n) / 2) (2 * Real.pi)
      (by positivity) n
    have he : -(2 * Real.pi * n) / 2 + n * (2 * Real.pi) = (2 * Real.pi * n) / 2 := by ring
    rw [he] at h
    rw [h]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold cellCenter
    congr 2 <;> ring
  unfold compactAngleBaseMeasure
  rw [h1, pi_sum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [restrict_Ioc_cell]
  rw [Measure.pi_map_pi (fun _ => (measurable_const_add _).aemeasurable)]

theorem integral_compactAngleBase_eq_sum {n : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Continuous f)
    {C : ℝ} (hfb : ∀ φ, |f φ| ≤ C) :
    ∫ φ, f φ ∂compactAngleBaseMeasure (2 * Real.pi * n) =
      ∑ k : Fin d → Fin n, ∫ t in gffFejerCellBox (V := Fin d),
        f fun j => cellCenter n (k j) + t j := by
  set μ₀ : Measure (Fin d → ℝ) :=
    Measure.pi fun _ : Fin d => volume.restrict (Ioc (-Real.pi) Real.pi) with hμ₀
  have hfin : IsFiniteMeasure μ₀ := by rw [hμ₀]; infer_instance
  have hT : ∀ k : Fin d → Fin n, Measurable fun (t : Fin d → ℝ) (j : Fin d) =>
      cellCenter n (k j) + t j := fun k => by fun_prop
  have hint : ∀ k : Fin d → Fin n,
      Integrable f (μ₀.map fun t j => cellCenter n (k j) + t j) := by
    intro k
    refine (integrable_map_measure hf.aestronglyMeasurable (hT k).aemeasurable).2 ?_
    exact Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable C
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hfb _)
  rw [compactAngleBaseMeasure_eq_sum, integral_finsetSum_measure fun k _ => hint k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_map (hT k).aemeasurable hf.aestronglyMeasurable]
  have hμ₀' : μ₀ = volume.restrict (Set.univ.pi fun _ : Fin d => Ioc (-Real.pi) Real.pi) := by
    rw [hμ₀, volume_pi, Measure.restrict_pi_pi]
  rw [hμ₀']
  refine setIntegral_congr_set ?_
  have h1 := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := fun _ => -Real.pi) (g := fun _ => Real.pi)
  have h2 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := fun _ => -Real.pi) (g := fun _ => Real.pi)
  rw [← volume_pi] at h1 h2
  exact h1.trans h2.symm

/-- **The Fejér limit on the compact clock box**: the shifted product Fejér weights concentrate on
the `n^d` cell centers, `∫ G ∏_j F_M(φ_j − δ_n) dφ → (2π)^d ∑_k G(c_k)` for continuous bounded
`G`. -/
theorem tendsto_integral_compactAngleBase_fejer {n : ℕ} (G : (Fin d → ℝ) → ℝ) (hG : Continuous G)
    {C : ℝ} (hGb : ∀ φ, |G φ| ≤ C) :
    Tendsto (fun M : ℕ => ∫ φ, G φ * ∏ j, fejerPolynomial M (φ j - clockOffset n)
        ∂compactAngleBaseMeasure (2 * Real.pi * n)) atTop
      (𝓝 ((2 * Real.pi) ^ d * ∑ k : Fin d → Fin n, G fun j => cellCenter n (k j))) := by
  have hcont : ∀ M : ℕ, Continuous fun φ : Fin d → ℝ =>
      G φ * ∏ j, fejerPolynomial M (φ j - clockOffset n) := by
    intro M
    refine hG.mul (continuous_finsetProd _ fun j _ => ?_)
    unfold fejerPolynomial fejerCosineCoefficient
    fun_prop
  have hbd : ∀ (M : ℕ) (φ : Fin d → ℝ),
      |G φ * ∏ j, fejerPolynomial M (φ j - clockOffset n)| ≤ C * (1 + 2 * M) ^ d := by
    intro M φ
    rw [abs_mul, Finset.abs_prod]
    have hC : 0 ≤ C := (abs_nonneg _).trans (hGb φ)
    refine mul_le_mul (hGb φ) ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hC
    calc ∏ j, |fejerPolynomial M (φ j - clockOffset n)| ≤ ∏ _j : Fin d, (1 + 2 * (M : ℝ)) :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => abs_fejerPolynomial_le M _
      _ = (1 + 2 * M) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hper : ∀ (M : ℕ) (a : ℕ) (t : ℝ),
      fejerPolynomial M (cellCenter n a + t - clockOffset n) =
        2 * Real.pi * gffNormalizedFejerKernel M t := by
    intro M a t
    obtain ⟨m, hm⟩ := exists_cellCenter_sub_clockOffset n a
    have : cellCenter n a + t - clockOffset n = t + 2 * Real.pi * m := by linarith
    rw [this, fejerPolynomial_add_two_pi_mul, gffNormalizedFejerKernel]
    field_simp
  have hdec : ∀ M : ℕ, ∫ φ, G φ * ∏ j, fejerPolynomial M (φ j - clockOffset n)
      ∂compactAngleBaseMeasure (2 * Real.pi * n) =
      ∑ k : Fin d → Fin n, (2 * Real.pi) ^ d * ∫ t in gffFejerCellBox (V := Fin d),
        (fun t => G fun j => cellCenter n (k j) + t j) t *
          ∏ j, gffNormalizedFejerKernel M (t j) := by
    intro M
    rw [integral_compactAngleBase_eq_sum _ (hcont M) (hbd M)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun t _ => ?_
    simp only
    simp_rw [hper]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  simp_rw [hdec]
  rw [Finset.mul_sum]
  refine tendsto_finsetSum _ fun k _ => ?_
  refine Tendsto.const_mul _ ?_
  have h := tendsto_integral_gffProductFejerKernel (V := Fin d)
    (fun t => G fun j => cellCenter n (k j) + t j) (hG.comp (by fun_prop))
  simpa using h

end Limit

/-! ### The Fejér limit of the clock law -/

section ClockLaw

variable {V : Type} [Fintype V] {E : Type} [Fintype E]

/-- The unnormalized clock edge density on fields indexed by `V`. -/
def clockDensity (β n : ℝ) (G : Multigraph V E) (φ : V → ℝ) : ℝ :=
  ∏ e, Real.exp (β * Real.cos (G.grad φ e / n))

omit [Fintype V] in
theorem clockDensity_pos (β n : ℝ) (G : Multigraph V E) (φ : V → ℝ) : 0 < clockDensity β n G φ :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

omit [Fintype V] in
theorem continuous_clockDensity (β n : ℝ) (G : Multigraph V E) :
    Continuous (clockDensity β n G) := by
  unfold clockDensity Multigraph.grad
  fun_prop

omit [Fintype V] in
theorem clockDensity_le (β n : ℝ) (hβ : 0 ≤ β) (G : Multigraph V E) (φ : V → ℝ) :
    clockDensity β n G φ ≤ Real.exp β ^ Fintype.card E := by
  unfold clockDensity
  calc ∏ e, Real.exp (β * Real.cos (G.grad φ e / n)) ≤ ∏ _e : E, Real.exp β :=
        Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun e _ => Real.exp_le_exp.2 (by
          have := Real.cos_le_one (G.grad φ e / n)
          nlinarith)
    _ = Real.exp β ^ Fintype.card E := by rw [Finset.prod_const, Finset.card_univ]

theorem clockBoxDensity_eq (β n : ℝ) (G : Multigraph V E) (φ : Fin (Fintype.card V) → ℝ) :
    clockBoxDensity β n (relabelGraph G (siteEquiv V)) φ = clockDensity β n G (pullField V φ) := by
  unfold clockBoxDensity clockDensity
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [clockEdgeWeight_ofReal]
  rfl

theorem integral_clockLaw_eq_base {β n : ℝ} (hβ : 0 ≤ β) (G : Multigraph V E)
    (f : (V → ℝ) → ℝ) :
    ∫ φ, f φ ∂clockLaw β n G =
      ((clockBoxMass β n (relabelGraph G (siteEquiv V)))⁻¹).toReal *
        ∫ φ, clockDensity β n G (pullField V φ) * f (pullField V φ) ∂clockAngleBaseMeasure n := by
  rw [integral_clockLaw]
  set G' := relabelGraph G (siteEquiv V)
  set ρ := clockBoxDensity β n G'
  have hρmeas : Measurable ρ := measurable_clockBoxDensity β n G'
  have hρnonneg : ∀ φ, 0 ≤ ρ φ := fun φ =>
    (le_of_lt (pow_pos (Real.exp_pos _) _)).trans (clockBoxDensity_bounds G' hβ φ).1
  have hbase :
      ∫ φ, f (pullField V φ) ∂(clockAngleBaseMeasure n).withDensity
          (fun φ => ENNReal.ofReal (ρ φ)) =
        ∫ φ, ρ φ * f (pullField V φ) ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, (ENNReal.ofReal (ρ φ)).toReal • f (pullField V φ) ∂clockAngleBaseMeasure n :=
        integral_withDensity_eq_integral_toReal_smul
          (ENNReal.measurable_ofReal.comp hρmeas)
          (Filter.Eventually.of_forall fun φ => ENNReal.ofReal_lt_top) _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with φ
        simp [ENNReal.toReal_ofReal (hρnonneg φ)]
  change ∫ φ, f (pullField V φ) ∂((clockBoxMass β n G')⁻¹ •
    (clockAngleBaseMeasure n).withDensity fun φ => ENNReal.ofReal (ρ φ)) = _
  rw [integral_smul_measure, hbase, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [ρ, G', clockBoxDensity_eq]

/-- The Fejér-weighted clock-law integral converges to the cell-center sum. -/
theorem tendsto_integral_clockLaw_fejer [DecidableEq V] {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (G : Multigraph V E)
    (g : (V → ℝ) → ℝ) (hg : Continuous g) {C : ℝ} (hgb : ∀ φ, |g φ| ≤ C) :
    Tendsto (fun M : ℕ => ∫ φ, g φ * ∏ v, fejerPolynomial M (φ v - clockOffset n)
        ∂clockLaw β n G) atTop
      (𝓝 (((clockBoxMass β n (relabelGraph G (siteEquiv V)))⁻¹).toReal *
        ((2 * Real.pi) ^ Fintype.card V * ∑ k : V → Fin n,
          clockDensity β n G (fun v => cellCenter n (k v)) *
            g (fun v => cellCenter n (k v))))) := by
  set e := siteEquiv V
  set G₁ : (Fin (Fintype.card V) → ℝ) → ℝ := fun φ =>
    clockDensity β n G (pullField V φ) * g (pullField V φ) with hG₁
  have hpull : Continuous (pullField V) := by
    unfold pullField; fun_prop
  have hG₁c : Continuous G₁ :=
    ((continuous_clockDensity β n G).comp hpull).mul (hg.comp hpull)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgb 0)
  have hG₁b : ∀ φ, |G₁ φ| ≤ Real.exp β ^ Fintype.card E * C := by
    intro φ
    simp only [hG₁]
    rw [abs_mul, abs_of_pos (clockDensity_pos β n G _)]
    exact mul_le_mul (clockDensity_le β n hβ G _) (hgb _) (abs_nonneg _) (by positivity)
  have hlim := tendsto_integral_compactAngleBase_fejer (n := n) G₁ hG₁c hG₁b
  have heq : ∀ M : ℕ, ∫ φ, g φ * ∏ v, fejerPolynomial M (φ v - clockOffset n) ∂clockLaw β n G =
      ((clockBoxMass β n (relabelGraph G e))⁻¹).toReal *
        ∫ φ, G₁ φ * ∏ j, fejerPolynomial M (φ j - clockOffset n)
          ∂compactAngleBaseMeasure (2 * Real.pi * n) := by
    intro M
    rw [integral_clockLaw_eq_base hβ]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only [hG₁, pullField]
    rw [← e.prod_comp fun j => fejerPolynomial M (φ j - clockOffset n)]
    ring
  simp_rw [heq]
  convert hlim.const_mul ((clockBoxMass β n (relabelGraph G e))⁻¹).toReal using 3
  · symm
    congr 1
    refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl (Fin n)))
      (fun k : Fin (Fintype.card V) → Fin n => G₁ fun j => cellCenter n (k j))
      (fun k : V → Fin n => clockDensity β n G (fun v => cellCenter n (k v)) *
        g (fun v => cellCenter n (k v))) fun k => ?_
    simp only [hG₁, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply]
    congr 2

end ClockLaw

end FroehlichSpencer.BKT.Clock.Compact

end
