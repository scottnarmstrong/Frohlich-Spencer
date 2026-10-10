/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.FejerCellLimit
import Mathlib.Tactic

/-!
# The Fejér cell limit for a cosine observable

`Gaussian/FejerCellLimit` passes from the GFF with Fejér weights `∏_j F_N(φ_j)` to the
integer-valued GFF, for exponential observables (`tendsto_gffFejerRatio_igff`). This file does the
same for the bounded observable `cos(ξ⟨φ, f⟩)`: as `N → ∞`,
`⟨cos(ξ⟨φ, f⟩)⟩_{GFF(β), Fejér N} → ⟨cos(2πξ⟨m, f⟩)⟩_{IGFF((2π)² β)}`.
The `ξ = 0` majorant dominates the cell terms, so dominated convergence for the cell sum applies
as in the exponential case.

* `gffFejerCosCellObservable`, `gffFejerCosCellIntegral`: the cosine cell observable, and its
  integral against the Fejér kernel on one cell.
* `gffFejerCosDensityIntegral_eq_scaled_cellSum`: the cell decomposition of the numerator.
* `abs_gffFejerCosCellIntegral_le_majorant`, `tendsto_tsum_gffFejerCosCellIntegral`: the
  domination, and the limit of the cell sum.
* **`tendsto_gffFejerCosRatio_igff`**: the limit of the Fejér ratio.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open MeasureTheory Filter Topology Multigraph

variable {V : Type*} {E : Type*}

/-! ### The Fejér cell limit for a cosine observable -/

section FejerCos

/-- The cosine cell observable `cos(ξ⟨2πm + t, f⟩) e^{-β Q(2πm + t)/2}` on one translated cell. -/
noncomputable def gffFejerCosCellObservable (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (β ξ : ℝ) {root : V} (f : V → ℝ) (m : pinnedIntegerField V root)
    (t : V → ℝ) : ℝ :=
  Real.cos (ξ * pairing (gffFejerCellField m t) f) * gffFejerCellObservable G β (fun _ => 0) m t

/-- The normalized product-Fejér integral of the cosine cell observable. -/
noncomputable def gffFejerCosCellIntegral (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (β ξ : ℝ) {root : V} (f : V → ℝ) (N : ℕ) (m : pinnedIntegerField V root) :
    ℝ :=
  ∫ t in gffFejerCellBox (V := V),
    gffFejerCosCellObservable G β ξ f m t * ∏ j, gffNormalizedFejerKernel N (t j)

theorem continuous_gffFejerCosCellObservable (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (β ξ : ℝ) {root : V} (f : V → ℝ) (m : pinnedIntegerField V root) :
    Continuous (gffFejerCosCellObservable G β ξ f m) := by
  have hp : Continuous (fun t : V → ℝ => pairing (gffFejerCellField m t) f) := by
    unfold pairing gffFejerCellField
    fun_prop
  exact (Real.continuous_cos.comp (continuous_const.mul hp)).mul
    (continuous_gffFejerCellObservable G β (fun _ => 0) m)

/-- The density integral of the cosine observable on one period cell. -/
theorem integral_gffFejerCosDensity_cell (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (β ξ : ℝ) {root : V} (f : V → ℝ) (N : ℕ)
    (m : pinnedIntegerField V root) :
    (∫ φ in gffFejerCell root m,
      Real.cos (ξ * pairing φ f) * gffFejerWeight N φ * gffDensity G β root φ) =
      (2 * Real.pi) ^ Fintype.card V * gffFejerCosCellIntegral G β ξ f N m := by
  rw [integral_gffFejerCell_eq_integral_box_translate]
  unfold gffFejerCosCellIntegral
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
  change Real.cos (ξ * pairing φ f) * gffFejerWeight N φ * gffDensity G β root φ =
    (2 * Real.pi) ^ Fintype.card V *
      (gffFejerCosCellObservable G β ξ f m t * ∏ j, gffNormalizedFejerKernel N (t j))
  rw [gffDensity_of_root_mem G β root φ hroot, hweight,
    gffFejerWeight_eq_two_pi_pow_mul_normalized]
  unfold gffFejerCosCellObservable gffFejerCellObservable
  simp only [pairing, mul_zero, Finset.sum_const_zero, zero_sub]
  dsimp only [φ]
  ring_nf

/-- The cosine density integral is the common cell volume times the sum of the normalized cosine
cell integrals. -/
theorem gffFejerCosDensityIntegral_eq_scaled_cellSum (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) (ξ : ℝ)
    (f : V → ℝ) (N : ℕ)
    (hsum : Summable fun m : pinnedIntegerField V root => gffFejerCosCellIntegral G β ξ f N m) :
    (∫ φ, Real.cos (ξ * pairing φ f) * gffFejerWeight N φ * gffDensity G β root φ) =
      (2 * Real.pi) ^ Fintype.card V *
        ∑' m : pinnedIntegerField V root, gffFejerCosCellIntegral G β ξ f N m := by
  let F : (V → ℝ) → ℝ := fun φ =>
    Real.cos (ξ * pairing φ f) * gffFejerWeight N φ * gffDensity G β root φ
  have h0 : Integrable (fun φ : V → ℝ => gffFejerWeight N φ * gffDensity G β root φ)
      (volume : Measure (V → ℝ)) := by
    simpa [pairing] using
      (integrable_gffFejerDensityIntegrand G hG β hβ root (fun _ => 0) N)
  have hfi : Integrable F (volume : Measure (V → ℝ)) := by
    have hmeas : Measurable fun φ : V → ℝ => Real.cos (ξ * pairing φ f) := by
      unfold pairing
      fun_prop
    refine (h0.bdd_mul (c := 1) hmeas.aestronglyMeasurable
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)).congr
      (ae_of_all _ fun φ => ?_)
    simp only [F]
    ring
  have hzero (φ : V → ℝ) (hφ : φ ∉ gffRootWindow root) : F φ = 0 := by
    simp [F, gffDensity_of_root_not_mem G β root φ hφ]
  calc (∫ φ, Real.cos (ξ * pairing φ f) * gffFejerWeight N φ * gffDensity G β root φ)
      = ∑' m : pinnedIntegerField V root, ∫ φ in gffFejerCell root m, F φ :=
        integral_eq_tsum_gffFejerCells root hfi hzero
    _ = ∑' m : pinnedIntegerField V root,
        (2 * Real.pi) ^ Fintype.card V * gffFejerCosCellIntegral G β ξ f N m :=
        tsum_congr fun m => integral_gffFejerCosDensity_cell G β ξ f N m
    _ = _ := hsum.tsum_mul_left _

/-- The cosine cell integrals are dominated by the zero-tilt majorant. -/
theorem abs_gffFejerCosCellIntegral_le_majorant (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β) {root : V} (ξ : ℝ) (f : V → ℝ)
    (N : ℕ) (m : pinnedIntegerField V root) :
    |gffFejerCosCellIntegral G β ξ f N m| ≤ gffFejerCellMajorant V β (fun _ => 0) m.1 := by
  classical
  let K (t : V → ℝ) := ∏ j, gffNormalizedFejerKernel N (t j)
  let H := gffFejerCellObservable G β (fun _ => 0) m
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
  have hHcont : Continuous H := continuous_gffFejerCellObservable G β (fun _ => 0) m
  have hcos := continuous_gffFejerCosCellObservable G β ξ f m
  have hfi : IntegrableOn (fun t => gffFejerCosCellObservable G β ξ f m t * K t)
      (gffFejerCellBox (V := V)) :=
    ((hcos.mul hKcont).continuousOn.integrableOn_compact hcompact).mono_set hboxsub
  have hHi : IntegrableOn (fun t => H t * K t) (gffFejerCellBox (V := V)) :=
    ((hHcont.mul hKcont).continuousOn.integrableOn_compact hcompact).mono_set hboxsub
  have hpoint (t : V → ℝ) :
      |gffFejerCosCellObservable G β ξ f m t * K t| ≤ H t * K t := by
    have hH0 : 0 ≤ gffFejerCellObservable G β (fun _ => 0) m t := (Real.exp_pos _).le
    unfold gffFejerCosCellObservable
    rw [abs_mul, abs_mul, abs_of_nonneg (hKnonneg t), abs_of_nonneg hH0]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)) (hKnonneg t)
  have h1 : |gffFejerCosCellIntegral G β ξ f N m| ≤ gffFejerCellIntegral G β (fun _ => 0) N m := by
    unfold gffFejerCosCellIntegral gffFejerCellIntegral
    refine (abs_integral_le_integral_abs).trans ?_
    exact setIntegral_mono_on hfi.abs hHi (measurableSet_gffFejerCellBox (V := V))
      fun t _ => hpoint t
  exact h1.trans ((le_abs_self _).trans
    (abs_gffFejerCellIntegral_le_majorant G hG β hβ (fun _ => 0) N m))

/-- The cosine cell sums converge to the cosine-weighted cell centers. -/
theorem tendsto_tsum_gffFejerCosCellIntegral (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) (ξ : ℝ)
    (f : V → ℝ) :
    Tendsto (fun N : ℕ => ∑' m : pinnedIntegerField V root,
      gffFejerCosCellIntegral G β ξ f N m) atTop
      (𝓝 (∑' m : pinnedIntegerField V root, gffFejerCosCellObservable G β ξ f m 0)) := by
  apply tendsto_tsum_of_dominated_convergence
    (@summable_gffFejerCellMajorant V (inferInstance) hG.nonempty β hβ root (fun _ => 0))
  · intro m
    simpa [gffFejerCosCellIntegral] using
      (tendsto_integral_gffProductFejerKernel
        (H := gffFejerCosCellObservable G β ξ f m)
        (continuous_gffFejerCosCellObservable G β ξ f m))
  · filter_upwards [] with N m
    rw [Real.norm_eq_abs]
    exact abs_gffFejerCosCellIntegral_le_majorant G hG β hβ ξ f N m

/-- At a cell center the cosine observable is `cos(2πξ⟨m, f⟩)` times the IGFF weight at
inverse temperature `(2π)² β`. -/
theorem gffFejerCosCellObservable_center (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (β ξ : ℝ) {root : V} (f : V → ℝ) (m : pinnedIntegerField V root) :
    gffFejerCosCellObservable G β ξ f m 0 =
      Real.cos (2 * Real.pi * ξ * pairing (fun j => (m.1 j : ℝ)) f) *
        igffWeight G ((2 * Real.pi) ^ 2 * β) m := by
  unfold gffFejerCosCellObservable
  rw [gffFejerCellObservable_center_eq_igffTiltedWeight]
  have hfield : gffFejerCellField m 0 = gffFejerCellShift m := by
    funext j
    simp [gffFejerCellField]
  rw [hfield, pairing_gffFejerCellShift]
  unfold igffTiltedWeight
  simp only [pairing, mul_zero, Finset.sum_const_zero, Real.exp_zero, one_mul]
  congr 2
  ring

/-- **The Fejér cell limit for a cosine observable** (KP §5.1, p. 4, , for
`cos(ξ⟨φ, f⟩)`): the Fejér-weighted GFF ratio of the cosine converges to the rooted IGFF
expectation of `cos(2πξ⟨m, f⟩)` at inverse temperature `(2π)² β`. -/
theorem tendsto_gffFejerCosRatio_igff (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) (ξ : ℝ)
    (f : V → ℝ) :
    Tendsto (fun N : ℕ =>
        (∫ φ, Real.cos (ξ * pairing φ f) * gffFejerWeight N φ ∂gffMeasure G hG β hβ root) /
          ∫ φ, gffFejerWeight N φ ∂gffMeasure G hG β hβ root) atTop
      (𝓝 (igffExpectation G hG ((2 * Real.pi) ^ 2 * β)
        (mul_pos (sq_pos_of_ne_zero (by positivity)) hβ) root
        (fun m => Real.cos (2 * Real.pi * ξ * pairing (fun j => (m.1 j : ℝ)) f)))) := by
  set β' := (2 * Real.pi) ^ 2 * β with hβ'
  have hβ'pos : 0 < β' := mul_pos (sq_pos_of_ne_zero (by positivity)) hβ
  let Sc : ℕ → ℝ := fun N => ∑' m : pinnedIntegerField V root,
    gffFejerCosCellIntegral G β ξ f N m
  let S0 : ℕ → ℝ := fun N => ∑' m : pinnedIntegerField V root,
    gffFejerCellIntegral G β (fun _ => 0) N m
  have hnum : Tendsto Sc atTop (𝓝 (∑' m : pinnedIntegerField V root,
      Real.cos (2 * Real.pi * ξ * pairing (fun j => (m.1 j : ℝ)) f) * igffWeight G β' m)) := by
    have h := tendsto_tsum_gffFejerCosCellIntegral G hG β hβ root ξ f
    simp_rw [gffFejerCosCellObservable_center] at h
    exact h
  have hden : Tendsto S0 atTop (𝓝 (igffPartitionFunction G β' root)) := by
    have h := tendsto_tsum_gffFejerCellIntegral_igff G hG β hβ root (fun _ => 0)
    simpa [S0, β', igffTiltedWeight, Multigraph.pairing, igffPartitionFunction] using h
  have hpart : 0 < igffPartitionFunction G β' root := igffPartitionFunction_pos G hG β' hβ'pos root
  have hquot := hnum.div hden (ne_of_gt hpart)
  have hsumc : ∀ N, Summable fun m : pinnedIntegerField V root =>
      gffFejerCosCellIntegral G β ξ f N m := fun N =>
    Summable.of_norm_bounded
      (@summable_gffFejerCellMajorant V (inferInstance) hG.nonempty β hβ root (fun _ => 0))
      fun m => by
        rw [Real.norm_eq_abs]
        exact abs_gffFejerCosCellIntegral_le_majorant G hG β hβ ξ f N m
  have hscale : 0 < (2 * Real.pi) ^ Fintype.card V := pow_pos (by positivity) _
  have hZ := gffPartitionFunction_pos G hG β hβ root
  have hratio : ∀ N : ℕ, 0 < N →
      (∫ φ, Real.cos (ξ * pairing φ f) * gffFejerWeight N φ ∂gffMeasure G hG β hβ root) /
          (∫ φ, gffFejerWeight N φ ∂gffMeasure G hG β hβ root) = Sc N / S0 N := by
    intro N hN
    have hi0 : Integrable (fun φ : V → ℝ => gffFejerWeight N φ * gffDensity G β root φ)
        (volume : Measure (V → ℝ)) := by
      simpa [pairing] using
        (integrable_gffFejerDensityIntegrand G hG β hβ root (fun _ => 0) N)
    have hic : Integrable (fun φ : V → ℝ =>
        Real.cos (ξ * pairing φ f) * gffFejerWeight N φ * gffDensity G β root φ)
        (volume : Measure (V → ℝ)) := by
      have hmeas : Measurable fun φ : V → ℝ => Real.cos (ξ * pairing φ f) := by
        unfold pairing
        fun_prop
      refine (hi0.bdd_mul (c := 1) hmeas.aestronglyMeasurable
        (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)).congr
        (ae_of_all _ fun φ => ?_)
      ring
    have hcnum := (gffMeasure_integral_eq_div G hG β hβ root
      (fun φ => Real.cos (ξ * pairing φ f) * gffFejerWeight N φ)
      (by simpa only [mul_assoc] using hic)).2
    have hcden := (gffMeasure_integral_eq_div G hG β hβ root
      (fun φ => gffFejerWeight N φ) hi0).2
    have hraw0pos := gffFejerDensityIntegral_pos G hG β hβ root N hN
    have hraw0 : (∫ φ, gffFejerWeight N φ * gffDensity G β root φ) =
        (2 * Real.pi) ^ Fintype.card V * S0 N := by
      simpa [S0, Multigraph.pairing] using
        gffFejerDensityIntegral_eq_scaled_cellSum G hG β hβ root (fun _ => 0) N
    have hrawc := gffFejerCosDensityIntegral_eq_scaled_cellSum G hG β hβ root ξ f N (hsumc N)
    rw [hcnum, hcden]
    simp only [mul_assoc] at hrawc ⊢
    have hrawc' : (∫ φ, Real.cos (ξ * pairing φ f) * (gffFejerWeight N φ *
        gffDensity G β root φ)) = (2 * Real.pi) ^ Fintype.card V * Sc N := by
      rw [← hrawc]
    rw [hrawc', hraw0]
    have hS0 : S0 N ≠ 0 := by
      intro h
      rw [hraw0, h, mul_zero] at hraw0pos
      exact lt_irrefl 0 hraw0pos
    field_simp
  refine Tendsto.congr' ?_ hquot
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hratio N hN).symm

end FejerCos

end FroehlichSpencer.BKT
