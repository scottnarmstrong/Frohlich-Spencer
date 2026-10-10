/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.TheoremB
public import FroehlichSpencer.BKT.Coulomb.FreeGas
public import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

/-!
# FS81 Theorem B: free boundary condition and the thermodynamic limit

* `integral_cos_mul_cos_charge_gffLaw`, `integral_cos_mul_prod_sineGordonWeight`,
  **`weightedGFFExpectation_cos_sineGordon`**: the charge representation of the fractional
  correlation, `⟨cos(ξ⟨φ, f⟩)⟩_sG = e^{-κξ²⟨f, Cf⟩/2} ⟨cosh(ξκ⟨q, Cf⟩)⟩_Λ`: FS81 (1.22) equals
  (1.23).

This is the ratio `Z_Λ(ξ f)/Z_Λ` of the partition functions with and without the
  fractional external dipole.
* `latticeToSquare_modEq`, `cyclicDist_eq_natAbs`, `eventually_latticeDistance_torus`: on large
  periodic squares, reduced lattice points are at their `ℓ¹` distance.
* `freeFracCorrInternal`: FS81's `G_ξ(o, x)` with free boundary condition, using the whole-plane
  potential as `freeExpMomentInternal` of  does.

By `tendsto_torus_fracCorr` it is the limit
  of the periodic sine-Gordon correlations with charges confined to the sites.
* **`coulombB_free`**: FS81 Theorem B with free boundary condition on every finite `Λ ⊂ ℤ²`:
  `0 ≤ G_ξ(o, x) ≤ 2 (|o − x|₁ + 1)^{-c η² κ}` for `κ > κ₀(z, η)`.
* **`coulombB_thermodynamicLimit`**: take any sequence of finite regions containing `a ≠ b`, for
  example an exhaustion of `ℤ²`.

The correlations have a convergent subsequence, and every limit
  point satisfies the same bound.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Filter Topology FroehlichSpencer.BKT.Generic.Marked

/-! ### The charge representation of the fractional correlation -/

section Duality

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

/-- `∫ cos(ξ⟨φ, f⟩) cos⟨φ, q⟩ dμ` for a real neutral `f` and an integer `q`: zero if `q` is
charged, and `e^{-(⟨q, Cq⟩ + ξ²⟨f, Cf⟩)/(2β)} cosh(ξ⟨q, Cf⟩/β)` otherwise (`C = -G⁻¹`). -/
theorem integral_cos_mul_cos_charge_gffLaw (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (f : V → ℝ)
    (hf : ∑ j, f j = 0) (ξ : ℝ) (q : V → ℤ) :
    ∫ φ, Real.cos (ξ * ∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ)) ∂gffLaw G hG β hβ v =
      if ∑ j, q j = 0 then
        Real.exp (-(∑ j, (q j : ℝ) * -(G.greenOp hG (fun i => (q i : ℝ)) j) +
            ξ ^ 2 * ∑ j, f j * -(G.greenOp hG f j)) / (2 * β)) *
          Real.cosh (ξ * (∑ j, (q j : ℝ) * -(G.greenOp hG f j)) / β)
      else 0 := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  have hpt : ∀ φ : V → ℝ, Real.cos (ξ * ∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ)) =
      (Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * (ξ * f j)) +
        Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * (-(ξ * f j)))) / 2 := by
    intro φ
    have e1 : ∑ j, φ j * (ξ * f j) = ξ * ∑ j, φ j * f j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, φ j * (-(ξ * f j)) = -(ξ * ∑ j, φ j * f j) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2, ← sub_eq_add_neg, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hpt]
  have hint : ∀ τ : V → ℝ, Integrable (fun φ : V → ℝ =>
      Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * τ j)) (gffLaw G hG β hβ v) := fun τ =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [integral_div, integral_add (hint _) (hint _)]
  have hτ1 : ∑ j, ξ * f j = 0 := by rw [← Finset.mul_sum, hf, mul_zero]
  have hτ2 : ∑ j, -(ξ * f j) = 0 := by rw [Finset.sum_neg_distrib, hτ1, neg_zero]
  split_ifs with hq
  · have hqR : ∑ j, (q j : ℝ) = 0 := by exact_mod_cast hq
    -- the quadratic form of `q + s f`
    set a := ∑ j, (q j : ℝ) * -(G.greenOp hG (fun i => (q i : ℝ)) j) with ha
    set b := ∑ j, (q j : ℝ) * -(G.greenOp hG f j) with hb
    set c := ∑ j, f j * -(G.greenOp hG f j) with hc
    have hsym : ∑ j, f j * -(G.greenOp hG (fun i => (q i : ℝ)) j) = b := by
      have h := G.pairing_greenOp_comm hG f (fun i => (q i : ℝ))
      unfold Multigraph.pairing at h
      rw [hb]
      simp only [mul_neg, Finset.sum_neg_distrib, h]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hval : ∀ s : ℝ, ∫ φ, Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * (s * f j))
        ∂gffLaw G hG β hβ v = Real.exp (-(a + 2 * s * b + s ^ 2 * c) / (2 * β)) := by
      intro s
      have hcomb : ∀ φ : V → ℝ, ∑ j, φ j * (q j : ℝ) + ∑ j, φ j * (s * f j) =
          ∑ j, φ j * ((q j : ℝ) + s * f j) := fun φ => by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hcomb]
      have hτ : ∑ j, ((q j : ℝ) + s * f j) = 0 := by
        rw [Finset.sum_add_distrib, hqR, ← Finset.mul_sum, hf, mul_zero, add_zero]
      rw [integral_cos_neutral_gffLaw G hG β hβ v _ hτ]
      congr 1
      have hlin : G.greenOp hG (fun j => (q j : ℝ) + s * f j) =
          fun j => G.greenOp hG (fun i => (q i : ℝ)) j + s * G.greenOp hG f j := by
        have : (fun j => (q j : ℝ) + s * f j) = (fun i => (q i : ℝ)) + s • f := by
          funext j
          simp
        rw [this, map_add, map_smul]
        funext j
        simp
      have hexpand : Multigraph.pairing (fun j => (q j : ℝ) + s * f j)
          (-G.greenOp hG (fun j => (q j : ℝ) + s * f j)) = a + 2 * s * b + s ^ 2 * c := by
        unfold Multigraph.pairing
        rw [hlin]
        have hterm : ∀ j, ((q j : ℝ) + s * f j) *
            (-(fun j => G.greenOp hG (fun i => (q i : ℝ)) j + s * G.greenOp hG f j)) j =
            (q j : ℝ) * -(G.greenOp hG (fun i => (q i : ℝ)) j) +
              s * ((q j : ℝ) * -(G.greenOp hG f j)) +
              s * (f j * -(G.greenOp hG (fun i => (q i : ℝ)) j)) +
              s ^ 2 * (f j * -(G.greenOp hG f j)) := fun j => by
          simp only [Pi.neg_apply]
          ring
        rw [Finset.sum_congr rfl fun j _ => hterm j]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [← ha, ← hb, ← hc, hsym]
        ring
      rw [hexpand]
    have h1 := hval ξ
    have h2 := hval (-ξ)
    have e2 : ∀ φ : V → ℝ, ∑ j, φ j * (-(ξ * f j)) = ∑ j, φ j * (-ξ * f j) := fun φ =>
      Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e2]
    rw [h1, h2, Real.cosh_eq]
    have hβ2 : (2 : ℝ) * β ≠ 0 := by positivity
    rw [show -(a + 2 * ξ * b + ξ ^ 2 * c) / (2 * β) =
        -(a + ξ ^ 2 * c) / (2 * β) + -(ξ * b / β) by field_simp; ring,
      show -(a + 2 * -ξ * b + (-ξ) ^ 2 * c) / (2 * β) =
        -(a + ξ ^ 2 * c) / (2 * β) + ξ * b / β by field_simp; ring,
      Real.exp_add, Real.exp_add]
    ring
  · have hzero : ∀ τ : V → ℝ, ∑ j, τ j = 0 →
        ∫ φ, Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, φ j * τ j) ∂gffLaw G hG β hβ v = 0 := by
      intro τ hτ
      have h := gffLaw_integral_cos_charged_mul_eq_zero G hG β hβ v q hq τ hτ (fun _ => 1)
        (fun _ _ => rfl) continuous_const 1 (fun _ => by simp)
      simpa using h
    rw [hzero _ hτ1, hzero _ hτ2]
    simp

/-- FS81 (1.15)–(1.16) and (1.23) for the fractional correlation: the sine-Gordon integral of
`cos(ξ⟨φ, f⟩)` is `e^{-κξ²⟨f, Cf⟩/2} ∑_q w_κ(q) cosh(ξκ⟨q, Cf⟩)` (a fractional external dipole
in the charge representation). -/
theorem integral_cos_mul_prod_sineGordonWeight (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (ξ : ℝ) :
    ∫ φ, Real.cos (ξ * ∑ j, φ j * f j) * ∏ j, sineGordonWeightInternal N (lam j) (φ j)
        ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) v =
      Real.exp (-(κ * ξ ^ 2 * (∑ j, f j * -(T f j)) / 2)) *
        ∑ q ∈ chargeConfigsInternal V N,
          gasWeightInternal T κ lam q * Real.cosh (ξ * (κ * ∑ j, (q j : ℝ) * -(T f j))) := by
  have hTg : T = G.greenOp hG := G.greenOp_unique hG T hT.1 hT.2
  subst hTg
  have hβ : 0 < κ⁻¹ := inv_pos.2 hκ
  have := isProbabilityMeasure_gffLaw G hG κ⁻¹ hβ v
  have hexp : ∀ φ : V → ℝ, Real.cos (ξ * ∑ j, φ j * f j) *
      ∏ j, sineGordonWeightInternal N (lam j) (φ j) =
      ∑ q ∈ chargeConfigsInternal V N, (∏ j, lam j (q j)) *
        (Real.cos (ξ * ∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ))) := fun φ => by
    rw [prod_sineGordonWeight_eq_sum N lam hlam, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [integral_congr_ae (ae_of_all _ hexp)]
  have hint : ∀ q : V → ℤ, Integrable (fun φ : V → ℝ => (∏ j, lam j (q j)) *
      (Real.cos (ξ * ∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ))))
        (gffLaw G hG κ⁻¹ hβ v) := fun q =>
    (Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun φ => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |Real.cos (ξ * ∑ j, φ j * f j)| * |Real.cos (∑ j, φ j * (q j : ℝ))| ≤ 1 * 1 :=
              mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1)).const_mul _
  rw [integral_finsetSum _ fun q _ => hint q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_const_mul, integral_cos_mul_cos_charge_gffLaw G hG κ⁻¹ hβ v f hf ξ q]
  unfold gasWeightInternal chargeEnergyInternal
  split_ifs with hq
  · set a := ∑ j, (q j : ℝ) * -(G.greenOp hG (fun i => (q i : ℝ)) j) with ha
    set b := ∑ j, (q j : ℝ) * -(G.greenOp hG f j) with hb
    set c := ∑ j, f j * -(G.greenOp hG f j) with hc
    have e1 : -(a + ξ ^ 2 * c) / (2 * κ⁻¹) = -κ * (a / 2) + -(κ * ξ ^ 2 * c / 2) := by
      field_simp
      ring
    have e2 : ξ * b / κ⁻¹ = ξ * (κ * b) := by
      field_simp
    rw [e1, e2, Real.exp_add]
    ring
  · simp

/-- **The fractional correlation in the charge representation** (FS81 (1.22) = (1.23)):
`⟨cos(ξ⟨φ, f⟩)⟩_sG = e^{-κξ²⟨f, Cf⟩/2} ⟨cosh(ξκ⟨q, Cf⟩)⟩_Λ`. -/
theorem weightedGFFExpectation_cos_sineGordon (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (ξ : ℝ) :
    weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j))
        (fun φ => Real.cos (ξ * ∑ j, φ j * f j)) =
      Real.exp (-(κ * ξ ^ 2 * (∑ j, f j * -(T f j)) / 2)) *
        gasExpectationInternal N T κ lam
          (fun q => Real.cosh (ξ * (κ * ∑ j, (q j : ℝ) * -(T f j)))) := by
  rw [weightedGFFExpectation, weightedGFFNormalizer_sineGordon G hG κ hκ v N lam hlam T hT,
    integral_cos_mul_prod_sineGordonWeight G hG κ hκ v N lam hlam T hT f hf ξ,
    gasExpectationInternal, mul_div_assoc]

end Duality

/-! ### The distance on the large tori -/

section TorusDistance

theorem finEquiv_eq_val' {L : ℕ} [NeZero L] (a : Fin L) : ZMod.finEquiv L a = (a.val : ZMod L) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      simp only [ZMod.finEquiv]
      exact (Fin.cast_val_eq_self a).symm

/-- The coordinates of the reduction `ℤ² → Fin L × Fin L` are congruent to the lattice
coordinates. -/
theorem latticeToSquare_modEq (L : ℕ) [NeZero L] (z : ℤ × ℤ) :
    (((latticeToSquareInternal L z).1.val : ℤ) ≡ z.1 [ZMOD L]) ∧
      (((latticeToSquareInternal L z).2.val : ℤ) ≡ z.2 [ZMOD L]) := by
  have h : squareTorusVertexEquiv L (latticeToSquareInternal L z) = torusPointInternal L z := by
    unfold latticeToSquareInternal
    exact Equiv.apply_symm_apply _ _
  simp only [squareTorusVertexEquiv, torusPointInternal, Equiv.prodCongr_apply, Prod.map,
    Prod.mk.injEq, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv] at h
  rw [finEquiv_eq_val', finEquiv_eq_val'] at h
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast]
    exact h.1
  · rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast]
    exact h.2

/-- The cyclic distance of two residues with representatives `s, t` is `|t − s|` once
`2|t − s| < L`. -/
theorem cyclicDist_eq_natAbs {L : ℕ} (hL : 0 < L) (a b : Fin L) {s t : ℤ}
    (hs : (a.val : ℤ) ≡ s [ZMOD L]) (ht : (b.val : ℤ) ≡ t [ZMOD L])
    (hlt : 2 * |t - s| < L) : cyclicDist L a b = (t - s).natAbs := by
  have hmod : t - s ≡ (b.val : ℤ) - a.val [ZMOD L] := (ht.sub hs).symm
  have hle := cyclicDist_le_abs L hL a b (t - s) hmod
  obtain ⟨u, hu, hu'⟩ := exists_abs_eq_cyclicDist L hL a b
  have hdvd : (L : ℤ) ∣ u - (t - s) := (Int.ModEq.dvd (hu.trans hmod.symm).symm)
  have habs : |u - (t - s)| < L := by
    have h1 : |u - (t - s)| ≤ |u| + |t - s| := abs_sub _ _
    rw [hu'] at h1
    linarith
  have h0 : u - (t - s) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hu2 : u = t - s := by linarith
  rw [hu2] at hu'
  have : ((cyclicDist L a b : ℕ) : ℤ) = ((t - s).natAbs : ℤ) := by
    rw [← hu', Int.natCast_natAbs]
  exact_mod_cast this

/-- **On large tori the reduced points are at their `ℓ¹` distance**: eventually in `n`,
`dist_{Λ_{L_n}^per}(ā, b̄) = |a₁ − b₁| + |a₂ − b₂|`. -/
theorem eventually_latticeDistance_torus (a b : ℤ × ℤ) :
    ∀ᶠ n in atTop, latticeDistance .periodic (torusSideInternal n)
        (latticeToSquareInternal (torusSideInternal n) a)
        (latticeToSquareInternal (torusSideInternal n) b) =
      (b.1 - a.1).natAbs + (b.2 - a.2).natAbs := by
  filter_upwards [eventually_ge_atTop ((b.1 - a.1).natAbs + (b.2 - a.2).natAbs)] with n hn
  set L := torusSideInternal n with hLdef
  have hL : 0 < L := by rw [hLdef]; unfold torusSideInternal; omega
  have hLn : (L : ℤ) = 2 * n + 4 := by rw [hLdef]; unfold torusSideInternal; push_cast; ring
  obtain ⟨ha1, ha2⟩ := latticeToSquare_modEq L a
  obtain ⟨hb1, hb2⟩ := latticeToSquare_modEq L b
  have hn1 : |b.1 - a.1| ≤ n := by
    have : ((b.1 - a.1).natAbs : ℤ) ≤ n := by exact_mod_cast (Nat.le_add_right _ _).trans hn
    rwa [Int.natCast_natAbs] at this
  have hn2 : |b.2 - a.2| ≤ n := by
    have : ((b.2 - a.2).natAbs : ℤ) ≤ n := by exact_mod_cast (Nat.le_add_left _ _).trans hn
    rwa [Int.natCast_natAbs] at this
  show (squarePeriodic L).toSimpleGraph.dist _ _ = _
  rw [squarePeriodic_dist_eq_cyclicDist,
    cyclicDist_eq_natAbs hL _ _ ha1 hb1 (by rw [hLn]; linarith),
    cyclicDist_eq_natAbs hL _ _ ha2 hb2 (by rw [hLn]; linarith)]

end TorusDistance

/-! ### The free boundary condition and the thermodynamic limit -/

section Free

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real dipole `δ_o − δ_x` on the sites. -/
def dipoleRealInternal (o x : V) : V → ℝ := fun v => (dipoleMark o x v : ℝ)

theorem sum_dipoleRealInternal (o x : V) : ∑ v, dipoleRealInternal o x v = 0 := by
  unfold dipoleRealInternal
  exact_mod_cast sum_univ_dipoleMark o x

theorem sum_dipoleRealInternal_mul (o x : V) (g : V → ℝ) :
    ∑ v, dipoleRealInternal o x v * g v = g o - g x := by
  unfold dipoleRealInternal dipoleMark
  push_cast
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-- **FS81 (1.23), free boundary condition**: the fractional-charge correlation of the
hard-core gas on the sites `V` (positions `pos`) with FS81's whole-plane potential,
`G_ξ(o, x) = e^{-κξ²⟨f, Cf⟩/2} ⟨cosh(ξκ⟨q, Cf⟩)⟩_Λ`, `f = δ_o − δ_x`: the charge representation
of `⟨cos(ξ(φ_o − φ_x))⟩` (`weightedGFFExpectation_cos_sineGordon`), and the limit of the periodic
sine-Gordon correlations (`tendsto_torus_fracCorr`). -/
def freeFracCorrInternal (pos : V → ℤ × ℤ) (κ z ξ : ℝ) (o x : V) : ℝ :=
  Real.exp (-(κ * ξ ^ 2 * freeQuadInternal pos (dipoleRealInternal o x) / 2)) *
    freeGasExpectationInternal pos κ z
      (fun p => Real.cosh (ξ * (κ * freeChargePairingInternal pos (dipoleRealInternal o x) p)))

/-- **The free fractional correlation is the periodic thermodynamic limit** (FS81 p. 531,
`dμ_κ = lim dμ_{κ,Ω}` with periodic `Ω`): the sine-Gordon correlations `G_ξ` on `Λ_{L_n}^per`,
charges confined to the sites, converge to `freeFracCorrInternal`. -/
theorem tendsto_torus_fracCorr (pos : V → ℤ × ℤ) (hpos : Function.Injective pos) (κ : ℝ)
    (hκ : 0 < κ) {z : ℝ} (hz : 0 ≤ z) (ξ : ℝ) (o x : V)
    (root : ∀ n, Fin (torusSideInternal n) × Fin (torusSideInternal n)) :
    Tendsto (fun n => fracCorrInternal (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n)
        (Finset.univ.image (torusSiteMapInternal pos n)) z ξ
        (torusSiteMapInternal pos n o) (torusSiteMapInternal pos n x))
      atTop (𝓝 (freeFracCorrInternal pos κ z ξ o x)) := by
  set f := dipoleRealInternal o x with hf
  have hf0 : ∑ v, f v = 0 := sum_dipoleRealInternal o x
  have hobs : ∀ n (φ : Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℝ),
      ξ * (φ (torusSiteMapInternal pos n o) - φ (torusSiteMapInternal pos n x)) =
        ξ * ∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j := by
    intro n φ
    congr 1
    rw [Finset.sum_congr rfl fun j _ => mul_comm (φ j) _, sum_latticePush_mul, hf,
      sum_dipoleRealInternal_mul]
    rfl
  have hrep : ∀ᶠ n in atTop,
      Real.exp (-(κ * ξ ^ 2 * (∑ v, f v * -(torusPullbackOpInternal pos n f v)) / 2)) *
        gasExpectationInternal 1 (torusPullbackOpInternal pos n) κ
          (fun _ => hardCoreWeightInternal z)
          (fun p => Real.cosh (ξ * (κ * ∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v)))) =
      fracCorrInternal (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n)
        (Finset.univ.image (torusSiteMapInternal pos n)) z ξ
        (torusSiteMapInternal pos n o) (torusSiteMapInternal pos n x) := by
    filter_upwards [eventually_injective_latticeToSquare pos hpos] with n hinj
    unfold fracCorrInternal
    simp_rw [hobs n]
    rw [weightedGFFExpectation_cos_sineGordon (squarePeriodic (torusSideInternal n))
      (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n) 1 _
      (regionWeight_neg _ (hardCoreWeight_neg z)) (torusGreenOpInternal n)
      (isLaplacianPseudoinverse_torusGreenOp n) (latticePushInternal (torusSideInternal n) pos f)
      (by rw [sum_latticePush]; exact hf0) ξ,
      torus_gasExpectation_eq pos n hinj κ z (fun y => Real.cosh (ξ * (κ * y))) f,
      ← sum_mul_neg_torusPullbackOp]
  refine Tendsto.congr' hrep ?_
  unfold freeFracCorrInternal freeGasExpectationInternal freeQuadInternal
    freeChargePairingInternal
  refine Tendsto.mul ((Real.continuous_exp.tendsto _).comp ?_) ?_
  · exact (((tendsto_sum_mul_neg_torusPullbackOp pos f f hf0).const_mul (κ * ξ ^ 2)).div_const
      2).neg
  · refine tendsto_gasExpectation_of_tendsto 1 _ _ κ _ _ _
      (fun p hp => tendsto_chargeEnergy_torusPullbackOp pos p hp) (fun p => ?_)
      (freeGasPartition_pos pos κ hz).ne'
    exact (Real.continuous_cosh.tendsto _).comp
      (((tendsto_sum_mul_neg_torusPullbackOp pos _ f hf0).const_mul κ).const_mul ξ)

end Free

/-! ### FS81 Theorem B: free boundary condition and the thermodynamic limit -/

section TheoremB

/-- **FS81 Theorem B, free boundary condition** (hard-core gas, `0 < ξ < 1`). There is an
absolute `c > 0` such that for every activity `z ≥ 0` and `η > 0` there is `κ₀` with: for every
finite set of sites `V` at distinct positions `pos : V → ℤ²`, all `o ≠ x` in `V`, `κ > κ₀` and
`min(ξ, 1 − ξ) ≥ η`, `0 ≤ G_ξ(o, x) ≤ 2 (|pos o − pos x|₁ + 1)^{-c η² κ}`. The exponent
`β' = c η² κ` tends to infinity with the Coulomb inverse temperature `κ` for fixed `ξ`. The bound
is uniform in `V`; the threshold `κ₀` depends on `η`, as in FS81 (`β > O(η⁻²)`). -/
theorem coulombB_free :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, 0 ≤ z → ∀ η : ℝ, 0 < η → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (pos : V → ℤ × ℤ), Function.Injective pos →
        ∀ o x : V, o ≠ x → ∀ κ : ℝ, κ₀ < κ → ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
          0 ≤ freeFracCorrInternal pos κ z ξ o x ∧
            freeFracCorrInternal pos κ z ξ o x ≤
              2 * ((((pos x).1 - (pos o).1).natAbs + ((pos x).2 - (pos o).2).natAbs : ℕ) + 1 :
                ℝ) ^ (-(c * η ^ 2 * κ)) := by
  obtain ⟨c, hc, hsq⟩ := coulombB_squares
  refine ⟨c, hc, fun z hz η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hL⟩ := hsq z hz η hη
  refine ⟨κ₀, hκ₀, fun V _ _ pos hpos o x hox κ hκκ₀ ξ hξ0 hξ1 hηξ => ?_⟩
  have hκ : 0 < κ := hκ₀.trans hκκ₀
  have hT := tendsto_torus_fracCorr pos hpos κ hκ hz ξ o x
    (fun n => torusSiteMapInternal pos n o)
  have hev : ∀ᶠ n in atTop,
      0 ≤ fracCorrInternal (squarePeriodic (torusSideInternal n))
          (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (torusSiteMapInternal pos n o)
          (Finset.univ.image (torusSiteMapInternal pos n)) z ξ
          (torusSiteMapInternal pos n o) (torusSiteMapInternal pos n x) ∧
        fracCorrInternal (squarePeriodic (torusSideInternal n))
          (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (torusSiteMapInternal pos n o)
          (Finset.univ.image (torusSiteMapInternal pos n)) z ξ
          (torusSiteMapInternal pos n o) (torusSiteMapInternal pos n x) ≤
        2 * ((((pos x).1 - (pos o).1).natAbs + ((pos x).2 - (pos o).2).natAbs : ℕ) + 1 :
          ℝ) ^ (-(c * η ^ 2 * κ)) := by
    filter_upwards [eventually_injective_latticeToSquare pos hpos,
      eventually_latticeDistance_torus (pos o) (pos x)] with n hinj hdist
    have hne : torusSiteMapInternal pos n o ≠ torusSiteMapInternal pos n x :=
      fun h => hox (hinj h)
    have h := ((hL (torusSideInternal n) (one_lt_torusSide n)).2 (even_torusSide n)) κ hκ hκκ₀
      (torusSiteMapInternal pos n o) (Finset.univ.image (torusSiteMapInternal pos n))
      (torusSiteMapInternal pos n o) (torusSiteMapInternal pos n x) hne ξ hξ0 hξ1 hηξ
    have hd : latticeDistance .periodic (torusSideInternal n) (torusSiteMapInternal pos n o)
        (torusSiteMapInternal pos n x) =
        ((pos x).1 - (pos o).1).natAbs + ((pos x).2 - (pos o).2).natAbs := hdist
    rw [hd] at h
    exact h
  exact ⟨ge_of_tendsto hT (hev.mono fun n h => h.1), le_of_tendsto hT (hev.mono fun n h => h.2)⟩

/-- FS81's `G_ξ(a, b)` on a finite region `Λ ⊂ ℤ²` with free boundary condition (`0` unless
`a, b ∈ Λ`). -/
def regionFracCorrInternal (Λ : Finset (ℤ × ℤ)) (κ z ξ : ℝ) (a b : ℤ × ℤ) : ℝ :=
  if h : a ∈ Λ ∧ b ∈ Λ then
    freeFracCorrInternal (fun v : Λ => (v : ℤ × ℤ)) κ z ξ ⟨a, h.1⟩ ⟨b, h.2⟩
  else 0

/-- **FS81 Theorem B in the thermodynamic limit** (hard-core gas, `0 < ξ < 1`). There is an
absolute `c > 0` such that for every `z ≥ 0` and `η > 0` there is `κ₀` with: for `κ > κ₀`,
`min(ξ, 1 − ξ) ≥ η`, `a ≠ b` in `ℤ²` and every sequence of finite regions `Λ_k ∋ a, b` (for
example an exhaustion of `ℤ²`), the free-b.c. correlations `G^{Λ_k}_ξ(a, b)` satisfy
`0 ≤ G ≤ B = 2 (|a − b|₁ + 1)^{-c η² κ}`, have a convergent subsequence, and every limit point
`ℓ` (every thermodynamic-limit value) satisfies `0 ≤ ℓ ≤ B`. -/
theorem coulombB_thermodynamicLimit :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, 0 ≤ z → ∀ η : ℝ, 0 < η → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ κ : ℝ, κ₀ < κ → ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
        ∀ a b : ℤ × ℤ, a ≠ b → ∀ Λs : ℕ → Finset (ℤ × ℤ), (∀ k, a ∈ Λs k ∧ b ∈ Λs k) →
          (∀ k, 0 ≤ regionFracCorrInternal (Λs k) κ z ξ a b ∧
            regionFracCorrInternal (Λs k) κ z ξ a b ≤
              2 * (((b.1 - a.1).natAbs + (b.2 - a.2).natAbs : ℕ) + 1 : ℝ) ^ (-(c * η ^ 2 * κ))) ∧
          (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => regionFracCorrInternal (Λs (φ k)) κ z ξ a b) atTop (𝓝 ℓ)) ∧
          ∀ ℓ : ℝ, MapClusterPt ℓ atTop (fun k => regionFracCorrInternal (Λs k) κ z ξ a b) →
            0 ≤ ℓ ∧
              ℓ ≤ 2 * (((b.1 - a.1).natAbs + (b.2 - a.2).natAbs : ℕ) + 1 : ℝ) ^
                (-(c * η ^ 2 * κ)) := by
  obtain ⟨c, hc, hfree⟩ := coulombB_free
  refine ⟨c, hc, fun z hz η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := hfree z hz η hη
  refine ⟨κ₀, hκ₀, fun κ hκ ξ hξ0 hξ1 hηξ a b hab Λs hΛs => ?_⟩
  set B : ℝ := 2 * (((b.1 - a.1).natAbs + (b.2 - a.2).natAbs : ℕ) + 1 : ℝ) ^
    (-(c * η ^ 2 * κ)) with hB
  have hk : ∀ k, 0 ≤ regionFracCorrInternal (Λs k) κ z ξ a b ∧
      regionFracCorrInternal (Λs k) κ z ξ a b ≤ B := by
    intro k
    unfold regionFracCorrInternal
    rw [dite_eq_left (hΛs k)]
    exact hF (Λs k) (fun v : Λs k => (v : ℤ × ℤ)) Subtype.val_injective ⟨a, (hΛs k).1⟩
      ⟨b, (hΛs k).2⟩ (fun h => hab (congrArg Subtype.val h)) κ hκ ξ hξ0 hξ1 hηξ
  have hmem : ∀ k, regionFracCorrInternal (Λs k) κ z ξ a b ∈ Set.Icc 0 B := fun k => hk k
  refine ⟨hk, ?_, fun ℓ hℓ => isClosed_Icc.mem_of_mapClusterPt hℓ (Eventually.of_forall hmem)⟩
  obtain ⟨ℓ, -, φ, hφ, hT⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 B) hmem
  exact ⟨ℓ, φ, hφ, hT⟩

end TheoremB

end FroehlichSpencer.BKT.Coulomb
