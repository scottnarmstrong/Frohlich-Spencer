/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Reduction.T16AssemblyStatements
public import FroehlichSpencer.BKT.Reduction.T16ImpliesT15
import FroehlichSpencer.BKT.Reduction.SpinWaveTranslation
import FroehlichSpencer.BKT.Gaussian.EnsembleSelection
import FroehlichSpencer.BKT.Charges.DensityRouting
import FroehlichSpencer.BKT.Charges.PatchIsolation
import FroehlichSpencer.BKT.FiniteGraph.Laplacian
import FroehlichSpencer.BKT.Surface.DensityCenterExists
import FroehlichSpencer.BKT.Surface.GFFWellDefined

/-!
# KP Theorem 1.6 from Theorem 2.2, Proposition 2.4 and Proposition 2.1

The three
inputs are the exact propositions of `Reduction/T16AssemblyStatements.lean`:
`t22Statement` (KP Theorem 2.2), `p24Statement` (KP Proposition 2.4) and `p21Statement`
(KP Proposition 2.1).

The conclusion `t16Statement` (`Reduction/T16ImpliesT15.lean`) is the
statement of the `weightedGFF_renormalization`, copied verbatim.

For one square domain `Λ`, root `v`, `0 < β < β₀` and sub-Gaussian `lam`:

1. **Expansion (T2.2).** `∏_j lam j (φ_j + σ_j) = ∑_i c_i ∏_{ϱ ∈ 𝒩_i} [1 + K cos(⟨φ + σ, ϱ⟩)]`,
   integrated term by term.
2. **Neutral reduction.** By T2.2(a) the non-neutral density integrates out
   (`gffLaw_integral_prod_shift_eq_neutralPart`); the branch becomes the neutral part `𝒩₀`.
3. **Spin waves.** P2.4 gives one spin wave `a_ϱ` per `ϱ ∈ 𝒩₀` (one admissible center choice
   and the cover selection of P2.4).

P2.1 has not on main, so it is the third hypothesis.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Reduction

open MeasureTheory

/-! ## Step 4: the coefficient damping algebra -/

/--
With
`h = ln Γ₊ + 1 + η` (`Γ₊ = max(1, Γ)`), `s = ‖ϱ‖₂²`, `S = ∑_k |𝒮_k^sep(ϱ)|`, `S₀ = |𝒮₀(ϱ)|`,
`A = A(ϱ)` and `ℓ = log₂(d(ϱ) + 1)`, the hypotheses `ℓ ≤ A ≤ D₁ (S₀ + S)` (P2.1) and `S₀ ≤ s`
give `D₂ A + (h + θ/β) s - β⁻¹ (s/16 + D₃ S) ≤ -(c₁/β)(s + ℓ)` for `0 < β < β₀`.
-/
theorem exists_damping_constants (Γ η θ D₁ D₂ D₃ : ℝ) (hθ : θ < 1 / 16) (hD₁ : 0 < D₁)
    (hD₂ : 0 < D₂) (hD₃ : 0 < D₃) :
    ∃ β₀ c₁ : ℝ, 0 < β₀ ∧ 0 < c₁ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s → A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 Γ) + 1 + η + θ / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 16 - θ := ⟨_, rfl⟩
  have hδpos : 0 < δ := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min 1 (δ / (2 * D₃)) := ⟨_, rfl⟩
  have htpos : 0 < t := ht ▸ lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := ht ▸ min_le_left _ _
  have htD : t * D₃ ≤ δ / 2 := by
    have h : t ≤ δ / (2 * D₃) := ht ▸ min_le_right _ _
    calc t * D₃ ≤ δ / (2 * D₃) * D₃ := mul_le_mul_of_nonneg_right h hD₃.le
      _ = δ / 2 := by field_simp
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Real.log (max 1 Γ) + |η| + 2 := ⟨_, rfl⟩
  have hlog : 0 ≤ Real.log (max 1 Γ) := Real.log_nonneg (le_max_left _ _)
  have hHpos : 0 < H := by
    have := abs_nonneg η
    linarith
  have hhH : Real.log (max 1 Γ) + 1 + η ≤ H := by
    have := le_abs_self η
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = t * D₃ / (2 * D₁) := ⟨_, rfl⟩
  have hepos : 0 < e := he ▸ by positivity
  have h2e : 2 * e * D₁ = t * D₃ := by
    rw [he]
    field_simp
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (δ / 4) e := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ lt_min (by positivity) hepos
  refine ⟨min (δ / (4 * H)) (e / D₂), c, lt_min (by positivity) (by positivity), hcpos, ?_⟩
  intro β hβ hββ₀ s S A ℓ S₀ hs hS hℓ hℓA hS₀ hA
  have hβ1 : β * H < δ / 4 := by
    have h : β < δ / (4 * H) := lt_of_lt_of_le hββ₀ (min_le_left _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  have hβ2 : β * D₂ < e := by
    have h : β < e / D₂ := lt_of_lt_of_le hββ₀ (min_le_right _ _)
    rwa [lt_div_iff₀ hD₂] at h
  have hA0 : 0 ≤ A := hℓ.trans hℓA
  have k1 : β * D₂ * A ≤ e * A := mul_le_mul_of_nonneg_right hβ2.le hA0
  have k2 : β * (Real.log (max 1 Γ) + 1 + η) * s ≤ δ / 4 * s := by
    refine mul_le_mul_of_nonneg_right ?_ hs
    calc β * (Real.log (max 1 Γ) + 1 + η) ≤ β * H := mul_le_mul_of_nonneg_left hhH hβ.le
      _ ≤ δ / 4 := hβ1.le
  have k3 : t * D₃ * S ≤ D₃ * S := by
    have h := mul_le_mul_of_nonneg_right ht1 (mul_nonneg hD₃.le hS)
    linarith
  have k4 : 2 * e * A ≤ t * D₃ * S₀ + t * D₃ * S := by
    calc 2 * e * A ≤ 2 * e * (D₁ * (S₀ + S)) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = t * D₃ * S₀ + t * D₃ * S := by rw [← h2e]; ring
  have k5 : t * D₃ * S₀ ≤ t * D₃ * s := mul_le_mul_of_nonneg_left hS₀ (by positivity)
  have k6 : t * D₃ * s ≤ δ / 2 * s := mul_le_mul_of_nonneg_right htD hs
  have kc1 : c * A ≤ e * A := mul_le_mul_of_nonneg_right (hc ▸ min_le_right _ _) hA0
  have kc2 : c * s ≤ δ / 4 * s := mul_le_mul_of_nonneg_right (hc ▸ min_le_left _ _) hs
  have kc3 : c * ℓ ≤ c * A := mul_le_mul_of_nonneg_left hℓA hcpos.le
  have key : β * D₂ * A + β * (Real.log (max 1 Γ) + 1 + η) * s + θ * s -
      (1 / 16 * s + D₃ * S) ≤ -(c * (s + ℓ)) := by
    linear_combination k1 + k2 + k3 + k4 + k5 + k6 + kc1 + kc2 + kc3 + s * hδ
  have hlhs : D₂ * A + (Real.log (max 1 Γ) + 1 + η + θ / β) * s -
      1 / β * (1 / 16 * s + D₃ * S) =
      (β * D₂ * A + β * (Real.log (max 1 Γ) + 1 + η) * s + θ * s -
        (1 / 16 * s + D₃ * S)) / β := by
    field_simp
    ring
  have hrhs : -(c / β) * (s + ℓ) = -(c * (s + ℓ)) / β := by ring
  rw [hlhs, hrhs]
  exact (div_le_div_iff_of_pos_right hβ).mpr key

/-! ## Step 4: the site-weight product -/

/-- `∏_{j ∈ supp ϱ} e^{ϱ(j)²} |λ̂_j(|ϱ(j)|)| ≤ e^{(ln Γ₊ + 1 + κ) ‖ϱ‖₂²}` when
`|λ̂_j(q)| ≤ Γ e^{κ q²}` for `q ≥ 1` (KP (1.9) with `κ = η + θ/β`; `Γ₊ = max(1, Γ)`). -/
theorem prod_exp_sq_mul_abs_le {V : Type*} [Fintype V] (ϱ : V → ℤ) (lamHat : V → ℕ → ℝ)
    (Γ κ : ℝ) (hbound : ∀ j q, 1 ≤ q → |lamHat j q| ≤ Γ * Real.exp (κ * q ^ 2)) :
    ∏ j ∈ Finset.univ.filter (fun j => ϱ j ≠ 0),
        Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
      Real.exp ((Real.log (max 1 Γ) + 1 + κ) * ∑ j, (ϱ j : ℝ) ^ 2) := by
  have hsum : ∑ j, (ϱ j : ℝ) ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j => ϱ j ≠ 0), (ϱ j : ℝ) ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · simp [not_not.mp h]
  have hlog : 0 ≤ Real.log (max 1 Γ) := Real.log_nonneg (le_max_left _ _)
  rw [hsum, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j hj => ?_
  have hj0 : ϱ j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hq : 1 ≤ (ϱ j).natAbs := Int.natAbs_pos.mpr hj0
  have hsq : (((ϱ j).natAbs : ℕ) : ℝ) ^ 2 = (ϱ j : ℝ) ^ 2 := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  have h1 : 1 ≤ (ϱ j : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ |(ϱ j : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hj0
    exact (one_le_sq_iff_one_le_abs _).mpr h
  have hb := hbound j _ hq
  rw [hsq] at hb
  have hΓ : Γ ≤ Real.exp (Real.log (max 1 Γ) * (ϱ j : ℝ) ^ 2) :=
    calc Γ ≤ max 1 Γ := le_max_right _ _
      _ = Real.exp (Real.log (max 1 Γ)) :=
        (Real.exp_log (lt_max_of_lt_left one_pos)).symm
      _ ≤ Real.exp (Real.log (max 1 Γ) * (ϱ j : ℝ) ^ 2) :=
        Real.exp_le_exp.mpr (le_mul_of_one_le_right hlog h1)
  calc Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|
      ≤ Real.exp ((ϱ j : ℝ) ^ 2) * (Γ * Real.exp (κ * (ϱ j : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ Real.exp ((ϱ j : ℝ) ^ 2) *
        (Real.exp (Real.log (max 1 Γ) * (ϱ j : ℝ) ^ 2) * Real.exp (κ * (ϱ j : ℝ) ^ 2)) := by
        gcongr
    _ = Real.exp ((Real.log (max 1 Γ) + 1 + κ) * (ϱ j : ℝ) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- `|𝒮₀(ϱ)| ≤ |supp ϱ|`: the scale-`0` squares at the support points cover the support. -/
theorem squareCoverNumber_zero_le_card (boundary : SquareBoundary) (L : ℕ)
    (ϱ : ChargeDensity L) : squareCoverNumber boundary L 0 ϱ ≤ (chargeSupport ϱ).card := by
  classical
  refine (squareCoverNumber_le boundary L 0 ϱ ((chargeSupport ϱ).image (kpSquare boundary L 0))
    ⟨?_, ?_⟩).trans Finset.card_image_le
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  · intro x hx
    exact ⟨kpSquare boundary L 0 x, Finset.mem_image_of_mem _ hx,
      anchor_mem_kpSquare boundary L 0 x⟩

/-- `|supp ϱ| ≤ ‖ϱ‖₂²` for an integer-valued `ϱ`. -/
theorem card_chargeSupport_le_sum_sq {L : ℕ} (ϱ : ChargeDensity L) :
    ((chargeSupport ϱ).card : ℝ) ≤ ∑ j, (ϱ j : ℝ) ^ 2 := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  calc ∑ j ∈ chargeSupport ϱ, (1 : ℝ) ≤ ∑ j ∈ chargeSupport ϱ, (ϱ j : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj0 : ϱ j ≠ 0 := (Finset.mem_filter.mp hj).2
        have h : (1 : ℝ) ≤ |(ϱ j : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hj0
        exact (one_le_sq_iff_one_le_abs _).mpr h
    _ ≤ ∑ j, (ϱ j : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j _ _ => sq_nonneg _

/-! ## Separation from T2.2(b) -/

section Separation

variable (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
  (Λ : Multigraph (Fin L × Fin L) E)

/-- `M t^α ≥ 2^16 t` for `t ≥ 1`, with `M = 2^16` and `α = 7/4`. -/
theorem le_chargeCoverScale_mul_rpow {t : ℝ} (ht : 1 ≤ t) :
    65536 * t ≤ (chargeCoverScale : ℝ) * t ^ chargeCoverExponent := by
  have hM : (chargeCoverScale : ℝ) = 65536 := by norm_num [chargeCoverScale]
  have hα : (1 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  rw [hM]
  exact mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_one_le ht hα) (by norm_num)

omit [Fintype E] in
/-- The distance between two densities is at most the graph distance between support points. -/
theorem densityDistance_le_dist
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    {ϱ ϱ' : ChargeDensity L} {x y : Fin L × Fin L} (hx : ϱ x ≠ 0) (hy : ϱ' y ≠ 0) :
    densityDistance boundary L ϱ ϱ' ≤ Λ.toSimpleGraph.dist x y := by
  rw [← hdist]
  exact squareDistance_le_latticeDistance_of_mem boundary L _ _ x y
    (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)

omit [Fintype E] in
/-- KP p. 12, P2.4(2) "in particular": by T2.2(b), a density `ϱ'` with `d(ϱ') > 2 d(ϱ)` has
support outside `D(ϱ)`. -/
theorem notMem_densityDomain_of_scaleSeparated (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    {ϱ ϱ' : ChargeDensity L} (hϱ0 : ϱ ≠ 0) (hQ : ∑ j, ϱ j = 0)
    (hsep : (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L ϱ) (chargeDiameter boundary L ϱ') : ℕ) : ℝ) ^
          chargeCoverExponent ≤ densityDistance boundary L ϱ ϱ')
    (hlt : 2 * Λ.densityDiameter ϱ < Λ.densityDiameter ϱ') {j : Fin L × Fin L}
    (hj : Λ.IsDensityCenter ϱ j) {x : Fin L × Fin L} (hx : ϱ' x ≠ 0) :
    x ∉ Λ.densityDomain ϱ j := by
  intro hxD
  have hd1 : 1 ≤ Λ.densityDiameter ϱ := Λ.one_le_densityDiameter_of_neutral hΛ ϱ hϱ0 hQ
  rw [chargeDiameter_eq_densityDiameter boundary Λ hdist,
    chargeDiameter_eq_densityDiameter boundary Λ hdist, min_eq_left (by omega)] at hsep
  have hdistle := densityDistance_le_dist boundary Λ hdist hj.1 hx
  have hxj : Λ.toSimpleGraph.dist x j < 2 * Λ.densityDiameter ϱ := hxD
  rw [SimpleGraph.dist_comm] at hdistle
  have hlow := le_chargeCoverScale_mul_rpow (t := (Λ.densityDiameter ϱ : ℝ))
    (by exact_mod_cast hd1)
  have hup : (densityDistance boundary L ϱ ϱ' : ℝ) < 2 * (Λ.densityDiameter ϱ : ℝ) := by
    exact_mod_cast lt_of_le_of_lt hdistle hxj
  have hd1' : (1 : ℝ) ≤ Λ.densityDiameter ϱ := by exact_mod_cast hd1
  linarith

omit [Fintype E] in

theorem densityDomain_inter_eq_empty (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    {ϱ₁ ϱ₂ : ChargeDensity L}
    (hsep : (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) : ℕ) : ℝ) ^
          chargeCoverExponent ≤ densityDistance boundary L ϱ₁ ϱ₂)
    {k : ℕ} (hk : 1 ≤ k)
    (h₁ : Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2))
    (h₂ : Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2))
    {j₁ j₂ : Fin L × Fin L} (hj₁ : Λ.IsDensityCenter ϱ₁ j₁) (hj₂ : Λ.IsDensityCenter ϱ₂ j₂) :
    Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx₁, hx₂⟩
  rw [chargeDiameter_eq_densityDiameter boundary Λ hdist,
    chargeDiameter_eq_densityDiameter boundary Λ hdist] at hsep
  have hx₁' : Λ.toSimpleGraph.dist x j₁ < 2 * Λ.densityDiameter ϱ₁ := hx₁
  have hx₂' : Λ.toSimpleGraph.dist x j₂ < 2 * Λ.densityDiameter ϱ₂ := hx₂
  have htri : Λ.toSimpleGraph.dist j₁ j₂ ≤
      Λ.toSimpleGraph.dist j₁ x + Λ.toSimpleGraph.dist x j₂ := hΛ.dist_triangle
  rw [SimpleGraph.dist_comm (u := j₁) (v := x)] at htri
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hk2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨h₁l, h₁u⟩ := h₁
  obtain ⟨h₂l, h₂u⟩ := h₂
  set t := min (Λ.densityDiameter ϱ₁) (Λ.densityDiameter ϱ₂) with ht
  have ht1 : 1 ≤ t := le_min (by omega) (by omega)
  have hclose : Λ.toSimpleGraph.dist j₁ j₂ < 8 * t := by
    have : Λ.densityDiameter ϱ₁ ≤ 2 * t ∧ Λ.densityDiameter ϱ₂ ≤ 2 * t := by
      rcases min_choice (Λ.densityDiameter ϱ₁) (Λ.densityDiameter ϱ₂) with h | h <;>
        rw [← ht] at h <;> constructor <;> omega
    omega
  have hdd : (densityDistance boundary L ϱ₁ ϱ₂ : ℝ) ≤ Λ.toSimpleGraph.dist j₁ j₂ := by
    exact_mod_cast densityDistance_le_dist boundary Λ hdist hj₁.1 hj₂.1
  have hlow := le_chargeCoverScale_mul_rpow (t := (t : ℝ)) (by exact_mod_cast ht1)
  have hclose' : (Λ.toSimpleGraph.dist j₁ j₂ : ℝ) < 8 * (t : ℝ) := by exact_mod_cast hclose
  have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  linarith

end Separation

/-! ## Step 2: orthogonality of the spin waves -/

section Orthogonality

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

theorem pairing_laplacian_eq_zero_of_eq_const (G : Multigraph V E) {f g : V → ℝ} {c : ℝ}
    (h : ∀ j, G.laplacian g j ≠ 0 → f j = c) : Multigraph.pairing f (G.laplacian g) = 0 := by
  have hterm : ∀ j, f j * G.laplacian g j = c * G.laplacian g j := by
    intro j
    by_cases hj : G.laplacian g j = 0
    · rw [hj, mul_zero, mul_zero]
    · rw [h j hj]
  rw [Multigraph.pairing, Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum,
    Multigraph.sum_laplacian_eq_zero, mul_zero]

omit [DecidableEq V] in
theorem pairing_eq_zero_of_eq_const {f : V → ℝ} {ϱ : V → ℤ} {c : ℝ} (hQ : ∑ j, ϱ j = 0)
    (h : ∀ j, ϱ j ≠ 0 → f j = c) : Multigraph.pairing f (fun j => (ϱ j : ℝ)) = 0 := by
  have hterm : ∀ j, f j * (ϱ j : ℝ) = c * (ϱ j : ℝ) := by
    intro j
    by_cases hj : ϱ j = 0
    · rw [hj, Int.cast_zero, mul_zero, mul_zero]
    · rw [h j hj]
  have hQ' : ∑ j, (ϱ j : ℝ) = 0 := by exact_mod_cast hQ
  rw [Multigraph.pairing, Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, hQ',
    mul_zero]

/--
The input `hfar` is the "in particular" of
P2.4(2), which follows from T2.2(b) (`notMem_densityDomain_of_scaleSeparated`).
-/
theorem spinWave_orthogonality (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (N₀ : Finset (V → ℤ)) (hneutral : ∀ ϱ ∈ N₀, ∑ j, ϱ j = 0) (centerOf : (V → ℤ) → V)
    (hcenter : ∀ ϱ ∈ N₀, G.IsDensityCenter ϱ (centerOf ϱ)) (a : (V → ℤ) → V → ℝ)
    (hconst : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ G.comparableDensities N₀ ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), a ϱ j = c)
    (hsupp : ∀ ϱ ∈ N₀, Function.support (a ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ))
    (hlap : ∀ ϱ ∈ N₀,
      Function.support (G.laplacian (a ϱ)) ⊆ G.densityDomain ϱ (centerOf ϱ))
    (hfar : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' → 2 * G.densityDiameter ϱ < G.densityDiameter ϱ' →
      ∀ x, ϱ' x ≠ 0 → x ∉ G.densityDomain ϱ (centerOf ϱ)) :
    (∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' → Multigraph.pairing (a ϱ) (fun j => (ϱ' j : ℝ)) = 0) ∧
      ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' → Multigraph.pairing (a ϱ) (G.laplacian (a ϱ')) = 0 := by
  -- `a_ϱ` is constant on `D⁺(ϱ')`, which contains `supp Δ a_{ϱ'}`, when `ϱ' ∈ 𝒩₀(ϱ)`.
  have hcomp : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' →
      G.densityDiameter ϱ' ≤ 2 * G.densityDiameter ϱ →
      Multigraph.pairing (a ϱ) (G.laplacian (a ϱ')) = 0 := by
    intro ϱ hϱ ϱ' hϱ' hne hle
    obtain ⟨c, hc⟩ := hconst ϱ hϱ ϱ' (G.mem_comparableDensities.mpr ⟨hϱ', hle, hne⟩)
    exact pairing_laplacian_eq_zero_of_eq_const G fun j hj =>
      hc j (G.densityDomain_subset_densityDomainPlus ϱ' _ (hlap ϱ' hϱ' hj))
  refine ⟨fun ϱ hϱ ϱ' hϱ' hne => ?_, fun ϱ hϱ ϱ' hϱ' hne => ?_⟩
  · by_cases hle : G.densityDiameter ϱ' ≤ 2 * G.densityDiameter ϱ
    · obtain ⟨c, hc⟩ := hconst ϱ hϱ ϱ' (G.mem_comparableDensities.mpr ⟨hϱ', hle, hne⟩)
      exact pairing_eq_zero_of_eq_const (hneutral ϱ' hϱ') fun j hj =>
        hc j (G.mem_densityDomainPlus_of_center hG (hneutral ϱ' hϱ') (hcenter ϱ' hϱ') hj)
    · have hzero : ∀ j, a ϱ j * (ϱ' j : ℝ) = 0 := by
        intro j
        by_cases hj : ϱ' j = 0
        · rw [hj, Int.cast_zero, mul_zero]
        · have hnot := hfar ϱ hϱ ϱ' hϱ' hne (not_le.mp hle) j hj
          have ha : a ϱ j = 0 := by
            by_contra ha
            exact hnot (hsupp ϱ hϱ ha)
          rw [ha, zero_mul]
      rw [Multigraph.pairing, Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero]
  · by_cases hle : G.densityDiameter ϱ' ≤ 2 * G.densityDiameter ϱ
    · exact hcomp ϱ hϱ ϱ' hϱ' hne hle
    · rw [Multigraph.pairing_laplacian_comm, Multigraph.pairing_comm]
      exact hcomp ϱ' hϱ' ϱ hϱ (Ne.symm hne) (by omega)

end Orthogonality

/-! ## The assembly on one domain -/

/--
The body of the KP Theorem 1.6 on one square domain `Λ` (the `step` of
`t16Statement`), with the constants `β₀, c₁`.
-/
def T16Step (Γ η θ β₀ c₁ : ℝ) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected) : Prop :=
  ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
    ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
    ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
      (z : Fin n → (Fin L × Fin L → ℤ) → ℝ)
      (ϱbar : Fin n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
      (∀ σ : Fin L × Fin L → ℝ,
        ∫ φ, ∏ j, lam j (φ j + σ j) ∂(gffLaw Λ hΛ β hβ v) =
          ∑ i, c i * ∫ φ, ∏ ϱ ∈ N i,
            (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j))
              ∂(gffLaw Λ hΛ β hβ v)) ∧
      ∀ i,
        (∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
        (∀ ϱ ∈ N i, |z i ϱ| ≤ Real.exp (-(c₁ / β) *
          (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)))) ∧
        ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
          Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
          Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
          ∀ j₁ j₂ : Fin L × Fin L, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
            Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅

/-- KP §2.3 on one square domain: T2.2, P2.1 and P2.4 for the boundary condition of `Λ`, with the
damping constants of `exists_damping_constants`, give the T1.6 step on `Λ`. -/
theorem t16Step_of (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    {Γ η θ D₁ D₂ D₃ β₀ c₁ : ℝ}
    (hdamp : ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s → A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 Γ) + 1 + η + θ / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ))
    (h22 : T22Step boundary L D₂) (h21 : P21Step boundary L D₁)
    (h24 : P24Step boundary Λ D₃) : T16Step Γ η θ β₀ c₁ Λ hΛ := by
  classical
  intro v β hβ hββ₀ lam hlam
  -- The Fourier data of the sub-Gaussian site weights (KP Definition 1.4).
  choose Nq hNq lamHat hzero hform hbound using hlam
  -- KP Theorem 2.2.
  obtain ⟨n, N, c, K, hens, hc, hcsum, hid, hbr⟩ := h22 lam Nq lamHat hNq hzero hform
  -- One admissible center for every density (KP p. 5), and the P2.4 cover selection.
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → Λ.IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨v, fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := Λ.exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  obtain ⟨cover, hcov⟩ := h24 centerOf hcenter
  -- KP Proposition 2.4 on every branch.
  have hwave := fun i : Fin n =>
    hcov β hβ (N i) (hens i) (hbr i).1 (hbr i).2.1 (hbr i).2.2.1
  choose! a ha using hwave
  -- Facts about the neutral part of a branch.
  have hmem : ∀ i, ∀ ϱ ∈ neutralPart (N i), ϱ ∈ N i ∧ ∑ j, ϱ j = 0 :=
    fun i ϱ hϱ => mem_neutralPart.mp hϱ
  have hne0 : ∀ i, ∀ ϱ ∈ neutralPart (N i), ϱ ≠ 0 :=
    fun i ϱ hϱ => (hens i).1 ϱ (hmem i ϱ hϱ).1
  have horth : ∀ i, _ := fun i => spinWave_orthogonality Λ hΛ (neutralPart (N i))
    (fun ϱ hϱ => (hmem i ϱ hϱ).2) centerOf (fun ϱ hϱ => hcenter ϱ (hne0 i ϱ hϱ)) (a i)
    (fun ϱ hϱ => (ha i ϱ hϱ).1) (fun ϱ hϱ => (ha i ϱ hϱ).2.1) (fun ϱ hϱ => (ha i ϱ hϱ).2.2.1)
    (fun ϱ hϱ ϱ' hϱ' hne hlt x hx =>
      notMem_densityDomain_of_scaleSeparated boundary Λ hΛ hdist (hne0 i ϱ hϱ)
        (hmem i ϱ hϱ).2 ((hbr i).2.1.1 ϱ (hmem i ϱ hϱ).1 ϱ' (hmem i ϱ' hϱ').1 hne) hlt
        (hcenter ϱ (hne0 i ϱ hϱ)) hx)
  refine ⟨n, fun i => neutralPart (N i), c,
    fun i ϱ => K i ϱ * Real.exp (-SpinWaves.energyFunctional Λ β (a i ϱ) ϱ),
    fun i ϱ j => (ϱ j : ℝ) + β * Λ.laplacian (a i ϱ) j,
    fun i => (hens i).neutralPart, hc, hcsum, ?_, ?_⟩
  · -- (1.13): expansion, Step 1 and Step 3.
    intro σ
    have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
    have hpt : ∀ φ : Fin L × Fin L → ℝ, ∏ j, lam j (φ j + σ j) =
        ∑ i, c i * ∏ ϱ ∈ N i,
          (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) := by
      intro φ
      have h := hid (φ + σ)
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib] at h
      exact h
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => (integrable_prod_one_add_mul_cos _ (N i) (K i)
      (fun ϱ φ => ∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))
      (fun ϱ => by fun_prop)).const_mul (c i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul,
      gffLaw_integral_prod_shift_eq_neutralPart Λ hΛ β hβ v (N i) (hbr i).1 (K i) σ,
      gffLaw_integral_prod_spinWave_translation_finset Λ hΛ β hβ v (neutralPart (N i))
        (fun ϱ hϱ => (hmem i ϱ hϱ).2) (K i) σ (a i) (horth i).1 (horth i).2]
  · intro i
    refine ⟨fun ϱ hϱ => (hmem i ϱ hϱ).2, fun ϱ hϱ => ?_, ?_⟩
    · -- (1.14), Step 4.
      obtain ⟨hϱN, hQ⟩ := hmem i ϱ hϱ
      have hϱ0 := hne0 i ϱ hϱ
      obtain ⟨hℓA, hAS⟩ := h21 cover ϱ hϱ0
      rw [chargeDiameter_eq_densityDiameter boundary Λ hdist] at hℓA
      have hK := (hbr i).2.2.2 ϱ hϱN hQ
      have hP := prod_exp_sq_mul_abs_le ϱ lamHat Γ (η + θ / β) (fun j q hq => hbound j q hq)
      have hE := (ha i ϱ hϱ).2.2.2
      have hS₀ : (squareCoverNumber boundary L 0 ϱ : ℝ) ≤ ∑ j, (ϱ j : ℝ) ^ 2 :=
        (Nat.cast_le.mpr (squareCoverNumber_zero_le_card boundary L ϱ)).trans
          (card_chargeSupport_le_sum_sq ϱ)
      have hd0 : (0 : ℝ) ≤ Λ.densityDiameter ϱ := Nat.cast_nonneg _
      have hℓ : 0 ≤ Real.logb 2 ((Λ.densityDiameter ϱ : ℝ) + 1) :=
        Real.logb_nonneg (by norm_num) (by linarith)
      have hX := hdamp β hβ hββ₀ (∑ j, (ϱ j : ℝ) ^ 2)
        (separatedSquareTotal boundary L cover ϱ) (chargeCoverCost boundary L ϱ)
        (Real.logb 2 ((Λ.densityDiameter ϱ : ℝ) + 1)) (squareCoverNumber boundary L 0 ϱ)
        (Finset.sum_nonneg fun j _ => sq_nonneg _) (Nat.cast_nonneg _) hℓ hℓA hS₀ hAS
      rw [abs_mul, Real.abs_exp]
      calc |K i ϱ| * Real.exp (-SpinWaves.energyFunctional Λ β (a i ϱ) ϱ)
          ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
              Real.exp ((Real.log (max 1 Γ) + 1 + (η + θ / β)) * ∑ j, (ϱ j : ℝ) ^ 2) *
            Real.exp (-(1 / β * (1 / 16 * ∑ j, (ϱ j : ℝ) ^ 2 +
              D₃ * separatedSquareTotal boundary L cover ϱ))) := by
            gcongr
            exact hK.trans (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le)
        _ = Real.exp (D₂ * chargeCoverCost boundary L ϱ +
              (Real.log (max 1 Γ) + 1 + η + θ / β) * ∑ j, (ϱ j : ℝ) ^ 2 -
              1 / β * (1 / 16 * ∑ j, (ϱ j : ℝ) ^ 2 +
                D₃ * separatedSquareTotal boundary L cover ϱ)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            ring_nf
        _ ≤ _ := Real.exp_le_exp.mpr hX
    · -- Property 3: disjoint domains in one band.
      intro ϱ₁ hϱ₁ ϱ₂ hϱ₂ hne k hk h₁ h₂ j₁ j₂ hj₁ hj₂
      exact densityDomain_inter_eq_empty boundary Λ hΛ hdist
        ((hbr i).2.1.1 ϱ₁ (hmem i ϱ₁ hϱ₁).1 ϱ₂ (hmem i ϱ₂ hϱ₂).1 hne) hk h₁ h₂ hj₁ hj₂

/-! ## KP Theorem 1.6 -/

/--
**KP Theorem 1.6 from Theorem 2.2, Proposition 2.4 and Proposition 2.1** (KP §2.3,
pp. 10–14).

The conclusion is `t16Statement`, the statement of the
`weightedGFF_renormalization`.
-/
theorem t16_of_t22_p24 : t22Statement → p24Statement → p21Statement → t16Statement := by
  rintro ⟨D₂, hD₂, h22⟩ ⟨D₃, hD₃, h24⟩ ⟨D₁, hD₁, h21⟩ Γ _ η θ _ hθ
  obtain ⟨β₀, c₁, hβ₀, hc₁, hdamp⟩ := exists_damping_constants Γ η θ D₁ D₂ D₃ hθ hD₁ hD₂ hD₃
  refine ⟨β₀, c₁, hβ₀, hc₁, fun L hL => ?_⟩
  obtain ⟨h22f, h22p⟩ := h22 L hL
  obtain ⟨h21f, h21p⟩ := h21 L hL
  obtain ⟨h24f, h24p⟩ := h24 L hL
  exact ⟨t16Step_of .free (squareFree L) (squareFree_connected L hL) (fun _ _ => rfl) hdamp
      h22f h21f h24f,
    fun hEven => t16Step_of .periodic (squarePeriodic L) (squarePeriodic_connected L hL)
      (fun _ _ => rfl) hdamp (h22p hEven) (h21p hEven) (h24p hEven)⟩

end FroehlichSpencer.BKT.Reduction

end
