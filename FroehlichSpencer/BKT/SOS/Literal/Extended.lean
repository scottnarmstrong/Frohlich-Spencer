/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Divergence
public import FroehlichSpencer.BKT.SOS.Literal.Plane

/-!
# FS81 (7.17) for every `ε`, in the extended sense (the finite comb construction)

FS81 print (7.17) with an unrestricted `ε` (FS81). In the literal state the moment
`⟨e^{ε[φ(u)−φ(v)]}⟩` is the `[0, ∞]`-valued lintegral `literalMomentExt`; it is even in `ε`
(`literalMomentExt_neg`), log-convex (`mgfExt_le_rpow_mul_rpow`), and `∞` for `u ≠ v` and
`|ε| ≥ 4β` (`literalMomentExt_eq_top`). From the window `|ε| ≤ β/2` this gives the bound for every
`ε` with `β'' = 8β'` (`literalMomentExt_ge_all`, via `le_mgfExt_of_window`).

* `literal_theorem73_ext`, `literal_theorem73_deep_ext`: the box forms of `Literal/Theorem73.lean`
  for every `ε`.
* `literal_theorem73_plane_ext`: every finite `A ⊂ ℤ²`, all `u, v ∈ A`, every large box around `A`,
  every `ε`, with `|x| = ‖u − v‖_∞`.
* `literal_theorem73_plane_euclid`: the same with the Euclidean `|x|`, after doubling `β''`
  (`log(1 + ‖x‖₂) ≤ 2 log(1 + ‖x‖_∞)`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

theorem literalMomentExt_eq_mgfExt (β : ℝ) (A : Finset (Site L)) (u v : Site L) (ε : ℝ) :
    literalMomentExt L β A u v ε = mgfExt (literalState L β A) (fun φ => φ u - φ v) ε := rfl

theorem literalMomentExt_self (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) (u : Site L) (ε : ℝ) : literalMomentExt L β A u u ε = 1 := by
  have := isProbabilityMeasure_literalState hL hβ hβ1 A
  simp [literalMomentExt]

/-- **From the window `|ε| ≤ β/2` to every `ε`**, with the constant divided by `8`. -/
theorem literalMomentExt_ge_all (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (Site L)} {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) {a : ℝ} (ha : 0 ≤ a)
    (hlow : ∀ ε : ℝ, |ε| ≤ β / 2 →
      ENNReal.ofReal (Real.exp (a * ε ^ 2)) ≤ literalMomentExt L β A u v ε) (ε : ℝ) :
    ENNReal.ofReal (Real.exp (a / 8 * ε ^ 2)) ≤ literalMomentExt L β A u v ε := by
  have := isProbabilityMeasure_literalState hL hβ hβ1 A
  by_cases huv : u = v
  · subst huv
    have hβ2 : 0 < β / 2 := by positivity
    have h := hlow (β / 2) (by rw [abs_of_pos hβ2])
    rw [literalMomentExt_self hL hβ hβ1 A u, ENNReal.ofReal_le_one, Real.exp_le_one_iff] at h
    have ha0 : a = 0 := by
      refine le_antisymm ?_ ha
      by_contra hc
      have := mul_pos (lt_of_not_ge hc) (pow_pos hβ2 2)
      linarith
    rw [literalMomentExt_self hL hβ hβ1 A u, ha0, zero_div, zero_mul, Real.exp_zero,
      ENNReal.ofReal_one]
  · exact le_mgfExt_of_window (literalState L β A) (X := fun φ => φ u - φ v)
      ((continuous_apply u).sub (continuous_apply v)).measurable ha (by positivity : 0 < β / 2)
      (literalMomentExt_neg hβ.le hu hv) hlow
      (fun ε hε => literalMomentExt_eq_top hL hβ hβ1 hu hv huv (by linarith)) ε

/-- **FS81 Theorem 7.3 in the literal state, for every `ε`**, for every region `A` of every large
box: (7.17) in `[0, ∞]` for all `ε` and (7.18), with `ℓ = log(1 + min(‖u − v‖_∞, depth_Ω(u)))`. -/
theorem literal_theorem73_ext :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧ β₀ ≤ 1 ∧ 1 < L₀ ∧
      Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ L, L₀ ≤ L → ∀ (A : Finset (Site L)) (u v : Site L),
        u ∈ A → v ∈ A →
        (∀ ε : ℝ,
          ENNReal.ofReal (Real.exp (ε ^ 2 / β' β *
            Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)))) ≤
            literalMomentExt L β A u v ε) ∧
        Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) / β' β ≤
          literalVariance L β A u v := by
  obtain ⟨β₀, β', L₀, hβ₀, hβ₀1, hL₀, hlim, h⟩ := literal_theorem73
  refine ⟨β₀, fun β => 8 * β' β, L₀, hβ₀, hβ₀1, hL₀, by simpa using hlim.const_mul 8,
    fun β hβ hββ₀ => ?_⟩
  obtain ⟨hβ'pos, h'⟩ := h β hβ hββ₀
  refine ⟨mul_pos (by norm_num) hβ'pos, fun L hL A u v hu hv => ?_⟩
  beta_reduce
  obtain ⟨hmom, hvar⟩ := h' L hL A u v hu hv
  have hL1 : 1 < L := lt_of_lt_of_le hL₀ hL
  have hβ1 : β ≤ 1 := hββ₀.trans hβ₀1
  set ℓ := Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (min (linfDist u v) (siteBoundaryDepth u)); linarith)
  refine ⟨fun ε => ?_, le_trans (div_le_div_of_nonneg_left hℓ0 hβ'pos (by linarith)) hvar⟩
  have hall := literalMomentExt_ge_all hL1 hβ hβ1 hu hv (a := ℓ / β' β)
    (div_nonneg hℓ0 hβ'pos.le) (fun ε hε => by
      have := hmom ε hε
      rwa [show ε ^ 2 / β' β * ℓ = ℓ / β' β * ε ^ 2 by ring] at this) ε
  rwa [show ℓ / β' β / 8 * ε ^ 2 = ε ^ 2 / (8 * β' β) * ℓ by ring] at hall

/-- **FS81 Theorem 7.3 in the literal state for every `ε`, away from the outside of `Ω`**. -/
theorem literal_theorem73_deep_ext :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧ β₀ ≤ 1 ∧ 1 < L₀ ∧
      Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ L, L₀ ≤ L → ∀ (A : Finset (Site L)) (u v : Site L),
        u ∈ A → v ∈ A → linfDist u v ≤ siteBoundaryDepth u →
        (∀ ε : ℝ,
          ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + (linfDist u v : ℝ)))) ≤
            literalMomentExt L β A u v ε) ∧
        Real.log (1 + (linfDist u v : ℝ)) / β' β ≤ literalVariance L β A u v := by
  obtain ⟨β₀, β', L₀, hβ₀, hβ₀1, hL₀, hlim, h⟩ := literal_theorem73_ext
  refine ⟨β₀, β', L₀, hβ₀, hβ₀1, hL₀, hlim, fun β hβ hββ₀ =>
    ⟨(h β hβ hββ₀).1, fun L hL A u v hu hv huv => ?_⟩⟩
  have h' := (h β hβ hββ₀).2 L hL A u v hu hv
  rw [min_eq_left huv] at h'
  exact h'

/-- **FS81 Theorem 7.3 for an arbitrary finite region of the plane, for every `ε`**, in the
literal state on every large box around it (`|x| = ‖u − v‖_∞`). -/
theorem literal_theorem73_plane_ext :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), 0 < β₀ ∧ β₀ ≤ 1 ∧ Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ (A : Finset (ℤ × ℤ)) (u v : ℤ × ℤ), u ∈ A → v ∈ A →
        ∃ L_A : ℕ, ∀ L, L_A ≤ L →
          (∀ ε : ℝ,
            ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + (planeLinf u v : ℝ)))) ≤
              literalMomentExt (L + 1) β (centeredRegion L A) (centeredSite L u)
                (centeredSite L v) ε) ∧
          Real.log (1 + (planeLinf u v : ℝ)) / β' β ≤
            literalVariance (L + 1) β (centeredRegion L A) (centeredSite L u)
              (centeredSite L v) := by
  obtain ⟨β₀, β', L₀, hβ₀, hβ₀1, -, hlim, h⟩ := literal_theorem73_deep_ext
  refine ⟨β₀, β', hβ₀, hβ₀1, hlim, fun β hβ hββ₀ => ⟨(h β hβ hββ₀).1, fun A u v hu hv => ?_⟩⟩
  set R := planeRadius A
  refine ⟨max L₀ (6 * R + 1), fun L hL => ?_⟩
  obtain ⟨hu1, hu2⟩ := coord_le_planeRadius hu
  obtain ⟨hv1, hv2⟩ := coord_le_planeRadius hv
  have hL6 : 6 * R + 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlinf := linfDist_centeredSite (by omega : 2 * R + 1 ≤ L) hu1 hu2 hv1 hv2
  have h' := (h β hβ hββ₀).2 (L + 1) (by have := le_max_left L₀ (6 * R + 1); omega)
    (centeredRegion L A) (centeredSite L u) (centeredSite L v) (Finset.mem_image_of_mem _ hu)
    (Finset.mem_image_of_mem _ hv) (hlinf ▸ planeLinf_le_depth hL6 hu1 hu2 hv1 hv2)
  rw [hlinf] at h'
  exact h'

/-! ## The Euclidean distance -/

/-- The Euclidean distance of plane sites. -/
def planeDist (u v : ℤ × ℤ) : ℝ :=
  Real.sqrt (((u.1 - v.1 : ℤ) : ℝ) ^ 2 + ((u.2 - v.2 : ℤ) : ℝ) ^ 2)

theorem abs_intCast_le_planeLinf_left (u v : ℤ × ℤ) :
    |((u.1 - v.1 : ℤ) : ℝ)| ≤ (planeLinf u v : ℝ) := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  exact_mod_cast le_max_left _ _

theorem abs_intCast_le_planeLinf_right (u v : ℤ × ℤ) :
    |((u.2 - v.2 : ℤ) : ℝ)| ≤ (planeLinf u v : ℝ) := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  exact_mod_cast le_max_right _ _

/-- `log(1 + ‖x‖₂) ≤ 2 log(1 + ‖x‖_∞)`. -/
theorem log_one_add_planeDist_le (u v : ℤ × ℤ) :
    Real.log (1 + planeDist u v) ≤ 2 * Real.log (1 + (planeLinf u v : ℝ)) := by
  set a : ℝ := ((u.1 - v.1 : ℤ) : ℝ)
  set b : ℝ := ((u.2 - v.2 : ℤ) : ℝ)
  set t : ℝ := (planeLinf u v : ℝ)
  have ha := abs_intCast_le_planeLinf_left u v
  have hb := abs_intCast_le_planeLinf_right u v
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hd : planeDist u v ≤ |a| + |b| := by
    unfold planeDist
    rw [← Real.sqrt_sq (add_nonneg (abs_nonneg a) (abs_nonneg b))]
    refine Real.sqrt_le_sqrt ?_
    have hab : 0 ≤ |a| * |b| := mul_nonneg (abs_nonneg a) (abs_nonneg b)
    have h2 : (|a| + |b|) ^ 2 = a ^ 2 + b ^ 2 + 2 * (|a| * |b|) := by
      rw [add_sq, sq_abs, sq_abs]
      ring
    rw [h2]
    linarith
  have hpos : 0 < 1 + planeDist u v := by
    have : 0 ≤ planeDist u v := Real.sqrt_nonneg _
    linarith
  rw [← Real.log_rpow (by linarith : (0 : ℝ) < 1 + t)]
  refine Real.log_le_log hpos ?_
  rw [show ((1 + t) ^ (2 : ℝ)) = (1 + t) ^ (2 : ℕ) by norm_cast]
  nlinarith

/-- **FS81 Theorem 7.3 for an arbitrary finite region of the plane, for every `ε`, with the
Euclidean `|x|`**. -/
theorem literal_theorem73_plane_euclid :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), 0 < β₀ ∧ β₀ ≤ 1 ∧ Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ (A : Finset (ℤ × ℤ)) (u v : ℤ × ℤ), u ∈ A → v ∈ A →
        ∃ L_A : ℕ, ∀ L, L_A ≤ L →
          (∀ ε : ℝ,
            ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + planeDist u v))) ≤
              literalMomentExt (L + 1) β (centeredRegion L A) (centeredSite L u)
                (centeredSite L v) ε) ∧
          Real.log (1 + planeDist u v) / β' β ≤
            literalVariance (L + 1) β (centeredRegion L A) (centeredSite L u)
              (centeredSite L v) := by
  obtain ⟨β₀, β', hβ₀, hβ₀1, hlim, h⟩ := literal_theorem73_plane_ext
  refine ⟨β₀, fun β => 2 * β' β, hβ₀, hβ₀1, by simpa using hlim.const_mul 2,
    fun β hβ hββ₀ => ?_⟩
  obtain ⟨hβ'pos, h'⟩ := h β hβ hββ₀
  refine ⟨mul_pos (by norm_num) hβ'pos, fun A u v hu hv => ?_⟩
  obtain ⟨L_A, hA⟩ := h' A u v hu hv
  refine ⟨L_A, fun L hL => ?_⟩
  beta_reduce
  obtain ⟨hmom, hvar⟩ := hA L hL
  have hlog := log_one_add_planeDist_le u v
  have hkey : Real.log (1 + planeDist u v) / (2 * β' β) ≤
      Real.log (1 + (planeLinf u v : ℝ)) / β' β := by
    rw [div_le_div_iff₀ (by positivity) hβ'pos]
    nlinarith
  refine ⟨fun ε => le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) (hmom ε),
    hkey.trans hvar⟩
  have h1 : ε ^ 2 / (2 * β' β) * Real.log (1 + planeDist u v) =
      ε ^ 2 * (Real.log (1 + planeDist u v) / (2 * β' β)) := by ring
  have h2 : ε ^ 2 / β' β * Real.log (1 + (planeLinf u v : ℝ)) =
      ε ^ 2 * (Real.log (1 + (planeLinf u v : ℝ)) / β' β) := by ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hkey (sq_nonneg ε)

end FroehlichSpencer.BKT.SOS.Literal

end
