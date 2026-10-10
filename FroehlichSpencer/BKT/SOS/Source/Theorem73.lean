/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.Geometry
public import FroehlichSpencer.BKT.SOS.Roughening.Theorem73
public import FroehlichSpencer.BKT.SOS.Source.Carrier

/-! Full-parameter and deep-point forms of FS81 Theorem 7.3 for the pinned Dirichlet-box SOS law. -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Source

open MeasureTheory ENNReal Filter Topology
open FroehlichSpencer.BKT.Generic.PinnedCharges
  (Site siteBoundaryDepth euclideanSiteDistance)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

private theorem ennreal_ofReal_exp_rpow (x p : ℝ) (hp : 0 ≤ p) :
    ENNReal.ofReal (Real.exp x) ^ p = ENNReal.ofReal (Real.exp (p * x)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hp]
  congr 1
  rw [← Real.exp_mul x p]
  ring_nf

private theorem sosMomentExt_ge_interpolated (hL : 1 < L) {β β' : ℝ}
    (hβ : 0 < β) (hβ' : 0 < β') (u v : Site L) (ell : ℝ) (hell : 0 ≤ ell)
    (hbase : ENNReal.ofReal
        (Real.exp ((β / 2) ^ 2 / β' * ell)) ≤
      sosMomentExt hL hβ u v (β / 2))
    {s : ℝ} (hslo : β / 2 ≤ s) (hshi : s ≤ 4 * β) :
    ENNReal.ofReal (Real.exp (s ^ 2 / (8 * β') * ell)) ≤
      sosMomentExt hL hβ u v s := by
  have ha : 0 < β / 2 := by positivity
  have hs : 0 < s := lt_of_lt_of_le ha hslo
  let θ : ℝ := (β / 2) / s
  let p : ℝ := s / (β / 2)
  have hθ0 : 0 < θ := by dsimp [θ]; exact div_pos ha hs
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    rw [div_le_iff₀ hs]
    linarith
  have hp0 : 0 < p := by dsimp [p]; exact div_pos hs ha
  have hp_nonneg : 0 ≤ p := hp0.le
  have harg : (1 - θ) * 0 + θ * s = β / 2 := by
    simp only [mul_zero, zero_add]
    dsimp [θ]
    field_simp
  have hconv := sosMomentExt_log_convex hL hβ u v 0 s θ (by linarith) hθ1
  rw [harg, sosMomentExt_zero hL hβ u v] at hconv
  simp only [one_rpow, one_mul] at hconv
  have hlow : sosMomentExt hL hβ u v (β / 2) ≤
      (sosMomentExt hL hβ u v s) ^ θ := hconv
  have hpow := ENNReal.rpow_le_rpow (hbase.trans hlow) hp_nonneg
  rw [← ENNReal.rpow_mul] at hpow
  have hθp : θ * p = 1 := by
    dsimp [θ, p]
    field_simp
  rw [hθp, ENNReal.rpow_one] at hpow
  rw [ennreal_ofReal_exp_rpow _ _ hp_nonneg] at hpow
  have htemp : s ^ 2 ≤ 4 * s * β := by
    have hmul := mul_le_mul_of_nonneg_left hshi hs.le
    nlinarith
  have hcoef : s ^ 2 / (8 * β') ≤ s * β / (2 * β') := by
    calc
      s ^ 2 / (8 * β') ≤ (4 * s * β) / (8 * β') :=
        div_le_div_of_nonneg_right htemp (by positivity)
      _ = s * β / (2 * β') := by ring
  have hexp : s ^ 2 / (8 * β') * ell ≤ s * β / (2 * β') * ell :=
    mul_le_mul_of_nonneg_right hcoef hell
  have hcalc : p * ((β / 2) ^ 2 / β' * ell) = s * β / (2 * β') * ell := by
    dsimp [p]
    field_simp
  apply le_trans ?_ hpow
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [hcalc]
  exact hexp

/-- The full real-parameter (7.17) for the pinned Dirichlet square-box SOS model, interpreted as
an extended expectation. The interpolation range follows from log-convexity between zero and
`β/2`; at `|ε| ≥ 4β` the moment is infinite by a one-site height shift. The source explicitly
licenses the Dirichlet variant, while its printed state is the free-boundary comb. -/
theorem sos_theorem73_all_eps :
    ∃ (β₀ : ℝ) (β'' : ℝ → ℝ) (L₀ : {L : ℕ // 1 < L}), 0 < β₀ ∧
      Tendsto β'' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β (hβ : 0 < β), β ≤ β₀ → 0 < β'' β ∧
        ∀ L (hL₀ : L₀.val ≤ L), ∀ u v : Site L,
        (∀ ε : ℝ,
          ENNReal.ofReal (Real.exp (ε ^ 2 / β'' β *
            Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)))) ≤
              @sosMomentExt L (lt_of_lt_of_le L₀.property hL₀) β hβ u v ε) ∧
        Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) /
            (β'' β / 8) ≤ @sosVarianceIntegral L
              (lt_of_lt_of_le L₀.property hL₀) β hβ u v := by
  obtain ⟨β₀, β', Lold, hβ₀, hlim, hmain⟩ := sos_theorem73
  refine ⟨min β₀ 1, fun β => 8 * β' β,
    ⟨max Lold 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _)⟩,
    lt_min hβ₀ (by norm_num), ?_, ?_⟩
  · simpa using hlim.const_mul 8
  · intro β hβ hβnew
    have hβold : β ≤ β₀ := (le_min_iff.mp hβnew).1
    have hβ1 : β ≤ 1 := (le_min_iff.mp hβnew).2
    obtain ⟨hβ'pos, hforL⟩ := hmain β hβ hβold
    refine ⟨by positivity, fun L hL0 u v => ?_⟩
    change max Lold 2 ≤ L at hL0
    have hL : 1 < L := by omega
    have hLold : Lold ≤ L := le_trans (Nat.le_max_left Lold 2) hL0
    have hclaims := hforL L hLold u v
    let ell : ℝ := Real.log
      (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ))
    have hell : 0 ≤ ell := by
      dsimp [ell]
      apply Real.log_nonneg
      have hn : (0 : ℝ) ≤ (linfDist u v : ℝ) := Nat.cast_nonneg _
      have hd : (0 : ℝ) ≤ (siteBoundaryDepth u : ℝ) := Nat.cast_nonneg _
      have hm : (0 : ℝ) ≤ min (linfDist u v : ℝ) (siteBoundaryDepth u : ℝ) :=
        le_min hn hd
      linarith
    have hbase : ENNReal.ofReal (Real.exp ((β / 2) ^ 2 / β' β * ell)) ≤
        sosMomentExt hL hβ u v (β / 2) := by
      have hreal := hclaims.1 (β / 2) (by rw [abs_of_pos (by positivity)])
      have hmatch := sosMomentExt_matches_sosMoment hL hβ hβ1 u v (β / 2)
        (by rw [abs_of_pos (by positivity)])
      rw [hmatch]
      apply ENNReal.ofReal_le_ofReal
      simpa [ell] using hreal
    have hmoment : ∀ ε : ℝ,
        ENNReal.ofReal (Real.exp (ε ^ 2 / (8 * β' β) * ell)) ≤
          sosMomentExt hL hβ u v ε := by
      intro ε
      by_cases hsmall : |ε| ≤ β / 2
      · have hreal := hclaims.1 ε hsmall
        have hmatch := sosMomentExt_matches_sosMoment hL hβ hβ1 u v ε hsmall
        rw [hmatch]
        apply ENNReal.ofReal_le_ofReal
        have hden : 0 < β' β := hβ'pos
        have hdiv : ε ^ 2 / (8 * β' β) ≤ ε ^ 2 / β' β := by
          apply div_le_div_of_nonneg_left (sq_nonneg ε) hden
          nlinarith
        have hexp : ε ^ 2 / (8 * β' β) * ell ≤ ε ^ 2 / β' β * ell :=
          mul_le_mul_of_nonneg_right hdiv hell
        exact (Real.exp_le_exp.mpr hexp).trans (by simpa [ell] using hreal)
      · have hlo : β / 2 ≤ |ε| := le_of_not_ge hsmall
        by_cases hlarge : 4 * β ≤ |ε|
        · by_cases huv : u = v
          · subst v
            have hell0 : ell = 0 := by simp [ell, linfDist_self]
            rw [hell0, sosMomentExt_self hL hβ u ε]
            simp
          · have htop := sosMomentExt_eq_top_of_abs_ge_four_beta hL hβ u v huv hlarge
            rw [htop]
            exact le_top
        · have hhi : |ε| ≤ 4 * β := le_of_not_ge hlarge
          have hmid := sosMomentExt_ge_interpolated hL hβ hβ'pos u v ell hell hbase hlo hhi
          have heven : sosMomentExt hL hβ u v ε = sosMomentExt hL hβ u v |ε| := by
            by_cases hε0 : 0 ≤ ε
            · rw [abs_of_nonneg hε0]
            · rw [abs_of_neg (lt_of_not_ge hε0)]
              exact (sosMomentExt_even hL hβ u v ε).symm
          rw [heven]
          simpa [ell] using hmid
    have hvar : ell / β' β ≤ sosVariance L β u v := by
      simpa [ell] using hclaims.2
    refine ⟨?_, ?_⟩
    · intro ε
      simpa [ell] using hmoment ε
    · have hden : (8 * β' β) / 8 = β' β := by ring
      rw [hden, sosVarianceIntegral_eq_sosVariance hL hβ u v]
      simpa [ell] using hvar

/-- The full-`ε` theorem at points at least their separation from the boundary. -/
theorem sos_theorem73_all_eps_deep :
    ∃ (β₀ : ℝ) (β'' : ℝ → ℝ) (L₀ : {L : ℕ // 1 < L}), 0 < β₀ ∧
      Tendsto β'' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β (hβ : 0 < β), β ≤ β₀ → 0 < β'' β ∧
        ∀ L (hL₀ : L₀.val ≤ L), ∀ u v : Site L,
        linfDist u v ≤ siteBoundaryDepth u →
        (∀ ε : ℝ,
          ENNReal.ofReal (Real.exp (ε ^ 2 / β'' β * Real.log (1 + (linfDist u v : ℝ)))) ≤
            @sosMomentExt L (lt_of_lt_of_le L₀.property hL₀) β hβ u v ε) ∧
        Real.log (1 + (linfDist u v : ℝ)) / (β'' β / 8) ≤
          @sosVarianceIntegral L (lt_of_lt_of_le L₀.property hL₀) β hβ u v := by
  obtain ⟨β₀, β'', L₀, hβ₀, hlim, hmain⟩ := sos_theorem73_all_eps
  refine ⟨β₀, β'', L₀, hβ₀, hlim, fun β hβ hββ₀ =>
    ⟨(hmain β hβ hββ₀).1, fun L hL₀ u v hdeep => ?_⟩⟩
  have h := (hmain β hβ hββ₀).2 L hL₀ u v
  rw [min_eq_left hdeep] at h
  simpa using h

private theorem euclideanSiteDistance_le_two_linfDist (x y : Site L) :
    euclideanSiteDistance x y ≤ 2 * (linfDist x y : ℝ) := by
  let dx : ℝ := (x.1.val : ℝ) - y.1.val
  let dy : ℝ := (x.2.val : ℝ) - y.2.val
  let d : ℝ := linfDist x y
  have hcastX :
      ((Int.natAbs ((x.1.val : ℤ) - y.1.val) : ℕ) : ℝ) = |dx| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    simp [dx]
  have hcastY :
      ((Int.natAbs ((x.2.val : ℤ) - y.2.val) : ℕ) : ℝ) = |dy| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    simp [dy]
  have hdx : |dx| ≤ d := by
    dsimp [d, linfDist]
    rw [← hcastX]
    exact_mod_cast (Nat.le_max_left _ _)
  have hdy : |dy| ≤ d := by
    dsimp [d, linfDist]
    rw [← hcastY]
    exact_mod_cast (Nat.le_max_right _ _)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hsq : dx ^ 2 + dy ^ 2 ≤ (2 * d) ^ 2 := by
    nlinarith [sq_nonneg (d - |dx|), sq_nonneg (d - |dy|), sq_abs dx, sq_abs dy]
  have hroot := Real.sqrt_le_sqrt hsq
  have hdist : euclideanSiteDistance x y = Real.sqrt (dx ^ 2 + dy ^ 2) := by
    simp [euclideanSiteDistance, dx, dy]
  rw [hdist]
  calc
    Real.sqrt (dx ^ 2 + dy ^ 2) ≤ Real.sqrt ((2 * d) ^ 2) := hroot
    _ = 2 * d := Real.sqrt_sq (by positivity)
    _ = 2 * (linfDist x y : ℝ) := by rfl

private theorem linfDist_le_euclideanSiteDistance (x y : Site L) :
    (linfDist x y : ℝ) ≤ euclideanSiteDistance x y := by
  let dx : ℝ := (x.1.val : ℝ) - y.1.val
  let dy : ℝ := (x.2.val : ℝ) - y.2.val
  have hcastX :
      ((Int.natAbs ((x.1.val : ℤ) - y.1.val) : ℕ) : ℝ) = |dx| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    simp [dx]
  have hcastY :
      ((Int.natAbs ((x.2.val : ℤ) - y.2.val) : ℕ) : ℝ) = |dy| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    simp [dy]
  have hdx : |dx| ≤ euclideanSiteDistance x y := by
    rw [euclideanSiteDistance]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg dy, sq_abs dx]
  have hdy : |dy| ≤ euclideanSiteDistance x y := by
    rw [euclideanSiteDistance]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg dx, sq_abs dy]
  have hdx' :
      ((Int.natAbs ((x.1.val : ℤ) - y.1.val) : ℕ) : ℝ) ≤
        euclideanSiteDistance x y := by rw [hcastX]; exact hdx
  have hdy' :
      ((Int.natAbs ((x.2.val : ℤ) - y.2.val) : ℕ) : ℝ) ≤
        euclideanSiteDistance x y := by rw [hcastY]; exact hdy
  change ((max (Int.natAbs ((x.1.val : ℤ) - y.1.val))
      (Int.natAbs ((x.2.val : ℤ) - y.2.val)) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max]
  exact max_le_iff.mpr ⟨hdx', hdy'⟩

private theorem log_one_add_euclidean_le_two_linf (x y : Site L) :
    Real.log (1 + euclideanSiteDistance x y) ≤
      2 * Real.log (1 + (linfDist x y : ℝ)) := by
  have hd : (0 : ℝ) ≤ (linfDist x y : ℝ) := Nat.cast_nonneg _
  have he : euclideanSiteDistance x y ≤ 2 * (linfDist x y : ℝ) :=
    euclideanSiteDistance_le_two_linfDist x y
  have hbase : 0 < 1 + (linfDist x y : ℝ) := by linarith
  have hepos : 0 < 1 + euclideanSiteDistance x y := by
    unfold euclideanSiteDistance
    positivity
  have harg : 1 + euclideanSiteDistance x y ≤ (1 + (linfDist x y : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (linfDist x y : ℝ)]
  calc
    Real.log (1 + euclideanSiteDistance x y) ≤
        Real.log ((1 + (linfDist x y : ℝ)) ^ 2) :=
      Real.log_le_log hepos harg
    _ = 2 * Real.log (1 + (linfDist x y : ℝ)) := by rw [Real.log_pow]; norm_num

/-- Euclidean deep-point form of the all-ε estimate. Its coefficient is doubled because
`log (1 + |x|₂) ≤ 2 log (1 + |x|∞)`. -/
theorem sos_theorem73_all_eps_euclidean_deep :
    ∃ (β₀ : ℝ) (β'' : ℝ → ℝ) (L₀ : {L : ℕ // 1 < L}), 0 < β₀ ∧
      Tendsto β'' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β (hβ : 0 < β), β ≤ β₀ → 0 < β'' β ∧
        ∀ L (hL₀ : L₀.val ≤ L), ∀ u v : Site L,
          euclideanSiteDistance u v ≤ siteBoundaryDepth u →
          (∀ ε : ℝ,
            ENNReal.ofReal (Real.exp (ε ^ 2 / (2 * β'' β) *
              Real.log (1 + euclideanSiteDistance u v))) ≤
                @sosMomentExt L (lt_of_lt_of_le L₀.property hL₀) β hβ u v ε) ∧
          Real.log (1 + euclideanSiteDistance u v) / (2 * β'' β) ≤
            @sosVarianceIntegral L (lt_of_lt_of_le L₀.property hL₀) β hβ u v := by
  obtain ⟨β₀, β'', L₀, hβ₀, hlim, hmain⟩ := sos_theorem73_all_eps
  refine ⟨β₀, β'', L₀, hβ₀, hlim, fun β hβ hββ₀ =>
    ⟨(hmain β hβ hββ₀).1, fun L hL₀ u v hdeep => ?_⟩⟩
  have hlinfdeep : linfDist u v ≤ siteBoundaryDepth u := by
    have hle := linfDist_le_euclideanSiteDistance u v
    exact_mod_cast hle.trans hdeep
  have hraw := (hmain β hβ hββ₀).2 L hL₀ u v
  have hclaims := hraw
  rw [min_eq_left hlinfdeep] at hclaims
  have hlog := log_one_add_euclidean_le_two_linf u v
  have hβ'' : 0 < β'' β := (hmain β hβ hββ₀).1
  have hvar : Real.log (1 + euclideanSiteDistance u v) / (2 * β'' β) ≤
      Real.log (1 + (linfDist u v : ℝ)) / β'' β := by
    calc
      Real.log (1 + euclideanSiteDistance u v) / (2 * β'' β) ≤
          (2 * Real.log (1 + (linfDist u v : ℝ))) / (2 * β'' β) :=
        div_le_div_of_nonneg_right hlog (by positivity)
      _ = Real.log (1 + (linfDist u v : ℝ)) / β'' β := by ring
  have hlogN : 0 ≤ Real.log (1 + (linfDist u v : ℝ)) := by
    apply Real.log_nonneg
    have hd : (0 : ℝ) ≤ (linfDist u v : ℝ) := Nat.cast_nonneg _
    linarith
  have hvar' : Real.log (1 + (linfDist u v : ℝ)) / β'' β ≤
      Real.log (1 + (linfDist u v : ℝ)) / (β'' β / 8) := by
    apply div_le_div_of_nonneg_left hlogN (by positivity)
    nlinarith
  refine ⟨?_, hvar.trans (hvar'.trans hclaims.2)⟩
  intro ε
  have hexp : ε ^ 2 / (2 * β'' β) * Real.log (1 + euclideanSiteDistance u v) ≤
      ε ^ 2 / β'' β * Real.log (1 + (linfDist u v : ℝ)) := by
    calc
      ε ^ 2 / (2 * β'' β) * Real.log (1 + euclideanSiteDistance u v) ≤
          ε ^ 2 / (2 * β'' β) * (2 * Real.log (1 + (linfDist u v : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = ε ^ 2 / β'' β * Real.log (1 + (linfDist u v : ℝ)) := by ring
  apply le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
  exact hclaims.1 ε

end FroehlichSpencer.BKT.SOS.Source

end
