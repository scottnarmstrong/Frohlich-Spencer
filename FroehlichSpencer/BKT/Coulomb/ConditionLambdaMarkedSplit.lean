/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Domain
import Mathlib.Tactic

/-!
# The split marked cluster estimate

`cluster_estimate` (`Generic/Marked/Domain.lean`) charges the activity growth `e^{h‖ϱ‖²}` against
the marked mass `‖ξ(δ_o − δ_x) + ϱ^𝒩‖² ≥ (η²/2)(|X| + Σ)` (`sum_markedDensity_sq_ge`). So its
condition (H1) `β(h + 1) + c ≤ η²/32` pays a Condition-λ growth `h ∋ θ/β` at the fractional rate
`η²`. That forces `θ < η²/32` (the marked-cluster estimate: `θ < η²/128`).

This module splits the composite self-energy instead:
* `sum_markedDensity_sq_ge_sub`: `‖ξ(δ_o − δ_x) + s‖² ≥ ‖s‖² − 2(|s(o)| + |s(x)|)`. The marked
  mass loses only at the two marked sites.
* `split_defect_le`: with `θ + δ = 1/16`, the growth `θΣ` against `(θ + δ/2)(Σ − 2(|a| + |b|))`
  leaves at most `1/(64δ)`.
* `split_gain_le`, `split_exponent_le`: the algebra of `Q/16 = 8δ·Q/16 + (θ + δ/2)·Q`.
  - The first part keeps the marked bookkeeping of `cluster_estimate` with `η²` replaced by `8δη²`.
  - The second part pays `θ/β` with the integer self-energy, as in FS81 Theorem 5.3.
* `cluster_orientationSum_le_split`, **`cluster_estimate_split`**: for activities
  `e^{(h₀ + θ/β)‖ϱ‖²}` with `θ ≥ 0`, `θ + δ = 1/16`, the branch bound of a neutral cluster is at
  most `2 e^{1/(64δβ)} e^{−(8δη²/(16384 D₁ β)) log₂(|o − x| + 1)}` times its exploration weight.
  The conditions (H1)–(H4) no longer contain `θ`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Reduction FroehlichSpencer.BKT.Generic.Marked

/-! ### The mass of the marked composite, site by site -/

section Mass

variable {L : ℕ}

/-- **The marked mass loses only at the two marked sites**: for `0 ≤ ξ ≤ 1` and any integer
satellite `s`, `‖ξ(δ_o − δ_x) + s‖² ≥ ‖s‖² − 2(|s(o)| + |s(x)|)`. Off `{o, x}` the marked charge is
the integer charge itself, so the full self-energy of the satellite survives there. -/
theorem sum_markedDensity_sq_ge_sub (o x : Fin L × Fin L) {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (s : ChargeDensity L) :
    ∑ j, ((s j : ℤ) : ℝ) ^ 2 - 2 * (|((s o : ℤ) : ℝ)| + |((s x : ℤ) : ℝ)|) ≤
      ∑ j, markedDensity ξ (dipoleMark o x) s j ^ 2 := by
  have hsite : ∀ j, ((s j : ℤ) : ℝ) ^ 2 + 2 * ξ * (((s j : ℤ) : ℝ) * (dipoleMark o x j : ℝ)) ≤
      markedDensity ξ (dipoleMark o x) s j ^ 2 := by
    intro j
    have hρ : markedDensity ξ (dipoleMark o x) s j = ξ * (dipoleMark o x j : ℝ) + (s j : ℝ) :=
      rfl
    rw [hρ]
    nlinarith [sq_nonneg (ξ * (dipoleMark o x j : ℝ))]
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hsite j
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_mul_dipoleMark (fun j => ((s j : ℤ) : ℝ)) o x] at hsum
  have ho := neg_abs_le ((s o : ℤ) : ℝ)
  have hx := le_abs_self ((s x : ℤ) : ℝ)
  have h1 : -(|((s o : ℤ) : ℝ)| + |((s x : ℤ) : ℝ)|) ≤ ((s o : ℤ) : ℝ) - ((s x : ℤ) : ℝ) := by
    linarith
  have h2 : 0 ≤ |((s o : ℤ) : ℝ)| + |((s x : ℤ) : ℝ)| := by positivity
  nlinarith

/-- **The defect at the marked sites is bounded**: with `θ + δ = 1/16`, `δ > 0` and
`a² + b² ≤ Σ`, the activity growth `θ Σ` against the split self-energy
`(θ + δ/2)(Σ − 2(|a| + |b|))` leaves at most `1/(64 δ)`. -/
theorem split_defect_le {θ δ sm a b : ℝ} (hδ : 0 < δ) (hθδ : θ + δ = 1 / 16)
    (hsm : a ^ 2 + b ^ 2 ≤ sm) :
    θ * sm - (θ + δ / 2) * (sm - 2 * (|a| + |b|)) ≤ 1 / (64 * δ) := by
  have hsite : ∀ t : ℝ, |t| / 8 - δ / 2 * t ^ 2 ≤ 1 / (128 * δ) := by
    intro t
    rw [le_div_iff₀ (by positivity), ← sq_abs t]
    nlinarith [sq_nonneg (8 * δ * |t| - 1)]
  have ha := hsite a
  have hb := hsite b
  have hab : 0 ≤ |a| + |b| := by positivity
  have hc : θ + δ / 2 ≤ 1 / 16 := by linarith
  have e : θ * sm - (θ + δ / 2) * (sm - 2 * (|a| + |b|)) =
      -(δ / 2) * sm + 2 * (θ + δ / 2) * (|a| + |b|) := by ring
  have h128 : 1 / (128 * δ) + 1 / (128 * δ) = 1 / (64 * δ) := by
    field_simp
    norm_num
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right hc hab]

end Mass

/-- The split of the composite self-energy, `Q/16 = 8δ Q/16 + (θ + δ/2) Q`: the first part pays
the marked bookkeeping of `cluster_estimate` with `η²` replaced by `8δη²`, the second the integer
self-energy away from the marks. -/
theorem split_gain_le {δ θ η nX sm A D₁ S Q a b : ℝ} (hD₁ : 1 ≤ D₁) (hδ : 0 < δ) (hθ : 0 ≤ θ)
    (hθδ : θ + δ = 1 / 16) (hnX : 0 ≤ nX) (hS : 0 ≤ S) (hAS : A / D₁ ≤ nX + S)
    (hmass : η ^ 2 / 2 * (nX + sm) ≤ Q) (hmass' : sm - 2 * (|a| + |b|) ≤ Q) :
    8 * δ * η ^ 2 * (nX / 64 + sm / 32 + A / (8192 * D₁)) +
      (θ + δ / 2) * (sm - 2 * (|a| + |b|)) ≤ Q / 16 + η ^ 2 / 8192 * S := by
  have hD₁0 : 0 < D₁ := by linarith
  have hδ8 : 8 * δ ≤ 1 := by linarith
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have e1 : 8 * δ * η ^ 2 * (A / D₁) ≤ 8 * δ * η ^ 2 * nX + η ^ 2 * S := by
    have h1 : 8 * δ * η ^ 2 * (A / D₁) ≤ 8 * δ * η ^ 2 * (nX + S) :=
      mul_le_mul_of_nonneg_left hAS (by positivity)
    have h2 : 8 * δ * η ^ 2 * S ≤ η ^ 2 * S := by
      have : 8 * δ * η ^ 2 ≤ η ^ 2 := by
        have := mul_le_mul_of_nonneg_right hδ8 hη2
        linarith
      exact mul_le_mul_of_nonneg_right this hS
    linarith
  have e2 : 0 ≤ 8 * δ * η ^ 2 * nX := by positivity
  have e3 : 8 * δ * (η ^ 2 / 2 * (nX + sm)) ≤ 8 * δ * Q :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  have e4 : (θ + δ / 2) * (sm - 2 * (|a| + |b|)) ≤ (θ + δ / 2) * Q :=
    mul_le_mul_of_nonneg_left hmass' (by linarith)
  have e5 : Q / 16 = 8 * δ * Q / 16 + (θ + δ / 2) * Q := by
    have : 1 = 16 * (θ + δ / 2) + 8 * δ := by linarith
    linear_combination Q / 16 * this
  have e6 : 8 * δ * η ^ 2 * (nX / 64 + sm / 32 + A / (8192 * D₁)) =
      8 * δ * η ^ 2 * nX / 64 + 8 * δ * η ^ 2 * sm / 32 +
        8 * δ * η ^ 2 * (A / D₁) / 8192 := by
    field_simp
  have e7 : 8 * δ * (η ^ 2 / 2 * (nX + sm)) =
      8 * δ * η ^ 2 * nX / 2 + 8 * δ * η ^ 2 * sm / 2 := by ring
  rw [e6, e5]
  rw [e7] at e3
  linarith

/-- The exponent algebra of one orientation: from `P + R ≤ W` and `θΣ − R ≤ 1/(64δ)`,
`X + (h₀ + θ/β) Σ − W/β ≤ 1/(64δβ) + (X + h₀ Σ − P/β)`. -/
theorem split_exponent_le {β δ θ h₀ sm X P R W : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    (hkey : P + R ≤ W) (hdef : θ * sm - R ≤ 1 / (64 * δ)) :
    X + (h₀ + θ / β) * sm - W / β ≤ 1 / (64 * δ * β) + (X + h₀ * sm - P / β) := by
  have h1 : θ * sm - W ≤ 1 / (64 * δ) - P := by linarith
  have h2 := div_le_div_of_nonneg_right h1 hβ.le
  have e1 : (θ * sm - W) / β = θ / β * sm - W / β := by ring
  have e2 : (1 / (64 * δ) - P) / β = 1 / (64 * δ * β) - P / β := by
    field_simp
  rw [e1, e2] at h2
  have e3 : (h₀ + θ / β) * sm = h₀ * sm + θ / β * sm := by ring
  rw [e3]
  linarith

/-! ### The cluster estimate with the activity growth split off -/

section ClusterEstimate

variable {boundary : SquareBoundary} {L : ℕ}

/-- **Step 1 of the split cluster estimate**: for activities `e^{(h₀ + θ/β)‖ϱ‖²}` with
`θ + δ = 1/16`, the orientation sum of a neutral cluster is at most
`e^{1/(64δβ)} e^{289 D₂ A + h₀ Σ − G*}` with `G* = (8δη²/β)(|X|/64 + Σ/32 + A(X)/(8192 D₁))`. The
growth `θ/β` is paid by the integer self-energy `(θ + δ/2)/β` on every site; only the two marked
sites leave the bounded defect `1/(64δβ)` (`split_defect_le`). -/
theorem cluster_orientationSum_le_split (hL : 1 < L) {D₁ D₂ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h21 : P21Step boundary L D₁) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNb : IsScaleSeparated boundary L N)
    (K : ChargeDensity L → ℝ) {lamHat : Fin L × Fin L → ℕ → ℝ} {h₀ θ δ : ℝ}
    (hθ : 0 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ = 1 / 16)
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    {β : ℝ} (hβ : 0 < β)
    (hlam : ∀ ϱ ∈ N, ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
      Real.exp ((h₀ + θ / β) * ∑ j, (ϱ j : ℝ) ^ 2))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 < η)
    (hηξ : η ≤ dipoleGap ξ)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    ∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T) ≤
      Real.exp (1 / (64 * δ * β) + (289 * D₂ * (chargeCoverCost boundary L
          (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) +
        h₀ * ∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2 -
        8 * δ * η ^ 2 / β * ((markedSupport L (dipoleMark o x) C).card / 64 +
          (∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2) / 32 +
          (chargeCoverCost boundary L (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) /
            (8192 * D₁)))) := by
  classical
  have hL0 : 0 < L := by omega
  obtain ⟨X, hX⟩ : ∃ X, X = markedSupport L (dipoleMark o x) C := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (chargeCoverCost boundary L (supportProxy X) : ℝ) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ sm : ℝ, sm = ∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨nX, hnX⟩ : ∃ nX : ℝ, nX = (X.card : ℝ) := ⟨_, rfl⟩
  rw [← hX, ← hA, ← hsm, ← hnX]
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hdisjC : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m') :=
    fun m hm m' hm' hne => hens.2 m (hCN hm) m' (hCN hm') hne
  have hdX : 1 ≤ squareDiameter boundary L (markedSupport L (dipoleMark o x) C) :=
    one_le_squareDiameter_markedSupport_dipole hL hox C
  have hnX0 : 0 ≤ nX := by rw [hnX]; exact Nat.cast_nonneg _
  -- the activity
  have hact : |(1 / 2) ^ C.card * ∏ m ∈ C, K m| ≤
      (1 / 2) ^ C.card * Real.exp (289 * D₂ * A) * Real.exp ((h₀ + θ / β) * sm) := by
    refine (abs_clusterWeight_le_coverCost hL hD₂ hd hens hNb hCN hCn hdX).trans ?_
    rw [hA, hX]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hsm, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun m _ => Finset.prod_nonneg fun j _ => by positivity)
      fun m hm => hlam m (hCN hm)
  -- the exponent of each orientation
  have hgain : ∀ T ∈ C.powerset, 289 * D₂ * A + (h₀ + θ / β) * sm -
      compositeGain boundary hL0 ξ η β (dipoleMark o x) C T ≤
      1 / (64 * δ * β) + (289 * D₂ * A + h₀ * sm -
        8 * δ * η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁))) := by
    intro T hT
    have hT' : T ⊆ C := Finset.mem_powerset.1 hT
    have hmass := sum_markedDensity_sq_ge hox hξ0 hξ1 hη.le hηξ hT' hdisjC
    rw [← hX, ← hsm, ← hnX] at hmass
    have hsat : ∑ j, ((satellite L C T j : ℤ) : ℝ) ^ 2 = sm := by
      rw [hsm, Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => satellite_sq hT' hdisjC j
    have hmass' := sum_markedDensity_sq_ge_sub o x hξ0.le hξ1.le (satellite L C T)
    rw [hsat] at hmass'
    set a : ℝ := ((satellite L C T o : ℤ) : ℝ) with ha
    set b : ℝ := ((satellite L C T x : ℤ) : ℝ) with hb
    have hab : a ^ 2 + b ^ 2 ≤ sm := by
      have hpair : a ^ 2 + b ^ 2 = ∑ j ∈ {o, x}, ((satellite L C T j : ℤ) : ℝ) ^ 2 := by
        rw [Finset.sum_pair hox]
      rw [← hsat, hpair]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun j _ _ => sq_nonneg _
    have hdef := split_defect_le hδ hθδ hab
    have hsuppP : chargeSupport (markedProxy (dipoleMark o x) C T) = X := by
      rw [hX]; exact chargeSupport_markedProxy_dipole hox hT' hdisjC
    have hp0 : markedProxy (dipoleMark o x) C T ≠ 0 := by
      intro h0
      have ho : o ∈ X := by
        rw [hX]
        exact chargeSupport_subset_markedSupport _ C
          (mem_chargeSupport'.2 (by simp [dipoleMark, hox]))
      rw [← hsuppP, h0] at ho
      exact (mem_chargeSupport'.1 ho) rfl
    obtain ⟨-, hP21⟩ := h21 (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) _ hp0
    have hAeq : chargeCoverCost boundary L (markedProxy (dipoleMark o x) C T) =
        chargeCoverCost boundary L (supportProxy X) :=
      chargeCoverCost_congr (by rw [hsuppP, chargeSupport_supportProxy])
    have hS0 : (squareCoverNumber boundary L 0 (markedProxy (dipoleMark o x) C T) : ℝ) ≤ nX := by
      have := squareCoverNumber_zero_le_card boundary L (markedProxy (dipoleMark o x) C T)
      rw [hsuppP] at this
      rw [hnX]
      exact_mod_cast this
    rw [hAeq, ← hA] at hP21
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (separatedSquareTotal boundary L
        (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k)
        (markedProxy (dipoleMark o x) C T) : ℝ) := ⟨_, rfl⟩
    rw [← hS] at hP21
    have hS0' : 0 ≤ S := by rw [hS]; exact Nat.cast_nonneg _
    have hAS : A / D₁ ≤ nX + S := by
      rw [div_le_iff₀ (by linarith)]
      have h2 : D₁ * ((squareCoverNumber boundary L 0 (markedProxy (dipoleMark o x) C T) : ℝ) +
          S) ≤ D₁ * (nX + S) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ j, markedDensity ξ (dipoleMark o x) (satellite L C T) j ^ 2 :=
      ⟨_, rfl⟩
    rw [← hQ] at hmass hmass'
    have hcg : compositeGain boundary hL0 ξ η β (dipoleMark o x) C T =
        (Q / 16 + η ^ 2 / 8192 * S) / β := by
      unfold compositeGain
      rw [hQ, hS]
    rw [hcg]
    have key := split_gain_le (η := η) (A := A) hD₁ hδ hθ hθδ hnX0 hS0' hAS hmass hmass'
    have e9 : 8 * δ * η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁)) =
        8 * δ * η ^ 2 * (nX / 64 + sm / 32 + A / (8192 * D₁)) / β := by ring
    rw [e9]
    exact split_exponent_le hβ hδ key hdef
  -- the sum over orientations
  calc ∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary hL0 ξ η β (dipoleMark o x) C T)
      ≤ ∑ _T ∈ C.powerset, (1 / 2) ^ C.card * Real.exp (1 / (64 * δ * β) +
          (289 * D₂ * A + h₀ * sm -
            8 * δ * η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁)))) := by
        refine Finset.sum_le_sum fun T hT => ?_
        calc |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
              Real.exp (-compositeGain boundary hL0 ξ η β (dipoleMark o x) C T)
            ≤ (1 / 2) ^ C.card * Real.exp (289 * D₂ * A) * Real.exp ((h₀ + θ / β) * sm) *
                Real.exp (-compositeGain boundary hL0 ξ η β (dipoleMark o x) C T) :=
              mul_le_mul_of_nonneg_right hact (Real.exp_pos _).le
          _ = (1 / 2) ^ C.card * Real.exp (289 * D₂ * A + (h₀ + θ / β) * sm -
                compositeGain boundary hL0 ξ η β (dipoleMark o x) C T) := by
              rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hgain T hT)) (by positivity)
    _ = Real.exp (1 / (64 * δ * β) + (289 * D₂ * A + h₀ * sm -
          8 * δ * η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁)))) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
          ← mul_assoc, ← mul_pow]
        norm_num

/-- **The split cluster estimate** (FS81 (5.31)–(5.33) for Condition-λ activities in the whole
range `θ < 1/16`). The activities grow like `e^{(h₀ + θ/β)‖ϱ‖²}` with `θ + δ = 1/16`, `θ ≥ 0`,
`δ > 0`. The conditions (H1)–(H3) are those of `cluster_estimate` with `η²` replaced by `8δη²` and
`h` by the `β`-independent `h₀`. The branch bound of a neutral cluster is then at most
`2 e^{1/(64δβ)} e^{-(8δη²/(16384 D₁ β)) log₂(|o − x| + 1)}` times its exploration weight. -/
theorem cluster_estimate_split (hL : 1 < L) {D₁ D₂ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h21 : P21Step boundary L D₁) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (K : ChargeDensity L → ℝ) {lamHat : Fin L × Fin L → ℕ → ℝ} {h₀ θ δ : ℝ}
    (hθ : 0 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ = 1 / 16)
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (hlam : ∀ ϱ ∈ N, ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
      Real.exp ((h₀ + θ / β) * ∑ j, (ϱ j : ℝ) ^ 2))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 < η)
    (hηξ : η ≤ dipoleGap ξ)
    (H1 : β * (h₀ + 1) + c ≤ 8 * δ * η ^ 2 / 32)
    (H2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤
      8 * δ * η ^ 2 / (64 * β))
    (H3 : 289 * D₂ * β + 289 * c ≤ 8 * δ * η ^ 2 / (16384 * D₁))
    (H4 : Real.exp (-(c / β)) ≤ 1 / 32)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T)) /
      ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
        (1 - memberWeight boundary c β m) ≤
      2 * Real.exp (1 / (64 * δ * β)) * Real.exp (-(8 * δ * η ^ 2 / (16384 * D₁ * β)) *
          Real.logb 2 (latticeDistance boundary L o x + 1)) *
        ((∏ m ∈ C, explorationWeight boundary c β m) *
          ∏ m ∈ N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C),
            (1 - explorationWeight boundary c β m)) := by
  classical
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hθle : ∀ m ∈ N, memberWeight boundary c β m ≤ 1 / 32 := fun m hm =>
    (memberWeight_le hc hβ (hens.1 m hm)).trans H4
  have hθ1 : ∀ m ∈ N, memberWeight boundary c β m ≤ 1 := fun m hm =>
    (hθle m hm).trans (by norm_num)
  have h1 := cluster_orientationSum_le_split hL hD₁ hD₂ h21 hens hNb K hθ hδ hθδ hd hβ hlam hox
    hξ0 hξ1 hη hηξ hC hCn
  have h2 := cluster_dropped_le (boundary := boundary) (c := c) (β := β)
    (R := markedRemainder boundary L (dipoleMark o x) N C) hθ1 hCN
  have h3 := cluster_exploration_ge (boundary := boundary) (c := c) (β := β)
    (R := markedRemainder boundary L (dipoleMark o x) N C) hNa hθ1 hCn
  have h4 := cluster_memberWeight_ge hL h21 hens hNb hox hc hβ H4 hC
  have h5 := cluster_neighbourWeight_ge (boundary := boundary) hL hens hox hCn hc hβ H4
  have h6 := logb_latticeDistance_le_coverCost hL h21 hox C
  -- names
  obtain ⟨X, hX⟩ : ∃ X, X = markedSupport L (dipoleMark o x) C := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (chargeCoverCost boundary L (supportProxy X) : ℝ) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ sm : ℝ, sm = ∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β)) :=
    ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.logb 2 (latticeDistance boundary L o x + 1) := ⟨_, rfl⟩
  obtain ⟨PC, hPC⟩ : ∃ PC : ℝ, PC = ∏ m ∈ C, memberWeight boundary c β m := ⟨_, rfl⟩
  obtain ⟨QC, hQC⟩ : ∃ QC : ℝ, QC = ∏ m ∈ C, (1 - memberWeight boundary c β m) := ⟨_, rfl⟩
  obtain ⟨QB, hQB⟩ : ∃ QB : ℝ, QB = ∏ m ∈ (N \ (C ∪ markedRemainder boundary L
      (dipoleMark o x) N C)).filter (fun m => ∑ j, m j = 0), (1 - memberWeight boundary c β m) :=
    ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = Real.sqrt (8 * δ) * η := ⟨_, rfl⟩
  have hν2 : ν ^ 2 = 8 * δ * η ^ 2 := by
    rw [hν, mul_pow, Real.sq_sqrt (by linarith)]
  rw [← hX, ← hA, ← hsm] at h1
  rw [← hQC, ← hQB] at h2
  rw [← hPC, ← hQB] at h3
  rw [← hX, ← hA, ← hsm, ← hPC, ← hQC] at h4
  rw [← hκ, ← hX, ← hQB] at h5
  rw [← hX, ← hA, ← hℓ] at h6
  rw [← hκ, ← hν2] at H2
  rw [← hν2] at H1 H3
  rw [← hℓ, ← hν2]
  rw [← hν2] at h1
  have hA0 : 0 ≤ A := by rw [hA]; exact Nat.cast_nonneg _
  have hsm0 : 0 ≤ sm := by
    rw [hsm]; exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have hexp := cluster_exponent_le (D₂ := D₂) (h := h₀) hD₁ hβ hA0 hsm0 hnX0 h6 H1 H2 H3
  have hQCpos : 0 < QC := by
    rw [hQC]
    exact Finset.prod_pos fun m hm => by have := hθle m (hCN hm); linarith
  have hQBpos : 0 < QB := by
    rw [hQB]
    exact Finset.prod_pos fun m hm => by
      have := hθle m (Finset.mem_sdiff.1 (Finset.mem_filter.1 hm).1).1; linarith
  have hPC0 : 0 ≤ PC := by
    rw [hPC]; exact Finset.prod_nonneg fun m _ => (memberWeight_pos (boundary := boundary) c β m).le
  have hDpos : 0 < QC * QB := mul_pos hQCpos hQBpos
  have hE : Real.exp (1 / (64 * δ * β) + (289 * D₂ * A + h₀ * sm -
        ν ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁)))) ≤
      Real.exp (1 / (64 * δ * β)) * Real.exp (-(ν ^ 2 / (16384 * D₁ * β)) * ℓ) * (PC * QC) *
        (QB * QB) := by
    calc Real.exp (1 / (64 * δ * β) + (289 * D₂ * A + h₀ * sm -
          ν ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁))))
        ≤ Real.exp (1 / (64 * δ * β)) * Real.exp (-(ν ^ 2 / (16384 * D₁ * β)) * ℓ) *
            (Real.exp (-(c / β) * (sm + 289 * A)) * Real.exp (-sm)) *
            (Real.exp (-(2 * κ * X.card)) * Real.exp (-(2 * κ * X.card))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          linarith
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h4 (by positivity))
          (mul_le_mul h5 h5 (Real.exp_pos _).le hQBpos.le) (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg hPC0 hQCpos.le))
  calc (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T)) /
        ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
          (1 - memberWeight boundary c β m)
      ≤ Real.exp (1 / (64 * δ * β) + (289 * D₂ * A + h₀ * sm -
          ν ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁)))) / (QC * QB) :=
        div_le_div₀ (Real.exp_pos _).le h1 hDpos h2
    _ ≤ 2 * Real.exp (1 / (64 * δ * β)) * Real.exp (-(ν ^ 2 / (16384 * D₁ * β)) * ℓ) *
          (PC * (1 / 2 * QB)) := by
        rw [div_le_iff₀ hDpos]
        calc Real.exp (1 / (64 * δ * β) + (289 * D₂ * A + h₀ * sm -
              ν ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁))))
            ≤ Real.exp (1 / (64 * δ * β)) * Real.exp (-(ν ^ 2 / (16384 * D₁ * β)) * ℓ) *
                (PC * QC) * (QB * QB) := hE
          _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

end ClusterEstimate

end FroehlichSpencer.BKT.Coulomb

end
