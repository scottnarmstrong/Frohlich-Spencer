/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Cluster
import Mathlib.Tactic

/-!
# The marked bound on a square domain

FS81 Theorem B on one square domain, for the hard-core gas and the dipole mark (CG.s4–s5 in
cluster form).

* `sum_markedDensity_sq_ge`: `‖ξ(δ_o − δ_x) + ϱ^𝒩‖² ≥ (η²/2)(|X| + ∑_C ‖m‖²)`.
* `chargeCoverCost_congr`: KP's cover cost depends only on the support.
* **`cluster_estimate`**: under explicit smallness conditions (H1)–(H4), the branch bound of
  each neutral cluster is at most `2 e^{-(η²/(16384 D₁ β)) log₂(|o − x| + 1)}` times its
  exploration weight.
  - The steps are `cluster_orientationSum_le`, `cluster_dropped_le`, `cluster_exploration_ge`,
    `cluster_memberWeight_ge`, `cluster_neighbourWeight_ge`,
    `logb_latticeDistance_le_coverCost` and `cluster_exponent_le`.
  - The activity `e^{289 D₂ A(X)} e^{h Σ}` (FS81 (2.30), ), the members' weights and the
    neighbours' costs are beaten by the composite energy
    `(η²/β)(|X|/64 + Σ/32 + A(X)/(8192 D₁))`. That bound uses P2.1 for the proxy.
* `hardCore_renormalizedActivity_le`: KP's damping `|K| e^{-E} ≤ e^{-(c/β)(‖m‖² + log₂(d + 1))}`
  for hard-core weights.
* **`markedDomain_bound`**: `0 < 𝒵 = ∫ ∏_j (1 + 2z_j cos φ_j) dμ` and
  `|∫ cos(ξ(φ_o − φ_x)) ∏_j (1 + 2z_j cos φ_j) dμ| ≤ 2 e^{-(η²/(16384 D₁ β)) log₂(|o − x| + 1)} 𝒵`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

open MeasureTheory Reduction

/-! ### The mass of the marked composite -/

section Mass

variable {L : ℕ}

/-- With pairwise disjoint member supports, `(ϱ^𝒩(j))² = ∑_{m ∈ C} m(j)²`. -/
theorem satellite_sq {C T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → Disjoint (Function.support m) (Function.support m'))
    (j : Fin L × Fin L) :
    ((satellite L C T j : ℤ) : ℝ) ^ 2 = ∑ m ∈ C, ((m j : ℤ) : ℝ) ^ 2 := by
  classical
  by_cases h : ∃ m ∈ C, m j ≠ 0
  · obtain ⟨m₀, hm₀, hj⟩ := h
    have hother : ∀ m ∈ C, m ≠ m₀ → m j = 0 := fun m hm hne => by
      by_contra h'
      exact Set.disjoint_left.1 (hdisj m hm m₀ hm₀ hne) h' hj
    have hsum : ∀ U ⊆ C, ∑ m ∈ U, m j = if m₀ ∈ U then m₀ j else 0 := by
      intro U hU
      rw [Finset.sum_congr rfl fun m hm => (show m j = if m = m₀ then m₀ j else 0 by
        split_ifs with h
        · rw [h]
        · exact hother m (hU hm) h), Finset.sum_ite_eq']
    have hsat : satellite L C T j = (if m₀ ∈ T then m₀ j else 0) -
        (if m₀ ∈ C \ T then m₀ j else 0) := by
      unfold satellite
      rw [hsum T hT, hsum (C \ T) Finset.sdiff_subset]
    rw [Finset.sum_eq_single_of_mem m₀ hm₀ fun m hm hne => by
      rw [hother m hm hne, Int.cast_zero]; ring, hsat]
    by_cases hmT : m₀ ∈ T
    · rw [ite_eq_left hmT, ite_eq_right fun h => (Finset.mem_sdiff.1 h).2 hmT, sub_zero]
    · rw [ite_eq_right hmT, ite_eq_left (Finset.mem_sdiff.2 ⟨hm₀, hmT⟩)]
      push_cast
      ring
  · push Not at h
    have hsat : satellite L C T j = 0 := by
      unfold satellite
      rw [Finset.sum_eq_zero fun m hm => h m (hT hm),
        Finset.sum_eq_zero fun m hm => h m (Finset.mem_sdiff.1 hm).1, sub_zero]
    rw [hsat, Finset.sum_eq_zero fun m hm => by rw [h m hm, Int.cast_zero]; ring]
    simp

/-- **The mass of the Coulomb-B composite**: for `0 < ξ < 1`, `0 ≤ η ≤ min(ξ, 1 − ξ)` and a
cluster with pairwise disjoint member supports,
`‖ξ(δ_o − δ_x) + ϱ^𝒩‖² ≥ (η²/2) (|X| + ∑_{m ∈ C} ‖m‖²)`, `X = supp ϱ₀ ∪ ⋃ C`: every site of
`X` carries a marked charge of size at least `η` (the gap at `o, x`, an integer elsewhere). -/
theorem sum_markedDensity_sq_ge {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) (hη : 0 ≤ η) (hηξ : η ≤ dipoleGap ξ) {C T : Finset (ChargeDensity L)}
    (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m')) :
    η ^ 2 / 2 * ((markedSupport L (dipoleMark o x) C).card +
        ∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2) ≤
      ∑ j, markedDensity ξ (dipoleMark o x) (satellite L C T) j ^ 2 := by
  classical
  set X := markedSupport L (dipoleMark o x) C with hX
  have hη2 : η ^ 2 ≤ 1 / 4 := by
    have h := hηξ.trans (dipoleGap_le_half ξ)
    nlinarith
  have hcard : (X.card : ℝ) = ∑ j, (if j ∈ X then (1 : ℝ) else 0) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsq : ∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2 = ∑ j, ((satellite L C T j : ℤ) : ℝ) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (satellite_sq hT hdisj j).symm
  rw [hcard, hsq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  set s : ℝ := ((satellite L C T j : ℤ) : ℝ) with hs
  have hρ : markedDensity ξ (dipoleMark o x) (satellite L C T) j =
      ξ * (dipoleMark o x j : ℝ) + s := rfl
  rw [hρ]
  by_cases hjX : j ∈ X
  · rw [ite_eq_left hjX]
    by_cases hm0 : dipoleMark o x j = 0
    · -- a site of the satellite only
      rw [hm0, Int.cast_zero, mul_zero, zero_add]
      obtain ⟨m, hmC, hmj⟩ := (mem_markedSupport.1 hjX).resolve_left (by simpa using hm0)
      have hs1 : (1 : ℝ) ≤ s ^ 2 := by
        rw [hs, satellite_sq hT hdisj j]
        have h1 : (1 : ℝ) ≤ ((m j : ℤ) : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ |((m j : ℤ) : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hmj
          nlinarith [abs_nonneg ((m j : ℤ) : ℝ), sq_abs ((m j : ℤ) : ℝ)]
        exact h1.trans (Finset.single_le_sum (fun m _ => sq_nonneg ((m j : ℤ) : ℝ)) hmC)
      nlinarith
    · -- a site of the mark: the gapped charge `±ξ + n`
      have hk : dipoleMark o x j = 1 ∨ dipoleMark o x j = -1 := by
        unfold dipoleMark at hm0 ⊢
        by_cases hjo : j = o
        · subst hjo
          simp [hox]
        · by_cases hjx : j = x
          · subst hjx
            simp [hjo]
          · simp [hjo, hjx] at hm0
      have hg := (isGapped_mul_add_int (ξ := ξ) hk (satellite L C T j)).le_abs
      rw [mul_comm] at hg
      have hgap : η ≤ |ξ * (dipoleMark o x j : ℝ) + s| := hηξ.trans hg
      have hk' : |(dipoleMark o x j : ℝ)| = 1 := by
        rcases hk with h | h <;> simp [h]
      by_cases hs2 : |s| ≤ 1
      · have : η ^ 2 ≤ (ξ * (dipoleMark o x j : ℝ) + s) ^ 2 := by
          rw [← sq_abs (ξ * _ + s)]
          exact pow_le_pow_left₀ hη hgap 2
        have hs1 : s ^ 2 ≤ 1 := by
          rw [← sq_abs]; nlinarith [abs_nonneg s]
        nlinarith
      · push Not at hs2
        have hlow : |s| - 1 ≤ |ξ * (dipoleMark o x j : ℝ) + s| := by
          have h1 : |ξ * (dipoleMark o x j : ℝ)| ≤ 1 := by
            rw [abs_mul, hk', mul_one, abs_of_pos hξ0]
            exact hξ1.le
          have h2 := abs_add_le (ξ * (dipoleMark o x j : ℝ) + s) (-(ξ * (dipoleMark o x j : ℝ)))
          rw [abs_neg, show ξ * (dipoleMark o x j : ℝ) + s + -(ξ * (dipoleMark o x j : ℝ)) = s by
            ring] at h2
          linarith
        have hsq' : (|s| - 1) ^ 2 ≤ (ξ * (dipoleMark o x j : ℝ) + s) ^ 2 := by
          rw [← sq_abs (ξ * _ + s)]
          exact pow_le_pow_left₀ (by linarith) hlow 2
        have hss : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
        have h2s : 2 ≤ |s| := by
          rw [hs, ← Int.cast_abs] at hs2 ⊢
          have : (1 : ℤ) < |satellite L C T j| := by exact_mod_cast hs2
          have : (2 : ℤ) ≤ |satellite L C T j| := this
          exact_mod_cast this
        nlinarith
  · -- off the composite support
    rw [ite_eq_right hjX]
    have hm0 : dipoleMark o x j = 0 := by
      by_contra h
      exact hjX (chargeSupport_subset_markedSupport _ C (mem_chargeSupport'.2 h))
    have hs0 : s = 0 := by
      rw [hs]
      have : satellite L C T j = 0 := by
        unfold satellite
        have hzero : ∀ m ∈ C, m j = 0 := fun m hm => by
          by_contra h
          exact hjX (chargeSupport_subset_markedSupport_of_mem hm (mem_chargeSupport'.2 h))
        rw [Finset.sum_eq_zero fun m hm => hzero m (hT hm),
          Finset.sum_eq_zero fun m hm => hzero m (Finset.mem_sdiff.1 hm).1, sub_zero]
      rw [this, Int.cast_zero]
    rw [hm0, hs0]
    simp

end Mass

/-! ### Support invariance of KP's cover cost -/

section Cost

variable {boundary : SquareBoundary} {L : ℕ}

theorem squareCoverNumber_congr {ρ ρ' : ChargeDensity L} (h : chargeSupport ρ = chargeSupport ρ')
    (k : ℕ) : squareCoverNumber boundary L k ρ = squareCoverNumber boundary L k ρ' := by
  have hc : squareCoverCandidates boundary L k ρ = squareCoverCandidates boundary L k ρ' := by
    unfold squareCoverCandidates IsSquareCover
    rw [h]
  unfold squareCoverNumber
  simp only [hc]

theorem chargeCoverCost_congr {ρ ρ' : ChargeDensity L} (h : chargeSupport ρ = chargeSupport ρ') :
    chargeCoverCost boundary L ρ = chargeCoverCost boundary L ρ' := by
  have hd : chargeDiameter boundary L ρ = chargeDiameter boundary L ρ' := by
    unfold chargeDiameter
    rw [h]
  unfold chargeCoverCost chargeCutoff
  simp only [hd, squareCoverNumber_congr (boundary := boundary) h]

end Cost

/-! ### The per-cluster estimate -/

section ClusterEstimate

variable (boundary : SquareBoundary) {L : ℕ}

/-- The member weight `θ_m = e^{-(c/β)(‖m‖² + log₂(d(m) + 1))}`, a bound on the renormalized
activity of a neutral member (KP (1.14) with constant `c`). -/
def memberWeight (c β : ℝ) (m : ChargeDensity L) : ℝ :=
  Real.exp (-(c / β) * (∑ j, (m j : ℝ) ^ 2 + Real.logb 2 (chargeDiameter boundary L m + 1)))

/-- The exploration weight: `θ_m` for neutral members, `1/2` for the (at most one) charged one. -/
def explorationWeight (c β : ℝ) (m : ChargeDensity L) : ℝ :=
  if ∑ j, m j = 0 then memberWeight boundary c β m else 1 / 2

variable {boundary}

theorem memberWeight_pos (c β : ℝ) (m : ChargeDensity L) : 0 < memberWeight boundary c β m :=
  Real.exp_pos _

theorem memberWeight_le {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) {m : ChargeDensity L}
    (hm : m ≠ 0) : memberWeight boundary c β m ≤ Real.exp (-(c / β)) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, m j ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  have hs : (1 : ℝ) ≤ ∑ j, (m j : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (m j₀ : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ |(m j₀ : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj₀
      nlinarith [abs_nonneg (m j₀ : ℝ), sq_abs (m j₀ : ℝ)]
    exact h1.trans (Finset.single_le_sum (fun j _ => sq_nonneg (m j : ℝ)) (Finset.mem_univ j₀))
  have hl : 0 ≤ Real.logb 2 (chargeDiameter boundary L m + 1) :=
    Real.logb_nonneg (by norm_num) (by
      have := (chargeDiameter boundary L m).cast_nonneg (α := ℝ)
      linarith)
  have hcb : 0 < c / β := div_pos hc hβ
  unfold memberWeight
  refine Real.exp_le_exp.2 ?_
  nlinarith

/-- `1 - t ≥ e^{-2t}` on `[0, 1/2]`. -/
theorem exp_neg_two_mul_le_one_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    Real.exp (-(2 * t)) ≤ 1 - t := by
  have hconv := convexOn_exp.2 (Set.mem_univ (-1 : ℝ)) (Set.mem_univ 0)
    (show (0 : ℝ) ≤ 2 * t by linarith) (show (0 : ℝ) ≤ 1 - 2 * t by linarith)
    (show 2 * t + (1 - 2 * t) = 1 by ring)
  simp only [smul_eq_mul, mul_neg, mul_one, mul_zero, add_zero, Real.exp_zero] at hconv
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  nlinarith

/-- Step 1 of the cluster estimate: the activity of the cluster against the energy gain of all
its orientations, `∑_T 2^{-|C|} |∏_C K| e^{-G(C,T)} ≤ e^{289 D₂ A(X) + h Σ − G*}` with
`G* = (η²/β)(|X|/64 + Σ/32 + A(X)/(8192 D₁))`, `Σ = ∑_{m ∈ C} ‖m‖²`. -/
theorem cluster_orientationSum_le (hL : 1 < L) {D₁ D₂ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h21 : P21Step boundary L D₁) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNb : IsScaleSeparated boundary L N)
    (K : ChargeDensity L → ℝ) {lamHat : Fin L × Fin L → ℕ → ℝ} {h : ℝ}
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    (hlam : ∀ ϱ ∈ N, ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
      Real.exp (h * ∑ j, (ϱ j : ℝ) ^ 2))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 < η)
    (hηξ : η ≤ dipoleGap ξ) {β : ℝ} (hβ : 0 < β)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    ∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T) ≤
      Real.exp (289 * D₂ * (chargeCoverCost boundary L
          (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) +
        h * ∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2 -
        η ^ 2 / β * ((markedSupport L (dipoleMark o x) C).card / 64 +
          (∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2) / 32 +
          (chargeCoverCost boundary L (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) /
            (8192 * D₁))) := by
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
      (1 / 2) ^ C.card * Real.exp (289 * D₂ * A) * Real.exp (h * sm) := by
    refine (abs_clusterWeight_le_coverCost hL hD₂ hd hens hNb hCN hCn hdX).trans ?_
    rw [hA, hX]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hsm, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun m _ => Finset.prod_nonneg fun j _ => by positivity)
      fun m hm => hlam m (hCN hm)
  -- the gain of each orientation
  have hgain : ∀ T ∈ C.powerset, η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁)) ≤
      compositeGain boundary hL0 ξ η β (dipoleMark o x) C T := by
    intro T hT
    have hT' : T ⊆ C := Finset.mem_powerset.1 hT
    have hmass := sum_markedDensity_sq_ge hox hξ0 hξ1 hη.le hηξ hT' hdisjC
    rw [← hX, ← hsm, ← hnX] at hmass
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
    have hAS : A / D₁ ≤ nX + S := by
      rw [div_le_iff₀ (by linarith)]
      have h2 : D₁ * ((squareCoverNumber boundary L 0 (markedProxy (dipoleMark o x) C T) : ℝ) +
          S) ≤ D₁ * (nX + S) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ j, markedDensity ξ (dipoleMark o x) (satellite L C T) j ^ 2 :=
      ⟨_, rfl⟩
    rw [← hQ] at hmass
    have hcg : compositeGain boundary hL0 ξ η β (dipoleMark o x) C T =
        (Q / 16 + η ^ 2 / 8192 * S) / β := by
      unfold compositeGain
      rw [hQ, hS]
    rw [hcg]
    have e1 : η ^ 2 * (A / D₁) ≤ η ^ 2 * nX + η ^ 2 * S := by
      calc η ^ 2 * (A / D₁) ≤ η ^ 2 * (nX + S) := mul_le_mul_of_nonneg_left hAS (sq_nonneg η)
        _ = η ^ 2 * nX + η ^ 2 * S := by ring
    have e2 : 0 ≤ η ^ 2 * nX := mul_nonneg (sq_nonneg η) hnX0
    have key : η ^ 2 * (nX / 64 + sm / 32 + A / (8192 * D₁)) ≤ Q / 16 + η ^ 2 / 8192 * S := by
      have h1 : η ^ 2 * (nX / 64 + sm / 32 + A / (8192 * D₁)) =
          η ^ 2 * nX / 64 + η ^ 2 * sm / 32 + η ^ 2 * (A / D₁) / 8192 := by ring
      have h2 : η ^ 2 / 2 * (nX + sm) = η ^ 2 * nX / 2 + η ^ 2 * sm / 2 := by ring
      rw [h1]
      rw [h2] at hmass
      linarith
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hβ]
    exact key
  -- the sum over orientations
  calc ∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary hL0 ξ η β (dipoleMark o x) C T)
      ≤ ∑ _T ∈ C.powerset, (1 / 2) ^ C.card * Real.exp (289 * D₂ * A) *
          Real.exp (h * sm) * Real.exp (-(η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁)))) :=
        Finset.sum_le_sum fun T hT => mul_le_mul hact
          (Real.exp_le_exp.2 (neg_le_neg (hgain T hT))) (Real.exp_pos _).le (by positivity)
    _ = Real.exp (289 * D₂ * A + h * sm -
          η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁))) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
          sub_eq_add_neg, Real.exp_add, Real.exp_add]
        have h2 : (2 : ℝ) ^ C.card * (1 / 2) ^ C.card = 1 := by
          rw [← mul_pow]; norm_num
        calc (2 : ℝ) ^ C.card * ((1 / 2) ^ C.card * Real.exp (289 * D₂ * A) *
              Real.exp (h * sm) * Real.exp (-(η ^ 2 / β * (nX / 64 + sm / 32 +
                A / (8192 * D₁)))))
            = ((2 : ℝ) ^ C.card * (1 / 2) ^ C.card) * (Real.exp (289 * D₂ * A) *
                Real.exp (h * sm) * Real.exp (-(η ^ 2 / β * (nX / 64 + sm / 32 +
                  A / (8192 * D₁))))) := by ring
          _ = _ := by rw [h2, one_mul]

/-- Step 2: the factors dropped from the branch normalizer are those of `C` and of its neutral
neighbours `Bd = (N ∖ (C ∪ R))₀`. -/
theorem cluster_dropped_le {c β : ℝ} {N C R : Finset (ChargeDensity L)}
    (hθ1 : ∀ m ∈ N, memberWeight boundary c β m ≤ 1) (hCN : C ⊆ N) :
    (∏ m ∈ C, (1 - memberWeight boundary c β m)) *
        ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
          (1 - memberWeight boundary c β m) ≤
      ∏ m ∈ neutralPart N \ neutralPart R, (1 - memberWeight boundary c β m) := by
  classical
  set Bd := (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0) with hBd
  have hBdC : Disjoint C Bd := by
    rw [Finset.disjoint_left]
    intro m hmC hmB
    exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hmB).1).2 (Finset.mem_union_left _ hmC)
  have hsub : neutralPart N \ neutralPart R ⊆ C ∪ Bd := by
    intro m hm
    obtain ⟨hmN₀, hmR₀⟩ := Finset.mem_sdiff.1 hm
    obtain ⟨hmN, hmn⟩ := mem_neutralPart.1 hmN₀
    by_cases hmC : m ∈ C
    · exact Finset.mem_union_left _ hmC
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hmN, ?_⟩, hmn⟩)
      intro hmCR
      rcases Finset.mem_union.1 hmCR with h' | h'
      · exact hmC h'
      · exact hmR₀ (mem_neutralPart.2 ⟨h', hmn⟩)
  have hmemN : ∀ m ∈ C ∪ Bd, m ∈ N := by
    intro m hm
    rcases Finset.mem_union.1 hm with h' | h'
    · exact hCN h'
    · exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 h').1).1
  rw [← Finset.prod_union hBdC, ← Finset.prod_sdiff hsub]
  have h1 : ∏ m ∈ (C ∪ Bd) \ (neutralPart N \ neutralPart R),
      (1 - memberWeight boundary c β m) ≤ 1 :=
    Finset.prod_le_one₀ (fun m hm => by
      have := hθ1 m (hmemN m (Finset.mem_sdiff.1 hm).1); linarith)
      fun m _ => by have := memberWeight_pos (boundary := boundary) c β m; linarith
  have h2 : 0 ≤ ∏ m ∈ neutralPart N \ neutralPart R, (1 - memberWeight boundary c β m) :=
    Finset.prod_nonneg fun m hm => by
      have := hθ1 m (mem_neutralPart.1 (Finset.mem_sdiff.1 hm).1).1; linarith
  calc (∏ m ∈ (C ∪ Bd) \ (neutralPart N \ neutralPart R), (1 - memberWeight boundary c β m)) *
        ∏ m ∈ neutralPart N \ neutralPart R, (1 - memberWeight boundary c β m)
      ≤ 1 * ∏ m ∈ neutralPart N \ neutralPart R, (1 - memberWeight boundary c β m) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

/-- Step 3: the exploration weight of a neutral cluster is at least
`∏_C θ · ½ ∏_{Bd} (1 − θ)` (at most one charged neighbour, of weight `½`). -/
theorem cluster_exploration_ge {c β : ℝ} {N C R : Finset (ChargeDensity L)}
    (hNa : AtMostOneNonNeutral N) (hθ1 : ∀ m ∈ N, memberWeight boundary c β m ≤ 1)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    (∏ m ∈ C, memberWeight boundary c β m) *
        (1 / 2 * ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
          (1 - memberWeight boundary c β m)) ≤
      (∏ m ∈ C, explorationWeight boundary c β m) *
        ∏ m ∈ N \ (C ∪ R), (1 - explorationWeight boundary c β m) := by
  classical
  have hπC : ∏ m ∈ C, explorationWeight boundary c β m = ∏ m ∈ C, memberWeight boundary c β m :=
    Finset.prod_congr rfl fun m hm => by simp only [explorationWeight, hCn m hm, ↓reduceIte]
  rw [hπC]
  refine mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun m _ => (memberWeight_pos (boundary := boundary) c β m).le)
  rw [← Finset.prod_filter_mul_prod_filter_not (N \ (C ∪ R)) (fun m => ∑ j, m j = 0)]
  have h1 : ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
      (1 - explorationWeight boundary c β m) =
      ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0), (1 - memberWeight boundary c β m) :=
    Finset.prod_congr rfl fun m hm => by
      simp only [explorationWeight, (Finset.mem_filter.1 hm).2, ↓reduceIte]
  have h2 : ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0),
      (1 - explorationWeight boundary c β m) =
      (1 / 2) ^ ((N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0)).card := by
    have h2' : ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0),
        (1 - explorationWeight boundary c β m) =
        ∏ _m ∈ (N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0), (1 / 2 : ℝ) :=
      Finset.prod_congr rfl fun m hm => by
        simp only [explorationWeight, (Finset.mem_filter.1 hm).2, ↓reduceIte]
        norm_num
    rw [h2', Finset.prod_const]
  have hcard : ((N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    exact hNa a (Finset.mem_sdiff.1 ha1).1 b (Finset.mem_sdiff.1 hb1).1 ha2 hb2
  have h3 : (1 / 2 : ℝ) ≤ (1 / 2) ^ ((N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0)).card := by
    calc (1 / 2 : ℝ) = (1 / 2) ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  have hB0 : 0 ≤ ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
      (1 - memberWeight boundary c β m) :=
    Finset.prod_nonneg fun m hm => by
      have := hθ1 m (Finset.mem_sdiff.1 (Finset.mem_filter.1 hm).1).1; linarith
  rw [h1, h2, mul_comm]
  exact mul_le_mul_of_nonneg_left h3 hB0

/-- Step 4a: `∏_C θ (1 − θ) ≥ e^{-(c/β)(Σ + 289 A(X)) − Σ}`. -/
theorem cluster_memberWeight_ge (hL : 1 < L) {D₁ : ℝ} (h21 : P21Step boundary L D₁)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNb : IsScaleSeparated boundary L N) {o x : Fin L × Fin L} (hox : o ≠ x) {c β : ℝ}
    (hc : 0 < c) (hβ : 0 < β) (H4 : Real.exp (-(c / β)) ≤ 1 / 32)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N) :
    Real.exp (-(c / β) * (∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2 +
        289 * (chargeCoverCost boundary L
          (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ))) *
        Real.exp (-∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2) ≤
      (∏ m ∈ C, memberWeight boundary c β m) * ∏ m ∈ C, (1 - memberWeight boundary c β m) := by
  classical
  have hL0 : 0 < L := by omega
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hdX := one_le_squareDiameter_markedSupport_dipole (boundary := boundary) hL hox C
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (chargeCoverCost boundary L
      (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ sm : ℝ, sm = ∑ m ∈ C, ∑ j, ((m j : ℤ) : ℝ) ^ 2 := ⟨_, rfl⟩
  rw [← hA, ← hsm]
  have hθle : ∀ m ∈ N, memberWeight boundary c β m ≤ 1 / 32 := fun m hm =>
    (memberWeight_le hc hβ (hens.1 m hm)).trans H4
  have hcover := fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k
  have hsumA : ∑ m ∈ C, Real.logb 2 (chargeDiameter boundary L m + 1) ≤ 289 * A := by
    have h289 := sum_chargeCoverCost_le hL hens hNb hCN
      (fun m hm => chargeSupport_subset_markedSupport_of_mem hm) hdX
    have h289R : (∑ m ∈ C, (chargeCoverCost boundary L m : ℝ)) ≤ 289 * A := by
      rw [hA]; exact_mod_cast h289
    exact (Finset.sum_le_sum fun m hm => (h21 hcover m (hens.1 m (hCN hm))).1).trans h289R
  have hcardC : (C.card : ℝ) ≤ sm := by
    rw [hsm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨j₀, hj₀⟩ : ∃ j, m j ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hens.1 m (hCN hm) (funext h')
    have h1 : (1 : ℝ) ≤ ((m j₀ : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ |((m j₀ : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj₀
      nlinarith [abs_nonneg ((m j₀ : ℤ) : ℝ), sq_abs ((m j₀ : ℤ) : ℝ)]
    exact h1.trans (Finset.single_le_sum (fun j _ => sq_nonneg ((m j : ℤ) : ℝ))
      (Finset.mem_univ j₀))
  have hθC : ∏ m ∈ C, memberWeight boundary c β m = Real.exp (-(c / β) *
      (sm + ∑ m ∈ C, Real.logb 2 (chargeDiameter boundary L m + 1))) := by
    unfold memberWeight
    rw [← Real.exp_sum]
    congr 1
    rw [hsm, ← Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : Real.exp (-(c / β) * (sm + 289 * A)) ≤ ∏ m ∈ C, memberWeight boundary c β m := by
    rw [hθC]
    refine Real.exp_le_exp.2 ?_
    have hcu : 0 ≤ c / β := (div_pos hc hβ).le
    have := mul_le_mul_of_nonneg_left (add_le_add_left hsumA sm) hcu
    linarith
  have h2 : Real.exp (-sm) ≤ ∏ m ∈ C, (1 - memberWeight boundary c β m) := by
    calc Real.exp (-sm) ≤ Real.exp (-(C.card : ℝ)) := Real.exp_le_exp.2 (by linarith)
      _ = (Real.exp (-1)) ^ C.card := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (1 / 2) ^ C.card := by
          refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ _
          have := Real.add_one_le_exp (1 : ℝ)
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          linarith
      _ = ∏ _m ∈ C, (1 / 2 : ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ m ∈ C, (1 - memberWeight boundary c β m) :=
          Finset.prod_le_prod₀ (fun _ _ => by norm_num)
            fun m hm => by have := hθle m (hCN hm); linarith
  exact mul_le_mul h1 h2 (Real.exp_pos _).le
    (Finset.prod_nonneg fun m _ => (memberWeight_pos (boundary := boundary) c β m).le)

/-- Step 4b: the neutral neighbours, `∏_{Bd} (1 − θ) ≥ e^{-2κ|X|}`, `κ = 288 M² e^{-c/β}`. -/
theorem cluster_neighbourWeight_ge (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) {o x : Fin L × Fin L} (hox : o ≠ x)
    {C : Finset (ChargeDensity L)} (hCn : ∀ m ∈ C, ∑ j, m j = 0) {c β : ℝ} (hc : 0 < c)
    (hβ : 0 < β) (H4 : Real.exp (-(c / β)) ≤ 1 / 32) :
    Real.exp (-(2 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) *
        (markedSupport L (dipoleMark o x) C).card)) ≤
      ∏ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
          (fun m => ∑ j, m j = 0), (1 - memberWeight boundary c β m) := by
  have hsumB := sum_neighbourWeight_le (boundary := boundary) hL hens hox hCn hc hβ H4
  have hθle : ∀ m ∈ N, memberWeight boundary c β m ≤ 1 / 32 := fun m hm =>
    (memberWeight_le hc hβ (hens.1 m hm)).trans H4
  calc Real.exp (-(2 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) *
        (markedSupport L (dipoleMark o x) C).card))
      ≤ Real.exp (-(2 * ∑ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
          (fun m => ∑ j, m j = 0), memberWeight boundary c β m)) := by
        refine Real.exp_le_exp.2 ?_
        unfold memberWeight
        linarith
    _ = ∏ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
          (fun m => ∑ j, m j = 0), Real.exp (-(2 * memberWeight boundary c β m)) := by
        rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
        fun m hm => exp_neg_two_mul_le_one_sub (memberWeight_pos (boundary := boundary) c β m).le
          ((hθle m (Finset.mem_sdiff.1 (Finset.mem_filter.1 hm).1).1).trans (by norm_num))

/-- Step 4c: `log₂(|o − x| + 1) ≤ A(X)` (KP P2.1, first half, for the composite support). -/
theorem logb_latticeDistance_le_coverCost (hL : 1 < L) {D₁ : ℝ} (h21 : P21Step boundary L D₁)
    {o x : Fin L × Fin L} (hox : o ≠ x) (C : Finset (ChargeDensity L)) :
    Real.logb 2 (latticeDistance boundary L o x + 1) ≤
      (chargeCoverCost boundary L (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) := by
  have hL0 : 0 < L := by omega
  have hXo : o ∈ markedSupport L (dipoleMark o x) C := chargeSupport_subset_markedSupport _ C
    (mem_chargeSupport'.2 (by simp [dipoleMark, hox]))
  have hXx : x ∈ markedSupport L (dipoleMark o x) C := chargeSupport_subset_markedSupport _ C
    (mem_chargeSupport'.2 (by simp [dipoleMark, Ne.symm hox]))
  have hsp0 : supportProxy (markedSupport L (dipoleMark o x) C) ≠ 0 := by
    intro h0
    have h1 : supportProxy (markedSupport L (dipoleMark o x) C) o = 1 := by
      show (if o ∈ markedSupport L (dipoleMark o x) C then (1 : ℤ) else 0) = 1
      exact ite_eq_left hXo
    rw [h0] at h1
    exact zero_ne_one h1
  have h1 := (h21 (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k)
    (supportProxy (markedSupport L (dipoleMark o x) C)) hsp0).1
  have hdiam : chargeDiameter boundary L (supportProxy (markedSupport L (dipoleMark o x) C)) =
      squareDiameter boundary L (markedSupport L (dipoleMark o x) C) := by
    unfold chargeDiameter
    rw [chargeSupport_supportProxy]
  have h2 : (latticeDistance boundary L o x : ℝ) ≤
      chargeDiameter boundary L (supportProxy (markedSupport L (dipoleMark o x) C)) := by
    rw [hdiam]
    exact_mod_cast latticeDistance_le_squareDiameter_of_mem boundary L _ o x hXo hXx
  refine le_trans ?_ h1
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)

/-- Step 5: the exponent algebra of the cluster estimate (conditions (H1)–(H3)). -/
theorem cluster_exponent_le {D₁ D₂ h c β η A sm nX ℓ κ : ℝ} (hD₁ : 1 ≤ D₁) (hβ : 0 < β)
    (hA : 0 ≤ A) (hsm : 0 ≤ sm) (hnX : 0 ≤ nX) (hℓ : ℓ ≤ A)
    (H1 : β * (h + 1) + c ≤ η ^ 2 / 32) (H2 : 4 * κ ≤ η ^ 2 / (64 * β))
    (H3 : 289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁)) :
    289 * D₂ * A + h * sm - η ^ 2 / β * (nX / 64 + sm / 32 + A / (8192 * D₁)) ≤
      -(η ^ 2 / (16384 * D₁ * β)) * ℓ - c / β * (sm + 289 * A) - sm - 2 * κ * nX -
        2 * κ * nX := by
  have hD₁pos : 0 < D₁ := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / β := ⟨_, rfl⟩
  have hupos : 0 < u := by rw [hu]; positivity
  have hβu : β * u = 1 := by rw [hu]; field_simp
  have e1 : η ^ 2 / β = η ^ 2 * u := by rw [hu]; ring
  have e2 : c / β = c * u := by rw [hu]; ring
  have e3 : η ^ 2 / (16384 * D₁ * β) = η ^ 2 * u / (16384 * D₁) := by rw [hu]; field_simp
  have e4 : η ^ 2 / (64 * β) = η ^ 2 * u / 64 := by rw [hu]; field_simp
  rw [e1, e2, e3]
  rw [e4] at H2
  have H1u : (h + 1) + c * u ≤ η ^ 2 * u / 32 := by
    have := mul_le_mul_of_nonneg_right H1 hupos.le
    have e : (β * (h + 1) + c) * u = (h + 1) * (β * u) + c * u := by ring
    rw [e, hβu, mul_one] at this
    linarith
  have H3u : 289 * D₂ + 289 * (c * u) ≤ η ^ 2 * u / (16384 * D₁) := by
    have := mul_le_mul_of_nonneg_right H3 hupos.le
    have e : (289 * D₂ * β + 289 * c) * u = 289 * D₂ * (β * u) + 289 * (c * u) := by ring
    rw [e, hβu, mul_one] at this
    have e2 : η ^ 2 / (16384 * D₁) * u = η ^ 2 * u / (16384 * D₁) := by ring
    linarith
  have k1 : (h + 1 + c * u - η ^ 2 * u / 32) * sm ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hsm
  have k2 : (289 * D₂ + 289 * (c * u) - η ^ 2 * u / (16384 * D₁)) * A ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hA
  have k3 : (4 * κ - η ^ 2 * u / 64) * nX ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hnX
  have hκB0 : 0 ≤ η ^ 2 * u / (16384 * D₁) := by positivity
  have k4 : η ^ 2 * u / (16384 * D₁) * ℓ ≤ η ^ 2 * u / (16384 * D₁) * A :=
    mul_le_mul_of_nonneg_left hℓ hκB0
  have e5 : η ^ 2 * u * (A / (8192 * D₁)) =
      η ^ 2 * u / (16384 * D₁) * A + η ^ 2 * u / (16384 * D₁) * A := by
    field_simp
    ring
  have e6 : η ^ 2 * u * (nX / 64 + sm / 32 + A / (8192 * D₁)) =
      η ^ 2 * u * nX / 64 + η ^ 2 * u * sm / 32 + η ^ 2 * u * (A / (8192 * D₁)) := by ring
  rw [e6, e5]
  nlinarith [k1, k2, k3, k4]

/-- **The estimate of one neutral cluster** (FS81 (5.31)–(5.33) with the exploration weights).
Let `N` be a KP ensemble with (a), (b) and the activity bound (d), whose site factors satisfy
`∏_{j ∈ supp ϱ} e^{ϱ(j)²} |λ̂_j| ≤ e^{h ‖ϱ‖²}`, and let `C` be a neutral cluster of the dipole
mark. Under the smallness conditions (H1)–(H4) on `c` and `β`, the bound of `abs_markedBranch_le`
for `C` is at most `2 e^{-(η²/(16384 D₁ β)) log₂(|o − x| + 1)}` times the exploration weight
`∏_C π ∏_{∂C} (1 − π)`. -/
theorem cluster_estimate (hL : 1 < L) {D₁ D₂ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h21 : P21Step boundary L D₁) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (K : ChargeDensity L → ℝ) {lamHat : Fin L × Fin L → ℕ → ℝ} {h : ℝ}
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    (hlam : ∀ ϱ ∈ N, ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
      Real.exp (h * ∑ j, (ϱ j : ℝ) ^ 2))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 < η)
    (hηξ : η ≤ dipoleGap ξ) {c β : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (H1 : β * (h + 1) + c ≤ η ^ 2 / 32)
    (H2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ η ^ 2 / (64 * β))
    (H3 : 289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁))
    (H4 : Real.exp (-(c / β)) ≤ 1 / 32)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T)) /
      ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
        (1 - memberWeight boundary c β m) ≤
      2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) *
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
  have h1 := cluster_orientationSum_le hL hD₁ hD₂ h21 hens hNb K hd hlam hox hξ0 hξ1 hη hηξ hβ hC
    hCn
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
  rw [← hX, ← hA, ← hsm] at h1
  rw [← hQC, ← hQB] at h2
  rw [← hPC, ← hQB] at h3
  rw [← hX, ← hA, ← hsm, ← hPC, ← hQC] at h4
  rw [← hκ, ← hX, ← hQB] at h5
  rw [← hX, ← hA, ← hℓ] at h6
  rw [← hκ] at H2
  rw [← hℓ]
  have hA0 : 0 ≤ A := by rw [hA]; exact Nat.cast_nonneg _
  have hsm0 : 0 ≤ sm := by
    rw [hsm]; exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have hexp := cluster_exponent_le (D₂ := D₂) (h := h) hD₁ hβ hA0 hsm0 hnX0 h6 H1 H2 H3
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
  have hnum0 : 0 ≤ ∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
      Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T) :=
    Finset.sum_nonneg fun T _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hE : Real.exp (289 * D₂ * A + h * sm -
        η ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁))) ≤
      Real.exp (-(η ^ 2 / (16384 * D₁ * β)) * ℓ) * (PC * QC) * (QB * QB) := by
    calc Real.exp (289 * D₂ * A + h * sm -
          η ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁)))
        ≤ Real.exp (-(η ^ 2 / (16384 * D₁ * β)) * ℓ) *
            (Real.exp (-(c / β) * (sm + 289 * A)) * Real.exp (-sm)) *
            (Real.exp (-(2 * κ * X.card)) * Real.exp (-(2 * κ * X.card))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          linarith
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le)
          (mul_le_mul h5 h5 (Real.exp_pos _).le hQBpos.le) (by positivity)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hPC0 hQCpos.le))
  calc (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-compositeGain boundary (by omega) ξ η β (dipoleMark o x) C T)) /
        ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
          (1 - memberWeight boundary c β m)
      ≤ Real.exp (289 * D₂ * A + h * sm -
          η ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁))) / (QC * QB) :=
        div_le_div₀ (Real.exp_pos _).le h1 hDpos h2
    _ ≤ 2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) * ℓ) * (PC * (1 / 2 * QB)) := by
        rw [div_le_iff₀ hDpos]
        calc Real.exp (289 * D₂ * A + h * sm -
              η ^ 2 / β * (X.card / 64 + sm / 32 + A / (8192 * D₁)))
            ≤ Real.exp (-(η ^ 2 / (16384 * D₁ * β)) * ℓ) * (PC * QC) * (QB * QB) := hE
          _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

end ClusterEstimate

/-! ### The marked bound on one square domain -/

section DomainBound

variable {boundary : SquareBoundary} {L : ℕ}

/-- The Fourier data of the hard-core weights `1 + 2 z_j cos φ`: `λ̂_j(1) = z_j`, zero above. -/
def hardCoreLamHat (zs : Fin L × Fin L → ℝ) : Fin L × Fin L → ℕ → ℝ :=
  fun j q => if q = 1 then zs j else 0

theorem abs_hardCoreLamHat_le {zs : Fin L × Fin L → ℝ} {zbar : ℝ} (hzs : ∀ j, |zs j| ≤ zbar)
    (hzbar : 0 ≤ zbar) (j : Fin L × Fin L) (q : ℕ) (_hq : 1 ≤ q) :
    |hardCoreLamHat zs j q| ≤ zbar * Real.exp (0 * (q : ℝ) ^ 2) := by
  rw [zero_mul, Real.exp_zero, mul_one]
  unfold hardCoreLamHat
  split_ifs
  · exact hzs j
  · simpa using hzbar

/-- **The renormalized activity bound** (KP (1.14) with constant `c ≤ c₁`, KP §2.3.4) for a
member of a branch of KP T2.2 with hard-core site weights: for every wave with KP's P2.4 energy
bound, `|K(m)| e^{-E_β(a, m)} ≤ θ_m = e^{-(c/β)(‖m‖² + log₂(d(m) + 1))}`. -/
theorem hardCore_renormalizedActivity_le {D₁ D₂ D₃ zbar β₀ c₁ : ℝ}
    (hdamp : ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s → A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 zbar) + 1 + 0 + 0 / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ))
    (h21 : P21Step boundary L D₁) (cover : MinimumCoverSelection boundary L)
    {zs : Fin L × Fin L → ℝ} (hzs : ∀ j, |zs j| ≤ zbar) (hzbar : 0 ≤ zbar)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N) (K : ChargeDensity L → ℝ)
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |hardCoreLamHat zs j (ϱ j).natAbs|)
    {c β : ℝ} (hcc₁ : c ≤ c₁) (hβ : 0 < β) (hββ₀ : β < β₀) {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) :
    ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 + D₃ * separatedSquareTotal boundary L cover m) ≤
        SpinWaves.energyFunctional Λ β a m →
      |K m| * Real.exp (-SpinWaves.energyFunctional Λ β a m) ≤ memberWeight boundary c β m := by
  intro m hm hq a hE
  have hm0 := hens.1 m hm
  obtain ⟨hℓA, hAS⟩ := h21 cover m hm0
  have hK := hd m hm hq
  have hP := prod_exp_sq_mul_abs_le m (hardCoreLamHat zs) zbar 0
    (abs_hardCoreLamHat_le hzs hzbar)
  have hS₀ : (squareCoverNumber boundary L 0 m : ℝ) ≤ ∑ j, (m j : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (squareCoverNumber_zero_le_card boundary L m)).trans
      (card_chargeSupport_le_sum_sq m)
  have hℓ : 0 ≤ Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by
      have := (chargeDiameter boundary L m).cast_nonneg (α := ℝ)
      linarith)
  have hX := hdamp β hβ hββ₀ (∑ j, (m j : ℝ) ^ 2)
    (separatedSquareTotal boundary L cover m) (chargeCoverCost boundary L m)
    (Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1)) (squareCoverNumber boundary L 0 m)
    (Finset.sum_nonneg fun j _ => sq_nonneg _) (Nat.cast_nonneg _) hℓ hℓA hS₀ hAS
  have hs0 : 0 ≤ ∑ j, (m j : ℝ) ^ 2 + Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1) := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (m j : ℝ)
    linarith
  calc |K m| * Real.exp (-SpinWaves.energyFunctional Λ β a m)
      ≤ Real.exp (D₂ * chargeCoverCost boundary L m) *
          Real.exp ((Real.log (max 1 zbar) + 1 + 0) * ∑ j, (m j : ℝ) ^ 2) *
        Real.exp (-(1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 +
          D₃ * separatedSquareTotal boundary L cover m))) := by
        refine mul_le_mul ?_ (Real.exp_le_exp.2 (neg_le_neg hE)) (Real.exp_pos _).le
          (by positivity)
        exact hK.trans (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le)
    _ = Real.exp (D₂ * chargeCoverCost boundary L m +
          (Real.log (max 1 zbar) + 1 + 0 + 0 / β) * ∑ j, (m j : ℝ) ^ 2 -
          1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 +
            D₃ * separatedSquareTotal boundary L cover m)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(c₁ / β) * (∑ j, (m j : ℝ) ^ 2 +
          Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1))) := Real.exp_le_exp.mpr hX
    _ ≤ memberWeight boundary c β m := by
        unfold memberWeight
        refine Real.exp_le_exp.2 ?_
        have : c / β ≤ c₁ / β := div_le_div_of_nonneg_right hcc₁ hβ.le
        nlinarith

theorem sum_mul_dipoleMark (φ : Fin L × Fin L → ℝ) (o x : Fin L × Fin L) :
    ∑ j, φ j * (dipoleMark o x j : ℝ) = φ o - φ x := by
  unfold dipoleMark
  push_cast
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-- **The marked bound on one square domain** (FS81 Theorem B before the limit, CG.s4–s5, for the
hard-core gas). Let the domain carry KP's T2.2, P2.1 and P2.4 with constants `D₂`, `D₁ ≥ 1`,
`D₃`, the damping constants `(β₀, c₁)` of the hard-core weights `|z_j| ≤ z̄`, and let `c ≤ c₁`,
`β < β₀` satisfy (H1)–(H4). Then for the dipole mark at `o ≠ x` and `η ≤ min(ξ, 1 − ξ)`,
`0 < 𝒵 = ∫ ∏_j (1 + 2 z_j cos φ_j) dμ` and
`|∫ cos(ξ(φ_o − φ_x)) ∏_j (1 + 2 z_j cos φ_j) dμ| ≤ 2 e^{-(η²/(16384 D₁ β)) log₂(|o − x| + 1)} 𝒵`.
-/
theorem markedDomain_bound (hL : 1 < L) {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    {D₁ D₂ D₃ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h22 : T22Step boundary L D₂) (h21 : P21Step boundary L D₁) (h24 : P24Step boundary Λ D₃)
    {zbar β₀ c₁ : ℝ} (hzbar : 0 ≤ zbar)
    (hdamp : ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s → A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 zbar) + 1 + 0 + 0 / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ))
    {η c β : ℝ} (hη : 0 < η) (hc : 0 < c) (hcc₁ : c ≤ c₁) (hβ : 0 < β) (hββ₀ : β < β₀)
    (H1 : β * (Real.log (max 1 zbar) + 1 + 0 + 1) + c ≤ η ^ 2 / 32)
    (H2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ η ^ 2 / (64 * β))
    (H3 : 289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁))
    (H4 : Real.exp (-(c / β)) ≤ 1 / 32)
    (v : Fin L × Fin L) (zs : Fin L × Fin L → ℝ) (hzs : ∀ j, |zs j| ≤ zbar)
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hηξ : η ≤ dipoleGap ξ) :
    0 < ∫ φ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂gffLaw Λ hΛ β hβ v ∧
      |∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, (1 + 2 * zs j * Real.cos (φ j))
          ∂gffLaw Λ hΛ β hβ v| ≤
        2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) *
            Real.logb 2 (latticeDistance boundary L o x + 1)) *
          ∫ φ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂gffLaw Λ hΛ β hβ v := by
  classical
  have hL0 : 0 < L := by omega
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  -- KP Theorem 2.2 for the hard-core weights
  obtain ⟨n, N, cc, K, hens, hcpos, hcsum, hid, hprop⟩ := h22 (fun j φ => 1 + 2 * zs j * Real.cos φ)
    (fun _ => 1) (hardCoreLamHat zs) (fun _ => Nat.one_pos)
    (fun j q hq => by unfold hardCoreLamHat; rw [ite_eq_right (by omega)])
    (fun j φ => by
      simp only [Finset.Icc_self, Finset.sum_singleton, hardCoreLamHat, ↓reduceIte, Nat.cast_one,
        one_mul]
      ring)
  -- the center choice and the P2.4 cover selection
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → Λ.IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨v, fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := Λ.exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  obtain ⟨cover, hcov⟩ := h24 centerOf hcenter
  have hws : WaveSelection boundary Λ centerOf cover D₃ := hcov
  -- the branch bounds
  set ε := 2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) *
    Real.logb 2 (latticeDistance boundary L o x + 1)) with hε
  have hθle : ∀ i, ∀ m ∈ N i, memberWeight boundary c β m ≤ 1 / 32 := fun i m hm =>
    (memberWeight_le hc hβ ((hens i).1 m hm)).trans H4
  have hbranch : ∀ i, 0 < ∫ φ, ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ ∧
      |∫ φ, Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ| ≤
        ε * ∫ φ, ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    intro i
    obtain ⟨hNa, hNb, hNc, hd⟩ := hprop i
    have hz := hardCore_renormalizedActivity_le (boundary := boundary) hdamp h21 cover hzs hzbar
      (hens i) (K i) hd hcc₁ hβ hββ₀ Λ
    obtain ⟨hZ, hI⟩ := abs_markedBranch_le hL Λ hΛ hdist B h46 centerOf hcenter cover hws hβ v
      (hens i) hNa hNb hNc (K i) (memberWeight boundary c β)
      (fun m hm => (hθle i m hm).trans_lt (by norm_num)) hz hox hξ0 hξ1 hη.le hηξ
    refine ⟨hZ, hI.trans (mul_le_mul_of_nonneg_right ?_ hZ.le)⟩
    -- the exploration-weight sum
    have hmono := markAdjacent_monotone (boundary := boundary) (dipoleMark_ne_zero hox)
    refine sum_le_of_le_explorationWeight hmono (N i) (explorationWeight boundary c β)
      (fun m hm => ?_) _ fun C hC => ?_
    · unfold explorationWeight
      split_ifs
      · exact (hθle i m hm).trans_lt (by norm_num)
      · norm_num
    · split_ifs with hCn
      · exact cluster_estimate hL hD₁ hD₂ h21 (hens i) hNa hNb (K i) hd
          (fun ϱ _ => prod_exp_sq_mul_abs_le ϱ (hardCoreLamHat zs) zbar 0
            (abs_hardCoreLamHat_le hzs hzbar)) hox hξ0 hξ1 hη hηξ hc hβ H1 H2 H3 H4 hC hCn
      · have hπ0 : ∀ m ∈ N i, 0 ≤ explorationWeight boundary c β m := fun m _ => by
          unfold explorationWeight
          split_ifs
          · exact (memberWeight_pos c β m).le
          · norm_num
        have hπ1 : ∀ m ∈ N i, explorationWeight boundary c β m ≤ 1 := fun m hm => by
          unfold explorationWeight
          split_ifs
          · exact (hθle i m hm).trans (by norm_num)
          · norm_num
        have hCN : C ⊆ N i := (mem_clusters.1 hC).1
        refine mul_nonneg (by positivity) (mul_nonneg
          (Finset.prod_nonneg fun m hm => hπ0 m (hCN hm))
          (Finset.prod_nonneg fun m hm => ?_))
        have := hπ1 m (Finset.mem_sdiff.1 hm).1
        linarith
  -- assemble the branches
  have hlamid : ∀ φ : Fin L × Fin L → ℝ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) =
      ∑ i, cc i * ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) := fun φ => hid φ
  have hint : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := fun i =>
    Reduction.integrable_prod_one_add_mul_cos μ (N i) (K i) (fun m φ => ∑ j, φ j * (m j : ℝ))
      (fun m => by fun_prop)
  have hintc : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := fun i =>
    (hint i).bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hZ : ∫ φ, ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂μ =
      ∑ i, cc i * ∫ φ, ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    simp_rw [hlamid]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hI : ∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, (1 + 2 * zs j * Real.cos (φ j)) ∂μ =
      ∑ i, cc i * ∫ φ, Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    have hpt : ∀ φ : Fin L × Fin L → ℝ,
        Real.cos (ξ * (φ o - φ x)) * ∏ j, (1 + 2 * zs j * Real.cos (φ j)) =
        ∑ i, cc i * (Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) := by
      intro φ
      rw [hlamid, Finset.mul_sum, sum_mul_dipoleMark]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ fun i _ => (hintc i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hcsum
    exact zero_ne_one hcsum
  refine ⟨?_, ?_⟩
  · rw [hZ]
    exact Finset.sum_pos (fun i _ => mul_pos (hcpos i) (hbranch i).1) hn
  · rw [hI, hZ, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hcpos i), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hbranch i).2 (hcpos i).le

end DomainBound

end FroehlichSpencer.BKT.Generic.Marked
