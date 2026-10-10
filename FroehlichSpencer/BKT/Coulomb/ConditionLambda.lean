/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ExpMoment
public import FroehlichSpencer.BKT.Coulomb.Screening
public import FroehlichSpencer.BKT.SpinWaves.SquareGeometry
public import FroehlichSpencer.BKT.Gaussian.IntegerField
import Mathlib.Tactic

/-!
# General Condition-λ Coulomb gases: cutoff gate and FS81 Theorems 5.1 and A

The Fourier series `λ̂(φ) = 1 + 2 ∑ λ(q) cos (q φ)` need
not converge under this growth , so everything is done at a **finite
frequency cutoff** `|q| ≤ N` and the cutoff is removed on the charge side by Gaussian damping.

For Condition λ with `c = 1/16`: `κ (1/16 - ε) > α`.
* `conditionLambda_cutoff_bound`: FS81 Theorems 5.1 and A at every cutoff on the free and even
  periodic squares, from the **** KP Theorem 1.5 with `Γ = max 1 C`, `η = α`,
  `θ = max 0 ε`, uniformly in the volume and the cutoff.
* `conditionLambda_full_bound`: the same **without cutoff** (`FullBoundInternal`): the gate
  (summable weights), `Z_N → Z ≥ 0` and the Theorem 5.1/A inequalities multiplied by `Z`, which is the
  form valid for signed weights.

For `Z > 0` (physical weights: `one_le_fullGasPartition`):
  `FullBoundInternal.expMoment_ge` (Theorem 5.1), `FullBoundInternal.secondMoment_ge` and
  `fullSecondMoment_le` (Theorem A).
* `tendsto_cutoff_expMoment`, `tendsto_cutoff_secondMoment`: the full functionals, defined by
  the representation formulas, are the limits of the cutoff sine-Gordon field functionals
  (FS81 (1.15)–(1.17) without cutoff).
* `gasExpectation_smul`, `fullGasExpectation_smul`: a nonzero vacancy weight `λ(0)` can be
  normalized to `1` without changing expectations ; `λ(0) = 0` is not covered.

FS81's printed (5.39) inequality is not used: at finite cutoff the identities are exact
.

The free-boundary version with FS81's whole-plane potential is
`Coulomb/ConditionLambdaFree.lean`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology MeasureTheory

/-! ### Condition λ and the cutoff coefficient test -/

/-- FS81 Condition λ (J p. 530, (1.11)–(1.12); restated as (5.36), p. 570) at Coulomb inverse
temperature `κ`, with its constants made explicit: `λ` is even and
`|λ(n)| ≤ C e^{(α + ε κ) n²}` for every integer `n`. FS81 require `ε < 1/16`; that margin is a
hypothesis of the theorems below, not of the predicate. Signed weights are allowed (p. 570). -/
def ConditionLambdaInternal (C α ε κ : ℝ) (lam : ℤ → ℝ) : Prop :=
  (∀ n, lam (-n) = lam n) ∧ ∀ n, |lam n| ≤ C * Real.exp ((α + ε * κ) * (n : ℝ) ^ 2)


def PhysicalWeightInternal (lam : ℤ → ℝ) : Prop :=
  lam 0 = 1 ∧ ∀ n, 0 ≤ lam n

theorem ConditionLambdaInternal.const_nonneg {C α ε κ : ℝ} {lam : ℤ → ℝ}
    (h : ConditionLambdaInternal C α ε κ lam) : 0 ≤ C := by
  have := h.2 0
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, mul_one] at this
  exact (abs_nonneg _).trans this

/-- A symmetric window sum of an even function: `∑_{|n| ≤ N} g n = g 0 + 2 ∑_{q=1}^N g q`. -/
theorem sum_Icc_eq_zero_add_two_mul (N : ℕ) (g : ℤ → ℝ) (hg : ∀ n, g (-n) = g n) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g n = g 0 + 2 * ∑ q ∈ Finset.Icc 1 N, g q := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega), ih,
      Finset.sum_Icc_succ_top (by omega), hg]
    push_cast
    ring


theorem isSubGaussian_sineGordonWeight (N : ℕ) {C α ε κ : ℝ} (hκ : 0 < κ) {lam : ℤ → ℝ}
    (hlam : ConditionLambdaInternal C α ε κ lam) (h0 : lam 0 = 1) :
    IsSubGaussian (max 1 C) α (max 0 ε) κ⁻¹ (sineGordonWeightInternal N lam) := by
  refine ⟨N + 1, Nat.succ_pos N, fun q => if q ≤ N then lam q else 0, ?_, ?_, ?_⟩
  · intro q hq
    simp [show ¬ q ≤ N by omega]
  · intro φ
    unfold sineGordonWeightInternal
    rw [sum_Icc_eq_zero_add_two_mul N (fun n => lam n * Real.cos (n * φ)) (fun n => by
      simp only [hlam.1 n, Int.cast_neg, neg_mul, Real.cos_neg]),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one, h0, Int.cast_natCast,
      show ¬ (N + 1 ≤ N) by omega, ite_false, zero_mul, add_zero]
    congr 2
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [(Finset.mem_Icc.1 hq).2, ite_true]
  · intro q _
    dsimp only
    have hRHS : 0 ≤ max 1 C * Real.exp ((α + max 0 ε / κ⁻¹) * (q : ℝ) ^ 2) :=
      mul_nonneg (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le
    split_ifs with hqN
    · have h := hlam.2 q
      push_cast at h
      refine h.trans (mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        (zero_le_one.trans (le_max_left _ _)))
      rw [div_inv_eq_mul]
      have : ε * κ ≤ max 0 ε * κ := mul_le_mul_of_nonneg_right (le_max_right _ _) hκ.le
      nlinarith [sq_nonneg (q : ℝ)]
    · simpa using hRHS

section Region

variable {V : Type*} [DecidableEq V]

/-- Region weights inherit Condition λ, with constant `max 1 C` (the vacuum weight `𝟙[n = 0]`
off the region needs `C ≥ 1`). -/
theorem conditionLambda_regionWeight (A : Finset V) {C α ε κ : ℝ} {lam : ℤ → ℝ}
    (hlam : ConditionLambdaInternal C α ε κ lam) (j : V) :
    ConditionLambdaInternal (max 1 C) α ε κ (regionWeightInternal A lam j) := by
  refine ⟨regionWeight_neg A hlam.1 j, fun n => ?_⟩
  unfold regionWeightInternal
  split_ifs with hj hn
  · exact (hlam.2 n).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  · subst hn
    simp
  · simp only [abs_zero]
    exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le

theorem regionWeight_zero (A : Finset V) {lam : ℤ → ℝ} (h0 : lam 0 = 1) (j : V) :
    regionWeightInternal A lam j 0 = 1 := by
  unfold regionWeightInternal
  split_ifs <;> simp_all

theorem regionWeight_nonneg (A : Finset V) {lam : ℤ → ℝ} (hnn : ∀ n, 0 ≤ lam n) (j : V) (n : ℤ) :
    0 ≤ regionWeightInternal A lam j n := by
  unfold regionWeightInternal
  split_ifs
  · exact hnn n
  · exact zero_le_one
  · exact le_rfl

end Region

/-! ### The neutral energy is coercive on graphs of degree at most four -/

section Energy

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

/-- `‖Δ g‖² ≤ 8 ‖∇ g‖²` on a multigraph whose vertices carry at most four edge ends. -/
theorem sum_laplacian_sq_le (G : Multigraph V E)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4) (g : V → ℝ) :
    ∑ j, G.laplacian g j ^ 2 ≤ 8 * ∑ e, (g (G.src e) - g (G.tgt e)) ^ 2 := by
  classical
  set ind : E → V → ℝ := fun e j =>
    (if G.src e = j then 1 else 0) + (if G.tgt e = j then 1 else 0) with hind
  set a : E → V → ℝ := fun e j => (if G.src e = j then g (G.tgt e) - g j else 0) +
      (if G.tgt e = j then g (G.src e) - g j else 0) with ha
  have hcase : ∀ e j, ind e j * a e j = a e j ∧
      a e j ^ 2 = ind e j * (g (G.src e) - g (G.tgt e)) ^ 2 ∧ ind e j ^ 2 = ind e j := by
    intro e j
    have hne := G.src_ne_tgt e
    by_cases hs : G.src e = j
    · have ht : G.tgt e ≠ j := fun h => hne (hs.trans h.symm)
      simp only [hind, ha, hs, ht, ite_true, ite_false]
      refine ⟨by ring, by ring, by ring⟩
    · by_cases ht : G.tgt e = j
      · simp only [hind, ha, hs, ht, ite_true, ite_false]
        refine ⟨by ring, by ring, by ring⟩
      · simp only [hind, ha, hs, ht, ite_false]
        refine ⟨by ring, by ring, by ring⟩
  have hj : ∀ j, G.laplacian g j ^ 2 ≤
      4 * ∑ e, ind e j * (g (G.src e) - g (G.tgt e)) ^ 2 := by
    intro j
    have hlap : G.laplacian g j = ∑ e, ind e j * a e j := by
      unfold Multigraph.laplacian
      exact Finset.sum_congr rfl fun e _ => ((hcase e j).1).symm
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun e => ind e j) (fun e => a e j)
    have hcard : ∑ e, ind e j ^ 2 ≤ 4 := by
      simp_rw [(hcase _ j).2.2]
      simp only [hind, Finset.sum_add_distrib, Finset.sum_boole]
      exact_mod_cast hdeg j
    rw [hlap]
    calc _ ≤ (∑ e, ind e j ^ 2) * ∑ e, a e j ^ 2 := hcs
      _ ≤ 4 * ∑ e, a e j ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = _ := by simp_rw [(hcase _ j).2.1]
  have h2 : ∀ e, ∑ j, ind e j = 2 := by
    intro e
    simp only [hind, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    norm_num
  calc ∑ j, G.laplacian g j ^ 2
      ≤ ∑ j, 4 * ∑ e, ind e j * (g (G.src e) - g (G.tgt e)) ^ 2 :=
        Finset.sum_le_sum fun j _ => hj j
    _ = 4 * ∑ e, (∑ j, ind e j) * (g (G.src e) - g (G.tgt e)) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = 8 * ∑ e, (g (G.src e) - g (G.tgt e)) ^ 2 := by
        simp_rw [h2]
        rw [← Finset.mul_sum]
        ring

/-- **The neutral energy is coercive** (the finite-volume form of FS81 (5.44), `E₀ = ‖ρ‖²/8`
for the self-energy part): on a connected multigraph whose vertices carry at most four edge
ends, `E(q) ≥ ‖q‖² / 16` for every neutral integer charge and every Laplacian pseudoinverse. -/
theorem chargeEnergy_ge_of_degree (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T) (q : V → ℤ)
    (hq : ∑ j, q j = 0) :
    (∑ j, (q j : ℝ) ^ 2) / 16 ≤ chargeEnergyInternal T q := by
  set qr : V → ℝ := fun j => (q j : ℝ) with hqr
  have hsum : ∑ j, qr j = 0 := by simp only [hqr]; exact_mod_cast hq
  set g : V → ℝ := -(T qr) with hg
  have hlap : -G.laplacian g = qr := by
    have h1 := (hT.1 qr hsum).1
    have h2 : G.laplacian g = -G.laplacian (T qr) := (G.laplacianₗ ℝ).map_neg (T qr)
    rw [h2, h1, neg_neg]
  obtain ⟨m, -, hD⟩ := neg_pseudoinverse_neg_laplacian G hG T hT g
  rw [hlap] at hD
  have hD' : ∑ j, qr j * -(T qr j) = ∑ e, (g (G.src e) - g (G.tgt e)) ^ 2 := by
    rw [← hD]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← congrFun hlap j]
    rfl
  have hsq : ∑ j, qr j ^ 2 ≤ 8 * ∑ e, (g (G.src e) - g (G.tgt e)) ^ 2 := by
    have h := sum_laplacian_sq_le G hdeg g
    have e : ∀ j, G.laplacian g j ^ 2 = qr j ^ 2 := fun j => by
      rw [← congrFun hlap j, Pi.neg_apply, neg_sq]
    simpa only [e] using h
  unfold chargeEnergyInternal
  change (∑ j, qr j ^ 2) / 16 ≤ (∑ j, qr j * -(T qr j)) / 2
  rw [hD']
  linarith

end Energy

/-! ### The summability gate and the cutoff limit -/

section Gate

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem intGaussianPiV_eq (b : ℝ) (q : V → ℤ) :
    intGaussianPiV V b q = Real.exp (-(b * ∑ j, (q j : ℝ) ^ 2)) := by
  unfold intGaussianPiV
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

omit [DecidableEq V] in
/-- The Gaussian domination of the full gas weight: if the neutral energy is `c`-coercive and
`|λ_j(n)| ≤ C e^{a n²}`, then `|w(q)| ≤ C^{|V|} ∏_j e^{-(κ c - a) q_j²}`. -/
theorem abs_gasWeight_le (T : (V → ℝ) →ₗ[ℝ] V → ℝ) {κ c a C : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (lam : V → ℤ → ℝ)
    (hE : ∀ q : V → ℤ, ∑ j, q j = 0 → c * ∑ j, (q j : ℝ) ^ 2 ≤ chargeEnergyInternal T q)
    (hlam : ∀ j n, |lam j n| ≤ C * Real.exp (a * (n : ℝ) ^ 2)) (q : V → ℤ) :
    |gasWeightInternal T κ lam q| ≤ C ^ Fintype.card V * intGaussianPiV V (κ * c - a) q := by
  unfold gasWeightInternal
  split_ifs with hq
  · rw [abs_mul, Real.abs_exp, Finset.abs_prod]
    have h1 : ∏ j, |lam j (q j)| ≤ ∏ j, (C * Real.exp (a * (q j : ℝ) ^ 2)) :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => hlam j (q j)
    have h2 : Real.exp (-κ * chargeEnergyInternal T q) ≤
        Real.exp (-(κ * c * ∑ j, (q j : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left (hE q hq) hκ
      linarith
    calc _ ≤ (∏ j, (C * Real.exp (a * (q j : ℝ) ^ 2))) *
          Real.exp (-(κ * c * ∑ j, (q j : ℝ) ^ 2)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => by positivity)
      _ = C ^ Fintype.card V * intGaussianPiV V (κ * c - a) q := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, intGaussianPiV_eq,
            ← Real.exp_sum, mul_assoc, ← Real.exp_add]
          congr 2
          rw [← Finset.mul_sum]
          ring
  · simp only [abs_zero]
    exact mul_nonneg (pow_nonneg hC _) (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)

/-- `(1 + t) e^{-b t} ≤ (1 + 2/b) e^{-b t/2}` for `t ≥ 0`, `b > 0`. -/
theorem one_add_mul_exp_le {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-(b * t)) ≤ (1 + 2 / b) * Real.exp (-(b / 2 * t)) := by
  have hsplit : Real.exp (-(b * t)) = Real.exp (-(b / 2 * t)) * Real.exp (-(b / 2 * t)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hexp : 1 + b / 2 * t ≤ Real.exp (b / 2 * t) := by
    have := Real.add_one_le_exp (b / 2 * t); linarith
  have hinv : Real.exp (-(b / 2 * t)) = (Real.exp (b / 2 * t))⁻¹ := Real.exp_neg _
  rw [hinv, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have h2b : 0 < 1 + 2 / b := by positivity
  calc 1 + t ≤ (1 + 2 / b) * (1 + b / 2 * t) := by
        field_simp
        nlinarith [mul_nonneg hb.le ht, mul_nonneg (mul_nonneg hb.le hb.le) ht]
    _ ≤ (1 + 2 / b) * Real.exp (b / 2 * t) := mul_le_mul_of_nonneg_left hexp h2b.le

omit [DecidableEq V] in
/-- **The summability gate** : under `c`-coercivity of the neutral energy and
growth `|λ_j(n)| ≤ C e^{a n²}` with `a < κ c`, the full gas weights times any observable of
quadratic growth are absolutely summable over all integer configurations. -/
theorem summable_gasWeight_mul (T : (V → ℝ) →ₗ[ℝ] V → ℝ) {κ c a C : ℝ} (hκ : 0 ≤ κ)
    (hC : 0 ≤ C) (lam : V → ℤ → ℝ)
    (hE : ∀ q : V → ℤ, ∑ j, q j = 0 → c * ∑ j, (q j : ℝ) ^ 2 ≤ chargeEnergyInternal T q)
    (hlam : ∀ j n, |lam j n| ≤ C * Real.exp (a * (n : ℝ) ^ 2)) (hac : a < κ * c)
    (F : (V → ℤ) → ℝ) (B : ℝ) (hF : ∀ q, |F q| ≤ B * (1 + ∑ j, (q j : ℝ) ^ 2)) :
    Summable fun q => gasWeightInternal T κ lam q * F q := by
  set b := κ * c - a with hb
  have hbpos : 0 < b := by rw [hb]; linarith
  have hB : 0 ≤ B := by
    have := hF 0
    simp only [Pi.zero_apply, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, add_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  refine Summable.of_norm_bounded
    ((summable_intGaussianPiV V (half_pos hbpos)).mul_left
      (C ^ Fintype.card V * B * (1 + 2 / b))) fun q => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have ht : 0 ≤ ∑ j, (q j : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc |gasWeightInternal T κ lam q| * |F q|
      ≤ (C ^ Fintype.card V * intGaussianPiV V b q) * (B * (1 + ∑ j, (q j : ℝ) ^ 2)) :=
        mul_le_mul (abs_gasWeight_le T hκ hC lam hE hlam q) (hF q) (abs_nonneg _)
          (mul_nonneg (pow_nonneg hC _) (by unfold intGaussianPiV; positivity))
    _ = C ^ Fintype.card V * B * ((1 + ∑ j, (q j : ℝ) ^ 2) *
          Real.exp (-(b * ∑ j, (q j : ℝ) ^ 2))) := by
        rw [intGaussianPiV_eq]; ring
    _ ≤ C ^ Fintype.card V * B * ((1 + 2 / b) *
          Real.exp (-(b / 2 * ∑ j, (q j : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left (one_add_mul_exp_le hbpos ht)
          (mul_nonneg (pow_nonneg hC _) hB)
    _ = C ^ Fintype.card V * B * (1 + 2 / b) * intGaussianPiV V (b / 2) q := by
        rw [intGaussianPiV_eq]; ring

/-- The charge windows `|q_j| ≤ N` exhaust all integer configurations. -/
theorem tendsto_chargeConfigs_atTop :
    Tendsto (chargeConfigsInternal V) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun N M h => ?_) fun q => ?_
  · exact Fintype.piFinset_subset _ _ fun _ => Finset.Icc_subset_Icc (by omega) (by omega)
  · refine ⟨∑ j, (q j).natAbs, ?_⟩
    simp only [chargeConfigsInternal, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have := Finset.single_le_sum (f := fun j => (q j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    omega

/-- Cutoff sums of a summable family converge to its sum as the cutoff is removed. -/
theorem tendsto_sum_chargeConfigs {F : (V → ℤ) → ℝ} (hF : Summable F) :
    Tendsto (fun N => ∑ q ∈ chargeConfigsInternal V N, F q) atTop (𝓝 (∑' q, F q)) :=
  hF.hasSum.comp tendsto_chargeConfigs_atTop

omit [DecidableEq V] in
/-- Cauchy–Schwarz for the charge pairing, in the quadratic-growth form of the gate. -/
theorem sq_pairing_le (h : V → ℝ) (q : V → ℤ) :
    (∑ j, (q j : ℝ) * h j) ^ 2 ≤ (∑ j, h j ^ 2) * (1 + ∑ j, (q j : ℝ) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => (q j : ℝ)) h
  have h0 : 0 ≤ ∑ j, h j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

end Gate

/-!
### FS81 Theorems 5.1 and A at every frequency cutoff, from the KP Theorem 1.5
-/

section Cutoff

variable {W : Type*} [Fintype W] [DecidableEq W] {E : Type*} [Fintype E]

/-- The conclusion of FS81 Theorems 5.1 and A for the gas `(T, κ, λ)` at frequency cutoff `N`:
`Z_N > 0` and, for every zero-sum `f`, `⟨cos (u κ ⟨q, C f⟩)⟩_N ≥ e^{-δ κ ⟨f, C f⟩ u²/2}` and
`⟨(κ ⟨q, C f⟩)²⟩_N ≤ δ κ ⟨f, C f⟩`, with `C = -T`. -/
def CutoffBoundInternal (N : ℕ) (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (κ δ : ℝ) (lam : W → ℤ → ℝ) : Prop :=
  0 < gasPartitionInternal N T κ lam ∧
    ∀ f : W → ℝ, ∑ j, f j = 0 →
      (∀ u : ℝ, Real.exp (-(δ * κ * (∑ j, f j * -(T f j)) / 2) * u ^ 2) ≤
        gasExpectationInternal N T κ lam
          (fun q => Real.cos (u * (κ * ∑ j, (q j : ℝ) * -(T f j))))) ∧
      gasExpectationInternal N T κ lam (fun q => (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2) ≤
        δ * κ * ∑ j, f j * -(T f j)

/-- `CutoffBoundInternal` multiplied through by `Z_N`, the form that survives limits of signed
weights: `Z_N ≥ 0`, `e^{-δ κ ⟨f,Cf⟩ u²/2} Z_N ≤ ∑_{|q| ≤ N} w(q) cos (u κ ⟨q, C f⟩)` and
`∑_{|q| ≤ N} w(q) (κ ⟨q, C f⟩)² ≤ δ κ ⟨f, C f⟩ Z_N`. -/
def CutoffSumBoundInternal (N : ℕ) (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (κ δ : ℝ) (lam : W → ℤ → ℝ) :
    Prop :=
  0 ≤ gasPartitionInternal N T κ lam ∧
    ∀ f : W → ℝ, ∑ j, f j = 0 →
      (∀ u : ℝ, Real.exp (-(δ * κ * (∑ j, f j * -(T f j)) / 2) * u ^ 2) *
          gasPartitionInternal N T κ lam ≤
        ∑ q ∈ chargeConfigsInternal W N, gasWeightInternal T κ lam q *
          Real.cos (u * (κ * ∑ j, (q j : ℝ) * -(T f j)))) ∧
      ∑ q ∈ chargeConfigsInternal W N,
          gasWeightInternal T κ lam q * (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2 ≤
        δ * κ * (∑ j, f j * -(T f j)) * gasPartitionInternal N T κ lam

omit [Fintype E] in
theorem CutoffBoundInternal.toSum {N : ℕ} {T : (W → ℝ) →ₗ[ℝ] W → ℝ} {κ δ : ℝ}
    {lam : W → ℤ → ℝ} (h : CutoffBoundInternal N T κ δ lam) : CutoffSumBoundInternal N T κ δ lam := by
  refine ⟨h.1.le, fun f hf => ⟨fun u => ?_, ?_⟩⟩
  · have h1 := (h.2 f hf).1 u
    unfold gasExpectationInternal at h1
    rwa [le_div_iff₀ h.1] at h1
  · have h1 := (h.2 f hf).2
    unfold gasExpectationInternal at h1
    rwa [div_le_iff₀ h.1] at h1

/-- `CutoffBoundInternal` on one domain, uniformly in `κ > κ₀`, in the normalized
Condition-λ weights with constants `(C, α, ε)`, in the cutoff and in the pseudoinverse. -/
def ConditionLambdaCutoffBoundInternal (Λ : Multigraph W E) (δ C α ε κ₀ : ℝ) : Prop :=
  ∀ κ : ℝ, κ₀ < κ → ∀ lam : W → ℤ → ℝ, (∀ j, ConditionLambdaInternal C α ε κ (lam j)) →
    (∀ j, lam j 0 = 1) → ∀ (N : ℕ) (T : (W → ℝ) →ₗ[ℝ] W → ℝ), Λ.IsLaplacianPseudoinverse T →
      CutoffBoundInternal N T κ δ lam

/-- `⟨f, C f⟩ ≥ 0` for zero-sum `f`. -/
theorem pairing_neg_pseudoinverse_nonneg (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected)
    (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (hT : Λ.IsLaplacianPseudoinverse T) (f : W → ℝ)
    (hf : ∑ j, f j = 0) : 0 ≤ ∑ j, f j * -(T f j) := by
  have hTg : T = Λ.greenOp hΛ := Λ.greenOp_unique hΛ T hT.1 hT.2
  have := Λ.pairing_greenOp_nonneg hΛ f hf
  rw [hTg]
  simpa [Multigraph.pairing] using this

/-- Transfer of KP Theorem 1.5 (with `Γ = max 1 C`, `η = α`, `θ = max 0 ε`, `ε_KP = δ`) to the
cutoff Condition-λ gas on one domain. -/
theorem conditionLambdaCutoffBound_of_kp (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected)
    (δ : ℝ) (hδ : 0 < δ) (C α ε β₀ : ℝ) (hβ₀ : 0 < β₀)
    (H : ∀ (v : W) (β : ℝ) (hβ : 0 < β), β < β₀ →
      ∀ lam : W → ℝ → ℝ, (∀ j, IsSubGaussian (max 1 C) α (max 0 ε) β (lam j)) →
        0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) ∧
        ∀ T : (W → ℝ) →ₗ[ℝ] W → ℝ, Λ.IsLaplacianPseudoinverse T →
          ∀ f : W → ℝ, ∑ j, f j = 0 →
            Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + δ) * β)) ≤
              (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) /
                ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) :
    ConditionLambdaCutoffBoundInternal Λ δ C α ε β₀⁻¹ := by
  intro κ hκ₀ lam hlam h0 N T hT
  have hκ : 0 < κ := (inv_pos.2 hβ₀).trans hκ₀
  have hβ : κ⁻¹ < β₀ := (inv_lt_comm₀ hκ hβ₀).2 hκ₀
  obtain ⟨v⟩ := hΛ.nonempty
  have hev : ∀ j n, lam j (-n) = lam j n := fun j => (hlam j).1
  obtain ⟨hZ, hbd⟩ := H v κ⁻¹ (inv_pos.2 hκ) hβ (fun j => sineGordonWeightInternal N (lam j))
    (fun j => isSubGaussian_sineGordonWeight N hκ (hlam j) (h0 j))
  have hZ' : 0 < gasPartitionInternal N T κ lam := by
    rw [← weightedGFFNormalizer_sineGordon Λ hΛ κ hκ v N lam hev T hT]
    exact hZ
  refine ⟨hZ', fun f hf => ?_⟩
  have hQnn := pairing_neg_pseudoinverse_nonneg Λ hΛ T hT f hf
  have hlow : ∀ u : ℝ, Real.exp (u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2) ≤
      weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j))
        (fun φ => Real.exp (u * ∑ j, φ j * f j)) := by
    intro u
    have huf : ∑ j, (u • f) j = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hf, mul_zero]
    have h := hbd T hT (u • f) huf
    have hQ : ∑ j, (u • f) j * -(T (u • f) j) = u ^ 2 * ∑ j, f j * -(T f j) := by
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hratio : (∫ φ, Real.exp (∑ j, φ j * (u • f) j) *
          ∏ j, sineGordonWeightInternal N (lam j) (φ j) ∂(gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v)) /
        ∫ φ, ∏ j, sineGordonWeightInternal N (lam j) (φ j)
          ∂(gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v) =
        weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
          (fun j => sineGordonWeightInternal N (lam j))
          (fun φ => Real.exp (u * ∑ j, φ j * f j)) := by
      rw [weightedGFFExpectation_eq]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun φ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hQ, hratio] at h
    refine le_trans ?_ h
    apply Real.exp_le_exp.2
    obtain ⟨P, hP⟩ : ∃ P, P = u ^ 2 * κ * ∑ j, f j * -(T f j) := ⟨_, rfl⟩
    have hPnn : 0 ≤ P := by rw [hP]; positivity
    have hlhs : u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2 = P * (1 - δ) / 2 := by
      rw [hP]; ring
    have hrhs : u ^ 2 * (∑ j, f j * -(T f j)) / (2 * (1 + δ) * κ⁻¹) = P / (2 * (1 + δ)) := by
      rw [hP]; field_simp
    rw [hlhs, hrhs, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hPnn (sq_nonneg δ)]
  refine ⟨fun u => ?_,
    gasExpectation_sq_le_of_expMoment Λ hΛ κ hκ v N lam hev T hT f hf δ hZ'.ne' hlow⟩
  have h1 := hlow u
  rw [weightedGFFExpectation_exp_mul_sineGordon Λ hΛ κ hκ v N lam hev T hT f hf u] at h1
  have hpos := Real.exp_pos (κ * (∑ j, f j * -(T f j)) / 2 * u ^ 2)
  rw [show -(δ * κ * (∑ j, f j * -(T f j)) / 2) * u ^ 2 =
      u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2 - κ * (∑ j, f j * -(T f j)) / 2 * u ^ 2 by
    ring, Real.exp_sub, div_le_iff₀ hpos]
  exact h1.trans_eq (mul_comm _ _)

/--
**FS81 Theorems 5.1 and A for Condition-λ gases at every frequency cutoff** (J pp. 570–572),
on the free square and on the even periodic square: for `δ > 0` and constants `(C, α, ε)` with
`ε < 1/16` there is `κ₀`, independent of the volume and of the cutoff, such that
`CutoffBoundInternal` holds for `κ > κ₀`.
-/
theorem conditionLambda_cutoff_bound (δ : ℝ) (hδ : 0 < δ) (C α ε : ℝ) (hε : ε < 1 / 16) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ (L : ℕ) (_ : 1 < L),
      ConditionLambdaCutoffBoundInternal (squareFree L) δ C α ε κ₀ ∧
        (Even L → ConditionLambdaCutoffBoundInternal (squarePeriodic L) δ C α ε κ₀) := by
  obtain ⟨β₀, hβ₀, H⟩ := weightedGFF_expMoment_lower_bound (max 1 C)
    (zero_lt_one.trans_le (le_max_left _ _)) α (max 0 ε) (le_max_left _ _)
    (max_lt (by norm_num) hε) δ hδ
  refine ⟨β₀⁻¹, inv_pos.2 hβ₀, fun L hL => ?_⟩
  have h := H L hL
  dsimp only at h
  exact ⟨conditionLambdaCutoffBound_of_kp _ _ δ hδ C α ε β₀ hβ₀ h.1,
    fun he => conditionLambdaCutoffBound_of_kp _ _ δ hδ C α ε β₀ hβ₀ (h.2 he)⟩

end Cutoff

/-! ### Removing the frequency cutoff -/

section Full

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- FS81 (1.8) without frequency cutoff: `Z = ∑_q w(q)` over **all** integer configurations.
Every theorem using it first proves summability (`summable_gasWeight_mul`) and identifies it as
the limit of the cutoff partition functions (`tendsto_gasPartition_cutoff`). -/
def fullGasPartitionInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) : ℝ :=
  ∑' q : V → ℤ, gasWeightInternal T κ lam q

/-- FS81 (1.9) without frequency cutoff. -/
def fullGasExpectationInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (F : (V → ℤ) → ℝ) : ℝ :=
  (∑' q : V → ℤ, gasWeightInternal T κ lam q * F q) / fullGasPartitionInternal T κ lam

/-- FS81 (5.6)/(5.12) for the Condition-λ gas: the sine-Gordon functional `⟨e^{u φ(f)}⟩`, defined
by the representation formula and identified with the limit of the cutoff sine-Gordon
functionals in `tendsto_cutoff_expMoment`. -/
def fullExpMomentInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) (f : V → ℝ)
    (u : ℝ) : ℝ :=
  Real.exp (κ * (∑ j, f j * -(T f j)) / 2 * u ^ 2) *
    fullGasExpectationInternal T κ lam (fun q => Real.cos (u * (κ * ∑ j, (q j : ℝ) * -(T f j))))

/-- FS81 (1.17) for the Condition-λ gas: `⟨φ(f)²⟩ = κ ⟨f, C f⟩ - ⟨(κ ⟨q, C f⟩)²⟩`, identified with
the limit of the cutoff second moments in `tendsto_cutoff_secondMoment`. -/
def fullSecondMomentInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (f : V → ℝ) : ℝ :=
  κ * (∑ j, f j * -(T f j)) -
    fullGasExpectationInternal T κ lam (fun q => (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2)

/-- The hypotheses of the summability gate for `(T, κ, λ)`: `c`-coercive neutral energy and
growth `|λ_j(n)| ≤ C e^{a n²}` with `C ≥ 0`, `κ ≥ 0` and `a < κ c`. -/
def GateInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) : Prop :=
  0 ≤ κ ∧ ∃ c a C : ℝ, 0 ≤ C ∧ a < κ * c ∧
    (∀ q : V → ℤ, ∑ j, q j = 0 → c * ∑ j, (q j : ℝ) ^ 2 ≤ chargeEnergyInternal T q) ∧
    ∀ j n, |lam j n| ≤ C * Real.exp (a * (n : ℝ) ^ 2)

omit [DecidableEq V] in
theorem GateInternal.summable_mul {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ}
    (h : GateInternal T κ lam) (F : (V → ℤ) → ℝ) (B : ℝ)
    (hF : ∀ q, |F q| ≤ B * (1 + ∑ j, (q j : ℝ) ^ 2)) :
    Summable fun q => gasWeightInternal T κ lam q * F q := by
  obtain ⟨hκ, c, a, C, hC, hac, hE, hlam⟩ := h
  exact summable_gasWeight_mul T hκ hC lam hE hlam hac F B hF

omit [DecidableEq V] in
theorem GateInternal.summable {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ}
    (h : GateInternal T κ lam) : Summable (gasWeightInternal T κ lam) := by
  have := h.summable_mul (fun _ => 1) 1 fun q => by
    have : 0 ≤ ∑ j, (q j : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [abs_one, one_mul]
    linarith
  simpa only [mul_one] using this

omit [DecidableEq V] in
/-- Observables of quadratic growth: bounded ones and squared charge pairings. -/
theorem abs_cos_le_quadratic (x : ℝ) (q : V → ℤ) :
    |Real.cos x| ≤ 1 * (1 + ∑ j, (q j : ℝ) ^ 2) := by
  have : 0 ≤ ∑ j, (q j : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have := Real.abs_cos_le_one x
  linarith

omit [DecidableEq V] in
theorem abs_sq_pairing_le_quadratic (κ : ℝ) (h : V → ℝ) (q : V → ℤ) :
    |(κ * ∑ j, (q j : ℝ) * h j) ^ 2| ≤ κ ^ 2 * (∑ j, h j ^ 2) * (1 + ∑ j, (q j : ℝ) ^ 2) := by
  rw [abs_of_nonneg (sq_nonneg _), mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (sq_pairing_le h q) (sq_nonneg κ)

/-- **Cutoff removal for the partition function**: `Z_N → Z`. -/
theorem tendsto_gasPartition_cutoff {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ}
    (h : GateInternal T κ lam) :
    Tendsto (fun N => gasPartitionInternal N T κ lam) atTop
      (𝓝 (fullGasPartitionInternal T κ lam)) :=
  tendsto_sum_chargeConfigs h.summable

/-- **Cutoff removal for weighted sums** of observables of quadratic growth. -/
theorem tendsto_gasSum_cutoff {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ}
    (h : GateInternal T κ lam) (F : (V → ℤ) → ℝ) (B : ℝ)
    (hF : ∀ q, |F q| ≤ B * (1 + ∑ j, (q j : ℝ) ^ 2)) :
    Tendsto (fun N => ∑ q ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam q * F q) atTop
      (𝓝 (∑' q, gasWeightInternal T κ lam q * F q)) :=
  tendsto_sum_chargeConfigs (h.summable_mul F B hF)

/-- **Cutoff removal for expectations** (`Z ≠ 0`). -/
theorem tendsto_gasExpectation_cutoff {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ}
    (h : GateInternal T κ lam) (hZ : fullGasPartitionInternal T κ lam ≠ 0)
    (F : (V → ℤ) → ℝ) (B : ℝ) (hF : ∀ q, |F q| ≤ B * (1 + ∑ j, (q j : ℝ) ^ 2)) :
    Tendsto (fun N => gasExpectationInternal N T κ lam F) atTop
      (𝓝 (fullGasExpectationInternal T κ lam F)) :=
  (tendsto_gasSum_cutoff h F B hF).div (tendsto_gasPartition_cutoff h) hZ

/-- The conclusion of FS81 Theorems 5.1 and A for the full (cutoff-free) gas `(T, κ, λ)`,
multiplied through by `Z` so that it holds for signed weights as well: the summability gate
holds (so `w` times any observable of quadratic growth is summable, `GateInternal.summable_mul`),
`Z_N → Z ≥ 0`, and for zero-sum `f`,
`e^{-δ κ ⟨f,Cf⟩ u²/2} Z ≤ ∑_q w(q) cos (u κ ⟨q, C f⟩)` and
`∑_q w(q) (κ ⟨q, C f⟩)² ≤ δ κ ⟨f, C f⟩ Z`. -/
def FullBoundInternal (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ δ : ℝ) (lam : V → ℤ → ℝ) : Prop :=
  GateInternal T κ lam ∧
    Tendsto (fun N => gasPartitionInternal N T κ lam) atTop
      (𝓝 (fullGasPartitionInternal T κ lam)) ∧
    0 ≤ fullGasPartitionInternal T κ lam ∧
    ∀ f : V → ℝ, ∑ j, f j = 0 →
      (∀ u : ℝ, Real.exp (-(δ * κ * (∑ j, f j * -(T f j)) / 2) * u ^ 2) *
          fullGasPartitionInternal T κ lam ≤
        ∑' q, gasWeightInternal T κ lam q *
          Real.cos (u * (κ * ∑ j, (q j : ℝ) * -(T f j)))) ∧
      ∑' q, gasWeightInternal T κ lam q * (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2 ≤
        δ * κ * (∑ j, f j * -(T f j)) * fullGasPartitionInternal T κ lam

/-- **Cutoff removal for FS81 Theorems 5.1 and A**: the cutoff bounds at every `N` (in the
multiplied form) and the summability gate give the full bound. -/
theorem fullBound_of_cutoffSum {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ δ : ℝ} {lam : V → ℤ → ℝ}
    (h : GateInternal T κ lam) (hcut : ∀ N, CutoffSumBoundInternal N T κ δ lam) :
    FullBoundInternal T κ δ lam := by
  have hZ := tendsto_gasPartition_cutoff h
  refine ⟨h, hZ, ge_of_tendsto' hZ fun N => (hcut N).1, fun f hf => ⟨fun u => ?_, ?_⟩⟩
  · exact le_of_tendsto_of_tendsto' (hZ.const_mul _)
      (tendsto_gasSum_cutoff h _ 1 fun q => abs_cos_le_quadratic _ q)
      fun N => ((hcut N).2 f hf).1 u
  · exact le_of_tendsto_of_tendsto'
      (tendsto_gasSum_cutoff h _ _ fun q => abs_sq_pairing_le_quadratic κ (fun j => -(T f j)) q)
      (hZ.const_mul _) fun N => ((hcut N).2 f hf).2

/-- FS81 Theorem 5.1 for the full gas, normalized (`Z > 0`):
`⟨e^{u φ(f)}⟩ ≥ exp (u² κ (1 - δ) ⟨f, C f⟩ / 2)`. -/
theorem FullBoundInternal.expMoment_ge {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ δ : ℝ}
    {lam : V → ℤ → ℝ} (h : FullBoundInternal T κ δ lam)
    (hZ : 0 < fullGasPartitionInternal T κ lam) (f : V → ℝ) (hf : ∑ j, f j = 0) (u : ℝ) :
    Real.exp (u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2) ≤
      fullExpMomentInternal T κ lam f u := by
  have h1 := (h.2.2.2 f hf).1 u
  unfold fullExpMomentInternal fullGasExpectationInternal
  rw [← le_div_iff₀ hZ] at h1
  calc Real.exp (u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2)
      = Real.exp (κ * (∑ j, f j * -(T f j)) / 2 * u ^ 2) *
          Real.exp (-(δ * κ * (∑ j, f j * -(T f j)) / 2) * u ^ 2) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

/-- FS81 Theorem A for the full gas, normalized (`Z > 0`): `⟨φ(f)²⟩ ≥ (1 - δ) κ ⟨f, C f⟩`. -/
theorem FullBoundInternal.secondMoment_ge {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ δ : ℝ}
    {lam : V → ℤ → ℝ} (h : FullBoundInternal T κ δ lam)
    (hZ : 0 < fullGasPartitionInternal T κ lam) (f : V → ℝ) (hf : ∑ j, f j = 0) :
    (1 - δ) * κ * (∑ j, f j * -(T f j)) ≤ fullSecondMomentInternal T κ lam f := by
  have h1 := (h.2.2.2 f hf).2
  unfold fullSecondMomentInternal fullGasExpectationInternal
  rw [← div_le_iff₀ hZ] at h1
  linarith

omit [DecidableEq V] in
/-- The upper half of FS81 Theorem A for nonnegative weights: `⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩`. -/
theorem fullSecondMoment_le {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ}
    (hnn : ∀ q, 0 ≤ gasWeightInternal T κ lam q) (hZ : 0 ≤ fullGasPartitionInternal T κ lam)
    (f : V → ℝ) : fullSecondMomentInternal T κ lam f ≤ κ * ∑ j, f j * -(T f j) := by
  unfold fullSecondMomentInternal fullGasExpectationInternal
  have : 0 ≤ (∑' q, gasWeightInternal T κ lam q * (κ * ∑ j, (q j : ℝ) * -(T f j)) ^ 2) /
      fullGasPartitionInternal T κ lam :=
    div_nonneg (tsum_nonneg fun q => mul_nonneg (hnn q) (sq_nonneg _)) hZ
  linarith

omit [DecidableEq V] in
/-- Physical weights (`λ_j ≥ 0`, `λ_j(0) = 1`) have nonnegative Gibbs weights. -/
theorem gasWeight_nonneg_of_physical (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) {lam : V → ℤ → ℝ}
    (hnn : ∀ j n, 0 ≤ lam j n) (q : V → ℤ) : 0 ≤ gasWeightInternal T κ lam q := by
  unfold gasWeightInternal
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg fun j _ => hnn j _) (Real.exp_pos _).le
  · exact le_rfl

omit [DecidableEq V] in
/-- **The positivity gate for physical weights**: `Z ≥ w(0) = 1`. -/
theorem one_le_fullGasPartition {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ : ℝ} {lam : V → ℤ → ℝ}
    (hs : Summable (gasWeightInternal T κ lam)) (hnn : ∀ j n, 0 ≤ lam j n)
    (h0 : ∀ j, lam j 0 = 1) : 1 ≤ fullGasPartitionInternal T κ lam := by
  have hw0 : gasWeightInternal T κ lam 0 = 1 := by
    unfold gasWeightInternal chargeEnergyInternal
    simp [h0]
  rw [← hw0]
  exact hs.le_tsum 0 fun q _ => gasWeight_nonneg_of_physical T κ hnn q

omit [DecidableEq V] in
/-- Normalization by nonzero vacancy weights : rescaling `λ_j` by constants `c_j`
multiplies every Gibbs weight by `∏_j c_j`. -/
theorem gasWeight_smul (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) (c : V → ℝ)
    (q : V → ℤ) :
    gasWeightInternal T κ (fun j n => c j * lam j n) q = (∏ j, c j) * gasWeightInternal T κ lam q := by
  unfold gasWeightInternal
  split_ifs
  · rw [Finset.prod_mul_distrib]; ring
  · simp

/-- Cutoff expectations are unchanged by rescaling the weights by nonzero constants. -/
theorem gasExpectation_smul (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (c : V → ℝ) (hc : ∏ j, c j ≠ 0) (F : (V → ℤ) → ℝ) :
    gasExpectationInternal N T κ (fun j n => c j * lam j n) F = gasExpectationInternal N T κ lam F := by
  unfold gasExpectationInternal gasPartitionInternal
  simp_rw [gasWeight_smul, mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

omit [DecidableEq V] in
/-- Full expectations are unchanged by rescaling the weights by nonzero constants. -/
theorem fullGasExpectation_smul (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (c : V → ℝ) (hc : ∏ j, c j ≠ 0) (F : (V → ℤ) → ℝ) :
    fullGasExpectationInternal T κ (fun j n => c j * lam j n) F =
      fullGasExpectationInternal T κ lam F := by
  unfold fullGasExpectationInternal fullGasPartitionInternal
  simp_rw [gasWeight_smul, mul_assoc, tsum_mul_left]
  exact mul_div_mul_left _ _ hc

end Full

/-! ### Field functionals and the square theorems -/

section Squares

variable {W : Type*} [Fintype W] [DecidableEq W] {E : Type*} [Fintype E]

/-- **FS81 (1.15)–(1.16) without frequency cutoff**: the cutoff sine-Gordon functionals
`⟨e^{u φ(f)}⟩_N` converge, as `N → ∞`, to `fullExpMomentInternal`. -/
theorem tendsto_cutoff_expMoment (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected) (κ : ℝ)
    (hκ : 0 < κ) (v : W) (lam : W → ℤ → ℝ) (hev : ∀ j n, lam j (-n) = lam j n)
    (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (hT : Λ.IsLaplacianPseudoinverse T) (h : GateInternal T κ lam)
    (hZ : fullGasPartitionInternal T κ lam ≠ 0) (f : W → ℝ) (hf : ∑ j, f j = 0) (u : ℝ) :
    Tendsto (fun N => weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j)) (fun φ => Real.exp (u * ∑ j, φ j * f j)))
      atTop (𝓝 (fullExpMomentInternal T κ lam f u)) := by
  simp_rw [weightedGFFExpectation_exp_mul_sineGordon Λ hΛ κ hκ v _ lam hev T hT f hf u]
  exact tendsto_const_nhds.mul
    (tendsto_gasExpectation_cutoff h hZ _ 1 fun q => abs_cos_le_quadratic _ q)

/-- **FS81 (1.17) without frequency cutoff**: the cutoff sine-Gordon second moments `⟨φ(f)²⟩_N`
converge to `fullSecondMomentInternal`. -/
theorem tendsto_cutoff_secondMoment (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected)
    (κ : ℝ) (hκ : 0 < κ) (v : W) (lam : W → ℤ → ℝ) (hev : ∀ j n, lam j (-n) = lam j n)
    (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (hT : Λ.IsLaplacianPseudoinverse T) (h : GateInternal T κ lam)
    (hZ : fullGasPartitionInternal T κ lam ≠ 0) (f : W → ℝ) (hf : ∑ j, f j = 0) :
    Tendsto (fun N => weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j)) (fun φ => (∑ j, φ j * f j) ^ 2))
      atTop (𝓝 (fullSecondMomentInternal T κ lam f)) := by
  have hZN : ∀ᶠ N in atTop, gasPartitionInternal N T κ lam ≠ 0 :=
    (tendsto_gasPartition_cutoff h).eventually_ne hZ
  refine Tendsto.congr' (hZN.mono fun N hN =>
    (weightedGFFExpectation_sq_sineGordon Λ hΛ κ hκ v N lam hev T hT f hf hN).symm) ?_
  exact tendsto_const_nhds.sub (tendsto_gasExpectation_cutoff h hZ _ _
    fun q => abs_sq_pairing_le_quadratic κ (fun j => -(T f j)) q)

omit [DecidableEq W] in
/-- The gate for Condition-λ weights with a `1/16`-coercive energy, once `κ (1/16 - ε) > α`. -/
theorem gate_of_conditionLambda {T : (W → ℝ) →ₗ[ℝ] W → ℝ} {κ C α ε : ℝ} (hκ : 0 ≤ κ)
    {lam : W → ℤ → ℝ} (hlam : ∀ j, ConditionLambdaInternal C α ε κ (lam j))
    (hE : ∀ q : W → ℤ, ∑ j, q j = 0 → (∑ j, (q j : ℝ) ^ 2) / 16 ≤ chargeEnergyInternal T q)
    (hκα : α < κ * (1 / 16 - ε)) : GateInternal T κ lam :=
  ⟨hκ, 1 / 16, α + ε * κ, max 1 C, zero_le_one.trans (le_max_left _ _), by linarith,
    fun q hq => by have := hE q hq; linarith,
    fun j n => ((hlam j).2 n).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)⟩

/-- **FS81 Theorems 5.1 and A for general Condition-λ gases** (J pp. 570–572, Theorems 5.2–5.3
and the concluding paragraph), on the free square and on the even periodic square, **without
frequency cutoff**: for `δ > 0` and constants `(C, α, ε)` with `ε < 1/16` there is `κ₀`,
independent of the volume, such that for `κ > κ₀`, every family of normalized Condition-λ
weights (signed allowed) and every pseudoinverse, `FullBoundInternal` holds: the gate holds
(the full gas weights are summable), `Z_N → Z ≥ 0`, and the Theorem 5.1/A inequalities hold multiplied by `Z`.
For `Z > 0` (in particular for physical weights, `one_le_fullGasPartition`) they give
`FullBoundInternal.expMoment_ge` and `FullBoundInternal.secondMoment_ge`. -/
theorem conditionLambda_full_bound (δ : ℝ) (hδ : 0 < δ) (C α ε : ℝ) (hε : ε < 1 / 16) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ (L : ℕ) (_ : 1 < L) (κ : ℝ), κ₀ < κ →
      ∀ lam : Fin L × Fin L → ℤ → ℝ, (∀ j, ConditionLambdaInternal C α ε κ (lam j)) →
        (∀ j, lam j 0 = 1) →
        (∀ T, (squareFree L).IsLaplacianPseudoinverse T → FullBoundInternal T κ δ lam) ∧
        (Even L → ∀ T, (squarePeriodic L).IsLaplacianPseudoinverse T →
          FullBoundInternal T κ δ lam) := by
  obtain ⟨κ₁, hκ₁, hcut⟩ := conditionLambda_cutoff_bound δ hδ C α ε hε
  have hd : 0 < 1 / 16 - ε := by linarith
  refine ⟨max κ₁ (α / (1 / 16 - ε)), lt_max_of_lt_left hκ₁, fun L hL κ hκ lam hlam h0 => ?_⟩
  have hκ1 : κ₁ < κ := (le_max_left _ _).trans_lt hκ
  have hκα : α < κ * (1 / 16 - ε) := (div_lt_iff₀ hd).1 ((le_max_right _ _).trans_lt hκ)
  have hκ0 : 0 ≤ κ := (hκ₁.trans hκ1).le
  refine ⟨fun T hT => fullBound_of_cutoffSum (gate_of_conditionLambda hκ0 hlam
      (fun q hq => chargeEnergy_ge_of_degree _ (squareFree_connected L hL)
        (SpinWaves.squareFreeBipartiteDegreeFour L hL).endpointDegree_le_four T hT q hq) hκα)
      fun N => ((hcut L hL).1 κ hκ1 lam hlam h0 N T hT).toSum,
    fun he T hT => fullBound_of_cutoffSum (gate_of_conditionLambda hκ0 hlam
      (fun q hq => chargeEnergy_ge_of_degree _ (squarePeriodic_connected L hL)
        (SpinWaves.squarePeriodicBipartiteDegreeFour L he hL).endpointDegree_le_four T hT q hq) hκα)
      fun N => (((hcut L hL).2 he) κ hκ1 lam hlam h0 N T hT).toSum⟩

end Squares

end FroehlichSpencer.BKT.Coulomb
