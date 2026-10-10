/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.L41Source
public import FroehlichSpencer.BKT.Charges.RecurrenceArithmetic
public import FroehlichSpencer.BKT.Reduction.T16AssemblyStatements
public import FroehlichSpencer.BKT.Charges.ScaleGeometry

/-! # KP Proposition 2.1

The source-facing statement is KP (2.5), with the reviewed project values
`α = 7/4` and `M = 2^16`. The exact target consumed by the T1.6 assembly is
`Reduction.p21Statement`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

/-- Extend a positive-scale minimum-cover selection to the scale-zero
recurrence API by choosing any minimum cover at scale zero. -/
noncomputable def p21CoverAt (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ρ : ChargeDensity L) (k : ℕ) :
    {C : Finset (Finset (Fin L × Fin L)) // IsMinimumSquareCover boundary L k ρ C} := by
  classical
  by_cases hk : 1 ≤ k
  · exact cover ρ ⟨k, hk⟩
  · exact ⟨Classical.choose (exists_minimumSquareCover boundary L k ρ),
      Classical.choose_spec (exists_minimumSquareCover boundary L k ρ)⟩

/-- The scale cover number, clipped to the scales needed in the finite P2.1
sum. Clipping only defines a convenient total function for the arithmetic
iteration. -/
def p21CoverWeight (boundary : SquareBoundary) (L n : ℕ)
    (ρ : ChargeDensity L) : ℤ → ℝ := fun q =>
  if 0 ≤ q ∧ q ≤ n then
    (squareCoverNumber boundary L q.toNat ρ : ℝ)
  else 0

/-- The separated-square weight on all integer scales, including the
scale-zero recurrence extension. At positive scales it uses exactly the
selected cover from `MinimumCoverSelection`. -/
noncomputable def p21SeparatedWeight (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ρ : ChargeDensity L) : ℤ → ℝ :=
  fun q => if 0 ≤ q then
    ((separatedSquaresNat boundary L ρ q.toNat
      (p21CoverAt boundary L cover ρ q.toNat)).card : ℝ) else 0

/-- The scale-zero separated term is at most the scale-zero cover count. -/
theorem p21SeparatedZero_le_coverZero (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ρ : ChargeDensity L) :
    (p21SeparatedWeight boundary L cover ρ 0) ≤
      (squareCoverNumber boundary L 0 ρ : ℝ) := by
  have hcard := card_separatedSquaresNat_zero_le boundary L ρ
    (p21CoverAt boundary L cover ρ 0)
  have hcover := card_eq_squareCoverNumber_of_isMinimumSquareCover boundary L 0 ρ
    (p21CoverAt boundary L cover ρ 0).val (p21CoverAt boundary L cover ρ 0).property
  simp [p21SeparatedWeight]
  exact_mod_cast (hcard.trans_eq hcover)

/-- The integer-scale separated sequence is summable, because all terms above
the finite domain scale vanish. -/
theorem p21SeparatedWeight_summable (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ρ : ChargeDensity L) :
    Summable (p21SeparatedWeight boundary L cover ρ) := by
  classical
  let F : Finset ℤ := insert 0
    ((Finset.range L).image fun k : ℕ => (k : ℤ) + 1)
  apply summable_of_ne_finset_zero (s := F)
  intro q hqF
  by_cases hq : 0 ≤ q
  · by_cases hzero : q = 0
    · exact False.elim (hqF (by simp [F, hzero]))
    · have hpos : 0 < q := by omega
      have hqNat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
      have hlarge : L < q.toNat := by
        by_contra hn
        have hk : q.toNat - 1 < L := by omega
        have hmem : q ∈ F := by
          simp only [F, Finset.mem_insert]
          right
          apply Finset.mem_image.mpr
          refine ⟨q.toNat - 1, Finset.mem_range.mpr hk, ?_⟩
          rw [Int.natCast_sub (by omega : 1 ≤ q.toNat)]
          omega
        exact hqF hmem
      have hscalePos : 1 ≤ q.toNat := by omega
      have hpow : q.toNat < 2 ^ q.toNat := Nat.lt_two_pow_self
      have hLpow : L < 2 ^ q.toNat := lt_trans hlarge hpow
      have hsep0 : separatedSquares boundary L ρ ⟨q.toNat, hscalePos⟩
          (p21CoverAt boundary L cover ρ q.toNat) = ∅ :=
        separatedSquares_eq_empty_of_lt_two_pow boundary L ρ ⟨q.toNat, hscalePos⟩
          (p21CoverAt boundary L cover ρ q.toNat) hLpow
      have hsepN : separatedSquaresNat boundary L ρ q.toNat
          (p21CoverAt boundary L cover ρ q.toNat) = ∅ := by
        rw [separatedSquaresNat_eq_separatedSquares boundary L ρ q.toNat hscalePos]
        exact hsep0
      simp [p21SeparatedWeight, hq, hsepN]
  · simp [p21SeparatedWeight, hq]

/-- The total recurrence separated weight is exactly the scale-zero term plus
KP's positive-scale sum. -/
theorem p21SeparatedWeight_tsum (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ρ : ChargeDensity L) :
    ∑' q : ℤ, p21SeparatedWeight boundary L cover ρ q =
      p21SeparatedWeight boundary L cover ρ 0 +
        (separatedSquareTotal boundary L cover ρ : ℝ) := by
  classical
  let F : Finset ℤ := insert 0
    ((Finset.range L).image fun k : ℕ => (k : ℤ) + 1)
  have hout : ∀ q ∉ F, p21SeparatedWeight boundary L cover ρ q = 0 := by
    intro q hq
    by_contra hne
    have hnotzero : p21SeparatedWeight boundary L cover ρ q ≠ 0 := hne
    have hqnonneg : 0 ≤ q := by
      by_contra hn
      simp [p21SeparatedWeight, hn] at hnotzero
    by_cases hzero : q = 0
    · exact hq (by simp [F, hzero])
    · have hpos : 0 < q := by omega
      have hqNat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hqnonneg
      have hqSmall : q.toNat ≤ L := by
        by_contra hlarge
        have hscalePos : 1 ≤ q.toNat := by omega
        have hpow : q.toNat < 2 ^ q.toNat := Nat.lt_two_pow_self
        have hsep0 : separatedSquares boundary L ρ ⟨q.toNat, hscalePos⟩
            (p21CoverAt boundary L cover ρ q.toNat) = ∅ :=
          separatedSquares_eq_empty_of_lt_two_pow boundary L ρ ⟨q.toNat, hscalePos⟩
            (p21CoverAt boundary L cover ρ q.toNat) (lt_trans (by omega) hpow)
        have hsepN : separatedSquaresNat boundary L ρ q.toNat
            (p21CoverAt boundary L cover ρ q.toNat) = ∅ := by
          rw [separatedSquaresNat_eq_separatedSquares boundary L ρ q.toNat hscalePos]
          exact hsep0
        simp [p21SeparatedWeight, hqnonneg, hsepN] at hnotzero
      have hmem : q ∈ F := by
        simp only [F, Finset.mem_insert]
        right
        apply Finset.mem_image.mpr
        refine ⟨q.toNat - 1, Finset.mem_range.mpr (by omega), ?_⟩
        rw [Int.natCast_sub (by omega : 1 ≤ q.toNat)]
        omega
      exact hq hmem
  rw [tsum_eq_sum hout]
  have hzero_not_image : (0 : ℤ) ∉
      (Finset.range L).image (fun k : ℕ => (k : ℤ) + 1) := by
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨k, hk, h⟩
    omega
  dsimp [F]
  rw [Finset.sum_insert hzero_not_image, Finset.sum_image]
  · apply congrArg (fun z : ℝ => p21SeparatedWeight boundary L cover ρ 0 + z)
    rw [separatedSquareTotal, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hq : 0 ≤ (k : ℤ) + 1 := by omega
    have hnat : (((k : ℤ) + 1).toNat) = k + 1 := by omega
    simp [p21SeparatedWeight, hq, hnat, p21CoverAt,
      separatedSquaresNat_eq_separatedSquares, separatedSquareCount]
  · intro a ha b hb hab
    exact_mod_cast (add_right_cancel hab)

/-- The two-sided iterate can also be written as one right application of
`γ`; this is the form used to apply Lemma 4.1 at an intermediate scale. -/
theorem p21_iterate_succ_right (m : ℕ) (q : ℤ) :
    recurrenceIterate (m + 1) q = recurrenceGamma (recurrenceIterate m q) := by
  induction m generalizing q with
  | zero => simp [recurrenceIterate]
  | succ m ih =>
      change recurrenceIterate (m + 1) (recurrenceGamma q) =
        recurrenceGamma (recurrenceIterate m (recurrenceGamma q))
      exact ih (recurrenceGamma q)

/-- Cover weights are nonnegative. -/
theorem p21CoverWeight_nonneg (boundary : SquareBoundary) (L n : ℕ)
    (ρ : ChargeDensity L) (q : ℤ) : 0 ≤ p21CoverWeight boundary L n ρ q := by
  by_cases hq : 0 ≤ q ∧ q ≤ n
  · simp [p21CoverWeight, hq]
  · simp [p21CoverWeight, hq]

/-- Separated weights are nonnegative. -/
theorem p21SeparatedWeight_nonneg (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ρ : ChargeDensity L) (q : ℤ) :
    0 ≤ p21SeparatedWeight boundary L cover ρ q := by
  by_cases hq : 0 ≤ q
  · simp [p21SeparatedWeight, hq]
  · simp [p21SeparatedWeight, hq]

/-- A nonzero density has nonempty support. -/
theorem chargeSupport_nonempty_of_ne_zero (L : ℕ) (ρ : ChargeDensity L)
    (hρ : ρ ≠ 0) : (chargeSupport ρ).Nonempty := by
  classical
  by_contra h
  have hempty : chargeSupport ρ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hex : ∃ x, ρ x ≠ 0 := by
    by_contra hn
    apply hρ
    funext x
    by_contra hx
    exact hn ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  have hmem : x ∈ chargeSupport ρ := by simp [chargeSupport, hx]
  rw [hempty] at hmem
  simp at hmem

/-- Every support cover of a nonzero density has at least one square. -/
theorem squareCoverNumber_pos_of_ne_zero (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) (hρ : ρ ≠ 0) : 0 < squareCoverNumber boundary L k ρ := by
  classical
  by_contra hpos
  have hzero : squareCoverNumber boundary L k ρ = 0 := by omega
  obtain ⟨C, hC, hcard⟩ := exists_squareCover_attaining_number boundary L k ρ
  have hCempty : C = ∅ := Finset.card_eq_zero.mp (hcard.trans hzero)
  obtain ⟨x, hx⟩ := chargeSupport_nonempty_of_ne_zero L ρ hρ
  obtain ⟨s, hs, _⟩ := hC.2 x hx
  rw [hCempty] at hs
  simp at hs

/-- The source lower estimate in Proposition 2.1. -/
theorem kp_p21_lower (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L)
    (hρ : ρ ≠ 0) :
    Real.logb 2 (chargeDiameter boundary L ρ + 1) ≤ chargeCoverCost boundary L ρ := by
  classical
  by_cases hd0 : chargeDiameter boundary L ρ = 0
  · simp [chargeCoverCost, hd0]
  · have hdNat : 1 ≤ chargeDiameter boundary L ρ := Nat.one_le_iff_ne_zero.mpr hd0
    let n := chargeCutoff boundary L ρ hdNat
    have hcost : chargeCoverCost boundary L ρ =
        ∑ k ∈ Finset.range (n + 1), squareCoverNumber boundary L k ρ := by
      simp [chargeCoverCost, hd0, n]
    have hsumNat : n + 1 ≤
        ∑ k ∈ Finset.range (n + 1), squareCoverNumber boundary L k ρ := by
      have hterm : ∀ k ∈ Finset.range (n + 1),
          1 ≤ squareCoverNumber boundary L k ρ := by
        intro k hk
        exact Nat.succ_le_of_lt (squareCoverNumber_pos_of_ne_zero boundary L k ρ hρ)
      calc
        n + 1 = ∑ _k ∈ Finset.range (n + 1), 1 := by simp
        _ ≤ ∑ k ∈ Finset.range (n + 1), squareCoverNumber boundary L k ρ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k hk
    have hsum : (n + 1 : ℝ) ≤
        (∑ k ∈ Finset.range (n + 1), squareCoverNumber boundary L k ρ : ℕ) := by
      exact_mod_cast hsumNat
    have hcutarg : (chargeDiameter boundary L ρ : ℝ) + 1 ≤
        (chargeCoverScale : ℝ) * (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent := by
      have hdR : 1 ≤ (chargeDiameter boundary L ρ : ℝ) := by exact_mod_cast hdNat
      have hpow : (chargeDiameter boundary L ρ : ℝ) ≤
          (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent := by
        rw [show chargeCoverExponent = 7 / 4 by rfl]
        exact Real.self_le_rpow_of_one_le hdR (by norm_num : (1 : ℝ) ≤ 7 / 4)
      dsimp [chargeCoverScale]
      nlinarith only [hdR, hpow]
    have hlog : Real.logb 2 ((chargeDiameter boundary L ρ : ℝ) + 1) ≤
        Real.logb 2 ((chargeCoverScale : ℝ) *
          (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent) := by
      have harg1 : 0 < (chargeDiameter boundary L ρ : ℝ) + 1 := by positivity
      have harg2 : 0 < (chargeCoverScale : ℝ) *
          (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent :=
        mul_pos (by norm_num [chargeCoverScale])
          (Real.rpow_pos_of_pos (by exact_mod_cast hdNat) _)
      exact (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ))
        harg1 harg2).2 hcutarg
    have hceil : Real.logb 2 ((chargeCoverScale : ℝ) *
        (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent) ≤ (n : ℝ) := by
      exact Nat.le_ceil _
    have hcostR : (n + 1 : ℝ) ≤ chargeCoverCost boundary L ρ := by
      rw [hcost]
      exact hsum
    calc
      Real.logb 2 (chargeDiameter boundary L ρ + 1) ≤
          Real.logb 2 ((chargeCoverScale : ℝ) *
            (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent) := by
        convert hlog using 1
      _ ≤ n := hceil
      _ ≤ n + 1 := by exact_mod_cast Nat.le_succ n
      _ ≤ chargeCoverCost boundary L ρ := hcostR

/-- At a recurrence step whose scale is no larger than the P2.1 cutoff, the
lower scale has side at most one quarter of the support diameter. -/
theorem p21_lowerScale_side_le_quarter (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) (hd : 0 < chargeDiameter boundary L ρ)
    {K : ℕ} (hK : 21 ≤ K)
    (hKcut : K ≤ chargeCutoff boundary L ρ
      (Nat.one_le_iff_ne_zero.mpr (by omega))) :
    (squareSide (l41LowerScale K) : ℝ) ≤
      (chargeDiameter boundary L ρ : ℝ) / 4 := by
  let d := chargeDiameter boundary L ρ
  let n := chargeCutoff boundary L ρ (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hdNat : 1 ≤ d := by dsimp [d]; omega
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hdNat
  have hpower : 1 ≤ (d : ℝ) ^ chargeCoverExponent := by
    exact hdR.trans (Real.self_le_rpow_of_one_le hdR (by
      change 1 ≤ (7 / 4 : ℝ)
      norm_num))
  have hfactor : 1 ≤ (chargeCoverScale : ℝ) * (d : ℝ) ^ chargeCoverExponent := by
    have hM : 1 ≤ (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
    exact le_trans (by norm_num) (mul_le_mul hM hpower (by norm_num) (zero_le_one.trans hM))
  have hlogx : Real.logb 2 ((chargeCoverScale : ℝ) *
      (d : ℝ) ^ chargeCoverExponent) =
      16 + (7 / 4 : ℝ) * Real.logb 2 (d : ℝ) := by
    have hpowPos : 0 < (d : ℝ) ^ chargeCoverExponent := by
      exact lt_of_lt_of_le (by norm_num) hpower
    have hMne : (chargeCoverScale : ℝ) ≠ 0 := by norm_num [chargeCoverScale]
    rw [Real.logb_mul hMne hpowPos.ne']
    rw [show (chargeCoverScale : ℝ) = (2 : ℝ) ^ 16 by norm_num [chargeCoverScale],
      Real.logb_pow 2 2 16]
    simp
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hdNat)]
    norm_num [chargeCoverExponent]
  have hlognonneg : 0 ≤ Real.logb 2
      ((chargeCoverScale : ℝ) * (d : ℝ) ^ chargeCoverExponent) :=
    Real.logb_nonneg (b := 2) (x := (chargeCoverScale : ℝ) *
      (d : ℝ) ^ chargeCoverExponent) (by norm_num) hfactor
  have hceil : (n : ℝ) <
      Real.logb 2 ((chargeCoverScale : ℝ) * (d : ℝ) ^ chargeCoverExponent) + 1 := by
    dsimp [n]
    exact Nat.ceil_lt_add_one hlognonneg
  have hKcast : (K : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hKcut
  have hKlog : (K : ℝ) <
      Real.logb 2 ((chargeCoverScale : ℝ) * (d : ℝ) ^ chargeCoverExponent) + 1 := by
    exact lt_of_le_of_lt hKcast hceil
  obtain ⟨hγ, _⟩ := l41LowerScale_spec K hK
  have hγcast : (l41LowerScale K : ℝ) = (recurrenceGamma (K : ℤ) : ℝ) := by
    exact_mod_cast hγ
  have hγupper := (recurrenceGamma_bounds (K : ℤ)).2
  have hKlog' : (K : ℝ) < 17 + (7 / 4 : ℝ) * Real.logb 2 (d : ℝ) := by
    rw [hlogx] at hKlog
    linarith only [hKlog]
  have hqUpper : (l41LowerScale K : ℝ) ≤
      (4 / 7 : ℝ) * (K : ℝ) - 83 / 7 := by
    rw [hγcast]
    exact hγupper
  have hγle : (l41LowerScale K : ℝ) ≤ Real.logb 2 (d : ℝ) - 15 / 7 := by
    nlinarith only [hqUpper, hKlog']
  have hpow₁ : (2 : ℝ) ^ (l41LowerScale K : ℝ) ≤
      (2 : ℝ) ^ (Real.logb 2 (d : ℝ) - 15 / 7) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hγle
  have hpow₂ : (2 : ℝ) ^ (Real.logb 2 (d : ℝ) - 15 / 7) ≤
      (2 : ℝ) ^ (Real.logb 2 (d : ℝ) - 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only
  have hpow_eq : (2 : ℝ) ^ (Real.logb 2 (d : ℝ) - 2) = (d : ℝ) / 4 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by exact_mod_cast hdNat)]
    norm_num
  have hside : (squareSide (l41LowerScale K) : ℝ) =
      (2 : ℝ) ^ (l41LowerScale K : ℝ) := by
    simp [squareSide, Real.rpow_natCast]
  rw [hside]
  exact hpow₁.trans (hpow₂.trans_eq hpow_eq)

/-- Every minimum cover at the lower scale in a valid P2.1 recurrence step
has at least two squares. -/
theorem p21_lowerCover_card_ge_two (boundary : SquareBoundary) (L : ℕ)
    (hL : 1 < L) (ρ : ChargeDensity L) (hρ : ρ ≠ 0)
    (hd : 0 < chargeDiameter boundary L ρ)
    {K : ℕ} (hK : 21 ≤ K)
    (hKcut : K ≤ chargeCutoff boundary L ρ
      (Nat.one_le_iff_ne_zero.mpr (by omega)))
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L (l41LowerScale K) ρ C}) : 2 ≤ C.val.card := by
  classical
  by_contra hcard
  have hnum : C.val.card = squareCoverNumber boundary L (l41LowerScale K) ρ :=
    card_eq_squareCoverNumber_of_isMinimumSquareCover boundary L
      (l41LowerScale K) ρ C.val C.property
  have hnumpos : 1 ≤ squareCoverNumber boundary L (l41LowerScale K) ρ :=
    Nat.succ_le_of_lt (squareCoverNumber_pos_of_ne_zero boundary L (l41LowerScale K) ρ hρ)
  have hone : C.val.card = 1 := by omega
  obtain ⟨s, hsC⟩ := Finset.card_eq_one.mp hone
  have hsub : chargeSupport ρ ⊆ s := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := C.property.1.2 x hx
    have hteq : t = s := by simpa [hsC] using ht
    simpa [hteq] using hxt
  have hsMem : s ∈ kpSquares boundary L (l41LowerScale K) := by
    have hsC' : s ∈ C.val := by rw [hsC]; simp
    exact C.property.1.1 hsC'
  have hdiamMono : chargeDiameter boundary L ρ ≤ squareDiameter boundary L s := by
    exact squareDiameter_mono boundary L hsub
  have hsdiam : squareDiameter boundary L s ≤
      2 * (squareSide (l41LowerScale K) - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L (l41LowerScale K) s hsMem
    | periodic => exact periodic_squareDiameter_le L (l41LowerScale K) hL s hsMem
  have hside := p21_lowerScale_side_le_quarter boundary L ρ hd hK hKcut
  have hdiamR : (chargeDiameter boundary L ρ : ℝ) ≤
      (squareDiameter boundary L s : ℝ) := by exact_mod_cast hdiamMono
  have hsdiamR : (squareDiameter boundary L s : ℝ) ≤
      2 * ((squareSide (l41LowerScale K) - 1 : ℕ) : ℝ) := by exact_mod_cast hsdiam
  have hsideR : ((squareSide (l41LowerScale K) - 1 : ℕ) : ℝ) ≤
      squareSide (l41LowerScale K) := by
    exact_mod_cast Nat.sub_le _ _
  have hdRpos : 0 < (chargeDiameter boundary L ρ : ℝ) := by exact_mod_cast hd
  have hcontr : (chargeDiameter boundary L ρ : ℝ) <
      (chargeDiameter boundary L ρ : ℝ) := by
    nlinarith only [hdiamR, hsdiamR, hside, hsideR, hdRpos]
  exact (lt_irrefl _ hcontr)

/-- The upper estimate in KP Proposition 2.1, obtained by summing Lemma 4.1
through the valid recurrence depths of  -/
theorem kp_p21_upper (boundary : SquareBoundary) (L : ℕ)
    (hL : 1 < L) (cover : MinimumCoverSelection boundary L)
    (ρ : ChargeDensity L) (hρ : ρ ≠ 0) :
    (chargeCoverCost boundary L ρ : ℝ) ≤
      recurrenceP21Constant *
        (squareCoverNumber boundary L 0 ρ + separatedSquareTotal boundary L cover ρ) := by
  classical
  by_cases hd0 : chargeDiameter boundary L ρ = 0
  · have hcost : chargeCoverCost boundary L ρ = 0 := by simp [chargeCoverCost, hd0]
    have hD : 0 < recurrenceP21Constant := by
      dsimp [recurrenceP21Constant, recurrenceFirstTermConstant,
        recurrenceSeparatedCoefficient]
      have htail : 0 ≤ ∑' n : ℕ, recurrenceTailTerm n :=
        tsum_nonneg (fun n : ℕ => recurrenceTailTerm_nonneg n)
      norm_num
      nlinarith only [htail]
    rw [hcost]
    simpa using (mul_nonneg (le_of_lt hD)
      (add_nonneg (Nat.cast_nonneg (squareCoverNumber boundary L 0 ρ))
        (Nat.cast_nonneg (separatedSquareTotal boundary L cover ρ))))
  · have hd : 0 < chargeDiameter boundary L ρ := by omega
    have hdNat : 1 ≤ chargeDiameter boundary L ρ := Nat.one_le_iff_ne_zero.mpr hd0
    let n := chargeCutoff boundary L ρ hdNat
    let c : ℤ → ℝ := p21CoverWeight boundary L n ρ
    let s : ℤ → ℝ := p21SeparatedWeight boundary L cover ρ
    have hstep : ∀ q m, m < recurrenceDepth q →
        c (recurrenceIterate m q) ≤
          (1 / 2 : ℝ) * c (recurrenceIterate (m + 1) q) +
            s (recurrenceIterate (m + 1) q) := by
      intro q m hm
      let r := recurrenceIterate m q
      have hrvalid : 21 ≤ r := recurrenceDepth_valid_before q hm
      have hrnonneg : 0 ≤ r := by omega
      have hnext : recurrenceIterate (m + 1) q = recurrenceGamma r :=
        p21_iterate_succ_right m q
      by_cases hrle : r ≤ n
      · let K := r.toNat
        have hrK : (K : ℤ) = r := Int.toNat_of_nonneg hrnonneg
        have hKvalid : 21 ≤ K := by
          have hcast : (21 : ℤ) ≤ (K : ℤ) := by rw [hrK]; exact hrvalid
          exact_mod_cast hcast
        have hKcut : K ≤ n := by
          have hcast : (K : ℤ) ≤ (n : ℤ) := by rw [hrK]; exact hrle
          exact_mod_cast hcast
        have hscale := l41LowerScale_spec K hKvalid
        have hnextScale : recurrenceIterate (m + 1) q = (l41LowerScale K : ℤ) := by
          calc
            recurrenceIterate (m + 1) q = recurrenceGamma r := hnext
            _ = recurrenceGamma (K : ℤ) := by rw [← hrK]
            _ = (l41LowerScale K : ℤ) := hscale.1.symm
        have hlowle : l41LowerScale K ≤ K := by omega
        have hlowcut : l41LowerScale K ≤ n := hlowle.trans hKcut
        have hDcover := p21CoverAt boundary L cover ρ K
        let hCcover := p21CoverAt boundary L cover ρ (l41LowerScale K)
        have hCcard := p21_lowerCover_card_ge_two boundary L hL ρ hρ hd
          hKvalid hKcut hCcover
        have hL41 := l41_recurrence_step boundary L K hL hKvalid ρ
          hCcover hDcover hCcard
        have hsourceR : (hDcover.val.card : ℝ) ≤
            (hCcover.val.card : ℝ) / 2 +
              ((separatedSquaresNat boundary L ρ (l41LowerScale K) hCcover).card : ℝ) := by
          have hcast : (hDcover.val.card : ℝ) ≤
              ((hCcover.val.card / 2 : ℕ) : ℝ) +
                ((separatedSquaresNat boundary L ρ (l41LowerScale K) hCcover).card : ℝ) := by
            exact_mod_cast hL41
          have hdiv : ((hCcover.val.card / 2 : ℕ) : ℝ) ≤
              (hCcover.val.card : ℝ) / 2 := by
            have hn := Nat.div_mul_le_self hCcover.val.card 2
            have hnR : ((hCcover.val.card / 2 : ℕ) : ℝ) * 2 ≤
                (hCcover.val.card : ℝ) := by exact_mod_cast hn
            apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
            nlinarith only [hnR]
          nlinarith only [hcast, hdiv]
        have hleft : c r = (hDcover.val.card : ℝ) := by
          have hrUpper : r ≤ (n : ℤ) := by exact_mod_cast hrle
          have hDcard := card_eq_squareCoverNumber_of_isMinimumSquareCover boundary L K
            ρ hDcover.val hDcover.property
          simp [c, p21CoverWeight, hrnonneg, hrUpper, K, hDcard]
        have hrightCover : c (recurrenceIterate (m + 1) q) =
            (hCcover.val.card : ℝ) := by
          have hnxtnonneg : 0 ≤ (l41LowerScale K : ℤ) := by omega
          have hnxtupper : (l41LowerScale K : ℤ) ≤ n := by exact_mod_cast hlowcut
          have hCcard' := card_eq_squareCoverNumber_of_isMinimumSquareCover boundary L
            (l41LowerScale K) ρ hCcover.val hCcover.property
          rw [hnextScale]
          simp [c, p21CoverWeight, hnxtnonneg, hnxtupper, hCcard']
        have hrightSep : s (recurrenceIterate (m + 1) q) =
            ((separatedSquaresNat boundary L ρ (l41LowerScale K) hCcover).card : ℝ) := by
          have hnxtnonneg : 0 ≤ (l41LowerScale K : ℤ) := by omega
          rw [hnextScale]
          simp [s, p21SeparatedWeight, hnxtnonneg, hCcover]
        rw [hleft, hrightCover, hrightSep]
        nlinarith only [hsourceR]
      · have hleft : c r = 0 := by
          have hrUpper : ¬ r ≤ n := by omega
          simp [c, p21CoverWeight, hrnonneg, hrUpper]
        rw [hleft]
        have hcoverNonneg := p21CoverWeight_nonneg boundary L n ρ
          (recurrenceIterate (m + 1) q)
        have hsepNonneg := p21SeparatedWeight_nonneg boundary L cover ρ
          (recurrenceIterate (m + 1) q)
        positivity
    have hterminal : ∀ k ∈ Finset.range (n + 1),
        c (recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)) ≤ c 0 := by
      intro k hk
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hkcut : k ≤ n := by omega
      have hzero : c 0 = (squareCoverNumber boundary L 0 ρ : ℝ) := by
        simp [c, p21CoverWeight]
      rw [hzero]
      by_cases hterm : 0 ≤ recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ) ∧
          recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ) ≤ n
      · have hiterCast :
            (((recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)).toNat : ℕ) : ℤ) =
              recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ) :=
          Int.toNat_of_nonneg hterm.1
        have hnatcut : (recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)).toNat ≤ n := by
          exact_mod_cast (show
            (((recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)).toNat : ℕ) : ℤ) ≤
              (n : ℤ) by rw [hiterCast]; exact hterm.2)
        have hbound := squareCoverNumber_le_squareCoverNumber_zero boundary L
          ((recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)).toNat) ρ
        have hnatcast : c (recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)) =
            (squareCoverNumber boundary L
              (recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)).toNat ρ : ℝ) := by
          simp [c, p21CoverWeight, hterm]
        rw [hnatcast]
        exact_mod_cast hbound
      · simp [c, p21CoverWeight, hterm]
    have hcover0 : 0 ≤ c 0 := p21CoverWeight_nonneg boundary L n ρ 0
    have hsepSummable : Summable s := by
      exact p21SeparatedWeight_summable boundary L cover ρ
    have hsepNonneg : ∀ j, 0 ≤ s j := by
      intro j
      exact p21SeparatedWeight_nonneg boundary L cover ρ j
    have hsum := recurrenceCover_total_sum_bound n c s hstep hterminal
      hcover0 hsepSummable hsepNonneg
    have hcost : (chargeCoverCost boundary L ρ : ℝ) =
        ∑ k ∈ Finset.range (n + 1), c (k : ℤ) := by
      rw [chargeCoverCost]
      simp only [hd0, ↓reduceDIte, n, c, p21CoverWeight, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hkcut : k ≤ chargeCutoff boundary L ρ hdNat := by
        dsimp [n] at hklt ⊢
        omega
      have hq : (0 : ℤ) ≤ k := by omega
      have hqcut : (k : ℤ) ≤ chargeCutoff boundary L ρ hdNat := by exact_mod_cast hkcut
      simp [hq, hqcut]
    rw [← hcost] at hsum
    rw [p21SeparatedWeight_tsum boundary L cover ρ] at hsum
    have hsep0 := p21SeparatedZero_le_coverZero boundary L cover ρ
    have hsepTotal : 0 ≤ (separatedSquareTotal boundary L cover ρ : ℝ) := by positivity
    have hcoverZero : 0 ≤ (squareCoverNumber boundary L 0 ρ : ℝ) := by positivity
    have hfirst : 0 ≤ recurrenceFirstTermConstant := by
      dsimp [recurrenceFirstTermConstant]
      have htail : 0 ≤ ∑' n : ℕ, recurrenceTailTerm n :=
        tsum_nonneg (fun n : ℕ => recurrenceTailTerm_nonneg n)
      linarith only [htail]
    have hcoef : 0 ≤ recurrenceSeparatedCoefficient := by
      norm_num [recurrenceSeparatedCoefficient]
    have hD : recurrenceP21Constant =
        recurrenceFirstTermConstant + recurrenceSeparatedCoefficient := rfl
    have hsepScaled := mul_le_mul_of_nonneg_left hsep0 hcoef
    have hsmall : recurrenceFirstTermConstant *
          (squareCoverNumber boundary L 0 ρ : ℝ) +
          recurrenceSeparatedCoefficient *
            (p21SeparatedWeight boundary L cover ρ 0 +
              (separatedSquareTotal boundary L cover ρ : ℝ)) ≤
        recurrenceP21Constant *
          ((squareCoverNumber boundary L 0 ρ : ℝ) +
            (separatedSquareTotal boundary L cover ρ : ℝ)) := by
      rw [hD]
      nlinarith only [hsepScaled, mul_nonneg hfirst hsepTotal]
    exact hsum.trans hsmall

/-- KP Proposition 2.1 in the exact form consumed by the T1.6 assembly. -/
theorem kp_p21Statement : Reduction.p21Statement := by
  have hDpos : 0 < recurrenceP21Constant := by
    have htail : 0 ≤ ∑' n : ℕ, recurrenceTailTerm n :=
      tsum_nonneg (fun n => recurrenceTailTerm_nonneg n)
    dsimp [recurrenceP21Constant, recurrenceFirstTermConstant,
      recurrenceSeparatedCoefficient]
    norm_num
    nlinarith only [htail]
  refine ⟨recurrenceP21Constant, hDpos, ?_⟩
  intro L hL
  constructor
  · intro cover ρ hρ
    exact ⟨kp_p21_lower .free L ρ hρ,
      kp_p21_upper .free L hL cover ρ hρ⟩
  · intro hEven cover ρ hρ
    exact ⟨kp_p21_lower .periodic L ρ hρ,
      kp_p21_upper .periodic L hL cover ρ hρ⟩

end FroehlichSpencer.BKT

end
