/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Tower
public import FroehlichSpencer.T12.Exterior
public import FroehlichSpencer.T12.Tails
import FroehlichSpencer.IDS.Green

/-!
# The path sum through the nested finite-volume tower
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.T12.Assembly

open Multiscale

private theorem siteDist_eq_sqrt {ν : ℕ} (x y : Site ν) :
    siteDist ν x y = Real.sqrt (∑ j, (((x j - y j : ℤ)) : ℝ) ^ 2) := rfl

private theorem exists_step {ν : ℕ} (a y : Site ν) (hy : y ≠ a) :
    ∃ y' : Site ν, siteDist ν y' y = 1 ∧ siteDist ν a y' ≤ siteDist ν a y ∧
      ∑ j, (y' j - a j).natAbs < ∑ j, (y j - a j).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ a i := by
    by_contra h
    push Not at h
    exact hy (funext h)
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (s = 1 ∧ a i < y i) ∨ (s = -1 ∧ y i < a i) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
  have hs2 : s ^ 2 = 1 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  refine ⟨Function.update y i (y i - s), ?_, ?_, ?_⟩
  · rw [siteDist_eq_sqrt, Finset.sum_eq_single i]
    · simp only [Function.update_self]
      have : (((Function.update y i (y i - s)) i - y i : ℤ) : ℝ) ^ 2 = 1 := by
        simp only [Function.update_self]
        have : ((y i - s - y i : ℤ) : ℝ) ^ 2 = ((s ^ 2 : ℤ) : ℝ) := by push_cast; ring
        rw [this, hs2]; norm_num
      simpa using this
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  · rw [siteDist_eq_sqrt, siteDist_eq_sqrt]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      have : (a j - (y j - s)) ^ 2 ≤ (a j - y j) ^ 2 := by
        rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> nlinarith
      exact_mod_cast this
    · simp [Function.update_of_ne hj]
  · apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega
      · simp [Function.update_of_ne hj]
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      simp only [Function.update_self]
      rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

private theorem siteDist_eq_one_of_hoppingKernel_ne_zero {ν : ℕ} {x w : Site ν}
    (h : hoppingKernel ν x w ≠ 0) : siteDist ν x w = 1 := by
  rw [siteDist_eq_norm]
  obtain ⟨k, rfl | rfl⟩ := hoppingKernel_ne_zero_exists h
  · exact (Infra.Lattice.norm_latticeCast_sub_eq_one_iff _ _).2
      ⟨k, Or.inr (by simp), fun j hj => by simp [hj]⟩
  · exact (Infra.Lattice.norm_latticeCast_sub_eq_one_iff _ _).2
      ⟨k, Or.inl (by simp), fun j hj => by simp [hj]⟩

private theorem exp_aux {M a b d : ℝ} (hM : 0 ≤ M) (hd : d ≤ a + 1 + b) :
    Real.exp (-M * a) * Real.exp (-M * b / 2) ≤
      Real.exp (-M * d / 2) * Real.exp (-M * a / 2) * Real.exp (M / 2) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left hd hM
  linarith

/-- One resolvent identity: from the inner block `D ⊆ Λ` to `Λ` (generic one-step lemma). -/
private theorem norm_finiteGreen_le_of_step {ν : ℕ} {Λ D : Finset (Site ν)} (hDΛ : D ⊆ Λ)
    (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0) {M : ℝ} (hM : 0 ≤ M) {s t : Site ν}
    (hsD : s ∈ D) (htD : t ∈ D)
    (hdir : ‖finiteGreen ν D v E ε hε ⟨s, hsD⟩ ⟨t, htD⟩‖ ≤ Real.exp (-M * siteDist ν s t))
    (hG : ∀ (u : Site ν) (hu : u ∈ D) (u' : Site ν) (hu' : u' ∈ Λ \ D),
      hoppingKernel ν u u' ≠ 0 →
      ‖finiteGreen ν D v E ε hε ⟨s, hsD⟩ ⟨u, hu⟩‖ ≤ Real.exp (-M * siteDist ν s u) ∧
      ‖finiteGreen ν Λ v E ε hε ⟨u', (Finset.mem_sdiff.1 hu').1⟩ ⟨t, hDΛ htD⟩‖ ≤
        2 * Real.exp (-M * siteDist ν u' t / 2))
    (hsum : ∑ u ∈ D, ∑ u' ∈ Λ \ D, ‖hoppingKernel ν u u'‖ *
      Real.exp (-M * siteDist ν s u / 2) * Real.exp (M / 2) ≤ 1 / 2) :
    ‖finiteGreen ν Λ v E ε hε ⟨s, hDΛ hsD⟩ ⟨t, hDΛ htD⟩‖ ≤
      2 * Real.exp (-M * siteDist ν s t / 2) := by
  classical
  set z : ℂ := (E : ℂ) + (ε : ℂ) * Complex.I with hz0
  have hz : z.im ≠ 0 := by simpa [hz0] using hε
  have hid := resolventColumn_eq_sub_sum_coupling_of_mem (a := hoppingKernel ν)
    (hoppingKernel_symm ν) (fun x => v x + 2 * (ν : ℝ)) hDΛ hz hsD htD
  rw [finiteGreen_eq_resolventColumn, hid, ← finiteGreen_eq_resolventColumn D v E ε hε
    ⟨s, hsD⟩ ⟨t, htD⟩]
  set W : ℝ := Real.exp (-M * siteDist ν s t / 2) with hW
  have hW0 : 0 < W := Real.exp_pos _
  have hterm : ∀ k ∈ D, ∀ k' ∈ Λ \ D,
      ‖Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) D z k s *
        hoppingKernel ν k k' *
        Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) Λ z t k'‖ ≤
      2 * W * (‖hoppingKernel ν k k'‖ * Real.exp (-M * siteDist ν s k / 2) *
        Real.exp (M / 2)) := by
    intro k hk k' hk'
    by_cases h0 : hoppingKernel ν k k' = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hG k hk k' hk' h0
      rw [finiteGreen_eq_resolventColumn] at h1 h2
      have hd1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
      have htri : siteDist ν s t ≤ siteDist ν s k + 1 + siteDist ν k' t := by
        have := siteDist_triangle ν s t k
        have := siteDist_triangle ν k t k'
        linarith
      have hex := exp_aux hM htri
      rw [norm_mul, norm_mul]
      calc _ ≤ Real.exp (-M * siteDist ν s k) * ‖hoppingKernel ν k k'‖ *
            (2 * Real.exp (-M * siteDist ν k' t / 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2 (norm_nonneg _)
              (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        _ = 2 * ‖hoppingKernel ν k k'‖ * (Real.exp (-M * siteDist ν s k) *
            Real.exp (-M * siteDist ν k' t / 2)) := by ring
        _ ≤ 2 * ‖hoppingKernel ν k k'‖ * (W * Real.exp (-M * siteDist ν s k / 2) *
            Real.exp (M / 2)) :=
            mul_le_mul_of_nonneg_left hex (mul_nonneg (by norm_num) (norm_nonneg _))
        _ = _ := by ring
  have hcross : ‖∑ k ∈ D, ∑ k' ∈ Λ \ D,
      Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) D z k s *
        hoppingKernel ν k k' *
        Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) Λ z t k'‖ ≤ W := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ k ∈ D, ∑ k' ∈ Λ \ D, 2 * W * (‖hoppingKernel ν k k'‖ *
          Real.exp (-M * siteDist ν s k / 2) * Real.exp (M / 2)) :=
          Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k' hk' => hterm k hk k' hk')
      _ = 2 * W * ∑ k ∈ D, ∑ k' ∈ Λ \ D, ‖hoppingKernel ν k k'‖ *
          Real.exp (-M * siteDist ν s k / 2) * Real.exp (M / 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
      _ ≤ 2 * W * (1 / 2) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = W := by ring
  have hdirW : ‖finiteGreen ν D v E ε hε ⟨s, hsD⟩ ⟨t, htD⟩‖ ≤ W := by
    refine hdir.trans (Real.exp_le_exp.2 ?_)
    have := mul_nonneg hM (siteDist_nonneg ν s t)
    linarith
  calc _ ≤ ‖finiteGreen ν D v E ε hε ⟨s, hsD⟩ ⟨t, htD⟩‖ + ‖∑ k ∈ D, ∑ k' ∈ Λ \ D,
        Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) D z k s *
        hoppingKernel ν k k' *
        Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) Λ z t k'‖ := by
        exact norm_sub_le _ _
    _ ≤ W + W := add_le_add hdirW hcross
    _ = _ := by ring

/-! ### Scalar facts and the crossing weight -/

private theorem rpow_three_quarters_le {l : ℝ} (hl : 65536 ≤ l) : l ^ (3 / 4 : ℝ) ≤ l / 16 := by
  have hl0 : 0 ≤ l := by linarith
  set x : ℝ := l ^ (1 / 4 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hl0 _
  have h4 : x ^ 4 = l := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num
  have h3 : x ^ 3 = l ^ (3 / 4 : ℝ) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num
  have h16 : 16 ≤ x := by
    by_contra h
    have := pow_lt_pow_left₀ (not_le.1 h) hx0 (by norm_num : (4 : ℕ) ≠ 0)
    norm_num at this
    linarith
  have := mul_le_mul_of_nonneg_left h16 (pow_nonneg hx0 3)
  rw [← h3]
  have h43 : x ^ 3 * x = l := by rw [← h4]; ring
  linarith

private theorem le_pow_four_mul {L : ℝ} (hL : 0 ≤ L) (j : ℕ) : L ≤ 4 ^ j * L :=
  le_mul_of_one_le_left hL (one_le_pow₀ (by norm_num))

private theorem four_mul_le_pow_four_mul {L : ℝ} (hL : 0 ≤ L) {j : ℕ} (hj : j ≠ 0) :
    4 * L ≤ 4 ^ j * L := by
  have : (4 : ℝ) ^ 1 ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.2 hj)
  rw [pow_one] at this
  exact mul_le_mul_of_nonneg_right this hL

private theorem crossing_weight {ν : ℕ} {Λ D : Finset (Site ν)} (hDΛ : D ⊆ Λ) {l M : ℝ}
    (hl : 1 ≤ l) (hM : 0 ≤ M) (s : Site ν)
    (hcnt : 4 * ν * (5 * l) ^ ν * Real.exp (-M * (l / 8 - 1)) ≤ 1)
    (hcr : ∀ u ∈ D, ∀ u' ∈ Λ \ D, hoppingKernel ν u u' ≠ 0 →
      siteDist ν 0 u ≤ l ∧ l / 4 - 1 ≤ siteDist ν s u) :
    ∑ u ∈ D, ∑ u' ∈ Λ \ D, ‖hoppingKernel ν u u'‖ *
      Real.exp (-M * siteDist ν s u / 2) * Real.exp (M / 2) ≤ 1 / 2 := by
  classical
  set W : ℝ := Real.exp (-M * (l / 8 - 1)) with hW
  have hW0 : 0 < W := Real.exp_pos _
  set T : Site ν → Site ν → ℝ := fun u u' => ‖hoppingKernel ν u u'‖ *
      Real.exp (-M * siteDist ν s u / 2) * Real.exp (M / 2) with hT
  have hterm : ∀ u ∈ D, ∀ u' ∈ Λ \ D, T u u' ≤ ‖hoppingKernel ν u u'‖ * W := by
    intro u hu u' hu'
    by_cases h0 : hoppingKernel ν u u' = 0
    · simp [hT, h0]
    · obtain ⟨-, h2⟩ := hcr u hu u' hu' h0
      have hex : Real.exp (-M * siteDist ν s u / 2) * Real.exp (M / 2) ≤ W := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left h2 hM
        linarith
      simp only [hT, mul_assoc]
      exact mul_le_mul_of_nonneg_left hex (norm_nonneg _)
  have hrow : ∀ u ∈ D, ∑ u' ∈ Λ \ D, T u u' ≤ 2 * ν * W := by
    intro u hu
    calc ∑ u' ∈ Λ \ D, T u u' ≤ ∑ u' ∈ Λ \ D, ‖hoppingKernel ν u u'‖ * W :=
          Finset.sum_le_sum fun u' hu' => hterm u hu u' hu'
      _ = (∑ u' ∈ Λ \ D, ‖hoppingKernel ν u u'‖) * W := by rw [Finset.sum_mul]
      _ ≤ 2 * ν * W := mul_le_mul_of_nonneg_right (sum_norm_hoppingKernel_le ν u _) hW0.le
  have hne : ∀ u ∈ D, ∑ u' ∈ Λ \ D, T u u' ≠ 0 → siteDist ν 0 u ≤ l := by
    intro u hu hne
    by_contra hlt
    apply hne
    refine Finset.sum_eq_zero fun u' hu' => ?_
    by_cases h0 : hoppingKernel ν u u' = 0
    · simp [hT, h0]
    · exact absurd (hcr u hu u' hu' h0).1 hlt
  have hl1 : (1 : ℝ) ≤ l := hl
  rw [← Finset.sum_filter_of_ne hne]
  have hcard : (((D.filter fun u => siteDist ν 0 u ≤ l).card : ℕ) : ℝ) ≤ (5 * l) ^ ν :=
    (Nat.cast_le.2 (Finset.card_le_card (Finset.filter_subset_filter _ hDΛ))).trans
      (card_filter_siteDist_le Λ 0 hl1)
  calc _ ≤ ∑ _u ∈ D.filter (fun u => siteDist ν 0 u ≤ l), 2 * (ν : ℝ) * W :=
        Finset.sum_le_sum fun u hu => hrow u (Finset.mem_filter.1 hu).1
    _ = ((D.filter fun u => siteDist ν 0 u ≤ l).card : ℝ) * (2 * ν * W) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (5 * l) ^ ν * (2 * ν * W) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 1 / 2 := by
        have : 2 * (ν : ℝ) * (5 * l) ^ ν * W = (4 * ν * (5 * l) ^ ν * W) / 2 := by ring
        linarith [mul_comm ((5 * l) ^ ν) (2 * (ν : ℝ) * W)]

private theorem mem_of_siteDist_lt_aux {ν : ℕ} {A : Set (Site ν)} {a : Site ν} (ha : a ∈ A)
    {r : ℝ} (hbd : ∀ b ∈ vertexBoundary A, r ≤ siteDist ν a b) :
    ∀ m : ℕ, ∀ z : Site ν, ∑ j, (z j - a j).natAbs ≤ m → siteDist ν a z < r → z ∈ A := by
  intro m
  induction m with
  | zero =>
    intro z hm _
    by_cases hza : z = a
    · exact hza ▸ ha
    · obtain ⟨z', -, -, h3⟩ := exists_step a z hza
      omega
  | succ m ih =>
    intro z hm hz
    by_cases hza : z = a
    · exact hza ▸ ha
    · obtain ⟨z', h1, h2, h3⟩ := exists_step a z hza
      have hz'A : z' ∈ A := ih z' (by omega) (lt_of_le_of_lt h2 hz)
      by_contra hzA
      have := hbd z' ⟨hz'A, z, h1, hzA⟩
      linarith


theorem mem_of_siteDist_lt {ν : ℕ} {A : Set (Site ν)} {a : Site ν} (ha : a ∈ A) {r : ℝ}
    (hbd : ∀ b ∈ vertexBoundary A, r ≤ siteDist ν a b) {z : Site ν}
    (hz : siteDist ν a z < r) : z ∈ A :=
  mem_of_siteDist_lt_aux ha hbd _ z le_rfl hz

/-! ### The downward induction on the tower scale -/


private def Claim {ν : ℕ} (Λ : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0)
    (L M : ℝ) (t : Site ν) (ht : t ∈ Λ) (j : ℕ) : Prop :=
  ∀ (s : Site ν) (hs : s ∈ Λ), siteDist ν 0 s ≤ 4 ^ j * L / 4 + 1 →
    (j = 0 → 3 * L / 16 ≤ siteDist ν s t) → (j ≠ 0 → 4 ^ j * L / 8 ≤ siteDist ν 0 s) →
    ‖finiteGreen ν Λ v E ε hε ⟨s, hs⟩ ⟨t, ht⟩‖ ≤ 2 * Real.exp (-M * siteDist ν s t / 2)

private theorem claim_of_next {ν : ℕ} (Λ : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ)
    (hε : ε ≠ 0) (A : ℕ → Finset (Site ν)) {L M : ℝ} (hL : 65536 ≤ L) (hM : 0 ≤ M)
    (hin : ∀ (j : ℕ) (z : Site ν), siteDist ν 0 z < 4 ^ j * L / 2 → z ∈ A j)
    (hout : ∀ (j : ℕ), ∀ z ∈ A j, siteDist ν 0 z ≤ 4 ^ j * L)
    (hbd : ∀ (j : ℕ), ∀ u ∈ A j, ∀ u' : Site ν, siteDist ν u u' = 1 → u' ∉ A j →
      4 ^ j * L / 2 ≤ siteDist ν 0 u)
    (hG : ∀ (j : ℕ) (s w : {x // x ∈ A j ∩ Λ}), (4 ^ j * L) ^ (3 / 4 : ℝ) ≤ siteDist ν s w →
      ‖finiteGreen ν (A j ∩ Λ) v E ε hε s w‖ ≤ Real.exp (-M * siteDist ν s w))
    (hcount : ∀ j : ℕ,
      4 * ν * (5 * (4 ^ j * L)) ^ ν * Real.exp (-M * (4 ^ j * L / 8 - 1)) ≤ 1)
    {t : Site ν} (ht : t ∈ Λ) (htL : siteDist ν 0 t ≤ L / 4) (j : ℕ)
    (hnext : Λ ⊆ A j ∨ Claim Λ v E ε hε L M t ht (j + 1)) : Claim Λ v E ε hε L M t ht j := by
  intro s hs hsl hj0 hjne
  set l : ℝ := 4 ^ j * L with hl
  have hL0 : 0 ≤ L := by linarith
  have hlL : L ≤ l := le_pow_four_mul hL0 j
  have hl65 : 65536 ≤ l := by linarith
  have h34 := rpow_three_quarters_le hl65
  have hsA : s ∈ A j := hin j s (by linarith)
  have htA : t ∈ A j := hin j t (by linarith)
  have hsD : s ∈ A j ∩ Λ := Finset.mem_inter.2 ⟨hsA, hs⟩
  have htD : t ∈ A j ∩ Λ := Finset.mem_inter.2 ⟨htA, ht⟩
  have hsep : l ^ (3 / 4 : ℝ) ≤ siteDist ν s t := by
    by_cases hj : j = 0
    · have hl0 : l = L := by simp [hl, hj]
      have := hj0 hj
      rw [hl0] at h34 ⊢
      linarith
    · have h4 := four_mul_le_pow_four_mul hL0 hj
      have h8 := hjne hj
      have := siteDist_triangle ν 0 s t
      have := siteDist_comm ν t s
      have := siteDist_comm ν 0 t
      linarith
  have hdir := hG j ⟨s, hsD⟩ ⟨t, htD⟩ hsep
  have hcr : ∀ u ∈ A j ∩ Λ, ∀ u' ∈ Λ \ (A j ∩ Λ), hoppingKernel ν u u' ≠ 0 →
      siteDist ν 0 u ≤ l ∧ l / 4 - 1 ≤ siteDist ν s u := by
    intro u hu u' hu' h0
    have hu'A : u' ∉ A j := fun h => (Finset.mem_sdiff.1 hu').2 (Finset.mem_inter.2
      ⟨h, (Finset.mem_sdiff.1 hu').1⟩)
    have hd1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
    have h1 := hbd j u (Finset.mem_inter.1 hu).1 u' hd1 hu'A
    have h2 := hout j u (Finset.mem_inter.1 hu).1
    have := siteDist_triangle ν 0 u s
    have := siteDist_comm ν s u
    have := siteDist_comm ν 0 s
    exact ⟨h2, by linarith⟩
  refine norm_finiteGreen_le_of_step (Finset.inter_subset_right (s₁ := A j)) v E ε hε hM hsD htD
    hdir ?_ (crossing_weight Finset.inter_subset_right (by linarith) hM s (hcount j) hcr)
  intro u hu u' hu' h0
  have hu'A : u' ∉ A j := fun h => (Finset.mem_sdiff.1 hu').2 (Finset.mem_inter.2
    ⟨h, (Finset.mem_sdiff.1 hu').1⟩)
  obtain ⟨h2, h3⟩ := hcr u hu u' hu' h0
  refine ⟨hG j ⟨s, hsD⟩ ⟨u, hu⟩ (by
    show l ^ (3 / 4 : ℝ) ≤ siteDist ν s u
    linarith), ?_⟩
  rcases hnext with hsub | hcl
  · exact absurd (hsub (Finset.mem_sdiff.1 hu').1) hu'A
  · have hd1 := siteDist_eq_one_of_hoppingKernel_ne_zero h0
    have hl4 : (4 : ℝ) ^ (j + 1) * L = 4 * l := by rw [hl]; ring
    have hlow : l / 2 ≤ siteDist ν 0 u' := by
      by_contra hlt
      exact hu'A (hin j u' (by linarith))
    have hup := siteDist_triangle ν 0 u' u
    have hup' := siteDist_comm ν u' u
    have := siteDist_comm ν u t
    exact hcl u' (Finset.mem_sdiff.1 hu').1 (by rw [hl4]; linarith)
      (fun h => absurd h (Nat.succ_ne_zero j)) (fun _ => by rw [hl4]; linarith)


theorem norm_finiteGreen_le_of_nested {ν : ℕ} (Λ : Finset (Site ν)) (v : Site ν → ℝ)
    (E ε : ℝ) (hε : ε ≠ 0) (A : ℕ → Finset (Site ν)) {L M : ℝ} (hL : 65536 ≤ L) (hM : 0 ≤ M)
    (hin : ∀ (j : ℕ) (z : Site ν), siteDist ν 0 z < 4 ^ j * L / 2 → z ∈ A j)
    (hout : ∀ (j : ℕ), ∀ z ∈ A j, siteDist ν 0 z ≤ 4 ^ j * L)
    (hbd : ∀ (j : ℕ), ∀ u ∈ A j, ∀ u' : Site ν, siteDist ν u u' = 1 → u' ∉ A j →
      4 ^ j * L / 2 ≤ siteDist ν 0 u)
    (hG : ∀ (j : ℕ) (s w : {x // x ∈ A j ∩ Λ}), (4 ^ j * L) ^ (3 / 4 : ℝ) ≤ siteDist ν s w →
      ‖finiteGreen ν (A j ∩ Λ) v E ε hε s w‖ ≤ Real.exp (-M * siteDist ν s w))
    (hcount : ∀ j : ℕ,
      4 * ν * (5 * (4 ^ j * L)) ^ ν * Real.exp (-M * (4 ^ j * L / 8 - 1)) ≤ 1)
    {s t : Site ν} (hs : s ∈ Λ) (ht : t ∈ Λ) (hsL : siteDist ν 0 s ≤ L / 4 + 1)
    (htL : siteDist ν 0 t ≤ L / 4) (hst : 3 * L / 16 ≤ siteDist ν s t) :
    ‖finiteGreen ν Λ v E ε hε ⟨s, hs⟩ ⟨t, ht⟩‖ ≤ 2 * Real.exp (-M * siteDist ν s t / 2) := by
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z ∈ Λ, siteDist ν 0 z ≤ R :=
    ⟨Λ.sup' ⟨t, ht⟩ (fun z => siteDist ν 0 z), fun z hz =>
      Finset.le_sup' (fun z => siteDist ν 0 z) hz⟩
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (max R 0) (by norm_num : (1 : ℝ) < 4)
  have hsub : ∀ j, J ≤ j → Λ ⊆ A j := by
    intro j hj z hz
    apply hin j z
    have h1 : (4 : ℝ) ^ J ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hj
    have h2 : (4 : ℝ) ^ j ≤ 4 ^ j * L / 2 := by
      have := mul_le_mul_of_nonneg_left (show (65536 : ℝ) ≤ L from hL)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) j)
      have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) j
      linarith
    have := hR z hz
    have := le_max_left R 0
    linarith
  have hall : ∀ i j : ℕ, J ≤ j + i → Claim Λ v E ε hε L M t ht j := by
    intro i
    induction i with
    | zero =>
      intro j hj
      exact claim_of_next Λ v E ε hε A hL hM hin hout hbd hG hcount ht htL j
        (Or.inl (hsub j (by omega)))
    | succ i ih =>
      intro j hj
      exact claim_of_next Λ v E ε hε A hL hM hin hout hbd hG hcount ht htL j
        (Or.inr (ih (j + 1) (by omega)))
  exact hall J 0 (by omega) s hs (by simpa using hsL) (fun _ => hst) (fun h => absurd rfl h)


theorem exists_norm_finiteGreen_le_of_towerEvent (ν : ℕ) : ∃ L₁ : ℝ, ∀ (P : Params),
    ScaleConditions P.K₀ → ∀ (Λ : Finset (Site ν)) (v : Configuration ν) (L M : ℝ), L₁ ≤ L →
    scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) → 0 ≤ M → v ∈ towerEvent P Λ 0 L →
    (∀ k : ℕ, JPred P Λ v (k + 1) M) →
    (∀ j : ℕ, 4 * ν * (5 * (4 ^ j * L)) ^ ν * Real.exp (-M * (4 ^ j * L / 8 - 1)) ≤ 1) →
    ∀ (ε : ℝ) (hε : ε ≠ 0) (s t : Site ν) (hs : s ∈ Λ) (ht : t ∈ Λ),
      siteDist ν 0 s ≤ L / 4 + 1 → siteDist ν 0 t ≤ L / 4 → 3 * L / 16 ≤ siteDist ν s t →
      ‖finiteGreen ν Λ v P.E ε hε ⟨s, hs⟩ ⟨t, ht⟩‖ ≤ 2 * Real.exp (-M * siteDist ν s t / 2) := by
  obtain ⟨L₀, hL₀⟩ := exists_towerRegion_spec ν
  obtain ⟨L₀', hL₀'⟩ := exists_norm_finiteGreen_towerRegion_le ν
  refine ⟨max (max L₀ L₀') 65536, fun P hK Λ v L M hL h1 hM hv hJ hcount ε hε s t hs ht hsL htL
    hst => ?_⟩
  have hL65 : 65536 ≤ L := (le_max_right _ _).trans hL
  have hL0 : L₀ ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hL0' : L₀' ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hKp : 0 < P.K₀ := by
    have h := hK.1
    unfold scaleD at h
    by_contra hn
    push Not at hn
    have : Real.exp (P.K₀ * (5 / 4 : ℝ) ^ 0) ≤ 1 := by
      rw [Real.exp_le_one_iff]; simpa using hn
    linarith
  have hfin : ∀ j, (towerRegion P Λ v 0 L j).Finite := fun j => (hL₀ P hK Λ v 0 L hL0 j).1
  refine norm_finiteGreen_le_of_nested Λ v P.E ε hε (fun j => (hfin j).toFinset) hL65 hM
    ?_ ?_ ?_ ?_ hcount hs ht hsL htL hst
  · intro j z hz
    have hspec := hL₀ P hK Λ v 0 L hL0 j
    rw [Set.Finite.mem_toFinset]
    exact mem_of_siteDist_lt hspec.2.1 (fun b hb => (hspec.2.2.2.1 b hb).1) hz
  · intro j z hz
    rw [Set.Finite.mem_toFinset] at hz
    exact (hL₀ P hK Λ v 0 L hL0 j).2.2.2.2.1 hz
  · intro j u hu u' hd hu'
    rw [Set.Finite.mem_toFinset] at hu hu'
    exact ((hL₀ P hK Λ v 0 L hL0 j).2.2.2.1 u ⟨hu, u', hd, hu'⟩).1
  · intro j x y hxy
    have hLl : L ^ (3 / 4 : ℝ) ≤ (4 ^ j * L) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (le_pow_four_mul (by linarith) j) (by norm_num)
    have hlev : 1 ≤ towerLevel P.K₀ (4 ^ j * L) := one_le_towerLevel hKp (by linarith)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hlev
    have hJk : JPred P Λ v (towerLevel P.K₀ (4 ^ j * L)) M := by
      rw [hk]; exact hJ k
    exact hL₀' P hK Λ v 0 L hL0' h1 hv M j hJk (hfin j) ε hε x y hxy

end FroehlichSpencer.T12.Assembly

end
