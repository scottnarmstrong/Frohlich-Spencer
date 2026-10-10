/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.ShiftProfile
import Mathlib.Tactic

/-!
# The explicit loop shift on `ℤ⁴` and its energy

The explicit shift `α` has components along the axes 2 and 3 only,
`α_j(y) = a_{depth(y₀,y₁), j}(y₂, y₃)`, where `depth` is the distance of the column from the
boundary of the sheet and `a_d` is the transverse shift of `ShiftProfile`.

The main result is `loopEnergy_le`: the sum of the squares of the components of `σ - dα`
over any finite box is at most `6 (L + T)`.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open Finset

/-- Depth of the column `(y₀, y₁)` inside the sheet `1 ≤ y₀ ≤ L`, `1 ≤ y₁ ≤ T`; zero on the
outer layer and outside. -/
@[expose] def loopDepth (L T : ℕ) (y₀ y₁ : ℤ) : ℕ :=
  (min (min (y₀ - 1) ((L : ℤ) - y₀)) (min (y₁ - 1) ((T : ℤ) - y₁))).toNat

/-- Coefficient of the sheet 2-form `σ` on the `2–3` plaquette based at `y` (FS82 (2.49)). -/
@[expose] noncomputable def sheetCoeff (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  if 1 ≤ y₀ ∧ y₀ ≤ (L : ℤ) ∧ 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ) ∧ y₂ = 0 ∧ y₃ = 0 then 1 else 0

/-- Component along axis 2 of the explicit shift `α^{L,T}`. -/
@[expose] noncomputable def loopShiftTwo (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  shiftTwo (loopDepth L T y₀ y₁) y₂ y₃

/-- Component along axis 3 of the explicit shift `α^{L,T}`. -/
@[expose] noncomputable def loopShiftThree (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  shiftThree (loopDepth L T y₀ y₁) y₂ y₃

/-- The `2–3` component of `σ - dα`. -/
@[expose] noncomputable def loopEps23 (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  sheetCoeff L T y₀ y₁ y₂ y₃ -
    ((loopShiftThree L T y₀ y₁ (y₂ + 1) y₃ - loopShiftThree L T y₀ y₁ y₂ y₃) -
      (loopShiftTwo L T y₀ y₁ y₂ (y₃ + 1) - loopShiftTwo L T y₀ y₁ y₂ y₃))

/-- The `0–2` component of `σ - dα`. -/
@[expose] noncomputable def loopEps02 (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  -(loopShiftTwo L T (y₀ + 1) y₁ y₂ y₃ - loopShiftTwo L T y₀ y₁ y₂ y₃)

/-- The `0–3` component of `σ - dα`. -/
@[expose] noncomputable def loopEps03 (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  -(loopShiftThree L T (y₀ + 1) y₁ y₂ y₃ - loopShiftThree L T y₀ y₁ y₂ y₃)

/-- The `1–2` component of `σ - dα`. -/
@[expose] noncomputable def loopEps12 (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  -(loopShiftTwo L T y₀ (y₁ + 1) y₂ y₃ - loopShiftTwo L T y₀ y₁ y₂ y₃)

/-- The `1–3` component of `σ - dα`. -/
@[expose] noncomputable def loopEps13 (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  -(loopShiftThree L T y₀ (y₁ + 1) y₂ y₃ - loopShiftThree L T y₀ y₁ y₂ y₃)

/-- Sum over the plaquettes based at `y` of the squares of the components of `σ - dα`
(the `0–1` component vanishes). -/
@[expose] noncomputable def loopEnergyDensity (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) : ℝ :=
  loopEps23 L T y₀ y₁ y₂ y₃ ^ 2 + loopEps02 L T y₀ y₁ y₂ y₃ ^ 2 + loopEps03 L T y₀ y₁ y₂ y₃ ^ 2 +
    loopEps12 L T y₀ y₁ y₂ y₃ ^ 2 + loopEps13 L T y₀ y₁ y₂ y₃ ^ 2

/-- The energy `‖σ - dα‖²` of the explicit shift, summed over base points in the box `B⁴`. -/
@[expose] noncomputable def loopEnergy (L T : ℕ) (B : Finset ℤ) : ℝ :=
  ∑ y₀ ∈ B, ∑ y₁ ∈ B, ∑ y₂ ∈ B, ∑ y₃ ∈ B, loopEnergyDensity L T y₀ y₁ y₂ y₃

/-! ### Depth bookkeeping -/

theorem loopDepth_eq_zero_of_not_mem {L T : ℕ} {y₀ y₁ : ℤ}
    (h : ¬(1 ≤ y₀ ∧ y₀ ≤ (L : ℤ) ∧ 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ))) : loopDepth L T y₀ y₁ = 0 := by
  unfold loopDepth
  omega

/-- A column of positive depth lies strictly inside the sheet. -/
theorem loopDepth_pos {L T : ℕ} {y₀ y₁ : ℤ} (h : 0 < loopDepth L T y₀ y₁) :
    (2 ≤ y₀ ∧ y₀ + 1 ≤ (L : ℤ)) ∧ (2 ≤ y₁ ∧ y₁ + 1 ≤ (T : ℤ)) := by
  unfold loopDepth at h
  omega

theorem loopDepth_le (L T : ℕ) (y₀ y₁ : ℤ) :
    (loopDepth L T y₀ y₁ : ℤ) ≤ L ∧ (loopDepth L T y₀ y₁ : ℤ) ≤ T := by
  unfold loopDepth
  omega

theorem loopDepth_step₀ (L T : ℕ) (y₀ y₁ : ℤ) :
    loopDepth L T (y₀ + 1) y₁ = loopDepth L T y₀ y₁ ∨
      loopDepth L T (y₀ + 1) y₁ = loopDepth L T y₀ y₁ + 1 ∨
      loopDepth L T y₀ y₁ = loopDepth L T (y₀ + 1) y₁ + 1 := by
  unfold loopDepth
  omega

theorem loopDepth_step₁ (L T : ℕ) (y₀ y₁ : ℤ) :
    loopDepth L T y₀ (y₁ + 1) = loopDepth L T y₀ y₁ ∨
      loopDepth L T y₀ (y₁ + 1) = loopDepth L T y₀ y₁ + 1 ∨
      loopDepth L T y₀ y₁ = loopDepth L T y₀ (y₁ + 1) + 1 := by
  unfold loopDepth
  omega

theorem loopDepth_step₀_ne {L T : ℕ} {y₀ y₁ : ℤ}
    (h : loopDepth L T (y₀ + 1) y₁ ≠ loopDepth L T y₀ y₁) :
    (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ) - 1 ∧ 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) ∧
      min (loopDepth L T y₀ y₁) (loopDepth L T (y₀ + 1) y₁) =
        (min (y₀ - 1) ((L : ℤ) - 1 - y₀)).toNat := by
  unfold loopDepth at h ⊢
  omega

theorem loopDepth_step₁_ne {L T : ℕ} {y₀ y₁ : ℤ}
    (h : loopDepth L T y₀ (y₁ + 1) ≠ loopDepth L T y₀ y₁) :
    (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ) ∧ 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ) - 1) ∧
      min (loopDepth L T y₀ y₁) (loopDepth L T y₀ (y₁ + 1)) =
        (min (y₁ - 1) ((T : ℤ) - 1 - y₁)).toNat := by
  unfold loopDepth at h ⊢
  omega

/-! ### The components of `σ - dα` -/

/-- On the sheet columns the `2–3` component is the spread flux; elsewhere it vanishes. -/
theorem loopEps23_eq (L T : ℕ) (y₀ y₁ y₂ y₃ : ℤ) :
    loopEps23 L T y₀ y₁ y₂ y₃ =
      if 1 ≤ y₀ ∧ y₀ ≤ (L : ℤ) ∧ 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ) then
        uni (loopDepth L T y₀ y₁) y₂ * uni (loopDepth L T y₀ y₁) y₃
      else 0 := by
  have hcurl := curl_shift (loopDepth L T y₀ y₁) y₂ y₃
  unfold loopEps23 loopShiftThree loopShiftTwo
  rw [hcurl]
  by_cases hR : 1 ≤ y₀ ∧ y₀ ≤ (L : ℤ) ∧ 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)
  · rw [ite_eq_left hR]
    have hs : sheetCoeff L T y₀ y₁ y₂ y₃ = uni 0 y₂ * uni 0 y₃ := by
      unfold sheetCoeff
      rw [uni_zero, uni_zero]
      by_cases h2 : y₂ = 0 <;> by_cases h3 : y₃ = 0 <;> simp [hR, h2, h3]
    rw [hs]
    ring
  · rw [ite_eq_right hR, loopDepth_eq_zero_of_not_mem hR]
    have hs : sheetCoeff L T y₀ y₁ y₂ y₃ = 0 := by
      unfold sheetCoeff
      rw [ite_eq_right]
      intro h
      exact hR ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [hs]
    ring

/-- The squared norm of the difference of two consecutive transverse shifts. -/
theorem sum_shift_diff_sq_le {d d' : ℕ} (h : d' = d ∨ d' = d + 1 ∨ d = d' + 1)
    (s t : Finset ℤ) :
    ∑ y ∈ s, ∑ z ∈ t, ((-(shiftTwo d' y z - shiftTwo d y z)) ^ 2 +
        (-(shiftThree d' y z - shiftThree d y z)) ^ 2) ≤
      if d' = d then 0 else levelBound (min d d') := by
  rcases h with h | h | h
  · subst h
    simp
  · subst h
    have hne : d + 1 ≠ d := by omega
    rw [ite_eq_right hne, min_eq_left (by omega : d ≤ d + 1)]
    refine le_trans (le_of_eq ?_) (sum_level_sq_le d s t)
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    rw [shiftTwo_succ, shiftThree_succ]
    ring
  · subst h
    have hne : d' ≠ d' + 1 := by omega
    rw [ite_eq_right hne, min_eq_right (by omega : d' ≤ d' + 1)]
    refine le_trans (le_of_eq ?_) (sum_level_sq_le d' s t)
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    rw [shiftTwo_succ, shiftThree_succ]
    ring

/-- Bound for the sheet term in the column `(y₀, y₁)`. -/
@[expose] noncomputable def sheetColumnBound (L T : ℕ) (y₀ y₁ : ℤ) : ℝ :=
  if (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) then
    1 / ((loopDepth L T y₀ y₁ : ℝ) + 1) ^ 2
  else 0

/-- Bound for the wall between the columns `(y₀, y₁)` and `(y₀ + 1, y₁)`. -/
@[expose] noncomputable def wallBound₀ (L T : ℕ) (y₀ y₁ : ℤ) : ℝ :=
  if (1 ≤ y₀ ∧ y₀ ≤ ((L - 1 : ℕ) : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) then
    levelBound (min (y₀ - 1) ((L : ℤ) - 1 - y₀)).toNat
  else 0

/-- Bound for the wall between the columns `(y₀, y₁)` and `(y₀, y₁ + 1)`. -/
@[expose] noncomputable def wallBound₁ (L T : ℕ) (y₀ y₁ : ℤ) : ℝ :=
  if (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ ((T - 1 : ℕ) : ℤ)) then
    levelBound (min (y₁ - 1) ((T : ℤ) - 1 - y₁)).toNat
  else 0

theorem sheetColumnBound_nonneg (L T : ℕ) (y₀ y₁ : ℤ) : 0 ≤ sheetColumnBound L T y₀ y₁ := by
  unfold sheetColumnBound
  split_ifs
  · positivity
  · exact le_rfl

theorem wallBound₀_nonneg (L T : ℕ) (y₀ y₁ : ℤ) : 0 ≤ wallBound₀ L T y₀ y₁ := by
  unfold wallBound₀
  split_ifs
  · exact levelBound_nonneg _
  · exact le_rfl

theorem wallBound₁_nonneg (L T : ℕ) (y₀ y₁ : ℤ) : 0 ≤ wallBound₁ L T y₀ y₁ := by
  unfold wallBound₁
  split_ifs
  · exact levelBound_nonneg _
  · exact le_rfl

theorem sum_loopEps23_sq_le (L T : ℕ) (y₀ y₁ : ℤ) (s t : Finset ℤ) :
    ∑ y₂ ∈ s, ∑ y₃ ∈ t, loopEps23 L T y₀ y₁ y₂ y₃ ^ 2 ≤ sheetColumnBound L T y₀ y₁ := by
  unfold sheetColumnBound
  by_cases hR : 1 ≤ y₀ ∧ y₀ ≤ (L : ℤ) ∧ 1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)
  · have hR' : (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) :=
      ⟨⟨hR.1, hR.2.1⟩, hR.2.2.1, hR.2.2.2⟩
    rw [ite_eq_left hR']
    refine le_trans (le_of_eq ?_) (sum_spread_sq_le (loopDepth L T y₀ y₁) s t)
    refine sum_congr rfl fun y₂ _ => sum_congr rfl fun y₃ _ => ?_
    rw [loopEps23_eq, ite_eq_left hR]
  · have hR' : ¬((1 ≤ y₀ ∧ y₀ ≤ (L : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ (T : ℤ))) := by
      intro h
      exact hR ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
    rw [ite_eq_right hR']
    refine le_of_eq (sum_eq_zero fun y₂ _ => sum_eq_zero fun y₃ _ => ?_)
    rw [loopEps23_eq, ite_eq_right hR]
    ring

theorem sum_loopEps0_sq_le (L T : ℕ) (y₀ y₁ : ℤ) (s t : Finset ℤ) :
    ∑ y₂ ∈ s, ∑ y₃ ∈ t, (loopEps02 L T y₀ y₁ y₂ y₃ ^ 2 + loopEps03 L T y₀ y₁ y₂ y₃ ^ 2) ≤
      wallBound₀ L T y₀ y₁ := by
  have h := sum_shift_diff_sq_le (loopDepth_step₀ L T y₀ y₁) s t
  refine le_trans h ?_
  by_cases hd : loopDepth L T (y₀ + 1) y₁ = loopDepth L T y₀ y₁
  · rw [ite_eq_left hd]
    exact wallBound₀_nonneg L T y₀ y₁
  · rw [ite_eq_right hd]
    obtain ⟨hmem, hmin⟩ := loopDepth_step₀_ne hd
    have hmem' : (1 ≤ y₀ ∧ y₀ ≤ ((L - 1 : ℕ) : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) := by omega
    unfold wallBound₀
    rw [ite_eq_left hmem', hmin]

theorem sum_loopEps1_sq_le (L T : ℕ) (y₀ y₁ : ℤ) (s t : Finset ℤ) :
    ∑ y₂ ∈ s, ∑ y₃ ∈ t, (loopEps12 L T y₀ y₁ y₂ y₃ ^ 2 + loopEps13 L T y₀ y₁ y₂ y₃ ^ 2) ≤
      wallBound₁ L T y₀ y₁ := by
  have h := sum_shift_diff_sq_le (loopDepth_step₁ L T y₀ y₁) s t
  refine le_trans h ?_
  by_cases hd : loopDepth L T y₀ (y₁ + 1) = loopDepth L T y₀ y₁
  · rw [ite_eq_left hd]
    exact wallBound₁_nonneg L T y₀ y₁
  · rw [ite_eq_right hd]
    obtain ⟨hmem, hmin⟩ := loopDepth_step₁_ne hd
    have hmem' : (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ ((T - 1 : ℕ) : ℤ)) := by omega
    unfold wallBound₁
    rw [ite_eq_left hmem', hmin]

/-! ### Sums over the columns -/

/-- A nonnegative function on `ℤ²` supported in `[1,n] × [1,m]` has every finite partial sum
bounded by the sum over that rectangle. -/
theorem sum_sum_le_sum_range_of_rect (f : ℤ → ℤ → ℝ) (hf : ∀ a b, 0 ≤ f a b) (n m : ℕ)
    (hsupp : ∀ a b, f a b ≠ 0 → (1 ≤ a ∧ a ≤ (n : ℤ)) ∧ (1 ≤ b ∧ b ≤ (m : ℤ)))
    (s t : Finset ℤ) :
    ∑ a ∈ s, ∑ b ∈ t, f a b ≤
      ∑ k ∈ range n, ∑ k' ∈ range m, f ((k : ℤ) + 1) ((k' : ℤ) + 1) := by
  have houter := sum_le_sum_range_of_param (fun a => ∑ b ∈ t, f a b)
    (fun a => sum_nonneg fun b _ => hf a b) n (fun k => (k : ℤ) + 1)
    (by
      intro a ha
      obtain ⟨b, _, hb⟩ := exists_ne_zero_of_sum_ne_zero ha
      have h := (hsupp a b hb).1
      exact ⟨(a - 1).toNat, by omega, by omega⟩) s
  refine houter.trans (sum_le_sum fun k _ => ?_)
  exact sum_le_sum_range_of_param (fun b => f ((k : ℤ) + 1) b) (fun b => hf _ b) m
    (fun k' => (k' : ℤ) + 1)
    (by
      intro b hb
      have h := (hsupp _ b hb).2
      exact ⟨(b - 1).toNat, by omega, by omega⟩) t

theorem sum_sheetColumnBound_le (L T : ℕ) (s t : Finset ℤ) :
    ∑ y₀ ∈ s, ∑ y₁ ∈ t, sheetColumnBound L T y₀ y₁ ≤ 4 * ((L : ℝ) + T) := by
  have h := sum_sum_le_sum_range_of_rect (sheetColumnBound L T)
    (sheetColumnBound_nonneg L T) L T
    (by
      intro a b hab
      by_contra hc
      exact hab (by unfold sheetColumnBound; rw [ite_eq_right hc])) s t
  refine h.trans ?_
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  refine le_trans (le_of_eq ?_) ((sheet_sum_le L' T').trans (le_of_eq ?_))
  · refine sum_congr rfl fun k hk => sum_congr rfl fun k' hk' => ?_
    have hk1 : k ≤ L' := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hk2 : k' ≤ T' := Nat.lt_succ_iff.mp (mem_range.mp hk')
    have hmem : (1 ≤ (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ ((L' + 1 : ℕ) : ℤ)) ∧
        (1 ≤ (k' : ℤ) + 1 ∧ (k' : ℤ) + 1 ≤ ((T' + 1 : ℕ) : ℤ)) := by omega
    have hdepth : loopDepth (L' + 1) (T' + 1) ((k : ℤ) + 1) ((k' : ℤ) + 1) =
        min (min k (L' - k)) (min k' (T' - k')) := by
      unfold loopDepth
      omega
    unfold sheetColumnBound
    rw [ite_eq_left hmem, hdepth]
  · push_cast
    ring

theorem sum_wallBound₀_le (L T : ℕ) (s t : Finset ℤ) :
    ∑ y₀ ∈ s, ∑ y₁ ∈ t, wallBound₀ L T y₀ y₁ ≤ 2 * (T : ℝ) := by
  have h := sum_sum_le_sum_range_of_rect (wallBound₀ L T) (wallBound₀_nonneg L T) (L - 1) T
    (by
      intro a b hab
      by_contra hc
      exact hab (by unfold wallBound₀; rw [ite_eq_right hc])) s t
  refine h.trans ?_
  rcases Nat.lt_or_ge L 2 with hL | hL
  · have h0 : L - 1 = 0 := by omega
    rw [h0]
    simp
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have hrange : m + 2 - 1 = m + 1 := by omega
  rw [hrange]
  have hterm : ∀ k ∈ range (m + 1), ∀ k' ∈ range T,
      wallBound₀ (m + 2) T ((k : ℤ) + 1) ((k' : ℤ) + 1) = levelBound (min k (m - k)) := by
    intro k hk k' hk'
    have hk1 : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hk2 : k' < T := mem_range.mp hk'
    have hmem : (1 ≤ (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ ((m + 2 - 1 : ℕ) : ℤ)) ∧
        (1 ≤ (k' : ℤ) + 1 ∧ (k' : ℤ) + 1 ≤ (T : ℤ)) := by omega
    have hmin : (min ((k : ℤ) + 1 - 1) (((m + 2 : ℕ) : ℤ) - 1 - ((k : ℤ) + 1))).toNat =
        min k (m - k) := by omega
    unfold wallBound₀
    rw [ite_eq_left hmem, hmin]
  calc ∑ k ∈ range (m + 1), ∑ k' ∈ range T,
        wallBound₀ (m + 2) T ((k : ℤ) + 1) ((k' : ℤ) + 1)
      = ∑ k ∈ range (m + 1), ∑ k' ∈ range T, levelBound (min k (m - k)) :=
        sum_congr rfl fun k hk => sum_congr rfl fun k' hk' => hterm k hk k' hk'
    _ = (T : ℝ) * ∑ k ∈ range (m + 1), levelBound (min k (m - k)) := by
        simp only [sum_const, card_range, nsmul_eq_mul, mul_sum]
    _ ≤ (T : ℝ) * 2 := by
        gcongr
        exact tent_levelBound_sum_le m
    _ = 2 * (T : ℝ) := by ring

theorem sum_wallBound₁_le (L T : ℕ) (s t : Finset ℤ) :
    ∑ y₀ ∈ s, ∑ y₁ ∈ t, wallBound₁ L T y₀ y₁ ≤ 2 * (L : ℝ) := by
  have h := sum_sum_le_sum_range_of_rect (wallBound₁ L T) (wallBound₁_nonneg L T) L (T - 1)
    (by
      intro a b hab
      by_contra hc
      exact hab (by unfold wallBound₁; rw [ite_eq_right hc])) s t
  refine h.trans ?_
  rcases Nat.lt_or_ge T 2 with hT | hT
  · have h0 : T - 1 = 0 := by omega
    rw [h0]
    simp
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 2 := ⟨T - 2, by omega⟩
  have hrange : m + 2 - 1 = m + 1 := by omega
  rw [hrange]
  have hterm : ∀ k ∈ range L, ∀ k' ∈ range (m + 1),
      wallBound₁ L (m + 2) ((k : ℤ) + 1) ((k' : ℤ) + 1) = levelBound (min k' (m - k')) := by
    intro k hk k' hk'
    have hk1 : k < L := mem_range.mp hk
    have hk2 : k' ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk')
    have hmem : (1 ≤ (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ (L : ℤ)) ∧
        (1 ≤ (k' : ℤ) + 1 ∧ (k' : ℤ) + 1 ≤ ((m + 2 - 1 : ℕ) : ℤ)) := by omega
    have hmin : (min ((k' : ℤ) + 1 - 1) (((m + 2 : ℕ) : ℤ) - 1 - ((k' : ℤ) + 1))).toNat =
        min k' (m - k') := by omega
    unfold wallBound₁
    rw [ite_eq_left hmem, hmin]
  calc ∑ k ∈ range L, ∑ k' ∈ range (m + 1),
        wallBound₁ L (m + 2) ((k : ℤ) + 1) ((k' : ℤ) + 1)
      = ∑ k ∈ range L, ∑ k' ∈ range (m + 1), levelBound (min k' (m - k')) :=
        sum_congr rfl fun k hk => sum_congr rfl fun k' hk' => hterm k hk k' hk'
    _ = (L : ℝ) * ∑ k' ∈ range (m + 1), levelBound (min k' (m - k')) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (L : ℝ) * 2 := by
        gcongr
        exact tent_levelBound_sum_le m
    _ = 2 * (L : ℝ) := by ring

/-- **The explicit shift has perimeter-order energy** (``, Theorem 5.1): over every finite
box, `‖σ - dα‖² ≤ 6 (L + T)`. -/
theorem loopEnergy_le (L T : ℕ) (B : Finset ℤ) : loopEnergy L T B ≤ 6 * ((L : ℝ) + T) := by
  have hcol : ∀ y₀ y₁ : ℤ, ∑ y₂ ∈ B, ∑ y₃ ∈ B, loopEnergyDensity L T y₀ y₁ y₂ y₃ ≤
      sheetColumnBound L T y₀ y₁ + wallBound₀ L T y₀ y₁ + wallBound₁ L T y₀ y₁ := by
    intro y₀ y₁
    have e : ∑ y₂ ∈ B, ∑ y₃ ∈ B, loopEnergyDensity L T y₀ y₁ y₂ y₃ =
        ∑ y₂ ∈ B, ∑ y₃ ∈ B, loopEps23 L T y₀ y₁ y₂ y₃ ^ 2 +
          ∑ y₂ ∈ B, ∑ y₃ ∈ B,
            (loopEps02 L T y₀ y₁ y₂ y₃ ^ 2 + loopEps03 L T y₀ y₁ y₂ y₃ ^ 2) +
          ∑ y₂ ∈ B, ∑ y₃ ∈ B,
            (loopEps12 L T y₀ y₁ y₂ y₃ ^ 2 + loopEps13 L T y₀ y₁ y₂ y₃ ^ 2) := by
      simp only [loopEnergyDensity, sum_add_distrib]
      ring
    rw [e]
    exact add_le_add (add_le_add (sum_loopEps23_sq_le L T y₀ y₁ B B)
      (sum_loopEps0_sq_le L T y₀ y₁ B B)) (sum_loopEps1_sq_le L T y₀ y₁ B B)
  have h1 := sum_sheetColumnBound_le L T B B
  have h2 := sum_wallBound₀_le L T B B
  have h3 := sum_wallBound₁_le L T B B
  calc loopEnergy L T B
      ≤ ∑ y₀ ∈ B, ∑ y₁ ∈ B,
          (sheetColumnBound L T y₀ y₁ + wallBound₀ L T y₀ y₁ + wallBound₁ L T y₀ y₁) :=
        sum_le_sum fun y₀ _ => sum_le_sum fun y₁ _ => hcol y₀ y₁
    _ = ∑ y₀ ∈ B, ∑ y₁ ∈ B, sheetColumnBound L T y₀ y₁ +
          ∑ y₀ ∈ B, ∑ y₁ ∈ B, wallBound₀ L T y₀ y₁ +
          ∑ y₀ ∈ B, ∑ y₁ ∈ B, wallBound₁ L T y₀ y₁ := by
        simp only [sum_add_distrib]
    _ ≤ 6 * ((L : ℝ) + T) := by linarith

end FroehlichSpencer.FS82.Wilson

end
