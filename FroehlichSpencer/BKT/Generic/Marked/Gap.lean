/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Concrete-mark charge gaps

The marked composite `ξ ϱ₀ + ϱ` of (2.29) is real-valued
(`markedDensity`); the energy estimate of Coulomb B needs every charged constituent to carry a
charge at least `q_* > 0` in absolute value.

* `IsGapped η q`: `q` is at distance at least `η` from `ℤ`; equivalent to FS81's interval form
  `q ∈ [m + η, m + 1 − η]` (`IsGapped.exists_mem_Icc`, `isGapped_of_mem_Icc`).
* `dipoleGap ξ = min(ξ, 1 − ξ)`, the `η` of CG.s5.
* **Unit marks** (`IsUnitMark`: every partial charge in `{−1, 0, 1}`): on a set `S` carrying a
  nonzero mark part, the marked charge is `±ξ + n`, hence `η`-gapped (`unitMark_isGapped`);
  otherwise it is the integer charge (`setCharge_markedDensity_of_sum_eq_zero`).

Every nonzero
  marked charge has `|q| ≥ η` (`unitMark_le_abs_setCharge`).
* **The dipole** `δ_o − δ_x` (`dipoleMark`) is a neutral unit mark: CG.s5's charge-structure
  lemma is `dipole_isGapped_of_separates` (sets separating `o` from `x`) and
  `dipole_setCharge_of_not_separates`; `dipole_le_abs_setCharge` is "charged ⇒ `|q| ≥ η`".
* `dipole_condition228_restriction`: FS81 (2.28) for the dipole in the restriction reading of
  CORE D:2.28, with `ξ′ = η`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

variable {V : Type*}

/-! ### Marked composites and gapped charges -/

/-- The marked composite `ξ ϱ₀ + ϱ` of FS81 (2.29): a real-valued density built from the integer
mark `ϱ₀` and an integer density `ϱ` (FS81's `ϱ^𝒩`). -/
def markedDensity (ξ : ℝ) (ϱ₀ ϱ : V → ℤ) : V → ℝ :=
  fun j => ξ * (ϱ₀ j : ℝ) + (ϱ j : ℝ)

/-- The total charge `Q` of a real density on a finite set of sites. -/
def setCharge (f : V → ℝ) (S : Finset V) : ℝ :=
  ∑ j ∈ S, f j

/-- `q` lies at distance at least `η` from every integer (FS81 (2.28): `q ∈ [m + η, m + 1 − η]`
for some integer `m`; see `IsGapped.exists_mem_Icc`). -/
def IsGapped (η q : ℝ) : Prop :=
  ∀ m : ℤ, η ≤ |q - m|

theorem IsGapped.le_abs {η q : ℝ} (h : IsGapped η q) : η ≤ |q| := by
  simpa using h 0

theorem IsGapped.ne_zero {η q : ℝ} (h : IsGapped η q) (hη : 0 < η) : q ≠ 0 := by
  intro hq
  have := h.le_abs
  rw [hq, abs_zero] at this
  linarith

theorem IsGapped.add_int {η q : ℝ} (h : IsGapped η q) (n : ℤ) : IsGapped η (q + n) := by
  intro m
  have := h (m - n)
  push_cast at this
  rwa [show q + (n : ℝ) - m = q - (m - n) by ring]

theorem IsGapped.neg {η q : ℝ} (h : IsGapped η q) : IsGapped η (-q) := by
  intro m
  have := h (-m)
  push_cast at this
  rwa [show -q - (m : ℝ) = -(q - -m) by ring, abs_neg]

theorem IsGapped.mono {η η' q : ℝ} (h : IsGapped η q) (hη : η' ≤ η) : IsGapped η' q :=
  fun m => hη.trans (h m)

/-- FS81's form of a gapped charge: `q ∈ [m + η, m + 1 − η]` for an integer `m`. -/
theorem IsGapped.exists_mem_Icc {η q : ℝ} (h : IsGapped η q) :
    ∃ m : ℤ, (m : ℝ) + η ≤ q ∧ q ≤ (m : ℝ) + 1 - η := by
  refine ⟨⌊q⌋, ?_, ?_⟩
  · have h1 := h ⌊q⌋
    have h2 := Int.floor_le q
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  · have h1 := h (⌊q⌋ + 1)
    have h2 := Int.lt_floor_add_one q
    push_cast at h1
    rw [abs_of_neg (by linarith)] at h1
    linarith

/-- Conversely, FS81's interval form implies the gap. -/
theorem isGapped_of_mem_Icc {η q : ℝ} (hη : 0 ≤ η) {m : ℤ}
    (h1 : (m : ℝ) + η ≤ q) (h2 : q ≤ (m : ℝ) + 1 - η) : IsGapped η q := by
  intro n
  rcases le_or_gt n m with hnm | hnm
  · have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hnm
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem setCharge_markedDensity (ξ : ℝ) (ϱ₀ ϱ : V → ℤ) (S : Finset V) :
    setCharge (markedDensity ξ ϱ₀ ϱ) S =
      ξ * ((∑ j ∈ S, ϱ₀ j : ℤ) : ℝ) + ((∑ j ∈ S, ϱ j : ℤ) : ℝ) := by
  unfold setCharge markedDensity
  push_cast
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-! ### The gap `η = min(ξ, 1 − ξ)` -/

/-- The dipole gap `η = min(ξ, 1 − ξ)` of CG.s5. -/
def dipoleGap (ξ : ℝ) : ℝ :=
  min ξ (1 - ξ)

theorem dipoleGap_pos {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ < 1) : 0 < dipoleGap ξ :=
  lt_min h0 (by linarith)

theorem dipoleGap_le_half (ξ : ℝ) : dipoleGap ξ ≤ 1 / 2 := by
  unfold dipoleGap
  rcases le_total ξ (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem dipoleGap_le_one (ξ : ℝ) : dipoleGap ξ ≤ 1 :=
  (dipoleGap_le_half ξ).trans (by norm_num)

/-- `±ξ + n` is `η`-gapped for every integer `n`, `η = min(ξ, 1 − ξ)`. -/
theorem isGapped_mul_add_int {ξ : ℝ} {k : ℤ} (hk : k = 1 ∨ k = -1) (n : ℤ) :
    IsGapped (dipoleGap ξ) (k * ξ + n) := by
  intro m
  rcases hk with rfl | rfl
  · push_cast
    rcases le_or_gt (m - n) 0 with h | h
    · have : (m : ℝ) - n ≤ 0 := by exact_mod_cast h
      calc dipoleGap ξ ≤ ξ := min_le_left _ _
        _ ≤ |1 * ξ + n - m| := by
          rw [show (1 : ℝ) * ξ + n - m = ξ - (m - n) by ring]
          exact (le_abs_self _).trans' (by linarith [le_abs_self (ξ - (m - n))])
    · have : (1 : ℝ) ≤ m - n := by exact_mod_cast h
      calc dipoleGap ξ ≤ 1 - ξ := min_le_right _ _
        _ ≤ |1 * ξ + n - m| := by
          rw [show (1 : ℝ) * ξ + n - m = -((m - n) - ξ) by ring, abs_neg]
          exact (le_abs_self _).trans' (by linarith)
  · push_cast
    rcases le_or_gt (n - m) 0 with h | h
    · have : (n : ℝ) - m ≤ 0 := by exact_mod_cast h
      calc dipoleGap ξ ≤ ξ := min_le_left _ _
        _ ≤ |-1 * ξ + n - m| := by
          rw [show (-1 : ℝ) * ξ + n - m = -(ξ - (n - m)) by ring, abs_neg]
          exact (le_abs_self _).trans' (by linarith)
    · have : (1 : ℝ) ≤ n - m := by exact_mod_cast h
      calc dipoleGap ξ ≤ 1 - ξ := min_le_right _ _
        _ ≤ |-1 * ξ + n - m| := by
          rw [show (-1 : ℝ) * ξ + n - m = (n - m) - ξ by ring]
          exact (le_abs_self _).trans' (by linarith)

/-! ### Unit marks and the dipole -/

/-- A mark whose partial charges `∑_{j ∈ S} ϱ₀(j)` all lie in `{-1, 0, 1}` (the dipole
`δ_o − δ_x` and the single sites `±δ_x`). -/
def IsUnitMark (ϱ₀ : V → ℤ) : Prop :=
  ∀ S : Finset V, |∑ j ∈ S, ϱ₀ j| ≤ 1


theorem unitMark_isGapped {ϱ₀ : V → ℤ} (hU : IsUnitMark ϱ₀) (ξ : ℝ) (ϱ : V → ℤ)
    (S : Finset V) (hS : ∑ j ∈ S, ϱ₀ j ≠ 0) :
    IsGapped (dipoleGap ξ) (setCharge (markedDensity ξ ϱ₀ ϱ) S) := by
  rw [setCharge_markedDensity]
  have hk : ∑ j ∈ S, ϱ₀ j = 1 ∨ ∑ j ∈ S, ϱ₀ j = -1 := by
    have := hU S
    rw [abs_le] at this
    omega
  have := isGapped_mul_add_int (ξ := ξ) hk (∑ j ∈ S, ϱ j)
  rwa [mul_comm] at this

/-- When `S` carries no net mark charge, the marked charge on `S` is the integer charge. -/
theorem setCharge_markedDensity_of_sum_eq_zero (ξ : ℝ) {ϱ₀ : V → ℤ} (ϱ : V → ℤ)
    (S : Finset V) (hS : ∑ j ∈ S, ϱ₀ j = 0) :
    setCharge (markedDensity ξ ϱ₀ ϱ) S = ((∑ j ∈ S, ϱ j : ℤ) : ℝ) := by
  rw [setCharge_markedDensity, hS]
  simp

/-- **Charged ⇒ gapped below** for unit marks: every nonzero marked charge has `|q| ≥ η`
(`η ≤ 1`, integer charges have `|q| ≥ 1`). -/
theorem unitMark_le_abs_setCharge {ϱ₀ : V → ℤ} (hU : IsUnitMark ϱ₀) (ξ : ℝ) (ϱ : V → ℤ)
    (S : Finset V) (hne : setCharge (markedDensity ξ ϱ₀ ϱ) S ≠ 0) :
    dipoleGap ξ ≤ |setCharge (markedDensity ξ ϱ₀ ϱ) S| := by
  by_cases hS : ∑ j ∈ S, ϱ₀ j = 0
  · rw [setCharge_markedDensity_of_sum_eq_zero ξ ϱ S hS] at hne ⊢
    have hn : (∑ j ∈ S, ϱ j) ≠ 0 := by exact_mod_cast hne
    have h1 : (1 : ℝ) ≤ |((∑ j ∈ S, ϱ j : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    exact (dipoleGap_le_one ξ).trans h1
  · exact (unitMark_isGapped hU ξ ϱ S hS).le_abs

section Dipole

variable [DecidableEq V]

/-- The fractional dipole of Coulomb B: `ϱ₀ = δ_o − δ_x` (FS81 p. 544, (1.22)). -/
def dipoleMark (o x : V) : V → ℤ :=
  fun j => (if j = o then 1 else 0) - (if j = x then 1 else 0)

theorem sum_dipoleMark (o x : V) (S : Finset V) :
    ∑ j ∈ S, dipoleMark o x j = (if o ∈ S then 1 else 0) - (if x ∈ S then 1 else 0) := by
  unfold dipoleMark
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

theorem isUnitMark_dipoleMark (o x : V) : IsUnitMark (dipoleMark o x) := by
  intro S
  rw [sum_dipoleMark]
  split_ifs <;> norm_num

theorem dipoleMark_ne_zero {o x : V} (hox : o ≠ x) : dipoleMark o x ≠ 0 := by
  intro h
  have := congrFun h o
  simp [dipoleMark, hox] at this

/-- The dipole is neutral. -/
theorem sum_univ_dipoleMark [Fintype V] (o x : V) : ∑ j, dipoleMark o x j = 0 := by
  rw [sum_dipoleMark]
  simp

/-- **Dipole charge-structure lemma** (CG.s5): if `S` separates `o` from `x`, the charge of
`ξ(δ_o − δ_x) + ϱ` on `S` is `±ξ + n`, at distance at least `η = min(ξ, 1 − ξ)` from `ℤ`. -/
theorem dipole_isGapped_of_separates {o x : V} (ξ : ℝ) (ϱ : V → ℤ) (S : Finset V)
    (hS : (o ∈ S ∧ x ∉ S) ∨ (o ∉ S ∧ x ∈ S)) :
    IsGapped (dipoleGap ξ) (setCharge (markedDensity ξ (dipoleMark o x) ϱ) S) := by
  refine unitMark_isGapped (isUnitMark_dipoleMark o x) ξ ϱ S ?_
  rw [sum_dipoleMark]
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- If `S` contains both or neither of `o, x`, the marked charge on `S` is an integer. -/
theorem dipole_setCharge_of_not_separates {o x : V} (ξ : ℝ) (ϱ : V → ℤ)
    (S : Finset V) (hS : (o ∈ S ↔ x ∈ S)) :
    setCharge (markedDensity ξ (dipoleMark o x) ϱ) S = ((∑ j ∈ S, ϱ j : ℤ) : ℝ) := by
  refine setCharge_markedDensity_of_sum_eq_zero ξ ϱ S ?_
  rw [sum_dipoleMark]
  by_cases ho : o ∈ S
  · simp [ho, hS.mp ho]
  · have hx : x ∉ S := fun h => ho (hS.mpr h)
    simp [ho, hx]

/-- **CG.s5 (charged ⇒ `|q| ≥ η`)** for the dipole. -/
theorem dipole_le_abs_setCharge (o x : V) (ξ : ℝ) (ϱ : V → ℤ) (S : Finset V)
    (hne : setCharge (markedDensity ξ (dipoleMark o x) ϱ) S ≠ 0) :
    dipoleGap ξ ≤ |setCharge (markedDensity ξ (dipoleMark o x) ϱ) S| :=
  unitMark_le_abs_setCharge (isUnitMark_dipoleMark o x) ξ ϱ S hne

/-- The restriction gap of the dipole: if `S` meets the dipole's support and misses part of it,
`ξ ∑_{j ∈ S} ϱ₀(j) = ±ξ` is `η`-gapped. -/
theorem dipole_isGapped_restriction {o x : V} (ξ : ℝ) (S : Finset V)
    (h1 : ∃ j ∈ S, dipoleMark o x j ≠ 0) (h2 : ∃ j ∉ S, dipoleMark o x j ≠ 0) :
    IsGapped (dipoleGap ξ) (ξ * ((∑ j ∈ S, dipoleMark o x j : ℤ) : ℝ)) := by
  have hsupp : ∀ j, dipoleMark o x j ≠ 0 → j = o ∨ j = x := by
    intro j hj
    by_contra h
    push Not at h
    exact hj (by simp [dipoleMark, h.1, h.2])
  have hsep : (o ∈ S ∧ x ∉ S) ∨ (o ∉ S ∧ x ∈ S) := by
    obtain ⟨j₁, hj₁S, hj₁⟩ := h1
    obtain ⟨j₂, hj₂S, hj₂⟩ := h2
    rcases hsupp j₁ hj₁ with rfl | rfl <;> rcases hsupp j₂ hj₂ with rfl | rfl
    · exact absurd hj₁S hj₂S
    · exact Or.inl ⟨hj₁S, hj₂S⟩
    · exact Or.inr ⟨hj₂S, hj₁S⟩
    · exact absurd hj₁S hj₂S
  have hg := dipole_isGapped_of_separates (o := o) (x := x) ξ 0 S hsep
  rw [setCharge_markedDensity] at hg
  simpa only [Pi.zero_apply, Finset.sum_const_zero, Int.cast_zero, add_zero] using hg

/-- FS81 Condition (2.28) for the dipole, read for **restrictions** `ϱ' = ϱ₀|_S` (the reading of
CORE D:2.28): if the restriction and its complement are both nonzero, then
`Q(ξ ϱ') ∈ [m + η, m + 1 − η]` with `η = min(ξ, 1 − ξ)` (`0 < η ≤ 1/2` for `0 < ξ < 1`). -/
theorem dipole_condition228_restriction {o x : V} (ξ : ℝ) (S : Finset V)
    (h1 : ∃ j ∈ S, dipoleMark o x j ≠ 0) (h2 : ∃ j ∉ S, dipoleMark o x j ≠ 0) :
    ∃ m : ℤ, (m : ℝ) + dipoleGap ξ ≤ ξ * ((∑ j ∈ S, dipoleMark o x j : ℤ) : ℝ) ∧
      ξ * ((∑ j ∈ S, dipoleMark o x j : ℤ) : ℝ) ≤ (m : ℝ) + 1 - dipoleGap ξ :=
  (dipole_isGapped_restriction ξ S h1 h2).exists_mem_Icc

end Dipole

end FroehlichSpencer.BKT.Generic.Marked
