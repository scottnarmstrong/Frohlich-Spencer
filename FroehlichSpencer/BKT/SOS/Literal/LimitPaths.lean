/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitClosure

/-!
# Unit flows along straight paths (the comb-inserted SOS construction)

For sites `u, v` of the box, `exists_flow` gives a flow `θ` with `Σ_e θ_e ∇φ(e) = φ(u) − φ(v)`
for every field, `|θ_e| ≤ 1`, supported on at most `2‖u − v‖_∞` bonds. It is the unit flow along
the path that goes horizontally from `u` to the column of `v`, then vertically to `v`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-- The horizontal bond from `(x, j)` to `(x+1, j)`. -/
def hBond (j : Fin L) (x : ℕ) (hx : x + 1 < L) : SquareZeroBond L :=
  .inl ⟨((⟨x, by omega⟩, j), (⟨x + 1, hx⟩, j)),
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp [Fin.lt_def])), by
      have h1 : |((x : ℕ) : ℤ) - ((x + 1 : ℕ) : ℤ)| = 1 := by push_cast; simp
      simp only [h1, sub_self, abs_zero]
      exact Finset.pair_comm 1 0⟩

/-- The vertical bond from `(i, y)` to `(i, y+1)`. -/
def vBond (i : Fin L) (y : ℕ) (hy : y + 1 < L) : SquareZeroBond L :=
  .inl ⟨((i, ⟨y, by omega⟩), (i, ⟨y + 1, hy⟩)),
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by simp [Fin.lt_def]⟩), by
      have h1 : |((y : ℕ) : ℤ) - ((y + 1 : ℕ) : ℤ)| = 1 := by push_cast; simp
      simp only [h1, sub_self, abs_zero]⟩

theorem pinnedGrad_hBond (φ : Site L → ℝ) (j : Fin L) (x : ℕ) (hx : x + 1 < L) :
    pinnedGrad L φ (hBond j x hx) = φ (⟨x, by omega⟩, j) - φ (⟨x + 1, hx⟩, j) := rfl

theorem pinnedGrad_vBond (φ : Site L → ℝ) (i : Fin L) (y : ℕ) (hy : y + 1 < L) :
    pinnedGrad L φ (vBond i y hy) = φ (i, ⟨y, by omega⟩) - φ (i, ⟨y + 1, hy⟩) := rfl

/-- A bond of the free square in row `j`. -/
def IsRowBond (j : Fin L) (e : SquareZeroBond L) : Prop :=
  ∃ e' : SquareFreeEdge L, e = .inl e' ∧ e'.val.1.2 = j ∧ e'.val.2.2 = j

/-- A bond of the free square in column `i`. -/
def IsColBond (i : Fin L) (e : SquareZeroBond L) : Prop :=
  ∃ e' : SquareFreeEdge L, e = .inl e' ∧ e'.val.1.1 = i ∧ e'.val.2.1 = i

theorem not_isRowBond_and_isColBond {i j : Fin L} {e : SquareZeroBond L}
    (hr : IsRowBond j e) (hc : IsColBond i e) : False := by
  obtain ⟨e₁, rfl, h1, h2⟩ := hr
  obtain ⟨e₂, he, h3, h4⟩ := hc
  have he' : e₁ = e₂ := Sum.inl_injective he
  subst he'
  have heq : e₁.val.1 = e₁.val.2 := Prod.ext (h3.trans h4.symm) (h1.trans h2.symm)
  exact lt_irrefl _ (heq ▸ e₁.2.1)

/-- **The horizontal segment flow** from `(a, j)` to `(a+n, j)`. -/
theorem exists_hSegment (j : Fin L) (a : ℕ) : ∀ (n : ℕ) (h : a + n < L),
    ∃ (P : Finset (SquareZeroBond L)) (θ : SquareZeroBond L → ℝ),
      (∀ e ∉ P, θ e = 0) ∧ (∀ e, θ e = 0 ∨ θ e = 1) ∧
      (∀ φ : Site L → ℝ, ∑ e, θ e * pinnedGrad L φ e =
        φ (⟨a, by omega⟩, j) - φ (⟨a + n, h⟩, j)) ∧ P.card ≤ n ∧
      (∀ e ∈ P, ∃ e' : SquareFreeEdge L, e = .inl e' ∧ e'.val.1.2 = j ∧ e'.val.2.2 = j ∧
        e'.val.1.1.val < a + n) := by
  classical
  intro n
  induction n with
  | zero =>
    intro h
    refine ⟨∅, fun _ => 0, fun _ _ => rfl, fun _ => Or.inl rfl, fun φ => ?_, by simp,
      fun e he => absurd he (Finset.notMem_empty e)⟩
    simp
  | succ n ih =>
    intro h
    obtain ⟨P, θ, hsupp, h01, hdiv, hcard, hinv⟩ := ih (by omega)
    set e₀ := hBond j (a + n) (by omega) with he₀
    have hnot : e₀ ∉ P := by
      intro hmem
      obtain ⟨e', he', -, -, hlt⟩ := hinv e₀ hmem
      have := Sum.inl_injective he'
      rw [← this] at hlt
      exact lt_irrefl _ hlt
    refine ⟨insert e₀ P, fun e => θ e + if e = e₀ then 1 else 0, fun e he => ?_, fun e => ?_,
      fun φ => ?_, ?_, fun e he => ?_⟩
    · have he1 : e ∉ P := fun h' => he (Finset.mem_insert_of_mem h')
      have he2 : e ≠ e₀ := fun h' => he (h' ▸ Finset.mem_insert_self e₀ P)
      simp [hsupp e he1, he2]
    · by_cases he : e = e₀
      · subst he; simp [hsupp _ hnot]
      · simp only [he, ↓reduceIte, add_zero]; exact h01 e
    · simp only [add_mul, Finset.sum_add_distrib, hdiv, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, he₀, pinnedGrad_hBond]
      ring_nf
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · rcases Finset.mem_insert.mp he with rfl | hP
      · exact ⟨_, rfl, rfl, rfl, by simp⟩
      · obtain ⟨e', h1, h2, h3, h4⟩ := hinv e hP
        exact ⟨e', h1, h2, h3, by omega⟩

/-- **The vertical segment flow** from `(i, a)` to `(i, a+n)`. -/
theorem exists_vSegment (i : Fin L) (a : ℕ) : ∀ (n : ℕ) (h : a + n < L),
    ∃ (P : Finset (SquareZeroBond L)) (θ : SquareZeroBond L → ℝ),
      (∀ e ∉ P, θ e = 0) ∧ (∀ e, θ e = 0 ∨ θ e = 1) ∧
      (∀ φ : Site L → ℝ, ∑ e, θ e * pinnedGrad L φ e =
        φ (i, ⟨a, by omega⟩) - φ (i, ⟨a + n, h⟩)) ∧ P.card ≤ n ∧
      (∀ e ∈ P, ∃ e' : SquareFreeEdge L, e = .inl e' ∧ e'.val.1.1 = i ∧ e'.val.2.1 = i ∧
        e'.val.1.2.val < a + n) := by
  classical
  intro n
  induction n with
  | zero =>
    intro h
    refine ⟨∅, fun _ => 0, fun _ _ => rfl, fun _ => Or.inl rfl, fun φ => ?_, by simp,
      fun e he => absurd he (Finset.notMem_empty e)⟩
    simp
  | succ n ih =>
    intro h
    obtain ⟨P, θ, hsupp, h01, hdiv, hcard, hinv⟩ := ih (by omega)
    set e₀ := vBond i (a + n) (by omega) with he₀
    have hnot : e₀ ∉ P := by
      intro hmem
      obtain ⟨e', he', -, -, hlt⟩ := hinv e₀ hmem
      have := Sum.inl_injective he'
      rw [← this] at hlt
      exact lt_irrefl _ hlt
    refine ⟨insert e₀ P, fun e => θ e + if e = e₀ then 1 else 0, fun e he => ?_, fun e => ?_,
      fun φ => ?_, ?_, fun e he => ?_⟩
    · have he1 : e ∉ P := fun h' => he (Finset.mem_insert_of_mem h')
      have he2 : e ≠ e₀ := fun h' => he (h' ▸ Finset.mem_insert_self e₀ P)
      simp [hsupp e he1, he2]
    · by_cases he : e = e₀
      · subst he; simp [hsupp _ hnot]
      · simp only [he, ↓reduceIte, add_zero]; exact h01 e
    · simp only [add_mul, Finset.sum_add_distrib, hdiv, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, he₀, pinnedGrad_vBond]
      ring_nf
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · rcases Finset.mem_insert.mp he with rfl | hP
      · exact ⟨_, rfl, rfl, rfl, by simp⟩
      · obtain ⟨e', h1, h2, h3, h4⟩ := hinv e hP
        exact ⟨e', h1, h2, h3, by omega⟩

/-- A flow `θ` from `u` to `v` supported on `P` with `|θ_e| ≤ 1`. -/
def IsUnitFlow (u v : Site L) (P : Finset (SquareZeroBond L)) (θ : SquareZeroBond L → ℝ) :
    Prop :=
  (∀ e ∉ P, θ e = 0) ∧ (∀ e, |θ e| ≤ 1) ∧
    ∀ φ : Site L → ℝ, ∑ e, θ e * pinnedGrad L φ e = φ u - φ v

theorem isUnitFlow_neg {u v : Site L} {P : Finset (SquareZeroBond L)}
    {θ : SquareZeroBond L → ℝ} (h : IsUnitFlow u v P θ) : IsUnitFlow v u P (-θ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e he => by simp [h1 e he], fun e => by simpa using h2 e, fun φ => ?_⟩
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, h3]
  ring

theorem exists_rowFlow (j x₁ x₂ : Fin L) :
    ∃ (P : Finset (SquareZeroBond L)) (θ : SquareZeroBond L → ℝ),
      IsUnitFlow (x₁, j) (x₂, j) P θ ∧
      P.card ≤ ((x₁.val : ℤ) - x₂.val).natAbs ∧ ∀ e ∈ P, IsRowBond j e := by
  rcases le_total x₁.val x₂.val with h | h
  · obtain ⟨P, θ, hs, h01, hd, hc, hinv⟩ := exists_hSegment j x₁.val (x₂.val - x₁.val) (by omega)
    have e1 : (⟨x₁.val, by omega⟩ : Fin L) = x₁ := rfl
    have e2 : (⟨x₁.val + (x₂.val - x₁.val), by omega⟩ : Fin L) = x₂ := Fin.ext (by simp; omega)
    refine ⟨P, θ, ⟨hs, fun e => ?_, fun φ => ?_⟩, by omega, fun e he => ?_⟩
    · rcases h01 e with h0 | h0 <;> simp [h0]
    · rw [hd φ, e1, e2]
    · obtain ⟨e', h1, h2, h3, -⟩ := hinv e he
      exact ⟨e', h1, h2, h3⟩
  · obtain ⟨P, θ, hs, h01, hd, hc, hinv⟩ := exists_hSegment j x₂.val (x₁.val - x₂.val) (by omega)
    have e1 : (⟨x₂.val, by omega⟩ : Fin L) = x₂ := rfl
    have e2 : (⟨x₂.val + (x₁.val - x₂.val), by omega⟩ : Fin L) = x₁ := Fin.ext (by simp; omega)
    have hflow : IsUnitFlow (x₂, j) (x₁, j) P θ :=
      ⟨hs, fun e => by rcases h01 e with h0 | h0 <;> simp [h0], fun φ => by
        rw [hd φ, e1, e2]⟩
    refine ⟨P, -θ, isUnitFlow_neg hflow, by omega, fun e he => ?_⟩
    obtain ⟨e', h1, h2, h3, -⟩ := hinv e he
    exact ⟨e', h1, h2, h3⟩

theorem exists_colFlow (i y₁ y₂ : Fin L) :
    ∃ (P : Finset (SquareZeroBond L)) (θ : SquareZeroBond L → ℝ),
      IsUnitFlow (i, y₁) (i, y₂) P θ ∧
      P.card ≤ ((y₁.val : ℤ) - y₂.val).natAbs ∧ ∀ e ∈ P, IsColBond i e := by
  rcases le_total y₁.val y₂.val with h | h
  · obtain ⟨P, θ, hs, h01, hd, hc, hinv⟩ := exists_vSegment i y₁.val (y₂.val - y₁.val) (by omega)
    have e1 : (⟨y₁.val, by omega⟩ : Fin L) = y₁ := rfl
    have e2 : (⟨y₁.val + (y₂.val - y₁.val), by omega⟩ : Fin L) = y₂ := Fin.ext (by simp; omega)
    refine ⟨P, θ, ⟨hs, fun e => ?_, fun φ => ?_⟩, by omega, fun e he => ?_⟩
    · rcases h01 e with h0 | h0 <;> simp [h0]
    · rw [hd φ, e1, e2]
    · obtain ⟨e', h1, h2, h3, -⟩ := hinv e he
      exact ⟨e', h1, h2, h3⟩
  · obtain ⟨P, θ, hs, h01, hd, hc, hinv⟩ := exists_vSegment i y₂.val (y₁.val - y₂.val) (by omega)
    have e1 : (⟨y₂.val, by omega⟩ : Fin L) = y₂ := rfl
    have e2 : (⟨y₂.val + (y₁.val - y₂.val), by omega⟩ : Fin L) = y₁ := Fin.ext (by simp; omega)
    have hflow : IsUnitFlow (i, y₂) (i, y₁) P θ :=
      ⟨hs, fun e => by rcases h01 e with h0 | h0 <;> simp [h0], fun φ => by
        rw [hd φ, e1, e2]⟩
    refine ⟨P, -θ, isUnitFlow_neg hflow, by omega, fun e he => ?_⟩
    obtain ⟨e', h1, h2, h3, -⟩ := hinv e he
    exact ⟨e', h1, h2, h3⟩

/-- **The straight-path unit flow** from `u` to `v`, on at most `2‖u − v‖_∞` bonds. -/
theorem exists_flow (u v : Site L) :
    ∃ (P : Finset (SquareZeroBond L)) (θ : SquareZeroBond L → ℝ),
      IsUnitFlow u v P θ ∧ P.card ≤ 2 * linfDist u v := by
  classical
  obtain ⟨P₁, θ₁, ⟨hs₁, hb₁, hd₁⟩, hc₁, hr₁⟩ := exists_rowFlow u.2 u.1 v.1
  obtain ⟨P₂, θ₂, ⟨hs₂, hb₂, hd₂⟩, hc₂, hr₂⟩ := exists_colFlow v.1 u.2 v.2
  have hdisj : ∀ e, e ∈ P₁ → e ∉ P₂ := fun e h1 h2 =>
    not_isRowBond_and_isColBond (hr₁ e h1) (hr₂ e h2)
  refine ⟨P₁ ∪ P₂, θ₁ + θ₂, ⟨fun e he => ?_, fun e => ?_, fun φ => ?_⟩, ?_⟩
  · simp only [Finset.mem_union, not_or] at he
    simp [hs₁ e he.1, hs₂ e he.2]
  · by_cases h1 : e ∈ P₁
    · simp only [Pi.add_apply, hs₂ e (hdisj e h1), add_zero]; exact hb₁ e
    · simp only [Pi.add_apply, hs₁ e h1, zero_add]; exact hb₂ e
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hd₁, hd₂]
    ring
  · refine (Finset.card_union_le _ _).trans ?_
    unfold linfDist
    have h1 := le_max_left (Int.natAbs ((u.1.val : ℤ) - v.1.val))
      (Int.natAbs ((u.2.val : ℤ) - v.2.val))
    have h2 := le_max_right (Int.natAbs ((u.1.val : ℤ) - v.1.val))
      (Int.natAbs ((u.2.val : ℤ) - v.2.val))
    omega

end FroehlichSpencer.BKT.SOS.Literal

end
