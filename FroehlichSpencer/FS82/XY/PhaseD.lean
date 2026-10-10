/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.ExtentD
public import FroehlichSpencer.FS82.Wilson.CubeLoopField
public import FroehlichSpencer.FS82.Currents.Current

/-!
# phase representatives of filled co-closed currents, in every dimension

Let `C` be an exact-one complex, `φ` an integer-valued form of top degree, `ε` its residual
`loopFieldResidual C φ` (the projection of `φ` orthogonal to the exact forms), and `τ` any
potential with `d₁ τ = φ − ε`.

For an integer current `J` with an integer filling `F`,
`d₁† F = J`,

`2π ⟨J, τ⟩ + 2π ⟨ε, F⟩ = 2π ⟨φ, F⟩ ∈ 2π ℤ`.

So `−2π ⟨ε, F⟩` represents the phase `2π ⟨J, τ⟩` modulo `2π`: FS82 (4.34)–(4.35).

For the dual
complex of a box of dimension `d ≥ 3` and a co-closed current of `L` cells and extent `L − 1`,
with `L` smaller than every side, the local relative filling of `XY/ExtentD.lean` gives such an
`F` with mass at most `4 ^ d · ‖J‖² · L ^ d`, supported within distance `2L` of a cell `p₀` where
`|ε|` is maximal on the support of `F`.

* `phase_representative_of_filling`: the identity above, for any exact-one complex.
* `currentEnergy`, `currentLength`: the squared norm and the number of cells of a current.
* `short_filling`: the filling data of a short co-closed current.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Wilson

/-! ## The phase identity in an exact-one complex -/

section Abstract

variable {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

/-- **The phase representative of a filled current.** -/
theorem phase_representative_of_filling (C : ExactOneComplex V E P)
    (φ : EuclideanSpace ℝ P) (hφ : ∀ p, ∃ m : ℤ, φ p = (m : ℝ))
    (τ : EuclideanSpace ℝ E) (hτ : C.d₁ τ = φ - loopFieldResidual C φ)
    (J : E → ℤ) (F : P → ℤ)
    (hF : C.d₁.adjoint (WithLp.toLp 2 fun p => ((F p : ℤ) : ℝ)) = currentVector J) :
    ∃ n : ℤ, 2 * Real.pi * inner ℝ (currentVector J) τ +
        2 * Real.pi * ∑ p, loopFieldResidual C φ p * ((F p : ℤ) : ℝ) =
      2 * Real.pi * (n : ℝ) := by
  choose m hm using hφ
  refine ⟨∑ p, m p * F p, ?_⟩
  rw [← hF, LinearMap.adjoint_inner_left, hτ, PiLp.inner_apply]
  have hterm : ∀ p : P,
      inner ℝ ((WithLp.toLp 2 fun p => ((F p : ℤ) : ℝ) : EuclideanSpace ℝ P) p)
        ((φ - loopFieldResidual C φ) p) =
      ((m p * F p : ℤ) : ℝ) - loopFieldResidual C φ p * ((F p : ℤ) : ℝ) := by
    intro p
    rw [PiLp.sub_apply, hm p]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Int.cast_sum]
  ring

/-- The squared norm of an integer current. -/
noncomputable def currentEnergy (J : E → ℤ) : ℝ := ∑ e, ((J e : ℤ) : ℝ) ^ 2

/-- The number of cells of an integer current. -/
def currentLength (J : E → ℤ) : ℕ := (currentSupport J).card

omit [DecidableEq E] in
theorem currentEnergy_nonneg (J : E → ℤ) : 0 ≤ currentEnergy J :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem mem_currentSupport_iff {J : E → ℤ} {e : E} : e ∈ currentSupport J ↔ J e ≠ 0 := by
  simp [currentSupport]

theorem currentLength_pos_of_ne_zero {J : E → ℤ} {e : E} (he : J e ≠ 0) : 1 ≤ currentLength J :=
  Finset.card_pos.mpr ⟨e, mem_currentSupport_iff.mpr he⟩

theorem exists_ne_zero_of_currentLength_pos {J : E → ℤ} (h : 1 ≤ currentLength J) :
    ∃ e, J e ≠ 0 := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  exact ⟨e, mem_currentSupport_iff.mp he⟩

omit [DecidableEq E] in
/-- The `ℓ¹` norm of an integer current is at most its squared norm. -/
theorem sum_natAbs_le_currentEnergy (J : E → ℤ) :
    ((∑ e : E, (J e).natAbs : ℕ) : ℝ) ≤ currentEnergy J := by
  unfold currentEnergy
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have habs : (((J e).natAbs : ℕ) : ℝ) = |((J e : ℤ) : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [habs, ← sq_abs]
  by_cases h0 : J e = 0
  · simp [h0]
  · have h1 : (1 : ℝ) ≤ |((J e : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |J e| := Int.one_le_abs h0
      exact_mod_cast this
    nlinarith

/-- The number of cells of an integer current is at most its squared norm. -/
theorem currentLength_le_currentEnergy (J : E → ℤ) :
    (currentLength J : ℝ) ≤ currentEnergy J := by
  unfold currentLength currentEnergy
  have hsub : ∑ e ∈ currentSupport J, ((J e : ℤ) : ℝ) ^ 2 ≤ ∑ e, ((J e : ℤ) : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  refine le_trans ?_ hsub
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun e he => ?_
  have h0 : J e ≠ 0 := mem_currentSupport_iff.mp he
  have h1 : (1 : ℝ) ≤ |((J e : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |J e| := Int.one_le_abs h0
    exact_mod_cast this
  rw [← sq_abs]
  push_cast
  nlinarith

end Abstract

/-! ## The short currents of the dual complex of a box -/

variable {d : ℕ} {B : Box d}

/-- **The filling data of a short co-closed current.** -/
theorem short_filling (hd : 3 ≤ d) (m : ℕ) (hm : ∀ k, m ≤ B k)
    (φ : EuclideanSpace ℝ (DualDForm B (d - 1))) (hφ : ∀ p, ∃ n : ℤ, φ p = (n : ℝ))
    (τ : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (hτ : (dualDExactOneComplex hd B).d₁ τ = φ - loopFieldResidual (dualDExactOneComplex hd B) φ)
    (J : DualDForm B (d - 2) → ℤ)
    (hJ : currentVector J ∈ coClosed (dualDExactOneComplex hd B))
    (hextent : ∀ e f, J e ≠ 0 → J f ≠ 0 → ∀ k,
      cellBase e.1 k + 1 ≤ cellBase f.1 k + currentLength J)
    (hpos : 1 ≤ currentLength J) (hshort : currentLength J < m) :
    ∃ (F : DualDForm B (d - 1) → ℤ) (p₀ : DualDForm B (d - 1)),
      (∃ n : ℤ, 2 * Real.pi * inner ℝ (currentVector J) τ +
        2 * Real.pi * ∑ p, loopFieldResidual (dualDExactOneComplex hd B) φ p * ((F p : ℤ) : ℝ) =
          2 * Real.pi * (n : ℝ)) ∧
      (∑ p, |((F p : ℤ) : ℝ)| ≤ (4 : ℝ) ^ d * currentEnergy J * (currentLength J : ℝ) ^ d) ∧
      (∀ p, F p ≠ 0 → |loopFieldResidual (dualDExactOneComplex hd B) φ p| ≤
        |loopFieldResidual (dualDExactOneComplex hd B) φ p₀|) ∧
      (∀ e : DualDForm B (d - 2), J e ≠ 0 → ∀ k,
        cellBase p₀.1 k ≤ cellBase e.1 k + 2 * currentLength J ∧
        cellBase e.1 k ≤ cellBase p₀.1 k + 2 * currentLength J) := by
  classical
  set L := currentLength J with hLdef
  set ε := loopFieldResidual (dualDExactOneComplex hd B) φ with hε
  obtain ⟨e₀, he₀⟩ := exists_ne_zero_of_currentLength_pos hpos
  have hext : ∀ e f, J e ≠ 0 → J f ≠ 0 → ∀ k, cellBase e.1 k ≤ cellBase f.1 k + (L - 1) := by
    intro e f he hf k
    have h := hextent e f he hf k
    omega
  have hD : ∀ k, L - 1 < B k := fun k => by
    have := hm k
    omega
  obtain ⟨F, hF, hsupp, hbound⟩ := exists_relativeFilling_of_extent hd J hJ e₀ he₀ (L - 1) hext hD
  have hFne : ∃ p, F p ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : (WithLp.toLp 2 fun p => ((F p : ℤ) : ℝ) :
        EuclideanSpace ℝ (DualDForm B (d - 1))) = 0 := by
      ext p
      simp [hall p]
    rw [hzero, map_zero] at hF
    have h0 : currentVector J e₀ = 0 := by rw [← hF]; rfl
    rw [currentVector_apply] at h0
    exact he₀ (Int.cast_eq_zero.mp h0)
  set S : Finset (DualDForm B (d - 1)) := Finset.univ.filter fun p => F p ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨p, hp⟩ := hFne
    exact ⟨p, by simp [hS, hp]⟩
  obtain ⟨p₀, hp₀S, hmax⟩ := Finset.exists_max_image S (fun p => |ε p|) hSne
  have hp₀ : F p₀ ≠ 0 := (Finset.mem_filter.mp hp₀S).2
  refine ⟨F, p₀, phase_representative_of_filling _ φ hφ τ hτ J F hF, ?_, ?_, ?_⟩
  · have hcardS : S.card ≤ 2 ^ d * ((L - 1) + ((L - 1) + 1) + 1) ^ d := by
      refine (Finset.card_le_card ?_).trans
        (card_window_le (fun p : DualDForm B (d - 1) => p.1) Subtype.val_injective
          (fun k => cellBase e₀.1 k) (L - 1) ((L - 1) + 1))
      intro p hp
      have hpF : F p ≠ 0 := (Finset.mem_filter.mp hp).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsupp p hpF
    have hcard' : (S.card : ℝ) ≤ (4 : ℝ) ^ d * (L : ℝ) ^ d := by
      have h2 : (L - 1) + ((L - 1) + 1) + 1 = 2 * L := by omega
      rw [h2] at hcardS
      have : (S.card : ℝ) ≤ ((2 ^ d * (2 * L) ^ d : ℕ) : ℝ) := by exact_mod_cast hcardS
      refine this.trans (le_of_eq ?_)
      push_cast
      rw [mul_pow, ← mul_assoc, ← mul_pow]
      norm_num
    have hnorm := sum_natAbs_le_currentEnergy J
    have hE0 := currentEnergy_nonneg J
    have hterm : ∀ p ∈ S, |((F p : ℤ) : ℝ)| ≤ currentEnergy J := by
      intro p _
      have h1 : |((F p : ℤ) : ℝ)| = (((F p).natAbs : ℕ) : ℝ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [h1]
      exact (by exact_mod_cast hbound p : (((F p).natAbs : ℕ) : ℝ) ≤
        ((∑ e : DualDForm B (d - 2), (J e).natAbs : ℕ) : ℝ)).trans hnorm
    calc ∑ p, |((F p : ℤ) : ℝ)| = ∑ p ∈ S, |((F p : ℤ) : ℝ)| := by
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
          have h0 : F p = 0 := by
            by_contra hne
            exact hp (by simp [hS, hne])
          simp [h0]
      _ ≤ ∑ _p ∈ S, currentEnergy J := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * currentEnergy J := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ d * (L : ℝ) ^ d * currentEnergy J := mul_le_mul_of_nonneg_right hcard' hE0
      _ = (4 : ℝ) ^ d * currentEnergy J * (L : ℝ) ^ d := by ring
  · intro p hp
    exact hmax p (by simp [hS, hp])
  · intro e he k
    have h1 := hsupp p₀ hp₀ k
    have h2 := hext e e₀ he he₀ k
    have h3 := hext e₀ e he₀ he k
    omega

end FroehlichSpencer.FS82.XY.DualD

end
