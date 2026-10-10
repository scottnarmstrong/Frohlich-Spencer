/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.OffsetP8
public import FroehlichSpencer.BKT.Rotator.Periodic.Comb

/-!
# Geometric mixtures for the periodic Dirichlet comb

The finite Dirichlet comb has a positive geometric mixture at every frequency. Its entropy leaf
bound is uniform in the cutoff, as required by the periodic shift estimate.
-/

@[expose] public section

open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Rotator.Periodic
open FroehlichSpencer.BKT.Rotator.TheoremC (dirichletComb)

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ}

/-- The cutoff frequency at each periodic site. -/
def periodicCombNq (N : ℕ) : Fin L × Fin L → ℕ := fun _ => N

/-- The Fourier coefficient of the Dirichlet comb. -/
def periodicCombLamHat (N : ℕ) : Fin L × Fin L → ℕ → ℝ := fun _ q => if q ≤ N then 1 else 0

/-- The truncated geometric distribution on the positive frequencies. -/
def periodicCombZeta (N : ℕ) : ∀ _j : Fin L × Fin L, SiteMode N → ℝ := fun _ q =>
  (1 / 2 : ℝ) ^ q.1 / ∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1

private theorem periodicCombZeta_den_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < ∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1 := by
  have hsum : (∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1) =
      ∑ r ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ r := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach _ _
  rw [hsum]
  apply Finset.sum_pos
  · intro r hr
    positivity
  · exact ⟨1, by simp [Finset.mem_Icc]; omega⟩

private theorem periodicCombZeta_den_le_one {N : ℕ} :
    ∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1 ≤ 1 := by
  have hsum : ∀ N : ℕ, (∑ r ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ r) =
      1 - (1 / 2 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, pow_succ]
      norm_num
      ring
  have hattach : (∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1) =
      ∑ r ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ r := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach _ _
  rw [hattach, hsum]
  have : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
  linarith

private theorem periodicCombZeta_sum {N : ℕ} (hN : 1 ≤ N) (j : Fin L × Fin L) :
    ∑ q : SiteMode N, periodicCombZeta N j q = 1 := by
  unfold periodicCombZeta
  have hd := periodicCombZeta_den_pos hN
  rw [← Finset.sum_div]
  exact div_self hd.ne'

/-- The Dirichlet comb mixture data meet the periodic shift input uniformly in the cutoff. -/
theorem periodicCombMixtureData (N : ℕ) (hN : 1 ≤ N) :
    (∀ j : Fin L × Fin L, 0 < periodicCombNq (L := L) N j) ∧
    (∀ j : Fin L × Fin L, ∀ q, periodicCombNq N j < q → periodicCombLamHat N j q = 0) ∧
    (∀ j : Fin L × Fin L, ∀ φ, dirichletComb N φ = 1 + 2 *
      ∑ q ∈ Finset.Icc 1 (periodicCombNq N j),
        periodicCombLamHat N j q * Real.cos (q * φ)) ∧
    (∀ j : Fin L × Fin L, ∀ q : SiteMode N, 0 < periodicCombZeta N j q) ∧
    (∀ j : Fin L × Fin L, ∑ q : SiteMode N, periodicCombZeta N j q = 1) ∧
    (∀ j : Fin L × Fin L, ∀ q, mixtureLeaf (L := L) (periodicCombNq N)
      (periodicCombLamHat N) (periodicCombZeta N) j q ≤ Real.exp (Real.log 4 * q)) := by
  have hden := periodicCombZeta_den_pos hN
  have hdenle : (∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1) ≤ 1 :=
    periodicCombZeta_den_le_one (N := N)
  refine ⟨fun _ => hN, ?_, ?_, ?_, periodicCombZeta_sum hN, ?_⟩
  · intro j q hq
    simp [periodicCombNq] at hq
    simp [periodicCombLamHat, hq]
  · intro j φ
    apply congrArg (fun s : ℝ => 1 + 2 * s)
    change (∑ q ∈ Finset.Icc 1 N, Real.cos (q * φ)) =
      ∑ q ∈ Finset.Icc 1 N, periodicCombLamHat N j q * Real.cos (q * φ)
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hqN : q ≤ N := (Finset.mem_Icc.mp hq).2
    simp [periodicCombLamHat, hqN]
  · intro j q
    unfold periodicCombZeta
    exact div_pos (by positivity) hden
  · intro j q
    unfold mixtureLeaf
    change (if h : q ∈ Finset.Icc 1 N then
      2 * |periodicCombLamHat N j q| / periodicCombZeta N j ⟨q, h⟩ else 0) ≤
        Real.exp (Real.log 4 * q)
    by_cases hq : q ∈ Finset.Icc 1 N
    · have hqN : q ≤ N := (Finset.mem_Icc.mp hq).2
      have hcoeff : periodicCombLamHat N j q = 1 := by simp [periodicCombLamHat, hqN]
      have hζ : periodicCombZeta N j ⟨q, hq⟩ =
          (1 / 2 : ℝ) ^ q / ∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1 := rfl
      rw [dite_eq_left hq, hcoeff, hζ, abs_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ))]
      have hpowpos : (1 / 2 : ℝ) ^ q ≠ 0 := by positivity
      have hratio : 2 / ((1 / 2 : ℝ) ^ q /
          ∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1) =
          2 * (∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1) * 2 ^ q := by
        field_simp [hpowpos]
        rw [← mul_pow]
        norm_num
      norm_num only [mul_one]
      rw [hratio]
      have hbound : 2 * (2 : ℝ) ^ q ≤ (4 : ℝ) ^ q := by
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hp : (4 : ℝ) ^ q = 2 ^ (2 * q) := by norm_num [pow_mul]
        rw [hp]
        have hpow : (2 : ℝ) ^ (q + 1) ≤ 2 ^ (2 * q) := by
          apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          omega
        calc
          2 * (2 : ℝ) ^ q = 2 ^ q * 2 := by ring
          _ = 2 ^ (q + 1) := by rw [pow_succ]
          _ ≤ 2 ^ (2 * q) := hpow
      have hexp : Real.exp (Real.log 4 * (q : ℝ)) = (4 : ℝ) ^ q := by
        calc
          Real.exp (Real.log 4 * (q : ℝ)) = Real.exp ((q : ℝ) * Real.log 4) := by
            congr 1
            ring
          _ = Real.exp (Real.log 4) ^ q := Real.exp_nat_mul _ _
          _ = (4 : ℝ) ^ q := by rw [Real.exp_log (by norm_num)]
      calc
        2 * (∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1) * (2 : ℝ) ^ q ≤ 2 * (2 : ℝ) ^ q :=
          mul_le_mul_of_nonneg_right (by
            calc
              2 * (∑ r : SiteMode N, (1 / 2 : ℝ) ^ r.1) ≤ 2 * 1 :=
                mul_le_mul_of_nonneg_left hdenle (by norm_num : (0 : ℝ) ≤ 2)
              _ = 2 := by ring)
            (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ q)
        _ ≤ (4 : ℝ) ^ q := hbound
        _ = Real.exp (Real.log 4 * (q : ℝ)) := hexp.symm
    · rw [dite_eq_right hq]
      positivity

end FroehlichSpencer.BKT.Rotator.Periodic

end
