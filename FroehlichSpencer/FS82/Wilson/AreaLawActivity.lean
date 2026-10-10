/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.DualityFinite
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Small-β one-plaquette activity

The nonzero integer Gaussian modes are bounded by the corresponding geometric
series. This is the single-site estimate used by the finite polymer bound.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- Sum of the nonzero integer Fourier activities at coupling `β`. -/
@[expose] noncomputable def nonzeroGaussianActivity (β : ℝ) : ℝ :=
  ∑' z : ℤ, if z = 0 then 0 else Real.exp (-(z : ℝ) ^ 2 / (2 * β))

theorem nonzeroGaussianActivity_le_geometric (β : ℝ) (hβ : 0 < β) :
    nonzeroGaussianActivity β ≤
      2 * Real.exp (-1 / (2 * β)) / (1 - Real.exp (-1 / (2 * β))) := by
  let f : ℤ → ℝ := fun z =>
    if z = 0 then 0 else Real.exp (-(z : ℝ) ^ 2 / (2 * β))
  let a : ℝ := 1 / (2 * β)
  let q : ℝ := Real.exp (-a)
  have hcoeff : Summable fun z : ℤ => Real.exp (-(z : ℝ) ^ 2 / (2 * β)) :=
    villainCharacterCoeff_summable β hβ
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
      (fun z => by
        dsimp [f]
        split_ifs <;> positivity)
      (fun z => by
        dsimp [f]
        split_ifs with hz
        · exact (Real.exp_pos _).le
        · exact le_rfl)
      hcoeff
  have hfEven : Function.Even f := by
    intro z
    dsimp [f]
    by_cases hz : z = 0
    · simp [hz]
    · have hnz : -z ≠ 0 := by simpa using hz
      simp [hz, hnz]
  have ha : 0 < a := by dsimp [a]; positivity
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [ha])
  have hgeom : Summable fun n : ℕ => q ^ n :=
    summable_geometric_of_lt_one hq0.le hq1
  have hgeomPos : Summable fun n : ℕ+ => q ^ (n : ℕ) :=
    hgeom.comp_injective (by
      intro n m h
      exact Subtype.ext h)
  have hpoint (n : ℕ+) :
      Real.exp (-((n : ℝ) ^ 2) / (2 * β)) ≤ q ^ (n : ℕ) := by
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
    have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hexpArg : -((n : ℝ) ^ 2) / (2 * β) = -a * (n : ℝ) ^ 2 := by
      dsimp [a]
      field_simp
    have hmul : -a * (n : ℝ) ^ 2 ≤ -a * (n : ℝ) := by
      nlinarith [mul_nonneg ha.le (sq_nonneg ((n : ℝ) - 1))]
    calc
      Real.exp (-((n : ℝ) ^ 2) / (2 * β)) = Real.exp (-a * (n : ℝ) ^ 2) := by
        rw [hexpArg]
      _ ≤ Real.exp (-a * (n : ℝ)) := Real.exp_le_exp.mpr hmul
      _ = q ^ (n : ℕ) := by
        dsimp [q]
        rw [show -a * (n : ℝ) = (n : ℝ) * (-a) by ring]
        exact Real.exp_nat_mul (-a) n
  have hgaussPos : Summable fun n : ℕ+ =>
      Real.exp (-((n : ℝ) ^ 2) / (2 * β)) := by
    apply Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hpoint hgeomPos
  have hcomp := hgaussPos.tsum_le_tsum hpoint hgeomPos
  have hpnat : (∑' n : ℕ+, q ^ (n : ℕ)) = q / (1 - q) := by
    rw [tsum_pnat_eq_tsum_succ]
    calc
      (∑' k : ℕ, q ^ (k + 1)) = (∑' k : ℕ, q ^ k) * q := by
        rw [show (fun k : ℕ => q ^ (k + 1)) = fun k => q ^ k * q by
          funext k
          rw [pow_succ]]
        exact hgeom.tsum_mul_right q
      _ = q / (1 - q) := by
        rw [tsum_geometric_of_lt_one hq0.le hq1]
        rw [div_eq_mul_inv]
        ring
  have hsplit : nonzeroGaussianActivity β =
      2 * (∑' n : ℕ+, Real.exp (-((n : ℝ) ^ 2) / (2 * β))) := by
    unfold nonzeroGaussianActivity
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hfEven hf]
    simp [f, nsmul_eq_mul]
  rw [hsplit]
  calc
    2 * (∑' n : ℕ+, Real.exp (-((n : ℝ) ^ 2) / (2 * β))) ≤
        2 * (∑' n : ℕ+, q ^ (n : ℕ)) :=
      mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ = 2 * (q / (1 - q)) := by rw [hpnat]
    _ = 2 * Real.exp (-1 / (2 * β)) /
        (1 - Real.exp (-1 / (2 * β))) := by
      have hq : q = Real.exp (-1 / (2 * β)) := by
        dsimp [q, a]
        ring_nf
      rw [hq]
      ring

theorem smallBeta_residualActivity_bound (β : ℝ) (hβ : 0 < β)
    (hsmall : β ≤ 1 / 80) :
    400 * nonzeroGaussianActivity (4 * β / 3) ≤ Real.exp (-7) := by
  have hβr : 0 < 4 * β / 3 := by positivity
  have hβrUpper : 4 * β / 3 ≤ 1 / 60 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    nlinarith
  have haLower : (30 : ℝ) ≤ 1 / (2 * (4 * β / 3)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (4 * β / 3))).2
    nlinarith [hβrUpper]
  have hq : Real.exp (-1 / (2 * (4 * β / 3))) ≤ 1 / (2 : ℝ) ^ 30 := by
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have he30 : (2 : ℝ) ^ 30 ≤ Real.exp 30 := by
      calc
        (2 : ℝ) ^ 30 ≤ (Real.exp 1) ^ 30 := by
          exact pow_le_pow_left₀ (by norm_num) he2 30
        _ = Real.exp 30 := by
          rw [← Real.exp_nat_mul]
          norm_num
    calc
      Real.exp (-1 / (2 * (4 * β / 3))) ≤ Real.exp (-30) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg (by
          have := haLower
          linarith)
      _ = 1 / Real.exp 30 := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / (2 : ℝ) ^ 30 := by
        exact one_div_le_one_div_of_le (by positivity) he30
  have hqhalf : Real.exp (-1 / (2 * (4 * β / 3))) ≤ 1 / 2 := by
    calc
      _ ≤ 1 / (2 : ℝ) ^ 30 := hq
      _ ≤ 1 / 2 := by norm_num
  have hactivity := nonzeroGaussianActivity_le_geometric (4 * β / 3) hβr
  have hactivity4 : nonzeroGaussianActivity (4 * β / 3) ≤
      4 * Real.exp (-1 / (2 * (4 * β / 3))) := by
    have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-1 / (2 * (4 * β / 3))) := by
      linarith
    calc
      nonzeroGaussianActivity (4 * β / 3) ≤
          2 * Real.exp (-1 / (2 * (4 * β / 3))) /
            (1 - Real.exp (-1 / (2 * (4 * β / 3)))) := hactivity
      _ ≤ 4 * Real.exp (-1 / (2 * (4 * β / 3))) := by
        rw [div_le_iff₀ (by linarith :
          0 < 1 - Real.exp (-1 / (2 * (4 * β / 3))))]
        nlinarith [Real.exp_pos (-1 / (2 * (4 * β / 3)))]
  have hrough : 400 * nonzeroGaussianActivity (4 * β / 3) ≤
      1600 / (2 : ℝ) ^ 30 := by
    have hscaled : 400 * nonzeroGaussianActivity (4 * β / 3) ≤
        1600 * Real.exp (-1 / (2 * (4 * β / 3))) := by
      calc
        400 * nonzeroGaussianActivity (4 * β / 3) ≤
            400 * (4 * Real.exp (-1 / (2 * (4 * β / 3)))) :=
          mul_le_mul_of_nonneg_left hactivity4 (by norm_num : (0 : ℝ) ≤ 400)
        _ = 1600 * Real.exp (-1 / (2 * (4 * β / 3))) := by ring
    calc
      400 * nonzeroGaussianActivity (4 * β / 3) ≤
          1600 * Real.exp (-1 / (2 * (4 * β / 3))) := hscaled
      _ ≤ 1600 / (2 : ℝ) ^ 30 := by
        have hmul := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 1600)
        simpa [div_eq_mul_inv] using hmul
  have hnum : 1600 / (2 : ℝ) ^ 30 ≤ 1 / 2187 := by norm_num
  have hexp7 : Real.exp 7 < 2187 := by
    calc
      Real.exp 7 = Real.exp 1 ^ 7 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < (3 : ℝ) ^ 7 := by
        gcongr
        exact Real.exp_one_lt_three
      _ = 2187 := by norm_num
  have hexpNeg7 : 1 / 2187 ≤ Real.exp (-7) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) hexp7.le
  exact hrough.trans (hnum.trans hexpNeg7)

theorem integer_abs_le_real_sq (z : ℤ) :
    |(z : ℝ)| ≤ (z : ℝ) ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hnatNe : z.natAbs ≠ 0 := by
    intro hzero
    exact hz (Int.natAbs_eq_zero.mp hzero)
  have hnat : 1 ≤ z.natAbs := by omega
  have hnatInt : (1 : ℤ) ≤ (z.natAbs : ℤ) := by exact_mod_cast hnat
  have habsInt : (1 : ℤ) ≤ |z| := by
    simpa only [Int.natCast_natAbs] using hnatInt
  have habs : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast habsInt
  have hnonneg : 0 ≤ |(z : ℝ)| := abs_nonneg _
  nlinarith [sq_abs (z : ℝ), mul_nonneg (sub_nonneg.mpr habs) hnonneg]

private theorem finset_prod_exp_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∏ x ∈ s, Real.exp (f x)) = Real.exp (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← Real.exp_add]

theorem dualGaussianProduct_le_residual_of_l1 {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (m : PrimalPlaquettes B → ℤ) :
    dualGaussianProduct β m ≤
      Real.exp (-((∑ p : PrimalPlaquettes B, |(m p : ℝ)|) / (8 * β))) *
        dualGaussianProduct (4 * β / 3) m := by
  classical
  unfold dualGaussianProduct
  calc
    (∏ p : PrimalPlaquettes B,
        Real.exp (-((m p : ℝ) ^ 2) / (2 * β))) ≤
        ∏ p : PrimalPlaquettes B,
          (Real.exp (-|(m p : ℝ)| / (8 * β)) *
            Real.exp (-((m p : ℝ) ^ 2) / (2 * (4 * β / 3)))) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hsq := integer_abs_le_real_sq (m p)
        have hβpos : 0 < β := hβ
        have hβr : 0 < 4 * β / 3 := by positivity
        field_simp
        nlinarith [hsq]
    _ = (∏ p : PrimalPlaquettes B, Real.exp (-|(m p : ℝ)| / (8 * β))) *
        (∏ p : PrimalPlaquettes B,
          Real.exp (-((m p : ℝ) ^ 2) / (2 * (4 * β / 3)))) := by
      rw [Finset.prod_mul_distrib]
    _ = Real.exp (-((∑ p : PrimalPlaquettes B, |(m p : ℝ)|) / (8 * β))) *
        dualGaussianProduct (4 * β / 3) m := by
      rw [finset_prod_exp_sum]
      congr 1
      congr 1
      calc
        (∑ p : PrimalPlaquettes B, -|(m p : ℝ)| / (8 * β)) =
            ∑ p : PrimalPlaquettes B, (-|(m p : ℝ)|) * (8 * β)⁻¹ := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [div_eq_mul_inv]
        _ = (∑ p : PrimalPlaquettes B, -|(m p : ℝ)|) * (8 * β)⁻¹ := by
              rw [Finset.sum_mul]
        _ = -((∑ p : PrimalPlaquettes B, |(m p : ℝ)|) / (8 * β)) := by
              rw [Finset.sum_neg_distrib, div_eq_mul_inv]
              ring

end FroehlichSpencer.FS82.Wilson

end
