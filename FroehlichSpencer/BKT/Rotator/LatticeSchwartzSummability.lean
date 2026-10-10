/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Lattice sample summability for finite-dimensional Schwartz functions -/

@[expose] public section

open scoped SchwartzMap
open scoped BigOperators

namespace FroehlichSpencer.BKT.Rotator

noncomputable def latticePhi (z : ℤ) : ℝ := 1 / (1 + |(z : ℝ)|) ^ 2

lemma latticePhi_nonneg (z : ℤ) : 0 ≤ latticePhi z := by unfold latticePhi; positivity

lemma summable_latticePhi : Summable latticePhi := by
  have hbase : Summable (fun z : ℤ => 1 / (z : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  apply Summable.of_norm_bounded_eventually hbase
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with z hz
  have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz
  dsimp [latticePhi]
  rw [abs_of_nonneg (by positivity)]
  have habs : |(z : ℝ)| = |(z : ℤ)| := by norm_cast
  rw [habs]
  have hzabs : 1 ≤ |(z : ℝ)| := by
    have hnat : 0 < z.natAbs := Int.natAbs_pos.mpr hz
    have hnat1 : 1 ≤ z.natAbs := Nat.succ_le_iff.mpr hnat
    have h : (1 : ℤ) ≤ |z| := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hnat1
    exact_mod_cast h
  have hden : |(z : ℝ)| ≤ 1 + |(z : ℝ)| := by linarith
  have : (1 + |(z : ℝ)|) ^ 2 ≥ |(z : ℝ)| ^ 2 := by nlinarith [abs_nonneg (z : ℝ)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa [sq_abs] using this

lemma prod_mono_nonneg_real {α : Type*} (s : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i) :
    ∏ i ∈ s, a i ≤ ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have haTail : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have habTail : ∀ j ∈ s, a j ≤ b j := fun j hj => hab j (Finset.mem_insert_of_mem hj)
      have htailA : 0 ≤ ∏ j ∈ s, a j := Finset.prod_nonneg fun j hj => haTail j hj
      have hbi : 0 ≤ b i := (ha i (Finset.mem_insert_self _ _)).trans
        (hab i (Finset.mem_insert_self _ _))
      exact mul_le_mul (hab i (Finset.mem_insert_self _ _)) (ih haTail habTail) htailA hbi

lemma summable_fin_prod_phi : ∀ n : ℕ, Summable (fun q : Fin n → ℤ => ∏ i : Fin n, latticePhi (q i)) := by
  intro n
  induction n with
  | zero =>
      apply summable_of_hasFiniteSupport
      exact Set.toFinite _
  | succ n ih =>
      let e := Fin.succFunEquiv ℤ n
      have hpair : Summable (fun p : (Fin n → ℤ) × ℤ =>
          (∏ i : Fin n, latticePhi (p.1 i)) * latticePhi p.2) := by
        have hnonneg : ∀ p : (Fin n → ℤ) × ℤ,
            0 ≤ (∏ i : Fin n, latticePhi (p.1 i)) * latticePhi p.2 := by
          intro p
          exact mul_nonneg (Finset.prod_nonneg fun i hi => latticePhi_nonneg _) (latticePhi_nonneg _)
        apply (summable_prod_of_nonneg hnonneg).2
        constructor
        · intro a
          exact summable_latticePhi.mul_left (∏ i : Fin n, latticePhi (a i))
        · have hOuter : Summable (fun a : Fin n → ℤ =>
              (∏ i : Fin n, latticePhi (a i)) * (∑' z : ℤ, latticePhi z)) :=
              ih.mul_right (∑' z : ℤ, latticePhi z)
          refine hOuter.congr ?_
          intro a
          rw [← tsum_mul_left]
      have hident (p : (Fin n → ℤ) × ℤ) :
          (∏ i : Fin (n + 1), latticePhi (e.symm p i)) =
            (∏ i : Fin n, latticePhi (p.1 i)) * latticePhi p.2 := by
        rw [Fin.prod_univ_castSucc]
        dsimp [e]
        have hleft (i : Fin n) : Fin.append p.1 (uniqueElim p.2) i.castSucc = p.1 i := by
          have hi : i.castSucc = Fin.castAdd 1 i := rfl
          rw [hi, Fin.append_left]
        have hright : Fin.append p.1 (uniqueElim p.2) (Fin.last n) = p.2 := by
          have hi : Fin.last n = Fin.natAdd n (0 : Fin 1) := rfl
          rw [hi, Fin.append_right]
          rfl
        simp only [Fin.succFunEquiv_symm_apply]
        simp_rw [hleft, hright]
      have hOld : Summable (fun p : (Fin n → ℤ) × ℤ =>
          ∏ i : Fin (n + 1), latticePhi (e.symm p i)) := hpair.congr fun p => (hident p).symm
      exact (e.symm.summable_iff).mp hOld

lemma summable_pi_prod_phi {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Summable (fun q : ι → ℤ => ∏ i : ι, latticePhi (q i)) := by
  classical
  let e := Fintype.equivFin ι
  let ep := Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℤ) e
  have hFin : Summable (fun q : Fin (Fintype.card ι) → ℤ =>
      ∏ i : Fin (Fintype.card ι), latticePhi (q i)) := summable_fin_prod_phi _
  have hReindex : Summable (fun q : Fin (Fintype.card ι) → ℤ =>
      ∏ i : ι, latticePhi ((ep.symm q) i)) := by
    apply hFin.congr
    intro q
    change (∏ j : Fin (Fintype.card ι), latticePhi (q j)) =
      ∏ i : ι, latticePhi (q (e i))
    exact (Equiv.prod_comp e (fun i => latticePhi (q i))).symm
  exact (ep.symm.summable_iff).mp hReindex

lemma schwartz_pi_lattice_samples_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ι → ℝ, ℂ)) :
    Summable (fun q : ι → ℤ => f (fun i => (q i : ℝ))) := by
  classical
  let N : ℕ := 2 * Fintype.card ι
  obtain ⟨C0, h0⟩ := f.decay' 0 0
  obtain ⟨C, hN⟩ := f.decay' N 0
  have h0fun (x : ι → ℝ) : ‖f x‖ ≤ C0 := by
    have h := h0 x
    change ‖f.toFun x‖ ≤ C0
    simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul] using h
  have hNfun (x : ι → ℝ) : ‖x‖ ^ N * ‖f x‖ ≤ C := by
    have h := hN x
    change ‖x‖ ^ N * ‖f.toFun x‖ ≤ C
    simpa only [norm_iteratedFDeriv_zero] using h
  have hC0 : 0 ≤ C0 := (norm_nonneg (f 0)).trans (h0fun 0)
  have hC : 0 ≤ C := by
    by_cases hNzero : N = 0
    · have h := hNfun 0
      exact (norm_nonneg (f 0)).trans (by simpa [hNzero] using h)
    · have h := hNfun 0
      simpa [hNzero] using h
  let D : ℝ := max C0 (C * 2 ^ N)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmajor (q : ι → ℤ) :
      ‖f (fun i => (q i : ℝ))‖ ≤ D * ∏ i : ι, latticePhi (q i) := by
    let x : ι → ℝ := fun i => (q i : ℝ)
    by_cases hq : q = 0
    · subst q
      have hD0 : C0 ≤ D := le_max_left _ _
      simp only [Pi.zero_apply, Int.cast_zero]
      change ‖f (fun _ : ι => (0 : ℝ))‖ ≤ D * ∏ i : ι, latticePhi 0
      calc
        ‖f (fun _ : ι => (0 : ℝ))‖ ≤ C0 := h0fun 0
        _ ≤ D := hD0
        _ = D * ∏ i : ι, latticePhi 0 := by simp [latticePhi]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
      have hnat : 0 < (q i).natAbs := Int.natAbs_pos.mpr hi
      have hnat1 : 1 ≤ (q i).natAbs := Nat.succ_le_iff.mpr hnat
      have hInt : (1 : ℤ) ≤ |q i| := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hnat1
      have hreal : 1 ≤ |(q i : ℝ)| := by exact_mod_cast hInt
      have hcoord : |(q i : ℝ)| ≤ ‖x‖ := by
        rw [← Real.norm_eq_abs]
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp le_rfl i
      have hu : 1 ≤ ‖x‖ := hreal.trans hcoord
      have hu0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hu
      have hpowpos : 0 < ‖x‖ ^ N := pow_pos hu0 N
      have hnorm : ‖f x‖ ≤ C / ‖x‖ ^ N := by
        apply (le_div_iff₀ hpowpos).2
        simpa [mul_comm] using hNfun x
      let P : ℝ := ∏ i : ι, (1 + |(q i : ℝ)|) ^ 2
      have hPpos : 0 < P := by
        dsimp [P]
        exact Finset.prod_pos fun j hj => by positivity
      have hPbound : P ≤ 2 ^ N * ‖x‖ ^ N := by
        have hP1 : P ≤ (1 + ‖x‖) ^ N := by
          dsimp [P, N]
          calc
            ∏ i : ι, (1 + |(q i : ℝ)|) ^ 2 ≤
                ∏ i : ι, (1 + ‖x‖) ^ 2 := by
                  apply prod_mono_nonneg_real
                  · intro j hj
                    positivity
                  · intro j hj
                    have hjcoord : |(q j : ℝ)| ≤ ‖x‖ := by
                      rw [← Real.norm_eq_abs]
                      exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp le_rfl j
                    gcongr
            _ = (1 + ‖x‖) ^ (2 * Fintype.card ι) := by simp [Finset.prod_const, pow_mul]
        have h1 : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
        calc
          P ≤ (1 + ‖x‖) ^ N := hP1
          _ ≤ (2 * ‖x‖) ^ N := by gcongr
          _ = 2 ^ N * ‖x‖ ^ N := by rw [mul_pow]
      have hmul : ‖f x‖ * P ≤ C * 2 ^ N := by
        calc
          ‖f x‖ * P ≤ ‖f x‖ * (2 ^ N * ‖x‖ ^ N) :=
            mul_le_mul_of_nonneg_left hPbound (norm_nonneg _)
          _ = 2 ^ N * (‖x‖ ^ N * ‖f x‖) := by ring
          _ ≤ 2 ^ N * C := mul_le_mul_of_nonneg_left (hNfun x) (by positivity)
          _ = C * 2 ^ N := by ring
      have hquot : ‖f x‖ ≤ (C * 2 ^ N) / P := by
        apply (le_div_iff₀ hPpos).2
        simpa [mul_comm] using hmul
      have hphi : (∏ i : ι, latticePhi (q i)) = P⁻¹ := by
        dsimp [latticePhi, P]
        rw [← Finset.prod_inv_distrib]
        congr 1
        funext j
        ring
      have hquot' : ‖f x‖ ≤ (C * 2 ^ N) * ∏ i : ι, latticePhi (q i) := by
        rw [hphi]
        simpa [div_eq_mul_inv] using hquot
      exact hquot'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.prod_nonneg fun j hj => latticePhi_nonneg _))
  have hg : Summable (fun q : ι → ℤ => D * ∏ i : ι, latticePhi (q i)) :=
    (summable_pi_prod_phi (ι := ι)).mul_left D
  exact Summable.of_norm_bounded hg hmajor

end FroehlichSpencer.BKT.Rotator
