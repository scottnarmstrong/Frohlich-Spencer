/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Finite products of one-dimensional Schwartz functions

The product `x ↦ ∏ i, f (x i)` is Schwartz on a finite product of real lines. The proof keeps the
finite Leibniz expansion explicit and uses polynomial decay in every coordinate to control the
product-space Schwartz seminorms.
-/

@[expose] public section

open Filter
open scoped ContDiff SchwartzMap

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

private lemma exists_iteratedDeriv_poly_bound {f : 𝓢(ℝ, ℂ)} (R m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedDeriv m f.toFun t‖ ≤ C / (1 + |t|) ^ R := by
  obtain ⟨C0, hC0⟩ := f.decay' 0 m
  obtain ⟨CR, hCR⟩ := f.decay' R m
  have hC0nonneg : 0 ≤ C0 := by
    have h := hC0 (0 : ℝ)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
    have hh : ‖iteratedDeriv m f.toFun 0‖ ≤ C0 := by simpa using h
    exact (norm_nonneg _).trans hh
  have hCRnonneg : 0 ≤ CR := by
    have h := hCR (1 : ℝ)
    have hn : ‖(1 : ℝ)‖ ^ R = 1 := by simp
    rw [hn, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
    have hh : ‖iteratedDeriv m f.toFun 1‖ ≤ CR := by simpa using h
    exact (norm_nonneg _).trans hh
  refine ⟨2 ^ R * max C0 CR, by positivity, fun t => ?_⟩
  by_cases ht : |t| ≤ 1
  · have hden : (1 + |t|) ^ R ≤ 2 ^ R := by gcongr; linarith
    have hval : ‖iteratedDeriv m f.toFun t‖ ≤ C0 := by
      have h := hC0 t
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
      change ‖iteratedDeriv m f.toFun t‖ ≤ C0
      simpa using h
    have hmul : (1 + |t|) ^ R * ‖iteratedDeriv m f.toFun t‖ ≤
        2 ^ R * max C0 CR := by
      calc
        _ ≤ 2 ^ R * ‖iteratedDeriv m f.toFun t‖ :=
          mul_le_mul_of_nonneg_right hden (norm_nonneg _)
        _ ≤ 2 ^ R * max C0 CR := mul_le_mul_of_nonneg_left
          (hval.trans (le_max_left _ _)) (by positivity)
    apply (le_div_iff₀ (pow_pos (show 0 < 1 + |t| by positivity) R)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  · have ht' : 1 ≤ |t| := le_of_not_ge ht
    have hval : |t| ^ R * ‖iteratedDeriv m f.toFun t‖ ≤ CR := by
      have h := hCR t
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
      change |t| ^ R * ‖iteratedDeriv m f.toFun t‖ ≤ CR
      simpa [Real.norm_eq_abs] using h
    have hden : (1 + |t|) ^ R ≤ 2 ^ R * |t| ^ R := by
      calc
        _ ≤ (2 * |t|) ^ R := by gcongr; nlinarith [ht']
        _ = 2 ^ R * |t| ^ R := by rw [mul_pow]
    have hmul : (1 + |t|) ^ R * ‖iteratedDeriv m f.toFun t‖ ≤
        2 ^ R * max C0 CR := by
      calc
        _ ≤ (2 ^ R * |t| ^ R) * ‖iteratedDeriv m f.toFun t‖ :=
          mul_le_mul_of_nonneg_right hden (norm_nonneg _)
        _ = 2 ^ R * (|t| ^ R * ‖iteratedDeriv m f.toFun t‖) := by ring
        _ ≤ 2 ^ R * max C0 CR := mul_le_mul_of_nonneg_left
          (hval.trans (le_max_right _ _)) (by positivity)
    apply (le_div_iff₀ (pow_pos (show 0 < 1 + |t| by positivity) R)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

private lemma factor_deriv_bound {ι : Type*} [Fintype ι] (f : 𝓢(ℝ, ℂ)) (i : ι)
    (m R : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → ℝ,
      ‖iteratedFDeriv ℝ m (fun x : ι → ℝ => f (x i)) x‖ ≤
        C / (1 + |x i|) ^ R := by
  obtain ⟨Cf, hCf, hbound⟩ := exists_iteratedDeriv_poly_bound (f := f) R m
  let e : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let C : ℝ := Cf * max 1 ‖e‖ ^ m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun x => ?_⟩
  have hf_m : ContDiff ℝ (m : ℕ∞ω) (f : ℝ → ℂ) :=
    (f.smooth ⊤).of_le (by simp)
  have heq := e.iteratedFDeriv_comp_right hf_m x (i := m) le_rfl
  have hcomp := (iteratedFDeriv ℝ m f.toFun (e x)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => e)
  change ‖iteratedFDeriv ℝ m ((f : ℝ → ℂ) ∘ e) x‖ ≤ _
  rw [heq]
  have hderiv : ‖iteratedFDeriv ℝ m f.toFun (e x)‖ ≤ Cf / (1 + |x i|) ^ R := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simpa [e, ContinuousLinearMap.proj_apply] using hbound (x i)
  have hprod' : (∏ _j : Fin m, ‖e‖) ≤ max 1 ‖e‖ ^ m := by
    simpa [Finset.prod_const] using
      (pow_le_pow_left₀ (norm_nonneg e) (le_max_right 1 ‖e‖) m)
  calc
    ‖(iteratedFDeriv ℝ m f.toFun (e x)).compContinuousLinearMap (fun _ => e)‖ ≤
        ‖iteratedFDeriv ℝ m f.toFun (e x)‖ * ∏ _j : Fin m, ‖e‖ := hcomp
    _ ≤ (Cf / (1 + |x i|) ^ R) * (max 1 ‖e‖ ^ m) := by
      exact mul_le_mul hderiv hprod' (by positivity) (by positivity)
    _ = C / (1 + |x i|) ^ R := by dsimp [C]; ring

private lemma prod_mono_nonneg_real {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
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

private lemma prod_one_le_real {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact one_le_mul_of_one_le_of_one_le (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) )

private lemma single_le_prod_real {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 1 ≤ f i) (a : ι) (ha : a ∈ s) :
    f a ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at ha
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      rcases Finset.mem_insert.mp ha with h | h
      · subst a
        have htail : 1 ≤ ∏ j ∈ s, f j := by
          apply prod_one_le_real s f
          intro j hj
          exact hf j (Finset.mem_insert_of_mem hj)
        calc
          f i = f i * 1 := by ring
          _ ≤ f i * ∏ j ∈ s, f j :=
            mul_le_mul_of_nonneg_left htail (by linarith [hf i (Finset.mem_insert_self _ _)])
      · have hfa := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) h
        have hprod : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg fun j hj =>
          le_trans (by linarith [hf j (Finset.mem_insert_of_mem hj)])
            (hf j (Finset.mem_insert_of_mem hj))
        calc
          f a ≤ ∏ j ∈ s, f j := hfa
          _ ≤ f i * ∏ j ∈ s, f j := by
            calc
              _ = (∏ j ∈ s, f j) * 1 := by ring
              _ ≤ (∏ j ∈ s, f j) * f i :=
                mul_le_mul_of_nonneg_left (hf i (Finset.mem_insert_self _ _)) hprod
              _ = f i * ∏ j ∈ s, f j := by ring

/-- Every finite coordinate product of a one-dimensional Schwartz function is a Schwartz
function. -/
theorem exists_schwartz_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : 𝓢(ℝ, ℂ)) :
    ∃ F : 𝓢(ι → ℝ, ℂ), ∀ x, F x = ∏ i : ι, f (x i) := by
  let g : ι → (ι → ℝ) → ℂ := fun i x => f (x i)
  have hg_smooth (i : ι) : ContDiff ℝ ∞ (g i) := by
    dsimp [g]
    let e : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact f.smooth'.comp e.contDiff
  refine ⟨{
    toFun := fun x => ∏ i : ι, f (x i)
    smooth' := by
      simpa [g] using
        (contDiff_prod (t := (Finset.univ : Finset ι)) (fun i hi => hg_smooth i))
    decay' := ?_}, fun x => rfl⟩
  intro k n
  let R := k
  choose B hBpos hB using fun i : ι => fun m : ℕ => factor_deriv_bound f i m R
  let s : Finset (Sym ι n) := Finset.univ.sym n
  let A : ℝ := ∑ p ∈ s,
    (↑(p : Multiset ι).countPerms : ℝ) * ∏ i : ι, B i ((p : Multiset ι).count i)
  have hA : 0 ≤ A := by
    dsimp [A]
    apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg
    · positivity
    · apply Finset.prod_nonneg
      intro i hi
      exact hBpos i _
  refine ⟨A, fun x => ?_⟩
  have hdiff := norm_iteratedFDeriv_prod_le
    (u := (Finset.univ : Finset ι))
    (f := g) (fun i hi => hg_smooth i) (x := x) (n := n) (by simp)
  let D : ι → ℝ := fun i => 1 + |x i|
  let den : ℝ := ∏ i : ι, D i ^ R
  have hDenPos : 0 < den := by
    apply Finset.prod_pos
    intro i hi
    exact pow_pos (by dsimp [D]; positivity) _
  have hnormLeProd : ‖x‖ ≤ ∏ i : ι, D i := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ∏ i : ι, D i)).2
    intro i
    have hsingle : D i ≤ ∏ j : ι, D j := by
      exact single_le_prod_real (Finset.univ : Finset ι) D
        (by intro j hj; dsimp [D]; exact le_add_of_nonneg_right (abs_nonneg _))
        i (Finset.mem_univ i)
    calc
      ‖x i‖ = |x i| := Real.norm_eq_abs _
      _ ≤ D i := by dsimp [D]; linarith
      _ ≤ ∏ j : ι, D j := hsingle
  have hweight : ‖x‖ ^ k ≤ den := by
    dsimp [den, D, R]
    calc
      ‖x‖ ^ k ≤ (∏ i : ι, (1 + |x i|)) ^ k := by gcongr
      _ = ∏ i : ι, (1 + |x i|) ^ k := by rw [Finset.prod_pow]
  have hterm : ∀ p ∈ s,
      (↑(p : Multiset ι).countPerms : ℝ) *
          ∏ i : ι, ‖iteratedFDeriv ℝ ((p : Multiset ι).count i) (g i) x‖ ≤
        ((↑(p : Multiset ι).countPerms : ℝ) *
          ∏ i : ι, B i ((p : Multiset ι).count i)) / den := by
    intro p hp
    have hfactor (i : ι) :
        ‖iteratedFDeriv ℝ ((p : Multiset ι).count i) (g i) x‖ ≤
          B i ((p : Multiset ι).count i) / D i ^ R := by
      have hb := hB i ((p : Multiset ι).count i) x
      simpa [g, D] using hb
    have hpProd := prod_mono_nonneg_real (Finset.univ : Finset ι)
      (fun i => ‖iteratedFDeriv ℝ ((p : Multiset ι).count i) (g i) x‖)
      (fun i => B i ((p : Multiset ι).count i) / D i ^ R)
      (fun i hi => norm_nonneg _) (fun i hi => hfactor i)
    have hrewrite :
        (∏ i : ι, (B i ((p : Multiset ι).count i) / D i ^ R)) =
          (∏ i : ι, B i ((p : Multiset ι).count i)) / den := by
      simp [den, D, Finset.prod_div_distrib]
    rw [hrewrite] at hpProd
    let c : ℝ := ↑(p : Multiset ι).countPerms
    calc
      c * (∏ i : ι, ‖iteratedFDeriv ℝ ((p : Multiset ι).count i) (g i) x‖) ≤
          c * ((∏ i : ι, B i ((p : Multiset ι).count i)) / den) :=
        mul_le_mul_of_nonneg_left hpProd (by dsimp [c]; positivity)
      _ = (c * ∏ i : ι, B i ((p : Multiset ι).count i)) / den := by ring
  have hiter : ‖iteratedFDeriv ℝ n (fun x => ∏ i : ι, g i x) x‖ ≤ A / den := by
    calc
      _ ≤ ∑ p ∈ s, (↑(p : Multiset ι).countPerms : ℝ) *
          ∏ i : ι, ‖iteratedFDeriv ℝ ((p : Multiset ι).count i) (g i) x‖ := by
        simpa [s] using hdiff
      _ ≤ ∑ p ∈ s,
          ((↑(p : Multiset ι).countPerms : ℝ) *
            ∏ i : ι, B i ((p : Multiset ι).count i)) / den := by
        apply Finset.sum_le_sum
        intro p hp
        exact hterm p hp
      _ = A / den := by
        dsimp [A]
        rw [Finset.sum_div]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => ∏ i : ι, g i x) x‖ ≤
        den * ‖iteratedFDeriv ℝ n (fun x => ∏ i : ι, g i x) x‖ :=
      mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    _ ≤ den * (A / den) := mul_le_mul_of_nonneg_left hiter (le_of_lt hDenPos)
    _ = A := by field_simp

end FroehlichSpencer.BKT.Rotator

end
