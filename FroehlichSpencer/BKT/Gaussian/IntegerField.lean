/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Green
public import FroehlichSpencer.BKT.Gaussian.Normalization
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Pinned integer Gaussian free field candidates

The weight below is the pinned integer Gaussian free field from KP, p. 3,
with the edge-once energy convention of KP (1.3).
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

open Multigraph

variable {V : Type u} {E : Type v}

/-- Integer configurations pinned to zero at the selected root. -/
def pinnedIntegerField (V : Type u) (root : V) :=
  {m : V → ℤ // m root = 0}

/-- The KP integer Gaussian weight on root-pinned configurations, with each
edge counted once; KP p. 3 and (1.3), p. 2. -/
noncomputable def igffWeight (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (β : ℝ) {root : V} (m : pinnedIntegerField V root) : ℝ :=
  Real.exp (-(β / 2) * G.energy (fun j => (m.1 j : ℝ)))

/-- The candidate integer Gaussian free field density is exactly the
edge-once KP weight on configurations pinned to zero at the root. -/
theorem igffWeight_eq_kp (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (β : ℝ) {root : V} (m : pinnedIntegerField V root) :
    igffWeight G β m = Real.exp (-(β / 2) *
      ∑ e, ((m.1 (G.src e) : ℝ) - (m.1 (G.tgt e) : ℝ)) ^ 2) := by
  rfl

/-- A one-dimensional integer Gaussian is summable. -/
theorem summable_int_gaussian {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-(a * (n : ℝ) ^ 2))) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hr : Real.exp (-a) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hgeom := summable_geometric_of_lt_one (Real.exp_pos _).le hr
  have hnat : Summable (fun n : ℕ => Real.exp (-(a * (n : ℝ) ^ 2))) := by
    refine hgeom.of_norm_bounded ?_
    intro n
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul (-a) n]
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      simpa only [pow_two] using
        (show (n : ℝ) ≤ (n : ℝ) * (n : ℝ) by exact_mod_cast Nat.le_mul_self n)
    have hm := mul_le_mul_of_nonpos_left hn (show -a ≤ 0 by linarith only [ha])
    nlinarith only [hm]
  constructor
  · exact hnat
  · simpa only [Int.cast_neg, neg_sq, Int.cast_natCast] using hnat

/-- The product-Gaussian weight on integer fields over `Fin n`. -/
noncomputable def intGaussianPi (n : ℕ) (a : ℝ)
    (m : Fin n → ℤ) : ℝ :=
  ∏ i, Real.exp (-(a * (m i : ℝ) ^ 2))

/-- Product-Gaussian weights are summable on every finite integer lattice. -/
theorem summable_intGaussianPi (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (intGaussianPi n a) := by
  induction n with
  | zero =>
      exact Summable.of_finite
  | succ n ih =>
      let e : (Fin (n + 1) → ℤ) ≃ ℤ × (Fin n → ℤ) :=
        (Equiv.piCongrLeft (fun _ : Option (Fin n) => ℤ)
          (finSuccEquiv n)).trans Equiv.piOptionEquivProd
      have hfactor (p : ℤ × (Fin n → ℤ)) :
          intGaussianPi (n + 1) a (e.symm p) =
            Real.exp (-(a * (p.1 : ℝ) ^ 2)) * intGaussianPi n a p.2 := by
        dsimp [intGaussianPi]
        rw [Fin.prod_univ_succ]
        simp [e]
      have hnonneg (p : ℤ × (Fin n → ℤ)) :
          0 ≤ Real.exp (-(a * (p.1 : ℝ) ^ 2)) * intGaussianPi n a p.2 := by
        apply mul_nonneg (Real.exp_pos _).le
        exact Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
      have hprod :
          Summable (fun p : ℤ × (Fin n → ℤ) =>
            Real.exp (-(a * (p.1 : ℝ) ^ 2)) * intGaussianPi n a p.2) := by
        rw [summable_prod_of_nonneg hnonneg]
        constructor
        · intro z
          exact (ih).mul_left (Real.exp (-(a * (z : ℝ) ^ 2)))
        · have hout : Summable (fun z : ℤ =>
              Real.exp (-(a * (z : ℝ) ^ 2)) * ∑' m, intGaussianPi n a m) :=
            (summable_int_gaussian ha).mul_right _
          convert hout using 1
          funext z
          change (∑' y, Real.exp (-(a * (z : ℝ) ^ 2)) * intGaussianPi n a y) =
            Real.exp (-(a * (z : ℝ) ^ 2)) * ∑' y, intGaussianPi n a y
          exact Summable.tsum_mul_left _ ih
      have hcomp : Summable (intGaussianPi (n + 1) a ∘ e.symm) := by
        convert hprod using 1
        funext p
        exact hfactor p
      exact (Equiv.summable_iff e.symm).mp hcomp

/-- The product-Gaussian weight on integer fields over a finite vertex type. -/
noncomputable def intGaussianPiV (V : Type u) [Fintype V] (a : ℝ)
    (m : V → ℤ) : ℝ :=
  ∏ j, Real.exp (-(a * (m j : ℝ) ^ 2))

/-- Product-Gaussian weights are summable on every finite integer lattice. -/
theorem summable_intGaussianPiV (V : Type u) [Fintype V] {a : ℝ}
    (ha : 0 < a) : Summable (intGaussianPiV V a) := by
  let eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let e := Equiv.piCongrLeft (fun _ : Fin (Fintype.card V) => ℤ) eV
  have hcomp : Summable (intGaussianPiV V a ∘ e.symm) := by
    convert summable_intGaussianPi (Fintype.card V) ha using 1
    funext m
    simp [intGaussianPiV, intGaussianPi, e, eV,
      Equiv.piCongrLeft_symm_apply]
    exact Equiv.prod_comp eV (fun i => Real.exp (-(a * (m i : ℝ) ^ 2)))
  exact (Equiv.summable_iff e.symm).mp hcomp

/-- The coordinate-square sum of a pinned integer field is bounded by the
edge energy through the connected-graph Poincaré estimate. -/
theorem igff_square_sum_le_energy (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) {root : V}
    (m : pinnedIntegerField V root) :
    ∑ j, (m.1 j : ℝ) ^ 2 ≤
      gffPoincareConstant V * G.energy (fun j => (m.1 j : ℝ)) := by
  have hroot : (m.1 root : ℝ) = 0 := by exact_mod_cast m.2
  have hp := G.poincare_bound hG root (fun j => (m.1 j : ℝ))
  simpa [hroot, gffPoincareConstant] using hp

/-- The candidate rooted IGFF weight is summable on a connected finite graph. -/
theorem summable_igffWeight (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) :
    Summable (fun m : pinnedIntegerField V root => igffWeight G β m) := by
  let C := gffPoincareConstant V
  let a := β / (2 * C)
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hG.nonempty
  have hC : 0 < C := by
    dsimp [C, gffPoincareConstant]
    exact mul_pos hcard (pow_pos (by norm_num) _)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hβ (mul_pos (by norm_num) hC)
  have hbase := summable_intGaussianPiV V ha
  have hpin : Summable (fun m : pinnedIntegerField V root =>
      intGaussianPiV V a m.1) :=
    hbase.comp_injective Subtype.val_injective
  have hprod_eq (m : pinnedIntegerField V root) :
      intGaussianPiV V a m.1 =
        Real.exp (-a * ∑ j, (m.1 j : ℝ) ^ 2) := by
    unfold intGaussianPiV
    rw [← Real.exp_sum]
    congr 1
    calc
      (∑ j, -(a * (m.1 j : ℝ) ^ 2)) =
          ∑ j, (-a) * (m.1 j : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (-a) * ∑ j, (m.1 j : ℝ) ^ 2 :=
        (Finset.mul_sum (Finset.univ : Finset V)
          (fun j => (m.1 j : ℝ) ^ 2) (-a)).symm
      _ = -a * ∑ j, (m.1 j : ℝ) ^ 2 := by ring
  refine hpin.of_norm_bounded ?_
  intro m
  rw [igffWeight, Real.norm_of_nonneg (Real.exp_pos _).le, hprod_eq]
  apply Real.exp_le_exp.mpr
  have hE := igff_square_sum_le_energy G hG m
  have hdiv : (∑ j, (m.1 j : ℝ) ^ 2) / C ≤
      G.energy (fun j => (m.1 j : ℝ)) := by
    apply (div_le_iff₀ hC).2
    nlinarith only [hE]
  have hcoefle : -(β / 2) ≤ 0 := by linarith only [hβ]
  have hmul := mul_le_mul_of_nonpos_left hdiv hcoefle
  dsimp [igffWeight, a]
  have hcoef : -(β / 2) *
      ((∑ j, (m.1 j : ℝ) ^ 2) / C) =
        -(β / (2 * C)) * ∑ j, (m.1 j : ℝ) ^ 2 := by
    field_simp [ne_of_gt hC]
  rw [hcoef] at hmul
  simpa [a] using hmul

/-- The unnormalized real exponential tilt of the rooted IGFF weight. -/
noncomputable def igffTiltedWeight (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (β : ℝ) {root : V} (f : V → ℝ)
    (m : pinnedIntegerField V root) : ℝ :=
  Real.exp (pairing (fun j => (m.1 j : ℝ)) f) * igffWeight G β m

/-- The linear part of a finite-dimensional Gaussian exponent is absorbed by
half of its quadratic decay, with the remaining factor integrable. -/
theorem summable_igffTiltedWeight (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (f : V → ℝ) :
    Summable (fun m : pinnedIntegerField V root =>
      igffTiltedWeight G β f m) := by
  let C := gffPoincareConstant V
  let a := β / (2 * C)
  let b := (∑ j, (f j) ^ 2) / (2 * a)
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hG.nonempty
  have hC : 0 < C := by
    dsimp [C, gffPoincareConstant]
    exact mul_pos hcard (pow_pos (by norm_num) _)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hβ (mul_pos (by norm_num) hC)
  have hhalf : 0 < a / 2 := by positivity
  have hbase := summable_intGaussianPiV V hhalf
  have hpin : Summable (fun m : pinnedIntegerField V root =>
      intGaussianPiV V (a / 2) m.1) :=
    hbase.comp_injective Subtype.val_injective
  have hYoung (x y : ℝ) : x * y ≤ (a / 2) * x ^ 2 + y ^ 2 / (2 * a) := by
    field_simp [ne_of_gt ha]
    nlinarith only [sq_nonneg (a * x - y)]
  have hpair (m : pinnedIntegerField V root) :
      pairing (fun j => (m.1 j : ℝ)) f ≤
        (a / 2) * (∑ j, (m.1 j : ℝ) ^ 2) + b := by
    unfold pairing
    calc
      (∑ j, (m.1 j : ℝ) * f j) ≤
          ∑ j, ((a / 2) * (m.1 j : ℝ) ^ 2 +
            (f j) ^ 2 / (2 * a)) :=
        Finset.sum_le_sum fun j _ => hYoung (m.1 j : ℝ) (f j)
      _ = (a / 2) * (∑ j, (m.1 j : ℝ) ^ 2) + b := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
        rfl
  have henergy (m : pinnedIntegerField V root) :
      -(β / 2) * G.energy (fun j => (m.1 j : ℝ)) ≤
        -a * ∑ j, (m.1 j : ℝ) ^ 2 := by
    have hp := igff_square_sum_le_energy G hG m
    have hdiv : (∑ j, (m.1 j : ℝ) ^ 2) / C ≤
        G.energy (fun j => (m.1 j : ℝ)) := by
      apply (div_le_iff₀ hC).2
      nlinarith only [hp]
    have hcoefle : -(β / 2) ≤ 0 := by linarith only [hβ]
    have hm := mul_le_mul_of_nonpos_left hdiv hcoefle
    have hcoef : -(β / 2) *
        ((∑ j, (m.1 j : ℝ) ^ 2) / C) =
          -a * ∑ j, (m.1 j : ℝ) ^ 2 := by
      dsimp [a]
      field_simp [ne_of_gt hC]
    dsimp [a] at hm ⊢
    rw [hcoef] at hm
    exact hm
  have hexp (m : pinnedIntegerField V root) :
      igffTiltedWeight G β f m ≤
        Real.exp b * intGaussianPiV V (a / 2) m.1 := by
    rw [igffTiltedWeight, igffWeight, intGaussianPiV,
      ← Real.exp_sum, ← Real.exp_add]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp := hpair m
    have he := henergy m
    dsimp [b] at hp ⊢
    have hsum : (∑ j, -(a / 2 * (m.1 j : ℝ) ^ 2)) =
        -(a / 2) * ∑ j, (m.1 j : ℝ) ^ 2 := by
      calc
        (∑ j, -(a / 2 * (m.1 j : ℝ) ^ 2)) =
            ∑ j, (-(a / 2)) * (m.1 j : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (-(a / 2)) * ∑ j, (m.1 j : ℝ) ^ 2 :=
          (Finset.mul_sum _ _ _).symm
    rw [hsum]
    nlinarith only [hp, he]
  have hmajor := Summable.mul_left (‖Real.exp b‖) hpin
  refine hmajor.of_norm_bounded ?_
  intro m
  have hnonneg : 0 ≤ igffTiltedWeight G β f m := by
    rw [igffTiltedWeight]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hexp m

/-- The partition sum for the root-pinned integer Gaussian free field, KP
p. 3. Its indexing type is the set of integer fields pinned to zero at the
root, so `tsum` is counting measure on the remaining coordinates. -/
noncomputable def igffPartitionFunction (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (β : ℝ) (root : V) : ℝ :=
  ∑' m : pinnedIntegerField V root, igffWeight G β m

/-- The rooted IGFF partition sum is positive for positive inverse temperature
on a connected graph. -/
theorem igffPartitionFunction_pos (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) : 0 < igffPartitionFunction G β root := by
  let m₀ : pinnedIntegerField V root := ⟨0, by simp⟩
  have hsum := summable_igffWeight G hG β hβ root
  have hzero : igffWeight G β m₀ = 1 := by
    simp [igffWeight, energy, grad, m₀]
  have hle := hsum.le_tsum m₀ fun m _ => (Real.exp_pos _).le
  rw [hzero] at hle
  change 1 ≤ igffPartitionFunction G β root at hle
  linarith only [hle]

/-- The candidate rooted IGFF expectation, defined as the normalized sum of
the observable against the KP weight, KP p. 3. -/
noncomputable def igffExpectation (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (_hG : G.Connected) (β : ℝ)
    (_hβ : 0 < β) (root : V)
    (F : pinnedIntegerField V root → ℝ) : ℝ :=
  (∑' m, F m * igffWeight G β m) / igffPartitionFunction G β root

/-- The IGFF expectation is the normalized absolutely summable lattice sum
whenever the weighted observable is summable. -/
theorem igffExpectation_eq_normalized_tsum (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V)
    (F : pinnedIntegerField V root → ℝ) :
    igffExpectation G hG β hβ root F =
      (∑' m, F m * igffWeight G β m) / igffPartitionFunction G β root := rfl

end FroehlichSpencer.BKT
