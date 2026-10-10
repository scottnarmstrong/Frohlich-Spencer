/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Green
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Variational principles for the finite graph Green operator

The Dirichlet and Thomson principles express the Green quadratic form as the
minimum energy of a flow and the supremum of a potential quotient. The signs
use KP's convention `Δ f(j) = ∑ (f(ℓ) - f(j))` and outgoing-minus-incoming
flow divergence.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

namespace Multigraph

universe u v

variable {V : Type u} {E : Type v}

/-- Real divergence of an edge flow, with outgoing edges positive and incoming
edges negative, matching `Villain.currentDivergence`. -/
def flowDivergence (G : Multigraph V E) [Fintype E] [DecidableEq V]
    (J : E → ℝ) (j : V) : ℝ :=
  (∑ e, if G.src e = j then J e else 0) -
    (∑ e, if G.tgt e = j then J e else 0)

/-- The gradient flow has divergence equal to minus the finite-difference
Laplacian. -/
theorem flowDivergence_grad_eq_neg_laplacian (G : Multigraph V E)
    [Fintype E] [DecidableEq V] (g : V → ℝ) (j : V) :
    G.flowDivergence (G.grad g) j = -G.laplacian g j := by
  classical
  unfold flowDivergence laplacian grad
  calc
    (∑ e, (if G.src e = j then g (G.src e) - g (G.tgt e) else 0)) -
        (∑ e, if G.tgt e = j then g (G.src e) - g (G.tgt e) else 0) =
        ∑ e, (((if G.src e = j then g (G.src e) - g (G.tgt e) else 0)) -
          ((if G.tgt e = j then g (G.src e) - g (G.tgt e) else 0))) := by
      simp only [Finset.sum_sub_distrib]
    _ = ∑ e, (-((if G.src e = j then g (G.tgt e) - g j else 0) +
          (if G.tgt e = j then g (G.src e) - g j else 0)) ) := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hs : G.src e = j <;> by_cases ht : G.tgt e = j
      · have hst : G.src e = G.tgt e := hs.trans ht.symm
        exact (G.src_ne_tgt e hst).elim
      · simp [hs, ht]
      · simp [hs, ht]
      · simp [hs, ht]
    _ = -(∑ e, ((if G.src e = j then g (G.tgt e) - g j else 0) +
          (if G.tgt e = j then g (G.src e) - g j else 0))) := by
      simp only [Finset.sum_neg_distrib]

/-- Summation by parts for a real flow and its divergence. -/
theorem pairing_flowDivergence_eq_sum_mul_grad (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (J : E → ℝ) (g : V → ℝ) :
    pairing (G.flowDivergence J) g = ∑ e, J e * G.grad g e := by
  classical
  unfold pairing flowDivergence
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hsrc :
      (∑ j, (∑ e, if G.src e = j then J e else 0) * g j) =
        ∑ e, J e * g (G.src e) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  have htgt :
      (∑ j, (∑ e, if G.tgt e = j then J e else 0) * g j) =
        ∑ e, J e * g (G.tgt e) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  rw [hsrc, htgt]
  simp only [Multigraph.grad, mul_sub, Finset.sum_sub_distrib]

/-- The Dirichlet principle: the squared pairing with a zero-sum source is
bounded by its Green quadratic form times the potential energy. -/
theorem dirichlet_principle (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∑ v, f v = 0) (u : V → ℝ) :
    (pairing u f) ^ 2 ≤ pairing f (-G.greenOp hG f) * G.energy u := by
  classical
  let g := G.greenOp hG f
  have hΔ : G.laplacian g = f := G.laplacian_greenOp_of_sum_eq_zero hG f hf
  have hpair : pairing u f = -∑ e, G.grad u e * G.grad g e := by
    rw [← hΔ]
    exact G.pairing_laplacian_eq_neg_sum_grad_mul u g
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun e => G.grad u e) (fun e => G.grad g e)
  have hcauchy' :
      (∑ e, G.grad u e * G.grad g e) ^ 2 ≤
        G.energy u * G.energy g := by
    simpa only [energy] using hcauchy
  calc
    (pairing u f) ^ 2 = (-∑ e, G.grad u e * G.grad g e) ^ 2 := by rw [hpair]
    _ = (∑ e, G.grad u e * G.grad g e) ^ 2 := by ring
    _ ≤ G.energy u * G.energy g := hcauchy'
    _ = pairing f (-G.greenOp hG f) * G.energy u := by
      rw [← G.pairing_eq_energy_greenOp hG f hf]
      ring

/-- Equality in the Dirichlet principle holds at the Green potential. -/
theorem dirichlet_principle_at_greenOp (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (f : V → ℝ) (hf : ∑ v, f v = 0) :
    (pairing (G.greenOp hG f) f) ^ 2 =
      pairing f (-G.greenOp hG f) * G.energy (G.greenOp hG f) := by
  calc
    (pairing (G.greenOp hG f) f) ^ 2 =
        (pairing f (-G.greenOp hG f)) ^ 2 := by
      rw [pairing_comm, pairing_neg_right]
      ring
    _ = pairing f (-G.greenOp hG f) * G.energy (G.greenOp hG f) := by
      rw [← G.pairing_eq_energy_greenOp hG f hf]
      ring

/-- Thomson's principle: every flow with divergence `f` has energy at least
the Green quadratic form of `f`. -/
theorem thomson_principle (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∑ v, f v = 0) (J : E → ℝ)
    (hJ : G.flowDivergence J = f) :
    pairing f (-G.greenOp hG f) ≤ ∑ e, J e ^ 2 := by
  classical
  let g := G.greenOp hG f
  have hQ : pairing f (-G.greenOp hG f) = G.energy g :=
    G.pairing_eq_energy_greenOp hG f hf
  have hdiv : pairing (G.flowDivergence J) g = pairing f g := by
    rw [hJ]
  have hparts := G.pairing_flowDivergence_eq_sum_mul_grad J g
  have hcross : ∑ e, J e * G.grad g e = -G.energy g := by
    rw [← hparts, hdiv, pairing_comm]
    rw [G.energy_eq_neg_pairing_laplacian]
    rw [G.laplacian_greenOp_of_sum_eq_zero hG f hf]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ J (fun e => G.grad g e)
  have hcs' : (∑ e, J e * G.grad g e) ^ 2 ≤
      (∑ e, J e ^ 2) * G.energy g := by
    simpa [energy] using hcs
  rw [hcross] at hcs'
  rw [hQ]
  have hE : 0 ≤ G.energy g := G.energy_nonneg g
  by_cases hzero : G.energy g = 0
  · rw [hzero]
    exact Finset.sum_nonneg fun e _ => sq_nonneg (J e)
  · have hpos : 0 < G.energy g := lt_of_le_of_ne hE (Ne.symm hzero)
    nlinarith [hcs']

end Multigraph

end FroehlichSpencer.BKT

end
