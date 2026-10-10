/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Potential.Variational
public import FroehlichSpencer.BKT.Potential.NashWilliams

/-!
# The unit dipole potential (the dipole tilt construction: the tilt and the shift of FS81 (7.22))

On a connected finite multigraph, the unit dipole potential is `g = −G⁻¹(δ_p − δ_q)`
(`dipolePotential`, with KP's mean-zero inverse `greenOp`), so `−Δg = δ_p − δ_q`. It carries both
the tilt and the real shift of the SOS argument (FS81 (7.22): `σ_β = σ(β) ε [C(·) − C(· − x)]`):

* `sum_grad_mul_grad_dipolePotential`: `⟨∇φ, ∇g⟩ = φ(p) − φ(q)` for **every** field `φ`, so the
  tilt `e^{ε(φ(p) − φ(q))}` is `e^{⟨∇φ, ε∇g⟩}`;
* `abs_grad_dipolePotential_le_one`: `|∇g(e)| ≤ 1` on every edge (the unit current is at most one
  on every edge: pair `∇g` with the indicator of a superlevel set of `g`);
* `sum_grad_sq_dipolePotential`: `‖∇g‖² = R(p, q)`, the effective resistance
  `R(p, q) = ⟨δ_p − δ_q, g⟩` (`dipoleResistance`), which Nash–Williams bounds from below
  (`Multigraph.pairing_pointDipole_ge_log_of_levelCut_bound`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Multigraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The unit dipole potential `g = −G⁻¹(δ_p − δ_q)`. -/
def dipolePotential (G : Multigraph V E) (hG : G.Connected) (p q : V) : V → ℝ :=
  -G.greenOp hG (pointDipole p q)

/-- The effective resistance `R(p, q) = ⟨δ_p − δ_q, −G⁻¹(δ_p − δ_q)⟩`. -/
def dipoleResistance (G : Multigraph V E) (hG : G.Connected) (p q : V) : ℝ :=
  pairing (pointDipole p q) (dipolePotential G hG p q)

theorem pairing_pointDipole_right (φ : V → ℝ) (p q : V) :
    pairing φ (pointDipole p q) = φ p - φ q := by
  unfold pairing pointDipole
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

theorem pairing_pointDipole_left (φ : V → ℝ) (p q : V) :
    pairing (pointDipole p q) φ = φ p - φ q := by
  rw [pairing_comm, pairing_pointDipole_right]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem grad_neg' (G : Multigraph V E) (f : V → ℝ) (e : E) : G.grad (-f) e = -G.grad f e := by
  simp only [Multigraph.grad, Pi.neg_apply]
  ring

/-- **The dipole identity**: `⟨∇φ, ∇g⟩ = φ(p) − φ(q)` for every field `φ`. -/
theorem sum_grad_mul_grad_dipolePotential (G : Multigraph V E) (hG : G.Connected) (p q : V)
    (φ : V → ℝ) :
    ∑ e, G.grad φ e * G.grad (dipolePotential G hG p q) e = φ p - φ q := by
  have hΔ := G.laplacian_greenOp_of_sum_eq_zero hG (pointDipole p q) (sum_pointDipole_eq_zero p q)
  have h := G.pairing_laplacian_eq_neg_sum_grad_mul φ (G.greenOp hG (pointDipole p q))
  rw [hΔ, pairing_pointDipole_right] at h
  unfold dipolePotential
  simp only [grad_neg', mul_neg, Finset.sum_neg_distrib]
  linarith

/-- The resistance is the Dirichlet energy of the dipole potential. -/
theorem sum_grad_sq_dipolePotential (G : Multigraph V E) (hG : G.Connected) (p q : V) :
    ∑ e, G.grad (dipolePotential G hG p q) e ^ 2 = dipoleResistance G hG p q := by
  have h := sum_grad_mul_grad_dipolePotential G hG p q (dipolePotential G hG p q)
  unfold dipoleResistance
  rw [pairing_pointDipole_left, ← h]
  exact Finset.sum_congr rfl fun e _ => sq _

theorem dipoleResistance_nonneg (G : Multigraph V E) (hG : G.Connected) (p q : V) :
    0 ≤ dipoleResistance G hG p q := by
  rw [← sum_grad_sq_dipolePotential]
  exact Finset.sum_nonneg fun e _ => sq_nonneg _

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- Against the indicator of a superlevel set of `g`, every edge term of `⟨∇φ, ∇g⟩` is
nonnegative. -/
lemma grad_superlevel_mul_grad_nonneg (G : Multigraph V E) (g : V → ℝ) (x : V) (e : E) :
    0 ≤ G.grad (fun z => if g x ≤ g z then (1 : ℝ) else 0) e * G.grad g e := by
  simp only [Multigraph.grad]
  by_cases h1 : g x ≤ g (G.src e) <;> by_cases h2 : g x ≤ g (G.tgt e) <;>
    simp only [h1, h2, ↓reduceIte, sub_self, zero_mul, sub_zero, one_mul, zero_sub, neg_mul,
      neg_nonneg] <;> linarith

/-- **The unit current is at most one on every edge.** -/
theorem abs_grad_dipolePotential_le_one (G : Multigraph V E) (hG : G.Connected) (p q : V)
    (e : E) : |G.grad (dipolePotential G hG p q) e| ≤ 1 := by
  set g := dipolePotential G hG p q with hg
  -- the pairing with a superlevel indicator is at most one
  have hsum : ∀ x : V, ∑ e', G.grad (fun z => if g x ≤ g z then (1 : ℝ) else 0) e' *
      G.grad g e' ≤ 1 := by
    intro x
    rw [sum_grad_mul_grad_dipolePotential]
    by_cases h1 : g x ≤ g p <;> by_cases h2 : g x ≤ g q <;> simp [h1, h2]
  have hterm : ∀ x : V, G.grad (fun z => if g x ≤ g z then (1 : ℝ) else 0) e * G.grad g e ≤ 1 :=
    fun x => le_trans (Finset.single_le_sum (f := fun e' =>
      G.grad (fun z => if g x ≤ g z then (1 : ℝ) else 0) e' * G.grad g e')
      (fun e' _ => grad_superlevel_mul_grad_nonneg G g x e') (Finset.mem_univ e)) (hsum x)
  rcases lt_trichotomy (g (G.src e)) (g (G.tgt e)) with hlt | heq | hgt
  · have h := hterm (G.tgt e)
    simp only [Multigraph.grad, not_le.mpr hlt, le_refl, ↓reduceIte] at h
    rw [abs_of_neg (by simp only [Multigraph.grad]; linarith)]
    simp only [Multigraph.grad]
    linarith
  · simp only [Multigraph.grad, heq, sub_self, abs_zero]
    norm_num
  · have h := hterm (G.src e)
    simp only [Multigraph.grad, not_le.mpr hgt, le_refl, ↓reduceIte] at h
    rw [abs_of_pos (by simp only [Multigraph.grad]; linarith)]
    simp only [Multigraph.grad]
    linarith

end FroehlichSpencer.BKT.SOS.Tilt

end
