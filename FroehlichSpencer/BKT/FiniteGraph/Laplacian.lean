/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite graph Laplacian algebra

Algebraic identities for the edge-once Laplacian and energy of a finite
oriented multigraph. The sign and multiplicity conventions are KP (1.1)–(1.3),
p. 2.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Multigraph

universe u v

variable {V : Type u} {E : Type v}

/-- Summation by parts for the finite-difference Laplacian, with every edge
counted once, as in KP (1.1)–(1.3), p. 2. -/
theorem pairing_laplacian_eq_neg_sum_grad_mul (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] {R : Type*} [CommRing R]
    (f g : V → R) :
    pairing f (G.laplacian g) = -∑ e, G.grad f e * G.grad g e := by
  classical
  simp only [pairing, laplacian, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, mul_ite, mul_zero, grad]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- The finite-difference Laplacian is symmetric for the vertex pairing. -/
theorem pairing_comm [Fintype V] {R : Type*} [CommRing R] (f g : V → R) :
    pairing f g = pairing g f := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The finite-difference Laplacian is symmetric for the vertex pairing. -/
theorem pairing_laplacian_comm (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] {R : Type*} [CommRing R] (f g : V → R) :
    pairing f (G.laplacian g) = pairing (G.laplacian f) g := by
  rw [pairing_laplacian_eq_neg_sum_grad_mul, pairing_comm,
    pairing_laplacian_eq_neg_sum_grad_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- The edge-once Dirichlet energy is the negative Laplacian quadratic form. -/
theorem energy_eq_neg_pairing_laplacian (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (f : V → ℝ) :
    G.energy f = -pairing f (G.laplacian f) := by
  rw [energy, pairing_laplacian_eq_neg_sum_grad_mul]
  simp only [neg_neg]
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- The edge-once Dirichlet energy is nonnegative. -/
theorem energy_nonneg (G : Multigraph V E) [Fintype E] (f : V → ℝ) :
    0 ≤ G.energy f := by
  unfold energy
  apply Finset.sum_nonneg
  intro e he
  exact sq_nonneg _

/-- A zero-energy field has zero difference along every edge. -/
theorem grad_eq_zero_of_energy_eq_zero (G : Multigraph V E) [Fintype E]
    (f : V → ℝ) (h : G.energy f = 0) (e : E) : G.grad f e = 0 := by
  have hle : G.grad f e ^ 2 ≤ G.energy f :=
    Finset.single_le_sum (fun e _ => sq_nonneg (G.grad f e)) (Finset.mem_univ e)
  rw [h] at hle
  have hsq : G.grad f e ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  have hmul : G.grad f e * G.grad f e = 0 := by
    simpa only [pow_two] using hsq
  rcases mul_eq_zero.mp hmul with hz | hz
  · exact hz
  · exact hz

/-- Adjacency in the underlying multigraph is symmetric. -/
theorem adj_symm (G : Multigraph V E) {j k : V} (h : G.Adj j k) : G.Adj k j := by
  rcases h with ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
  · exact ⟨e, Or.inr ⟨hs, ht⟩⟩
  · exact ⟨e, Or.inl ⟨hs, ht⟩⟩

/-- A zero-energy field takes equal values at adjacent vertices. -/
theorem eq_of_adj_of_energy_eq_zero (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (f : V → ℝ) (hE : G.energy f = 0) {j k : V}
    (hjk : G.Adj j k) : f j = f k := by
  rcases hjk with ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
  · have hz := G.grad_eq_zero_of_energy_eq_zero f hE e
    change f (G.src e) - f (G.tgt e) = 0 at hz
    rw [hs, ht] at hz
    exact sub_eq_zero.mp hz
  · have hz := G.grad_eq_zero_of_energy_eq_zero f hE e
    change f (G.src e) - f (G.tgt e) = 0 at hz
    rw [hs, ht] at hz
    exact (sub_eq_zero.mp hz).symm

/-- Zero energy forces equality along every walk in the underlying graph. -/
theorem eq_of_reachable_of_energy_eq_zero (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (hG : G.Connected) (f : V → ℝ) (hE : G.energy f = 0)
    (j k : V) : f j = f k := by
  have hreach : G.toSimpleGraph.Reachable j k := hG.preconnected j k
  rcases hreach with ⟨p⟩
  induction p with
  | nil => rfl
  | @cons u v w hadj p ih =>
      have hadjG : G.Adj u v := by
        rcases (SimpleGraph.fromRel_adj G.Adj u v).mp hadj with ⟨_, h | h⟩
        · exact h
        · exact G.adj_symm h
      exact (G.eq_of_adj_of_energy_eq_zero f hE hadjG).trans ih

/-- On a connected finite multigraph, zero energy characterizes constant fields. -/
theorem energy_eq_zero_iff_exists_const (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (f : V → ℝ) :
    G.energy f = 0 ↔ ∃ c, f = fun _ => c := by
  constructor
  · intro hE
    let v : V := Classical.choice hG.nonempty
    refine ⟨f v, ?_⟩
    funext j
    exact (G.eq_of_reachable_of_energy_eq_zero hG f hE v j).symm
  · rintro ⟨c, rfl⟩
    simp [energy, grad]

/-- The square of the difference across one edge is bounded by the full
Dirichlet energy. -/
theorem edge_difference_sq_le_energy (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (f : V → ℝ) {j k : V} (hjk : G.Adj j k) :
    (f j - f k) ^ 2 ≤ G.energy f := by
  have hle : (G.grad f (Classical.choose hjk)) ^ 2 ≤ G.energy f := by
    unfold energy
    exact Finset.single_le_sum (fun e _ => sq_nonneg (G.grad f e))
      (Finset.mem_univ (Classical.choose hjk))
  rcases Classical.choose_spec hjk with h | h
  · simpa [grad, h.1, h.2] using hle
  · have hgrad : G.grad f (Classical.choose hjk) = f k - f j := by
      simp [grad, h.1, h.2]
    rw [hgrad] at hle
    nlinarith

/-- A walk of length `n` bounds the squared endpoint difference by
`4^n` times the Dirichlet energy. -/
theorem walk_difference_sq_le_energy_pow (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (f : V → ℝ) {j k : V}
    (p : G.toSimpleGraph.Walk j k) :
    (f j - f k) ^ 2 ≤ (4 : ℝ) ^ p.length * G.energy f := by
  induction p with
  | nil => simpa using G.energy_nonneg f
  | @cons u v w hadj p ih =>
      have hadjG : G.Adj u v := by
        rcases (SimpleGraph.fromRel_adj G.Adj u v).mp hadj with ⟨_, h | h⟩
        · exact h
        · exact G.adj_symm h
      have hedge := G.edge_difference_sq_le_energy f hadjG
      let a : ℝ := f u - f v
      let b : ℝ := f v - f w
      have hsum : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
        nlinarith [sq_nonneg (a - b)]
      have ha : 2 * a ^ 2 ≤ 2 * G.energy f := by
        change 2 * (f u - f v) ^ 2 ≤ 2 * G.energy f
        nlinarith [hedge]
      have hb : 2 * b ^ 2 ≤ 2 * (4 : ℝ) ^ p.length * G.energy f := by
        change 2 * (f v - f w) ^ 2 ≤ 2 * (4 : ℝ) ^ p.length * G.energy f
        nlinarith [ih]
      have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ p.length :=
        one_le_pow₀ (by norm_num)
      have hcoeff : 2 + 2 * (4 : ℝ) ^ p.length ≤ 4 ^ (p.length + 1) := by
        rw [pow_succ]
        nlinarith
      have hE := G.energy_nonneg f
      calc
        (f u - f w) ^ 2 = (a + b) ^ 2 := by dsimp [a, b]; ring
        _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := hsum
        _ ≤ 2 * G.energy f + 2 * (4 : ℝ) ^ p.length * G.energy f :=
          add_le_add ha hb
        _ = (2 + 2 * (4 : ℝ) ^ p.length) * G.energy f := by ring
        _ ≤ 4 ^ (p.length + 1) * G.energy f :=
          mul_le_mul_of_nonneg_right hcoeff hE
        _ = (4 : ℝ) ^ (SimpleGraph.Walk.cons hadj p).length * G.energy f := by
          rw [SimpleGraph.Walk.length_cons]

/-- A connected finite graph satisfies a Poincaré-type estimate with the
explicit graph-dependent constant `|V| 4^|V|`. -/
theorem poincare_bound (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (root : V) (f : V → ℝ) :
    ∑ j, (f j - f root) ^ 2 ≤
      (Fintype.card V : ℝ) * (4 : ℝ) ^ Fintype.card V * G.energy f := by
  have hpoint (j : V) : (f j - f root) ^ 2 ≤
      (4 : ℝ) ^ Fintype.card V * G.energy f := by
    obtain ⟨p, hp⟩ := hG.exists_isPath root j
    have hwalk := G.walk_difference_sq_le_energy_pow f p
    have hwalk' : (f j - f root) ^ 2 ≤ (4 : ℝ) ^ p.length * G.energy f := by
      nlinarith [hwalk]
    have hlen : p.length < Fintype.card V := hp.length_lt
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hlen.le
    exact hwalk'.trans (mul_le_mul_of_nonneg_right hpow (G.energy_nonneg f))
  calc
    ∑ j, (f j - f root) ^ 2 ≤ ∑ j, ((4 : ℝ) ^ Fintype.card V * G.energy f) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = (Fintype.card V : ℝ) * (4 : ℝ) ^ Fintype.card V * G.energy f := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- For a connected graph, the kernel of the Laplacian consists exactly of
constant functions. -/
theorem laplacian_eq_zero_iff_exists_const (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (f : V → ℝ) :
    G.laplacian f = 0 ↔ ∃ c, f = fun _ => c := by
  constructor
  · intro hΔ
    have hE : G.energy f = 0 := by
      rw [G.energy_eq_neg_pairing_laplacian]
      simp [hΔ, pairing]
    exact (G.energy_eq_zero_iff_exists_const hG f).mp hE
  · rintro ⟨c, rfl⟩
    funext j
    simp [laplacian]

/-- The Laplacian annihilates every constant function, KP (1.1), p. 2. -/
@[simp]
theorem laplacian_const (G : Multigraph V E) [Fintype E] [DecidableEq V] {R : Type*}
    [AddCommGroup R] (c : R) : G.laplacian (fun _ : V => c) = 0 := by
  funext j
  simp [laplacian]

/-- The sum of the values of a finite graph Laplacian vanishes. -/
theorem sum_laplacian_eq_zero (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] {R : Type*} [CommRing R] (f : V → R) :
    ∑ j, G.laplacian f j = 0 := by
  have h := pairing_laplacian_eq_neg_sum_grad_mul G (fun _ => 1) f
  simpa [pairing, grad] using h

/-- The Laplacian as a linear map on vertex functions. -/
def laplacianₗ (G : Multigraph V E) [Fintype E] [DecidableEq V]
    (R : Type*) [CommRing R] :
    (V → R) →ₗ[R] (V → R) where
  toFun := fun f => G.laplacian f
  map_add' f g := by
    funext j
    classical
    simp only [laplacian, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> ring
  map_smul' a f := by
    funext j
    classical
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, laplacian]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> ring

/-- Pointwise evaluation of the Laplacian linear map. -/
@[simp]
theorem laplacianₗ_apply (G : Multigraph V E) [Fintype E] [DecidableEq V]
    {R : Type*} [CommRing R] (f : V → R) (j : V) :
    G.laplacianₗ R f j = G.laplacian f j := rfl

end FroehlichSpencer.BKT.Multigraph
