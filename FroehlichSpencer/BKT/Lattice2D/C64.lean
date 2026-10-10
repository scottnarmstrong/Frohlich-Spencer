/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import FroehlichSpencer.BKT.Lattice2D.TorusLogUpperBound

/-!
# KP Claim 6.4: reflection and line-source Green energy

This module records the free-box line source and its finite four-cycle value,
then develops the reflected torus estimate used in Claim 6.4.
-/

@[expose] public section

open FroehlichSpencer.BKT.Multigraph

namespace FroehlichSpencer.BKT.Lattice2D

noncomputable section

@[instance_reducible] def squareFreeEdgeIndexUnique :
    Unique {i : Fin 2 // i.val + 1 < 2} where
  default := ⟨0, by decide⟩
  uniq a := by
    apply Subtype.ext
    apply Fin.ext
    have hp : a.1.val + 1 < 2 := a.2
    change a.1.val = 0
    omega

local instance : Unique {i : Fin 2 // i.val + 1 < 2} :=
  squareFreeEdgeIndexUnique

@[simp] theorem default_squareFreeEdgeIndex_val :
    (default : {i : Fin 2 // i.val + 1 < 2}).val = 0 := rfl

def squareFree2p : SquareFreeVertex 2 :=
  (⟨1, by omega⟩, ⟨0, by omega⟩)

def squareFree2q : SquareFreeVertex 2 :=
  (⟨1, by omega⟩, ⟨1, by omega⟩)

def squareFree2r : SquareFreeVertex 2 :=
  (⟨0, by omega⟩, ⟨1, by omega⟩)

def squareFree2s : SquareFreeVertex 2 :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

def squareFree2Dipole : SquareFreeVertex 2 → ℝ := fun v =>
  (if v = squareFree2p then 1 else 0) -
    (if v = squareFree2q then 1 else 0)

def squareFree2Potential : SquareFreeVertex 2 → ℝ := fun v =>
  if v = squareFree2p then -(3 / 8 : ℝ)
  else if v = squareFree2q then 3 / 8
  else if v = squareFree2r then 1 / 8
  else if v = squareFree2s then -(1 / 8)
  else 0

theorem squareFree2Potential_sum :
    ∑ v : SquareFreeVertex 2, squareFree2Potential v = 0 := by
  norm_num [squareFree2Potential, squareFree2p, squareFree2q, squareFree2r,
    squareFree2s, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem squareFree2Potential_laplacian :
    (squareFreeGraph 2).laplacian squareFree2Potential = squareFree2Dipole := by
  funext v
  rcases v with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Multigraph.laplacian, squareFreeGraph, squareFree2Potential,
      squareFree2Dipole, squareFree2p, squareFree2q, squareFree2r,
      squareFree2s, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_succ, default_squareFreeEdgeIndex_val] <;> norm_num

/-- The free four-cycle has dipole Green energy `3/4`. This explicitly checks
the `N = 1` endpoint that invalidates the cancelled cross-term formula. -/
theorem squareFree_two_by_two_lineSource_energy_eq_threeQuarters :
    pairing squareFree2Dipole
      (-((squareFreeGraph 2).greenOp (squareFreeGraph_connected (by omega))
        squareFree2Dipole)) = (3 / 4 : ℝ) := by
  have hgreen :
      (squareFreeGraph 2).greenOp (squareFreeGraph_connected (by omega))
        squareFree2Dipole = squareFree2Potential := by
    calc
      _ = (squareFreeGraph 2).greenOp (squareFreeGraph_connected (by omega))
          ((squareFreeGraph 2).laplacian squareFree2Potential) := by
            rw [squareFree2Potential_laplacian]
      _ = squareFree2Potential :=
        Multigraph.greenOp_laplacian_of_sum_eq_zero (G := squareFreeGraph 2)
          (squareFreeGraph_connected (by omega)) squareFree2Potential
          squareFree2Potential_sum
  rw [hgreen]
  norm_num [Multigraph.pairing, squareFree2Dipole, squareFree2Potential,
    squareFree2p, squareFree2q, squareFree2r, squareFree2s,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The `N = 1` free-box energy is covered by the same explicit error
constant used for the reflected-strip estimate. -/
theorem squareFree_two_by_two_lineSource_energy_ge_one_sub_656_log_two :
    (3 / 4 : ℝ) ≥ 1 - 656 * Real.log 2 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  nlinarith only [hlog]

/-- The centered natural representative of a cyclic displacement. -/
def torusCyclicAxisDistance (n m : ℕ) : ℕ := min m (n - m)

/-- KP (6.13) for an arbitrary natural representative of a cyclic horizontal
displacement. -/
theorem torusGreenKernel_axis_cyclic_log_upper_bound {n : ℕ} [NeZero n]
    (hn : 2 < n) (hG : (torusGraph n hn).Connected) (m : ℕ) (hmn : m ≤ n) :
    torusGreenKernel hn hG (0, 0) (0, 0) -
        torusGreenKernel hn hG ((m : ZMod n), 0) (0, 0) ≤
      41 * Real.log (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ) := by
  let d := torusCyclicAxisDistance n m
  have hd : 2 * d ≤ n := by
    dsimp [d, torusCyclicAxisDistance]
    by_cases h : m ≤ n - m <;> omega
  have hcast : (d : ZMod n) = (m : ZMod n) ∨
      (d : ZMod n) = -(m : ZMod n) := by
    dsimp [d, torusCyclicAxisDistance]
    by_cases h : m ≤ n - m
    · left
      rw [Nat.min_eq_left h]
    · right
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]
      rw [Nat.cast_sub hmn]
      simp
  have hneg (x : TorusVertex n) :
      torusGreenKernel hn hG (-x) (0, 0) =
        torusGreenKernel hn hG x (0, 0) := by
    calc
      torusGreenKernel hn hG (-x) (0, 0) =
          torusGreenKernel hn hG (0, 0) (-x) :=
            torusGreenKernel_symm hn hG (-x) (0, 0)
      _ = torusGreenKernel hn hG x (0, 0) := by
        have hzero : x + -x = (0, 0) := by ext <;> simp
        have hsum : (0, 0) + -x = -x := by ext <;> simp
        simpa only [hzero, hsum] using
          torusGreenKernel_translation hn hG (-x) x (0, 0)
  have hpoint :
      torusGreenKernel hn hG ((m : ZMod n), 0) (0, 0) =
        torusGreenKernel hn hG ((d : ZMod n), 0) (0, 0) := by
    rcases hcast with h | h
    · simpa [d] using congrArg
        (fun z : ZMod n => torusGreenKernel hn hG (z, 0) (0, 0)) h.symm
    · have htuple : ((d : ZMod n), (0 : ZMod n)) =
        -((m : ZMod n), (0 : ZMod n)) := by
        ext <;> simp [h]
      calc
        torusGreenKernel hn hG ((m : ZMod n), 0) (0, 0) =
            torusGreenKernel hn hG (-((m : ZMod n), 0)) (0, 0) :=
              (hneg ((m : ZMod n), 0)).symm
        _ = torusGreenKernel hn hG ((d : ZMod n), 0) (0, 0) := by
          rw [← htuple]
  have haxis := torusGreenKernel_axis_log_upper_bound hn hG d hd
  rw [hpoint]
  simpa [d, torusCyclicAxisDistance] using haxis

/-- The Green energy of a torus dipole is twice the corresponding kernel
difference, with no restriction on the location of its endpoints. -/
theorem torusGreenBilinear_dipole_eq_two_kernel_difference {n : ℕ} [NeZero n]
    (hn : 2 < n) (hG : (torusGraph n hn).Connected) (p q : TorusVertex n) :
    greenBilinear (torusGraph n hn) hG (dipole p q) (dipole p q) =
      2 * (torusGreenKernel hn hG (0, 0) (0, 0) -
        torusGreenKernel hn hG (q - p) (0, 0)) := by
  let G := torusGraph n hn
  let δp : TorusVertex n → ℝ := deltaAt p
  let δq : TorusVertex n → ℝ := deltaAt q
  have hdipole : dipole p q = δp - δq := by
    funext v
    simp [δp, δq, dipole, deltaAt]
  have hkernel (x y : TorusVertex n) :
      greenBilinear G hG (deltaAt x) (deltaAt y) =
        torusGreenKernel hn hG x y := by
    rw [torusGreenKernel_eq_pairing]
    rfl
  have hdiag (x : TorusVertex n) :
      torusGreenKernel hn hG x x = torusGreenKernel hn hG (0, 0) (0, 0) := by
    have hzero : (0, 0) + x = x := by ext <;> simp
    simpa only [hzero] using
      torusGreenKernel_translation hn hG x (0, 0) (0, 0)
  have hcross :
      torusGreenKernel hn hG p q =
        torusGreenKernel hn hG (0, 0) (q - p) := by
    have hpzero : p + -p = (0, 0) := by ext <;> simp
    have hqsub : q + -p = q - p := by ext <;> simp [sub_eq_add_neg]
    simpa only [hpzero, hqsub] using
      (torusGreenKernel_translation hn hG (-p) p q).symm
  have henergy :
      greenBilinear G hG (dipole p q) (dipole p q) =
        2 * (torusGreenKernel hn hG (0, 0) (0, 0) -
          torusGreenKernel hn hG (q - p) (0, 0)) := by
    rw [hdipole]
    rw [greenBilinear_sub_self G hG δp δq]
    dsimp [δp, δq]
    rw [hkernel p p, hkernel q q, hkernel p q, hkernel q p]
    rw [hdiag p, hdiag q, torusGreenKernel_symm hn hG q p, hcross]
    rw [torusGreenKernel_symm hn hG (0, 0) (q - p)]
    ring
  exact henergy

/-- Horizontal torus dipoles have Green energy at most `82 log(d+1)`, where
`d` is the centered cyclic displacement. -/
theorem torusGreenBilinear_horizontal_dipole_log_upper_bound {n : ℕ} [NeZero n]
    (hn : 2 < n) (hG : (torusGraph n hn).Connected) (p : TorusVertex n)
    (m : ℕ) (hmn : m ≤ n) :
    greenBilinear (torusGraph n hn) hG (dipole p (p + ((m : ZMod n), 0)))
        (dipole p (p + ((m : ZMod n), 0))) ≤
      82 * Real.log (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ) := by
  rw [torusGreenBilinear_dipole_eq_two_kernel_difference]
  have hdiff : p + ((m : ZMod n), 0) - p = ((m : ZMod n), 0) := by
    ext <;> simp
  rw [hdiff]
  have haxis := torusGreenKernel_axis_cyclic_log_upper_bound hn hG m hmn
  nlinarith only [haxis]

/-- Cauchy--Schwarz for the positive Green bilinear form, obtained from the
finite-graph Dirichlet principle. -/
theorem torusGreenBilinear_cauchy_sq {n : ℕ} [NeZero n]
    (hn : 2 < n) (hG : (torusGraph n hn).Connected)
    (f g : TorusVertex n → ℝ) (hf : ∑ x, f x = 0) (hg : ∑ x, g x = 0) :
    greenBilinear (torusGraph n hn) hG f g ^ 2 ≤
      greenBilinear (torusGraph n hn) hG f f *
        greenBilinear (torusGraph n hn) hG g g := by
  let G := torusGraph n hn
  let u : TorusVertex n → ℝ := -G.greenOp hG g
  have hpair : pairing u f = greenBilinear G hG f g := by
    dsimp [u, greenBilinear]
    rw [pairing_comm]
  have henergy : G.energy u = G.energy (G.greenOp hG g) := by
    simp only [u, Multigraph.energy, Multigraph.grad, Pi.neg_apply]
    apply Finset.sum_congr rfl
    intro e he
    ring
  have hdir := G.dirichlet_principle hG f hf u
  have hdir' : (pairing u f) ^ 2 ≤
      greenBilinear G hG f f * G.energy u := by
    simpa [greenBilinear] using hdir
  have hgreenEnergy : G.energy (G.greenOp hG g) =
      greenBilinear G hG g g :=
    (G.pairing_eq_energy_greenOp hG g hg).symm
  calc
    greenBilinear G hG f g ^ 2 = (pairing u f) ^ 2 := by rw [hpair]
    _ ≤ greenBilinear G hG f f * greenBilinear G hG g g := by
      calc
        _ ≤ greenBilinear G hG f f * G.energy u := hdir'
        _ = greenBilinear G hG f f * greenBilinear G hG g g := by
          rw [henergy, hgreenEnergy]

/-- Cauchy--Schwarz turns separate Green-energy bounds for two zero-sum
sources into an absolute covariance bound. -/
theorem torusGreenBilinear_abs_le_of_quadratic_bounds {n : ℕ} [NeZero n]
    (hn : 2 < n) (hG : (torusGraph n hn).Connected)
    (f g : TorusVertex n → ℝ) (hf : ∑ x, f x = 0) (hg : ∑ x, g x = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hQf : greenBilinear (torusGraph n hn) hG f f ≤ K)
    (hQg : greenBilinear (torusGraph n hn) hG g g ≤ K) :
    |greenBilinear (torusGraph n hn) hG f g| ≤ K := by
  have hQf0 := (torusGraph n hn).pairing_greenOp_nonneg hG f hf
  have hQg0 := (torusGraph n hn).pairing_greenOp_nonneg hG g hg
  have hprod : greenBilinear (torusGraph n hn) hG f f *
      greenBilinear (torusGraph n hn) hG g g ≤ K ^ 2 := by
    calc
      _ ≤ K * greenBilinear (torusGraph n hn) hG g g :=
        mul_le_mul_of_nonneg_right hQf hQg0
      _ ≤ K * K := mul_le_mul_of_nonneg_left hQg hK
      _ = K ^ 2 := by ring
  have hcs := torusGreenBilinear_cauchy_sq hn hG f g hf hg
  exact abs_le_of_sq_le_sq (hcs.trans hprod) hK

/-- Parallel horizontal dipoles with the same displacement have covariance
bounded in absolute value by the same `82 log(d+1)` estimate as their
individual energies. -/
theorem torusGreenBilinear_horizontal_dipole_covariance_abs_bound
    {n : ℕ} [NeZero n] (hn : 2 < n) (hG : (torusGraph n hn).Connected)
    (p q : TorusVertex n) (m : ℕ) (hmn : m ≤ n) :
    |greenBilinear (torusGraph n hn) hG
      (dipole p (p + ((m : ZMod n), 0)))
      (dipole q (q + ((m : ZMod n), 0)))| ≤
      82 * Real.log (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ) := by
  let f := dipole p (p + ((m : ZMod n), 0))
  let g := dipole q (q + ((m : ZMod n), 0))
  let K := 82 * Real.log (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ)
  have hf : ∑ x, f x = 0 := by dsimp [f]; exact sum_dipole_eq_zero _ _
  have hg : ∑ x, g x = 0 := by dsimp [g]; exact sum_dipole_eq_zero _ _
  have hqf := torusGreenBilinear_horizontal_dipole_log_upper_bound
    hn hG p m hmn
  have hqg := torusGreenBilinear_horizontal_dipole_log_upper_bound
    hn hG q m hmn
  have hqf' : greenBilinear (torusGraph n hn) hG f f ≤ K := by
    simpa [f, K] using hqf
  have hqg' : greenBilinear (torusGraph n hn) hG g g ≤ K := by
    simpa [g, K] using hqg
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have habs : |greenBilinear (torusGraph n hn) hG f g| ≤ K :=
    torusGreenBilinear_abs_le_of_quadratic_bounds hn hG f g hf hg K hK
      hqf' hqg'
  simpa [f, g, K] using habs

/-- The quadratic form of the difference of two parallel horizontal dipoles
of the same length is bounded by `328 log(d+1)`. This controls the two-row
source `∂₁F_y`. -/
theorem torusGreenBilinear_horizontal_dipole_difference_log_upper_bound
    {n : ℕ} [NeZero n] (hn : 2 < n) (hG : (torusGraph n hn).Connected)
    (p q : TorusVertex n) (m : ℕ) (hmn : m ≤ n) :
    greenBilinear (torusGraph n hn) hG
      (dipole p (p + ((m : ZMod n), 0)) -
        dipole q (q + ((m : ZMod n), 0)))
      (dipole p (p + ((m : ZMod n), 0)) -
        dipole q (q + ((m : ZMod n), 0))) ≤
      328 * Real.log (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ) := by
  let f := dipole p (p + ((m : ZMod n), 0))
  let g := dipole q (q + ((m : ZMod n), 0))
  let K := 82 * Real.log (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ)
  have hf : ∑ x, f x = 0 := by dsimp [f]; exact sum_dipole_eq_zero _ _
  have hg : ∑ x, g x = 0 := by dsimp [g]; exact sum_dipole_eq_zero _ _
  have hqf := torusGreenBilinear_horizontal_dipole_log_upper_bound
    hn hG p m hmn
  have hqg := torusGreenBilinear_horizontal_dipole_log_upper_bound
    hn hG q m hmn
  have hqf' : greenBilinear (torusGraph n hn) hG f f ≤ K := by
    simpa [f, K] using hqf
  have hqg' : greenBilinear (torusGraph n hn) hG g g ≤ K := by
    simpa [g, K] using hqg
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcov := torusGreenBilinear_abs_le_of_quadratic_bounds
    hn hG f g hf hg K hK hqf' hqg'
  have hcovlo : -K ≤ greenBilinear (torusGraph n hn) hG f g :=
    (abs_le.mp hcov).1
  have hsymm := greenBilinear_symm (torusGraph n hn) hG f g
  have hexpand := greenBilinear_sub_self (torusGraph n hn) hG f g
  have hbound : greenBilinear (torusGraph n hn) hG (f - g) (f - g) ≤
      4 * K := by
    rw [hexpand, hsymm]
    nlinarith only [hsymm, hqf', hqg', hcovlo]
  calc
    _ = greenBilinear (torusGraph n hn) hG (f - g) (f - g) := by
      simp [f, g]
    _ ≤ 4 * K := hbound
    _ = 328 * Real.log
        (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ) := by
      dsimp [K]
      ring

/-- Replacing a cyclic displacement by its centered representative can only
decrease the logarithmic bound. -/
theorem torusCyclicAxisDistance_log_le {n m : ℕ} :
    Real.log (((torusCyclicAxisDistance n m) + 1 : ℕ) : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) := by
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right (Nat.min_le_left m (n - m)) 1

/-- At displacement `2N`, the cyclic Green logarithm is at most twice the
logarithm of `N+1`. -/
theorem torusCyclicAxisDistance_two_mul_log_le (L N : ℕ) :
    Real.log (((torusCyclicAxisDistance (2 * L) (2 * N)) + 1 : ℕ) : ℝ) ≤
      2 * Real.log ((N + 1 : ℕ) : ℝ) := by
  have hdist : torusCyclicAxisDistance (2 * L) (2 * N) ≤ 2 * N :=
    Nat.min_le_left _ _
  have hreal :
      (((torusCyclicAxisDistance (2 * L) (2 * N) + 1 : ℕ) : ℕ) : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) ^ 2 := by
    have hdistR :
        (torusCyclicAxisDistance (2 * L) (2 * N) : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast hdist
    push_cast
    nlinarith only [sq_nonneg (N : ℝ), hdistR]
  calc
    _ ≤ Real.log (((N + 1 : ℕ) : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hreal
    _ = 2 * Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [Real.log_pow]
      norm_num

/-- The reflected endpoint span `2N` contributes at most
`656 log(N+1)` to a two-row horizontal dipole difference. -/
theorem torusC64_reflected_row_dipole_energy_upper_bound (L N : ℕ)
    [NeZero (2 * L)]
    (hside : 2 < 2 * L) (hG : (torusGraph (2 * L) hside).Connected)
    (hN : N ≤ L) (p q : TorusVertex (2 * L)) :
    greenBilinear (torusGraph (2 * L) hside) hG
      (dipole p (p + (((2 * N : ℕ) : ZMod (2 * L)), 0)) -
        dipole q (q + (((2 * N : ℕ) : ZMod (2 * L)), 0)))
      (dipole p (p + (((2 * N : ℕ) : ZMod (2 * L)), 0)) -
        dipole q (q + (((2 * N : ℕ) : ZMod (2 * L)), 0))) ≤
      656 * Real.log ((N + 1 : ℕ) : ℝ) := by
  have hdisp : 2 * N ≤ 2 * L := Nat.mul_le_mul_left 2 hN
  have hraw := torusGreenBilinear_horizontal_dipole_difference_log_upper_bound
    hside hG p q (2 * N) hdisp
  have hlog := torusCyclicAxisDistance_two_mul_log_le L N
  have hraw' : _ ≤ 328 * Real.log
      (((torusCyclicAxisDistance (2 * L) (2 * N)) + 1 : ℕ) : ℝ) := hraw
  have hlog' : 328 * Real.log
      (((torusCyclicAxisDistance (2 * L) (2 * N)) + 1 : ℕ) : ℝ) ≤
      656 * Real.log ((N + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ 328 * (2 * Real.log ((N + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ = _ := by ring
  exact hraw'.trans hlog'

/-- The periodic indicator of the reflected horizontal strip. -/
def torusC64StripIndicator (L a : ℕ) [NeZero (2 * L)]
    (x : ZMod (2 * L)) : ℝ :=
  if a ≤ x.val ∧ x.val < 2 * L - a then 1 else 0

/-- A backward difference of the strip indicator is the corrected endpoint
dipole, with endpoints `a` and `2L-a`. -/
theorem torusC64StripIndicator_backward_difference (L a : ℕ)
    [NeZero (2 * L)] (hL : 1 < L) (ha : a < L) (x : ZMod (2 * L)) :
    torusC64StripIndicator L a x - torusC64StripIndicator L a (x - 1) =
      dipole (a : ZMod (2 * L)) ((2 * L - a : ℕ) : ZMod (2 * L)) x := by
  have hn : 2 < 2 * L := by omega
  have haPos : 0 < 2 * L := by omega
  have haLt : a < 2 * L := by omega
  have hq : a < 2 * L - a := by omega
  have hvalOne : ((1 : ZMod (2 * L)).val) = 1 := by
    simpa using (ZMod.val_natCast_of_lt (n := 2 * L) (a := 1) (by omega))
  by_cases h0 : a = 0
  · subst a
    have hI : torusC64StripIndicator L 0 x = 1 := by
      simp [torusC64StripIndicator, x.val_lt]
    have hI' : torusC64StripIndicator L 0 (x - 1) = 1 := by
      simp [torusC64StripIndicator, (x - 1).val_lt]
    simp [hI, hI', dipole]
  · have haPos' : 0 < a := Nat.pos_of_ne_zero h0
    have hqLt : 2 * L - a < 2 * L := by omega
    have hvalA : ((a : ZMod (2 * L)).val) = a := ZMod.val_natCast_of_lt haLt
    have hvalQ : (((2 * L - a : ℕ) : ZMod (2 * L)).val) = 2 * L - a :=
      ZMod.val_natCast_of_lt hqLt
    have honeNe : (1 : ZMod (2 * L)) ≠ 0 := by
      intro h
      have hh := congrArg ZMod.val h
      rw [hvalOne] at hh
      simp at hh
    have hneNeg : (-1 : ZMod (2 * L)) ≠ 0 := by
      intro h
      apply honeNe
      have hh := congrArg Neg.neg h
      simpa using hh
    have hnegOne : (-1 : ZMod (2 * L)).val = 2 * L - 1 := by
      rw [show (-1 : ZMod (2 * L)) = -(1 : ZMod (2 * L)) by norm_num,
        ZMod.neg_val, ite_eq_right honeNe, hvalOne]
    by_cases hx0 : x = 0
    · have hxv : x.val = 0 := by simp [hx0]
      have hprev : (x - 1).val = 2 * L - 1 := by
        rw [show x - 1 = -1 by simp [hx0], hnegOne]
      have hcurr : torusC64StripIndicator L a x = 0 := by
        simp [torusC64StripIndicator, hxv]
        omega
      have hleft : torusC64StripIndicator L a (x - 1) = 0 := by
        have hlow : a ≤ 2 * L - 1 := by omega
        have hhigh : ¬ 2 * L - 1 < 2 * L - a := by omega
        simp [torusC64StripIndicator, hprev, hlow, hhigh]
      have hneA : x ≠ (a : ZMod (2 * L)) := by
        intro hh
        have hh' := congrArg ZMod.val hh
        rw [hvalA] at hh'
        omega
      have hneQ : x ≠ ((2 * L - a : ℕ) : ZMod (2 * L)) := by
        intro hh
        have hh' := congrArg ZMod.val hh
        rw [hvalQ] at hh'
        omega
      rw [hcurr, hleft]
      simp [dipole, hneA, hneQ]
    · have hxpos : 0 < x.val := by
        by_contra hpos
        have hxv : x.val = (0 : ZMod (2 * L)).val := by simpa using (show x.val = 0 by omega)
        exact hx0 (ZMod.val_injective (2 * L) hxv)
      have hprev : (x - 1).val = x.val - 1 := by
        rw [ZMod.val_sub (by rw [hvalOne]; omega), hvalOne]
      have hxEqA : x = (a : ZMod (2 * L)) ↔ x.val = a := by
        constructor
        · intro h
          rw [h, hvalA]
        · intro h
          exact ZMod.val_injective (2 * L) (h.trans hvalA.symm)
      have hxEqQ : x = ((2 * L - a : ℕ) : ZMod (2 * L)) ↔
          x.val = 2 * L - a := by
        constructor
        · intro h
          rw [h, hvalQ]
        · intro h
          exact ZMod.val_injective (2 * L) (h.trans hvalQ.symm)
      by_cases hxa : x.val = a
      · have hxA : x = (a : ZMod (2 * L)) := hxEqA.mpr hxa
        have hcastNe : (a : ZMod (2 * L)) ≠
            ((2 * L - a : ℕ) : ZMod (2 * L)) := by
          intro heq
          have hh := congrArg ZMod.val heq
          rw [hvalA, hvalQ] at hh
          omega
        have hcurr : torusC64StripIndicator L a x = 1 := by
          simp [torusC64StripIndicator, hxa, hq]
        have hleft : torusC64StripIndicator L a (x - 1) = 0 := by
          simp [torusC64StripIndicator, hprev, hxa]
          omega
        have hneQ : x ≠ ((2 * L - a : ℕ) : ZMod (2 * L)) := by
          intro heq
          have hh := (hxEqQ.mp heq)
          omega
        rw [hcurr, hleft]
        simp [dipole, hxA, hcastNe]
      · by_cases hxq : x.val = 2 * L - a
        · have hxQ : x = ((2 * L - a : ℕ) : ZMod (2 * L)) := hxEqQ.mpr hxq
          have hcastNe : (a : ZMod (2 * L)) ≠
              ((2 * L - a : ℕ) : ZMod (2 * L)) := by
            intro heq
            have hh := congrArg ZMod.val heq
            rw [hvalA, hvalQ] at hh
            omega
          have hcurr : torusC64StripIndicator L a x = 0 := by
            simp [torusC64StripIndicator, hxq]
          have hleft : torusC64StripIndicator L a (x - 1) = 1 := by
            simp [torusC64StripIndicator, hprev, hxq]
            omega
          have hneA : x ≠ (a : ZMod (2 * L)) := by
            intro heq
            have hh := (hxEqA.mp heq)
            omega
          rw [hcurr, hleft]
          simp [dipole, hxQ, hcastNe.symm]
        · by_cases hbelow : x.val < a
          · have hcurr : torusC64StripIndicator L a x = 0 := by
              simp [torusC64StripIndicator, hbelow]
            have hleft : torusC64StripIndicator L a (x - 1) = 0 := by
              simp [torusC64StripIndicator, hprev]
              omega
            have hneA : x ≠ (a : ZMod (2 * L)) := by
              intro heq
              have hh := (hxEqA.mp heq)
              omega
            have hneQ : x ≠ ((2 * L - a : ℕ) : ZMod (2 * L)) := by
              intro heq
              have hh := (hxEqQ.mp heq)
              omega
            rw [hcurr, hleft]
            simp [dipole, hneA, hneQ]
          · by_cases habove : 2 * L - a < x.val
            · have hcurr : torusC64StripIndicator L a x = 0 := by
                simp [torusC64StripIndicator]
                omega
              have hleft : torusC64StripIndicator L a (x - 1) = 0 := by
                simp [torusC64StripIndicator, hprev]
                omega
              have hneA : x ≠ (a : ZMod (2 * L)) := by
                intro heq
                have hh := (hxEqA.mp heq)
                omega
              have hneQ : x ≠ ((2 * L - a : ℕ) : ZMod (2 * L)) := by
                intro heq
                have hh := (hxEqQ.mp heq)
                omega
              rw [hcurr, hleft]
              simp [dipole, hneA, hneQ]
            · have hinside : a < x.val ∧ x.val < 2 * L - a := by omega
              have hcurr : torusC64StripIndicator L a x = 1 := by
                have hlow : a ≤ x.val := Nat.le_of_lt hinside.1
                simp [torusC64StripIndicator, hlow, hinside.2]
              have hleft : torusC64StripIndicator L a (x - 1) = 1 := by
                have hlow : a ≤ x.val - 1 := by omega
                have hhigh : x.val - 1 < 2 * L - a := by omega
                simp [torusC64StripIndicator, hprev, hlow, hhigh]
              have hneA : x ≠ (a : ZMod (2 * L)) := by
                intro heq
                have hh := (hxEqA.mp heq)
                omega
              have hneQ : x ≠ ((2 * L - a : ℕ) : ZMod (2 * L)) := by
                intro heq
                have hh := (hxEqQ.mp heq)
                omega
              rw [hcurr, hleft]
              simp [dipole, hneA, hneQ]

/-- The reflected two-strip potential `F_y` from KP (6.14). -/
def torusC64ReflectedPotential (L y₀ y₁ : ℕ) [NeZero (2 * L)]
    (z : TorusVertex (2 * L)) : ℝ :=
  torusC64StripIndicator L y₀ z.1 *
      (if z.2 = (y₁ : ZMod (2 * L)) then 1 else 0) -
    torusC64StripIndicator L y₀ z.1 *
      (if z.2 = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) then 1 else 0)

/-- The backward first-coordinate torus difference used in KP (6.11). -/
def torusC64Backward1 {L : ℕ} [NeZero (2 * L)]
    (F : TorusVertex (2 * L) → ℝ) (z : TorusVertex (2 * L)) : ℝ :=
  F z - F (z - (1, 0))

/-- The corrected endpoint formula for `∂₁F_y`: both horizontal dipoles have
length `2(L-y₀)`. -/
theorem torusC64_backward1_reflectedPotential_eq_dipoles (L y₀ y₁ : ℕ)
    [NeZero (2 * L)] (hL : 1 < L) (hy₀ : y₀ < L)
    (z : TorusVertex (2 * L)) :
    torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁) z =
      (dipole ((y₀ : ZMod (2 * L)), (y₁ : ZMod (2 * L)))
        (((2 * L - y₀ : ℕ) : ZMod (2 * L)), (y₁ : ZMod (2 * L))) -
    dipole ((y₀ : ZMod (2 * L)), ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)))
        (((2 * L - y₀ : ℕ) : ZMod (2 * L)),
          ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)))) z := by
  rcases z with ⟨x, y⟩
  have hstrip := torusC64StripIndicator_backward_difference L y₀ hL hy₀ x
  have hrow (a b r : ZMod (2 * L)) :
      dipole a b x * (if y = r then 1 else 0) =
        dipole (a, r) (b, r) (x, y) := by
    by_cases hyr : y = r <;> by_cases hxa : x = a <;>
      by_cases hxb : x = b <;> simp [dipole, hyr, hxa, hxb]
  simp only [torusC64Backward1]
  have hshift : (x, y) - (1, 0) = (x - 1, y) := by ext <;> simp
  rw [hshift]
  unfold torusC64ReflectedPotential
  calc
    _ = (torusC64StripIndicator L y₀ x -
          torusC64StripIndicator L y₀ (x - 1)) *
        (if y = (y₁ : ZMod (2 * L)) then 1 else 0) -
        (torusC64StripIndicator L y₀ x -
          torusC64StripIndicator L y₀ (x - 1)) *
        (if y = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) then 1 else 0) := by
          ring
    _ = dipole (y₀ : ZMod (2 * L)) ((2 * L - y₀ : ℕ) : ZMod (2 * L)) x *
          (if y = (y₁ : ZMod (2 * L)) then 1 else 0) -
        dipole (y₀ : ZMod (2 * L)) ((2 * L - y₀ : ℕ) : ZMod (2 * L)) x *
          (if y = ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)) then 1 else 0) := by
            rw [hstrip]
    _ = _ := by
      rw [hrow (y₀ : ZMod (2 * L)) ((2 * L - y₀ : ℕ) : ZMod (2 * L))
          (y₁ : ZMod (2 * L)),
        hrow (y₀ : ZMod (2 * L)) ((2 * L - y₀ : ℕ) : ZMod (2 * L))
          ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L))]
      rfl

/-- The quadratic form of `∂₁F_y` is at most `656 log(N+1)`, including
`N=1`. The endpoint is `2N`, not `2(N-1)`. -/
theorem torusC64_reflectedPotential_backward1_energy_log_upper_bound
    (L y₀ y₁ : ℕ) [NeZero (2 * L)] (hside : 2 < 2 * L)
    (hG : (torusGraph (2 * L) hside).Connected)
    (hy₀ : y₀ < L) :
    greenBilinear (torusGraph (2 * L) hside) hG
      (torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁))
      (torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁)) ≤
      656 * Real.log (((L - y₀) + 1 : ℕ) : ℝ) := by
  let N := L - y₀
  let p : TorusVertex (2 * L) :=
    ((y₀ : ZMod (2 * L)), (y₁ : ZMod (2 * L)))
  let q : TorusVertex (2 * L) :=
    ((y₀ : ZMod (2 * L)), ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)))
  have hN : N ≤ L := by dsimp [N]; omega
  have hdisp : y₀ + 2 * N = 2 * L - y₀ := by dsimp [N]; omega
  have hpos : p + (((2 * N : ℕ) : ZMod (2 * L)), 0) =
      (((2 * L - y₀ : ℕ) : ZMod (2 * L)), (y₁ : ZMod (2 * L))) := by
    dsimp [p]
    ext
    · change ((y₀ : ℕ) : ZMod (2 * L)) +
        ((2 * N : ℕ) : ZMod (2 * L)) =
        ((2 * L - y₀ : ℕ) : ZMod (2 * L))
      rw [← Nat.cast_add]
      exact congrArg (fun k : ℕ => (k : ZMod (2 * L))) hdisp
    · simp
  have hneg : q + (((2 * N : ℕ) : ZMod (2 * L)), 0) =
      (((2 * L - y₀ : ℕ) : ZMod (2 * L)),
        ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L))) := by
    dsimp [q]
    ext
    · change ((y₀ : ℕ) : ZMod (2 * L)) +
        ((2 * N : ℕ) : ZMod (2 * L)) =
        ((2 * L - y₀ : ℕ) : ZMod (2 * L))
      rw [← Nat.cast_add]
      exact congrArg (fun k : ℕ => (k : ZMod (2 * L))) hdisp
    · simp
  have hdecomp :
      torusC64Backward1 (torusC64ReflectedPotential L y₀ y₁) =
        dipole p (p + (((2 * N : ℕ) : ZMod (2 * L)), 0)) -
          dipole q (q + (((2 * N : ℕ) : ZMod (2 * L)), 0)) := by
    funext z
    rw [torusC64_backward1_reflectedPotential_eq_dipoles
      L y₀ y₁ (by omega) hy₀ z]
    rw [← hpos, ← hneg]
  rw [hdecomp]
  simpa [N] using torusC64_reflected_row_dipole_energy_upper_bound
    L (L - y₀) hside hG (Nat.sub_le L y₀) p q

/-- A covariance between horizontal dipoles of spans `N` and `2N` is at
most `164 log(N+1)` in absolute value. -/
theorem torusC64_mixed_span_covariance_abs_bound (L N : ℕ)
    [NeZero (2 * L)] (hside : 2 < 2 * L)
    (hG : (torusGraph (2 * L) hside).Connected) (hN : N ≤ L)
    (p q : TorusVertex (2 * L)) :
    |greenBilinear (torusGraph (2 * L) hside) hG
      (dipole p (p + (((N : ℕ) : ZMod (2 * L)), 0)))
      (dipole q (q + (((2 * N : ℕ) : ZMod (2 * L)), 0)))| ≤
      164 * Real.log ((N + 1 : ℕ) : ℝ) := by
  let f := dipole p (p + (((N : ℕ) : ZMod (2 * L)), 0))
  let g := dipole q (q + (((2 * N : ℕ) : ZMod (2 * L)), 0))
  let K := 164 * Real.log ((N + 1 : ℕ) : ℝ)
  have hf : ∑ x, f x = 0 := by dsimp [f]; exact sum_dipole_eq_zero _ _
  have hg : ∑ x, g x = 0 := by dsimp [g]; exact sum_dipole_eq_zero _ _
  have hlog0 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.succ_pos N)
  have hqf := torusGreenBilinear_horizontal_dipole_log_upper_bound
    hside hG p N (by omega)
  have hqg := torusGreenBilinear_horizontal_dipole_log_upper_bound
    hside hG q (2 * N) (by omega)
  have hlogf := torusCyclicAxisDistance_log_le (n := 2 * L) (m := N)
  have hlogg := torusCyclicAxisDistance_two_mul_log_le L N
  have hqf' : greenBilinear (torusGraph (2 * L) hside) hG f f ≤ K := by
    calc
      _ ≤ 82 * Real.log
          (((torusCyclicAxisDistance (2 * L) N) + 1 : ℕ) : ℝ) := by
        simpa [f] using hqf
      _ ≤ 82 * Real.log ((N + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogf (by norm_num)
      _ ≤ K := by dsimp [K]; nlinarith only [hlog0]
  have hqg' : greenBilinear (torusGraph (2 * L) hside) hG g g ≤ K := by
    calc
      _ ≤ 82 * Real.log
          (((torusCyclicAxisDistance (2 * L) (2 * N)) + 1 : ℕ) : ℝ) := by
        simpa [g] using hqg
      _ ≤ 82 * (2 * Real.log ((N + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogg (by norm_num)
      _ ≤ K := by dsimp [K]; nlinarith only
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcov := torusGreenBilinear_abs_le_of_quadratic_bounds
    hside hG f g hf hg K hK hqf' hqg'
  simpa [f, g, K] using hcov

/-- The corrected C6.4 cross term, with short endpoint `N` and reflected
endpoints `2N`, is bounded by `328 log(N+1)`. -/
theorem torusC64_corrected_cross_term_abs_bound (L y₀ y₁ : ℕ)
    [NeZero (2 * L)] (hside : 2 < 2 * L)
    (hG : (torusGraph (2 * L) hside).Connected) (hy₀ : y₀ < L) :
    let N := L - y₀
    let p : TorusVertex (2 * L) :=
      ((y₀ : ZMod (2 * L)), (y₁ : ZMod (2 * L)))
    let q : TorusVertex (2 * L) :=
      ((y₀ : ZMod (2 * L)), ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)))
    |greenBilinear (torusGraph (2 * L) hside) hG
      (dipole p (p + (((N : ℕ) : ZMod (2 * L)), 0)))
      ((dipole p (p + (((2 * N : ℕ) : ZMod (2 * L)), 0))) -
        (dipole q (q + (((2 * N : ℕ) : ZMod (2 * L)), 0))))| ≤
      328 * Real.log ((N + 1 : ℕ) : ℝ) := by
  dsimp
  let N := L - y₀
  let p : TorusVertex (2 * L) :=
    ((y₀ : ZMod (2 * L)), (y₁ : ZMod (2 * L)))
  let q : TorusVertex (2 * L) :=
    ((y₀ : ZMod (2 * L)), ((2 * L - 2 - y₁ : ℕ) : ZMod (2 * L)))
  have hN : N ≤ L := by dsimp [N]; omega
  have hA := torusC64_mixed_span_covariance_abs_bound L N
    hside hG hN p p
  have hB := torusC64_mixed_span_covariance_abs_bound L N
    hside hG hN p q
  rw [greenBilinear_sub_right]
  have hAl := by
    simpa [N, p, q] using (abs_le.mp hA).1
  have hAu := by
    simpa [N, p, q] using (abs_le.mp hA).2
  have hBl := by
    simpa [N, p, q] using (abs_le.mp hB).1
  have hBu := by
    simpa [N, p, q] using (abs_le.mp hB).2
  push_cast
  simp only [add_zero] at hAl hAu hBl hBu ⊢
  apply abs_le.mpr
  constructor <;> nlinarith

end

end FroehlichSpencer.BKT.Lattice2D

end
