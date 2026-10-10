/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.JensenD
public import FroehlichSpencer.FS82.XY.SpinLaw

/-!
# the assembly of FS82 (4.38)–(4.40) for every `d ≥ 3`, from an explicit interface

The theorems of this file take two hypotheses.

Both are discharged elsewhere: the interface in
`XY/SpinTheoremD.lean` (`branchJensenInterface_holds`), the residual bound in `XY/FanFlowD.lean`.

The unconditional root is `fs82_xyD_spinCorrelation_root` in `XY/SpinTheoremD.lean`.

* `BranchJensenInterface hd β x y φ τ a`: the output of the Poisson, expansion and Gaussian layers
  (FS82 (4.13)–(4.33) and Jensen's inequality on each branch of the expansion).

It says: if every
  admissible family of currents has phase representatives with Jensen budget at most `E`, then
  `exp(−‖ε‖²/(2β) − E) ≤ Re ⟨e^{i(θ_x − θ_y)}⟩`.

From these, with the Jensen/packing step `DualD.phaseRepresentatives` of `XY/JensenD.lean`:

* `endpointExpectation_lower_of_interface`: the finite-volume form of (4.38),
  `exp(−(1/(2β) + jensenRateD d a) ‖ε‖² − 5π² #cells e^{−a m}) ≤ Re ⟨e^{i(θ_x − θ_y)}⟩`;
* `cube_spinCorrelation_lower_of_interface`: on a cube, for `a ≥ d`,
  `exp(−((1/(2β) + jensenRateD d a) C + 5π² 4^d e^{−a})) ≤ ⟨cos(θ_x − θ_y)⟩`;
* `cube_spinCorrelation_root_of_interface`: with a rate `a = κβ − b`, the bound `exp(−C'/β)` of
  (4.40) with an explicit `C'`, uniformly in the cube and the sites.

Nothing in this file asserts that the interface holds; `XY/SpinTheoremD.lean` proves it.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Moment.SourceJensen

variable {d : ℕ} {B : Box d}

/-! ## The interface -/

/-- A family of currents to which the Jensen/packing step applies: co-closed, with pairwise
disjoint supports, each of extent at most its number of cells minus one, and with amplitudes
under the envelope of rate `a`. -/
structure AdmissibleFamily (hd : 3 ≤ d) (a : ℝ) {ι : Type} (J : ι → DualDForm B (d - 2) → ℤ)
    (z : ι → ℝ) : Prop where
  coClosed : ∀ i, currentVector (J i) ∈ coClosed (dualDExactOneComplex hd B)
  disjoint : ∀ i j, i ≠ j → ∀ e, J i e ≠ 0 → J j e = 0
  extent : ∀ i e f, J i e ≠ 0 → J i f ≠ 0 → ∀ k,
    cellBase e.1 k + 1 ≤ cellBase f.1 k + currentLength (J i)
  nonneg : ∀ i, 0 ≤ z i
  envelope : ∀ i, z i ≤ Real.exp (-(a * (currentEnergy (J i) + (currentLength (J i) : ℝ))))

/-- **The interface with the Poisson, expansion and Gaussian layers.** If every admissible family
has phase representatives of the phases `2π ⟨J_i, τ⟩` with Jensen budget at most `E`, then the
endpoint character is at least `exp(−‖ε‖²/(2β) − E)`. -/
def BranchJensenInterface (hd : 3 ≤ d) (β : ℝ) (x y : XYSites B)
    (φ : EuclideanSpace ℝ (DualDForm B (d - 1))) (τ : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (a : ℝ) : Prop :=
  ∀ E : ℝ,
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → DualDForm B (d - 2) → ℤ) (z : ι → ℝ),
      AdmissibleFamily hd a J z →
      ∃ θ' : ι → ℝ,
        (∀ i, ∃ n : ℤ, 2 * Real.pi * inner ℝ (currentVector (J i)) τ + θ' i =
          2 * Real.pi * (n : ℝ)) ∧
        ∑ i, sourceJensenGamma (z i) * θ' i ^ 2 ≤ E) →
    Real.exp (-((∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2) / (2 * β)) - E) ≤
      (xyEndpointCharacterExpectation β x y).re

/-! ## (4.38) -/

/-- **FS82 (4.38) in finite volume for every `d ≥ 3`, from the interface.** -/
theorem endpointExpectation_lower_of_interface (hd : 3 ≤ d) {β a : ℝ} (hβ : 0 < β)
    (ha1 : 1 ≤ a) (m : ℕ) (hm : ∀ k, m ≤ B k) (x y : XYSites B)
    (φ : EuclideanSpace ℝ (DualDForm B (d - 1))) (hφ : ∀ p, ∃ n : ℤ, φ p = (n : ℝ))
    (τ : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (hτ : (dualDExactOneComplex hd B).d₁ τ = φ - loopFieldResidual (dualDExactOneComplex hd B) φ)
    (hI : BranchJensenInterface hd β x y φ τ a) :
    Real.exp (-((1 / (2 * β) + jensenRateD d a) *
          (∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2)) -
        5 * Real.pi ^ 2 * (Fintype.card (DualDForm B (d - 2)) : ℝ) *
          Real.exp (-(a * (m : ℝ)))) ≤
      (xyEndpointCharacterExpectation β x y).re := by
  have h := hI (jensenRateD d a * (∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2) +
      5 * Real.pi ^ 2 * (Fintype.card (DualDForm B (d - 2)) : ℝ) * Real.exp (-(a * (m : ℝ))))
    (fun ι _ _ J z hadm =>
      phaseRepresentatives hd m hm φ hφ τ hτ J z ha1 hadm.coClosed hadm.disjoint hadm.extent
        hadm.nonneg hadm.envelope)
  refine le_trans (le_of_eq ?_) h
  congr 1
  have hβ' := hβ.ne'
  field_simp
  ring

/-! ## Cubes -/

/-- A box with all sides zero has no dual cell of degree less than `d`. -/
theorem dualDForm_isEmpty_of_sides_zero (hB : ∀ k, B k = 0) {n : ℕ} (hn : n < d) :
    IsEmpty (DualDForm B n) := by
  refine ⟨fun c => ?_⟩
  have hall : ∀ i, (c.1 i).isRight = true := by
    intro i
    cases hci : c.1 i with
    | inl v =>
      have hlt : v.val < B i := v.isLt
      have h0 := hB i
      omega
    | inr u => rfl
  have hdeg : dualCellDegree c.1 = d := by
    unfold dualCellDegree dualCellAxes
    rw [Finset.filter_true_of_mem fun i _ => hall i, Finset.card_univ, Fintype.card_fin]
  have := c.2
  omega

/-- A box with sides at most `N` has at most `2 ^ d (N + 1) ^ d` dual cells of a given degree. -/
theorem card_dualDForm_le (N : ℕ) (hB : ∀ k, B k ≤ N) (n : ℕ) :
    Fintype.card (DualDForm B n) ≤ 2 ^ d * (N + 1) ^ d := by
  classical
  have h := card_window_le (fun e : DualDForm B n => e.1) Subtype.val_injective
    (fun _ => 0) 0 N
  have hall : (Finset.univ.filter fun e : DualDForm B n =>
      ∀ k, (0 : ℕ) ≤ cellBase e.1 k + 0 ∧ cellBase e.1 k ≤ 0 + N) = Finset.univ := by
    refine Finset.filter_true_of_mem fun e _ k => ⟨Nat.zero_le _, ?_⟩
    have := cellBase_le e.1 k
    have := hB k
    omega
  rw [← Finset.card_univ]
  calc (Finset.univ : Finset (DualDForm B n)).card
      = (Finset.univ.filter fun e : DualDForm B n =>
          ∀ k, (0 : ℕ) ≤ cellBase e.1 k + 0 ∧ cellBase e.1 k ≤ 0 + N).card := by rw [hall]
    _ ≤ 2 ^ d * (0 + N + 1) ^ d := by convert h using 2
    _ = 2 ^ d * (N + 1) ^ d := by rw [Nat.zero_add]

/-- `(N + 1)^d e^{−aN} ≤ 2^d e^{−a}` for `N ≥ 1` and `a ≥ d`. -/
theorem pow_mul_exp_le {a : ℝ} (ha : (d : ℝ) ≤ a) {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) + 1) ^ d * Real.exp (-(a * (N : ℝ))) ≤ (2 : ℝ) ^ d * Real.exp (-a) := by
  have h2N : ((N : ℝ) + 1) ≤ (2 : ℝ) ^ N := by
    have h := Nat.lt_two_pow_self (n := N)
    have h' : N + 1 ≤ 2 ^ N := h
    exact_mod_cast h'
  set x : ℝ := (2 : ℝ) ^ d * Real.exp (-a) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    have h2e : (2 : ℝ) ^ d ≤ Real.exp (d : ℝ) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      calc (2 : ℝ) ^ d ≤ (Real.exp 1) ^ d := pow_le_pow_left₀ (by norm_num) h2 d
        _ = Real.exp (d : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    calc x ≤ Real.exp (d : ℝ) * Real.exp (-a) :=
          mul_le_mul_of_nonneg_right h2e (Real.exp_pos _).le
      _ = Real.exp ((d : ℝ) - a) := by rw [← Real.exp_add]; ring_nf
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpow : ((N : ℝ) + 1) ^ d * Real.exp (-(a * (N : ℝ))) ≤ x ^ N := by
    have h1 : ((N : ℝ) + 1) ^ d ≤ ((2 : ℝ) ^ d) ^ N := by
      calc ((N : ℝ) + 1) ^ d ≤ ((2 : ℝ) ^ N) ^ d := pow_le_pow_left₀ (by positivity) h2N d
        _ = ((2 : ℝ) ^ d) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
    have h2 : Real.exp (-(a * (N : ℝ))) = (Real.exp (-a)) ^ N := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hx, mul_pow, h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  exact hpow.trans (pow_le_of_le_one hx0 hx1 (by omega))

/-- The long-current term on a cube is bounded uniformly in the side. -/
theorem cubeLongTerm_le (hd : 3 ≤ d) {a : ℝ} (ha : (d : ℝ) ≤ a) (N : ℕ) (hB : ∀ k, B k = N) :
    5 * Real.pi ^ 2 * (Fintype.card (DualDForm B (d - 2)) : ℝ) * Real.exp (-(a * (N : ℝ))) ≤
      5 * Real.pi ^ 2 * (4 : ℝ) ^ d * Real.exp (-a) := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · have hempty : IsEmpty (DualDForm B (d - 2)) :=
      dualDForm_isEmpty_of_sides_zero (fun k => (hB k).trans h0) (by omega)
    have hcard : Fintype.card (DualDForm B (d - 2)) = 0 := Fintype.card_eq_zero_iff.mpr hempty
    rw [hcard]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    positivity
  · have hcard : (Fintype.card (DualDForm B (d - 2)) : ℝ) ≤ (2 : ℝ) ^ d * ((N : ℝ) + 1) ^ d := by
      have h := card_dualDForm_le (B := B) N (fun k => (hB k).le) (d - 2)
      exact_mod_cast h
    have hpe := pow_mul_exp_le ha hpos
    have hexp0 : 0 ≤ Real.exp (-(a * (N : ℝ))) := (Real.exp_pos _).le
    have h4 : (4 : ℝ) ^ d = (2 : ℝ) ^ d * (2 : ℝ) ^ d := by
      rw [← mul_pow]
      norm_num
    calc 5 * Real.pi ^ 2 * (Fintype.card (DualDForm B (d - 2)) : ℝ) * Real.exp (-(a * (N : ℝ)))
        ≤ 5 * Real.pi ^ 2 * ((2 : ℝ) ^ d * ((N : ℝ) + 1) ^ d) * Real.exp (-(a * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity)) hexp0
      _ = 5 * Real.pi ^ 2 * (2 : ℝ) ^ d * (((N : ℝ) + 1) ^ d * Real.exp (-(a * (N : ℝ)))) := by
          ring
      _ ≤ 5 * Real.pi ^ 2 * (2 : ℝ) ^ d * ((2 : ℝ) ^ d * Real.exp (-a)) :=
          mul_le_mul_of_nonneg_left hpe (by positivity)
      _ = 5 * Real.pi ^ 2 * (4 : ℝ) ^ d * Real.exp (-a) := by rw [h4]; ring

/-- **The spin correlation on a cube, from the interface and a residual bound.** -/
theorem cube_spinCorrelation_lower_of_interface (hd : 3 ≤ d) {β a C : ℝ} (hβ : 0 < β)
    (ha : (d : ℝ) ≤ a) (N : ℕ) (hB : ∀ k, B k = N) (x y : XYSites B)
    (φ : EuclideanSpace ℝ (DualDForm B (d - 1))) (hφ : ∀ p, ∃ n : ℤ, φ p = (n : ℝ))
    (τ : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (hτ : (dualDExactOneComplex hd B).d₁ τ = φ - loopFieldResidual (dualDExactOneComplex hd B) φ)
    (hI : BranchJensenInterface hd β x y φ τ a)
    (hres : ∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2 ≤ C) :
    Real.exp (-((1 / (2 * β) + jensenRateD d a) * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d *
        Real.exp (-a))) ≤ xyEndpointCosExpectation β x y := by
  have hd1 : (1 : ℝ) ≤ a := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmain := endpointExpectation_lower_of_interface hd hβ hd1 N (fun k => (hB k).ge) x y
    φ hφ τ hτ hI
  rw [xyEndpointCosExpectation_eq_re_characterExpectation β hβ x y]
  refine le_trans (Real.exp_le_exp.mpr ?_) hmain
  have hlong := cubeLongTerm_le hd ha N hB
  have hcoef : 0 ≤ 1 / (2 * β) + jensenRateD d a := by
    have := jensenRateD_nonneg d a
    have : 0 ≤ 1 / (2 * β) := by positivity
    linarith
  have := mul_le_mul_of_nonneg_left hres hcoef
  linarith

/-! ## (4.40) -/

/-- The constant of the root, for a rate `a = κβ − b`, a residual bound `C` and dimension `d`. -/
noncomputable def rootConstantD (d : ℕ) (κ b C : ℝ) : ℝ :=
  C / 2 + (20 * (10 : ℝ) ^ d * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 * polyTail (3 * d) * Real.exp 1 * C +
    5 * Real.pi ^ 2 * (4 : ℝ) ^ d) * Real.exp b / κ

/-- `e^{−(κβ − b)} ≤ e^{b} / (κ β)`. -/
theorem exp_neg_rate_le {κ b β : ℝ} (hκ : 0 < κ) (hβ : 0 < β) :
    Real.exp (-(κ * β - b)) ≤ Real.exp b / (κ * β) := by
  have ht : 0 < κ * β := mul_pos hκ hβ
  have h1 : Real.exp (-(κ * β)) * (κ * β) ≤ 1 := by
    have h := Real.add_one_le_exp (κ * β)
    have hpos := Real.exp_pos (-(κ * β))
    calc Real.exp (-(κ * β)) * (κ * β) ≤ Real.exp (-(κ * β)) * Real.exp (κ * β) :=
          mul_le_mul_of_nonneg_left (by linarith) hpos.le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [le_div_iff₀ ht]
  have hsplit : Real.exp (-(κ * β - b)) = Real.exp b * Real.exp (-(κ * β)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, mul_assoc]
  calc Real.exp b * (Real.exp (-(κ * β)) * (κ * β)) ≤ Real.exp b * 1 :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp b := mul_one _

/-- **FS82 (4.40) in finite volume for every `d ≥ 3`, from the interface and a residual bound.**
If the envelope rate is `a = κβ − b ≥ d`, the residual energy is at most `C`, and the interface
holds at this rate, then `exp(−rootConstantD d κ b C / β) ≤ ⟨cos(θ_x − θ_y)⟩` on the cube, with a
constant that does not depend on the side, the sites or `β`. -/
theorem cube_spinCorrelation_root_of_interface (hd : 3 ≤ d) {β κ b C : ℝ} (hβ : 0 < β)
    (hκ : 0 < κ) (hC : 0 ≤ C) (ha : (d : ℝ) ≤ κ * β - b) (N : ℕ) (hB : ∀ k, B k = N)
    (x y : XYSites B)
    (φ : EuclideanSpace ℝ (DualDForm B (d - 1))) (hφ : ∀ p, ∃ n : ℤ, φ p = (n : ℝ))
    (τ : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (hτ : (dualDExactOneComplex hd B).d₁ τ = φ - loopFieldResidual (dualDExactOneComplex hd B) φ)
    (hI : BranchJensenInterface hd β x y φ τ (κ * β - b))
    (hres : ∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2 ≤ C) :
    Real.exp (-(rootConstantD d κ b C / β)) ≤ xyEndpointCosExpectation β x y := by
  set a := κ * β - b with ha_def
  have hd0 : 0 < d := by omega
  have ha1 : (1 : ℝ) ≤ a := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmain := cube_spinCorrelation_lower_of_interface hd hβ ha N hB x y φ hφ τ hτ hI hres
  refine le_trans (Real.exp_le_exp.mpr ?_) hmain
  set K : ℝ := 20 * (10 : ℝ) ^ d * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 * polyTail (3 * d) with hK
  have hK0 : 0 ≤ K := by
    have := polyTail_nonneg (3 * d)
    positivity
  set e := Real.exp (-a) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hrate : jensenRateD d a ≤ K * Real.exp 1 * e := by
    have h := jensenRateD_le hd0 ha1
    have hexp : Real.exp (1 - a) = Real.exp 1 * e := by
      rw [he, ← Real.exp_add, sub_eq_add_neg]
    rw [hexp] at h
    rw [hK]
    linarith
  have hebound : e ≤ Real.exp b / (κ * β) := exp_neg_rate_le hκ hβ
  have hcoef : 0 ≤ K * Real.exp 1 * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d := by positivity
  have hhalf : 1 / (2 * β) * C = C / 2 / β := by
    field_simp
  have htotal : (1 / (2 * β) + jensenRateD d a) * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d * e ≤
      rootConstantD d κ b C / β := by
    calc (1 / (2 * β) + jensenRateD d a) * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d * e
        = C / 2 / β + jensenRateD d a * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d * e := by
          rw [add_mul, hhalf]
      _ ≤ C / 2 / β + K * Real.exp 1 * e * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d * e := by
          have := mul_le_mul_of_nonneg_right hrate hC
          linarith
      _ = C / 2 / β + (K * Real.exp 1 * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d) * e := by ring
      _ ≤ C / 2 / β + (K * Real.exp 1 * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d) *
            (Real.exp b / (κ * β)) := by
          have := mul_le_mul_of_nonneg_left hebound hcoef
          linarith
      _ = rootConstantD d κ b C / β := by
          unfold rootConstantD
          rw [hK]
          field_simp
  linarith

end FroehlichSpencer.FS82.XY.DualD

end
