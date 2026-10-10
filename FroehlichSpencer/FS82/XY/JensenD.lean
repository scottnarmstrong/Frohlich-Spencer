/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.PhaseD
public import FroehlichSpencer.FS82.XY.PackingD

/-!
# the Jensen/packing step of FS82 (4.35)–(4.38) in every dimension `d ≥ 3`

Let `φ` be an integer-valued form of degree `d − 1` on the dual complex of a box `B` (the star of
an integer bond chain), `ε = loopFieldResidual φ` its residual, and `τ` a potential with
`d₁ τ = φ − ε`.

Let `J_i` be a finite family of co-closed integer currents on the dual cells of
degree `d − 2` with pairwise disjoint supports, each of extent at most its number of cells `L_i`
minus one (a connected support), and let the amplitudes obey the envelope
`z_i ≤ exp(−a (‖J_i‖² + L_i))` with `a ≥ 1`.

Then the phases `2π ⟨J_i, τ⟩` have representatives
`θ'_i` modulo `2π` with

`∑_i γ(z_i) θ'_i² ≤ jensenRateD d a · ‖ε‖² + 5π² · #cells · e^{−a m}`

for every `m` not larger than any side of the box.

The first term is the packing estimate for
the currents with fewer than `m` cells, which have local relative fillings; the second accounts
for the others, whose phases get representatives in `[−π, π]`.

The rate
`jensenRateD d a = polyPackingConstant d (10 ^ d) a (2π · 4 ^ d)` is at most a multiple of
`e^{1−a}`.

It does not depend on how the family `J_i` is produced.

* `cellBox`, `cellBox_card_le`: the window of cells around a cell of degree `d − 1`.
* `jensenRateD`, `jensenRateD_le`.
* `short_packing`, `long_term_le`, `phaseRepresentatives`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.Moment.Packing

variable {d : ℕ} {B : Box d}

/-- Every real phase has a representative modulo `2π` of absolute value at most `π`. -/
theorem exists_phase_representative_abs_le_pi (x : ℝ) :
    ∃ θ : ℝ, (∃ n : ℤ, x + θ = 2 * Real.pi * (n : ℝ)) ∧ |θ| ≤ Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ) - x,
    ⟨round (x / (2 * Real.pi)), by ring⟩, ?_⟩
  have h := abs_sub_round (x / (2 * Real.pi))
  have hrew : 2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ) - x =
      -(2 * Real.pi) * (x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ)) := by
    field_simp
    ring
  rw [hrew, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  nlinarith

theorem sourceJensenGamma_nonneg' {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ sourceJensenGamma z := by
  unfold sourceJensenGamma
  have h1 : 0 < 1 - z := by linarith
  positivity

/-! ## The window of cells around a cell of degree `d − 1` -/

/-- The cells of degree `d − 2` within coordinate distance `2L` of a cell of degree `d − 1`; empty
for `L = 0`. -/
noncomputable def cellBox (p : DualDForm B (d - 1)) (L : ℕ) : Finset (DualDForm B (d - 2)) :=
  open Classical in
  if L = 0 then ∅ else
    Finset.univ.filter fun e : DualDForm B (d - 2) =>
      ∀ k, cellBase p.1 k ≤ cellBase e.1 k + 2 * L ∧ cellBase e.1 k ≤ cellBase p.1 k + 2 * L

theorem cellBox_card_le (p : DualDForm B (d - 1)) (L : ℕ) :
    (cellBox p L).card ≤ 10 ^ d * L ^ d := by
  classical
  unfold cellBox
  by_cases hL : L = 0
  · simp [hL]
  · simp only [hL, ↓reduceIte]
    have h := card_window_le (fun e : DualDForm B (d - 2) => e.1) Subtype.val_injective
      (fun k => cellBase p.1 k) (2 * L) (2 * L)
    refine (le_trans (le_of_eq ?_) h).trans ?_
    · congr 1
    · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL
      have h1 : 2 * L + 2 * L + 1 ≤ 5 * L := by omega
      calc 2 ^ d * (2 * L + 2 * L + 1) ^ d ≤ 2 ^ d * (5 * L) ^ d :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
        _ = 10 ^ d * L ^ d := by
            rw [mul_pow, ← mul_assoc, ← mul_pow]
            norm_num

/-! ## The Jensen rate -/

/-- The Jensen rate of FS82 (4.38) in dimension `d`, as a function of the activity rate `a`. -/
noncomputable def jensenRateD (d : ℕ) (a : ℝ) : ℝ :=
  polyPackingConstant d (10 ^ d) a (2 * Real.pi * (4 : ℝ) ^ d)

theorem jensenRateD_nonneg (d : ℕ) (a : ℝ) : 0 ≤ jensenRateD d a :=
  polyPackingConstant_nonneg _ _ _ _

/-- The Jensen rate is exponentially small in the activity rate. -/
theorem jensenRateD_le (hd : 0 < d) {a : ℝ} (ha1 : 1 ≤ a) :
    jensenRateD d a ≤
      20 * (10 : ℝ) ^ d * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 * polyTail (3 * d) * Real.exp (1 - a) := by
  have ha0 : 0 < a := by linarith
  have h := polyPackingConstant_le_exponential_tail d (10 ^ d) hd a (2 * Real.pi * (4 : ℝ) ^ d)
    ha0 ha1
  have hpoly := polyTail_nonneg (3 * d)
  have hexp0 : 0 ≤ Real.exp (1 - a) := (Real.exp_pos _).le
  have hnum : (0 : ℝ) ≤ 20 * ((10 ^ d : ℕ) : ℝ) * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 := by positivity
  have hdiv : 20 * ((10 ^ d : ℕ) : ℝ) * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 / a ^ 2 ≤
      20 * ((10 ^ d : ℕ) : ℝ) * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 := by
    apply div_le_self hnum
    nlinarith
  unfold jensenRateD
  calc polyPackingConstant d (10 ^ d) a (2 * Real.pi * (4 : ℝ) ^ d)
      ≤ 20 * ((10 ^ d : ℕ) : ℝ) * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 / a ^ 2 * Real.exp (1 - a) *
          polyTail (3 * d) := h
    _ ≤ 20 * ((10 ^ d : ℕ) : ℝ) * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 * Real.exp (1 - a) *
          polyTail (3 * d) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiv hexp0) hpoly
    _ = 20 * (10 : ℝ) ^ d * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 * polyTail (3 * d) *
          Real.exp (1 - a) := by
        push_cast
        ring

/-! ## The family of currents -/

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The total number of cells of a family of currents with disjoint supports is at most the number
of cells. -/
theorem sum_currentLength_le (J : ι → DualDForm B (d - 2) → ℤ)
    (hdisj : ∀ i j, i ≠ j → ∀ e, J i e ≠ 0 → J j e = 0) :
    ∑ i, currentLength (J i) ≤ Fintype.card (DualDForm B (d - 2)) := by
  classical
  have hd' : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      Disjoint (currentSupport (J i)) (currentSupport (J j)) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun e hei hej => ?_
    exact (mem_currentSupport_iff.mp hej) (hdisj i j hij e (mem_currentSupport_iff.mp hei))
  unfold currentLength
  rw [← Finset.card_biUnion hd']
  exact Finset.card_le_univ _

/-- The Jensen term of a long current with a representative in `[−π, π]`. -/
theorem long_term_le {a : ℝ} (ha1 : 1 ≤ a) (m : ℕ) (J : DualDForm B (d - 2) → ℤ) {z : ℝ}
    (hz0 : 0 ≤ z)
    (hz : z ≤ Real.exp (-(a * (currentEnergy J + (currentLength J : ℝ)))))
    (hpos : 1 ≤ currentLength J) (hlong : m ≤ currentLength J) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    sourceJensenGamma z * θ ^ 2 ≤ 5 * Real.pi ^ 2 * Real.exp (-(a * (m : ℝ))) := by
  set L := currentLength J with hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hpos
  have hLm : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlong
  have hE0 := currentEnergy_nonneg J
  have hsmall : z ≤ 1 / 2 := activity_z_le_half_positive a (currentEnergy J) (L : ℝ) z ha1 hE0 hL1 hz
  have hγ := sourceJensenGamma_le_five_mul hz0 hsmall
  have hγ0 : 0 ≤ sourceJensenGamma z := sourceJensenGamma_nonneg' hz0 (by linarith)
  have hzm : z ≤ Real.exp (-(a * (m : ℝ))) := by
    refine hz.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have hsq : θ ^ 2 ≤ Real.pi ^ 2 := by
    have := abs_le.mp hθ
    nlinarith [Real.pi_pos]
  calc sourceJensenGamma z * θ ^ 2
      ≤ (5 * Real.exp (-(a * (m : ℝ)))) * Real.pi ^ 2 :=
        mul_le_mul (hγ.trans (by linarith)) hsq (sq_nonneg _) (by positivity)
    _ = 5 * Real.pi ^ 2 * Real.exp (-(a * (m : ℝ))) := by ring

variable (hd : 3 ≤ d) (m : ℕ) (hm : ∀ k, m ≤ B k)
  (φ : EuclideanSpace ℝ (DualDForm B (d - 1))) (hφ : ∀ p, ∃ n : ℤ, φ p = (n : ℝ))
  (τ : EuclideanSpace ℝ (DualDForm B (d - 2)))
  (hτ : (dualDExactOneComplex hd B).d₁ τ = φ - loopFieldResidual (dualDExactOneComplex hd B) φ)
  (J : ι → DualDForm B (d - 2) → ℤ) (z : ι → ℝ) {a : ℝ} (ha1 : 1 ≤ a)
  (hco : ∀ i, currentVector (J i) ∈ coClosed (dualDExactOneComplex hd B))
  (hdisj : ∀ i j, i ≠ j → ∀ e, J i e ≠ 0 → J j e = 0)
  (hextent : ∀ i e f, J i e ≠ 0 → J i f ≠ 0 → ∀ k,
    cellBase e.1 k + 1 ≤ cellBase f.1 k + currentLength (J i))
  (hz0 : ∀ i, 0 ≤ z i)
  (hz : ∀ i, z i ≤ Real.exp (-(a * (currentEnergy (J i) + (currentLength (J i) : ℝ)))))

include hm hφ hτ ha1 hco hdisj hextent hz0 hz in
/-- **The Jensen budget of the short currents.** -/
theorem short_packing :
    ∃ θs : ι → ℝ,
      (∀ i, 1 ≤ currentLength (J i) → currentLength (J i) < m → ∃ n : ℤ,
        2 * Real.pi * inner ℝ (currentVector (J i)) τ + θs i = 2 * Real.pi * (n : ℝ)) ∧
      (open Classical in
        ∑ i ∈ Finset.univ.filter (fun i : ι =>
            1 ≤ currentLength (J i) ∧ currentLength (J i) < m),
          sourceJensenGamma (z i) * θs i ^ 2) ≤
        jensenRateD d a *
          ∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2 := by
  classical
  set ε := loopFieldResidual (dualDExactOneComplex hd B) φ with hε
  set T := Finset.univ.filter (fun i : ι =>
    1 ≤ currentLength (J i) ∧ currentLength (J i) < m) with hT
  have hEres : 0 ≤ ∑ p, (ε p) ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  by_cases hTne : T.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hTne
    have hi₀' := (Finset.mem_filter.mp hi₀).2
    obtain ⟨_, p₀', _⟩ := short_filling hd m hm φ hφ τ hτ (J i₀) (hco i₀) (hextent i₀)
      hi₀'.1 hi₀'.2
    have hdata : ∀ i : ι, ∃ (F : DualDForm B (d - 1) → ℤ) (p₀ : DualDForm B (d - 1)),
        (1 ≤ currentLength (J i) ∧ currentLength (J i) < m) →
        (∃ n : ℤ, 2 * Real.pi * inner ℝ (currentVector (J i)) τ +
          2 * Real.pi * ∑ p, ε p * ((F p : ℤ) : ℝ) = 2 * Real.pi * (n : ℝ)) ∧
        (∑ p, |((F p : ℤ) : ℝ)| ≤ (4 : ℝ) ^ d * currentEnergy (J i) *
          (currentLength (J i) : ℝ) ^ d) ∧
        (∀ p, F p ≠ 0 → |ε p| ≤ |ε p₀|) ∧
        (∀ e : DualDForm B (d - 2), J i e ≠ 0 → ∀ k,
          cellBase p₀.1 k ≤ cellBase e.1 k + 2 * currentLength (J i) ∧
          cellBase e.1 k ≤ cellBase p₀.1 k + 2 * currentLength (J i)) := by
      intro i
      by_cases hs : 1 ≤ currentLength (J i) ∧ currentLength (J i) < m
      · obtain ⟨F, p₀, h⟩ := short_filling hd m hm φ hφ τ hτ (J i) (hco i) (hextent i)
          hs.1 hs.2
        exact ⟨F, p₀, fun _ => h⟩
      · exact ⟨fun _ => 0, p₀', fun h => absurd h hs⟩
    choose F p₀ hprops using hdata
    refine ⟨fun i => 2 * Real.pi * ∑ p, ε p * ((F i p : ℤ) : ℝ), ?_, ?_⟩
    · intro i h1 h2
      exact (hprops i ⟨h1, h2⟩).1
    · have hpack := relativePhase_packing_poly (I := ι) (P := DualDForm B (d - 1))
        (α := DualDForm B (d - 2)) d (10 ^ d) T
        (T.image fun i => currentLength (J i))
        (fun i => currentSupport (J i)) cellBox p₀
        (fun i => currentLength (J i)) z
        (fun i => currentEnergy (J i))
        (fun i => 2 * Real.pi * ∑ p, ε p * ((F i p : ℤ) : ℝ))
        (fun p => ε p) (fun i p => ((F i p : ℤ) : ℝ))
        a ((4 : ℝ) ^ d) (by linarith) ha1
        (fun i hi => Finset.mem_image_of_mem _ hi)
        (by
          intro L hL
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hL
          exact (Finset.mem_filter.mp hi).2.1)
        (fun i _ => currentEnergy_nonneg _)
        (fun i _ => hz0 i)
        (fun i _ => hz i)
        (fun i _ => rfl)
        (fun i hi => (hprops i (Finset.mem_filter.mp hi).2).2.1)
        (by
          intro i hi p hp
          refine (hprops i (Finset.mem_filter.mp hi).2).2.2.1 p ?_
          intro h0
          exact hp (by simp [h0]))
        (by
          intro i _ j _ hij
          refine Finset.disjoint_left.mpr fun e hei hej => ?_
          exact (mem_currentSupport_iff.mp hej)
            (hdisj i j hij e (mem_currentSupport_iff.mp hei)))
        (fun i _ => rfl)
        (by
          intro i hi e he
          have hs := (Finset.mem_filter.mp hi).2
          have hne : J i e ≠ 0 := mem_currentSupport_iff.mp he
          have hL0 : currentLength (J i) ≠ 0 := by omega
          unfold cellBox
          simp only [hL0, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (hprops i hs).2.2.2 e hne)
        (fun p L => by exact_mod_cast cellBox_card_le p L)
      exact hpack
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i h1 h2
      exact absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1, h2⟩⟩ hTne
    · rw [Finset.not_nonempty_iff_eq_empty.mp hTne, Finset.sum_empty]
      exact mul_nonneg (jensenRateD_nonneg d a) hEres

include hm hφ hτ ha1 hco hdisj hextent hz0 hz in
/-- **Phase representatives with their Jensen budget, in every dimension `d ≥ 3`.** -/
theorem phaseRepresentatives :
    ∃ θ' : ι → ℝ,
      (∀ i, ∃ n : ℤ, 2 * Real.pi * inner ℝ (currentVector (J i)) τ + θ' i =
        2 * Real.pi * (n : ℝ)) ∧
      ∑ i, sourceJensenGamma (z i) * θ' i ^ 2 ≤
        jensenRateD d a * ∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2 +
          5 * Real.pi ^ 2 * (Fintype.card (DualDForm B (d - 2)) : ℝ) *
            Real.exp (-(a * (m : ℝ))) := by
  classical
  obtain ⟨θs, hs1, hs2⟩ := short_packing hd m hm φ hφ τ hτ J z ha1 hco hdisj hextent hz0 hz
  choose θl hl1 hl2 using fun i : ι =>
    exists_phase_representative_abs_le_pi (2 * Real.pi * inner ℝ (currentVector (J i)) τ)
  set short : ι → Prop := fun i => 1 ≤ currentLength (J i) ∧ currentLength (J i) < m with hshort
  set c : ℝ := 5 * Real.pi ^ 2 * Real.exp (-(a * (m : ℝ))) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨fun i => if short i then θs i
    else if 1 ≤ currentLength (J i) then θl i else 0, ?_, ?_⟩
  · intro i
    by_cases hsh : short i
    · simp only [hsh, ↓reduceIte]
      exact hs1 i hsh.1 hsh.2
    · by_cases hpos : 1 ≤ currentLength (J i)
      · simp only [hsh, hpos, ↓reduceIte]
        exact hl1 i
      · simp only [hsh, hpos, ↓reduceIte]
        have hzero : J i = 0 := by
          funext e
          by_contra hne
          exact hpos (currentLength_pos_of_ne_zero hne)
        refine ⟨0, ?_⟩
        have hvec : currentVector (J i) = 0 := by
          ext e
          simp [currentVector_apply, hzero]
        rw [hvec]
        simp
  · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ short]
    have hfirst : ∑ i ∈ Finset.univ.filter short,
        sourceJensenGamma (z i) *
          (if short i then θs i else if 1 ≤ currentLength (J i) then θl i else 0) ^ 2 =
        ∑ i ∈ Finset.univ.filter short, sourceJensenGamma (z i) * θs i ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hsh : short i := (Finset.mem_filter.mp hi).2
      simp only [hsh, ↓reduceIte]
    have hsecond : ∑ i ∈ Finset.univ.filter (fun i => ¬ short i),
        sourceJensenGamma (z i) *
          (if short i then θs i else if 1 ≤ currentLength (J i) then θl i else 0) ^ 2 ≤
        ∑ i ∈ Finset.univ.filter (fun i => ¬ short i), (currentLength (J i) : ℝ) * c := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hsh : ¬ short i := (Finset.mem_filter.mp hi).2
      by_cases hpos : 1 ≤ currentLength (J i)
      · have hlong : m ≤ currentLength (J i) := by
          by_contra hlt
          exact hsh ⟨hpos, by omega⟩
        simp only [hsh, hpos, ↓reduceIte]
        have hterm := long_term_le ha1 m (J i) (hz0 i) (hz i) hpos hlong (θl i) (hl2 i)
        have hL1 : (1 : ℝ) ≤ (currentLength (J i) : ℝ) := by exact_mod_cast hpos
        calc sourceJensenGamma (z i) * θl i ^ 2 ≤ c := hterm
          _ ≤ (currentLength (J i) : ℝ) * c := by nlinarith
      · simp only [hsh, hpos, ↓reduceIte]
        have h0 : currentLength (J i) = 0 := by omega
        simp [h0]
    have hsumL : ∑ i ∈ Finset.univ.filter (fun i => ¬ short i), (currentLength (J i) : ℝ) * c ≤
        (Fintype.card (DualDForm B (d - 2)) : ℝ) * c := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hc0
      have hsub : ∑ i ∈ Finset.univ.filter (fun i => ¬ short i), (currentLength (J i) : ℝ) ≤
          ∑ i : ι, (currentLength (J i) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => Nat.cast_nonneg _
      refine hsub.trans ?_
      exact_mod_cast sum_currentLength_le J hdisj
    rw [hfirst]
    calc ∑ i ∈ Finset.univ.filter short, sourceJensenGamma (z i) * θs i ^ 2 +
          ∑ i ∈ Finset.univ.filter (fun i => ¬ short i),
            sourceJensenGamma (z i) *
              (if short i then θs i else if 1 ≤ currentLength (J i) then θl i else 0) ^ 2
        ≤ jensenRateD d a * ∑ p, (loopFieldResidual (dualDExactOneComplex hd B) φ p) ^ 2 +
            (Fintype.card (DualDForm B (d - 2)) : ℝ) * c :=
          add_le_add (by convert hs2 using 2) (hsecond.trans hsumL)
      _ = _ := by rw [hc]; ring

end Family

end FroehlichSpencer.FS82.XY.DualD

end
