/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# FS82 maximum-plaquette packing: abstract maximum-plaquette packing and moment algebra

Transient feasibility development; not a project module or  API.
-/

public section

namespace FroehlichSpencer.FS82.Moment.Packing

/-- Disjoint supports of fixed cardinality inside one finite box. -/
theorem card_mul_le_of_disjoint_supports
    {ι α : Type*} [DecidableEq α] (T : Finset ι) (S : ι → Finset α)
    (B : Finset α) (L : ℕ)
    (hdisj : (↑T : Set ι).PairwiseDisjoint S)
    (hsub : ∀ i ∈ T, S i ⊆ B)
    (hsize : ∀ i ∈ T, (S i).card = L) :
    T.card * L ≤ B.card := by
  have hUnionSub : T.biUnion S ⊆ B := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    exact hsub i hi hxi
  have hUnionCard := Finset.card_le_card hUnionSub
  calc
    T.card * L = ∑ i ∈ T, L := by simp
    _ = ∑ i ∈ T, (S i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hsize i hi).symm
    _ = (T.biUnion S).card := (Finset.card_biUnion hdisj).symm
    _ ≤ B.card := hUnionCard


/-- A finite-family `ℓ²` packing inequality. The coefficient budget is the sum over lengths;
thus it is independent of the plaquette field and of the finite-volume box. -/
theorem sum_l2_with_length_budget
    {P : Type*} [Fintype P] [DecidableEq P]
    (K : Finset ℕ) (g : P → ℝ) (q : ℕ → ℝ) (c : ℝ)
    (hbudget : (∑ L ∈ K, q L) ≤ c) :
    (∑ p, ∑ L ∈ K, q L * (g p)^2) ≤ c * (∑ p, (g p)^2) := by
  calc
    (∑ p, ∑ L ∈ K, q L * (g p)^2)
        = ∑ p, ((∑ L ∈ K, q L) * (g p)^2) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.sum_mul]
    _ ≤ ∑ p, c * (g p)^2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_right hbudget (sq_nonneg (g p))
    _ = c * (∑ p, (g p)^2) := by rw [Finset.mul_sum]

/-- For `a>0`, the elementary Gaussian-tail factor is bounded uniformly in `x≥0`. -/
theorem square_mul_exp_neg_le (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    x^2 * Real.exp (-(a * x)) ≤ 4 / a^2 := by
  have hb : 0 < a / 2 := by linarith
  have hbase : x * Real.exp (-((a / 2) * x)) ≤ 1 / (a / 2) := by
    let b : ℝ := a / 2
    have hb' : 0 < b := by dsimp [b]; linarith
    have hexp : 0 < Real.exp (b * x) := Real.exp_pos _
    have hmain : b * x ≤ Real.exp (b * x) := by
      have h := Real.add_one_le_exp (b * x)
      linarith
    have hxle : x ≤ Real.exp (b * x) / b := (le_div_iff₀ hb').2 (by nlinarith [hmain])
    calc
      x * Real.exp (-(b * x)) = x / Real.exp (b * x) := by
        rw [Real.exp_neg]
        simp only [div_eq_mul_inv]
      _ ≤ (Real.exp (b * x) / b) / Real.exp (b * x) :=
        div_le_div_of_nonneg_right hxle hexp.le
      _ = 1 / b := by field_simp [ne_of_gt hb', ne_of_gt hexp]
  have hbase' : 0 ≤ x * Real.exp (-((a / 2) * x)) :=
    mul_nonneg hx (le_of_lt (Real.exp_pos _))
  have hsq := (sq_le_sq₀ hbase' (by positivity : 0 ≤ 1 / (a / 2))).2 hbase
  have hexpeq : Real.exp (-(a * x)) = Real.exp (-((a / 2) * x))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  calc
    x^2 * Real.exp (-(a * x))
        = (x * Real.exp (-((a / 2) * x)))^2 := by rw [hexpeq]; ring_nf
    _ ≤ (1 / (a / 2))^2 := hsq
    _ = 4 / a^2 := by field_simp [ne_of_gt hb]; ring_nf


/-- The exact Jensen coefficient used by the cosine Jensen proof. -/
@[expose] noncomputable def jensenGamma (z : ℝ) : ℝ :=
  z / (2 * (1 - z)) + 2 * z^2 / (1 - z)^2

/-- Source correction to the printed (2.102): the valid uniform bound on `0≤z≤1/2` is
`Γ(z)≤5z`. The printed constant `4` fails at `z=1/2` (`Γ(1/2)=5/2`). -/
theorem jensenGamma_le_five_mul (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) :
    jensenGamma z ≤ 5 * z := by
  have hden : 0 < 1 - z := by linarith
  have hden2 : 0 < (1 - z)^2 := sq_pos_of_pos hden
  have hden1 : 1 ≤ 2 * (1 - z) := by linarith
  have hterm1 : z / (2 * (1 - z)) ≤ z := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 - z))).2
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hden1)]
  have hdenSq : (1 / 2 : ℝ)^2 ≤ (1 - z)^2 := by
    exact (sq_le_sq₀ (by norm_num) hden.le).2 (by linarith)
  have hterm2 : 2 * z^2 / (1 - z)^2 ≤ 8 * z^2 := by
    apply (div_le_iff₀ hden2).2
    nlinarith [sq_nonneg z, hdenSq]
  have hquad : 8 * z^2 ≤ 4 * z := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz)]
  unfold jensenGamma
  linarith


/-- Abstract per-current estimate from (2.102)--(2.104), with the corrected positive rate.
`x` is `‖ρ‖₂²`, `L` is the support length, and `M` is the maximum of `|dτ|` on the
containing cube. -/
theorem per_current_activity_error
    (a C x L M z gamma theta : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hx : 0 ≤ x) (hM : 0 ≤ M)
    (hz : z ≤ Real.exp (-(a * (x + L))))
    (hgamma : gamma ≤ 5 * z)
    (htheta : |theta| ≤ C * M * x * L^4) :
    gamma * theta^2 ≤ 20 * C^2 / a^2 * L^8 * Real.exp (-(a * L)) * M^2 := by
  have hbound : 0 ≤ C * M * x * L^4 := by positivity
  have hthetaSq : theta^2 ≤ (C * M * x * L^4)^2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg theta) hbound).2 htheta
  have hga : 0 ≤ Real.exp (-(a * (x + L))) := (Real.exp_pos _).le
  have hgaSplit : Real.exp (-(a * (x + L))) = Real.exp (-(a * x)) * Real.exp (-(a * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have htail := square_mul_exp_neg_le a x ha hx
  calc
    gamma * theta^2 ≤ (5 * z) * theta^2 := mul_le_mul_of_nonneg_right hgamma (sq_nonneg theta)
    _ ≤ (5 * Real.exp (-(a * (x + L)))) * (C * M * x * L^4)^2 := by
      have hzt : z * theta^2 ≤ Real.exp (-(a * (x + L))) * (C * M * x * L^4)^2 := by
        calc
          z * theta^2 ≤ Real.exp (-(a * (x + L))) * theta^2 :=
            mul_le_mul_of_nonneg_right hz (sq_nonneg theta)
          _ ≤ Real.exp (-(a * (x + L))) * (C * M * x * L^4)^2 :=
            mul_le_mul_of_nonneg_left hthetaSq hga
      nlinarith [hzt]
    _ = 5 * C^2 * M^2 * L^8 * (x^2 * Real.exp (-(a * x))) * Real.exp (-(a * L)) := by
      rw [hgaSplit]
      ring_nf
    _ ≤ 20 * C^2 / a^2 * L^8 * Real.exp (-(a * L)) * M^2 := by
      have hcoef : 0 ≤ 5 * C^2 * M^2 * L^8 * Real.exp (-(a * L)) := by positivity
      calc
        5 * C^2 * M^2 * L^8 * (x^2 * Real.exp (-(a * x))) * Real.exp (-(a * L))
            = (5 * C^2 * M^2 * L^8 * Real.exp (-(a * L))) * (x^2 * Real.exp (-(a * x))) := by ring_nf
        _ ≤ (5 * C^2 * M^2 * L^8 * Real.exp (-(a * L))) * (4 / a^2) :=
            mul_le_mul_of_nonneg_left htail hcoef
        _ = 20 * C^2 / a^2 * L^8 * Real.exp (-(a * L)) * M^2 := by ring_nf


/-- The activity after absorbing the squared current norm in the Gaussian tail. -/
@[expose] noncomputable def currentActivity (a C : ℝ) (L : ℕ) : ℝ :=
  (20 * C^2 / a^2) * (L : ℝ)^8 * Real.exp (-(a * (L : ℝ)))


/-- The explicit summable coefficient budget; the source sum starts at `L=4`, while this
convenient formula includes the nonnegative terms `L<4`. -/
@[expose] noncomputable def cpack (a C : ℝ) : ℝ :=
  (1280 * C^2 / a^2) * ∑' L : ℕ, (L : ℝ)^11 * Real.exp (-(a * (L : ℝ)))

/-- Polynomial times exponential tails are summable at every positive rate. -/
theorem summable_poly_exp (a : ℝ) (ha : 0 < a) :
    Summable (fun L : ℕ => (L : ℝ)^11 * Real.exp (-(a * (L : ℝ)))) := by
  simpa only [neg_mul] using
    (Real.summable_pow_mul_exp_neg_nat_mul 11 (r := a) ha)

/-- The finite coefficient sum used by the box packing is bounded by `cpack(a,C)`. -/
theorem activity_budget_le_cpack (a C : ℝ) (ha : 0 < a)
    (K : Finset ℕ) :
    (∑ L ∈ K, 64 * (L : ℝ)^3 * currentActivity a C L) ≤ cpack a C := by
  have hsum := (summable_poly_exp a ha).sum_le_tsum K (by intro L hL; positivity)
  have hcoef : 0 ≤ 1280 * C^2 / a^2 := by positivity
  have hfinite1 :
      (∑ L ∈ K, 64 * (L : ℝ)^3 * currentActivity a C L) =
        ∑ L ∈ K, (1280 * C^2 / a^2) *
          ((L : ℝ)^11 * Real.exp (-(a * (L : ℝ)))) := by
    apply Finset.sum_congr rfl
    intro L hL
    simp only [currentActivity]
    ring_nf
  have hfinite :
      (∑ L ∈ K, 64 * (L : ℝ)^3 * currentActivity a C L) =
        (1280 * C^2 / a^2) *
          ∑ L ∈ K, (L : ℝ)^11 * Real.exp (-(a * (L : ℝ))) := by
    rw [hfinite1, ← Finset.mul_sum]
  rw [hfinite]
  calc
    (1280 * C^2 / a^2) *
        (∑ L ∈ K, (L : ℝ)^11 * Real.exp (-(a * (L : ℝ))))
        ≤ (1280 * C^2 / a^2) *
          ∑' L : ℕ, (L : ℝ)^11 * Real.exp (-(a * (L : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum hcoef
    _ = cpack a C := rfl

/-- A fixed finite constant for the polynomial-geometric tail at unit rate. -/
@[expose] noncomputable def polyTail11 : ℝ :=
  ∑' L : ℕ, (L : ℝ)^11 * Real.exp (-(1 * (L : ℝ)))

/-- The explicit coefficient is exponentially small: for `a≥1`, `cpack(a,C)` is at most a
constant times `a⁻² exp(1-a)`. -/
theorem cpack_le_exponential_tail (a C : ℝ) (ha : 0 < a) (ha1 : 1 ≤ a) :
    cpack a C ≤ (1280 * C^2 / a^2) * Real.exp (1 - a) * polyTail11 := by
  let fA : ℕ → ℝ := fun L => (L : ℝ)^11 * Real.exp (-(a * (L : ℝ)))
  let f1 : ℕ → ℝ := fun L => (L : ℝ)^11 * Real.exp (-(1 * (L : ℝ)))
  have hsA : Summable fA := by
    simpa [fA] using summable_poly_exp a ha
  have hs1 : Summable f1 := by
    simpa [f1] using summable_poly_exp 1 (by norm_num)
  have hpoint : ∀ L, fA L ≤ Real.exp (1 - a) * f1 L := by
    intro L
    by_cases hL : L = 0
    · simp [fA, f1, hL]
    · have hLpos : 1 ≤ (L : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hL)
      have hLminus : 0 ≤ (L : ℝ) - 1 := by linarith
      have harg : -(a * ((L : ℝ) - 1)) ≤ -((L : ℝ) - 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hLminus]
      have hExp : Real.exp (-(a * ((L : ℝ) - 1))) ≤ Real.exp (-((L : ℝ) - 1)) :=
        (Real.exp_le_exp).2 harg
      have hfactorA : Real.exp (-(a * (L : ℝ))) =
          Real.exp (-a) * Real.exp (-(a * ((L : ℝ) - 1))) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      have hfactor1 : Real.exp (-((L : ℝ) - 1)) =
          Real.exp 1 * Real.exp (-(L : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      have hcoeff : Real.exp (-a) * Real.exp (-((L : ℝ) - 1)) =
          Real.exp (1 - a) * Real.exp (-(L : ℝ)) := by
        calc
          Real.exp (-a) * Real.exp (-((L : ℝ) - 1))
              = Real.exp (-a - ((L : ℝ) - 1)) := by rw [← Real.exp_add]; congr 1
          _ = Real.exp ((1 - a) + (-(L : ℝ))) := by
            congr 1
            ring_nf
          _ = Real.exp (1 - a) * Real.exp (-(L : ℝ)) := Real.exp_add _ _
      calc
        fA L = (L : ℝ)^11 *
            (Real.exp (-a) * Real.exp (-(a * ((L : ℝ) - 1)))) := by
              simp only [fA, hfactorA]
        _ ≤ (L : ℝ)^11 * (Real.exp (-a) * Real.exp (-((L : ℝ) - 1))) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_left hExp (Real.exp_pos _).le
              · positivity
        _ = Real.exp (1 - a) * f1 L := by
              rw [hcoeff]
              simp only [f1]
              ring_nf
  have hscaled : Summable (fun L => Real.exp (1 - a) * f1 L) := hs1.mul_left _
  have htsum := Summable.tsum_le_tsum hpoint hsA hscaled
  have hscale : (∑' L : ℕ, Real.exp (1 - a) * f1 L) =
      Real.exp (1 - a) * polyTail11 := by
    simpa [f1, polyTail11] using hs1.tsum_mul_left (Real.exp (1 - a))
  have hcoef : 0 ≤ 1280 * C^2 / a^2 := by positivity
  calc
    cpack a C = (1280 * C^2 / a^2) * ∑' L : ℕ, fA L := by
      simp [cpack, fA]
    _ ≤ (1280 * C^2 / a^2) *
        (Real.exp (1 - a) * polyTail11) := by
          rw [← hscale]
          exact mul_le_mul_of_nonneg_left htsum hcoef
    _ = (1280 * C^2 / a^2) * Real.exp (1 - a) * polyTail11 := by ring_nf


/-- The corrected positive decay rate from FS82 (2.103). -/
@[expose] noncomputable def currentRate (beta beta₁ : ℝ) : ℝ := (beta / 216 - beta₁) / 2


end FroehlichSpencer.FS82.Moment.Packing

end
