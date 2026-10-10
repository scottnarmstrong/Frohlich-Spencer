/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Carrier
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Limit
import FroehlichSpencer.BKT.Bridge.IntegerGFFSymmetry
import Mathlib.Tactic

/-! # The complex character in the finite-volume Theorem D identity

The zero-exterior height law (1.35) already has a complex-character expectation in `Carrier`. This
module proves that height negation preserves its weight and kills the imaginary part of its
fractional dipole character. Thus the finite Villain/height duality (1.38) holds as a complex
identity. The centered complex formulation of Theorem D preserves the current every-limit-point
scope; it does not assert uniqueness of the thermodynamic limit.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet
open FroehlichSpencer.BKT

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

private theorem dipoleCharacter_neg (R n : ℕ) (hn : n ≤ R) (ξ : ℝ)
    (h : Height R) :
    dipoleCharacter R n hn ξ (pinnedIntegerFieldNegEquiv none h) =
      star (dipoleCharacter R n hn ξ h) := by
  unfold dipoleCharacter
  let θ : ℝ := 2 * Real.pi * ξ *
    (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ))
  let θneg : ℝ := 2 * Real.pi * ξ *
    (((((pinnedIntegerFieldNegEquiv none h).1 (some (center R))) -
      ((pinnedIntegerFieldNegEquiv none h).1 (some (axialSite R n hn))) : ℤ) : ℝ))
  change Complex.exp (Complex.I * (θneg : ℂ)) =
    star (Complex.exp (Complex.I * (θ : ℂ)))
  have hθ : θneg = -θ := by
    dsimp only [θneg, θ]
    have hfield : (pinnedIntegerFieldNegEquiv none h).1 = fun j => -h.1 j := rfl
    rw [hfield]
    push_cast
    ring_nf
  rw [hθ]
  have hleft : Complex.I * ((-θ : ℝ) : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I := by ring
  have hright : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
  rw [hleft, hright, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp [Real.cos_neg]
  · simp [Real.sin_neg]

/-- The complex numerator of (1.35) has zero imaginary part by height-sign symmetry. -/
theorem characterNumerator_im_zero {R n : ℕ} (hR : 1 ≤ R) (hn : n ≤ R)
    {β ξ : ℝ} (hβ : 0 < β) :
    Complex.im (characterNumerator R n hn β ξ) = 0 := by
  let e := pinnedIntegerFieldNegEquiv (none : Option (Site R))
  let g : Height R → ℂ := fun h =>
    dipoleCharacter R n hn ξ h * (heightWeight R β h : ℂ)
  have hweight := summable_heightWeight hR hβ
  have hcast : Summable (fun h : Height R => (heightWeight R β h : ℂ)) :=
    Complex.summable_ofReal.mpr hweight
  have hg : Summable g := by
    apply Summable.of_norm_bounded hcast.norm
    intro h
    dsimp [g]
    rw [norm_mul, dipoleCharacter_norm, one_mul]
  have hnegweight (h : Height R) : heightWeight R β (e h) = heightWeight R β h := by
    change heightWeight R β ⟨-h.1, by simp [h.2]⟩ = _
    exact heightWeight_neg R β h
  have hnegterm (h : Height R) : g (e h) = star (g h) := by
    dsimp [g]
    rw [dipoleCharacter_neg R n hn ξ h, hnegweight h]
    simp
  have hodd (h : Height R) : (g h).im = - (g (e h)).im := by
    rw [hnegterm]
    simp
  have hsum : (∑' h : Height R, (g h).im) = -(∑' h : Height R, (g h).im) := by
    calc
      (∑' h : Height R, (g h).im) = ∑' h : Height R, -(g (e h)).im := by
        apply tsum_congr
        intro h
        exact hodd h
      _ = ∑' h : Height R, -(g h).im := Equiv.tsum_eq e (fun h => -(g h).im)
      _ = -(∑' h : Height R, (g h).im) := by rw [← tsum_neg]
  have hzero : (∑' h : Height R, (g h).im) = 0 := by linarith
  change Complex.im (∑' h : Height R, g h) = 0
  rw [Complex.im_tsum hg]
  exact hzero

/-- The normalized complex expectation of the zero-exterior height law is real. -/
theorem characterExpectation_im_zero {R n : ℕ} (hR : 1 ≤ R) (hn : n ≤ R)
    {β ξ : ℝ} (hβ : 0 < β) :
    Complex.im (characterExpectation R n hn β ξ) = 0 := by
  have hnum := characterNumerator_im_zero (ξ := ξ) hR hn hβ
  change (characterNumerator R n hn β ξ / (partitionFunction R β : ℂ)).im = 0
  rw [Complex.div_im, hnum]
  simp

/-- The (1.35) complex character expectation is exactly the complexification of its cosine
expectation. -/
theorem characterExpectation_eq_ofReal_cosineExpectation {R n : ℕ}
    (hR : 1 ≤ R) (hn : n ≤ R) {β ξ : ℝ} (hβ : 0 < β) :
    characterExpectation R n hn β ξ = (cosineExpectation R n hn β ξ : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      (characterExpectation_re_eq_cosineExpectation hR hn hβ)
  · simpa only [Complex.ofReal_im] using characterExpectation_im_zero hR hn hβ

/-- The finite complex form of the FS81 (1.38) identity. -/
theorem dirichletFullFreeVillainDisorderExpectation_eq_characterExpectation
    (R n : ℕ) (hR : 1 ≤ R) (hn : n ≤ R) (β ξ : ℝ) (_hβ : 0 < β) :
    (dirichletFullFreeVillainDisorderExpectation R n hn β ξ _hβ : ℂ) =
      characterExpectation R n hn β ξ := by
  rw [dirichletFullFreeVillainDisorderExpectation_eq_cosineExpectation R n hR hn β ξ _hβ]
  exact (characterExpectation_eq_ofReal_cosineExpectation hR hn _hβ).symm

/-- The centered complex-character expectation; as for the real centered sequence, it is set to
zero when the fixed dipole string does not fit in the box. -/
def dirichletFullCenteredCharacter (R n : ℕ) (β ξ : ℝ) (_hβ : 0 < β) : ℂ :=
  if hn : n ≤ R then characterExpectation R n hn β ξ else 0

/-- Every finite centered complex expectation is the complexification of the existing full
free-boundary Villain expectation. -/
theorem dirichletFullCenteredCharacter_eq_ofReal
    (R n : ℕ) (β ξ : ℝ) (hβ : 0 < β) (hnpos : 1 ≤ n) :
    dirichletFullCenteredCharacter R n β ξ hβ =
      (dirichletFullCenteredDisorder R n β ξ hβ : ℂ) := by
  unfold dirichletFullCenteredCharacter dirichletFullCenteredDisorder
  split_ifs with hn
  · have hR : 1 ≤ R := hnpos.trans hn
    exact dirichletFullFreeVillainDisorderExpectation_eq_characterExpectation
      R n hR hn β ξ hβ |>.symm
  · rfl

/-- Complex-valued restatement of the finite and every-limit-point conclusions of Theorem D.
The thermodynamic-limit scope is unchanged: convergence is only asserted along a subsequence, and
every cluster point satisfies the same bound. -/
theorem dirichletFullTheoremD_complexThermodynamicLimit
    (hFejer : RootedDirichletFejerGlobalInput) :
    ∃ c : ℝ, 0 < c ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        ∃ β₀ : ℝ, ∃ _hβ₀ : 0 < β₀,
          ∀ β : ℝ, ∀ hβ : 0 < β, ∀ _hβlarge : β₀ < β,
            ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
              ∀ n : ℕ, ∀ _hnpos : 1 ≤ n,
                (∀ᶠ R in atTop, n ≤ R) ∧
                (∀ R : ℕ,
                  Complex.re (dirichletFullCenteredCharacter R n β ξ hβ) ∈ Set.Icc (-1) 1 ∧
                  Complex.im (dirichletFullCenteredCharacter R n β ξ hβ) = 0) ∧
                (∀ᶠ R in atTop,
                  Complex.re (dirichletFullCenteredCharacter R n β ξ hβ) ∈ Set.Icc 0
                    (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))) ∧
                  Complex.im (dirichletFullCenteredCharacter R n β ξ hβ) = 0) ∧
                (∃ z : ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
                  Tendsto (fun k => dirichletFullCenteredCharacter (φ k) n β ξ hβ)
                    atTop (𝓝 z)) ∧
                ∀ z : ℂ,
                  MapClusterPt z atTop (fun R => dirichletFullCenteredCharacter R n β ξ hβ) →
                    Complex.re z ∈ Set.Icc 0
                      (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))) ∧
                    Complex.im z = 0 := by
  obtain ⟨c, hc, hrest⟩ := dirichletFullTheoremD_thermodynamicLimit hFejer
  refine ⟨c, hc, fun η hη hηle => ?_⟩
  obtain ⟨β₀, hβ₀, hβrest⟩ := hrest η hη hηle
  refine ⟨β₀, hβ₀, fun β hβ hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos => ?_⟩
  obtain ⟨hfit, hglobal, htail, hseq, hcluster⟩ :=
    hβrest β hβ hβlarge ξ hξpos hξlt hηξ hηcomp n hnpos
  refine ⟨hfit, ?_, ?_, ?_, ?_⟩
  · intro R
    rw [dirichletFullCenteredCharacter_eq_ofReal R n β ξ hβ hnpos]
    exact ⟨by simpa using hglobal R, by simp⟩
  · filter_upwards [htail] with R hR
    rw [dirichletFullCenteredCharacter_eq_ofReal R n β ξ hβ hnpos]
    exact ⟨by simpa using hR, by simp⟩
  · obtain ⟨ℓ, φ, hφ, hT⟩ := hseq
    refine ⟨(ℓ : ℂ), φ, hφ, ?_⟩
    have hT' := Complex.continuous_ofReal.continuousAt.tendsto.comp hT
    have hEq : (fun k => dirichletFullCenteredCharacter (φ k) n β ξ hβ) =
        fun k => (dirichletFullCenteredDisorder (φ k) n β ξ hβ : ℂ) := by
      funext k
      exact dirichletFullCenteredCharacter_eq_ofReal (φ k) n β ξ hβ hnpos
    rw [hEq]
    change Tendsto (fun k => Complex.ofReal (dirichletFullCenteredDisorder (φ k) n β ξ hβ))
      atTop (𝓝 (ℓ : ℂ))
    exact hT'
  · intro z hz
    have hzre : MapClusterPt z.re atTop (fun R => dirichletFullCenteredDisorder R n β ξ hβ) := by
      have hmap := hz.continuousAt_comp Complex.continuous_re.continuousAt
      change MapClusterPt z.re atTop
        (fun R => Complex.re (dirichletFullCenteredCharacter R n β ξ hβ)) at hmap
      have heq : (fun R => Complex.re (dirichletFullCenteredCharacter R n β ξ hβ)) =
          fun R => dirichletFullCenteredDisorder R n β ξ hβ := by
        funext R
        rw [dirichletFullCenteredCharacter_eq_ofReal R n β ξ hβ hnpos]
        rfl
      rw [heq] at hmap
      exact hmap
    have hzim : z.im = 0 := by
      have hmap := hz.continuousAt_comp Complex.continuous_im.continuousAt
      change MapClusterPt z.im atTop
        (fun R => Complex.im (dirichletFullCenteredCharacter R n β ξ hβ)) at hmap
      have heq : (fun R => Complex.im (dirichletFullCenteredCharacter R n β ξ hβ)) =
          fun _ : ℕ => (0 : ℝ) := by
        funext R
        rw [dirichletFullCenteredCharacter_eq_ofReal R n β ξ hβ hnpos]
        rfl
      rw [heq] at hmap
      have hzmem : z.im ∈ ({(0 : ℝ)} : Set ℝ) := by
        exact (isClosed_singleton : IsClosed ({(0 : ℝ)} : Set ℝ)).mem_of_mapClusterPt
          hmap (Eventually.of_forall fun _ => by simp)
      simpa using hzmem
    exact ⟨hcluster z.re hzre, hzim⟩

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
