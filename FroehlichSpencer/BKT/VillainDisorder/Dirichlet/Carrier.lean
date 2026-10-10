/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.IntegerGFFSymmetry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter
public import FroehlichSpencer.BKT.Potential.Transport
public import FroehlichSpencer.BKT.Villain.TheoremC.CurrentHeight

/-! # The finite zero-exterior Villain height law (FS81 (1.34)–(1.35))

The bounded faces of a centered square of radius `R` are indexed by
`Fin (2 * R + 1) × Fin (2 * R + 1)`. The extra vertex `none` is the zero exterior height.
Every edge of `squareZero` is included, so boundary-crossing edges are part of the product.
The Fourier coefficient is represented with the normalization in the repository's periodized
Gaussian Fourier series; its per-edge scalar is retained and then shown to cancel from normalized
expectations.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC

/-- The side length of the centered dual square with radius `R`. -/
def sideLength (R : ℕ) : ℕ := 2 * R + 1

/-- Bounded dual faces of the centered square with radius `R`. -/
abbrev Site (R : ℕ) := Fin (sideLength R) × Fin (sideLength R)

/-- Integer heights on the centered square, pinned to zero at its exterior vertex. -/
abbrev Height (R : ℕ) := pinnedIntegerField (Option (Site R)) none

/-- Read a squareZero-pinned height in the dual-face carrier of the Villain route. -/
def toRotatorHeight (R : ℕ) (h : Height R) : RotatorFaceHeight (sideLength R) :=
  ⟨h.1, h.2⟩

/-- The site at the center of the square. -/
def center (R : ℕ) : Site R :=
  (⟨R, by simp [sideLength]; omega⟩, ⟨R, by simp [sideLength]; omega⟩)

/-- The site at horizontal displacement `n` from the center, when it lies in the square. -/
def axialSite (R n : ℕ) (hn : n ≤ R) : Site R :=
  (⟨R + n, by simp [sideLength]; omega⟩, ⟨R, by simp [sideLength]; omega⟩)

/-- The squareZero graph on the centered square, including every exterior edge. -/
abbrev graph (R : ℕ) : Multigraph (Option (Site R)) (SquareZeroBond (sideLength R)) :=
  squareZero (sideLength R)

/-- The scalar in the repository's Fourier coefficient of the Villain periodized Gaussian. -/
def fourierConstant (β : ℝ) : ℝ := (2 * Real.pi * β) ^ (-(1 / 2 : ℝ))

/-- The one-edge Fourier normalization is positive at positive temperature. -/
theorem fourierConstant_pos {β : ℝ} (hβ : 0 < β) : 0 < fourierConstant β := by
  unfold fourierConstant
  apply Real.rpow_pos_of_pos
  positivity

/-- The Villain Fourier coefficient `I_β(q)`, including its one-edge normalization. -/
def fourierCoefficient (β : ℝ) (q : ℤ) : ℝ :=
  fourierConstant β * Real.exp (-((q : ℝ) ^ 2) / (2 * β))

/-- The finite-volume source weight in (1.35), with all edges meeting the square included. -/
def heightWeight (R : ℕ) (β : ℝ) (h : Height R) : ℝ :=
  ∏ e : SquareZeroBond (sideLength R),
    fourierCoefficient β ((graph R).grad h.1 e)

/-- The partition function of the finite zero-exterior height law. -/
def partitionFunction (R : ℕ) (β : ℝ) : ℝ :=
  ∑' h : Height R, heightWeight R β h

/-- The fractional dipole cosine in (1.38), at the center and the axial site. -/
def dipoleCosine (R n : ℕ) (hn : n ≤ R) (ξ : ℝ) (h : Height R) : ℝ :=
  Real.cos (2 * Real.pi * ξ *
    (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ)))

/-- The numerator of the finite-volume (1.35) cosine expectation. -/
def cosineNumerator (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ) : ℝ :=
  ∑' h : Height R, dipoleCosine R n hn ξ h * heightWeight R β h

/-- The finite-volume expectation under (1.35). -/
def cosineExpectation (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ) : ℝ :=
  cosineNumerator R n hn β ξ / partitionFunction R β

/-- The Gaussian factor of the source weight is exactly the rooted squareZero integer GFF
weight, at the reciprocal inverse temperature. The explicit one-edge scalar is the only
normalization difference. -/
theorem heightWeight_eq_constant_mul_igffWeight {R : ℕ} {β : ℝ} (hβ : 0 < β)
    (h : Height R) :
    heightWeight R β h =
      fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
        igffWeight (graph R) β⁻¹ h := by
  classical
  have hgauss :
      (∏ e : SquareZeroBond (sideLength R),
        Real.exp (-(((graph R).grad h.1 e : ℤ) : ℝ) ^ 2 / (2 * β))) =
        igffWeight (graph R) β⁻¹ h := by
    let hR : Option (Site R) → ℝ := fun j => (h.1 j : ℝ)
    have hgrad (e : SquareZeroBond (sideLength R)) :
        (((graph R).grad h.1 e : ℤ) : ℝ) = (graph R).grad hR e := by
      simp [hR, Multigraph.grad, Int.cast_sub]
    have hterm (e : SquareZeroBond (sideLength R)) :
        -(((graph R).grad h.1 e : ℤ) : ℝ) ^ 2 / (2 * β) =
          -(β⁻¹ / 2) * (((graph R).grad h.1 e : ℤ) : ℝ) ^ 2 := by
      field_simp [ne_of_gt hβ]
    calc
      (∏ e : SquareZeroBond (sideLength R),
          Real.exp (-(((graph R).grad h.1 e : ℤ) : ℝ) ^ 2 / (2 * β))) =
        Real.exp (∑ e : SquareZeroBond (sideLength R),
          -(β⁻¹ / 2) * (graph R).grad hR e ^ 2) := by
            rw [← Real.exp_sum]
            apply congrArg Real.exp
            apply Finset.sum_congr rfl
            intro e he
            rw [hterm, hgrad]
      _ = igffWeight (graph R) β⁻¹ h := by
            rw [← Finset.mul_sum]
            unfold igffWeight Multigraph.energy
            congr 1
  unfold heightWeight fourierCoefficient
  rw [Finset.prod_mul_distrib, Finset.prod_const, hgauss]
  simp only [Finset.card_univ]

/-- The zero-exterior squareZero height weight and the weight used by the Villain
Theorem C route differ by exactly the Fourier scalar for every edge. -/
theorem heightWeight_eq_constant_mul_gaussianVillainHeightWeight {R : ℕ} {β : ℝ}
    (hβ : 0 < β) (h : Height R) :
    heightWeight R β h =
      fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
        gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := by
  rw [heightWeight_eq_constant_mul_igffWeight hβ h]
  congr 1
  unfold gaussianVillainHeightWeight
  -- Both finite graphs are the same rooted dual carrier after the wired edge reindexing.
  let I := squareZero_dualFace_carrier_isomorphism (sideLength R)
  let hR : RotatorDualFace (sideLength R) → ℝ := fun j => (h.1 j : ℝ)
  have hvertices : I.vertices = Equiv.refl _ := rfl
  have hpush : I.pushField hR = hR := by
    funext v
    change hR (I.vertices.symm v) = hR v
    rw [hvertices]
    rfl
  have henergy :
      (rotatorDualGraph (sideLength R)).energy hR = (graph R).energy hR := by
    have htransport := Multigraph.Isomorphism.energy_transport I hR
    simpa [hpush] using htransport
  have hleft :
      currentGaussianWeight β (rotatorFaceHeightCurrent (toRotatorHeight R h)) =
        Real.exp (-(β⁻¹ / 2) * (rotatorDualGraph (sideLength R)).energy hR) := by
    have hgrad (e : RotatorInternalBond (sideLength R)) :
        ((rotatorFaceHeightCurrent (toRotatorHeight R h) e : ℤ) : ℝ) =
          (rotatorDualGraph (sideLength R)).grad hR e := by
      change (((toRotatorHeight R h).1 ((rotatorDualGraph (sideLength R)).src e) -
        (toRotatorHeight R h).1 ((rotatorDualGraph (sideLength R)).tgt e) : ℤ) : ℝ) = _
      simp [toRotatorHeight, hR, Multigraph.grad]
    have hterm (e : RotatorInternalBond (sideLength R)) :
        -((rotatorFaceHeightCurrent (toRotatorHeight R h) e : ℤ) : ℝ) ^ 2 /
            (2 * β) =
          -(β⁻¹ / 2) * (rotatorDualGraph (sideLength R)).grad hR e ^ 2 := by
      rw [hgrad]
      field_simp [ne_of_gt hβ]
    unfold currentGaussianWeight
    rw [← Real.exp_sum]
    rw [show (∑ e : RotatorInternalBond (sideLength R),
      -((rotatorFaceHeightCurrent (toRotatorHeight R h) e : ℤ) : ℝ) ^ 2 / (2 * β)) =
      ∑ e : RotatorInternalBond (sideLength R),
        -(β⁻¹ / 2) * (rotatorDualGraph (sideLength R)).grad hR e ^ 2 by
      apply Finset.sum_congr rfl
      intro e he
      exact hterm e]
    apply congrArg Real.exp
    rw [← Finset.mul_sum]
    unfold Multigraph.energy
    rfl
  rw [hleft, igffWeight, henergy]

/-- A centered square of radius at least one gives the connected squareZero graph. -/
theorem graph_connected (R : ℕ) (hR : 1 ≤ R) : (graph R).toSimpleGraph.Connected := by
  have hside : 1 < sideLength R := by simp [sideLength]; omega
  simpa [graph] using squareZero_connected (sideLength R) hside

/-- The source weight is strictly positive at every admissible height. -/
theorem heightWeight_pos {R : ℕ} {β : ℝ} (hβ : 0 < β) (h : Height R) :
    0 < heightWeight R β h := by
  rw [heightWeight_eq_constant_mul_igffWeight hβ h]
  exact mul_pos (pow_pos (fourierConstant_pos hβ) _) (Real.exp_pos _)

/-- The zero-exterior source weights are summable on every nontrivial centered square. -/
theorem summable_heightWeight {R : ℕ} {β : ℝ} (hR : 1 ≤ R) (hβ : 0 < β) :
    Summable (fun h : Height R => heightWeight R β h) := by
  have hIG := summable_igffWeight (graph R) (graph_connected R hR) β⁻¹
    (inv_pos.mpr hβ) none
  have hmul := hIG.mul_left
    (fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)))
  refine hmul.congr fun h => ?_
  rw [heightWeight_eq_constant_mul_igffWeight hβ h]

/-- The source partition function is the explicit per-edge normalization times the rooted IGFF
partition function. This proves that the Fourier constant cancels from every normalized law. -/
theorem partitionFunction_eq_constant_mul_igffPartitionFunction {R : ℕ} {β : ℝ}
    (hR : 1 ≤ R) (hβ : 0 < β) :
    partitionFunction R β =
      fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
        igffPartitionFunction (graph R) β⁻¹ none := by
  have hIG := summable_igffWeight (graph R) (graph_connected R hR) β⁻¹
    (inv_pos.mpr hβ) none
  rw [partitionFunction]
  calc
    (∑' h : Height R, heightWeight R β h) =
        ∑' h : Height R,
          fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
            igffWeight (graph R) β⁻¹ h := by
          apply tsum_congr
          intro h
          exact heightWeight_eq_constant_mul_igffWeight hβ h
    _ = fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
        ∑' h : Height R, igffWeight (graph R) β⁻¹ h :=
          hIG.tsum_mul_left _

/-- The finite source partition function is strictly positive. -/
theorem partitionFunction_pos {R : ℕ} {β : ℝ} (hR : 1 ≤ R) (hβ : 0 < β) :
    0 < partitionFunction R β := by
  rw [partitionFunction_eq_constant_mul_igffPartitionFunction hR hβ]
  exact mul_pos (pow_pos (fourierConstant_pos hβ) _)
    (igffPartitionFunction_pos (graph R) (graph_connected R hR) β⁻¹
      (inv_pos.mpr hβ) none)

/-- The normalized finite (1.35) cosine expectation is exactly the rooted squareZero IGFF
expectation. The edge normalization is proved to cancel. -/
theorem cosineExpectation_eq_igffExpectation {R n : ℕ} (hR : 1 ≤ R) (hn : n ≤ R)
    {β ξ : ℝ} (hβ : 0 < β) :
    cosineExpectation R n hn β ξ =
      igffExpectation (graph R) (graph_connected R hR) β⁻¹ (inv_pos.mpr hβ) none
        (fun h => dipoleCosine R n hn ξ h) := by
  let F : Height R → ℝ := fun h => dipoleCosine R n hn ξ h
  have hIG := summable_igffWeight (graph R) (graph_connected R hR) β⁻¹
    (inv_pos.mpr hβ) none
  have hnumIG : Summable (fun h : Height R => F h * igffWeight (graph R) β⁻¹ h) := by
    apply hIG.of_norm_bounded
    intro h
    have hw : 0 < igffWeight (graph R) β⁻¹ h := by
      unfold igffWeight
      exact Real.exp_pos _
    calc
      ‖F h * igffWeight (graph R) β⁻¹ h‖ = |F h| * igffWeight (graph R) β⁻¹ h := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
      _ ≤ 1 * igffWeight (graph R) β⁻¹ h :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hw.le
      _ = igffWeight (graph R) β⁻¹ h := one_mul _
  have hc : fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) ≠ 0 := by
    exact ne_of_gt (pow_pos (fourierConstant_pos hβ) _)
  have hZ : igffPartitionFunction (graph R) β⁻¹ none ≠ 0 :=
    (igffPartitionFunction_pos (graph R) (graph_connected R hR) β⁻¹
      (inv_pos.mpr hβ) none).ne'
  have hnum : cosineNumerator R n hn β ξ =
      fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
        ∑' h : Height R, F h * igffWeight (graph R) β⁻¹ h := by
    unfold cosineNumerator
    calc
      (∑' h : Height R, dipoleCosine R n hn ξ h * heightWeight R β h) =
          ∑' h : Height R,
            fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
              (F h * igffWeight (graph R) β⁻¹ h) := by
                apply tsum_congr
                intro h
                rw [heightWeight_eq_constant_mul_igffWeight hβ h]
                dsimp [F]
                ring
      _ = fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R)) *
          ∑' h : Height R, F h * igffWeight (graph R) β⁻¹ h := hnumIG.tsum_mul_left _
  rw [cosineExpectation, hnum,
    partitionFunction_eq_constant_mul_igffPartitionFunction hR hβ]
  unfold igffExpectation
  field_simp [hc, hZ]
  simp [F]

/-- The complex dipole character whose real part is the cosine observable. -/
def dipoleCharacter (R n : ℕ) (hn : n ≤ R) (ξ : ℝ) (h : Height R) : ℂ :=
  let θ : ℝ := 2 * Real.pi * ξ *
    (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ))
  Complex.exp (Complex.I * (θ : ℂ))

/-- The complex dipole character has unit modulus. -/
theorem dipoleCharacter_norm (R n : ℕ) (hn : n ≤ R) (ξ : ℝ) (h : Height R) :
    ‖dipoleCharacter R n hn ξ h‖ = 1 := by
  simp only [dipoleCharacter, Complex.norm_exp_I_mul_ofReal]

/-- The complex numerator for the fractional dipole character. -/
def characterNumerator (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ) : ℂ :=
  ∑' h : Height R, dipoleCharacter R n hn ξ h * (heightWeight R β h : ℂ)

/-- The complex expectation of the fractional dipole character under (1.35). -/
def characterExpectation (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ) : ℂ :=
  characterNumerator R n hn β ξ / (partitionFunction R β : ℂ)

/-- The real part of one character summand is its cosine summand. -/
theorem re_dipoleCharacter_mul_weight (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ)
    (h : Height R) :
    Complex.re (dipoleCharacter R n hn ξ h * (heightWeight R β h : ℂ)) =
      dipoleCosine R n hn ξ h * heightWeight R β h := by
  unfold dipoleCharacter dipoleCosine
  let θ : ℝ := 2 * Real.pi * ξ *
    (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ))
  change Complex.re (Complex.exp (Complex.I * (θ : ℂ)) *
      (heightWeight R β h : ℂ)) = Real.cos θ * heightWeight R β h
  have hphase : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
  rw [hphase, Complex.exp_ofReal_mul_I]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- Even weights and the real-part identity show that (1.35)'s complex character expectation has
the stated real cosine expectation. -/
theorem characterExpectation_re_eq_cosineExpectation {R n : ℕ} (hR : 1 ≤ R)
    (hn : n ≤ R) {β ξ : ℝ} (hβ : 0 < β) :
    Complex.re (characterExpectation R n hn β ξ) = cosineExpectation R n hn β ξ := by
  have hweight := summable_heightWeight hR hβ
  have hcharacter : Summable (fun h : Height R =>
      dipoleCharacter R n hn ξ h * (heightWeight R β h : ℂ)) := by
    have hcast : Summable (fun h : Height R => (heightWeight R β h : ℂ)) :=
      Complex.summable_ofReal.mpr hweight
    have hcastNorm : Summable (fun h : Height R => ‖(heightWeight R β h : ℂ)‖) :=
      hcast.norm
    exact Summable.of_norm_bounded hcastNorm fun h => by
      rw [norm_mul, dipoleCharacter_norm, one_mul]
  have hRe : Complex.re (characterNumerator R n hn β ξ) = cosineNumerator R n hn β ξ := by
    unfold characterNumerator cosineNumerator
    rw [Complex.re_tsum hcharacter]
    apply tsum_congr
    intro h
    exact re_dipoleCharacter_mul_weight R n hn β ξ h
  have hZ : 0 < partitionFunction R β := partitionFunction_pos hR hβ
  unfold characterExpectation cosineExpectation
  rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero]
  rw [zero_div, add_zero, hRe]
  field_simp [ne_of_gt hZ]

/-- Negation preserves the source weight, by the evenness of every coefficient in (1.34). -/
theorem heightWeight_neg (R : ℕ) (β : ℝ) (h : Height R) :
    heightWeight R β ⟨-h.1, by simp [h.2]⟩ = heightWeight R β h := by
  unfold heightWeight fourierCoefficient
  apply Finset.prod_congr rfl
  intro e he
  have hgrad :
      (graph R).grad (-h.1) e = -((graph R).grad h.1 e) := by
    simp [Multigraph.grad]
    ring
  rw [hgrad]
  simp [Int.cast_neg, sq]

/-- Negation preserves the fractional dipole cosine. -/
theorem dipoleCosine_neg (R n : ℕ) (hn : n ≤ R) (ξ : ℝ) (h : Height R) :
    dipoleCosine R n hn ξ ⟨-h.1, by simp [h.2]⟩ = dipoleCosine R n hn ξ h := by
  unfold dipoleCosine
  change Real.cos (2 * Real.pi * ξ *
      (((-h.1 (some (center R)) - (-h.1 (some (axialSite R n hn))) : ℤ) : ℝ))) =
    Real.cos (2 * Real.pi * ξ *
      (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ)))
  have harg :
      2 * Real.pi * ξ *
          (((-h.1 (some (center R)) - (-h.1 (some (axialSite R n hn))) : ℤ) : ℝ)) =
        -(2 * Real.pi * ξ *
          (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ))) := by
    push_cast
    ring
  rw [harg, Real.cos_neg]

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
