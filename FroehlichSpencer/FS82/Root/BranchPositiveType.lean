module

public import FroehlichSpencer.FS82.Root.ExpansionOuterMixture
public import FroehlichSpencer.FS82.Moment.QuotientGaussian

/-!
# positive type for Expansion branches

Finite signed-current expansion of each branch state, followed by completed-square estimate.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.ExpansionIntegral
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Poisson

noncomputable section

variable {B : Box 4}

/-- The ordinary finite cosine-current expansion of a branch state. -/
noncomputable def sourceBranchCurrentExpansion (q : Link B → ℤ) (z : ℤ → ℝ)
    (s : CurrentState B) : List (CurrentFourierTerm B) :=
  s.toList.foldl (fun T h => extendCurrentFourierExpansion q z h T)
    [⟨1, 0⟩]

/-- Convert an integer frequency function to the physical integer-current
carrier, undoing the lattice orientation sign. -/
noncomputable def sourceBranchModeCurrent (k : Link B → ℤ) : IntegerCurrent B :=
  physicalGaugeCurrent k

private theorem sourceBranchModeCurrent_physicalMode (k : Link B → ℤ)
    (e : SourceDualOneCells B) :
    latticePhysicalMode (B := B) (sourceBranchModeCurrent k) e = k e := by
  rw [latticePhysicalMode, sourceBranchModeCurrent]
  have happly (j : SourcePoissonEdge B → ℤ) :
      physicalGaugeCurrent (B := B) j e = Gaussian.sourceDualT e * j e := by
    simp [physicalGaugeCurrent]
  rw [happly]
  rcases Gaussian.sourceDualT_is_pm_one e with he | he <;> rw [he] <;> ring

private theorem sourceBranchModeCurrent_phase (k : Link B → ℤ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
    inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
      (B := B) (sourceBranchModeCurrent k)) α =
      Currents.currentPhase (fun e => 2 * Real.pi * α e) k := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, PiLp.smul_apply, smul_eq_mul,
    latticeIntegerModeVector_apply, sourceBranchModeCurrent_physicalMode]
  unfold Currents.currentPhase
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem sourceBranchModeCurrent_phase_neg (k : Link B → ℤ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
    inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
      (B := B) (sourceBranchModeCurrent (-k))) α =
      -Currents.currentPhase (fun e => 2 * Real.pi * α e) k := by
  rw [sourceBranchModeCurrent_phase]
  simp [Currents.currentPhase, Pi.neg_apply, Int.cast_neg,
    Finset.sum_neg_distrib]

private theorem sourceBranchCurrentExpansion_sum_fold
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (l : List (ExpansionLineage B)) (T : List (CurrentFourierTerm B)) :
    currentFourierSum φ (l.foldl
      (fun U h => extendCurrentFourierExpansion q z h U) T) =
      l.foldl (fun a h => a *
        (1 + lineageCoefficient q z h *
          Real.cos (Currents.currentPhase φ (lineageCurrent q h))))
        (currentFourierSum φ T) := by
  induction l generalizing T with
  | nil => simp
  | cons h l ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [currentFourierSum_extend]

private theorem sourceBranchCurrentExpansion_sum
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (s : CurrentState B) :
    currentFourierSum φ (sourceBranchCurrentExpansion q z s) =
      currentStateProduct q z φ s := by
  change currentFourierSum φ
      (s.toList.foldl (fun T h => extendCurrentFourierExpansion q z h T)
        [⟨1, 0⟩]) = currentStateProduct q z φ s
  calc
    _ = s.toList.foldl (fun a h => a *
        (1 + lineageCoefficient q z h *
          Real.cos (Currents.currentPhase φ (lineageCurrent q h))))
        (currentFourierSum φ [⟨1, 0⟩]) :=
      sourceBranchCurrentExpansion_sum_fold q z φ s.toList [⟨1, 0⟩]
    _ = currentStateProduct q z φ s := by
      have hprod : s.toList.foldl (fun a h => a *
          (1 + lineageCoefficient q z h *
            Real.cos (Currents.currentPhase φ (lineageCurrent q h)))) 1 =
          (s.toList.map fun h =>
            1 + lineageCoefficient q z h *
              Real.cos (Currents.currentPhase φ (lineageCurrent q h))).prod := by
        have hgen : ∀ (l : List (ExpansionLineage B)) (a : ℝ),
            l.foldl (fun a h => a *
              (1 + lineageCoefficient q z h *
                Real.cos (Currents.currentPhase φ (lineageCurrent q h)))) a =
            a * (l.map fun h =>
              1 + lineageCoefficient q z h *
                Real.cos (Currents.currentPhase φ (lineageCurrent q h))).prod := by
          intro l
          induction l with
          | nil => intro a; simp
          | cons h l ih =>
              intro a
              simp only [List.foldl_cons, List.map_cons, List.prod_cons]
              rw [ih]
              ring
        simpa using hgen s.toList 1
      rw [show currentFourierSum φ [⟨1, 0⟩] = 1 by
        simp [currentFourierSum, Currents.currentPhase]]
      rw [hprod, Finset.prod_map_toList]
      rfl

private theorem extendCurrentFourierExpansion_weight_nonneg
    (q : Link B → ℤ) (z : ℤ → ℝ) (h : ExpansionLineage B)
    (T : List (CurrentFourierTerm B))
    (hT : ∀ a ∈ T, 0 ≤ a.weight)
    (hK : 0 ≤ lineageCoefficient q z h) :
    ∀ a ∈ extendCurrentFourierExpansion q z h T, 0 ≤ a.weight := by
  intro a ha
  rw [extendCurrentFourierExpansion, List.mem_flatMap] at ha
  rcases ha with ⟨b, hb, hmem⟩
  have hcases : a = b ∨
      a = ⟨(lineageCoefficient q z h / 2) * b.weight,
        b.current + lineageCurrent q h⟩ ∨
      a = ⟨(lineageCoefficient q z h / 2) * b.weight,
        b.current - lineageCurrent q h⟩ := by
    simpa [extendCurrentFourierTerm] using hmem
  rcases hcases with hab | hab | hab
  · rw [hab]
    exact hT b hb
  · rw [hab]
    exact mul_nonneg (mul_nonneg hK (by norm_num)) (hT b hb)
  · rw [hab]
    exact mul_nonneg (mul_nonneg hK (by norm_num)) (hT b hb)

private theorem sourceBranchCurrentExpansion_weight_nonneg
    (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)
    (hK : ∀ h ∈ s, 0 ≤ lineageCoefficient q z h) :
    ∀ a ∈ sourceBranchCurrentExpansion q z s, 0 ≤ a.weight := by
  unfold sourceBranchCurrentExpansion
  have hfold : ∀ l : List (ExpansionLineage B),
      ∀ T : List (CurrentFourierTerm B),
      (∀ a ∈ T, 0 ≤ a.weight) →
      (∀ h ∈ l, 0 ≤ lineageCoefficient q z h) →
      ∀ a ∈ l.foldl (fun U h => extendCurrentFourierExpansion q z h U) T,
        0 ≤ a.weight := by
    intro l
    induction l with
    | nil => intro T hT _ a ha; simpa using hT a ha
    | cons h l ih =>
        intro T hT hKrest a ha
        simp only [List.foldl_cons] at ha ⊢
        apply ih
        · exact extendCurrentFourierExpansion_weight_nonneg q z h T hT
            (hKrest h (by simp))
        · intro u hu
          exact hKrest u (by simp [hu])
        · exact ha
  apply hfold s.toList [⟨1, 0⟩]
  · intro a ha
    simp at ha
    subst a
    norm_num
  · intro h hh
    exact hK h (Finset.mem_toList.mp hh)

private theorem sourceBranchCurrentExpansion_head
    (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B) :
    (sourceBranchCurrentExpansion q z s).head? = some ⟨1, 0⟩ := by
  unfold sourceBranchCurrentExpansion
  have hpres : ∀ (l : List (ExpansionLineage B)) (T : List (CurrentFourierTerm B)),
      T.head? = some ⟨1, 0⟩ →
      (l.foldl (fun U h => extendCurrentFourierExpansion q z h U) T).head? =
        some ⟨1, 0⟩ := by
    intro l
    induction l with
    | nil => intro T hT; simpa using hT
    | cons h l ih =>
        intro T hT
        simp only [List.foldl_cons]
        apply ih
        cases T with
        | nil => simp at hT
        | cons a rest =>
            simp only [List.head?_cons, Option.some.injEq] at hT
            subst a
            simp [extendCurrentFourierExpansion, extendCurrentFourierTerm]
  exact hpres s.toList [⟨1, 0⟩] rfl

private theorem list_map_sum_eq_fin_sum {α γ : Type*} [AddCommMonoid γ]
    (l : List α) (f : α → γ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, List.get_cons_succ']
      rw [ih]

/-- The signed Fourier polynomial associated with every term in the
recursive cosine expansion of a state. -/
private noncomputable def sourceBranchFourierPolynomial
    (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) : ℂ :=
  physicalRealTrigPolynomial (B := B) Finset.univ
    (fun i : Fin (sourceBranchCurrentExpansion q z s).length × Bool =>
      (((sourceBranchCurrentExpansion q z s).get i.1).weight / 2 : ℝ))
    (fun i => sourceBranchModeCurrent
      (if i.2 then
        ((sourceBranchCurrentExpansion q z s).get i.1).current
      else -((sourceBranchCurrentExpansion q z s).get i.1).current))
    α

private theorem sourceCurrentFourierSum_eq_polynomial
    (T : List (CurrentFourierTerm B))
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
    (currentFourierSum (fun e => 2 * Real.pi * α e) T : ℂ) =
      physicalRealTrigPolynomial (B := B) Finset.univ
        (fun i : Fin T.length × Bool => ((T.get i.1).weight / 2 : ℝ))
        (fun i => sourceBranchModeCurrent
          (if i.2 then (T.get i.1).current else -(T.get i.1).current)) α := by
  classical
  have hcos (x : ℝ) :
      (Real.cos x : ℂ) =
        (Complex.exp ((x : ℂ) * Complex.I) +
          Complex.exp (-(x : ℂ) * Complex.I)) / 2 := by
    rw [Complex.ofReal_cos]
    simp [Complex.cos, mul_comm]
  have hsum (T : List (CurrentFourierTerm B)) :
      (currentFourierSum (fun e => 2 * Real.pi * α e) T : ℂ) =
        ∑ i : Fin T.length,
          ((T.get i).weight : ℂ) *
            (Real.cos (Currents.currentPhase (fun e => 2 * Real.pi * α e)
              (T.get i).current) : ℂ) := by
    unfold currentFourierSum
    rw [list_map_sum_eq_fin_sum]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hsum]
  unfold physicalRealTrigPolynomial
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  have hphase (b : Bool) :
      inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
        (B := B) (sourceBranchModeCurrent
          (if b then (T.get i).current else -(T.get i).current))) α =
        if b then Currents.currentPhase (fun e => 2 * Real.pi * α e)
          (T.get i).current else
          -Currents.currentPhase (fun e => 2 * Real.pi * α e)
            (T.get i).current := by
    cases b
    · simp [sourceBranchModeCurrent_phase_neg]
    · simp [sourceBranchModeCurrent_phase]
  rw [hcos]
  simp only [Fintype.sum_bool, hphase]
  push_cast
  ring

private noncomputable def sourceBranchMomentEnvelope
    (β t : ℝ) (μ : SourceW B) : ℝ :=
  Real.exp ((β / 2) * (t ^ 2 * inner ℝ μ
    (latticeVΛ (B := B) Cubical.originZero μ)))

private theorem sourceTiltFactor_zero_re_nonneg
    (β : ℝ) (hβ : 0 ≤ β) (μ : SourceW B) (j : IntegerCurrent B) :
    0 ≤ (physicalGaussianTiltCompletedSquareFactor
      (B := B) β hβ 0 μ j).re := by
  classical
  by_cases hd : currentDivergence j = 0
  · have hc : 0 < FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter
        (B := B) β j hd := Real.exp_pos _
    simpa [physicalGaussianTiltCompletedSquareFactor, hd] using hc.le
  · simp [physicalGaussianTiltCompletedSquareFactor, hd]

private theorem sourceTiltFactor_norm_le_envelope
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (μ : SourceW B)
    (j : IntegerCurrent B) :
    ‖physicalGaussianTiltCompletedSquareFactor
        (B := B) β hβ t μ j‖ ≤
      sourceBranchMomentEnvelope β t μ *
        (physicalGaussianTiltCompletedSquareFactor
          (B := B) β hβ 0 μ j).re := by
  classical
  by_cases hd : currentDivergence j = 0
  · let c := FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter
      (B := B) β j hd
    have hc : 0 < c := Real.exp_pos _
    let A : ℝ := (β / 2) * (t ^ 2 * inner ℝ μ
      (latticeVΛ (B := B) Cubical.originZero μ))
    let P : ℝ := β * t * inner ℝ μ
      (latticeVΛ (B := B) Cubical.originZero
        (FroehlichSpencer.FS82.Moment.SourceCoercivity.sourcePhysicalCurrentCoClosed
          Cubical.originZero j hd))
    have hRe : ((A : ℂ) + Complex.I * (P : ℂ)).re = A := by simp
    have hexp :
        ‖Complex.exp ((A : ℂ) + Complex.I * (P : ℂ))‖ = Real.exp A := by
      rw [Complex.norm_exp, hRe]
    have hfactor : physicalGaussianTiltCompletedSquareFactor
        (B := B) β hβ t μ j =
          Complex.exp ((A : ℂ) + Complex.I * (P : ℂ)) * Complex.ofReal c := by
      simp [physicalGaussianTiltCompletedSquareFactor, hd, A, P, c]
    have hfactor0 : physicalGaussianTiltCompletedSquareFactor
        (B := B) β hβ 0 μ j = Complex.ofReal c := by
      simp [physicalGaussianTiltCompletedSquareFactor, hd, c]
    have hnormc : ‖(c : ℂ)‖ = c := by
      calc
        ‖(c : ℂ)‖ = |c| := RCLike.norm_ofReal c
        _ = c := abs_of_pos hc
    have hzero :
        (physicalGaussianTiltCompletedSquareFactor
          (B := B) β hβ 0 μ j).re = c := by
      rw [hfactor0]
      simp
    have hnorm :
        ‖physicalGaussianTiltCompletedSquareFactor
            (B := B) β hβ t μ j‖ = sourceBranchMomentEnvelope β t μ * c := by
      rw [hfactor, Complex.norm_mul, hexp, hnormc]
      rfl
    rw [hnorm, hzero]
  · simp [physicalGaussianTiltCompletedSquareFactor, hd]

private theorem sourceTiltFactor_zero_at_zero
    (β : ℝ) (hβ : 0 ≤ β) (μ : SourceW B) :
    physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ 0 = 1 := by
  have hd : Currents.currentDivergence (0 : IntegerCurrent B) = 0 := by
    funext v
    simp [Currents.currentDivergence, Currents.sourceDualDivergenceOperator,
      Currents.realCurrent]
  simp [physicalGaussianTiltCompletedSquareFactor, hd,
    FroehlichSpencer.FS82.Moment.QuotientGaussian.sourcePhysicalGaussianCharacter,
    FroehlichSpencer.FS82.Moment.SourceCoercivity.sourcePhysicalCurrentCoClosed,
    FroehlichSpencer.FS82.Moment.SourceCoercivity.sourcePhysicalCurrentVector,
    FroehlichSpencer.FS82.Currents.physicalCurrent,
    FroehlichSpencer.FS82.Gaussian.quotientCovarianceQuadratic,
    FroehlichSpencer.FS82.Gaussian.latticeVΛ]

private theorem sourceBranchModeCurrent_zero :
    sourceBranchModeCurrent (0 : Link B → ℤ) = 0 := by
  ext e
  simp [sourceBranchModeCurrent, physicalGaugeCurrent]

private theorem sourceBranchFourierIntegral_eq_sum
    (β t : ℝ) (hβ : 0 ≤ β) (μ : SourceW B)
    (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B) :
    (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (μ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
      ∂gaugeAveragedRealGaussian (B := B) β hβ) =
      ∑ i : Fin (sourceBranchCurrentExpansion q z s).length × Bool,
        (((sourceBranchCurrentExpansion q z s).get i.1).weight / 2 : ℝ) *
          physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t μ
            (sourceBranchModeCurrent
              (if i.2 then
                ((sourceBranchCurrentExpansion q z s).get i.1).current
              else -((sourceBranchCurrentExpansion q z s).get i.1).current)) := by
  have hpoint (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
      (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ) =
        sourceBranchFourierPolynomial q z s α := by
    calc
      _ = (currentFourierSum (fun e => 2 * Real.pi * α e)
          (sourceBranchCurrentExpansion q z s) : ℂ) := by
            rw [sourceBranchCurrentExpansion_sum]
      _ = sourceBranchFourierPolynomial q z s α := by
            exact sourceCurrentFourierSum_eq_polynomial _ _
  calc
    _ = ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
          Complex.exp ((t * inner ℝ (μ : EuclideanSpace ℝ
            (SourceDualOneCells B)) α : ℝ) : ℂ) *
            sourceBranchFourierPolynomial q z s α
          ∂gaugeAveragedRealGaussian (B := B) β hβ := by
      apply integral_congr_ae
      filter_upwards [] with α
      rw [hpoint α]
    _ = _ := by
      simpa [sourceBranchFourierPolynomial] using
        (gaugeAveragedRealGaussian_tiltedTrigPolynomial_integral_completedSquare
          (B := B) β hβ t μ Finset.univ
          (fun i : Fin (sourceBranchCurrentExpansion q z s).length × Bool =>
            (((sourceBranchCurrentExpansion q z s).get i.1).weight / 2 : ℝ))
          (fun i => sourceBranchModeCurrent
            (if i.2 then
              ((sourceBranchCurrentExpansion q z s).get i.1).current
            else -((sourceBranchCurrentExpansion q z s).get i.1).current)))

private theorem sourceBranchZeroIntegral_ge_one
    (β : ℝ) (hβ : 0 ≤ β) (μ : SourceW B)
    (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)
    (hK : ∀ h ∈ s, 0 ≤ lineageCoefficient q z h) :
    1 ≤ (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
      ∂gaugeAveragedRealGaussian (B := B) β hβ).re := by
  let T := sourceBranchCurrentExpansion q z s
  let I : ℂ := ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
    (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
    ∂gaugeAveragedRealGaussian (B := B) β hβ
  have hsum := sourceBranchFourierIntegral_eq_sum β 0 hβ μ q z s
  have hterms : ∀ a ∈ T, 0 ≤ a.weight := by
    exact sourceBranchCurrentExpansion_weight_nonneg q z s hK
  have hnonneg : ∀ i : Fin T.length × Bool, 0 ≤
      ((((T.get i.1).weight / 2 : ℝ) : ℂ) *
        physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
          (sourceBranchModeCurrent
            (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re := by
    intro i
    have hcoef : 0 ≤ (T.get i.1).weight / 2 :=
      div_nonneg (hterms _ (List.get_mem T i.1)) (by norm_num)
    have hfactor := sourceTiltFactor_zero_re_nonneg β hβ μ
      (sourceBranchModeCurrent
        (if i.2 then (T.get i.1).current else -(T.get i.1).current))
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg hcoef hfactor
  have hhead : T.head? = some ⟨1, 0⟩ := by
    exact sourceBranchCurrentExpansion_head q z s
  obtain ⟨rest, hT⟩ := List.head?_eq_some_iff.mp hhead
  let i0 : Fin T.length := ⟨0, by simp [hT]⟩
  let p : Fin T.length × Bool := (i0, true)
  let r : Fin T.length × Bool := (i0, false)
  let S : Finset (Fin T.length × Bool) := {p, r}
  have hpr : p ≠ r := by simp [p, r]
  have hbase : ∑ i ∈ S,
      ((((T.get i.1).weight / 2 : ℝ) : ℂ) *
        physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
          (sourceBranchModeCurrent
            (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re = 1 := by
    simp [S, p, r, hpr, i0, hT, sourceBranchModeCurrent_zero,
      sourceTiltFactor_zero_at_zero]
    norm_num
  have hsum_re : I.re = ∑ i : Fin T.length × Bool,
      ((((T.get i.1).weight / 2 : ℝ) : ℂ) *
        physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
          (sourceBranchModeCurrent
            (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re := by
    rw [show I = ∑ i : Fin T.length × Bool,
        (((T.get i.1).weight / 2 : ℝ) : ℂ) *
          physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
            (sourceBranchModeCurrent
              (if i.2 then (T.get i.1).current else -(T.get i.1).current)) by
        simpa [I, T] using hsum]
    simp [Complex.re_sum]
  have hsubset : S ⊆ Finset.univ := by simp
  have hbase_le :
      ∑ i ∈ S,
        ((((T.get i.1).weight / 2 : ℝ) : ℂ) *
          physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
            (sourceBranchModeCurrent
              (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re ≤
      ∑ i : Fin T.length × Bool,
        ((((T.get i.1).weight / 2 : ℝ) : ℂ) *
          physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
            (sourceBranchModeCurrent
              (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => hnonneg i)
  have hI : I.re = (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
      ∂gaugeAveragedRealGaussian (B := B) β hβ).re := rfl
  calc
    1 = ∑ i ∈ S,
        ((((T.get i.1).weight / 2 : ℝ) : ℂ) *
          physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
            (sourceBranchModeCurrent
              (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re := hbase.symm
    _ ≤ ∑ i : Fin T.length × Bool,
        ((((T.get i.1).weight / 2 : ℝ) : ℂ) *
          physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
            (sourceBranchModeCurrent
              (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re := hbase_le
    _ = I.re := hsum_re.symm
    _ = (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
        ∂gaugeAveragedRealGaussian (B := B) β hβ).re := hI

private theorem sourceBranchFourierIntegral_norm_le
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (μ : SourceW B)
    (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)
    (hK : ∀ h ∈ s, 0 ≤ lineageCoefficient q z h) :
    ‖∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (μ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
      ∂gaugeAveragedRealGaussian (B := B) β hβ‖ ≤
      sourceBranchMomentEnvelope β t μ *
        (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
          (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
          ∂gaugeAveragedRealGaussian (B := B) β hβ).re := by
  let T := sourceBranchCurrentExpansion q z s
  have hterms : ∀ a ∈ T, 0 ≤ a.weight :=
    sourceBranchCurrentExpansion_weight_nonneg q z s hK
  have hsumt := sourceBranchFourierIntegral_eq_sum β t hβ μ q z s
  have hsum0 := sourceBranchFourierIntegral_eq_sum β 0 hβ μ q z s
  have hcoef (i : Fin T.length × Bool) :
      0 ≤ (T.get i.1).weight / 2 :=
    div_nonneg (hterms _ (List.get_mem T i.1)) (by norm_num)
  have hfactor0 (i : Fin T.length × Bool) :
      0 ≤ (physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
        (sourceBranchModeCurrent
          (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re :=
    sourceTiltFactor_zero_re_nonneg β hβ μ _
  have hzeroSum :
      (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
        ∂gaugeAveragedRealGaussian (B := B) β hβ).re =
        ∑ i : Fin T.length × Bool,
          (T.get i.1).weight / 2 *
            (physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
              (sourceBranchModeCurrent
                (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re := by
    calc
      _ = (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
            Complex.exp ((0 * inner ℝ (μ : EuclideanSpace ℝ
              (SourceDualOneCells B)) α : ℝ) : ℂ) *
              (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
            ∂gaugeAveragedRealGaussian (B := B) β hβ).re := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with α
          simp
      _ = (∑ i : Fin T.length × Bool,
            (((T.get i.1).weight / 2 : ℝ) : ℂ) *
              physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
                (sourceBranchModeCurrent
                  (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re := by
          rw [show (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
                Complex.exp ((0 * inner ℝ (μ : EuclideanSpace ℝ
                  (SourceDualOneCells B)) α : ℝ) : ℂ) *
                  (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
                ∂gaugeAveragedRealGaussian (B := B) β hβ) =
              ∑ i : Fin T.length × Bool,
                (((T.get i.1).weight / 2 : ℝ) : ℂ) *
                  physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
                    (sourceBranchModeCurrent
                      (if i.2 then (T.get i.1).current else -(T.get i.1).current)) by
            simpa [T] using hsum0]
      _ = _ := by simp [Complex.re_sum, Complex.mul_re]
  have hsumBound :
      ‖∑ i : Fin T.length × Bool,
          (((T.get i.1).weight / 2 : ℝ) : ℂ) *
            physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t μ
              (sourceBranchModeCurrent
                (if i.2 then (T.get i.1).current else -(T.get i.1).current))‖ ≤
        sourceBranchMomentEnvelope β t μ *
          (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
            (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
            ∂gaugeAveragedRealGaussian (B := B) β hβ).re := by
    calc
      _ ≤ ∑ i : Fin T.length × Bool,
          ‖(((T.get i.1).weight / 2 : ℝ) : ℂ) *
            physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t μ
              (sourceBranchModeCurrent
                (if i.2 then (T.get i.1).current else -(T.get i.1).current))‖ := by
          exact norm_sum_le Finset.univ _
      _ ≤ ∑ i : Fin T.length × Bool,
          (T.get i.1).weight / 2 *
            (sourceBranchMomentEnvelope β t μ *
              (physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
                (sourceBranchModeCurrent
                  (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re) := by
          apply Finset.sum_le_sum
          intro i hi
          have hfactor := sourceTiltFactor_norm_le_envelope β hβ t μ
            (sourceBranchModeCurrent
              (if i.2 then (T.get i.1).current else -(T.get i.1).current))
          have hnormcoef :
              ‖(((T.get i.1).weight / 2 : ℝ) : ℂ)‖ =
                (T.get i.1).weight / 2 := by
            calc
              ‖(((T.get i.1).weight / 2 : ℝ) : ℂ)‖ =
                  |(T.get i.1).weight / 2| := RCLike.norm_ofReal _
              _ = (T.get i.1).weight / 2 := abs_of_nonneg (hcoef i)
          calc
            ‖(((T.get i.1).weight / 2 : ℝ) : ℂ) *
                physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t μ
                  (sourceBranchModeCurrent
                    (if i.2 then (T.get i.1).current else -(T.get i.1).current))‖ =
              (T.get i.1).weight / 2 *
                ‖physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t μ
                  (sourceBranchModeCurrent
                    (if i.2 then (T.get i.1).current else -(T.get i.1).current))‖ := by
                  rw [Complex.norm_mul, hnormcoef]
            _ ≤ (T.get i.1).weight / 2 *
                (sourceBranchMomentEnvelope β t μ *
                  (physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
                    (sourceBranchModeCurrent
                      (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re) :=
                  mul_le_mul_of_nonneg_left hfactor (hcoef i)
      _ = sourceBranchMomentEnvelope β t μ *
          (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
            (currentStateProduct q z (fun e => 2 * Real.pi * α e) s : ℂ)
            ∂gaugeAveragedRealGaussian (B := B) β hβ).re := by
          calc
            _ = sourceBranchMomentEnvelope β t μ *
                ∑ i : Fin T.length × Bool,
                  (T.get i.1).weight / 2 *
                    (physicalGaussianTiltCompletedSquareFactor (B := B) β hβ 0 μ
                      (sourceBranchModeCurrent
                        (if i.2 then (T.get i.1).current else -(T.get i.1).current))).re := by
                  calc
                    _ = ∑ i : Fin T.length × Bool,
                        sourceBranchMomentEnvelope β t μ *
                          ((T.get i.1).weight / 2 *
                            (physicalGaussianTiltCompletedSquareFactor
                              (B := B) β hβ 0 μ
                              (sourceBranchModeCurrent
                                (if i.2 then (T.get i.1).current
                                  else -(T.get i.1).current))).re) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                    _ = _ := by rw [Finset.mul_sum]
            _ = _ := by rw [hzeroSum]
  rw [hsumt]
  exact hsumBound

/-- The zero-tilt mass of every Expansion terminal branch is strictly positive.
Its positive-type Fourier expansion has nonnegative coefficients and the
empty signed pattern contributes exactly one. -/
theorem branchMass_pos
    {β : ℝ} (hβ : 0 ≤ β) (z : ℕ → ℝ)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (hTerms : ∀ q, IsFixedFrequencyCurrentExpansion
      (sourceAssignmentIntegerFrequency q) (sourceAssignmentIntegerActivity z)
        (terms q))
    (ω : Σ q, SourceExpansionBranch terms q) :
    0 < sourceExpansionBranchMass β hβ z terms ω := by
  let b := sourceExpansionBranchTerm terms ω.1 ω.2
  rcases hTerms ω.1 with ⟨_, _, _, hweight, _, _, hcoeff, _⟩
  have hbweight : 0 < b.weight := by
    exact hweight b (by simp [b, sourceExpansionBranchTerm])
  have hK : ∀ h ∈ b.state,
      0 ≤ lineageCoefficient (sourceAssignmentIntegerFrequency ω.1)
        (sourceAssignmentIntegerActivity z) h := by
    intro h hh
    exact (hcoeff b (by simp [b, sourceExpansionBranchTerm]) h hh).le
  have hzero : 1 ≤ sourceExpansionBranchZeroIntegral β hβ ω.1 z b := by
    unfold sourceExpansionBranchZeroIntegral
    exact sourceBranchZeroIntegral_ge_one β hβ (0 : SourceW B)
      (sourceAssignmentIntegerFrequency ω.1)
      (sourceAssignmentIntegerActivity z) b.state hK
  unfold sourceExpansionBranchMass
  dsimp [sourceExpansionBranchTerm] at *
  exact mul_pos hbweight (lt_of_lt_of_le (by norm_num) hzero)

/-- The normalized branch moment has the uniform absolute bound required by
the branch mixture. The moment field is exactly `sourceExpansionBranchMoment`, the ratio of the
real part of the tilted branch integral to its zero-tilt branch mass. -/
theorem branchMoment_abs_le
    {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) (μ : SourceW B)
    (z : ℕ → ℝ)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (hTerms : ∀ q, IsFixedFrequencyCurrentExpansion
      (sourceAssignmentIntegerFrequency q) (sourceAssignmentIntegerActivity z)
        (terms q))
    (ω : Σ q, SourceExpansionBranch terms q) :
    ‖sourceExpansionBranchMoment β t hβ μ z terms ω‖ ≤
      Real.exp ((β / 2) * (t ^ 2 * inner ℝ μ
        (latticeVΛ (B := B) Cubical.originZero μ))) := by
  let b := sourceExpansionBranchTerm terms ω.1 ω.2
  let q := sourceAssignmentIntegerFrequency ω.1
  let activity := sourceAssignmentIntegerActivity z
  rcases hTerms ω.1 with ⟨_, _, _, hweight, _, _, hcoeff, _⟩
  have hbweight : 0 < b.weight := by
    exact hweight b (by simp [b, sourceExpansionBranchTerm])
  have hbweight' : 0 < ((terms ω.1).get ω.2).weight := by
    simpa [b, sourceExpansionBranchTerm] using hbweight
  have hK : ∀ h ∈ b.state, 0 ≤ lineageCoefficient q activity h := by
    intro h hh
    exact (hcoeff b (by simp [b, sourceExpansionBranchTerm]) h hh).le
  have hzero_pos : 0 < sourceExpansionBranchZeroIntegral β hβ ω.1 z b := by
    have h := sourceBranchZeroIntegral_ge_one β hβ μ q activity b.state hK
    unfold sourceExpansionBranchZeroIntegral
    exact lt_of_lt_of_le (by norm_num) h
  have htilt_bound :
      |(sourceExpansionBranchIntegral β t hβ μ ω.1 z b).re| ≤
        Real.exp ((β / 2) * (t ^ 2 * inner ℝ μ
          (latticeVΛ (B := B) Cubical.originZero μ))) *
          sourceExpansionBranchZeroIntegral β hβ ω.1 z b := by
    calc
      |(sourceExpansionBranchIntegral β t hβ μ ω.1 z b).re| ≤
          ‖sourceExpansionBranchIntegral β t hβ μ ω.1 z b‖ :=
            Complex.abs_re_le_norm _
      _ ≤ Real.exp ((β / 2) * (t ^ 2 * inner ℝ μ
            (latticeVΛ (B := B) Cubical.originZero μ))) *
            sourceExpansionBranchZeroIntegral β hβ ω.1 z b := by
          simpa [sourceExpansionBranchIntegral, sourceExpansionBranchZeroIntegral,
            sourceExpansionBranchTerm, sourceBranchMomentEnvelope, b, q, activity] using
            sourceBranchFourierIntegral_norm_le β hβ t μ q activity b.state hK
  have hmoment_eq :
      sourceExpansionBranchMoment β t hβ μ z terms ω =
        (sourceExpansionBranchIntegral β t hβ μ ω.1 z b).re /
          sourceExpansionBranchZeroIntegral β hβ ω.1 z b := by
    unfold sourceExpansionBranchMoment sourceExpansionBranchRawMoment
      sourceExpansionBranchMass
    simp only [sourceExpansionBranchTerm, b]
    rw [mul_div_mul_left _ _ (ne_of_gt hbweight')]
  rw [hmoment_eq, Real.norm_eq_abs, abs_div, abs_of_pos hzero_pos]
  calc
    |(sourceExpansionBranchIntegral β t hβ μ ω.1 z b).re| /
        sourceExpansionBranchZeroIntegral β hβ ω.1 z b ≤
      (Real.exp ((β / 2) * (t ^ 2 * inner ℝ μ
        (latticeVΛ (B := B) Cubical.originZero μ))) *
          sourceExpansionBranchZeroIntegral β hβ ω.1 z b) /
        sourceExpansionBranchZeroIntegral β hβ ω.1 z b := by
          exact div_le_div_of_nonneg_right htilt_bound hzero_pos.le
    _ = Real.exp ((β / 2) * (t ^ 2 * inner ℝ μ
        (latticeVΛ (B := B) Cubical.originZero μ))) := by
          field_simp [ne_of_gt hzero_pos]

/-- the branch mixture's branch `HasSum` after discharging its two analytic hypotheses by
the positive-type argument (2.99). -/
theorem sourceDualMoment_hasSum_branch_of_positiveType
    {β : ℝ} (hβ : 0 < β) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q)) (μ : SourceW B)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (hTerms : ∀ q, IsFixedFrequencyCurrentExpansion
      (sourceAssignmentIntegerFrequency q) (sourceAssignmentIntegerActivity z)
        (terms q)) :
    (∀ ω : Σ q, SourceExpansionBranch terms q,
      0 ≤ sourceExpansionBranchWeight β hβ z terms ω) ∧
    HasSum (sourceExpansionBranchWeight β hβ z terms) 1 ∧
    (∀ t, HasSum (fun ω : Σ q, SourceExpansionBranch terms q =>
      sourceExpansionBranchWeight β hβ z terms ω *
        sourceExpansionBranchMoment β t hβ.le μ z terms ω)
      (sourceDualMoment β μ t)) := by
  have hMass_pos : ∀ ω : Σ q, SourceExpansionBranch terms q,
      0 < sourceExpansionBranchMass β hβ.le z terms ω :=
    fun ω => branchMass_pos hβ.le z terms hTerms ω
  have hMoment_bound : ∀ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : Σ q,
      SourceExpansionBranch terms q,
        ‖sourceExpansionBranchMoment β t hβ.le μ z terms ω‖ ≤ C := by
    intro t
    refine ⟨Real.exp ((β / 2) * (t ^ 2 * inner ℝ μ
      (latticeVΛ (B := B) Cubical.originZero μ))), (Real.exp_pos _).le, ?_⟩
    intro ω
    exact branchMoment_abs_le hβ.le t μ z terms hTerms ω
  exact sourceDualMoment_hasSum_branch hβ z hnorm hweight_nonneg hz μ
    terms hTerms hMass_pos hMoment_bound

end

end FroehlichSpencer.FS82.Root

end
