module

public import FroehlichSpencer.FS82.Root.PhysicalOuter
public import FroehlichSpencer.FS82.Moment.ExpansionIntegral
public import FroehlichSpencer.FS82.Moment.SourceConstructor
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# normalize the Expansion terminal branches in the outer mixture

The assignment-level physical mixture is refined by the finite Expansion expansion
for each frequency assignment.

A terminal branch is kept as a list index, so
repeated terms in the expansion retain their multiplicity.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.ExpansionIntegral
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Poisson

noncomputable section

variable {B : Cubical.Box 4}

/--
The complex integral attached to one fixed-frequency Expansion terminal
branch.
-/
noncomputable def sourceExpansionBranchIntegral (β t : ℝ) (hβ : 0 ≤ β)
    (μ : SourceW B) (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (b : CurrentExpansionTerm B) : ℂ :=
  ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
    Complex.exp ((t * inner ℝ (μ : EuclideanSpace ℝ (SourceDualOneCells B)) α : ℝ) : ℂ) *
      (currentStateProduct (sourceAssignmentIntegerFrequency q)
        (sourceAssignmentIntegerActivity z)
        (fun e => 2 * Real.pi * α e) b.state : ℂ)
    ∂gaugeAveragedRealGaussian (B := B) β hβ

/-- The zero-tilt mass of one Expansion branch, before the outer Poisson coefficient
and the global normalizer are included. -/
noncomputable def sourceExpansionBranchZeroIntegral (β : ℝ) (hβ : 0 ≤ β)
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (b : CurrentExpansionTerm B) : ℝ :=
  (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
    (currentStateProduct (sourceAssignmentIntegerFrequency q)
      (sourceAssignmentIntegerActivity z)
      (fun e => 2 * Real.pi * α e) b.state : ℂ)
    ∂gaugeAveragedRealGaussian (B := B) β hβ).re

/-- A finite Expansion branch is an indexed entry of the assignment's terminal list.
Using `Fin length` preserves repeated entries in that list. -/
abbrev SourceExpansionBranch (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (q : SourcePoissonEdge B → ℕ) := Fin (terms q).length

/-- The Expansion terminal term at one assignment and one list index. -/
def sourceExpansionBranchTerm
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (q : SourcePoissonEdge B → ℕ) (i : SourceExpansionBranch terms q) :
    CurrentExpansionTerm B := (terms q).get i

/-- The branch's unnormalized tilted moment, including its positive Expansion
coefficient. -/
noncomputable def sourceExpansionBranchRawMoment (β t : ℝ) (hβ : 0 ≤ β)
    (μ : SourceW B) (z : ℕ → ℝ)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (ω : Σ q, SourceExpansionBranch terms q) : ℝ :=
  (sourceExpansionBranchTerm terms ω.1 ω.2).weight *
    (sourceExpansionBranchIntegral β t hβ μ ω.1 z
      (sourceExpansionBranchTerm terms ω.1 ω.2)).re

/-- The branch's zero-tilt mass, including its Expansion coefficient. -/
noncomputable def sourceExpansionBranchMass (β : ℝ) (hβ : 0 ≤ β)
    (z : ℕ → ℝ)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (ω : Σ q, SourceExpansionBranch terms q) : ℝ :=
  (sourceExpansionBranchTerm terms ω.1 ω.2).weight *
    sourceExpansionBranchZeroIntegral β hβ ω.1 z
      (sourceExpansionBranchTerm terms ω.1 ω.2)

/-- The normalized moment of one Expansion branch. -/
noncomputable def sourceExpansionBranchMoment (β t : ℝ) (hβ : 0 ≤ β)
    (μ : SourceW B) (z : ℕ → ℝ)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (ω : Σ q, SourceExpansionBranch terms q) : ℝ :=
  sourceExpansionBranchRawMoment β t hβ μ z terms ω /
    sourceExpansionBranchMass β hβ z terms ω

/-- The explicit outer weight of an Expansion branch: assignment coefficient times
its zero-tilt branch mass, divided by `Ξ_Λ`. -/
noncomputable def sourceExpansionBranchWeight (β : ℝ) (hβ : 0 < β) (z : ℕ → ℝ)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (ω : Σ q, SourceExpansionBranch terms q) : ℝ :=
  assignmentCoefficient z ω.1 * sourceExpansionBranchMass β hβ.le z terms ω /
    xi (sourceChordMatrix (B := B) β)

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

private theorem list_complex_re_sum (l : List ℂ) :
    l.sum.re = (l.map Complex.re).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Complex.add_re]

private theorem sourceExpansionBranchIntegral_zero (β : ℝ) (hβ : 0 ≤ β)
    (μ : SourceW B) (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (b : CurrentExpansionTerm B) :
    (sourceExpansionBranchIntegral β 0 hβ μ q z b).re =
      sourceExpansionBranchZeroIntegral β hβ q z b := by
  simp [sourceExpansionBranchIntegral, sourceExpansionBranchZeroIntegral]

private theorem sourceAssignmentGaussianMoment_re_eq_expansionBranchRaw_sum
    (β : ℝ) (hβ : 0 ≤ β) (μ : SourceW B) (q : SourcePoissonEdge B → ℕ)
    (z : ℕ → ℝ) (terms : List (CurrentExpansionTerm B))
    (hTerms : IsFixedFrequencyCurrentExpansion
      (sourceAssignmentIntegerFrequency q) (sourceAssignmentIntegerActivity z) terms)
    (t : ℝ) :
    (sourceAssignmentGaussianMoment β hβ t μ q z).re =
      ∑ i : Fin terms.length,
        (terms.get i).weight *
          (sourceExpansionBranchIntegral β t hβ μ q z (terms.get i)).re := by
  have hbranch := sourceAssignmentGaussianMoment_eq_branchSum β t hβ μ q z terms hTerms
  calc
    (sourceAssignmentGaussianMoment β hβ t μ q z).re =
        ((terms.map fun b => b.weight *
          sourceExpansionBranchIntegral β t hβ μ q z b).sum).re := by
            rw [hbranch]
            rfl
    _ = (terms.map fun b =>
        (b.weight * sourceExpansionBranchIntegral β t hβ μ q z b).re).sum := by
          rw [list_complex_re_sum]
          simp only [List.map_map, Function.comp_def]
    _ = ∑ i : Fin terms.length,
        (terms.get i).weight *
          (sourceExpansionBranchIntegral β t hβ μ q z (terms.get i)).re := by
            rw [list_map_sum_eq_fin_sum]
            apply Finset.sum_congr rfl
            intro i hi
            simp [Complex.mul_re]

theorem sourceDualMoment_zero {β : ℝ} (hβ : 0 < β) (μ : SourceW B) :
    sourceDualMoment β μ 0 = 1 := by
  let A := sourceChordMatrix (B := B) β
  let τ := sourceChordTest μ
  have hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  have hpoisson := Poisson.tested_poisson_ratio A hA τ 0
  have hxi := Poisson.xi_complex_eq A hA
  have hzero : Poisson.realTiltParameter τ 0 = 0 := by
    funext i
    simp [Poisson.realTiltParameter]
  have hXiNe : xi A ≠ 0 := ne_of_gt (xi_pos A hA)
  have hXiC : (xi A : ℂ) ≠ 0 := by exact_mod_cast hXiNe
  have htest : Poisson.testedExpectation A τ 0 = 1 := by
    calc
      Poisson.testedExpectation A τ 0 =
          (∑' k : (sourceRootedTree B).Chord → ℤ,
            dualQuadraticExp A (Poisson.realTiltParameter τ 0) k) / (xi A : ℂ) := hpoisson
      _ = (xi A : ℂ) / (xi A : ℂ) := by rw [hzero, ← hxi]
      _ = 1 := div_self hXiC
  have hreal := testedExpectation_eq_dualMoment A τ 0
  have hcomplex : (dualMoment A τ 0 : ℂ) = 1 := by
    calc
      (dualMoment A τ 0 : ℂ) = Poisson.testedExpectation A τ 0 := hreal.symm
      _ = 1 := htest
  change dualMoment A τ 0 = 1
  exact_mod_cast hcomplex

theorem sourceDualMoment_hasSum_branch
    {β : ℝ} (hβ : 0 < β) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q)) (μ : SourceW B)
    (terms : (SourcePoissonEdge B → ℕ) → List (CurrentExpansionTerm B))
    (hTerms : ∀ q, IsFixedFrequencyCurrentExpansion
      (sourceAssignmentIntegerFrequency q) (sourceAssignmentIntegerActivity z)
        (terms q))
    (hMass_pos : ∀ ω : Σ q, SourceExpansionBranch terms q,
      0 < sourceExpansionBranchMass β hβ.le z terms ω)
    (hMoment_bound : ∀ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : Σ q,
      SourceExpansionBranch terms q,
        ‖sourceExpansionBranchMoment β t hβ.le μ z terms ω‖ ≤ C) :
    (∀ ω : Σ q, SourceExpansionBranch terms q,
      0 ≤ sourceExpansionBranchWeight β hβ z terms ω) ∧
    HasSum (sourceExpansionBranchWeight β hβ z terms) 1 ∧
    (∀ t, HasSum (fun ω : Σ q, SourceExpansionBranch terms q =>
      sourceExpansionBranchWeight β hβ z terms ω *
        sourceExpansionBranchMoment β t hβ.le μ z terms ω)
      (sourceDualMoment β μ t)) := by
  let A := sourceChordMatrix (B := B) β
  have hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  have hXiPos : 0 < xi A := xi_pos A hA
  have hXiNe : xi A ≠ 0 := ne_of_gt hXiPos
  have hweight : ∀ ω : Σ q, SourceExpansionBranch terms q,
      0 ≤ sourceExpansionBranchWeight β hβ z terms ω := by
    intro ω
    unfold sourceExpansionBranchWeight
    exact div_nonneg (mul_nonneg
      (assignmentCoefficient_pos z ω.1 hz).le (hMass_pos ω).le) hXiPos.le
  have hsource := sourceDualMoment_hasSum_physicalAssignment hβ z hnorm
    hweight_nonneg hz μ
  have hInner : ∀ q : SourcePoissonEdge B → ℕ, ∀ t : ℝ,
      HasSum (fun i : SourceExpansionBranch terms q =>
        sourceExpansionBranchWeight β hβ z terms ⟨q, i⟩ *
          sourceExpansionBranchMoment β t hβ.le μ z terms ⟨q, i⟩)
        (assignmentCoefficient z q *
          (sourceAssignmentGaussianMoment β hβ.le t μ q z).re / xi A) := by
    intro q t
    let f : CurrentExpansionTerm B → ℝ := fun b =>
      b.weight * (sourceExpansionBranchIntegral β t hβ.le μ q z b).re
    have hBranchSum := sourceAssignmentGaussianMoment_re_eq_expansionBranchRaw_sum
      β hβ.le μ q z (terms q) (hTerms q) t
    have hsum :
        (∑ i : Fin (terms q).length,
          ((terms q).get i).weight *
            (sourceExpansionBranchIntegral β t hβ.le μ q z ((terms q).get i)).re) =
        (sourceAssignmentGaussianMoment β hβ.le t μ q z).re := by
      exact hBranchSum.symm
    have hf : ∀ i : Fin (terms q).length,
        sourceExpansionBranchWeight β hβ z terms ⟨q, i⟩ *
          sourceExpansionBranchMoment β t hβ.le μ z terms ⟨q, i⟩ =
        assignmentCoefficient z q * f ((terms q).get i) / xi A := by
      intro i
      have hMi := hMass_pos (⟨q, i⟩ : Σ q, SourceExpansionBranch terms q)
      have hTermWeight : 0 < ((terms q).get i).weight := by
        rcases hTerms q with ⟨_, _, _, hw, _, _, _, _⟩
        exact hw _ (List.get_mem _ i)
      have hZeroPos : 0 < sourceExpansionBranchZeroIntegral β hβ.le q z ((terms q).get i) := by
        simp [sourceExpansionBranchMass, sourceExpansionBranchTerm] at hMi
        exact (mul_pos_iff_of_pos_left hTermWeight).mp hMi
      have hXiNe' : xi (sourceChordMatrix (B := B) β) ≠ 0 := by
        simpa [A] using hXiNe
      unfold sourceExpansionBranchWeight sourceExpansionBranchMoment
        sourceExpansionBranchMass sourceExpansionBranchRawMoment sourceExpansionBranchTerm f
      field_simp [hXiNe, hXiNe', ne_of_gt hMi, ne_of_gt hZeroPos]
      simp only [A]
      ring_nf
    have hval :
        (∑ i : Fin (terms q).length,
          sourceExpansionBranchWeight β hβ z terms ⟨q, i⟩ *
            sourceExpansionBranchMoment β t hβ.le μ z terms ⟨q, i⟩) =
          assignmentCoefficient z q *
            (sourceAssignmentGaussianMoment β hβ.le t μ q z).re / xi A := by
      calc
        _ = ∑ i : Fin (terms q).length,
            (assignmentCoefficient z q * f ((terms q).get i) / xi A) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hf i
        _ = (assignmentCoefficient z q / xi A) *
            (∑ i : Fin (terms q).length, f ((terms q).get i)) := by
              calc
                _ = ∑ i : Fin (terms q).length,
                    (assignmentCoefficient z q / xi A) * f ((terms q).get i) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
                _ = _ := by rw [Finset.mul_sum]
        _ = assignmentCoefficient z q *
            (sourceAssignmentGaussianMoment β hβ.le t μ q z).re / xi A := by
              rw [hsum]
              ring
    change HasSum
      (fun i : Fin (terms q).length =>
        sourceExpansionBranchWeight β hβ z terms ⟨q, i⟩ *
          sourceExpansionBranchMoment β t hβ.le μ z terms ⟨q, i⟩)
      (assignmentCoefficient z q *
        (sourceAssignmentGaussianMoment β hβ.le t μ q z).re / xi A)
    rw [← hval]
    exact hasSum_fintype _
  have hbranchMoment0 : ∀ ω : Σ q, SourceExpansionBranch terms q,
      sourceExpansionBranchMoment β 0 hβ.le μ z terms ω = 1 := by
    intro ω
    unfold sourceExpansionBranchMoment sourceExpansionBranchRawMoment sourceExpansionBranchMass
    rw [sourceExpansionBranchIntegral_zero]
    exact div_self (ne_of_gt (hMass_pos ω))
  have hweight_fib : ∀ q, Summable
      (fun i : SourceExpansionBranch terms q =>
        sourceExpansionBranchWeight β hβ z terms ⟨q, i⟩) := by
    intro q
    exact (hasSum_fintype _).summable
  have hInner0 : ∀ q : SourcePoissonEdge B → ℕ,
      HasSum (fun i : SourceExpansionBranch terms q =>
        sourceExpansionBranchWeight β hβ z terms ⟨q, i⟩)
        (assignmentCoefficient z q *
          (sourceAssignmentGaussianMoment β hβ.le 0 μ q z).re / xi A) := by
    intro q
    apply (hInner q 0).congr_fun
    intro i
    simp [hbranchMoment0]
  have hweight_group : Summable (fun q =>
      ∑' i : SourceExpansionBranch terms q,
        sourceExpansionBranchWeight β hβ z terms ⟨q, i⟩) := by
    refine (hsource 0).summable.congr ?_
    intro q
    exact (hInner0 q).tsum_eq.symm
  have hweight_flat : Summable (sourceExpansionBranchWeight β hβ z terms) :=
    (summable_sigma_of_nonneg hweight).2 ⟨hweight_fib, hweight_group⟩
  have hweights0 : HasSum (sourceExpansionBranchWeight β hβ z terms)
      (sourceDualMoment β μ 0) :=
    HasSum.sigma_of_hasSum (hsource 0) hInner0 hweight_flat
  have hweights : HasSum (sourceExpansionBranchWeight β hβ z terms) 1 := by
    simpa [sourceDualMoment_zero hβ μ] using hweights0
  have htotal (t : ℝ) :
      HasSum (fun ω : Σ q, SourceExpansionBranch terms q =>
        sourceExpansionBranchWeight β hβ z terms ω *
          sourceExpansionBranchMoment β t hβ.le μ z terms ω)
        (sourceDualMoment β μ t) := by
    let f : (Σ q, SourceExpansionBranch terms q) → ℝ := fun ω =>
      sourceExpansionBranchWeight β hβ z terms ω *
        sourceExpansionBranchMoment β t hβ.le μ z terms ω
    have hfib : ∀ q, Summable (fun i : SourceExpansionBranch terms q => f ⟨q, i⟩) := by
      intro q
      exact (hInner q t).summable
    obtain ⟨C, hC, hbound⟩ := hMoment_bound t
    have hflat : Summable f := by
      apply Summable.of_norm_bounded (hweights.summable.mul_left C)
      intro ω
      rw [show f ω = sourceExpansionBranchWeight β hβ z terms ω *
          sourceExpansionBranchMoment β t hβ.le μ z terms ω by rfl]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hweight ω)]
      calc
        sourceExpansionBranchWeight β hβ z terms ω *
            ‖sourceExpansionBranchMoment β t hβ.le μ z terms ω‖ ≤
          sourceExpansionBranchWeight β hβ z terms ω * C :=
            mul_le_mul_of_nonneg_left (hbound ω) (hweight ω)
        _ = C * sourceExpansionBranchWeight β hβ z terms ω := by ring
    exact HasSum.sigma_of_hasSum (hsource t) (fun q => hInner q t) hflat
  exact ⟨hweight, hweights, htotal⟩


end

end FroehlichSpencer.FS82.Root

end
