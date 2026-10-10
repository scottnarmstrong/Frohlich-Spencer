/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.CharacterRegroup
public import FroehlichSpencer.FS82.Poisson.IntegralDuality
public import FroehlichSpencer.FS82.Poisson.QuadraticModel
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Poisson

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Signed-character branches indexed by actual co-closed integer link fields;
inactive positive modes are still attached to every source link. -/
def GaugeCharacterBranch (T : RootedTreeGauge V E) :=
  Σ j : {j : E → ℤ // RootedTreeGauge.CoClosed T j},
    (Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ)

namespace GaugeCharacterBranch

def current {T : RootedTreeGauge V E} (b : GaugeCharacterBranch T) : E → ℤ := b.1.1

noncomputable def coefficient {T : RootedTreeGauge V E}
    (z : ℕ → ℝ) (b : GaugeCharacterBranch T) : ℝ :=
  ∏ i, inactiveWeight z (b.2 i)

end GaugeCharacterBranch

omit [Fintype V] in
private theorem gaugeCharacterBranch_fiber_hasSum
    (T : RootedTreeGauge V E) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (j : {j : E → ℤ // RootedTreeGauge.CoClosed T j})
    (Char : {j : E → ℤ // RootedTreeGauge.CoClosed T j} → ℂ) :
    HasSum (fun q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ =>
      ((∏ i, inactiveWeight z (q i) : ℝ) : ℂ) * Char j) (Char j) := by
  have hs : HasSum (fun q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ =>
      ((∏ i, inactiveWeight z (q i) : ℝ) : ℂ)) 1 :=
    (Complex.hasSum_ofReal).mpr
      (hasSum_fin_inactiveWeight_one z hnorm hweight_nonneg _)
  convert HasSum.mul_right (Char j) hs using 1
  all_goals simp only [one_mul]

omit [Fintype V] in
private theorem gaugeCharacterBranch_absSummable
    (T : RootedTreeGauge V E) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (Char : {j : E → ℤ // RootedTreeGauge.CoClosed T j} → ℂ)
    (hChar : Summable Char) :
    Summable (fun b : GaugeCharacterBranch T =>
      (GaugeCharacterBranch.coefficient z b : ℂ) * Char b.1) := by
  classical
  let f : GaugeCharacterBranch T → ℝ := fun b =>
    GaugeCharacterBranch.coefficient z b * ‖Char b.1‖
  have hf_nonneg (b : GaugeCharacterBranch T) : 0 ≤ f b := by
    dsimp [f, GaugeCharacterBranch.coefficient]
    exact mul_nonneg
      (Finset.prod_nonneg fun _ _ => hweight_nonneg _)
      (norm_nonneg _)
  have hf_fiber (j : {j : E → ℤ // RootedTreeGauge.CoClosed T j}) :
      Summable (fun q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ =>
        f (⟨j, q⟩ : GaugeCharacterBranch T)) := by
    have hweights :=
      (hasSum_fin_inactiveWeight_one z hnorm hweight_nonneg
        (Fintype.card {e : E // j.1 e = 0})).summable
    exact hweights.mul_right ‖Char j‖
  have hf_fiber_tsum (j : {j : E → ℤ // RootedTreeGauge.CoClosed T j}) :
      (∑' q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ,
        f (⟨j, q⟩ : GaugeCharacterBranch T)) = ‖Char j‖ := by
    have hweights := hasSum_fin_inactiveWeight_one z hnorm hweight_nonneg
      (Fintype.card {e : E // j.1 e = 0})
    have hscaled := hweights.mul_right ‖Char j‖
    change (∑' q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ,
      (∏ i, inactiveWeight z (q i)) * ‖Char j‖) = ‖Char j‖
    simpa using hscaled.tsum_eq
  have hf_outer : Summable (fun j : {j : E → ℤ // RootedTreeGauge.CoClosed T j} =>
      ∑' q : Fin (Fintype.card {e : E // j.1 e = 0}) → ℕ,
        f (⟨j, q⟩ : GaugeCharacterBranch T)) := by
    refine hChar.norm.congr ?_
    intro j
    exact (hf_fiber_tsum j).symm
  have hf_sigma : Summable f :=
    (summable_sigma_of_nonneg hf_nonneg).2 ⟨hf_fiber, hf_outer⟩
  refine Summable.of_norm_bounded hf_sigma ?_
  intro b
  calc
    ‖(GaugeCharacterBranch.coefficient z b : ℂ) * Char b.1‖ =
        GaugeCharacterBranch.coefficient z b * ‖Char b.1‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (show 0 ≤ GaugeCharacterBranch.coefficient z b by
              unfold GaugeCharacterBranch.coefficient
              exact Finset.prod_nonneg fun _ _ => hweight_nonneg _)]
    _ = f b := rfl
    _ ≤ f b := le_rfl

/-- Absolutely convergent regrouping of the signed-character branches over
co-closed integer link fields. The Gaussian majorant is obtained after the
proved circulation/chord equivalence, while inactive source-link modes have
total mass one. -/
theorem gaugeCharacterRegroup_hasSum
    (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (hA : A.PosDef) (w : T.Chord → ℂ) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q) :
    HasSum (fun b : GaugeCharacterBranch T =>
      (GaugeCharacterBranch.coefficient z b : ℂ) *
        dualQuadraticExp A w (T.restrictChord b.1.1))
      (∑' j : {j : E → ℤ // RootedTreeGauge.CoClosed T j},
        dualQuadraticExp A w (T.restrictChord j.1)) := by
  let Char : {j : E → ℤ // RootedTreeGauge.CoClosed T j} → ℂ :=
    fun j => dualQuadraticExp A w (T.restrictChord j.1)
  have hChar : Summable Char := by
    let e := RootedTreeGauge.circulationEquiv (R := ℤ) T
    have hcomp : Summable (Char ∘ e) := by
      refine (summable_dual_quadratic_exp A hA w).congr ?_
      intro k
      change dualQuadraticExp A w k = Char (e k)
      change dualQuadraticExp A w k =
        dualQuadraticExp A w (T.restrictChord (e k).1)
      have hres : T.restrictChord (e k).1 = k := by
        change T.restrictChord (RootedTreeGauge.cycleExtension (R := ℤ) T k) = k
        exact RootedTreeGauge.restrict_cycleExtension (R := ℤ) T k
      exact (congrArg (dualQuadraticExp A w) hres).symm
    exact (Equiv.summable_iff (f := Char) e).mp hcomp
  apply HasSum.sigma_of_hasSum hChar.hasSum
  · intro j
    simpa [Char, GaugeCharacterBranch.coefficient] using
      gaugeCharacterBranch_fiber_hasSum T z hnorm hweight_nonneg j Char
  · exact gaugeCharacterBranch_absSummable T z hnorm hweight_nonneg Char hChar

/-- The real branch weight in the finite source-link model. -/
noncomputable def gaugeBranchMass (T : RootedTreeGauge V E)
    (A : Matrix T.Chord T.Chord ℝ) (z : ℕ → ℝ)
    (b : GaugeCharacterBranch T) : ℝ :=
  GaugeCharacterBranch.coefficient z b *
    dualGaussianWeight A (T.restrictChord b.1.1)

/-- The tested branch character divided by the zero-shift branch weight. -/
noncomputable def gaugeBranchMoment (T : RootedTreeGauge V E)
    (A : Matrix T.Chord T.Chord ℝ) (τ : T.Chord → ℝ) (t : ℝ)
    (b : GaugeCharacterBranch T) : ℂ :=
  dualQuadraticExp A (realTiltParameter τ t) (T.restrictChord b.1.1) /
    (dualGaussianWeight A (T.restrictChord b.1.1) : ℂ)


/-- The normalized all-link outer moment agrees with the tested Poisson
ratio in the finite gauge model. -/
theorem gauge_hOuterMoment_of_model
    (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (hA : A.PosDef) (τ : T.Chord → ℝ) (t : ℝ) (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q) :
    testedExpectation A τ t =
      (∑' b : GaugeCharacterBranch T,
        (gaugeBranchMass T A z b : ℂ) * gaugeBranchMoment T A τ t b) /
        (xi A : ℂ) := by
  let w := realTiltParameter τ t
  let Char : {j : E → ℤ // RootedTreeGauge.CoClosed T j} → ℂ :=
    fun j => dualQuadraticExp A w (T.restrictChord j.1)
  have hReg := gaugeCharacterRegroup_hasSum T A hA w z hnorm hweight_nonneg
  have hBranch (b : GaugeCharacterBranch T) :
      (gaugeBranchMass T A z b : ℂ) * gaugeBranchMoment T A τ t b =
        (GaugeCharacterBranch.coefficient z b : ℂ) *
          dualQuadraticExp A w (T.restrictChord b.1.1) := by
    have hweight :
        (dualGaussianWeight A (T.restrictChord b.1.1) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
    rw [gaugeBranchMass, gaugeBranchMoment, Complex.ofReal_mul]
    field_simp [hweight]
    rfl
  have hsum :
      (∑' b : GaugeCharacterBranch T,
        (gaugeBranchMass T A z b : ℂ) * gaugeBranchMoment T A τ t b) =
        ∑' j : {j : E → ℤ // RootedTreeGauge.CoClosed T j}, Char j := by
    calc
      _ = ∑' b : GaugeCharacterBranch T,
          (GaugeCharacterBranch.coefficient z b : ℂ) *
            dualQuadraticExp A w (T.restrictChord b.1.1) := tsum_congr hBranch
      _ = _ := hReg.tsum_eq
  let e := RootedTreeGauge.circulationEquiv (R := ℤ) T
  have hNum :
      (∑' j : {j : E → ℤ // RootedTreeGauge.CoClosed T j}, Char j) =
        ∑' k : T.Chord → ℤ, dualQuadraticExp A w k := by
    calc
      _ = ∑' k : T.Chord → ℤ, Char (e k) := (e.tsum_eq Char).symm
      _ = ∑' k : T.Chord → ℤ, dualQuadraticExp A w k := by
        apply tsum_congr
        intro k
        change dualQuadraticExp A w (T.restrictChord (e k).1) = _
        have hres : T.restrictChord (e k).1 = k := by
          change T.restrictChord (RootedTreeGauge.cycleExtension (R := ℤ) T k) = k
          exact RootedTreeGauge.restrict_cycleExtension (R := ℤ) T k
        rw [hres]
  rw [tested_poisson_ratio A hA τ t]
  rw [hsum, hNum]

end FroehlichSpencer.FS82.Poisson
