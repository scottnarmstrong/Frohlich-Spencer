/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.SourceModel
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Per-assignment form of the tested Poisson identity
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Poisson

noncomputable section

variable {E J : Type*} [Fintype E]

/-- A signed-current branch with a positive mode assigned at every zero link. -/
abbrev ModeBranch (current : J → E → ℤ) :=
  Σ j : J, (Fin (Fintype.card {e : E // current j e = 0}) → ℕ)

/-- The per-link mode assignment carried by a signed-current branch. -/
def ModeBranch.assignment (current : J → E → ℤ) (b : ModeBranch current) : E → ℕ :=
  fun e => if h : current b.1 e = 0 then
      b.2 (Fintype.equivFin {x : E // current b.1 x = 0} ⟨e, h⟩)
    else (current b.1 e).natAbs - 1

/-- The sign/selection pattern of a signed current. -/
def ModeBranch.selectionCode (current : J → E → ℤ) (b : ModeBranch current) :
    E → Option Bool :=
  fun e => if current b.1 e = 0 then none else some (decide (0 < current b.1 e))

/-- The only currents over a fixed assignment are zero and its two signed
positive modes. -/
private theorem modeBranch_current_eq_code (current : J → E → ℤ)
    (b : ModeBranch current) (q : E → ℕ)
    (hq : b.assignment current = q) (e : E) :
    current b.1 e =
      match b.selectionCode current e with
      | none => 0
      | some true => ((q e + 1 : ℕ) : ℤ)
      | some false => -((q e + 1 : ℕ) : ℤ) := by
  classical
  by_cases hzero : current b.1 e = 0
  · simp [ModeBranch.selectionCode, hzero]
  · have hmode : (current b.1 e).natAbs - 1 = q e := by
      have h := congrFun hq e
      simpa [ModeBranch.assignment, hzero] using h
    have habs : (current b.1 e).natAbs = q e + 1 := by omega
    by_cases hnonneg : 0 ≤ current b.1 e
    · have hcast := Int.natAbs_of_nonneg hnonneg
      have hcur : current b.1 e = ((q e + 1 : ℕ) : ℤ) := by
        calc
          current b.1 e = ((current b.1 e).natAbs : ℤ) := hcast.symm
          _ = ((q e + 1 : ℕ) : ℤ) := by exact_mod_cast habs
      have hpos : 0 < current b.1 e := by omega
      simpa [ModeBranch.selectionCode, hzero, hpos] using hcur
    · have hnonneg' : 0 ≤ -(current b.1 e) := by omega
      have hcast := Int.natAbs_of_nonneg hnonneg'
      have hnat : (-(current b.1 e)).natAbs = (current b.1 e).natAbs := by
        rw [Int.natAbs_neg]
      have hcur : current b.1 e = -((q e + 1 : ℕ) : ℤ) := by
        have hnat' : (-(current b.1 e)).natAbs = q e + 1 := hnat.trans habs
        have hcast' : ((-(current b.1 e)).natAbs : ℤ) = ((q e + 1 : ℕ) : ℤ) := by
          exact_mod_cast hnat'
        calc
          current b.1 e = -((-(current b.1 e)).natAbs : ℤ) := by
            rw [hcast]
            ring
          _ = -((q e + 1 : ℕ) : ℤ) := by
            rw [hcast']
      have hnotpos : ¬ 0 < current b.1 e := by omega
      simpa [ModeBranch.selectionCode, hzero, hnotpos] using hcur

/-- A fixed assignment has only the finitely many choices of selected links
and signs. The current is determined by this code, and the inactive-mode
vector is then determined by the assignment. -/
theorem modeBranch_assignmentFiber_finite (current : J → E → ℤ)
    (hinj : Function.Injective current) (q : E → ℕ) :
    Finite {b : ModeBranch current // b.assignment current = q} := by
  classical
  let code : {b : ModeBranch current // b.assignment current = q} → E → Option Bool :=
    fun b => b.1.selectionCode current
  have hcode : Function.Injective code := by
    intro b b' h
    apply Subtype.ext
    cases b with
    | mk br hb =>
      cases br with
      | mk j modes =>
        cases b' with
        | mk br' hb' =>
          cases br' with
          | mk j' modes' =>
            change ModeBranch.selectionCode current ⟨j, modes⟩ =
              ModeBranch.selectionCode current ⟨j', modes'⟩ at h
            have hbase : j = j' := hinj (by
              funext e
              rw [modeBranch_current_eq_code current ⟨j, modes⟩ q hb e,
                modeBranch_current_eq_code current ⟨j', modes'⟩ q hb' e]
              rw [congrFun h e])
            cases hbase
            change (⟨j, modes⟩ : ModeBranch current) = ⟨j, modes'⟩
            have hmode : modes = modes' := by
              funext i
              let e0 := (Fintype.equivFin {e : E // current j e = 0}).symm i
              have h₁ := congrFun hb e0.1
              have h₂ := congrFun hb' e0.1
              have hzero : current j e0.1 = 0 := e0.2
              simpa [ModeBranch.assignment, hzero, e0] using h₁.trans h₂.symm
            exact Sigma.ext (β := fun j =>
              Fin (Fintype.card {e : E // current j e = 0}) → ℕ) rfl (by
                cases hmode
                rfl)
  exact Finite.of_injective code hcode


set_option linter.style.haveILetI false in

/-- A finite sum over one assignment fiber. -/
noncomputable def assignmentFiberMoment {B Q : Type*}
    (assignment : B → Q)
    (relativeCoefficient : Q → B → ℝ) (branchMoment : B → ℂ) (q : Q) : ℂ := by
  exact ∑' b : {b : B // assignment b = q},
    ((relativeCoefficient q b.1 : ℂ) * branchMoment b.1)

set_option linter.style.haveILetI false in
/-- Regroup an absolutely summable branch family by a finite assignment
partition and factor out the assignment coefficient. -/
theorem hasSum_assignment_factor {B Q : Type*}
    (assignment : B → Q) (hfinite : ∀ q, Finite {b : B // assignment b = q})
    (coefficient : B → ℝ) (outerCoefficient : Q → ℝ)
    (relativeCoefficient : Q → B → ℝ) (branchMoment : B → ℂ) (s : ℂ)
    (hfactor : ∀ b, coefficient b =
      outerCoefficient (assignment b) * relativeCoefficient (assignment b) b)
    (hsum : HasSum (fun b => (coefficient b : ℂ) * branchMoment b) s) :
    HasSum (fun q => (outerCoefficient q : ℂ) *
      assignmentFiberMoment assignment relativeCoefficient branchMoment q) s := by
  classical
  let fiber := fun q : Q => {b : B // assignment b = q}
  let e : (q : Q) × fiber q ≃ B := Equiv.sigmaFiberEquiv assignment
  have hReindex : HasSum (fun p : (q : Q) × fiber q =>
      (coefficient (e p) : ℂ) * branchMoment (e p)) s :=
    e.hasSum_iff.mpr hsum
  have hGrouped : HasSum (fun q : Q =>
      ∑' b : fiber q, (coefficient b.1 : ℂ) * branchMoment b.1) s := by
    apply hReindex.sigma
    intro q
    haveI : Finite (fiber q) := hfinite q
    haveI : Fintype (fiber q) := Fintype.ofFinite _
    simpa [e, fiber] using
      (hasSum_fintype (fun b : fiber q =>
        (coefficient b.1 : ℂ) * branchMoment b.1))
  have hFiber (q : Q) :
      (∑' b : fiber q, (coefficient b.1 : ℂ) * branchMoment b.1) =
        (outerCoefficient q : ℂ) *
          assignmentFiberMoment assignment relativeCoefficient branchMoment q := by
    haveI : Finite (fiber q) := hfinite q
    haveI : Fintype (fiber q) := Fintype.ofFinite _
    simp only [assignmentFiberMoment, tsum_fintype]
    calc
      _ = ∑ b : fiber q,
          (outerCoefficient q : ℂ) *
            ((relativeCoefficient q b.1 : ℂ) * branchMoment b.1) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hq : assignment b.1 = q := b.2
          rw [hfactor b.1, hq, Complex.ofReal_mul]
          ring
      _ = (outerCoefficient q : ℂ) *
          ∑ b : fiber q, (relativeCoefficient q b.1 : ℂ) * branchMoment b.1 :=
            (Finset.mul_sum ..).symm
  convert hGrouped using 1
  funext q
  exact (hFiber q).symm

/--
The branch coefficient, in the common mode-branch presentation.
-/
def ModeBranch.coefficient (current : J → E → ℤ) (z : ℕ → ℝ)
    (b : ModeBranch current) : ℝ :=
  ∏ i, inactiveWeight z (b.2 i)

/-- Outer Poisson weight associated with a per-link assignment. -/
def assignmentCoefficient (z : ℕ → ℝ) (q : E → ℕ) : ℝ :=
  ∏ e, inactiveWeight z (q e)

/-- The relative finite Fourier coefficient of a branch within its assignment
fiber. -/
def assignmentRelativeCoefficient {current : J → E → ℤ}
    (z : ℕ → ℝ) (q : E → ℕ) (b : ModeBranch current) : ℝ :=
  ModeBranch.coefficient current z b / assignmentCoefficient z q

/-- In a fixed assignment fiber, the relative branch coefficient is the
product of `z/2` over the selected links. -/
theorem modeBranch_relativeCoefficient_eq_selectedProduct
    (current : J → E → ℤ) (z : ℕ → ℝ) (q : E → ℕ)
    (b : ModeBranch current) (hb : b.assignment current = q)
    (hz : ∀ n, 0 < z (positiveMode n)) :
    assignmentRelativeCoefficient z q b =
      ∏ e ∈ (Finset.univ.filter fun e : E => current b.1 e ≠ 0),
        z (positiveMode (q e)) / 2 := by
  classical
  let zeroEdges : Finset E := Finset.univ.filter fun e => current b.1 e = 0
  let selectedEdges : Finset E := Finset.univ.filter fun e => current b.1 e ≠ 0
  let zeroWeight : ℝ := ∏ e ∈ zeroEdges, inactiveWeight z (q e)
  let selectedWeight : ℝ := ∏ e ∈ selectedEdges, inactiveWeight z (q e)
  let zeros := {e : E // current b.1 e = 0}
  let eFin : zeros ≃ Fin (Fintype.card zeros) := Fintype.equivFin zeros
  have hmode (i : Fin (Fintype.card zeros)) :
      b.2 i = q ((eFin.symm i).1) := by
    let e0 := eFin.symm i
    have hzero : current b.1 e0.1 = 0 := e0.2
    have hidx : eFin e0 = i := Equiv.apply_symm_apply eFin i
    have h := congrFun hb e0.1
    simpa [ModeBranch.assignment, zeros, eFin, e0, hzero, hidx] using h
  have hcoeff : ModeBranch.coefficient current z b = zeroWeight := by
    unfold ModeBranch.coefficient
    calc
      _ = ∏ i : Fin (Fintype.card zeros), inactiveWeight z (q ((eFin.symm i).1)) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [hmode]
      _ = ∏ e : zeros, inactiveWeight z (q e.1) := by
            simpa [eFin, zeros] using
              (Equiv.prod_comp eFin.symm
                (fun e : zeros => inactiveWeight z (q e.1)))
      _ = zeroWeight := by
            unfold zeroWeight zeroEdges
            symm
            apply Finset.prod_subtype
            · intro e
              simp
  have hsplit : zeroWeight * selectedWeight = assignmentCoefficient z q := by
    unfold zeroWeight selectedWeight zeroEdges selectedEdges assignmentCoefficient
    simpa [ne_eq] using
      (Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset E)
        (fun e => current b.1 e = 0) (fun e => inactiveWeight z (q e)))
  have hweight_pos (e : E) : 0 < inactiveWeight z (q e) := by
    simpa [inactiveWeight, positiveMode] using
      (div_pos (by norm_num : (0 : ℝ) < 2) (hz (q e)))
  have hzero_pos : 0 < zeroWeight := by
    unfold zeroWeight
    apply Finset.prod_pos
    intro e he
    exact hweight_pos e
  have hselected_pos : 0 < selectedWeight := by
    unfold selectedWeight
    apply Finset.prod_pos
    intro e he
    exact hweight_pos e
  have hrelative : assignmentRelativeCoefficient z q b = selectedWeight⁻¹ := by
    unfold assignmentRelativeCoefficient
    rw [hcoeff, ← hsplit]
    field_simp [ne_of_gt hzero_pos, ne_of_gt hselected_pos]
  calc
    assignmentRelativeCoefficient z q b = selectedWeight⁻¹ := hrelative
    _ = ∏ e ∈ selectedEdges, (inactiveWeight z (q e))⁻¹ := by
      unfold selectedWeight
      symm
      exact Finset.prod_inv_distrib (s := selectedEdges)
        (fun e => inactiveWeight z (q e))
    _ = ∏ e ∈ selectedEdges, z (positiveMode (q e)) / 2 := by
      apply Finset.prod_congr rfl
      intro e he
      unfold inactiveWeight positiveMode
      have hz' : z (q e + 1) ≠ 0 := ne_of_gt (hz (q e))
      field_simp [hz']


/-- Every assignment has strictly positive outer coefficient when the source
mode weights are positive. -/
theorem assignmentCoefficient_pos (z : ℕ → ℝ) (q : E → ℕ)
    (hz : ∀ n, 0 < z (positiveMode n)) : 0 < assignmentCoefficient z q := by
  unfold assignmentCoefficient
  apply Finset.prod_pos
  intro e he
  simpa [inactiveWeight, positiveMode] using
    (div_pos (by norm_num : (0 : ℝ) < 2) (hz (q e)))


set_option linter.style.haveILetI false in


/--
co-closed source branches carry the same per-link assignment map.
-/
def GaugeCharacterBranch.assignment {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {T : RootedTreeGauge V E}
    (b : GaugeCharacterBranch T) : E → ℕ :=
  ModeBranch.assignment (fun j : {j : E → ℤ // RootedTreeGauge.CoClosed T j} => j.1) b


/-- The source assignment fiber is finite: a fixed mode assignment leaves
only the selected subset and its two signs at each selected link. -/
theorem gaugeCharacterBranch_assignmentFiber_finite {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (T : RootedTreeGauge V E) (q : E → ℕ) :
    Finite {b : GaugeCharacterBranch T // b.assignment = q} := by
  simpa [GaugeCharacterBranch.assignment, GaugeCharacterBranch, ModeBranch] using
    (modeBranch_assignmentFiber_finite
      (fun j : {j : E → ℤ // RootedTreeGauge.CoClosed T j} => j.1)
      (by intro a b h; exact Subtype.ext h) q)

/--
Relative source coefficient within one assignment fiber.
-/
def GaugeCharacterBranch.assignmentRelativeCoefficient {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {T : RootedTreeGauge V E} (z : ℕ → ℝ) (q : E → ℕ)
    (b : GaugeCharacterBranch T) : ℝ :=
  GaugeCharacterBranch.coefficient z b / assignmentCoefficient z q

/-- The finite co-closed character expansion for a source mode assignment. -/
noncomputable def gaugeAssignmentMoment {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (T : RootedTreeGauge V E)
    (A : Matrix T.Chord T.Chord ℝ) (τ : T.Chord → ℝ) (t : ℝ)
    (z : ℕ → ℝ) (q : E → ℕ) : ℂ :=
  assignmentFiberMoment (GaugeCharacterBranch.assignment (T := T))
    (GaugeCharacterBranch.assignmentRelativeCoefficient (T := T) z)
    (fun b => dualQuadraticExp A (realTiltParameter τ t)
      (T.restrictChord b.1.1)) q

/--
The relative coefficient is the product of `z/2` on selected source
links, so the finite sum is the signed-character expansion of the cosine
product.
-/
theorem gaugeCharacterBranch_assignmentRelativeCoefficient_eq_selectedProduct
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {T : RootedTreeGauge V E} (z : ℕ → ℝ) (q : E → ℕ)
    (b : GaugeCharacterBranch T) (hb : b.assignment = q)
    (hz : ∀ n, 0 < z (positiveMode n)) :
    GaugeCharacterBranch.assignmentRelativeCoefficient z q b =
      ∏ e ∈ (Finset.univ.filter fun e : E => b.1.1 e ≠ 0),
        z (positiveMode (q e)) / 2 := by
  change assignmentRelativeCoefficient z q b =
    ∏ e ∈ (Finset.univ.filter fun e : E => b.1.1 e ≠ 0),
      z (positiveMode (q e)) / 2
  exact modeBranch_relativeCoefficient_eq_selectedProduct
    (fun j : {j : E → ℤ // RootedTreeGauge.CoClosed T j} => j.1)
    z q b hb hz

/--
specialized to a per-assignment outer sum on the actual FS82 source
carrier.

Each `gaugeAssignmentMoment` is the finite signed-character
expansion; measure integral identification is a separate bridge.
-/
theorem source_testedExpectation_eq_tsum_assignment
    {B : Cubical.Box 4} (origin : Fin 4 → ℤ) {β : ℝ} (hβ : 0 < β)
    (τ : (sourceRootedTree B).Chord → ℝ) (t : ℝ)
    (z : ℕ → ℝ) (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q)) :
    sourceFiniteModelTestedExpectation (B := B) origin β τ t =
      (∑' q : SourcePoissonEdge B → ℕ,
        (assignmentCoefficient z q : ℂ) *
          gaugeAssignmentMoment (sourceRootedTree B)
            (scaledChordMatrix (sourceRootedTree B)
              (sourceFinitePoissonModel (B := B) origin) β) τ t z q) /
        (xi (scaledChordMatrix (sourceRootedTree B)
          (sourceFinitePoissonModel (B := B) origin) β) : ℂ) := by
  let T := sourceRootedTree B
  let A := scaledChordMatrix T (sourceFinitePoissonModel (B := B) origin) β
  let w := realTiltParameter τ t
  have hA : A.PosDef := by
    dsimp [A, T]
    exact scaledChordMatrix_posDef (sourceRootedTree B)
      (sourceFinitePoissonModel (B := B) origin) hβ
  have hReg := gaugeCharacterRegroup_hasSum T A hA w z hnorm hweight_nonneg
  have hfactor (b : GaugeCharacterBranch T) :
      GaugeCharacterBranch.coefficient z b =
        assignmentCoefficient z (b.assignment) *
          GaugeCharacterBranch.assignmentRelativeCoefficient z b.assignment b := by
    have hc : assignmentCoefficient z b.assignment ≠ 0 :=
      ne_of_gt (assignmentCoefficient_pos z b.assignment hz)
    unfold GaugeCharacterBranch.assignmentRelativeCoefficient
    field_simp
  have hGrouped := hasSum_assignment_factor (GaugeCharacterBranch.assignment (T := T))
    (fun q => gaugeCharacterBranch_assignmentFiber_finite T q)
    (fun b => GaugeCharacterBranch.coefficient z b)
    (fun q => assignmentCoefficient z q)
    (GaugeCharacterBranch.assignmentRelativeCoefficient z)
    (fun b => dualQuadraticExp A w (T.restrictChord b.1.1)) _ hfactor hReg
  have hGrouped' : HasSum (fun q : SourcePoissonEdge B → ℕ =>
      (assignmentCoefficient z q : ℂ) * gaugeAssignmentMoment T A τ t z q)
      (∑' j : {j : SourcePoissonEdge B → ℤ //
        RootedTreeGauge.CoClosed T j},
        dualQuadraticExp A w (T.restrictChord j.1)) := by
    simpa [gaugeAssignmentMoment] using hGrouped
  have hBranch (b : GaugeCharacterBranch T) :
      (gaugeBranchMass T A z b : ℂ) * gaugeBranchMoment T A τ t b =
        (GaugeCharacterBranch.coefficient z b : ℂ) *
          dualQuadraticExp A w (T.restrictChord b.1.1) := by
    have hweight :
        (dualGaussianWeight A (T.restrictChord b.1.1) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
    rw [gaugeBranchMass, gaugeBranchMoment, Complex.ofReal_mul]
    field_simp [hweight]
    rfl
  have hBranchSum :
      (∑' b : GaugeCharacterBranch T,
        (gaugeBranchMass T A z b : ℂ) * gaugeBranchMoment T A τ t b) =
      ∑' q : SourcePoissonEdge B → ℕ,
        (assignmentCoefficient z q : ℂ) * gaugeAssignmentMoment T A τ t z q := by
    calc
      _ = ∑' b : GaugeCharacterBranch T,
          (GaugeCharacterBranch.coefficient z b : ℂ) *
            dualQuadraticExp A w (T.restrictChord b.1.1) := by
              apply tsum_congr
              intro b
              exact hBranch b
      _ = _ := hReg.tsum_eq.trans hGrouped'.tsum_eq.symm
  rw [source_hOuterMoment (B := B) origin hβ τ t z hnorm hweight_nonneg]
  rw [hBranchSum]

end

end FroehlichSpencer.FS82.Poisson

end
