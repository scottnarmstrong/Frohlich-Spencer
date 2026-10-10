/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.CurrentExpansion
public import FroehlichSpencer.FS82.ZN.Model
public import FroehlichSpencer.FS82.ZN.Convergence
public import FroehlichSpencer.FS82.Cubical.UnitBox
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# FS82 §3 countable Wilson mode assignments

This module assembles the absolutely summable one-link mixtures over a finite
link carrier and records their fixed-assignment finite-current expansion.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.ZN

open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Wilson
open MeasureTheory
open Filter
open scoped Topology

local instance assignmentSum_fact_one : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩


/-- The source integral definition of the positive cosine coefficient, written
against normalized Haar measure on the unit circle. -/
@[expose] noncomputable def sourceWilsonLambdaIntegral
    (N q : ℕ) (h : NNReal) : ℝ :=
  2 * pinningNormalization N h *
    ∫ z : UnitAddCircle,
      Real.exp ((h : ℝ) * circleCosCharacter N z) * circleCosCharacter (q * N) z
        ∂AddCircle.haarAddCircle


private theorem summable_mul_prod {α : Type*} {f : ℕ → ℝ} {g : α → ℝ}
    (hf : Summable f) (hg : Summable g) :
    Summable (fun p : ℕ × α => f p.1 * g p.2) := by
  have hnorm : Summable (fun p : ℕ × α => ‖f p.1‖ * ‖g p.2‖) := by
    apply (summable_prod_of_nonneg (f := fun p : ℕ × α => ‖f p.1‖ * ‖g p.2‖)
      (by intro p; positivity)).2
    refine ⟨?_, ?_⟩
    · intro a
      simpa using (hg.norm.mul_left ‖f a‖)
    · convert hf.norm.mul_right (∑' b : α, ‖g b‖) using 1
      ext a
      change (∑' b : α, ‖f a‖ * ‖g b‖) = _
      rw [tsum_mul_left]
  exact Summable.of_norm_bounded hnorm (by intro p; simp)

private theorem hasSum_finPiProd : ∀ (n : ℕ) (f : Fin n → ℕ → ℝ),
    (∀ i, Summable (f i)) →
      HasSum (fun m : Fin n → ℕ => ∏ i, f i (m i))
        (∏ i, ∑' q, f i q) := by
  intro n
  induction n with
  | zero =>
      intro f hf
      let x : Fin 0 → ℕ := fun i => Fin.elim0 i
      have hterm : (fun m : Fin 0 → ℕ => ∏ i, f i (m i)) =
          fun m => if m = x then 1 else 0 := by
        funext m
        have hm : m = x := Subsingleton.elim _ _
        simp [hm]
      rw [hterm]
      simpa using (hasSum_ite_eq x (1 : ℝ))
  | succ n ih =>
      intro f hf
      let g : Fin n → ℕ → ℝ := fun i => f i.succ
      have hg : ∀ i, Summable (g i) := fun i => hf i.succ
      have htail := ih g hg
      have hpair := summable_mul_prod (hf 0) htail.summable
      have hpairsum := (hf 0).hasSum.mul htail hpair
      let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
      have hterm (a : ℕ) (b : Fin n → ℕ) :
          (∏ i : Fin (n + 1), f i (e (a, b) i)) =
            f 0 a * ∏ i : Fin n, f i.succ (b i) := by
        simp [e, Fin.prod_univ_succ]
      have hassignFun :
          (fun m : Fin (n + 1) → ℕ => ∏ i, f i (m i)) =
          (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)) ∘ e.symm := by
        funext m
        have hp := hterm (e.symm m).1 (e.symm m).2
        rw [e.apply_symm_apply] at hp
        simpa using hp
      have hassign : HasSum (fun m : Fin (n + 1) → ℕ => ∏ i, f i (m i))
          (∏ i : Fin (n + 1), ∑' q, f i q) := by
        have hpre := e.symm.hasSum_iff.mpr hpairsum
        rw [hassignFun]
        convert hpre using 1
        simp [Fin.prod_univ_succ, g]
      exact hassign

private theorem hasSum_fintypePiProd {α : Type*} [Fintype α]
    (f : α → ℕ → ℝ) (hf : ∀ a, Summable (f a)) :
    HasSum (fun m : α → ℕ => ∏ a, f a (m a)) (∏ a, ∑' q, f a q) := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let f' : Fin (Fintype.card α) → ℕ → ℝ := fun i => f (e.symm i)
  have hf' : ∀ i, Summable (f' i) := fun i => hf (e.symm i)
  have hfin := hasSum_finPiProd (Fintype.card α) f' hf'
  let e' : (Fin (Fintype.card α) → ℕ) ≃ (α → ℕ) :=
    Equiv.arrowCongr e.symm (Equiv.refl ℕ)
  have hpre := e'.symm.hasSum_iff.mpr hfin
  convert hpre using 1
  · funext m
    change (∏ a, f a (m a)) =
      ∏ i : Fin (Fintype.card α), f (e.symm i) (m (e.symm i))
    exact (e.symm.prod_comp (fun a => f a (m a))).symm
  · change (∏ a, ∑' q, f a q) =
      ∏ i : Fin (Fintype.card α), ∑' q, f (e.symm i) q
    exact (e.symm.prod_comp (fun a => ∑' q, f a q)).symm

/-- One link's `q ≥ 1` summand in the source's geometric mixture (3.13). -/
@[expose] noncomputable def wilsonAssignmentLinkTerm
    (epsilon : ℝ) (N : ℕ) (h θ : ℝ) (q : ℕ) : ℝ :=
  (wilsonSplittingWeight epsilon q)⁻¹ *
    (1 + wilsonSplittingWeight epsilon q *
      wilsonCharacterCoefficient N (q + 1) h *
        Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ)))

/-- The weighted term for one positive mode assignment on the finite link
carrier used by the §2 fixed-frequency current API. -/
@[expose] noncomputable def wilsonModeAssignmentTerm {B : Box 4}
    (epsilon : ℝ) (N : ℕ) (h : ℝ) (φ : Link B → ℝ)
    (m : Link B → ℕ) : ℝ :=
  ∏ e : Link B, wilsonAssignmentLinkTerm epsilon N h (φ e) (m e)

/-- The source's geometric coefficient `c_m` for a mode assignment. -/
@[expose] noncomputable def wilsonModeAssignmentCoefficient {B : Box 4}
    (epsilon : ℝ) (m : Link B → ℕ) : ℝ :=
  ∏ e : Link B, (wilsonSplittingWeight epsilon (m e))⁻¹

/-- The one-link mixture is absolutely summable: its summands equal the
normalized geometric weight plus the absolutely summable Fourier cosine term. -/
theorem summable_wilsonAssignmentLinkTerm {epsilon : ℝ} {N : ℕ} {h θ : ℝ}
    (hepsilon : 0 < epsilon) (hh : 0 ≤ h) :
    Summable (wilsonAssignmentLinkTerm epsilon N h θ) := by
  have hw := wilsonSplittingWeight_inv_tsum hepsilon
  have hcos := summable_wilsonCosineMode (N := N) (h := h)
    (θ := θ) hh
  have hterm (q : ℕ) : wilsonAssignmentLinkTerm epsilon N h θ q =
      (wilsonSplittingWeight epsilon q)⁻¹ +
        wilsonCharacterCoefficient N (q + 1) h *
          Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ)) := by
    unfold wilsonAssignmentLinkTerm
    exact wilsonSplittingFactor_identity
      (wilsonSplittingWeight_pos hepsilon).ne'
  exact (hw.1.add hcos).congr (fun q => (hterm q).symm)

/-- The full finite product of one-link mixtures is the absolutely convergent
countable sum over all assignments `m : Link B → ℕ`. -/
theorem wilsonModeAssignment_hasSum {B : Box 4} {epsilon : ℝ} {N : ℕ}
    {h : ℝ} (φ : Link B → ℝ) (hepsilon : 0 < epsilon) (hh : 0 ≤ h) :
    HasSum (wilsonModeAssignmentTerm epsilon N h φ)
      (∏ e : Link B,
        (1 + ∑' q : ℕ,
          wilsonCharacterCoefficient N (q + 1) h *
            Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e)))) := by
  classical
  have hlink (e : Link B) : Summable (wilsonAssignmentLinkTerm epsilon N h (φ e)) :=
    summable_wilsonAssignmentLinkTerm hepsilon hh
  have hsum := hasSum_fintypePiProd
    (fun e q => wilsonAssignmentLinkTerm epsilon N h (φ e) q) hlink
  have hlocal (e : Link B) : HasSum (wilsonAssignmentLinkTerm epsilon N h (φ e))
      (1 + ∑' q : ℕ,
        wilsonCharacterCoefficient N (q + 1) h *
          Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e))) := by
    change HasSum
      (fun q => (wilsonSplittingWeight epsilon q)⁻¹ *
        (1 + wilsonSplittingWeight epsilon q *
          wilsonCharacterCoefficient N (q + 1) h *
            Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e)))) _
    exact wilsonSplittingMixture_hasSum (N := N) (h := h) hepsilon
      (fun q => Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e)))
      (summable_wilsonCosineMode (N := N) (h := h) (θ := φ e) hh)
  have hvalue :
      (∏ e : Link B,
        (1 + ∑' q : ℕ,
          wilsonCharacterCoefficient N (q + 1) h *
            Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e)))) =
        ∏ e : Link B, ∑' q : ℕ, wilsonAssignmentLinkTerm epsilon N h (φ e) q := by
    apply Finset.prod_congr rfl
    intro e he
    exact (hlocal e).tsum_eq.symm
  rw [hvalue]
  exact hsum

/-- Absolute summability of the countable product expansion over all finite-box
link assignments. -/
theorem summable_norm_wilsonModeAssignment {B : Box 4} {epsilon : ℝ} {N : ℕ}
    {h : ℝ} (φ : Link B → ℝ) (hepsilon : 0 < epsilon) (hh : 0 ≤ h) :
    Summable (fun m : Link B → ℕ => ‖wilsonModeAssignmentTerm epsilon N h φ m‖) :=
  (wilsonModeAssignment_hasSum φ hepsilon hh).summable.norm

/--
The hypothesis records the source activity `z_{Nq}=ζ(q)λ(q)` on every link.
-/
theorem wilsonModeAssignment_eq_weightedCurrentExpansion
    {B : Box 4} {N : ℕ} (epsilon h : ℝ) (m : Link B → ℕ)
    (φ : Link B → ℝ) (z : ℤ → ℝ) (T : List (CurrentExpansionTerm B))
    (hprofile : ∀ e,
      z (abs (wilsonModeFrequencyAssignment N m e)) =
        wilsonCoefficientActivity epsilon N (m e) h)
    (hT : IsFixedFrequencyCurrentExpansion
      (wilsonModeFrequencyAssignment N m) z T) :
    wilsonModeAssignmentTerm epsilon N h φ m =
      wilsonModeAssignmentCoefficient epsilon m *
        currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ T := by
  classical
  rw [wilsonModeAssignmentTerm, wilsonModeAssignmentCoefficient]
  rcases hT with ⟨_, _, _, _, _, hidentity, _, _⟩
  have hfactor : ∀ e : Link B,
      wilsonAssignmentLinkTerm epsilon N h (φ e) (m e) =
        (wilsonSplittingWeight epsilon (m e))⁻¹ *
          (1 + z (abs (wilsonModeFrequencyAssignment N m e)) *
            Real.cos (φ e * (wilsonModeFrequencyAssignment N m e : ℝ))) := by
    intro e
    unfold wilsonAssignmentLinkTerm
    rw [hprofile e, wilsonCoefficientActivity]
    have hangle : ((m e + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e) =
        φ e * (wilsonModeFrequencyAssignment N m e : ℝ) := by
      calc
        ((m e + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e) =
            (((m e + 1) * N : ℕ) : ℝ) * φ e := by push_cast; ring
        _ = φ e * (((m e + 1) * N : ℕ) : ℝ) := by ring
        _ = φ e * (wilsonModeFrequencyAssignment N m e : ℝ) := by
          congr 1
    rw [hangle]
  calc
    (∏ e : Link B, wilsonAssignmentLinkTerm epsilon N h (φ e) (m e)) =
        ∏ e : Link B,
          (wilsonSplittingWeight epsilon (m e))⁻¹ *
            (1 + z (abs (wilsonModeFrequencyAssignment N m e)) *
              Real.cos (φ e * (wilsonModeFrequencyAssignment N m e : ℝ))) :=
      Finset.prod_congr rfl (by intro e he; exact hfactor e)
    _ = wilsonModeAssignmentCoefficient epsilon m *
        sourceCurrentProduct (wilsonModeFrequencyAssignment N m) z φ := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = wilsonModeAssignmentCoefficient epsilon m *
        currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ T := by
      rw [hidentity φ]


/-- The outer sum of the finite separated-current expansions is absolutely
summable. Each outer term is the finite sum supplied for that assignment; this
statement does not flatten the finite inner lists into a single index type. -/
theorem wilsonModeAssignment_currentExpansion_hasSum
    {B : Box 4} {N : ℕ} {epsilon h : ℝ} (φ : Link B → ℝ)
    (hepsilon : 0 < epsilon) (hh : 0 ≤ h)
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B))
    (z : ℤ → ℝ)
    (hprofile : ∀ m : Link B → ℕ, ∀ e,
      z (abs (wilsonModeFrequencyAssignment N m e)) =
        wilsonCoefficientActivity epsilon N (m e) h)
    (hT : ∀ m, IsFixedFrequencyCurrentExpansion
      (wilsonModeFrequencyAssignment N m) z (T m)) :
    HasSum (fun m : Link B → ℕ =>
      wilsonModeAssignmentCoefficient epsilon m *
        currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ (T m))
      (∏ e : Link B,
        (1 + ∑' q : ℕ,
          wilsonCharacterCoefficient N (q + 1) h *
            Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e)))) := by
  have hsum := wilsonModeAssignment_hasSum (B := B) (epsilon := epsilon)
    (N := N) (h := h) φ hepsilon hh
  have hterm (m : Link B → ℕ) :
      wilsonModeAssignmentTerm epsilon N h φ m =
        wilsonModeAssignmentCoefficient epsilon m *
          currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ (T m) :=
    wilsonModeAssignment_eq_weightedCurrentExpansion
      epsilon h m φ z (T m) (hprofile m) (hT m)
  convert hsum using 1
  funext m
  exact (hterm m).symm


private theorem list_sum_map_fin {α : Type*} (L : List α) (f : α → ℝ) :
    (L.map f).sum = ∑ i : Fin L.length, f (L.get i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Fin.sum_univ_succ,
        List.get_cons_zero]
      have hs : ∀ i : Fin L.length, (a :: L).get i.succ = L.get i := by
        intro i
        exact List.get_cons_succ (i := i.val) (h := by
          simp only [List.length_cons]
          omega)
      have hsums : (∑ i : Fin L.length, f ((a :: L).get i.succ)) =
          ∑ i : Fin L.length, f (L.get i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hs i]
      rw [hsums, ih]

private theorem currentFactor_abs_le_zero {B : Box 4} (q : Link B → ℤ)
    (z : ℤ → ℝ) (φ : Link B → ℝ) (t : ExpansionLineage B)
    (ha : 0 < lineageCoefficient q z t) :
    |currentFactor q z φ t| ≤ currentFactor q z (fun _ => 0) t := by
  let a := lineageCoefficient q z t
  let x := currentPhase φ (lineageCurrent q t)
  have ha0 : 0 ≤ a := le_of_lt ha
  have hlower : -(1 + a) ≤ 1 + a * Real.cos x := by
    have hc := Real.neg_one_le_cos x
    nlinarith
  have hupper : 1 + a * Real.cos x ≤ 1 + a := by
    have hc := Real.cos_le_one x
    nlinarith
  have habs : |1 + a * Real.cos x| ≤ 1 + a := abs_le.mpr ⟨hlower, hupper⟩
  have hzero : currentFactor q z (fun _ => 0) t = 1 + a := by
    simp [currentFactor, currentPhase, a]
  calc
    |currentFactor q z φ t| = |1 + a * Real.cos x| := by simp [currentFactor, x, a]
    _ ≤ 1 + a := habs
    _ = currentFactor q z (fun _ => 0) t := hzero.symm

private theorem finset_prod_le_of_nonneg {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hfg : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hga := hg a (by simp)
      have hrestf : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (by
        intro i hi
        exact hf i (by simp [hi]))
      exact mul_le_mul (hfg a (by simp))
        (ih (by intro i hi; exact hf i (by simp [hi]))
          (by intro i hi; exact hg i (by simp [hi]))
          (by intro i hi; exact hfg i (by simp [hi]))) hrestf hga

private theorem currentStateProduct_abs_le_zero {B : Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (s : CurrentState B)
    (ha : ∀ t ∈ s, 0 < lineageCoefficient q z t) :
    |currentStateProduct q z φ s| ≤ currentStateProduct q z (fun _ => 0) s := by
  classical
  unfold currentStateProduct
  rw [Finset.abs_prod]
  apply finset_prod_le_of_nonneg
  · intro t ht
    exact abs_nonneg _
  · intro t ht
    have hc := ha t ht
    have hzero : currentFactor q z (fun _ => 0) t =
        1 + lineageCoefficient q z t := by
      simp [currentFactor, currentPhase]
    rw [hzero]
    linarith
  · intro t ht
    exact currentFactor_abs_le_zero q z φ t (ha t ht)

private theorem currentExpansion_variation_le_zero {B : Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (T : List (CurrentExpansionTerm B))
    (hweight : ∀ t ∈ T, 0 < t.weight)
    (hcoeff : ∀ t ∈ T, ∀ u ∈ t.state, 0 < lineageCoefficient q z u) :
    ((T.map fun t => |t.weight * currentStateProduct q z φ t.state|).sum) ≤
      currentExpansionSum q z (fun _ => 0) T := by
  induction T with
  | nil => simp [currentExpansionSum]
  | cons t T ih =>
      simp only [List.map_cons, List.sum_cons, currentExpansionSum]
      have ht := hweight t (by simp)
      have hstate := currentStateProduct_abs_le_zero q z φ t.state (fun u hu =>
        hcoeff t (by simp) u hu)
      have hterm : |t.weight * currentStateProduct q z φ t.state| ≤
          t.weight * currentStateProduct q z (fun _ => 0) t.state := by
        rw [abs_mul, abs_of_pos ht]
        exact mul_le_mul_of_nonneg_left hstate ht.le
      have hih : ((T.map fun u =>
          |u.weight * currentStateProduct q z φ u.state|).sum) ≤
          currentExpansionSum q z (fun _ => 0) T :=
        ih (fun u hu => hweight u (by simp [hu]))
          (fun u hu v hv => hcoeff u (by simp [hu]) v hv)
      exact add_le_add hterm hih

/-- A flattened index for one mode assignment together with one term in that
assignment's finite separated-current list. -/
@[expose] noncomputable def wilsonModeAssignmentCurrentTerm {B : Box 4}
    (N : ℕ)
    (epsilon : ℝ) (φ : Link B → ℝ)
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B)) (z : ℤ → ℝ)
    (p : Σ m : Link B → ℕ, Fin (T m).length) : ℝ :=
  let t := (T p.1).get p.2
  wilsonModeAssignmentCoefficient epsilon p.1 *
    (t.weight * currentStateProduct (wilsonModeFrequencyAssignment N p.1) z φ t.state)

private theorem wilsonModeAssignmentCurrentTerm_inner_bound {B : Box 4} {N : ℕ}
    {epsilon h : ℝ} (φ : Link B → ℝ) (hepsilon : 0 < epsilon)
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B)) (z : ℤ → ℝ)
    (hprofile : ∀ m : Link B → ℕ, ∀ e,
      z (abs (wilsonModeFrequencyAssignment N m e)) =
        wilsonCoefficientActivity epsilon N (m e) h)
    (hT : ∀ m, IsFixedFrequencyCurrentExpansion
      (wilsonModeFrequencyAssignment N m) z (T m))
    (m : Link B → ℕ) :
    (∑ i : Fin (T m).length,
      ‖wilsonModeAssignmentCurrentTerm N epsilon φ T z ⟨m, i⟩‖) ≤
      wilsonModeAssignmentTerm epsilon N h (fun _ => 0) m := by
  classical
  let q := wilsonModeFrequencyAssignment N m
  let c := wilsonModeAssignmentCoefficient epsilon m
  have hc : 0 < c := by
    dsimp [c, wilsonModeAssignmentCoefficient]
    apply Finset.prod_pos
    intro e he
    exact inv_pos.mpr (wilsonSplittingWeight_pos hepsilon)
  rcases hT m with ⟨_, _, _, hweight, _, _, hcoeffPos, _⟩
  have hsumvariation :
      ((T m).map fun t => |t.weight * currentStateProduct q z φ t.state|).sum ≤
        currentExpansionSum q z (fun _ => 0) (T m) :=
    currentExpansion_variation_le_zero q z φ (T m) hweight hcoeffPos
  have hfinite :
      (∑ i : Fin (T m).length,
        ‖c * (((T m).get i).weight * currentStateProduct q z φ ((T m).get i).state)‖) =
      c * ((T m).map fun t => |t.weight * currentStateProduct q z φ t.state|).sum := by
    calc
      _ = ∑ i : Fin (T m).length,
          c * |((T m).get i).weight * currentStateProduct q z φ ((T m).get i).state| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hc]
      _ = c * ∑ i : Fin (T m).length,
          |((T m).get i).weight * currentStateProduct q z φ ((T m).get i).state| := by
        rw [Finset.mul_sum]
      _ = c * ((T m).map fun t => |t.weight * currentStateProduct q z φ t.state|).sum := by
        rw [← list_sum_map_fin (T m) (fun t =>
          |t.weight * currentStateProduct q z φ t.state|)]
  have hle :
      (∑ i : Fin (T m).length,
        ‖c * (((T m).get i).weight * currentStateProduct q z φ ((T m).get i).state)‖) ≤
      c * currentExpansionSum q z (fun _ => 0) (T m) := by
    rw [hfinite]
    exact mul_le_mul_of_nonneg_left hsumvariation hc.le
  have hterm := wilsonModeAssignment_eq_weightedCurrentExpansion
    (B := B) (N := N) epsilon h m (fun _ => 0) z (T m) (hprofile m) (hT m)
  simpa [wilsonModeAssignmentCurrentTerm, q, c] using hle.trans_eq hterm.symm

/-- Absolute summability of the flattened family of all assignment/current
term pairs. At zero field each current factor is positive, and the triangle
bound by that zero-field product is summable by the link-mixture theorem. -/
theorem summable_norm_wilsonModeAssignmentCurrentTerm {B : Box 4} {N : ℕ}
    {epsilon h : ℝ} (φ : Link B → ℝ) (hepsilon : 0 < epsilon) (hh : 0 ≤ h)
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B)) (z : ℤ → ℝ)
    (hprofile : ∀ m : Link B → ℕ, ∀ e,
      z (abs (wilsonModeFrequencyAssignment N m e)) =
        wilsonCoefficientActivity epsilon N (m e) h)
    (hT : ∀ m, IsFixedFrequencyCurrentExpansion
      (wilsonModeFrequencyAssignment N m) z (T m)) :
    Summable (fun p : Σ m : Link B → ℕ, Fin (T m).length =>
      ‖wilsonModeAssignmentCurrentTerm N epsilon φ T z p‖) := by
  classical
  let f : (Σ m : Link B → ℕ, Fin (T m).length) → ℝ :=
    fun p => ‖wilsonModeAssignmentCurrentTerm N epsilon φ T z p‖
  have hf : ∀ p, 0 ≤ f p := fun p => norm_nonneg _
  have hb : ∀ m : Link B → ℕ,
      0 ≤ wilsonModeAssignmentTerm epsilon N h (fun _ => 0) m := by
    intro m
    have hbound := wilsonModeAssignmentCurrentTerm_inner_bound
      φ hepsilon T z hprofile hT m
    have hleft : 0 ≤ ∑ i : Fin (T m).length, f ⟨m, i⟩ :=
      Finset.sum_nonneg (fun i hi => hf ⟨m, i⟩)
    exact hleft.trans hbound
  have houter : Summable (fun m : Link B → ℕ =>
      wilsonModeAssignmentTerm epsilon N h (fun _ => 0) m) := by
    have hs := summable_norm_wilsonModeAssignment
      (B := B) (epsilon := epsilon) (N := N) (h := h) (fun _ => 0) hepsilon hh
    apply hs.congr
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (hb m)]
  have htsumBound : ∀ m : Link B → ℕ,
      (∑' i : Fin (T m).length, f ⟨m, i⟩) ≤
        wilsonModeAssignmentTerm epsilon N h (fun _ => 0) m := by
    intro m
    simpa [f, tsum_fintype] using
      wilsonModeAssignmentCurrentTerm_inner_bound φ hepsilon T z hprofile hT m
  have hsigma := (summable_sigma_of_nonneg (f := f) hf).2
    ⟨(fun m => Summable.of_finite),
      Summable.of_nonneg_of_le
        (fun m => tsum_nonneg (fun i => hf ⟨m, i⟩)) htsumBound houter⟩
  exact hsigma

private theorem wilsonModeAssignmentCurrentTerm_inner_hasSum {B : Box 4} {N : ℕ}
    {epsilon : ℝ} (φ : Link B → ℝ)
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B)) (z : ℤ → ℝ)
    (m : Link B → ℕ) :
    HasSum (fun i : Fin (T m).length =>
      wilsonModeAssignmentCurrentTerm N epsilon φ T z ⟨m, i⟩)
      (wilsonModeAssignmentCoefficient epsilon m *
        currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ (T m)) := by
  classical
  have hfinite : HasSum
      (fun i : Fin (T m).length =>
        wilsonModeAssignmentCurrentTerm N epsilon φ T z ⟨m, i⟩)
      (∑ i : Fin (T m).length,
        wilsonModeAssignmentCurrentTerm N epsilon φ T z ⟨m, i⟩) := hasSum_fintype _
  have hsum : (∑ i : Fin (T m).length,
      wilsonModeAssignmentCurrentTerm N epsilon φ T z ⟨m, i⟩) =
      wilsonModeAssignmentCoefficient epsilon m *
        currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ (T m) := by
    change ∑ i : Fin (T m).length,
        wilsonModeAssignmentCoefficient epsilon m *
          (((T m).get i).weight * currentStateProduct
            (wilsonModeFrequencyAssignment N m) z φ ((T m).get i).state) = _
    calc
      _ = wilsonModeAssignmentCoefficient epsilon m *
          ∑ i : Fin (T m).length,
            (((T m).get i).weight * currentStateProduct
              (wilsonModeFrequencyAssignment N m) z φ ((T m).get i).state) := by
        simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (T m).length))
          (fun i => (((T m).get i).weight * currentStateProduct
            (wilsonModeFrequencyAssignment N m) z φ ((T m).get i).state))
          (wilsonModeAssignmentCoefficient epsilon m)).symm
      _ = wilsonModeAssignmentCoefficient epsilon m *
          ((T m).map fun t => t.weight * currentStateProduct
            (wilsonModeFrequencyAssignment N m) z φ t.state).sum := by
        exact congrArg (fun x : ℝ => wilsonModeAssignmentCoefficient epsilon m * x)
          (list_sum_map_fin (T m) (fun t => t.weight * currentStateProduct
            (wilsonModeFrequencyAssignment N m) z φ t.state)).symm
      _ = _ := rfl
  exact hfinite.summable.hasSum_iff.mpr (by simpa only [tsum_fintype] using hsum)

/-- The doubly indexed separated-current expansion is an absolutely summable
series over assignment/term pairs, and its sum is the original finite product
of link mixtures. The finite current expansion is indexed inside each fixed
positive-mode assignment, so no global finite-`γ` interpretation is used. -/
theorem wilsonModeAssignmentCurrentTerm_hasSum {B : Box 4} {N : ℕ}
    {epsilon h : ℝ} (φ : Link B → ℝ) (hepsilon : 0 < epsilon) (hh : 0 ≤ h)
    (T : (Link B → ℕ) → List (CurrentExpansionTerm B)) (z : ℤ → ℝ)
    (hprofile : ∀ m : Link B → ℕ, ∀ e,
      z (abs (wilsonModeFrequencyAssignment N m e)) =
        wilsonCoefficientActivity epsilon N (m e) h)
    (hT : ∀ m, IsFixedFrequencyCurrentExpansion
      (wilsonModeFrequencyAssignment N m) z (T m)) :
    HasSum (fun p : Σ m : Link B → ℕ, Fin (T m).length =>
      wilsonModeAssignmentCurrentTerm N epsilon φ T z p)
      (∏ e : Link B,
        (1 + ∑' q : ℕ,
          wilsonCharacterCoefficient N (q + 1) h *
            Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * φ e)))) := by
  have hgrouped := wilsonModeAssignment_currentExpansion_hasSum
    (B := B) (N := N) (epsilon := epsilon) (h := h) φ hepsilon hh T z hprofile hT
  have hnorm := summable_norm_wilsonModeAssignmentCurrentTerm
    (B := B) (N := N) (epsilon := epsilon) (h := h) φ hepsilon hh T z hprofile hT
  have hflat : Summable (fun p : Σ m : Link B → ℕ, Fin (T m).length =>
      wilsonModeAssignmentCurrentTerm N epsilon φ T z p) := hnorm.of_norm
  have hinner : ∀ m : Link B → ℕ,
      HasSum (fun i : Fin (T m).length =>
        wilsonModeAssignmentCurrentTerm N epsilon φ T z ⟨m, i⟩)
        (wilsonModeAssignmentCoefficient epsilon m *
          currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ (T m)) :=
    fun m => wilsonModeAssignmentCurrentTerm_inner_hasSum φ T z m
  have htsum : (∑' p : Σ m : Link B → ℕ, Fin (T m).length,
      wilsonModeAssignmentCurrentTerm N epsilon φ T z p) =
      ∑' m : Link B → ℕ,
        wilsonModeAssignmentCoefficient epsilon m *
          currentExpansionSum (wilsonModeFrequencyAssignment N m) z φ (T m) := by
    calc
      _ = ∑' m : Link B → ℕ,
          ∑' i : Fin (T m).length,
            wilsonModeAssignmentCurrentTerm N epsilon φ T z ⟨m, i⟩ := hflat.tsum_sigma
      _ = _ := tsum_congr fun m => (hinner m).tsum_eq
  exact hflat.hasSum_iff.mpr (htsum.trans hgrouped.tsum_eq)


/-- Integer-indexed extension of the source activity `ζ(q) λ(q)`. On a
nonzero multiple `qN`, it returns the source value at mode `q`; values between
the clock frequencies are chosen only to provide positive activities for the
finite current API. -/
@[expose] noncomputable def wilsonIntegerActivity
    (epsilon : ℝ) (N : ℕ) (h : ℝ) (n : ℤ) : ℝ :=
  wilsonSourceCoefficientActivity epsilon N (max 1 (n.natAbs / N)) h

theorem wilsonSourceCoefficientActivity_succ (epsilon : ℝ) (N q : ℕ) (h : ℝ) :
    wilsonSourceCoefficientActivity epsilon N (q + 1) h =
      wilsonCoefficientActivity epsilon N q h := by
  rfl

theorem wilsonIntegerActivity_pos (epsilon : ℝ) (N : ℕ) (h : ℝ)
    (hepsilon : 0 < epsilon) (hh : 0 < h) (n : ℤ) :
    0 < wilsonIntegerActivity epsilon N h n := by
  unfold wilsonIntegerActivity
  exact (wilsonSourceCoefficientActivity_bound hepsilon hh (by omega)).1

/-- On every positive clock frequency from a Wilson assignment, the integer
extension agrees exactly with the source activity profile (3.13). -/
theorem wilsonIntegerActivity_frequency_profile {B : Box 4} {N : ℕ}
    (epsilon h : ℝ) (hN : 0 < N) (m : Link B → ℕ) (e : Link B) :
    wilsonIntegerActivity epsilon N h
        (abs (wilsonModeFrequencyAssignment N m e)) =
      wilsonCoefficientActivity epsilon N (m e) h := by
  unfold wilsonIntegerActivity
  have hn : 0 ≤ wilsonModeFrequencyAssignment N m e := by
    dsimp [wilsonModeFrequencyAssignment]
    exact_mod_cast Nat.zero_le ((m e + 1) * N)
  rw [abs_of_nonneg hn]
  simp only [wilsonModeFrequencyAssignment, Int.natAbs_natCast]
  rw [Nat.mul_div_left (m e + 1) hN]
  rw [show max 1 (m e + 1) = m e + 1 by omega]
  exact wilsonSourceCoefficientActivity_succ epsilon N (m e) h


private noncomputable def wilsonCircleBesselTerm (N : ℕ) (h : ℝ)
    (m : Sum ℕ ℕ) (z : UnitAddCircle) : ℂ :=
  match m with
  | Sum.inl n => (modifiedBesselI n h : ℂ) *
      fourier (T := (1 : ℝ)) ((n * N : ℕ) : ℤ) z
  | Sum.inr n => (modifiedBesselI (n + 1) h : ℂ) *
      fourier (T := (1 : ℝ)) (-((n + 1) * N : ℕ) : ℤ) z

private theorem wilsonCircleBesselTerm_coe (N : ℕ) (h x : ℝ) (m : Sum ℕ ℕ) :
    wilsonCircleBesselTerm N h m (x : UnitAddCircle) =
      wilsonBesselFrequencyTerm h ((N : ℝ) * (2 * Real.pi * x)) m := by
  cases m with
  | inl n =>
      simp only [wilsonCircleBesselTerm, wilsonBesselFrequencyTerm]
      rw [fourier_coe_apply]
      simp only [Complex.ofReal_one, div_one]
      congr 1
      congr 1
      push_cast
      ring
  | inr n =>
      simp only [wilsonCircleBesselTerm, wilsonBesselFrequencyTerm]
      rw [fourier_coe_apply]
      simp only [Complex.ofReal_one, div_one]
      congr 1
      congr 1
      push_cast
      ring

private theorem hasSum_wilsonCircleBesselTerm (N : ℕ) (h : ℝ)
    (z : UnitAddCircle) :
    HasSum (fun m => wilsonCircleBesselTerm N h m z)
      (Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ))) := by
  refine QuotientAddGroup.induction_on z ?_
  intro x
  have hs := wilsonBesselCharacterExpansion h ((N : ℝ) * (2 * Real.pi * x))
  have ht : ∀ m, wilsonCircleBesselTerm N h m (x : UnitAddCircle) =
      wilsonBesselFrequencyTerm h ((N : ℝ) * (2 * Real.pi * x)) m :=
    fun m => wilsonCircleBesselTerm_coe N h x m
  have hs' : HasSum (fun m => wilsonCircleBesselTerm N h m (x : UnitAddCircle))
      (Complex.exp ((h : ℂ) *
        (Real.cos ((N : ℝ) * (2 * Real.pi * x)) : ℂ))) := by
    have hnew := hs.summable.congr (fun m => (ht m).symm)
    have htsum : (∑' m, wilsonCircleBesselTerm N h m (x : UnitAddCircle)) =
        ∑' m, wilsonBesselFrequencyTerm h ((N : ℝ) * (2 * Real.pi * x)) m :=
      tsum_congr ht
    exact hnew.hasSum_iff.mpr (htsum.trans hs.tsum_eq)
  convert hs' using 1
  rw [circleCosCharacter_real]
  congr 1
  push_cast
  ring_nf

private theorem haarFourierIntegral (n : ℤ) :
    ∫ z : UnitAddCircle, fourier (T := (1 : ℝ)) n z ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right hn]
    apply integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
    intro z
    exact fourier_add_half_inv_index hn (by norm_num) z

private theorem integral_wilsonCircleBesselTerm_zero (N : ℕ) (h : ℝ)
    (hN : 0 < N) (m : Sum ℕ ℕ) :
    ∫ z : UnitAddCircle, wilsonCircleBesselTerm N h m z ∂AddCircle.haarAddCircle =
      if m = Sum.inl 0 then (modifiedBesselI 0 h : ℂ) else 0 := by
  cases m with
  | inl n =>
      by_cases hn : n = 0
      · subst n
        simp [wilsonCircleBesselTerm]
      · have hpNat : n * N ≠ 0 :=
          Nat.mul_ne_zero (Nat.ne_of_gt (Nat.pos_of_ne_zero hn)) (Nat.ne_of_gt hN)
        have hfreq : ((n * N : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hpNat
        simp only [wilsonCircleBesselTerm, Sum.inl.injEq]
        change ∫ z : UnitAddCircle,
          (modifiedBesselI n h : ℂ) * fourier (T := (1 : ℝ)) ((n * N : ℕ) : ℤ) z
            ∂AddCircle.haarAddCircle =
              if n = 0 then (modifiedBesselI 0 h : ℂ) else 0
        rw [ite_eq_right hn, MeasureTheory.integral_const_mul, haarFourierIntegral,
          ite_eq_right hfreq]
        simp only [mul_zero]
  | inr n =>
      have hpNat : (n + 1) * N ≠ 0 :=
        Nat.mul_ne_zero (Nat.succ_ne_zero n) (Nat.ne_of_gt hN)
      have hcast : ((n + 1) * N : ℕ) ≠ (0 : ℤ) := Nat.cast_ne_zero.mpr hpNat
      have hfreq : (-((n + 1) * N : ℕ) : ℤ) ≠ 0 := Int.neg_ne_zero.mpr hcast
      simp only [wilsonCircleBesselTerm]
      change ∫ z : UnitAddCircle,
        (modifiedBesselI (n + 1) h : ℂ) *
          fourier (T := (1 : ℝ)) (-((n + 1) * N : ℕ) : ℤ) z ∂AddCircle.haarAddCircle =
        (if Sum.inr n = Sum.inl 0 then (modifiedBesselI 0 h : ℂ) else 0)
      simp only [reduceCtorEq]
      rw [MeasureTheory.integral_const_mul, haarFourierIntegral,
        ite_eq_right hfreq]
      simp

private theorem norm_fourier_wilsonCircle (n : ℤ) (z : UnitAddCircle) :
    ‖fourier (T := (1 : ℝ)) n z‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

private theorem wilsonCircleBesselTerm_norm_at_zero (N : ℕ) (h : ℝ)
    (m : Sum ℕ ℕ) (z : UnitAddCircle) :
    ‖wilsonCircleBesselTerm N h m z‖ =
      ‖wilsonCircleBesselTerm N h m (0 : UnitAddCircle)‖ := by
  cases m <;> simp [wilsonCircleBesselTerm]

private theorem integrable_wilsonCircleBesselTerm (N : ℕ) (h : ℝ)
    (m : Sum ℕ ℕ) :
    Integrable (fun z : UnitAddCircle => wilsonCircleBesselTerm N h m z)
      AddCircle.haarAddCircle := by
  apply MeasureTheory.integrableOn_univ.mp
  have hc : Continuous (fun z : UnitAddCircle => wilsonCircleBesselTerm N h m z) := by
    cases m with
    | inl n =>
        change Continuous (fun z : UnitAddCircle =>
          (modifiedBesselI n h : ℂ) * fourier (T := (1 : ℝ)) ((n * N : ℕ) : ℤ) z)
        exact continuous_const.mul (fourier (T := (1 : ℝ)) ((n * N : ℕ) : ℤ)).continuous
    | inr n =>
        change Continuous (fun z : UnitAddCircle =>
          (modifiedBesselI (n + 1) h : ℂ) *
            fourier (T := (1 : ℝ)) (-((n + 1) * N : ℕ) : ℤ) z)
        exact continuous_const.mul
          (fourier (T := (1 : ℝ)) (-((n + 1) * N : ℕ) : ℤ)).continuous
  exact hc.continuousOn.integrableOn_compact isCompact_univ

private theorem circleExpIntegral_eq_bessel_zero (N : ℕ) (hN : 0 < N)
    (h : ℝ) :
    ∫ z : UnitAddCircle,
      Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ)) ∂AddCircle.haarAddCircle =
      (modifiedBesselI 0 h : ℂ) := by
  have hcoeff : Summable (fun m : Sum ℕ ℕ =>
      ‖wilsonCircleBesselTerm N h m (0 : UnitAddCircle)‖) := by
    have hs := (wilsonBesselCharacterExpansion h 0).summable.norm
    refine hs.congr ?_
    intro m
    cases m <;> simp [wilsonCircleBesselTerm, wilsonBesselFrequencyTerm]
  have hnormInt (m : Sum ℕ ℕ) :
      ∫ z : UnitAddCircle, ‖wilsonCircleBesselTerm N h m z‖ ∂AddCircle.haarAddCircle =
        ‖wilsonCircleBesselTerm N h m (0 : UnitAddCircle)‖ := by
    calc
      _ = ∫ z : UnitAddCircle, ‖wilsonCircleBesselTerm N h m (0 : UnitAddCircle)‖
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => wilsonCircleBesselTerm_norm_at_zero N h m z)
      _ = _ := by simp
  have hnorms : Summable (fun m : Sum ℕ ℕ =>
      ∫ z : UnitAddCircle, ‖wilsonCircleBesselTerm N h m z‖ ∂AddCircle.haarAddCircle) := by
    refine hcoeff.congr ?_
    intro m
    exact (hnormInt m).symm
  have htermsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun m => integrable_wilsonCircleBesselTerm N h m) hnorms
  have hsumTerms : (∑' m : Sum ℕ ℕ,
      ∫ z : UnitAddCircle, wilsonCircleBesselTerm N h m z ∂AddCircle.haarAddCircle) =
      (modifiedBesselI 0 h : ℂ) := by
    calc
      _ = ∑' m : Sum ℕ ℕ,
          (if m = Sum.inl 0 then (modifiedBesselI 0 h : ℂ) else 0) :=
        tsum_congr (fun m => integral_wilsonCircleBesselTerm_zero N h hN m)
      _ = (modifiedBesselI 0 h : ℂ) :=
        (hasSum_ite_eq (Sum.inl 0) (modifiedBesselI 0 h : ℂ)).tsum_eq
  calc
    _ = ∫ z : UnitAddCircle, ∑' m : Sum ℕ ℕ, wilsonCircleBesselTerm N h m z
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => (hasSum_wilsonCircleBesselTerm N h z).tsum_eq.symm)
    _ = ∑' m : Sum ℕ ℕ,
        ∫ z : UnitAddCircle, wilsonCircleBesselTerm N h m z ∂AddCircle.haarAddCircle :=
      htermsum.tsum_eq.symm
    _ = (modifiedBesselI 0 h : ℂ) := hsumTerms

private theorem pinningNormalizer_eq_bessel (N : ℕ) (hN : 0 < N)
    (h : NNReal) :
    pinningNormalizer N h = modifiedBesselI 0 (h : ℝ) := by
  have hc := circleExpIntegral_eq_bessel_zero N hN (h : ℝ)
  have hInt : Integrable (fun z : UnitAddCircle =>
      Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ))) AddCircle.haarAddCircle := by
    apply MeasureTheory.integrableOn_univ.mp
    have hcont : Continuous (fun z : UnitAddCircle =>
        Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ))) :=
      Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_circleCosCharacter N)))
    exact hcont.continuousOn.integrableOn_compact isCompact_univ
  have hRe := Complex.reCLM.integral_comp_comm hInt
  have hReFn : (fun z : UnitAddCircle =>
      (Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ))).re) =
        fun z => Real.exp ((h : ℝ) * circleCosCharacter N z) := by
    funext z
    have hx : (h : ℂ) * (circleCosCharacter N z : ℂ) =
        (((h : ℝ) * circleCosCharacter N z : ℝ) : ℂ) := by push_cast; ring
    rw [hx]
    simp [Complex.exp_re]
  calc
    pinningNormalizer N h = ∫ z : UnitAddCircle,
        Real.exp ((h : ℝ) * circleCosCharacter N z) ∂AddCircle.haarAddCircle := rfl
    _ = ∫ z : UnitAddCircle,
        (Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ))).re
          ∂AddCircle.haarAddCircle := by rw [hReFn]
    _ = (∫ z : UnitAddCircle,
        Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ))
          ∂AddCircle.haarAddCircle).re := hRe
    _ = modifiedBesselI 0 (h : ℝ) := by rw [hc]; rfl

/-- The source's normalization `ξ(h)` is the reciprocal zero-mode Bessel
coefficient, for every positive clock order. -/
theorem pinningNormalization_eq_bessel_inv {N : ℕ} (hN : 0 < N)
    (h : NNReal) :
    pinningNormalization N h = (modifiedBesselI 0 (h : ℝ))⁻¹ := by
  rw [pinningNormalization, pinningNormalizer_eq_bessel N hN h]

private theorem haarFourierIntegral_wilson (n : ℤ) :
    ∫ z : UnitAddCircle, fourier (T := (1 : ℝ)) n z ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := haarFourierIntegral n

private theorem integral_fourierProduct_wilson (a b : ℤ) :
    ∫ z : UnitAddCircle,
      fourier (T := (1 : ℝ)) a z * fourier (T := (1 : ℝ)) b z
        ∂AddCircle.haarAddCircle = if a + b = 0 then 1 else 0 := by
  have hfun : (fun z : UnitAddCircle =>
      fourier (T := (1 : ℝ)) a z * fourier (T := (1 : ℝ)) b z) =
      fun z => fourier (T := (1 : ℝ)) (a + b) z := by
    funext z
    exact (fourier_add).symm
  rw [show (∫ z : UnitAddCircle,
      fourier (T := (1 : ℝ)) a z * fourier (T := (1 : ℝ)) b z
        ∂AddCircle.haarAddCircle) =
      ∫ z : UnitAddCircle, fourier (T := (1 : ℝ)) (a + b) z
        ∂AddCircle.haarAddCircle from congrArg (fun f : UnitAddCircle → ℂ =>
          ∫ z : UnitAddCircle, f z ∂AddCircle.haarAddCircle) hfun]
  exact haarFourierIntegral_wilson (a + b)

private theorem integral_const_fourierProduct_wilson (c : ℂ) (a b : ℤ) :
    ∫ z : UnitAddCircle,
      (c * fourier (T := (1 : ℝ)) a z) * fourier (T := (1 : ℝ)) b z
        ∂AddCircle.haarAddCircle = c * (if a + b = 0 then 1 else 0) := by
  calc
    _ = ∫ z : UnitAddCircle,
        c * (fourier (T := (1 : ℝ)) a z * fourier (T := (1 : ℝ)) b z)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by ring)
    _ = c * ∫ z : UnitAddCircle,
        fourier (T := (1 : ℝ)) a z * fourier (T := (1 : ℝ)) b z
          ∂AddCircle.haarAddCircle := integral_const_mul _ _
    _ = _ := by rw [integral_fourierProduct_wilson]

private theorem integral_wilsonCircleBesselTerm_mode (N : ℕ) (h : ℝ)
    (hN : 0 < N) (q : ℕ) (hq : 0 < q) (m : Sum ℕ ℕ) :
    ∫ z : UnitAddCircle,
      wilsonCircleBesselTerm N h m z *
        fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z
          ∂AddCircle.haarAddCircle =
      if m = Sum.inl q then (modifiedBesselI q h : ℂ) else 0 := by
  cases m with
  | inl n =>
      have hmulzero : ((n * N : ℕ) : ℤ) + -((q * N : ℕ) : ℤ) = 0 → n = q := by
        intro hz
        have hz' : ((n * N : ℕ) : ℤ) = ((q * N : ℕ) : ℤ) := by omega
        have hn : n * N = q * N := by exact_mod_cast hz'
        exact Nat.eq_of_mul_eq_mul_right hN hn
      by_cases hn : n = q
      · subst n
        simp only [wilsonCircleBesselTerm]
        rw [integral_const_fourierProduct_wilson]
        simp
      · have hz' : (n : ℤ) * (N : ℤ) + -((q : ℤ) * (N : ℤ)) ≠ 0 := by
          intro heq
          have heq' : ((n * N : ℕ) : ℤ) = ((q * N : ℕ) : ℤ) := by omega
          have heqNat : n * N = q * N := by exact_mod_cast heq'
          exact hn (Nat.eq_of_mul_eq_mul_right hN heqNat)
        simp only [wilsonCircleBesselTerm]
        rw [integral_const_fourierProduct_wilson]
        simp [hn, hz']
  | inr n =>
      have hp : 0 < (n + 1) * N + q * N :=
        Nat.add_pos_right _ (Nat.mul_pos hq hN)
      have hz' : -((n + 1 : ℤ) * (N : ℤ)) + -((q : ℤ) * (N : ℤ)) ≠ 0 := by
        intro heq
        have hsum : (((n + 1) * N + q * N : ℕ) : ℤ) = 0 := by
          push_cast
          omega
        have hsumNat : (n + 1) * N + q * N = 0 := by exact_mod_cast hsum
        omega
      simp only [wilsonCircleBesselTerm, reduceCtorEq]
      rw [integral_const_fourierProduct_wilson]
      simp [hz']

private theorem integrable_wilsonCircleBesselTerm_mode (N : ℕ) (h : ℝ)
    (q : ℕ) (m : Sum ℕ ℕ) :
    Integrable (fun z : UnitAddCircle =>
      wilsonCircleBesselTerm N h m z *
        fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z)
      AddCircle.haarAddCircle := by
  apply MeasureTheory.integrableOn_univ.mp
  have hc : Continuous (fun z : UnitAddCircle =>
      wilsonCircleBesselTerm N h m z *
        fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z) := by
    cases m with
    | inl n =>
        change Continuous (fun z : UnitAddCircle =>
          ((modifiedBesselI n h : ℂ) * fourier (T := (1 : ℝ)) ((n * N : ℕ) : ℤ) z) *
            fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z)
        exact (continuous_const.mul (fourier (T := (1 : ℝ)) ((n * N : ℕ) : ℤ)).continuous).mul
          (fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ))).continuous
    | inr n =>
        change Continuous (fun z : UnitAddCircle =>
          ((modifiedBesselI (n + 1) h : ℂ) *
            fourier (T := (1 : ℝ)) (-((n + 1) * N : ℕ) : ℤ) z) *
              fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z)
        exact (continuous_const.mul
          (fourier (T := (1 : ℝ)) (-((n + 1) * N : ℕ) : ℤ)).continuous).mul
            (fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ))).continuous
  exact hc.continuousOn.integrableOn_compact isCompact_univ

private theorem circleExpFourierIntegral (N : ℕ) (h : ℝ) (hN : 0 < N)
    (q : ℕ) (hq : 0 < q) :
    ∫ z : UnitAddCircle,
      Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ)) *
        fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z
          ∂AddCircle.haarAddCircle = (modifiedBesselI q h : ℂ) := by
  have hcoeff : Summable (fun m : Sum ℕ ℕ =>
      ‖wilsonCircleBesselTerm N h m (0 : UnitAddCircle)‖) := by
    have hs := (wilsonBesselCharacterExpansion h 0).summable.norm
    refine hs.congr ?_
    intro m
    cases m <;> simp [wilsonCircleBesselTerm, wilsonBesselFrequencyTerm]
  have hnormInt (m : Sum ℕ ℕ) :
      ∫ z : UnitAddCircle,
        ‖wilsonCircleBesselTerm N h m z *
          fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z‖
          ∂AddCircle.haarAddCircle =
        ‖wilsonCircleBesselTerm N h m (0 : UnitAddCircle)‖ := by
    calc
      _ = ∫ z : UnitAddCircle, ‖wilsonCircleBesselTerm N h m z‖
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by simp)
      _ = ∫ z : UnitAddCircle,
          ‖wilsonCircleBesselTerm N h m (0 : UnitAddCircle)‖
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => wilsonCircleBesselTerm_norm_at_zero N h m z)
      _ = _ := by simp
  have hnorms : Summable (fun m : Sum ℕ ℕ =>
      ∫ z : UnitAddCircle,
        ‖wilsonCircleBesselTerm N h m z *
          fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z‖
          ∂AddCircle.haarAddCircle) := by
    refine hcoeff.congr ?_
    intro m
    exact (hnormInt m).symm
  have hseries := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun m => integrable_wilsonCircleBesselTerm_mode N h q m) hnorms
  have hsumTerms : (∑' m : Sum ℕ ℕ,
      ∫ z : UnitAddCircle,
        wilsonCircleBesselTerm N h m z *
          fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z
          ∂AddCircle.haarAddCircle) = (modifiedBesselI q h : ℂ) := by
    calc
      _ = ∑' m : Sum ℕ ℕ,
          (if m = Sum.inl q then (modifiedBesselI q h : ℂ) else 0) :=
        tsum_congr (fun m => integral_wilsonCircleBesselTerm_mode N h hN q hq m)
      _ = _ := (hasSum_ite_eq (Sum.inl q) (modifiedBesselI q h : ℂ)).tsum_eq
  calc
    _ = ∫ z : UnitAddCircle,
        ∑' m : Sum ℕ ℕ,
          wilsonCircleBesselTerm N h m z *
            fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        have hs := (hasSum_wilsonCircleBesselTerm N h z).mul_right
          (fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z)
        exact hs.tsum_eq.symm)
    _ = _ := hseries.tsum_eq.symm.trans hsumTerms

private theorem circleCosIntegral_eq_bessel (N : ℕ) (h : ℝ) (hN : 0 < N)
    (q : ℕ) (hq : 0 < q) :
    ∫ z : UnitAddCircle,
      Real.exp (h * circleCosCharacter N z) * circleCosCharacter (q * N) z
        ∂AddCircle.haarAddCircle = modifiedBesselI q h := by
  let f : UnitAddCircle → ℂ := fun z =>
    Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ)) *
      fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z
  have hfc : Continuous f := by
    dsimp [f]
    exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_circleCosCharacter N)))).mul
        (fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ))).continuous
  have hfint : Integrable f AddCircle.haarAddCircle := by
    apply MeasureTheory.integrableOn_univ.mp
    exact hfc.continuousOn.integrableOn_compact isCompact_univ
  have hRe := Complex.reCLM.integral_comp_comm hfint
  have hpoint : ∀ z : UnitAddCircle,
      (f z).re = Real.exp (h * circleCosCharacter N z) * circleCosCharacter (q * N) z := by
    intro z
    change (Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ)) *
        fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z).re = _
    rw [fourier_neg]
    have hexp : Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ)) =
        (Real.exp (h * circleCosCharacter N z) : ℂ) := by
      have hx : (h : ℂ) * (circleCosCharacter N z : ℂ) =
          ((h * circleCosCharacter N z : ℝ) : ℂ) := by push_cast; ring
      rw [hx, ← Complex.ofReal_exp]
    rw [hexp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, sub_zero, zero_mul]
    rfl
  calc
    _ = ∫ z : UnitAddCircle, (f z).re ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => (hpoint z).symm)
    _ = (∫ z : UnitAddCircle, f z ∂AddCircle.haarAddCircle).re := hRe
    _ = modifiedBesselI q h := by
      rw [show (∫ z : UnitAddCircle, f z ∂AddCircle.haarAddCircle) =
          ∫ z : UnitAddCircle,
            Complex.exp ((h : ℂ) * (circleCosCharacter N z : ℂ)) *
              fourier (T := (1 : ℝ)) (-((q * N : ℕ) : ℤ)) z ∂AddCircle.haarAddCircle from rfl]
      rw [circleExpFourierIntegral N h hN q hq]
      rfl

/-- The source integral definition of `λ(q)` agrees with its Bessel-series
coefficient for positive clock order and positive mode. -/
theorem sourceWilsonLambdaIntegral_eq_series (N q : ℕ) (hN : 0 < N)
    (hq : 0 < q) (h : NNReal) :
    sourceWilsonLambdaIntegral N q h =
      wilsonCharacterCoefficient N q (h : ℝ) := by
  unfold sourceWilsonLambdaIntegral pinningNormalization wilsonCharacterCoefficient
  rw [circleCosIntegral_eq_bessel N (h : ℝ) hN q hq,
    pinningNormalizer_eq_bessel N hN h]
  simp only [div_eq_mul_inv]
  ring


/-- The integral-defined source coefficient has the strict bounds in (3.11)
for every positive mode and positive coupling. -/
theorem sourceWilsonLambdaIntegral_bounds (N q : ℕ) (hN : 0 < N)
    (hq : 0 < q) {h : NNReal} (hh : 0 < h) :
    0 < sourceWilsonLambdaIntegral N q h ∧
      sourceWilsonLambdaIntegral N q h < 2 := by
  rw [sourceWilsonLambdaIntegral_eq_series N q hN hq h]
  exact wilsonCharacterCoefficient_bounds hq (by exact_mod_cast hh)


end FroehlichSpencer.FS82.ZN

end
