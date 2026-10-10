/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryBase
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProxy
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProxyCut
public import FroehlichSpencer.BKT.Generic.Marked.Energy
public import FroehlichSpencer.BKT.Generic.Marked.Waves
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3DecompTerminal
import Mathlib.Tactic

/-! # Rooted profile energy assembly

This module builds a root-zero real base wave by selecting the heavier bounded-face parity in
squared mass. The wired graph is not assumed bipartite. A general finite profile family can then
be added when its pairings, energy bounds and gradient separation are available.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.SpinWaves
open FroehlichSpencer.BKT.Lattice2D

variable {L : ℕ}

/-- Squared real-source mass on one checkerboard class of bounded faces. -/
def rootedRealSquareParityMass (ρ : RotatorDualFace L → ℝ) (b : Bool) : ℝ :=
  ∑ x : SquareFreeVertex L,
    if squareParityColor x = b then ρ (some x) ^ 2 else 0

/-- Choose the bounded-face parity carrying the larger squared mass. -/
def rootedRealSquareBaseParity (ρ : RotatorDualFace L → ℝ) : Bool :=
  if rootedRealSquareParityMass ρ true ≤ rootedRealSquareParityMass ρ false then false else true

/-- The restriction of a rooted real source to its heavier bounded-face parity. It vanishes at the
wired root, so no bipartition is asserted for `squareZero`. -/
def rootedRealSquareBaseWave (ρ : RotatorDualFace L → ℝ) : RotatorDualFace L → ℝ
  | none => 0
  | some x => if squareParityColor x = rootedRealSquareBaseParity ρ then ρ (some x) else 0

/-- At least half of the squared mass of a root-zero source lies on the selected bounded-face
parity. -/
theorem half_sq_mass_le_rootedRealSquareBase (ρ : RotatorDualFace L → ℝ)
    : (1 / 2 : ℝ) * ∑ x : SquareFreeVertex L, ρ (some x) ^ 2 ≤
      ∑ j, rootedRealSquareBaseWave ρ j ^ 2 := by
  classical
  have hface : ∑ x : SquareFreeVertex L, ρ (some x) ^ 2 =
      rootedRealSquareParityMass ρ false + rootedRealSquareParityMass ρ true := by
    unfold rootedRealSquareParityMass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    cases squareParityColor x <;> simp
  have hbase : ∑ j, rootedRealSquareBaseWave ρ j ^ 2 =
      rootedRealSquareParityMass ρ (rootedRealSquareBaseParity ρ) := by
    rw [Fintype.sum_option]
    simp [rootedRealSquareBaseWave, rootedRealSquareParityMass]
  have hmax : rootedRealSquareParityMass ρ false + rootedRealSquareParityMass ρ true ≤
      2 * rootedRealSquareParityMass ρ (rootedRealSquareBaseParity ρ) := by
    unfold rootedRealSquareBaseParity
    split_ifs <;> linarith
  rw [hface, hbase]
  linarith

/-- A field supported on one bounded-face parity has its energy bounded by four times its squared
mass. Edges to the wired root contribute only the bounded-face endpoint because the field is zero
at the root. -/
theorem energy_supported_one_face_parity_le (b : Bool) (a : RotatorDualFace L → ℝ)
    (hroot : a none = 0)
    (hsupport : ∀ x : SquareFreeVertex L, a (some x) ≠ 0 → squareParityColor x = b) :
    (squareZero L).energy a ≤ 4 * ∑ j, a j ^ 2 := by
  classical
  let srcCount : RotatorDualFace L → ℕ := fun j =>
    (Finset.univ.filter fun e : SquareZeroBond L => (squareZero L).src e = j).card
  let tgtCount : RotatorDualFace L → ℕ := fun j =>
    (Finset.univ.filter fun e : SquareZeroBond L => (squareZero L).tgt e = j).card
  have hEdge (e : SquareZeroBond L) :
      ((squareZero L).grad a e) ^ 2 = a ((squareZero L).src e) ^ 2 + a ((squareZero L).tgt e) ^ 2 := by
    cases e with
    | inl f =>
      change (a (some f.1.1) - a (some f.1.2)) ^ 2 =
        a (some f.1.1) ^ 2 + a (some f.1.2) ^ 2
      have hnot : ¬ (a (some f.1.1) ≠ 0 ∧ a (some f.1.2) ≠ 0) := by
        rintro ⟨hs, ht⟩
        have hcs := hsupport f.1.1 hs
        have hct := hsupport f.1.2 ht
        exact (squareFree_color_edge f) (hcs.trans hct.symm)
      by_cases hs : a (some f.1.1) = 0
      · simp [hs]
      · have ht : a (some f.1.2) = 0 := by
          by_contra ht
          exact hnot ⟨hs, ht⟩
        simp [ht]
    | inr k =>
      change (a (some k.1) - a none) ^ 2 = a (some k.1) ^ 2 + a none ^ 2
      simp [hroot]
  have hsumSrc : ∑ e : SquareZeroBond L, a ((squareZero L).src e) ^ 2 =
      ∑ j, (srcCount j : ℝ) * a j ^ 2 := by
    simp only [srcCount]
    calc
      (∑ e, a ((squareZero L).src e) ^ 2) =
          ∑ e, ∑ j, if (squareZero L).src e = j then a j ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            simp
      _ = ∑ j, ∑ e, if (squareZero L).src e = j then a j ^ 2 else 0 := Finset.sum_comm
      _ = ∑ j, (↑(Finset.univ.filter fun e => (squareZero L).src e = j).card) * a j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_filter]
            simp
  have hsumTgt : ∑ e : SquareZeroBond L, a ((squareZero L).tgt e) ^ 2 =
      ∑ j, (tgtCount j : ℝ) * a j ^ 2 := by
    simp only [tgtCount]
    calc
      (∑ e, a ((squareZero L).tgt e) ^ 2) =
          ∑ e, ∑ j, if (squareZero L).tgt e = j then a j ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            simp
      _ = ∑ j, ∑ e, if (squareZero L).tgt e = j then a j ^ 2 else 0 := Finset.sum_comm
      _ = ∑ j, (↑(Finset.univ.filter fun e => (squareZero L).tgt e = j).card) * a j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_filter]
            simp
  have hdeg (x : SquareFreeVertex L) : srcCount (some x) + tgtCount (some x) ≤ 4 := by
    let S := Finset.univ.filter fun e : SquareZeroBond L => (squareZero L).src e = some x
    let T := Finset.univ.filter fun e : SquareZeroBond L => (squareZero L).tgt e = some x
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro e heS heT
      have hs := (Finset.mem_filter.mp heS).2
      have ht := (Finset.mem_filter.mp heT).2
      exact (squareZero L).src_ne_tgt e (hs.trans ht.symm)
    have hunion : S ∪ T ⊆ Finset.univ.filter fun e : SquareZeroBond L =>
        (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x := by
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp he).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp he).2⟩
    have hcard := Finset.card_union_of_disjoint hdisj
    change S.card + T.card ≤ 4
    calc
      S.card + T.card = (S ∪ T).card := hcard.symm
      _ ≤ (Finset.univ.filter fun e : SquareZeroBond L =>
        (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x).card := Finset.card_le_card hunion
      _ ≤ 4 := card_incident_le_four x
  rw [Multigraph.energy]
  calc
    (∑ e, ((squareZero L).grad a e) ^ 2) =
        ∑ e, (a ((squareZero L).src e) ^ 2 + a ((squareZero L).tgt e) ^ 2) := by
          apply Finset.sum_congr rfl
          intro e he
          exact hEdge e
    _ = ∑ j, ((srcCount j + tgtCount j : ℕ) : ℝ) * a j ^ 2 := by
          rw [Finset.sum_add_distrib, hsumSrc, hsumTgt, ← Finset.sum_add_distrib]
          simp_rw [Nat.cast_add, add_mul]
    _ ≤ ∑ j, (4 : ℝ) * a j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          cases j with
          | none => simp [hroot]
          | some x =>
            have hd := hdeg x
            have hd' : ((srcCount (some x) + tgtCount (some x) : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hd
            exact mul_le_mul_of_nonneg_right hd' (sq_nonneg (a (some x)))
    _ = 4 * ∑ j, a j ^ 2 := by rw [Finset.mul_sum]

/-- The selected squared-mass base wave has the rooted degree-four energy bound. -/
theorem energy_rootedRealSquareBaseWave_le (ρ : RotatorDualFace L → ℝ) :
    (squareZero L).energy (rootedRealSquareBaseWave ρ) ≤
      4 * ∑ j, rootedRealSquareBaseWave ρ j ^ 2 := by
  apply energy_supported_one_face_parity_le (rootedRealSquareBaseParity ρ)
    (rootedRealSquareBaseWave ρ) rfl
  intro x hx
  simp only [rootedRealSquareBaseWave] at hx
  split_ifs at hx with h
  · exact h
  · exact (hx rfl).elim

/-- Pairing the selected base wave with its source gives its squared mass. -/
theorem pairing_rootedRealSquareBaseWave (ρ : RotatorDualFace L → ℝ) :
    Multigraph.pairing (rootedRealSquareBaseWave ρ) ρ =
      ∑ j, rootedRealSquareBaseWave ρ j ^ 2 := by
  classical
  unfold Multigraph.pairing
  rw [Fintype.sum_option]
  rw [Fintype.sum_option (fun j => rootedRealSquareBaseWave ρ j ^ 2)]
  simp only [rootedRealSquareBaseWave]
  norm_num
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : squareParityColor x = rootedRealSquareBaseParity ρ
  · simp [h]
    ring
  · simp [h]

/-- The base part alone supplies the usual `‖ρ‖²/(16τ)` Gaussian gain on the wired carrier. -/
theorem translationEnergy_rootedRealSquareBaseWave_ge {τ : ℝ} (hτ : 0 < τ)
    (ρ : RotatorDualFace L → ℝ) :
    (∑ x : SquareFreeVertex L, ρ (some x) ^ 2) / (16 * τ) ≤
      translationEnergy (fun u => τ / 2 * u ^ 2) (gradLinear (squareZero L))
        (fun j => 1 / (4 * τ) * rootedRealSquareBaseWave ρ j) ρ := by
  rw [FroehlichSpencer.BKT.Generic.Marked.translationEnergy_gaussian_const_mul]
  have hpair := pairing_rootedRealSquareBaseWave ρ
  set M := ∑ j, rootedRealSquareBaseWave ρ j ^ 2 with hM
  have hhalf : (1 / 2 : ℝ) * ∑ x : SquareFreeVertex L, ρ (some x) ^ 2 ≤ M := by
    simpa [hM] using half_sq_mass_le_rootedRealSquareBase ρ
  have henergy : (squareZero L).energy (rootedRealSquareBaseWave ρ) ≤ 4 * M := by
    simpa [hM] using energy_rootedRealSquareBaseWave_le ρ
  have hcoef : 0 ≤ τ / 2 * (1 / (4 * τ)) ^ 2 := by positivity
  have hkey : 1 / (4 * τ) * M - τ / 2 * (1 / (4 * τ)) ^ 2 * (4 * M) = M / (8 * τ) := by
    field_simp
    ring
  have hmass : (∑ x : SquareFreeVertex L, ρ (some x) ^ 2) / (16 * τ) ≤ M / (8 * τ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [hpair]
  nlinarith [mul_le_mul_of_nonneg_left henergy hcoef]

/-- A finite family of P4.7-style profiles adds its fractional-cut gain to the rooted base wave.
The wave is root-zero whenever each profile is root-zero. -/
theorem rootedMarkedProfileEnergyLowerBound {τ : ℝ} (hτ : 0 < τ)
    (σ : RotatorDualFace L → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → RotatorDualFace L → ℝ) (q : ι → ℝ) {qStar : ℝ} (hqStar : 0 ≤ qStar)
    (hpair : ∀ t, Multigraph.pairing (ψ t) σ = q t)
    (hgap : ∀ t, qStar ≤ |q t|)
    (henergy : ∀ t, (squareZero L).energy (ψ t) ≤ 6400)
    (hdisj : ∀ t t', t ≠ t' → ∀ e,
      (squareZero L).grad (ψ t) e = 0 ∨ (squareZero L).grad (ψ t') e = 0)
    (hbase : ∀ t e,
      (squareZero L).grad (rootedRealSquareBaseWave σ) e = 0 ∨
        (squareZero L).grad (ψ t) e = 0) :
    ((∑ i : SquareFreeVertex L, σ (some i) ^ 2) / 16 +
      qStar ^ 2 / 12800 * Fintype.card ι) / τ ≤
      gffTranslationEnergy (squareZero L) τ
        (fun j => 1 / (4 * τ) * rootedRealSquareBaseWave σ j +
          ∑ t, q t / (τ * 6400) * ψ t j) σ := by
  classical
  let a : Option ι → RotatorDualFace L → ℝ := fun o => match o with
    | none => fun j => 1 / (4 * τ) * rootedRealSquareBaseWave σ j
    | some t => fun j => q t / (τ * 6400) * ψ t j
  have hg (c : ℝ) (f : RotatorDualFace L → ℝ) (e : SquareZeroBond L) :
      (gradLinear (squareZero L)) (fun j => c * f j) e = c * (squareZero L).grad f e := by
    show (squareZero L).grad (fun j => c * f j) e = c * (squareZero L).grad f e
    unfold Multigraph.grad
    ring
  have hdisjA : ∀ o ∈ (Finset.univ : Finset (Option ι)), ∀ o' ∈ Finset.univ,
      o ≠ o' → ∀ e, (gradLinear (squareZero L)) (a o) e = 0 ∨
        (gradLinear (squareZero L)) (a o') e = 0 := by
    intro o _ o' _ hne e
    cases o with
    | none =>
      cases o' with
      | none => exact absurd rfl hne
      | some t' =>
        rw [hg, hg]
        rcases hbase t' e with h | h
        · exact Or.inl (by rw [h, mul_zero])
        · exact Or.inr (by rw [h, mul_zero])
    | some t =>
      cases o' with
      | none =>
        rw [hg, hg]
        rcases hbase t e with h | h
        · exact Or.inr (by rw [h, mul_zero])
        · exact Or.inl (by rw [h, mul_zero])
      | some t' =>
        rw [hg, hg]
        rcases hdisj t t' (fun h => hne (by rw [h])) e with h | h
        · exact Or.inl (by rw [h, mul_zero])
        · exact Or.inr (by rw [h, mul_zero])
  have hsum : (fun j => 1 / (4 * τ) * rootedRealSquareBaseWave σ j +
      ∑ t, q t / (τ * 6400) * ψ t j) = fun j => ∑ o : Option ι, a o j := by
    funext j
    rw [Fintype.sum_option]
  have hbaseE : (∑ i : SquareFreeVertex L, σ (some i) ^ 2) / (16 * τ) ≤
      translationEnergy (fun u => τ / 2 * u ^ 2) (gradLinear (squareZero L)) (a none) σ := by
    simpa [a] using translationEnergy_rootedRealSquareBaseWave_ge hτ σ
  have hprofile : ∀ t, qStar ^ 2 / (12800 * τ) ≤
      translationEnergy (fun u => τ / 2 * u ^ 2) (gradLinear (squareZero L)) (a (some t)) σ := by
    intro t
    rw [FroehlichSpencer.BKT.Generic.Marked.translationEnergy_gaussian_const_mul, hpair t]
    have hq2 : qStar ^ 2 ≤ q t ^ 2 := by
      have := hgap t
      nlinarith [abs_nonneg (q t), sq_abs (q t)]
    have hcoef : 0 ≤ τ / 2 * (q t / (τ * 6400)) ^ 2 := by positivity
    have hkey : q t / (τ * 6400) * q t -
        τ / 2 * (q t / (τ * 6400)) ^ 2 * 6400 = q t ^ 2 / (12800 * τ) := by
      field_simp
      ring
    have h1 : qStar ^ 2 / (12800 * τ) ≤ q t ^ 2 / (12800 * τ) :=
      div_le_div_of_nonneg_right hq2 (by positivity)
    have hE := henergy t
    nlinarith [mul_le_mul_of_nonneg_left hE hcoef]
  have hprofileSum : Fintype.card ι * (qStar ^ 2 / (12800 * τ)) ≤
      ∑ t, translationEnergy (fun u => τ / 2 * u ^ 2) (gradLinear (squareZero L))
        (a (some t)) σ := by
    calc
      Fintype.card ι * (qStar ^ 2 / (12800 * τ)) =
          ∑ t, qStar ^ 2 / (12800 * τ) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun t _ => hprofile t
  rw [← FroehlichSpencer.BKT.Generic.Marked.translationEnergy_gaussian_real, hsum,
    SpinWave.translationEnergy_sum_of_grad_disjoint Finset.univ
      (fun u => τ / 2 * u ^ 2) (by simp) (gradLinear (squareZero L)) a σ hdisjA]
  have hsplit : ((∑ i : SquareFreeVertex L, σ (some i) ^ 2) / 16 +
      qStar ^ 2 / 12800 * Fintype.card ι) / τ =
      (∑ i : SquareFreeVertex L, σ (some i) ^ 2) / (16 * τ) +
        Fintype.card ι * (qStar ^ 2 / (12800 * τ)) := by
    field_simp
  rw [Fintype.sum_option (fun o : Option ι =>
    translationEnergy (fun u => τ / 2 * u ^ 2) (gradLinear (squareZero L)) (a o) σ)]
  rw [hsplit]
  exact add_le_add hbaseE hprofileSum

/-- Pairing distributes over a finite family sum in its first field. -/
private theorem pairing_fintype_sum_left {ι V : Type*} [Fintype ι] [Fintype V]
    (f : ι → V → ℝ) (g : V → ℝ) :
    Multigraph.pairing (fun v => ∑ i, f i v) g = ∑ i, Multigraph.pairing (f i) g := by
  classical
  unfold Multigraph.pairing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem pairing_const_mul_real {V : Type*} [Fintype V] (c : ℝ)
    (f g : V → ℝ) :
    Multigraph.pairing (fun j => c * f j) g = c * Multigraph.pairing f g := by
  classical
  unfold Multigraph.pairing
  calc
    (∑ j, c * f j * g j) = ∑ j, c * (f j * g j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ j, f j * g j := by rw [Finset.mul_sum]


theorem rootedMarkedComposite_profilePatch_gap {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n)
    (ξ : ℝ) (C T : Finset (RotatorDualFace (sideLength R) → ℤ))
    (ψ : RotatorDualFace (sideLength R) → ℝ) (S : Finset (Site R))
    (hpair : Multigraph.pairing ψ (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) =
      ∑ x ∈ S, rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x))
    (hproxy : ∑ x ∈ S,
      siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0) :
    Generic.Marked.dipoleGap ξ ≤
      |Multigraph.pairing ψ (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T)| := by
  rw [hpair]
  exact dipoleGap_le_abs_sum_rootedMarkedComposite hn hn0 ξ C T S hproxy


theorem rootedMarkedComposite_profileFamily_gap {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n)
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ))
    {ι : Type*} [Fintype ι]
    (ψ : ι → RotatorDualFace (sideLength R) → ℝ) (S : ι → Finset (Site R))
    (hpair : ∀ t, Multigraph.pairing (ψ t)
      (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) =
        ∑ x ∈ S t, rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x))
    (hproxy : ∀ t, ∑ x ∈ S t,
      siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0) :
    0 ≤ Generic.Marked.dipoleGap ξ ∧
      ∀ t, Generic.Marked.dipoleGap ξ ≤
        |Multigraph.pairing (ψ t)
          (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T)| := by
  refine ⟨le_of_lt (Generic.Marked.dipoleGap_pos hξ0 hξ1), ?_⟩
  intro t
  exact rootedMarkedComposite_profilePatch_gap hn hn0 ξ C T (ψ t) (S t)
    (hpair t) (hproxy t)

/--
Geometry forced on a density in the collapse family of a charged selected square.
-/
theorem profileA3_rootedMarked_collapse_member_data {L : ℕ}
    {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ : ChargeDensity L} (hρ : ρ ∈ F) {j : ℕ}
    {s : Finset (Generic.PinnedCharges.Site L)}
    (hs : s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j)
    (hq : totalCharge (chargeRestriction ρ s) ≠ 0)
    (σ : ChargeDensity L)
    (hσ : σ ∈ profileCollapseFamily F ρ j
      (chargeSupport (chargeRestriction ρ s))) :
    σ ∈ F ∧ σ ≠ ρ ∧ totalCharge σ = 0 ∧ σ ≠ 0 ∧
      boundaryAdjustedSize σ < boundaryAdjustedSize ρ ∧
      (65536 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤ 5 * 2 ^ j ∧
      (65526 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤ (9 / 4 : ℝ) * 2 ^ j ∧
      (65536 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤
        euclideanSetDistance (chargeSupport (chargeRestriction ρ s)) (chargeSupport σ) := by
  classical
  have hσmem := Finset.mem_filter.mp hσ
  have hσF : σ ∈ F := hσmem.1
  obtain ⟨hne, hneutral, hsmall, hnear⟩ := hσmem.2
  have hσ0 : σ ≠ 0 := hFzero σ hσF
  have hSq := chargedSelectedSquare_of_mem hs hq
  have hsize := profileA3_collapse_size_lt_parent j ρ σ hSq.size hσ0 (by
    simpa [chargeCoverScale_eq] using hsmall)
  have hparentSubset := profileA3_restriction_support_subset ρ s
  have hKne : (chargeSupport (chargeRestriction ρ s)).Nonempty :=
    chargeSupport_nonempty_of_ne_zero _ (by
      intro hzero
      exact hq (by simp [hzero, totalCharge]))
  have hM : (chargeCoverScale : ℝ) = 65536 := chargeCoverScale_eq
  have hα : chargeCoverExponent = (7 / 4 : ℝ) := rfl
  have hpair := hFsep ρ hρ σ hσF (Ne.symm hne)
  have hparentSep : (65536 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤
      euclideanSetDistance (chargeSupport (chargeRestriction ρ s)) (chargeSupport σ) := by
    have hpair' := Generic.PinnedCharges.SelectionG.setDist_le_of_subset
      hparentSubset subset_rfl hKne
      (chargeSupport_nonempty_of_ne_zero σ hσ0)
    have hmin : min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) =
        boundaryAdjustedSize σ := min_eq_right hsize.le
    rw [hM, hα, hmin] at hpair
    exact hpair.trans hpair'
  have hnear' : (profileA3NeutralNeighborhood σ ∩
      boundaryEnergyNeighborhood ((9 / 4 : ℝ) * 2 ^ j)
        (chargeSupport (chargeRestriction ρ s))).Nonempty := by
    simpa [profileA3NeutralNeighborhood] using hnear
  have hnearScale := profileA3_nearby_neutral_scale_bound (65536 : ℝ) (7 / 4 : ℝ)
    ((9 / 4 : ℝ) * 2 ^ j) F ρ σ (chargeSupport (chargeRestriction ρ s))
    hFsep hρ hσF (Ne.symm hne) hσ0 hparentSubset hsize.le (by norm_num) hnear'
  refine ⟨hσF, hne, hneutral, hσ0, hsize, ?_, ?_, hparentSep⟩
  · simpa [hM, hα] using hsmall
  · simpa [show (65536 : ℝ) - 10 = 65526 by norm_num] using hnearScale

private theorem profileA3_rootedMarked_ballReachable {L : ℕ}
    (𝓔 : Finset (Finset (Generic.PinnedCharges.Site L)))
    (E : Finset (Generic.PinnedCharges.Site L)) (hE : E ∈ 𝓔)
    (S : Finset (Generic.PinnedCharges.Site L)) (a : Generic.PinnedCharges.Site L)
    (ha : a ∈ S) (R : ℝ) {x : Generic.PinnedCharges.Site L}
    (hxd : euclideanSiteDistance x a ≤ R) (hEeq : E = boundaryEnergyNeighborhood R S) :
    (profileFreeGraph 𝓔).Reachable x a := by
  have aux : ∀ n, ∀ x : Generic.PinnedCharges.Site L, l1 x a = n →
      euclideanSiteDistance x a ≤ R → (profileFreeGraph 𝓔).Reachable x a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hlen hdist
      have hdist' : euclideanSiteDistance a x ≤ R := by
        rw [siteDist_comm]
        exact hdist
      by_cases hxa : x = a
      · subst x
        exact SimpleGraph.Reachable.rfl
      · obtain ⟨z, hxz, hzn, hzd⟩ := exists_step_toward hxa
        have hlt : l1 z a < n := by omega
        have hzd' : euclideanSiteDistance z a ≤ R := hzd.trans hdist
        have hxE : x ∈ E := by
          rw [hEeq, mem_boundaryEnergyNeighborhood_iff]
          exact ⟨a, ha, hdist'⟩
        have hzE : z ∈ E := by
          rw [hEeq, mem_boundaryEnergyNeighborhood_iff]
          have hzd'' : euclideanSiteDistance a z ≤ R := by
            rw [siteDist_comm]
            exact hzd'
          exact ⟨a, ha, hzd''⟩
        have hadj : (profileFreeGraph 𝓔).Adj x z := ⟨hxz, ⟨E, hE, hxE, hzE⟩⟩
        exact (SimpleGraph.Adj.reachable hadj).trans (ih (l1 z a) hlt z rfl hzd')
  exact aux (l1 x a) x rfl hxd

private theorem profileA3_rootedMarked_neighborhood_reachable {L : ℕ}
    (𝓔 : Finset (Finset (Generic.PinnedCharges.Site L))) (σ : ChargeDensity L)
    (hE : profileA3NeutralNeighborhood σ ∈ 𝓔) {x y : Generic.PinnedCharges.Site L}
    (hx : x ∈ profileA3NeutralNeighborhood σ) (hy : y ∈ profileA3NeutralNeighborhood σ) :
    (profileFreeGraph 𝓔).Reachable x y := by
  let R := 8 * boundaryAdjustedSize σ + 2
  obtain ⟨a, ha, hxa⟩ := (mem_boundaryEnergyNeighborhood_iff R
    (chargeSupport σ) x).mp (by simpa [R, profileA3NeutralNeighborhood] using hx)
  obtain ⟨b, hb, hyb⟩ := (mem_boundaryEnergyNeighborhood_iff R
    (chargeSupport σ) y).mp (by simpa [R, profileA3NeutralNeighborhood] using hy)
  have hab : euclideanSiteDistance a b ≤ boundaryAdjustedSize σ :=
    (siteDist_le_diam ha hb).trans (chargeEuclideanDiameter_le_boundaryAdjustedSize σ)
  have hbound : boundaryAdjustedSize σ ≤ R := by
    dsimp [R]
    linarith [boundaryAdjustedSize_nonneg σ]
  have hxa' := profileA3_rootedMarked_ballReachable 𝓔
    (profileA3NeutralNeighborhood σ) hE (chargeSupport σ) a ha R
    (by rw [siteDist_comm]; exact hxa) rfl
  have hab' := profileA3_rootedMarked_ballReachable 𝓔
    (profileA3NeutralNeighborhood σ) hE (chargeSupport σ) a ha R
    (by rw [siteDist_comm]; exact hab.trans hbound) rfl
  have hyb' := profileA3_rootedMarked_ballReachable 𝓔
    (profileA3NeutralNeighborhood σ) hE (chargeSupport σ) b hb R
    (by rw [siteDist_comm]; exact hyb) rfl
  exact hxa'.trans (hab'.symm.trans hyb'.symm)

private theorem profileA3_rootedMarked_collapsedComponent_eq_overlapUnion {L : ℕ}
    (F : Finset (ChargeDensity L)) (y : Generic.PinnedCharges.Site L)
    (σ : ChargeDensity L) (hσ : σ ∈ F)
    (hy : y ∈ profileA3NeutralNeighborhood σ) :
    collapsedComponent (F.image profileA3NeutralNeighborhood) y =
      profileA3LabelUnion (fun a : {τ : ChargeDensity L // τ ∈ F} => a.val)
        (profileA3GraphComponentVertices
          ((profileA3OverlapGraph F).connectedComponentMk ⟨σ, hσ⟩)) := by
  classical
  let 𝓔 := F.image profileA3NeutralNeighborhood
  let G := profileA3OverlapGraph F
  let a : {τ : ChargeDensity L // τ ∈ F} := ⟨σ, hσ⟩
  let c := G.connectedComponentMk a
  have hEσ : profileA3NeutralNeighborhood σ ∈ 𝓔 := Finset.mem_image.mpr ⟨σ, hσ, rfl⟩
  have hforward : ∀ {x}, x ∈ collapsedComponent 𝓔 y →
      x ∈ profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F} => t.val)
        (profileA3GraphComponentVertices c) := by
    intro x hx
    have hreach := mem_collapsedComponent.mp hx
    let P : Generic.PinnedCharges.Site L → Prop := fun z =>
      ∃ t : {τ : ChargeDensity L // τ ∈ F},
        z ∈ profileA3NeutralNeighborhood t.val ∧ G.connectedComponentMk t = c
    have hstart : P y := ⟨a, hy, rfl⟩
    have hstep : ∀ ⦃u v⦄, P u → (profileFreeGraph 𝓔).Adj u v → P v := by
      intro u v hu huv
      rcases hu with ⟨t, hut, htc⟩
      obtain ⟨-, hc⟩ := huv
      obtain ⟨E, hE, huE, hvE⟩ := hc
      obtain ⟨τ, hτ, hEeq⟩ := Finset.mem_image.mp hE
      have huτ : u ∈ profileA3NeutralNeighborhood τ := by simpa [hEeq] using huE
      have hvτ : v ∈ profileA3NeutralNeighborhood τ := by simpa [hEeq] using hvE
      let t' : {τ : ChargeDensity L // τ ∈ F} := ⟨τ, hτ⟩
      have htc' : G.connectedComponentMk t' = c := by
        by_cases heq : t.val = τ
        · have hnodes : t = t' := Subtype.ext heq
          simpa [hnodes] using htc
        · have hadj : G.Adj t t' := ⟨heq, ⟨u, Finset.mem_inter.mpr ⟨hut, huτ⟩⟩⟩
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans htc
      exact ⟨t', hvτ, htc'⟩
    have hxP := hreach.elim fun p => profileA3_walk_preserves hstep p hstart
    rcases hxP with ⟨t, hxt, htc⟩
    exact Finset.mem_biUnion.mpr ⟨t, (mem_profileA3GraphComponentVertices c t).mpr htc, hxt⟩
  have hbackward : ∀ {x},
      x ∈ profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F} => t.val)
        (profileA3GraphComponentVertices c) → x ∈ collapsedComponent 𝓔 y := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨t, htC, hxt⟩
    have hnodes : G.connectedComponentMk t = c :=
      (mem_profileA3GraphComponentVertices c t).mp htC
    have hpath : G.Reachable a t := by
      apply SimpleGraph.ConnectedComponent.eq.mp
      exact rfl.trans hnodes.symm
    let P : {τ : ChargeDensity L // τ ∈ F} → Prop := fun u =>
      ∀ z, z ∈ profileA3NeutralNeighborhood u.val → (profileFreeGraph 𝓔).Reachable y z
    have hstart : P a := by
      intro z hz
      exact profileA3_rootedMarked_neighborhood_reachable 𝓔 σ hEσ hy hz
    have hstep : ∀ ⦃u v⦄, P u → G.Adj u v → P v := by
      intro u v hu huv z hz
      obtain ⟨q, hq⟩ := huv.2
      have hEv : profileA3NeutralNeighborhood v.val ∈ 𝓔 :=
        Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩
      have hyq := hu q (Finset.mem_inter.mp hq).1
      have hqz := profileA3_rootedMarked_neighborhood_reachable 𝓔 v.val hEv
        (Finset.mem_inter.mp hq).2 hz
      exact hyq.trans hqz
    have htx := hpath.elim fun p => profileA3_walk_preserves hstep p hstart
    have hyx := htx x hxt
    exact mem_collapsedComponent.mpr hyx
  ext x
  exact ⟨hforward, hbackward⟩

/-- The collapse-family decomposition used by the profile potential only needs pairwise
Appendix-D separation of its nonzero members. -/
theorem profileA3_rootedMarked_uniqueMaxDecomposition {L : ℕ}
    {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    (ρ : ChargeDensity L) (j : ℕ) (K : Finset (Generic.PinnedCharges.Site L)) :
    ProfileA3UniqueMaxDecomposition F ρ j K := by
  classical
  intro y hy
  let F' := profileCollapseFamily F ρ j K
  obtain ⟨E, hE, hyE⟩ := hy
  obtain ⟨σ, hσ, hEeq⟩ := Finset.mem_image.mp hE
  have hyσ : y ∈ profileA3NeutralNeighborhood σ := by simpa [hEeq] using hyE
  have hzero : ∀ t : {τ : ChargeDensity L // τ ∈ F'}, t.val ≠ 0 := by
    intro t
    exact hFzero t.val (Finset.mem_filter.mp t.property).1
  have hAdj : ∀ ⦃u v : {τ : ChargeDensity L // τ ∈ F'}⦄,
      (profileA3OverlapGraph F').Adj u v →
        (profileA3NeutralNeighborhood u.val ∩ profileA3NeutralNeighborhood v.val).Nonempty :=
    fun _ _ huv => huv.2
  have hsep : ∀ ⦃u v : {τ : ChargeDensity L // τ ∈ F'}⦄, u ≠ v →
      (65536 : ℝ) * min (boundaryAdjustedSize u.val) (boundaryAdjustedSize v.val) ^
          (7 / 4 : ℝ) ≤
        euclideanSetDistance (chargeSupport u.val) (chargeSupport v.val) := by
    intro u v huv
    have hval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    have hpair := hFsep u.val (Finset.mem_filter.mp u.property).1
      v.val (Finset.mem_filter.mp v.property).1 hval
    simpa [chargeCoverScale_eq,
      (show chargeCoverExponent = (7 / 4 : ℝ) from rfl)] using hpair
  let G := profileA3OverlapGraph F'
  let a : {τ : ChargeDensity L // τ ∈ F'} := ⟨σ, hσ⟩
  let c := G.connectedComponentMk a
  have hdecomp := profileA3_separated_component_decomposition_strong
    (profileA3GraphComponentVertices c).card
    (fun t : {τ : ChargeDensity L // τ ∈ F'} => t.val)
    Subtype.val_injective G hAdj hzero hsep c rfl
  have hCeq : collapsedComponent (profileCollapsedSets F ρ j K) y =
      profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F'} => t.val)
        (profileA3GraphComponentVertices c) := by
    have hgraph : collapsedComponent (F'.image profileA3NeutralNeighborhood) y =
        profileA3LabelUnion (fun t : {τ : ChargeDensity L // τ ∈ F'} => t.val)
          (profileA3GraphComponentVertices
            ((profileA3OverlapGraph F').connectedComponentMk ⟨σ, hσ⟩)) :=
      profileA3_rootedMarked_collapsedComponent_eq_overlapUnion F' y σ hσ hyσ
    simpa only [profileCollapsedSets, G, a, c, F'] using hgraph
  obtain ⟨v, hv, hvmax, hvsmall, pieces, hcover, hpiecesdiam, hpiecesattach, hdiam⟩ := hdecomp
  rw [hCeq, hcover]
  exact ⟨v.val, v.property, pieces, rfl, hpiecesdiam, hpiecesattach⟩

/-- The collapsed-potential support estimate on one charged selected square of any pinned,
Appendix-D-separated ensemble. -/
theorem profileA3_rootedMarked_collapsedSupportControl {L : ℕ}
    {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ : ChargeDensity L} (hρ : ρ ∈ F) {j : ℕ} {s : Finset (Generic.PinnedCharges.Site L)}
    (hs : s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j)
    (hq : totalCharge (chargeRestriction ρ s) ≠ 0)
    (hroot : ProfileA3RootedComponents F ρ j
      (chargeSupport (chargeRestriction ρ s))) :
    ProfileA3CollapsedSupportControl j (chargeSupport (chargeRestriction ρ s))
      (profileCollapsedPotential F ρ j (chargeSupport (chargeRestriction ρ s))) := by
  classical
  set K := chargeSupport (chargeRestriction ρ s) with hK
  set 𝓔 := profileCollapsedSets F ρ j K with h𝓔
  set d := profileCollapsedPotential F ρ j K with hd
  intro x hx
  have hlt : collapsedDistance 𝓔 K (2 ^ (j + 1)) x < 2 ^ (j + 1) := by
    have hx' : ((collapsedDistance 𝓔 K (2 ^ (j + 1)) x : ℕ) : ℝ) <
        ((2 ^ (j + 1) : ℕ) : ℝ) := by
      push_cast
      exact hx
    exact_mod_cast hx'
  obtain ⟨k, hk, w, hw⟩ := exists_walk_of_lt hlt
  have hdx : d x = (collapsedDistance 𝓔 K (2 ^ (j + 1)) x : ℝ) := rfl
  have hcost : pathCost 𝓔 (k :: w.support.tail) = collapsedDistance 𝓔 K (2 ^ (j + 1)) x := by
    rw [← support_eq_cons_tail w, ← collapsedCost_eq_pathCost, hw]
  have hd0 : 0 ≤ d x := by rw [hdx]; exact Nat.cast_nonneg _
  set root : Finset (Generic.PinnedCharges.Site L) → ChargeDensity L :=
    fun C => profileA3RootOf F ρ j K C with hrootdef
  set δ : Finset (Generic.PinnedCharges.Site L) → ℝ :=
    fun C => 40 * boundaryAdjustedSize (root C) with hδdef
  have hspec : ∀ y, InCollapsed 𝓔 y → _ := fun y hy => profileA3RootOf_spec hroot hy
  have hδ : ∀ y, InCollapsed 𝓔 y → 0 ≤ δ (collapsedComponent 𝓔 y) ∧
      ∀ z ∈ collapsedComponent 𝓔 y, ∀ z' ∈ collapsedComponent 𝓔 y,
        euclideanSiteDistance z z' ≤ δ (collapsedComponent 𝓔 y) := by
    intro y hy
    obtain ⟨-, -, -, hdiam⟩ := hspec y hy
    refine ⟨by have := boundaryAdjustedSize_nonneg (root (collapsedComponent 𝓔 y)); positivity,
      fun z hz z' hz' => (euclideanSiteDistance_le_profileA3GraphLength z z').trans
        (hdiam z hz z' hz')⟩
  have hchain : List.IsChain (fun a b => l1 a b = 1) (k :: w.support.tail) := by
    rw [← support_eq_cons_tail w]
    exact isChain_support w
  have hlast : (k :: w.support.tail).getLast? = some x := by
    rw [← support_eq_cons_tail w]
    exact getLast?_support w
  obtain ⟨V, pos, hV1, hV2, hV3, hV4, hV5⟩ :=
    exists_collapsedPathData 𝓔 δ hδ w.support.tail k x hchain hlast
  rw [hcost] at hV2 hV3
  have hendK : euclideanSetDistance K {x} ≤ euclideanSiteDistance k x :=
    setDist_le_siteDist hk (Finset.mem_singleton_self x)
  rcases V.eq_empty_or_nonempty with hVe | hVne
  · rw [hVe, Finset.sum_empty, add_zero] at hV2
    rw [← hdx] at hV2
    linarith
  have hdata : ∀ C ∈ V, ∃ y, InCollapsed 𝓔 y ∧ C = collapsedComponent 𝓔 y := by
    intro C hC
    obtain ⟨y, -, hy, hyC⟩ := hV1 C hC
    exact ⟨y, hy, hyC⟩
  choose yOf hyOf hCy using hdata
  have hmember : ∀ C ∈ V,
      root C ∈ profileCollapseFamily F ρ j K ∧ chargeSupport (root C) ⊆ C ∧
      ProfileA3ComponentRootedAt C (root C) (boundaryAdjustedSize (root C)) ∧
      ∀ z ∈ C, ∀ z' ∈ C,
        profileA3GraphLength z z' ≤ 40 * boundaryAdjustedSize (root C) := by
    intro C hC
    have h := hspec (yOf C hC) (hyOf C hC)
    rw [← h𝓔, ← hCy C hC] at h
    exact h
  have hmemberData : ∀ C ∈ V, _ := fun C hC =>
    profileA3_rootedMarked_collapse_member_data hFzero hFsep hρ hs hq
      (root C) (hmember C hC).1
  have hsize1 : ∀ C ∈ V, 1 ≤ boundaryAdjustedSize (root C) := fun C hC =>
    one_le_boundaryAdjustedSize (hmemberData C hC).2.2.2.1
  have hCne : ∀ C ∈ V, C.Nonempty := fun C hC => by
    have h := mem_collapsedComponent_self 𝓔 (yOf C hC)
    rw [← hCy C hC] at h
    exact ⟨_, h⟩
  have hδnn : ∀ C ∈ V, 0 ≤ δ C := fun C hC => by
    have := hsize1 C hC
    simp only [hδdef]
    linarith
  obtain ⟨Cs, hCs, hCsmax⟩ := V.exists_max_image (fun C => boundaryAdjustedSize (root C)) hVne
  set budget := d x + ∑ C ∈ V, δ C with hbudget
  have hposb : ∀ C ∈ V, 0 ≤ pos C ∧ pos C ≤ budget := by
    intro C hC
    obtain ⟨h1, h2⟩ := hV3 C hC
    have := hδnn C hC
    rw [← hdx] at h2
    exact ⟨h1, by linarith⟩
  have hSq := chargedSelectedSquare_of_mem hs hq
  have hKne : K.Nonempty := chargeSupport_nonempty_of_ne_zero _
    (fun h0 => hq (by simp [h0, totalCharge]))
  have hKρ : K ⊆ chargeSupport ρ := profileA3_restriction_support_subset ρ s
  have hM : (chargeCoverScale : ℝ) = 65536 := chargeCoverScale_eq
  have hα : chargeCoverExponent = (7 / 4 : ℝ) := rfl
  let W : ProfileA3PathWitness K d x :=
    { Index := Finset (Generic.PinnedCharges.Site L)
      indexDecidableEq := inferInstance
      components := V
      size := fun C => boundaryAdjustedSize (root C)
      diameter := δ
      bin := fun C => profileA3Bin (boundaryAdjustedSize (root C))
      maxBin := profileA3Bin (boundaryAdjustedSize (root Cs))
      budget := budget
      maxSize := boundaryAdjustedSize (root Cs)
      parentSize := boundaryAdjustedSize ρ
      parentDistance := euclideanSetDistance K Cs
      collapsed_nonneg := hd0
      packing :=
        { budget_nonneg := by
            have := Finset.sum_nonneg hδnn
            rw [hbudget]
            linarith
          max_lower := two_pow_profileA3Bin_le (hsize1 Cs hCs)
          max_upper := hCsmax
          bin_bound := fun C hC => profileA3Bin_mono (hCsmax C hC)
          bin_lower := fun C hC => two_pow_profileA3Bin_le (hsize1 C hC)
          bin_upper := fun C hC => lt_two_pow_profileA3Bin_succ _
          position := pos
          position_bounds := hposb
          same_bin_separation := by
            intro C hC C' hC' hbin hne
            obtain ⟨u, hu, u', hu', huu'⟩ := hV5 C hC C' hC' hne
            obtain ⟨hσF, hσsupp, hσroot, -⟩ := hmember C hC
            obtain ⟨hσF', hσsupp', hσroot', -⟩ := hmember C' hC'
            have hdisj : Disjoint C C' := by
              rw [hCy C hC, hCy C' hC']
              apply disjoint_collapsedComponent
              rw [← hCy C hC, ← hCy C' hC']
              exact hne
            have hσne : root C ≠ root C' := by
              intro heq
              obtain ⟨a, ha⟩ := chargeSupport_nonempty_of_ne_zero _
                (hmemberData C hC).2.2.2.1
              exact Finset.disjoint_left.mp hdisj (hσsupp ha) (hσsupp' (heq ▸ ha))
            have hsep := hFsep (root C) (hmemberData C hC).1
              (root C') (hmemberData C' hC').1 hσne
            rw [hM, hα] at hsep
            have hcomp := profileA3_distinct_components_separation (65536 : ℝ) (7 / 4 : ℝ)
              (boundaryAdjustedSize (root C)) (boundaryAdjustedSize (root C'))
              (root C) (root C') C C' hsep hσroot hσroot' (hCne C hC) (hCne C' hC')
            have hdist : euclideanSetDistance C C' ≤ euclideanSiteDistance u u' :=
              setDist_le_siteDist hu hu'
            have hnum := sameBin_separation_le
              (D := boundaryAdjustedSize (root C))
              (D' := boundaryAdjustedSize (root C'))
              (profileA3Bin (boundaryAdjustedSize (root C)))
              (two_pow_profileA3Bin_le (hsize1 C hC))
              (by rw [hbin]; exact two_pow_profileA3Bin_le (hsize1 C' hC'))
              (lt_two_pow_profileA3Bin_succ _)
              (by rw [hbin]; exact lt_two_pow_profileA3Bin_succ _)
            linarith }
      max_size_lower := two_pow_profileA3Bin_le (hsize1 Cs hCs)
      component_diameter := fun C _ => le_rfl
      parent_scale_order := (hmemberData Cs hCs).2.2.2.2.1.le
      parent_component_separation := by
        obtain ⟨hσF, -, hσroot, -⟩ := hmember Cs hCs
        have hsep := hFsep ρ hρ (root Cs) (hmemberData Cs hCs).1
          (hmemberData Cs hCs).2.1.symm
        rw [hM, hα] at hsep
        exact profileA3_parent_component_separation (65536 : ℝ) (7 / 4 : ℝ)
          (boundaryAdjustedSize ρ) (boundaryAdjustedSize (root Cs)) ρ (root Cs) K Cs hsep
          hσroot hKρ hKne (hCne Cs hCs)
      parent_path_length := by
        obtain ⟨u, hu, hku⟩ := hV4 Cs hCs
        exact (setDist_le_siteDist hk hu).trans (hku.trans (hposb Cs hCs).2)
      budget_eq := rfl
      endpoint_bound := by
        rw [← hdx] at hV2
        exact hendK.trans hV2 }
  exact le_nine_eighths_of_profileA3PathWitness W

/-- A pinned Appendix-D-separated family supplies the full P4.7 context for each charged
selected square. The rooted marked extension therefore uses the same profile potentials as the
comb-terminal construction, without assuming a comb history. -/
theorem rootedMarkedProfileContext_of_mem {L : ℕ}
    {F : Finset (ChargeDensity L)} (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ : ChargeDensity L} (hρ : ρ ∈ F) {j : ℕ} {s : Finset (Generic.PinnedCharges.Site L)}
    (hj : 1 ≤ j) (hs : s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j)
    (hq : totalCharge (chargeRestriction ρ s) ≠ 0) :
    ProfileContext F ρ j s (profilePotential F ρ j
      (chargeSupport (chargeRestriction ρ s))) := by
  classical
  have hunique := profileA3_rootedMarked_uniqueMaxDecomposition hFzero hFsep ρ j
    (chargeSupport (chargeRestriction ρ s))
  have hroot := profileA3RootedComponents_of_uniqueMaxDecomposition hFzero hunique
  have hsupport := profileA3_rootedMarked_collapsedSupportControl hFzero hFsep hρ hs hq hroot
  refine ⟨hFsep, hFzero, hρ, hj, ?_, chargedSelectedSquare_of_mem hs hq,
    profilePotential_spec (⟨_, isProfilePotential_of_supportControl hsupport⟩)⟩
  simpa [selectedSquares] using hs

/-- The rooted profile context of each member of the established P4.7 index. -/
theorem rootedMarkedProfileContext_of_profileIndex {L : ℕ}
    {F : Finset (ChargeDensity L)} (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ϱ : RotatorDualFace L → ℤ} (hϱ : ϱ ∈ F.image neutralizeAtWiredRoot)
    (t : Σ _j : ℕ, Finset (Generic.PinnedCharges.Site L)) (ht : t ∈ profileIndex ϱ) :
    ProfileContext F (siteRestrict ϱ) t.1 t.2
      (profilePotential F (siteRestrict ϱ) t.1
        (profileCluster ϱ t)) := by
  classical
  obtain ⟨hρ, hϱeq⟩ := siteRestrict_mem_of_mem_image hϱ
  obtain ⟨hj, hs⟩ := Finset.mem_sigma.mp ht
  have hj' := (Finset.mem_filter.mp hj).1
  have hs' : t.2 ∈ selectedSquares ϱ t.1 ∧
      totalCharge (chargeRestriction (siteRestrict ϱ) t.2) ≠ 0 := by
    unfold goodSquares at hs
    exact Finset.mem_filter.mp hs
  have hsel : t.2 ∈ selectedSquares (neutralizeAtWiredRoot (siteRestrict ϱ)) t.1 := by
    simpa [hϱeq] using hs'.1
  have hc := rootedMarkedProfileContext_of_mem hFzero hFsep hρ
    (Finset.mem_Icc.mp hj').1 hsel hs'.2
  simpa [profileCluster] using hc

/-- A profile pairs with any real charge having the same face support as its pinned density by
the charge restricted to its selected square. -/
theorem ProfileContext.pairing_profilePiece_of_faceSupportEq {L : ℕ}
    {F : Finset (ChargeDensity L)} {ρ : ChargeDensity L} {j : ℕ}
    {s : Finset (Generic.PinnedCharges.Site L)} {f : Generic.PinnedCharges.Site L → ℝ}
    (h : ProfileContext F ρ j s f) (σ : RotatorDualFace L → ℝ)
    (hsupp : ∀ x, σ (some x) ≠ 0 ↔ neutralizeAtWiredRoot ρ (some x) ≠ 0) :
    Multigraph.pairing (profilePiece j f) σ = ∑ x ∈ s, σ (some x) := by
  classical
  unfold Multigraph.pairing
  rw [Fintype.sum_option, profilePiece_none, zero_mul, zero_add]
  have hsum : ∑ x : Generic.PinnedCharges.Site L,
      profileRamp j (f x) * σ (some x) = ∑ x ∈ s, σ (some x) := by
    calc
      (∑ x, profileRamp j (f x) * σ (some x)) =
          ∑ x, if x ∈ s then σ (some x) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hxs : x ∈ s
            · by_cases hσx : σ (some x) = 0
              · simp [hxs, hσx]
              · have hρx : neutralizeAtWiredRoot ρ (some x) ≠ 0 :=
                  (hsupp x).mp hσx
                have hK : x ∈ chargeSupport (chargeRestriction ρ s) :=
                  (mem_chargeSupport_restriction_iff ρ s x).mpr
                    ⟨hxs, by simpa [chargeSupport] using hρx⟩
                rw [h.ramp_eq_one_of_l1 hK (by rw [l1_self, Nat.cast_zero]; positivity)]
                simp [hxs]
            · by_cases hσx : σ (some x) = 0
              · simp [hxs, hσx]
              · have hρx : neutralizeAtWiredRoot ρ (some x) ≠ 0 :=
                  (hsupp x).mp hσx
                have hxρ : x ∈ chargeSupport ρ := by
                  simpa [chargeSupport] using hρx
                have hnot : ¬ IsProfileNear ρ j s x := by
                  intro hnear
                  exact hxs (mem_chargeSupport_restriction_iff ρ s x |>.mp
                    (h.mem_cluster_of_near hnear hxρ)).1
                rw [h.ramp_eq_zero_of_not_near hnot]
                simp [hxs]
      _ = ∑ x ∈ s, σ (some x) := by
        rw [Finset.sum_ite_mem]
        simp
  exact hsum

/-- Every nonzero edge gradient of the squared-mass base wave is incident to a nonzero face of its
source. -/
theorem exists_face_of_rootedRealSquareBaseWave_grad_ne {L : ℕ}
    (σ : RotatorDualFace L → ℝ) (e : SquareZeroBond L)
    (he : (squareZero L).grad (rootedRealSquareBaseWave σ) e ≠ 0) :
    ∃ x : SquareFreeVertex L, σ (some x) ≠ 0 ∧
      ((squareZero L).src e = some x ∨ (squareZero L).tgt e = some x) := by
  have hbase : ∀ x, rootedRealSquareBaseWave σ (some x) ≠ 0 → σ (some x) ≠ 0 := by
    intro x hx hz
    apply hx
    simp [rootedRealSquareBaseWave, hz]
  cases e with
  | inl f =>
    change rootedRealSquareBaseWave σ (some f.1.1) -
      rootedRealSquareBaseWave σ (some f.1.2) ≠ 0 at he
    by_cases hleft : rootedRealSquareBaseWave σ (some f.1.1) ≠ 0
    · exact ⟨f.1.1, hbase f.1.1 hleft, Or.inl rfl⟩
    · have hright : rootedRealSquareBaseWave σ (some f.1.2) ≠ 0 := by
        intro hr
        have hleft0 : rootedRealSquareBaseWave σ (some f.1.1) = 0 := by
          simpa using hleft
        apply he
        simp [hleft0, hr]
      exact ⟨f.1.2, hbase f.1.2 hright, Or.inr rfl⟩
  | inr k =>
    change rootedRealSquareBaseWave σ (some k.1) -
      rootedRealSquareBaseWave σ none ≠ 0 at he
    have hface : rootedRealSquareBaseWave σ (some k.1) ≠ 0 := by
      simpa [rootedRealSquareBaseWave] using he
    exact ⟨k.1, hbase k.1 hface, Or.inl rfl⟩

/-- Profile gradients vanish on edges carrying the base source, so their energies can be added
without cross terms. -/
theorem ProfileContext.grad_profilePiece_zero_of_rootedBase_grad_ne {L : ℕ}
    {F : Finset (ChargeDensity L)} {ρ : ChargeDensity L} {j : ℕ}
    {s : Finset (Generic.PinnedCharges.Site L)} {f : Generic.PinnedCharges.Site L → ℝ}
    (h : ProfileContext F ρ j s f) (hL : 1 < L)
    (σ : RotatorDualFace L → ℝ)
    (hsupp : ∀ x, σ (some x) ≠ 0 ↔ neutralizeAtWiredRoot ρ (some x) ≠ 0)
    (e : SquareZeroBond L)
    (he : (squareZero L).grad (rootedRealSquareBaseWave σ) e ≠ 0) :
    (squareZero L).grad (profilePiece j f) e = 0 := by
  obtain ⟨x, hxσ, hinc⟩ := exists_face_of_rootedRealSquareBaseWave_grad_ne σ e he
  have hxρ : neutralizeAtWiredRoot ρ (some x) ≠ 0 := (hsupp x).mp hxσ
  have hx : x ∈ chargeSupport ρ := by simpa [chargeSupport] using hxρ
  exact h.grad_eq_zero_of_incident hL h.mem hx hinc

/-- The finite set of P4.7 profiles attached to a rooted integer proxy. -/
def rootedMarkedP4Index {L : ℕ} (p : RotatorDualFace L → ℤ) :=
  {t : Σ _j : ℕ, Finset (Generic.PinnedCharges.Site L) // t ∈ profileIndex p}

noncomputable instance rootedMarkedP4IndexFintype {L : ℕ}
    (p : RotatorDualFace L → ℤ) : Fintype (rootedMarkedP4Index p) := by
  classical
  exact Fintype.ofFinset (profileIndex p) (fun _ => Iff.rfl)

/-- The mod-three P4.7 selection retains at least one third of the proxy's charged selected
squares. -/
theorem rootedMarkedP4Index_covers_goodSquares {L : ℕ}
    (p : RotatorDualFace L → ℤ) :
    goodSelectedSum p ≤ 3 * (Fintype.card (rootedMarkedP4Index p) : ℝ) := by
  have hcard : ((Fintype.card (rootedMarkedP4Index p) : ℕ) : ℝ) =
      ((profileIndex p).card : ℝ) := by
    simp [rootedMarkedP4Index, Fintype.card_coe]
  calc
    goodSelectedSum p ≤ 3 * residueSum p (profileResidue p) :=
      goodSelectedSum_le_three_mul p
    _ = 3 * ((profileIndex p).card : ℝ) := by rw [card_profileIndex]
    _ = 3 * (Fintype.card (rootedMarkedP4Index p) : ℝ) := by rw [← hcard]

/-- The pinned profile wave at an index of the rooted proxy. -/
def rootedMarkedP4Wave {L : ℕ} (F : Finset (ChargeDensity L))
    (p : RotatorDualFace L → ℤ) (t : rootedMarkedP4Index p) :
    RotatorDualFace L → ℝ := profileFamilyPiece F p t.val

/-- Each proxy profile has the P4.7 context supplied by the extension geometry. -/
theorem rootedMarkedP4Context {L : ℕ} {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {p : RotatorDualFace L → ℤ} (hp : p ∈ F.image neutralizeAtWiredRoot)
    (t : rootedMarkedP4Index p) :
    ProfileContext F (siteRestrict p) t.val.1 t.val.2
      (profilePotential F (siteRestrict p) t.val.1
        (profileCluster p t.val)) :=
  rootedMarkedProfileContext_of_profileIndex hFzero hFsep hp t.val t.property

/-- The proxy profile family consists of root-zero pieces with the uniform P4.7 energy bound. -/
theorem rootedMarkedP4Wave_root_energy {L : ℕ} {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {p : RotatorDualFace L → ℤ} (hp : p ∈ F.image neutralizeAtWiredRoot)
    (hL : 1 < L) (t : rootedMarkedP4Index p) :
    rootedMarkedP4Wave F p t none = 0 ∧
      (squareZero L).energy (rootedMarkedP4Wave F p t) ≤ 6400 := by
  let hc := rootedMarkedP4Context hFzero hFsep hp t
  constructor
  · simp [rootedMarkedP4Wave, profileFamilyPiece, profilePiece]
  · simpa [rootedMarkedP4Wave, profileFamilyPiece] using hc.energy_profilePiece_le hL

/-- The profile wave pairs with a real source by its charge on the selected square, whenever the
source has the proxy's face support. -/
theorem rootedMarkedP4Wave_pairing_patch {L : ℕ} {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {p : RotatorDualFace L → ℤ} (hp : p ∈ F.image neutralizeAtWiredRoot)
    (t : rootedMarkedP4Index p) (σ : RotatorDualFace L → ℝ)
    (hsupp : ∀ x, σ (some x) ≠ 0 ↔ neutralizeAtWiredRoot (siteRestrict p) (some x) ≠ 0) :
    Multigraph.pairing (rootedMarkedP4Wave F p t) σ =
      ∑ x ∈ t.val.2, σ (some x) := by
  simpa [Multigraph.pairing, rootedMarkedP4Wave, profileFamilyPiece] using
    ProfileContext.pairing_profilePiece_of_faceSupportEq
      (rootedMarkedP4Context hFzero hFsep hp t) σ hsupp

/-- Distinct profiles of one proxy have disjoint gradient supports, by the mod-three scale
selection and the P4.7 same-density separation lemma. -/
theorem rootedMarkedP4Wave_grad_disjoint {L : ℕ} {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {p : RotatorDualFace L → ℤ} (hp : p ∈ F.image neutralizeAtWiredRoot)
    (hL : 1 < L) {t t' : rootedMarkedP4Index p} (hne : t ≠ t')
    (e : SquareZeroBond L) :
    (squareZero L).grad (rootedMarkedP4Wave F p t) e = 0 ∨
      (squareZero L).grad (rootedMarkedP4Wave F p t') e = 0 := by
  classical
  let hc := rootedMarkedP4Context hFzero hFsep hp t
  let hc' := rootedMarkedP4Context hFzero hFsep hp t'
  obtain ⟨hj, _⟩ := Finset.mem_sigma.mp t.property
  obtain ⟨hj', _⟩ := Finset.mem_sigma.mp t'.property
  have hr : t.val.1 % 3 = t'.val.1 % 3 := by
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := (Finset.mem_filter.mp hj').2
    rw [h1, h2]
  rcases lt_trichotomy t.val.1 t'.val.1 with hlt | heq | hgt
  · have hgap : t.val.1 + 3 ≤ t'.val.1 := by omega
    rcases hc'.grad_disjoint_same hc hL (Or.inr hgap) e with h' | h
    · exact Or.inr h'
    · exact Or.inl h
  · have hsq : t.val.2 ≠ t'.val.2 := by
      intro hs
      apply hne
      apply Subtype.ext
      exact Sigma.ext heq (heq_of_eq hs)
    simpa [rootedMarkedP4Wave, profileFamilyPiece] using
      hc.grad_disjoint_same hc' hL (Or.inl ⟨heq, hsq⟩) e
  · have hgap : t'.val.1 + 3 ≤ t.val.1 := by omega
    exact hc.grad_disjoint_same hc' hL (Or.inr hgap) e

/-- The base wave and each proxy profile have disjoint gradient supports: profile gradients vanish
on the charge support where the base wave can have a gradient. -/
theorem rootedMarkedP4Wave_grad_disjoint_base {L : ℕ} {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {p : RotatorDualFace L → ℤ} (hp : p ∈ F.image neutralizeAtWiredRoot)
    (hL : 1 < L) (σ : RotatorDualFace L → ℝ)
    (hsupp : ∀ x, σ (some x) ≠ 0 ↔ neutralizeAtWiredRoot (siteRestrict p) (some x) ≠ 0)
    (t : rootedMarkedP4Index p) (e : SquareZeroBond L) :
    (squareZero L).grad (rootedRealSquareBaseWave σ) e = 0 ∨
      (squareZero L).grad (rootedMarkedP4Wave F p t) e = 0 := by
  by_cases he : (squareZero L).grad (rootedRealSquareBaseWave σ) e = 0
  · exact Or.inl he
  · right
    simpa [rootedMarkedP4Wave, profileFamilyPiece] using
      ProfileContext.grad_profilePiece_zero_of_rootedBase_grad_ne
        (rootedMarkedP4Context hFzero hFsep hp t) hL σ hsupp e he

/-- A proxy profile is orthogonal to every other member of its pinned extension. -/
theorem rootedMarkedP4Wave_orthogonal_other {L : ℕ} {F : Finset (ChargeDensity L)}
    (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {p : RotatorDualFace L → ℤ} (hp : p ∈ F.image neutralizeAtWiredRoot)
    {ρ : ChargeDensity L} (hρ : ρ ∈ F)
    (hρne : ρ ≠ siteRestrict p) (t : rootedMarkedP4Index p) :
    Multigraph.pairing (rootedMarkedP4Wave F p t)
      (fun j => (neutralizeAtWiredRoot ρ j : ℝ)) = 0 := by
  simpa [Multigraph.pairing, rootedMarkedP4Wave, profileFamilyPiece] using
    (rootedMarkedP4Context hFzero hFsep hp t).sum_profilePiece_mul_neutralize_eq_zero
      hρ hρne

/-- The proxy extension produces its concrete finite P4.7 family, with fractional cut gaps,
rooted gradient separation, and orthogonality to every branch remainder charge. -/
theorem rootedMarkedComposite_profileGeometry {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n)
    {M α ξ : ℝ} (hM : 0 < M) (hα : 0 ≤ α)
    (hMscale : M = (chargeCoverScale : ℝ)) (hαscale : α = chargeCoverExponent)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (F : Finset (ChargeDensity (sideLength R)))
    (hgeo : AppendixDChargeGeometry M α F)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ))
    (hC : C ∈ clusters (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot))
    (T : Finset (RotatorDualFace (sideLength R) → ℤ)) (hT : T ⊆ C)
    (hL : 1 < sideLength R) :
    let N := F.image neutralizeAtWiredRoot
    let Rm := Generic.Marked.remainder (RootedMarkAdjacent M α R n hn) N C
    let p := rootedMarkedProxy R n hn C T
    let σ := rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
    let Fext := (rootedMarkedExtension M α R n hn N C T).image siteRestrict
    let ι := rootedMarkedP4Index p
    let ψ : ι → RotatorDualFace (sideLength R) → ℝ := rootedMarkedP4Wave Fext p
    let S : ι → Finset (Site R) := fun t => t.val.2
    (∀ t, ψ t none = 0 ∧
      (squareZero (sideLength R)).energy (ψ t) ≤ 6400) ∧
    (∀ t, Multigraph.pairing (ψ t) σ = ∑ x ∈ S t, σ (some x)) ∧
    (∀ t, Generic.Marked.dipoleGap ξ ≤ |Multigraph.pairing (ψ t) σ|) ∧
    (∀ t t', t ≠ t' → ∀ e,
      (squareZero (sideLength R)).grad (ψ t) e = 0 ∨
        (squareZero (sideLength R)).grad (ψ t') e = 0) ∧
    (∀ t e,
      (squareZero (sideLength R)).grad (rootedRealSquareBaseWave σ) e = 0 ∨
        (squareZero (sideLength R)).grad (ψ t) e = 0) ∧
    (∀ ϱ ∈ Rm,
      Multigraph.pairing (rootedRealSquareBaseWave σ) (fun j => (ϱ j : ℝ)) = 0) ∧
    (∀ t, ∀ ϱ ∈ Rm,
      Multigraph.pairing (ψ t) (fun j => (ϱ j : ℝ)) = 0) := by
  classical
  let N := F.image neutralizeAtWiredRoot
  let Rm := Generic.Marked.remainder (RootedMarkAdjacent M α R n hn) N C
  let p := rootedMarkedProxy R n hn C T
  let σ := rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
  let ext := rootedMarkedExtension M α R n hn N C T
  let Fext := ext.image siteRestrict
  let ι := rootedMarkedP4Index p
  let ψ : ι → RotatorDualFace (sideLength R) → ℝ := rootedMarkedP4Wave Fext p
  let S : ι → Finset (Site R) := fun t => t.val.2
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hEG := rootedMarkedExtensionGeometry_holds hM hα hn hn0 F hgeo.ensemble
    hgeo.separated C T hCN hT
  have hFextPin : IsPinnedChargeEnsemble Fext := hEG.1
  have hFextSep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent Fext := by
    simpa [Fext, ext, hMscale, hαscale] using hEG.2.1
  have hNeutralExt : Fext.image neutralizeAtWiredRoot = ext := hEG.2.2.1
  have hpNotRem : p ∉ Rm := hEG.2.2.2.1
  have hRemDisj : ∀ ϱ ∈ Rm,
      Disjoint (chargeSupport (siteRestrict ϱ)) (rootedMarkedSupport R n hn C) := hEG.2.2.2.2
  have hmembersDisj := disjoint_siteRestrict_of_subset_image hgeo.ensemble hCN
  have hpSupport : chargeSupport (siteRestrict p) = rootedMarkedSupport R n hn C :=
    chargeSupport_siteRestrict_rootedMarkedProxy hn hT hmembersDisj
  have hCneutral : ∀ m ∈ C, ∑ j, m j = 0 := fun m hm => sum_eq_zero_of_mem_image (hCN hm)
  have hpNeutral : neutralizeAtWiredRoot (siteRestrict p) = p :=
    neutralizeAtWiredRoot_siteRestrict_rootedMarkedProxy hn hn0 C T hCneutral hT
  have hσSupport : ∀ x : Site R,
      σ (some x) ≠ 0 ↔ neutralizeAtWiredRoot (siteRestrict p) (some x) ≠ 0 := by
    intro x
    simpa [neutralizeAtWiredRoot, siteRestrict] using
      rootedMarkedComposite_ne_zero_iff_proxy hn hξ0 hξ1 C T (some x)
  have hpInExt : p ∈ ext := by
    dsimp [ext, rootedMarkedExtension, Rm, N]
    exact Finset.mem_insert_self _ _
  have hpImage : p ∈ Fext.image neutralizeAtWiredRoot := by
    rw [hNeutralExt]
    exact hpInExt
  have hpDensity : siteRestrict p ∈ Fext := Finset.mem_image.mpr ⟨p, hpInExt, rfl⟩
  have hFzero : ∀ ρ ∈ Fext, ρ ≠ 0 := hFextPin.1
  have hrootEnergy : ∀ t : ι,
      ψ t none = 0 ∧ (squareZero (sideLength R)).energy (ψ t) ≤ 6400 := by
    intro t
    exact rootedMarkedP4Wave_root_energy hFzero hFextSep hpImage hL t
  have hpairPatch : ∀ t : ι, Multigraph.pairing (ψ t) σ =
      ∑ x ∈ S t, σ (some x) := by
    intro t
    exact rootedMarkedP4Wave_pairing_patch hFzero hFextSep hpImage t σ hσSupport
  have hproxyPatch : ∀ t : ι, ∑ x ∈ S t, siteRestrict p x ≠ 0 := by
    intro t
    obtain ⟨_, hs⟩ := Finset.mem_sigma.mp t.property
    unfold goodSquares at hs
    have hcharge := (Finset.mem_filter.mp hs).2
    rw [← totalCharge_chargeRestriction (siteRestrict p) (S t)]
    exact hcharge
  have hgap : ∀ t : ι, Generic.Marked.dipoleGap ξ ≤
      |Multigraph.pairing (ψ t) σ| := by
    intro t
    exact rootedMarkedComposite_profilePatch_gap hn hn0 ξ C T (ψ t) (S t)
      (hpairPatch t) (hproxyPatch t)
  have hdisj : ∀ t t' : ι, t ≠ t' → ∀ e,
      (squareZero (sideLength R)).grad (ψ t) e = 0 ∨
        (squareZero (sideLength R)).grad (ψ t') e = 0 := by
    intro t t' hne e
    exact rootedMarkedP4Wave_grad_disjoint hFzero hFextSep hpImage hL hne e
  have hbaseDisj : ∀ t : ι, ∀ e,
      (squareZero (sideLength R)).grad (rootedRealSquareBaseWave σ) e = 0 ∨
        (squareZero (sideLength R)).grad (ψ t) e = 0 := by
    intro t e
    exact rootedMarkedP4Wave_grad_disjoint_base hFzero hFextSep hpImage hL σ
      hσSupport t e
  have hbaseOrth : ∀ ϱ ∈ Rm,
      Multigraph.pairing (rootedRealSquareBaseWave σ) (fun j => (ϱ j : ℝ)) = 0 := by
    intro ϱ hϱ
    have hfacezero : ∀ x : Site R,
        rootedRealSquareBaseWave σ (some x) ≠ 0 → ϱ (some x) = 0 := by
      intro x hbase
      have hσx : σ (some x) ≠ 0 := by
        intro hz
        exact hbase (by simp [rootedRealSquareBaseWave, hz])
      have hpface : p (some x) ≠ 0 := by
        have hx := (hσSupport x).mp hσx
        simpa [neutralizeAtWiredRoot, siteRestrict] using hx
      have hxP : x ∈ chargeSupport (siteRestrict p) := by
        exact mem_chargeSupport'.2 (by simpa [siteRestrict] using hpface)
      have hxX : x ∈ rootedMarkedSupport R n hn C := by
        rw [← hpSupport]
        exact hxP
      have hxR : x ∉ chargeSupport (siteRestrict ϱ) :=
        (Finset.disjoint_left.mp ((hRemDisj ϱ hϱ).symm)) hxX
      have hxzero : siteRestrict ϱ x = 0 := by
        by_contra hnzero
        exact hxR (mem_chargeSupport'.2 hnzero)
      simpa [siteRestrict] using hxzero
    unfold Multigraph.pairing
    rw [Fintype.sum_option]
    change rootedRealSquareBaseWave σ none * (ϱ none : ℝ) +
      ∑ x, rootedRealSquareBaseWave σ (some x) * (ϱ (some x) : ℝ) = 0
    rw [rootedRealSquareBaseWave, zero_mul, zero_add]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hbase : rootedRealSquareBaseWave σ (some x) = 0
    · simp [hbase]
    · simp [hfacezero x hbase]
  have hprofileOrth : ∀ t : ι, ∀ ϱ ∈ Rm,
      Multigraph.pairing (ψ t) (fun j => (ϱ j : ℝ)) = 0 := by
    intro t ϱ hϱ
    have hϱN : ϱ ∈ N := Generic.Marked.remainder_subset _ _ hϱ
    obtain ⟨hρF, hneutralϱ⟩ := siteRestrict_mem_of_mem_image hϱN
    have hρExt : siteRestrict ϱ ∈ Fext :=
      Finset.mem_image.mpr ⟨ϱ, Finset.mem_insert_of_mem hϱ, rfl⟩
    have hρne : siteRestrict ϱ ≠ siteRestrict p := by
      intro heq
      have heq' : neutralizeAtWiredRoot (siteRestrict ϱ) =
          neutralizeAtWiredRoot (siteRestrict p) := congrArg neutralizeAtWiredRoot heq
      rw [hneutralϱ, hpNeutral] at heq'
      exact hpNotRem (heq' ▸ hϱ)
    have horth := rootedMarkedP4Wave_orthogonal_other hFzero hFextSep hpImage
      hρExt hρne t
    rw [hneutralϱ] at horth
    exact horth
  refine ⟨hrootEnergy, hpairPatch, hgap, hdisj, hbaseDisj, hbaseOrth, hprofileOrth⟩

/-- Assemble a composite wave once the marked proxy has supplied its P4.7 profile family. The
profiles are orthogonal to every remainder charge, and their fractional cut gaps pay the required
gain through the energy estimate above. -/
theorem rootedCompositeWave_ofProfileFamily {τ gain qStar : ℝ} (hτ : 0 < τ)
    (σ : RotatorDualFace L → ℝ)
    (R : Finset (RotatorDualFace L → ℤ))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → RotatorDualFace L → ℝ) (q : ι → ℝ)
    (hroot : ∀ t, ψ t none = 0)
    (hpair : ∀ t, Multigraph.pairing (ψ t) σ = q t)
    (hqStar : 0 ≤ qStar) (hgap : ∀ t, qStar ≤ |q t|)
    (henergy : ∀ t, (squareZero L).energy (ψ t) ≤ 6400)
    (hdisj : ∀ t t', t ≠ t' → ∀ e,
      (squareZero L).grad (ψ t) e = 0 ∨ (squareZero L).grad (ψ t') e = 0)
    (hbaseDisj : ∀ t e,
      (squareZero L).grad (rootedRealSquareBaseWave σ) e = 0 ∨
        (squareZero L).grad (ψ t) e = 0)
    (hbaseOrth : ∀ ϱ ∈ R,
      Multigraph.pairing (rootedRealSquareBaseWave σ) (fun j => (ϱ j : ℝ)) = 0)
    (hprofileOrth : ∀ t, ∀ ϱ ∈ R,
      Multigraph.pairing (ψ t) (fun j => (ϱ j : ℝ)) = 0)
    (hbudget : gain ≤ ((∑ i : SquareFreeVertex L, σ (some i) ^ 2) / 16 +
      qStar ^ 2 / 12800 * Fintype.card ι) / τ) :
    ∃ a₀ : RotatorDualFace L → ℝ,
      a₀ none = 0 ∧
      (∀ ϱ ∈ R, Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) ∧
      gain ≤ gffTranslationEnergy (squareZero L) τ a₀ σ := by
  let a₀ : RotatorDualFace L → ℝ := fun j =>
    1 / (4 * τ) * rootedRealSquareBaseWave σ j +
      ∑ t, q t / (τ * 6400) * ψ t j
  have henergyGain := rootedMarkedProfileEnergyLowerBound hτ σ ψ q hqStar
    hpair hgap henergy hdisj hbaseDisj
  have hpairAdd (ϱ : RotatorDualFace L → ℤ) :
      Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) =
        1 / (4 * τ) * Multigraph.pairing (rootedRealSquareBaseWave σ)
          (fun j => (ϱ j : ℝ)) +
          ∑ t, q t / (τ * 6400) * Multigraph.pairing (ψ t) (fun j => (ϱ j : ℝ)) := by
    classical
    unfold Multigraph.pairing a₀
    calc
      ∑ j, (1 / (4 * τ) * rootedRealSquareBaseWave σ j +
      ∑ t, q t / (τ * 6400) * ψ t j) * (ϱ j : ℝ) =
        (∑ j, (1 / (4 * τ) * rootedRealSquareBaseWave σ j) * (ϱ j : ℝ)) +
          ∑ j, (∑ t, q t / (τ * 6400) * ψ t j) * (ϱ j : ℝ) := by
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
      _ = (1 / (4 * τ) *
          Multigraph.pairing (rootedRealSquareBaseWave σ) (fun j => (ϱ j : ℝ))) +
          ∑ t, Multigraph.pairing (fun j => q t / (τ * 6400) * ψ t j)
            (fun j => (ϱ j : ℝ)) := by
            congr 1
            · exact pairing_const_mul_real _ _ _
            · exact pairing_fintype_sum_left
                (fun t j => q t / (τ * 6400) * ψ t j) (fun j => (ϱ j : ℝ))
      _ = (1 / (4 * τ) *
          Multigraph.pairing (rootedRealSquareBaseWave σ) (fun j => (ϱ j : ℝ))) +
          ∑ t, q t / (τ * 6400) *
            Multigraph.pairing (ψ t) (fun j => (ϱ j : ℝ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro t ht
            exact pairing_const_mul_real _ _ _
  refine ⟨a₀, ?_, ?_, ?_⟩
  · simp [a₀, rootedRealSquareBaseWave, hroot]
  · intro ϱ hϱ
    rw [hpairAdd ϱ, hbaseOrth ϱ hϱ]
    simp only [mul_zero]
    rw [zero_add]
    apply Finset.sum_eq_zero
    intro t ht
    rw [hprofileOrth t ϱ hϱ]
    simp
  · exact hbudget.trans (by simpa [a₀] using henergyGain)

/-- The concrete proxy profile family proves the composite-wave conclusion as soon as its
cardinality and base-mass terms dominate the specified cluster cost. -/
theorem rootedMarkedCompositeWave_of_profileBudget {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n)
    {M α ξ τ γ ℓ : ℝ} (hM : 0 < M) (hα : 0 ≤ α)
    (hMscale : M = (chargeCoverScale : ℝ)) (hαscale : α = chargeCoverExponent)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hτ : 0 < τ)
    (F : Finset (ChargeDensity (sideLength R)))
    (hgeo : AppendixDChargeGeometry M α F)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ))
    (hC : C ∈ clusters (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot))
    (T : Finset (RotatorDualFace (sideLength R) → ℤ)) (hT : T ⊆ C)
    (hL : 1 < sideLength R)
    (hbudget : γ * (∑ m ∈ C, layerA m + ℓ) ≤
      ((∑ x : SquareFreeVertex (sideLength R),
        (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x)) ^ 2) / 16 +
        Generic.Marked.dipoleGap ξ ^ 2 / 12800 *
          Fintype.card (rootedMarkedP4Index (rootedMarkedProxy R n hn C T))) / τ) :
    ∃ a₀ : RotatorDualFace (sideLength R) → ℝ,
      a₀ none = 0 ∧
      (∀ ϱ ∈ Generic.Marked.remainder
        (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot) C,
        Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) ∧
      γ * (∑ m ∈ C, layerA m + ℓ) ≤
        gffTranslationEnergy (squareZero (sideLength R)) τ a₀
          (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) := by
  classical
  let N := F.image neutralizeAtWiredRoot
  let Rm := Generic.Marked.remainder (RootedMarkAdjacent M α R n hn) N C
  let p := rootedMarkedProxy R n hn C T
  let σ := rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
  let Fext := (rootedMarkedExtension M α R n hn N C T).image siteRestrict
  let ι := rootedMarkedP4Index p
  let ψ : ι → RotatorDualFace (sideLength R) → ℝ := rootedMarkedP4Wave Fext p
  let q : ι → ℝ := fun t => Multigraph.pairing (ψ t) σ
  have hgeom := rootedMarkedComposite_profileGeometry hn hn0 hM hα hMscale hαscale
    hξ0 hξ1 F hgeo C hC T hT hL
  obtain ⟨hroot, hpatch, hgap, hdisj, hbaseDisj, hbaseOrth, hprofileOrth⟩ := hgeom
  have hpair : ∀ t, Multigraph.pairing (ψ t) σ = q t := fun _ => rfl
  have hqstar : 0 ≤ Generic.Marked.dipoleGap ξ :=
    le_of_lt (Generic.Marked.dipoleGap_pos hξ0 hξ1)
  have hprofilegap : ∀ t, Generic.Marked.dipoleGap ξ ≤ |q t| := by
    intro t
    simpa [q] using hgap t
  have hbudget' : γ * (∑ m ∈ C, layerA m + ℓ) ≤
      ((∑ x : SquareFreeVertex (sideLength R), σ (some x) ^ 2) / 16 +
        Generic.Marked.dipoleGap ξ ^ 2 / 12800 * Fintype.card ι) / τ := by
    simpa [σ, ι, p] using hbudget
  simpa [σ, Rm, ψ, q] using
    rootedCompositeWave_ofProfileFamily (L := sideLength R) hτ σ Rm ψ q
      (fun t => (hroot t).1) hpair hqstar hprofilegap (fun t => (hroot t).2)
      hdisj hbaseDisj hbaseOrth hprofileOrth hbudget'

/--
The remaining hypotheses are the P4.7 profile, separation,
orthogonality and cardinal-budget clauses supplied by the profile construction.
-/
theorem rootedMarkedCompositeWave_ofProfileFamily {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n)
    {ξ τ γ ℓ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hτ : 0 < τ)
    (M α : ℝ) (N C T : Finset (RotatorDualFace (sideLength R) → ℤ))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → RotatorDualFace (sideLength R) → ℝ) (S : ι → Finset (Site R))
    (hroot : ∀ t, ψ t none = 0)
    (hpairPatch : ∀ t, Multigraph.pairing (ψ t)
      (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) =
        ∑ x ∈ S t,
          rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x))
    (hproxy : ∀ t, ∑ x ∈ S t,
      siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0)
    (henergy : ∀ t, (squareZero (sideLength R)).energy (ψ t) ≤ 6400)
    (hdisj : ∀ t t', t ≠ t' → ∀ e,
      (squareZero (sideLength R)).grad (ψ t) e = 0 ∨
        (squareZero (sideLength R)).grad (ψ t') e = 0)
    (hbaseDisj : ∀ t e,
      (squareZero (sideLength R)).grad
          (rootedRealSquareBaseWave
            (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T)) e = 0 ∨
        (squareZero (sideLength R)).grad (ψ t) e = 0)
    (hbaseOrth : ∀ ϱ ∈ Generic.Marked.remainder
      (RootedMarkAdjacent M α R n hn) N C,
      Multigraph.pairing
        (rootedRealSquareBaseWave (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T))
        (fun j => (ϱ j : ℝ)) = 0)
    (hprofileOrth : ∀ t, ∀ ϱ ∈ Generic.Marked.remainder
      (RootedMarkAdjacent M α R n hn) N C,
      Multigraph.pairing (ψ t) (fun j => (ϱ j : ℝ)) = 0)
    (hbudget : γ * (∑ m ∈ C, layerA m + ℓ) ≤
      ((∑ x : SquareFreeVertex (sideLength R),
        (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x)) ^ 2) / 16 +
        Generic.Marked.dipoleGap ξ ^ 2 / 12800 * Fintype.card ι) / τ) :
    ∃ a₀ : RotatorDualFace (sideLength R) → ℝ,
      a₀ none = 0 ∧
      (∀ ϱ ∈ Generic.Marked.remainder (RootedMarkAdjacent M α R n hn) N C,
        Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) ∧
      γ * (∑ m ∈ C, layerA m + ℓ) ≤
        gffTranslationEnergy (squareZero (sideLength R)) τ a₀
          (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) := by
  let σ := rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
  let q : ι → ℝ := fun t => Multigraph.pairing (ψ t) σ
  let R₀ := Generic.Marked.remainder (RootedMarkAdjacent M α R n hn) N C
  have hpair : ∀ t, Multigraph.pairing (ψ t) σ = q t := fun _ => rfl
  have hgapData := rootedMarkedComposite_profileFamily_gap hn hn0 hξ0 hξ1 C T ψ S
    hpairPatch hproxy
  have hbudget' : γ * (∑ m ∈ C, layerA m + ℓ) ≤
      ((∑ x : SquareFreeVertex (sideLength R), σ (some x) ^ 2) / 16 +
        Generic.Marked.dipoleGap ξ ^ 2 / 12800 * Fintype.card ι) / τ := by
    simpa [σ] using hbudget
  simpa only [σ, q] using rootedCompositeWave_ofProfileFamily
    (L := sideLength R) hτ σ R₀ ψ q hroot hpair hgapData.1 hgapData.2 henergy hdisj
    hbaseDisj hbaseOrth hprofileOrth hbudget'

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
