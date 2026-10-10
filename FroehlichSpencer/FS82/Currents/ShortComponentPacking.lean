/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.ShortComponentPhase
public import FroehlichSpencer.FS82.Currents.SourcePacking
public import FroehlichSpencer.FS82.Moment.PositivePacking

/-!
# FS82 ShortComponentPhase: Jensen transfer of a short parent and side-six packing of the components

* `shortParent_jensen_error_le`: for a short co-closed parent current with an amplitude below
  the exponential envelope, the Jensen error `γ(z) θ²` is at most the sum over its incidence
  components of SourcePacking's activity `sourceComponentActivityL5` times the squared maximum of the
  local curvature on the component's source cube (/PlaquetteCarrierPacking transfer with ShortPhase's phase bound on
  every component).
* `sum_componentMajorants_le`: over a family of parents with pairwise disjoint supports, these
  component majorants sum to at most `81 · sourceComponentCpackPrime` times the total squared
  local curvature (FS82 (2.105)–(2.106): each component is assigned a maximizing plaquette of
  its source cube, and disjoint components of size `L` assigned to one plaquette lie in a link
  box of side `6 L`).
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Currents.ShortComponentPhase

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.SourcePacking
open FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Moment.SourceJensen

noncomputable section

variable {B : Box 4}

/-- The local curvature of the zero-extended one-form, as a field on the plaquettes of the
bumped box. -/
def localCurvature (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (p : SourcePlaquette B) : ℝ :=
  chainCoboundary (sourcePrimalOneForm τ) p.1

/-- The maximum of the local curvature on the source cube of a component. -/
def componentCurvatureMax (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (lo : Fin 4 → ℕ) (L : ℕ) : ℝ :=
  sourceOmegaMax lo (2 * L) (localCurvature τ)

theorem sourceComponentActivityL5_nonneg (a C : ℝ) (L : ℕ) :
    0 ≤ sourceComponentActivityL5 a C L := by
  unfold sourceComponentActivityL5
  positivity

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  rw [Real.exp_neg, ← one_div]
  have h : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  exact one_div_le_one_div_of_le (by norm_num) h

theorem sourceCurrentPhase_zero (tau : Link B → ℝ) :
    sourceCurrentPhase tau (0 : IntegerCurrent B) = 0 := by
  simp [sourceCurrentPhase]

/-- **Jensen transfer for a short parent.** -/
theorem shortParent_jensen_error_le (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    (m : ℕ) (hmin : ∀ i, m ≤ B i) (hshort : j.support.card < m)
    (a z : ℝ) (ha : 1 ≤ a) (hz0 : 0 ≤ z)
    (hz : z ≤ Real.exp (-(a * (currentEnergy j + currentLength j))))
    (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (lo : CurrentComponentClass j → Fin 4 → ℕ)
    (hlo : ∀ c ∈ currentComponents j, ∀ i, lo c i ≤ B i + 1)
    (hcube : ∀ c ∈ currentComponents j,
      supportInSourceCube (currentComponentSupport j c) (lo c)
        (2 * (currentComponentSupport j c).card)) :
    sourceJensenGamma z * (sourceCurrentPhase (twistedLinkField τ) j) ^ 2 ≤
      ∑ c ∈ currentComponents j,
        sourceComponentActivityL5 a (50 * Real.pi * 10000)
            (currentComponentSupport j c).card *
          componentCurvatureMax τ (lo c) (currentComponentSupport j c).card ^ 2 := by
  by_cases hj : j = 0
  · subst hj
    rw [sourceCurrentPhase_zero]
    have hsum : 0 ≤ ∑ c ∈ currentComponents (0 : IntegerCurrent B),
        sourceComponentActivityL5 a (50 * Real.pi * 10000)
            (currentComponentSupport (0 : IntegerCurrent B) c).card *
          componentCurvatureMax τ (lo c)
            (currentComponentSupport (0 : IntegerCurrent B) c).card ^ 2 :=
      Finset.sum_nonneg fun c _ =>
        mul_nonneg (sourceComponentActivityL5_nonneg _ _ _) (sq_nonneg _)
    simpa using hsum
  · have hLpos : (1 : ℝ) ≤ currentLength j := by
      unfold currentLength
      have hne : j.support.Nonempty := Finsupp.support_nonempty_iff.mpr hj
      exact_mod_cast Finset.card_pos.mpr hne
    have hE := currentEnergy_nonneg j
    have hzHalf : z ≤ 1 / 2 := by
      refine hz.trans (le_trans ?_ exp_neg_one_le_half)
      apply Real.exp_le_exp.mpr
      nlinarith
    have hC : (0 : ℝ) ≤ 50 * Real.pi * 10000 := by
      have := Real.pi_pos
      positivity
    refine sourceCurrent_jensen_error_le_componentActivityL5_ofSourcePhase j
      (twistedLinkField τ) a (50 * Real.pi * 10000) z hz0 hzHalf ha hC
      (fun c => componentCurvatureMax τ (lo c) (currentComponentSupport j c).card)
      (fun c _ => sourceOmegaMax_nonneg _ _ _) hz ?_
    intro c hc
    have hcard : (currentComponentSupport j c).card < m :=
      lt_of_le_of_lt (Finset.card_le_card (currentComponentSupport_subset j c)) hshort
    exact component_sourcePhase_le j hdiv hc m hmin hcard (lo c) (hlo c hc) (hcube c hc) τ

/-! ### Side-six packing of the component majorants -/

theorem sourceOmegaMax_eq_zero_of_empty (lo : Fin 4 → ℕ) (D : ℕ)
    (field : SourcePlaquette B → ℝ) (h : ¬(sourceOmega (B := B) lo D).Nonempty) :
    sourceOmegaMax lo D field = 0 := by
  rw [Finset.not_nonempty_iff_eq_empty] at h
  unfold sourceOmegaMax
  rw [h]
  simp

/-- A component in the source cube `[lo, lo + 2L]` lies in the link box of half-side `3L`
centred at any plaquette of that cube. -/
theorem component_subset_centeredLinkBox {S : Finset (Link B)} {lo : Fin 4 → ℕ} {L : ℕ}
    (hL : 1 ≤ L) (hcube : supportInSourceCube S lo (2 * L))
    {p : SourcePlaquette B} (hp : p ∈ sourceOmega (B := B) lo (2 * L)) :
    S ⊆ sourceCenteredLinkBox (sourcePlaquetteCoord p) (3 * L) := by
  intro e he
  apply mem_sourceCenteredLinkBox_of_bounds
  intro k
  have hc := hcube k e he
  have hpk := (Finset.mem_filter.mp hp).2 k
  have hlu := cellCoordLower_le_upper p.1 k
  have hite : 0 ≤ (if axis e = k then 1 else 0 : ℕ) := Nat.zero_le _
  unfold sourcePlaquetteCoord
  push_cast
  constructor <;> omega

/-- **Packing of the component majorants** (FS82 (2.105)–(2.106), side-six form). -/
theorem sum_componentMajorants_le (S : Finset (IntegerCurrent B))
    (hdisj : (↑S : Set (IntegerCurrent B)).PairwiseDisjoint fun j => j.support)
    (a : ℝ) (ha : 0 < a) (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (lo : (j : IntegerCurrent B) → CurrentComponentClass j → Fin 4 → ℕ)
    (hcube : ∀ j ∈ S, ∀ c ∈ currentComponents j,
      supportInSourceCube (currentComponentSupport j c) (lo j c)
        (2 * (currentComponentSupport j c).card)) :
    (∑ j ∈ S, ∑ c ∈ currentComponents j,
        sourceComponentActivityL5 a (50 * Real.pi * 10000)
            (currentComponentSupport j c).card *
          componentCurvatureMax τ (lo j c) (currentComponentSupport j c).card ^ 2) ≤
      81 * sourceComponentCpackPrime a (50 * Real.pi * 10000) *
        ∑ p : SourcePlaquette B, (localCurvature τ p) ^ 2 := by
  classical
  let I := Σ j : IntegerCurrent B, CurrentComponentClass j
  let X : Finset I := S.sigma fun j => currentComponents j
  let len : I → ℕ := fun x => (currentComponentSupport x.1 x.2).card
  let good : I → Prop := fun x => (sourceOmega (B := B) (lo x.1 x.2) (2 * len x)).Nonempty
  let err : I → ℝ := fun x =>
    sourceComponentActivityL5 a (50 * Real.pi * 10000) (len x) *
      componentCurvatureMax τ (lo x.1 x.2) (len x) ^ 2
  let T : Finset I := X.filter good
  have hsigma : (∑ j ∈ S, ∑ c ∈ currentComponents j,
        sourceComponentActivityL5 a (50 * Real.pi * 10000)
            (currentComponentSupport j c).card *
          componentCurvatureMax τ (lo j c) (currentComponentSupport j c).card ^ 2) =
      ∑ x ∈ X, err x := (Finset.sum_sigma S (fun j => currentComponents j) err).symm
  have hbad : ∀ x ∈ X, ¬good x → err x = 0 := by
    intro x _ hx
    have h0 : componentCurvatureMax τ (lo x.1 x.2) (len x) = 0 :=
      sourceOmegaMax_eq_zero_of_empty _ _ _ hx
    simp [err, h0]
  have hfilter : ∑ x ∈ X, err x = ∑ x ∈ T, err x := by
    refine (Finset.sum_subset (Finset.filter_subset good X) fun x hx hxT => ?_).symm
    exact hbad x hx fun hg => hxT (Finset.mem_filter.mpr ⟨hx, hg⟩)
  rw [hsigma, hfilter]
  have hRHS : 0 ≤ 81 * sourceComponentCpackPrime a (50 * Real.pi * 10000) *
      ∑ p : SourcePlaquette B, (localCurvature τ p) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (sourceComponentCpackPrime_nonneg a _ ha))
      (Finset.sum_nonneg fun p _ => sq_nonneg _)
  rcases T.eq_empty_or_nonempty with hT | ⟨x₀, hx₀⟩
  · rw [hT, Finset.sum_empty]
    exact hRHS
  have hgood₀ : good x₀ := (Finset.mem_filter.mp hx₀).2
  let p₀ : SourcePlaquette B := hgood₀.choose
  let plaq : I → SourcePlaquette B := fun x =>
    if h : good x then
      sourceMaximizingPlaquette (lo x.1 x.2) (2 * len x) (localCurvature τ) h
    else p₀
  have hmemX : ∀ x ∈ T, x.1 ∈ S ∧ x.2 ∈ currentComponents x.1 := by
    intro x hx
    exact Finset.mem_sigma.mp (Finset.mem_filter.mp hx).1
  have hlenpos : ∀ x ∈ T, 1 ≤ len x := by
    intro x hx
    exact Finset.card_pos.mpr (currentComponentSupport_nonempty x.1 (hmemX x hx).2)
  refine finite_current_packing_l2_side_six_positive T (T.image len)
    (fun x => currentComponentSupport x.1 x.2)
    (fun p L => sourceCenteredLinkBox (sourcePlaquetteCoord p) (3 * L))
    plaq len err (localCurvature τ)
    (sourceComponentActivityL5 a (50 * Real.pi * 10000))
    (81 * sourceComponentCpackPrime a (50 * Real.pi * 10000))
    (fun x hx => Finset.mem_image_of_mem len hx) ?_ ?_ (fun x _ => rfl) ?_ ?_ ?_
    (fun L _ => sourceComponentActivityL5_nonneg _ _ L)
    (sourceComponentActivityL5_budget_side_six a _ ha _)
  · intro L hL
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hL
    exact hlenpos x hx
  · rintro ⟨j, c⟩ hx ⟨j', c'⟩ hy hne
    have hx' := hmemX _ (Finset.mem_coe.mp hx)
    have hy' := hmemX _ (Finset.mem_coe.mp hy)
    by_cases hjj : j = j'
    · subst hjj
      have hcc : c ≠ c' := fun h => hne (by rw [h])
      exact currentComponentSupport_pairwiseDisjoint j hx'.2 hy'.2 hcc
    · exact Finset.disjoint_of_subset_left (currentComponentSupport_subset j c)
        (Finset.disjoint_of_subset_right (currentComponentSupport_subset j' c')
          (hdisj hx'.1 hy'.1 hjj))
  · intro x hx
    have hg : good x := (Finset.mem_filter.mp hx).2
    have hpl : plaq x =
        sourceMaximizingPlaquette (lo x.1 x.2) (2 * len x) (localCurvature τ) hg :=
      dite_eq_left hg
    rw [hpl]
    exact component_subset_centeredLinkBox (hlenpos x hx)
      (hcube x.1 (hmemX x hx).1 x.2 (hmemX x hx).2)
      (sourceMaximizingPlaquette_mem _ _ _ hg)
  · intro p L
    have h := sourceCenteredLinkBox_card_le (B := B) (sourcePlaquetteCoord p) (3 * L)
    have e : 2 * (3 * L) = 6 * L := by ring
    rwa [e] at h
  · intro x hx
    have hg : good x := (Finset.mem_filter.mp hx).2
    have hpl : plaq x =
        sourceMaximizingPlaquette (lo x.1 x.2) (2 * len x) (localCurvature τ) hg :=
      dite_eq_left hg
    have hmax : componentCurvatureMax τ (lo x.1 x.2) (len x) =
        |localCurvature τ (plaq x)| := by
      rw [hpl]
      exact sourceOmegaMax_eq_maximizingPlaquette _ _ _ hg
    simp only [err]
    rw [hmax, sq_abs]

end

end FroehlichSpencer.FS82.Currents.ShortComponentPhase
