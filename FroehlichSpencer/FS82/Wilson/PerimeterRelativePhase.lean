/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.JensenControlledFilling

/-!
# phase representatives from relative fillings

A finite co-closed current need not be a cycle of the full lattice: its lattice boundary may sit
on exterior vertices.

So `controlledComponent_phase_representative`, which asks for a full cycle,
does not apply to it.

The corrected statement is relative.

A short connected co-closed current `q`
is closed by a chain on the exterior shell and filled there (`short_current_phase_bound`); the
zero-extended one-form vanishes on the shell, so Stokes still gives the phase as the pairing of
its curvature with the filling.

If the curvature is an integer sheet minus a field on every
plaquette (FS82 (2.51)), the phase is, modulo `2π`, minus the pairing of the field with the
filling (FS82 (2.56)–(2.57)).

* `short_current_relative_phase`: the representative and its bound for a short connected current.
* `component_relative_phase`: the same for a short incidence component of a co-closed current.
* `exists_phase_representative_abs_le_pi`: any phase has a representative in `[−π, π]`; this is
  used for the long components.
* `exists_relativeParent_phase`: the representative of a co-closed parent, with its Jensen error
  bounded by component majorants.
* `relative_filling_wilson_bound`: the sum over a family with pairwise disjoint supports.

The short
  components are packed against the `ℓ²` norm of the field, and the long components contribute a
  term that is exponentially small in the box size.
-/

open scoped BigOperators
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Currents.PackingFamily
open FroehlichSpencer.FS82.Currents.SourcePacking
open FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.Packing

@[expose] public section

namespace FroehlichSpencer.FS82.Wilson

noncomputable section

variable {B : Box 4}

/-- The constant of the relative filling estimate, `50π·10⁴` (ShortPhase). -/
def relativeFillingConstant : ℝ := 50 * Real.pi * 10000

theorem relativeFillingConstant_pos : 0 < relativeFillingConstant := by
  unfold relativeFillingConstant
  have := Real.pi_pos
  positivity

/-- **The relative phase representative of a short connected co-closed current.** If on every
plaquette the field plus the curvature of the zero-extended one-form is an integer, then the
source phase plus `θ` is an integer multiple of `2π`, where `θ` is `2π` times the pairing of the
field with a relative filling, and `|θ| ≤ 50π·10⁴ · max|field| · L⁵ · ‖q‖₁`. -/
theorem short_current_relative_phase (q : IntegerCurrent B)
    (hco : currentDivergence q = 0) (hconn : SourceCurrentConnected q)
    (m : ℕ) (hmin : ∀ i, m ≤ B i)
    (hL : 1 ≤ q.support.card) (hshort : q.support.card < m)
    (lo : Fin 4 → ℕ) (hlo : ∀ i, lo i ≤ B i + 1)
    (hcube : supportInSourceCube q.support lo (2 * q.support.card))
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : ℝ,
      (∃ n : ℤ, sourceCurrentPhase (twistedLinkField tau) q + θ = 2 * Real.pi * (n : ℝ)) ∧
      |θ| ≤ relativeFillingConstant * sourceOmegaMax lo (2 * q.support.card) field *
        (q.support.card : ℝ) ^ 5 * (chainL1 (sourceCurrentLatticeChain q) : ℝ) := by
  classical
  obtain ⟨ε, μ, _hcycle, _hεshell, _hεhom, _hεmass, hξmass, _hεrect,
      _hfillBoundary, hfillOmega, hfillCoef, hrelative, _hrawBound⟩ :=
    short_current_phase_bound q hco hconn m hmin hL hshort lo hlo hcube
      (sourcePrimalOneForm tau) (sourcePrimalOneForm_shell tau)
  let α := sourcePrimalOneForm tau
  let sheetCell : Cell 4 (bumpedBox B) → ℤ := fun d =>
    if hd : cellDegree d = 2 then sheet ⟨d, hd⟩ else 0
  have hcell : ∀ d ∈ μ.support,
      controlledPlaquetteFieldCell field d + chainCoboundary α d = (sheetCell d : ℝ) := by
    intro d hd
    obtain ⟨p, _, rfl⟩ := hfillOmega d hd
    simp only [controlledPlaquetteFieldCell, sheetCell, dite_eq_left p.2]
    exact hdecomp p
  have hpair : chainPairing (fun d => (sheetCell d : ℝ)) μ =
      chainPairing (controlledPlaquetteFieldCell field) μ +
        chainPairing (chainCoboundary α) μ := by
    rw [chainPairing_eq_support_sum, chainPairing_eq_support_sum,
      chainPairing_eq_support_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hlocal := hcell d hd
    change (sheetCell d : ℝ) * (μ d : ℝ) =
      controlledPlaquetteFieldCell field d * (μ d : ℝ) + chainCoboundary α d * (μ d : ℝ)
    rw [← hlocal]
    ring
  obtain ⟨n, hn⟩ := chainPairing_integer_valued sheetCell μ
  refine ⟨(2 * Real.pi) * chainPairing (controlledPlaquetteFieldCell field) μ, ⟨n, ?_⟩, ?_⟩
  · rw [sourceCurrentPhase_twistedLinkField, ← hrelative, ← hn, hpair]
    ring
  · let L := q.support.card
    let K := chainL1 (sourceCurrentLatticeChain q + ε)
    let M := sourceOmegaMax lo (2 * L) field
    have hM : 0 ≤ M := sourceOmegaMax_nonneg lo (2 * L) field
    have hfield : ∀ d ∈ μ.support, |controlledPlaquetteFieldCell field d| ≤ M := by
      intro d hd
      obtain ⟨p, hp, hpd⟩ := hfillOmega d hd
      rw [← hpd]
      simp only [controlledPlaquetteFieldCell, dite_eq_left p.2]
      exact sourceOmegaMax_bound lo (2 * L) field hp
    have hpairBound := chainPairing_abs_le_card_mul_coefficientBound
      (controlledPlaquetteFieldCell field) μ M K hM hfield hfillCoef
    have hcardOmega := sourceChain_support_card_le_omega μ lo (2 * L) K hfillOmega hfillCoef
    have hOmega := sourceOmega_card_le_10000L4 (B := B) lo L hL
    have hcard : (μ.support.card : ℝ) ≤ 10000 * (L : ℝ) ^ 4 := by
      exact_mod_cast hcardOmega.1.trans hOmega
    have hK : (K : ℝ) ≤ 25 * (L : ℝ) * (chainL1 (sourceCurrentLatticeChain q) : ℝ) := by
      exact_mod_cast hξmass
    have hpi := Real.pi_pos
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
    have hstep : |chainPairing (controlledPlaquetteFieldCell field) μ| ≤
        (10000 * (L : ℝ) ^ 4) * M *
          (25 * (L : ℝ) * (chainL1 (sourceCurrentLatticeChain q) : ℝ)) := by
      calc |chainPairing (controlledPlaquetteFieldCell field) μ|
          ≤ (μ.support.card : ℝ) * M * K := hpairBound
        _ ≤ (10000 * (L : ℝ) ^ 4) * M *
            (25 * (L : ℝ) * (chainL1 (sourceCurrentLatticeChain q) : ℝ)) := by gcongr
    calc |(2 * Real.pi) * chainPairing (controlledPlaquetteFieldCell field) μ|
        = (2 * Real.pi) * |chainPairing (controlledPlaquetteFieldCell field) μ| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (2 * Real.pi) * ((10000 * (L : ℝ) ^ 4) * M *
          (25 * (L : ℝ) * (chainL1 (sourceCurrentLatticeChain q) : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = relativeFillingConstant * sourceOmegaMax lo (2 * q.support.card) field *
          (q.support.card : ℝ) ^ 5 * (chainL1 (sourceCurrentLatticeChain q) : ℝ) := by
          simp only [relativeFillingConstant, M, L]
          ring

/-- **The relative phase representative of a short incidence component** of a co-closed current,
in the shape `|θ| ≤ C · (L · max|field|) · E · L⁴` used by the component Jensen transfer. -/
theorem component_relative_phase (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    {c : CurrentComponentClass j} (hc : c ∈ currentComponents j)
    (m : ℕ) (hmin : ∀ i, m ≤ B i) (hshort : (currentComponentSupport j c).card < m)
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : ℝ,
      (∃ n : ℤ, sourceCurrentPhase (twistedLinkField tau) (currentComponentCurrent j c) + θ =
        2 * Real.pi * (n : ℝ)) ∧
      |θ| ≤ relativeFillingConstant *
        (((currentComponentSupport j c).card : ℝ) *
          sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) *
        currentEnergy (currentComponentCurrent j c) *
        ((currentComponentSupport j c).card : ℝ) ^ 4 := by
  have hqs := currentComponentCurrent_support j c
  have hco := currentComponentCurrent_divergence_eq_zero_of_divergence_eq_zero j c hdiv
  have hconn : SourceCurrentConnected (currentComponentCurrent j c) := by
    intro u hu v hv
    obtain ⟨n, hn, hpath⟩ := currentComponent_boundary_vertices_connected j c hu hv
    exact ⟨n, by rw [hqs]; exact hn, hpath⟩
  have hL : 1 ≤ (currentComponentCurrent j c).support.card := by
    rw [hqs]
    exact Finset.card_pos.mpr (currentComponentSupport_nonempty j hc)
  have hcube : supportInSourceCube (currentComponentCurrent j c).support
      (componentCubeLower j c) (2 * (currentComponentCurrent j c).support.card) := by
    rw [hqs]
    simpa [componentCubeSide] using componentSupport_in_componentCube j c
  obtain ⟨θ, hn, hbound⟩ := short_current_relative_phase (currentComponentCurrent j c) hco hconn
    m hmin hL (by rw [hqs]; exact hshort) (componentCubeLower j c)
    (componentCubeLower_le j c) hcube tau field sheet hdecomp
  refine ⟨θ, hn, ?_⟩
  rw [hqs] at hbound
  have hmass := chainL1_sourceCurrentLatticeChain_le_energy (currentComponentCurrent j c)
  have hκ := sourceOmegaMax_nonneg (componentCubeLower j c)
    (2 * (currentComponentSupport j c).card) field
  have hC := relativeFillingConstant_pos
  have hLr : (0 : ℝ) ≤ ((currentComponentSupport j c).card : ℝ) := by positivity
  refine hbound.trans ?_
  have hcoef : 0 ≤ relativeFillingConstant *
      sourceOmegaMax (componentCubeLower j c) (2 * (currentComponentSupport j c).card) field *
      ((currentComponentSupport j c).card : ℝ) ^ 5 := by positivity
  calc relativeFillingConstant *
        sourceOmegaMax (componentCubeLower j c) (2 * (currentComponentSupport j c).card) field *
        ((currentComponentSupport j c).card : ℝ) ^ 5 *
        (chainL1 (sourceCurrentLatticeChain (currentComponentCurrent j c)) : ℝ)
      ≤ relativeFillingConstant *
        sourceOmegaMax (componentCubeLower j c) (2 * (currentComponentSupport j c).card) field *
        ((currentComponentSupport j c).card : ℝ) ^ 5 *
        currentEnergy (currentComponentCurrent j c) := mul_le_mul_of_nonneg_left hmass hcoef
    _ = _ := by
        simp only [componentCubeSide]
        ring

/-- Every real phase has a representative modulo `2π` of absolute value at most `π`. -/
theorem exists_phase_representative_abs_le_pi (x : ℝ) :
    ∃ θ : ℝ, (∃ n : ℤ, x + θ = 2 * Real.pi * (n : ℝ)) ∧ |θ| ≤ Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ) - x,
    ⟨round (x / (2 * Real.pi)), by ring⟩, ?_⟩
  have h := abs_sub_round (x / (2 * Real.pi))
  have hrew : 2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ) - x =
      -(2 * Real.pi) * (x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ)) := by
    field_simp
    ring
  rw [hrew, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  nlinarith

/-! ### The parent current -/

/-- The component maximum of the relative estimate: `L · max|field|` on a short component (so that
the bound has the shape `C · κ · E · L⁴`), and `π / C` on a long one. -/
def relativeComponentMax (m : ℕ) (j : IntegerCurrent B) (field : SourcePlaquette B → ℝ)
    (c : CurrentComponentClass j) : ℝ :=
  if (currentComponentSupport j c).card < m then
    ((currentComponentSupport j c).card : ℝ) *
      sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field
  else Real.pi / relativeFillingConstant

theorem relativeComponentMax_nonneg (m : ℕ) (j : IntegerCurrent B)
    (field : SourcePlaquette B → ℝ) (c : CurrentComponentClass j) :
    0 ≤ relativeComponentMax m j field c := by
  unfold relativeComponentMax
  split_ifs
  · exact mul_nonneg (by positivity) (sourceOmegaMax_nonneg _ _ _)
  · exact div_nonneg Real.pi_pos.le relativeFillingConstant_pos.le

/-- The energy of a nonzero current is at least one. -/
theorem one_le_currentEnergy_of_support_nonempty (q : IntegerCurrent B)
    (hq : q.support.Nonempty) : 1 ≤ currentEnergy q := by
  obtain ⟨e, he⟩ := hq
  have hne : q e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hterm : (1 : ℝ) ≤ ((q e : ℤ) : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (q e) ^ 2 := by
      have hpos : 0 < (q e) ^ 2 := by positivity
      omega
    exact_mod_cast h1
  unfold currentEnergy
  exact hterm.trans (Finset.single_le_sum (f := fun e : Link B => ((q e : ℤ) : ℝ) ^ 2)
    (fun _ _ => sq_nonneg _) he)

/-- The source phase is additive over the incidence components. -/
theorem sourceCurrentPhase_eq_sum_components (α : Link B → ℝ) (j : IntegerCurrent B) :
    sourceCurrentPhase α j =
      ∑ c ∈ currentComponents j, sourceCurrentPhase α (currentComponentCurrent j c) := by
  have h : ∀ q : IntegerCurrent B,
      sourceCurrentPhase α q = currentPhase (fun e => α e * (2 * Real.pi)) q := by
    intro q
    unfold sourceCurrentPhase currentPhase
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h, currentPhase_eq_sum_components]
  exact Finset.sum_congr rfl fun c _ => (h _).symm

/-- **The phase representative of a co-closed parent.** Each short component gets its relative
filling representative and each long component a representative in `[−π, π]`; the Jensen error of
their sum is bounded by the component majorants. -/
theorem exists_relativeParent_phase (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    (m : ℕ) (hmin : ∀ i, m ≤ B i) (a z : ℝ) (ha : 1 ≤ a) (hz0 : 0 ≤ z)
    (hz : z ≤ Real.exp (-(a * (currentEnergy j + currentLength j))))
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : ℝ,
      (∃ n : ℤ, sourceCurrentPhase (twistedLinkField tau) j + θ = 2 * Real.pi * (n : ℝ)) ∧
      jensenGamma z * θ ^ 2 ≤
        ∑ c ∈ currentComponents j,
          (20 * relativeFillingConstant ^ 2 / a ^ 2) *
            ((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
                relativeComponentMax m j field c ^ 2 := by
  classical
  have hC := relativeFillingConstant_pos
  have hcomp : ∀ c : CurrentComponentClass j, ∃ θ : ℝ, ∃ n : ℤ, c ∈ currentComponents j →
      (sourceCurrentPhase (twistedLinkField tau) (currentComponentCurrent j c) + θ =
          2 * Real.pi * (n : ℝ) ∧
        |θ| ≤ relativeFillingConstant * relativeComponentMax m j field c *
          currentEnergy (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ) ^ 4) := by
    intro c
    by_cases hc : c ∈ currentComponents j
    · by_cases hshort : (currentComponentSupport j c).card < m
      · obtain ⟨θ, ⟨n, hn⟩, hb⟩ :=
          component_relative_phase j hdiv hc m hmin hshort tau field sheet hdecomp
        refine ⟨θ, n, fun _ => ⟨hn, ?_⟩⟩
        simpa [relativeComponentMax, hshort] using hb
      · obtain ⟨θ, ⟨n, hn⟩, hb⟩ := exists_phase_representative_abs_le_pi
          (sourceCurrentPhase (twistedLinkField tau) (currentComponentCurrent j c))
        refine ⟨θ, n, fun _ => ⟨hn, hb.trans ?_⟩⟩
        have hne := currentComponentSupport_nonempty j hc
        have hE : 1 ≤ currentEnergy (currentComponentCurrent j c) :=
          one_le_currentEnergy_of_support_nonempty _
            (by rw [currentComponentCurrent_support]; exact hne)
        have hL : (1 : ℝ) ≤ ((currentComponentSupport j c).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hne
        have hL4 : (1 : ℝ) ≤ ((currentComponentSupport j c).card : ℝ) ^ 4 :=
          one_le_pow₀ hL
        have hmax : relativeFillingConstant * relativeComponentMax m j field c = Real.pi := by
          simp only [relativeComponentMax, ite_eq_right hshort]
          field_simp
        rw [hmax]
        have hpi := Real.pi_pos
        nlinarith [mul_le_mul hE hL4 zero_le_one (zero_le_one.trans hE)]
    · exact ⟨0, 0, fun h => (hc h).elim⟩
  choose θc nc hθc using hcomp
  refine ⟨∑ c ∈ currentComponents j, θc c, ⟨∑ c ∈ currentComponents j, nc c, ?_⟩, ?_⟩
  · rw [sourceCurrentPhase_eq_sum_components, ← Finset.sum_add_distrib, Int.cast_sum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c hc => (hθc c hc).1
  · by_cases hzero : j = 0
    · subst hzero
      simp [currentComponents]
    have hL : 1 ≤ currentLength j := by
      unfold currentLength
      have hne : j.support.Nonempty := Finsupp.support_nonempty_iff.mpr hzero
      exact_mod_cast Finset.card_pos.mpr hne
    have hzHalf : z ≤ 1 / 2 := activity_z_le_half_positive a
      (currentEnergy j) (currentLength j) z ha (currentEnergy_nonneg j) hL hz
    exact currentComponents_jensen_error_le_componentMajorants j a relativeFillingConstant z
      (jensenGamma z) (∑ c ∈ currentComponents j, θc c) θc (relativeComponentMax m j field)
      ha hC.le (fun c _ => relativeComponentMax_nonneg m j field c) rfl
      (jensenGamma_le_five_mul z hz0 hzHalf) hz (fun c hc => (hθc c hc).2)

/-! ### The family -/

/-- **Packing of the short majorants for an arbitrary field**, in the `L⁵` form of the relative
filling (the proof of `ShortComponentPhase.sum_componentMajorants_le` with the field in place of the local
curvature). -/
theorem sum_relativeMajorants_le (S : Finset (IntegerCurrent B))
    (hdisj : (↑S : Set (IntegerCurrent B)).PairwiseDisjoint fun j => j.support)
    (a : ℝ) (ha : 0 < a) (field : SourcePlaquette B → ℝ) :
    (∑ j ∈ S, ∑ c ∈ currentComponents j,
        sourceComponentActivityL5 a relativeFillingConstant
            (currentComponentSupport j c).card *
          (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2) ≤
      81 * sourceComponentCpackPrime a relativeFillingConstant *
        ∑ p : SourcePlaquette B, (field p) ^ 2 := by
  classical
  let I := Σ j : IntegerCurrent B, CurrentComponentClass j
  let X : Finset I := S.sigma fun j => currentComponents j
  let len : I → ℕ := fun x => (currentComponentSupport x.1 x.2).card
  let good : I → Prop := fun x =>
    (sourceOmega (B := B) (componentCubeLower x.1 x.2) (2 * len x)).Nonempty
  let err : I → ℝ := fun x =>
    sourceComponentActivityL5 a relativeFillingConstant (len x) *
      (sourceOmegaMax (componentCubeLower x.1 x.2) (2 * len x) field) ^ 2
  let T : Finset I := X.filter good
  have hsigma :
      (∑ j ∈ S, ∑ c ∈ currentComponents j,
        sourceComponentActivityL5 a relativeFillingConstant
            (currentComponentSupport j c).card *
          (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2) =
        ∑ x ∈ X, err x := (Finset.sum_sigma S (fun j => currentComponents j) err).symm
  have hbad : ∀ x ∈ X, ¬good x → err x = 0 := by
    intro x _ hgood
    have h0 := sourceOmegaMax_eq_zero_of_empty
      (componentCubeLower x.1 x.2) (2 * len x) field hgood
    simp [err, h0]
  have hfilter : ∑ x ∈ X, err x = ∑ x ∈ T, err x := by
    refine (Finset.sum_subset (Finset.filter_subset good X) fun x hx hxT => ?_).symm
    exact hbad x hx fun hg => hxT (Finset.mem_filter.mpr ⟨hx, hg⟩)
  rw [hsigma, hfilter]
  have hRHS : 0 ≤ 81 * sourceComponentCpackPrime a relativeFillingConstant *
      ∑ p : SourcePlaquette B, (field p) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (sourceComponentCpackPrime_nonneg a _ ha))
      (Finset.sum_nonneg fun p _ => sq_nonneg _)
  rcases T.eq_empty_or_nonempty with hT | ⟨x₀, hx₀⟩
  · rw [hT, Finset.sum_empty]
    exact hRHS
  have hgood₀ : good x₀ := (Finset.mem_filter.mp hx₀).2
  let pbase : SourcePlaquette B := hgood₀.choose
  let plaq : I → SourcePlaquette B := fun x =>
    if h : good x then
      sourceMaximizingPlaquette (componentCubeLower x.1 x.2) (2 * len x) field h
    else pbase
  have hmemX : ∀ x ∈ T, x.1 ∈ S ∧ x.2 ∈ currentComponents x.1 := by
    intro x hx
    exact Finset.mem_sigma.mp (Finset.mem_filter.mp hx).1
  have hlenpos : ∀ x ∈ T, 1 ≤ len x := by
    intro x hx
    exact Finset.card_pos.mpr (currentComponentSupport_nonempty x.1 (hmemX x hx).2)
  refine finite_current_packing_l2_side_six_positive T (T.image len)
    (fun x => currentComponentSupport x.1 x.2)
    (fun p L => sourceCenteredLinkBox (B := B) (sourcePlaquetteCoord p) (3 * L))
    plaq len err field (sourceComponentActivityL5 a relativeFillingConstant)
    (81 * sourceComponentCpackPrime a relativeFillingConstant)
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
    have hgx : good x := (Finset.mem_filter.mp hx).2
    have hpl : plaq x = sourceMaximizingPlaquette
        (componentCubeLower x.1 x.2) (2 * len x) field hgx := dite_eq_left hgx
    rw [hpl]
    exact component_subset_controlledCenteredLinkBox (hlenpos x hx)
      (by simpa [len, componentCubeSide] using componentSupport_in_componentCube x.1 x.2)
      (sourceMaximizingPlaquette_mem _ _ _ hgx)
  · intro p L
    have h := sourceCenteredLinkBox_card_le (B := B) (sourcePlaquetteCoord p) (3 * L)
    have e : 2 * (3 * L) = 6 * L := by ring
    rwa [e] at h
  · intro x hx
    have hgx : good x := (Finset.mem_filter.mp hx).2
    have hpl : plaq x = sourceMaximizingPlaquette
        (componentCubeLower x.1 x.2) (2 * len x) field hgx := dite_eq_left hgx
    have hmax : sourceOmegaMax (componentCubeLower x.1 x.2) (2 * len x) field =
        |field (plaq x)| := by
      rw [hpl]
      exact sourceOmegaMax_eq_maximizingPlaquette _ _ _ hgx
    simp only [err]
    rw [hmax, sq_abs]

/-- A long length has `L⁸ e^{−aL} ≤ L e^{−(a−7)m}` once `a ≥ 7` and `L ≥ m`. -/
theorem long_majorant_le {a : ℝ} (ha : 7 ≤ a) {L m : ℕ} (hLm : m ≤ L) :
    (L : ℝ) ^ 8 * Real.exp (-(a * (L : ℝ))) ≤ (L : ℝ) * Real.exp (-((a - 7) * (m : ℝ))) := by
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h1 : (L : ℝ) ≤ Real.exp (L : ℝ) := by linarith [Real.add_one_le_exp (L : ℝ)]
  have h7 : (L : ℝ) ^ 7 ≤ Real.exp (7 * (L : ℝ)) := by
    calc (L : ℝ) ^ 7 ≤ Real.exp (L : ℝ) ^ 7 := pow_le_pow_left₀ hL0 h1 7
      _ = Real.exp (7 * (L : ℝ)) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hm : Real.exp (-((a - 7) * (L : ℝ))) ≤ Real.exp (-((a - 7) * (m : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hLm' : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLm
    nlinarith
  calc (L : ℝ) ^ 8 * Real.exp (-(a * (L : ℝ)))
      = (L : ℝ) * ((L : ℝ) ^ 7 * Real.exp (-(a * (L : ℝ)))) := by ring
    _ ≤ (L : ℝ) * (Real.exp (7 * (L : ℝ)) * Real.exp (-(a * (L : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le) hL0
    _ = (L : ℝ) * Real.exp (-((a - 7) * (L : ℝ))) := by
        rw [← Real.exp_add]
        congr 2
        ring
    _ ≤ (L : ℝ) * Real.exp (-((a - 7) * (m : ℝ))) := mul_le_mul_of_nonneg_left hm hL0

/-- **The long components.** In a family with pairwise disjoint supports the long majorants sum to
at most the number of links times `e^{−(a−7)m}`. -/
theorem sum_longMajorants_le (S : Finset (IntegerCurrent B))
    (hdisj : (↑S : Set (IntegerCurrent B)).PairwiseDisjoint fun j => j.support)
    (m N : ℕ) (hBmax : ∀ i : Fin 4, B i ≤ N) (a : ℝ) (ha : 7 ≤ a) :
    (∑ j ∈ S, ∑ c ∈ currentComponents j,
        if (currentComponentSupport j c).card < m then (0 : ℝ) else
          ((currentComponentSupport j c).card : ℝ) ^ 8 *
            Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) ≤
      ((4 * (N + 1) ^ 4 : ℕ) : ℝ) * Real.exp (-((a - 7) * (m : ℝ))) := by
  classical
  have hterm : ∀ j ∈ S, ∀ c ∈ currentComponents j,
      (if (currentComponentSupport j c).card < m then (0 : ℝ) else
          ((currentComponentSupport j c).card : ℝ) ^ 8 *
            Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) ≤
        ((currentComponentSupport j c).card : ℝ) * Real.exp (-((a - 7) * (m : ℝ))) := by
    intro j _ c _
    split_ifs with h
    · positivity
    · exact long_majorant_le ha (not_lt.mp h)
  have hcard : (∑ j ∈ S, (j.support.card : ℝ)) ≤ ((4 * (N + 1) ^ 4 : ℕ) : ℝ) := by
    have h1 : ∑ j ∈ S, j.support.card = (S.biUnion fun j => j.support).card :=
      (Finset.card_biUnion hdisj).symm
    have h2 : (S.biUnion fun j => j.support).card ≤ Fintype.card (Link B) :=
      Finset.card_le_univ _
    have h3 : Fintype.card (Link B) ≤ 4 * (N + 1) ^ 4 := sourceDualOneCells_card_le_4 hBmax
    have h4 : ∑ j ∈ S, j.support.card ≤ 4 * (N + 1) ^ 4 := by omega
    exact_mod_cast h4
  calc (∑ j ∈ S, ∑ c ∈ currentComponents j,
        if (currentComponentSupport j c).card < m then (0 : ℝ) else
          ((currentComponentSupport j c).card : ℝ) ^ 8 *
            Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))))
      ≤ ∑ j ∈ S, ∑ c ∈ currentComponents j,
          ((currentComponentSupport j c).card : ℝ) * Real.exp (-((a - 7) * (m : ℝ))) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun c hc => hterm j hj c hc
    _ = (∑ j ∈ S, (j.support.card : ℝ)) * Real.exp (-((a - 7) * (m : ℝ))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, ← currentLength_additive]
        rfl
    _ ≤ ((4 * (N + 1) ^ 4 : ℕ) : ℝ) * Real.exp (-((a - 7) * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le

/-- **The relative-filling Wilson estimate.** For a family of co-closed currents with pairwise
disjoint supports and activities below `e^{−a(‖j‖² + |j|)}`, `a ≥ 7`, in a box with sides between
`m` and `N`: if the curvature of the zero-extended `tau` is an integer sheet minus `field` on
every plaquette, then the source phases have representatives modulo `2π` whose Jensen errors sum
to at most

`81 c'_pack(a) ‖field‖² + (20π²/a²) · 4(N+1)⁴ · e^{−(a−7)m}`.

The first term comes from the short components and their relative fillings, the second from the
components of length at least `m`. -/
theorem relative_filling_wilson_bound (S : Finset (IntegerCurrent B))
    (hclosed : ∀ j ∈ S, currentDivergence j = 0)
    (hdisj : (↑S : Set (IntegerCurrent B)).PairwiseDisjoint fun j => j.support)
    (m N : ℕ) (hmin : ∀ i, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    (a : ℝ) (ha : 7 ≤ a) (z : IntegerCurrent B → ℝ)
    (hz : ∀ j ∈ S,
      0 ≤ z j ∧ z j ≤ Real.exp (-(a * (currentEnergy j + currentLength j))))
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (field : SourcePlaquette B → ℝ) (sheet : SourcePlaquette B → ℤ)
    (hdecomp : ∀ p : SourcePlaquette B,
      field p + chainCoboundary (sourcePrimalOneForm tau) p.1 = (sheet p : ℝ)) :
    ∃ θ : IntegerCurrent B → ℝ,
      (∀ j ∈ S, ∃ n : ℤ,
        sourceCurrentPhase (twistedLinkField tau) j + θ j = 2 * Real.pi * (n : ℝ)) ∧
      ∑ j ∈ S, jensenGamma (z j) * θ j ^ 2 ≤
        81 * sourceComponentCpackPrime a relativeFillingConstant *
            ∑ p : SourcePlaquette B, (field p) ^ 2 +
          (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (N + 1) ^ 4 : ℕ) : ℝ) *
            Real.exp (-((a - 7) * (m : ℝ))) := by
  classical
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hC := relativeFillingConstant_pos
  have hpar : ∀ j : IntegerCurrent B, ∃ θ : ℝ, j ∈ S →
      ((∃ n : ℤ, sourceCurrentPhase (twistedLinkField tau) j + θ = 2 * Real.pi * (n : ℝ)) ∧
        jensenGamma (z j) * θ ^ 2 ≤
          ∑ c ∈ currentComponents j,
            (20 * relativeFillingConstant ^ 2 / a ^ 2) *
              ((currentComponentSupport j c).card : ℝ) ^ 8 *
                Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
                  relativeComponentMax m j field c ^ 2) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨θ, hn, hb⟩ := exists_relativeParent_phase j (hclosed j hj) m hmin a (z j) ha1
        (hz j hj).1 (hz j hj).2 tau field sheet hdecomp
      exact ⟨θ, fun _ => ⟨hn, hb⟩⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose θ hθ using hpar
  refine ⟨θ, fun j hj => (hθ j hj).1, ?_⟩
  have hsplit : ∀ j ∈ S, ∀ c ∈ currentComponents j,
      (20 * relativeFillingConstant ^ 2 / a ^ 2) *
          ((currentComponentSupport j c).card : ℝ) ^ 8 *
            Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
              relativeComponentMax m j field c ^ 2 ≤
        sourceComponentActivityL5 a relativeFillingConstant
            (currentComponentSupport j c).card *
          (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2 +
        (20 * Real.pi ^ 2 / a ^ 2) *
          (if (currentComponentSupport j c).card < m then (0 : ℝ) else
            ((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) := by
    intro j _ c _
    by_cases hshort : (currentComponentSupport j c).card < m
    · simp only [relativeComponentMax, ite_eq_left hshort, sourceComponentActivityL5, mul_zero,
        add_zero]
      apply le_of_eq
      ring
    · simp only [relativeComponentMax, ite_eq_right hshort, sourceComponentActivityL5]
      have hnn : 0 ≤ (20 * relativeFillingConstant ^ 2 / a ^ 2) *
          ((currentComponentSupport j c).card : ℝ) ^ 10 *
            Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
          (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2 := by
        positivity
      have heq : (20 * relativeFillingConstant ^ 2 / a ^ 2) *
            ((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))) *
                (Real.pi / relativeFillingConstant) ^ 2 =
          (20 * Real.pi ^ 2 / a ^ 2) *
            (((currentComponentSupport j c).card : ℝ) ^ 8 *
              Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) := by
        field_simp
      rw [heq]
      linarith
  calc ∑ j ∈ S, jensenGamma (z j) * θ j ^ 2
      ≤ ∑ j ∈ S, ∑ c ∈ currentComponents j,
          (sourceComponentActivityL5 a relativeFillingConstant
              (currentComponentSupport j c).card *
            (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2 +
          (20 * Real.pi ^ 2 / a ^ 2) *
            (if (currentComponentSupport j c).card < m then (0 : ℝ) else
              ((currentComponentSupport j c).card : ℝ) ^ 8 *
                Real.exp (-(a * ((currentComponentSupport j c).card : ℝ))))) :=
        Finset.sum_le_sum fun j hj => (hθ j hj).2.trans
          (Finset.sum_le_sum fun c hc => hsplit j hj c hc)
    _ = (∑ j ∈ S, ∑ c ∈ currentComponents j,
          sourceComponentActivityL5 a relativeFillingConstant
              (currentComponentSupport j c).card *
            (sourceOmegaMax (componentCubeLower j c) (componentCubeSide j c) field) ^ 2) +
        (20 * Real.pi ^ 2 / a ^ 2) *
          ∑ j ∈ S, ∑ c ∈ currentComponents j,
            (if (currentComponentSupport j c).card < m then (0 : ℝ) else
              ((currentComponentSupport j c).card : ℝ) ^ 8 *
                Real.exp (-(a * ((currentComponentSupport j c).card : ℝ)))) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 81 * sourceComponentCpackPrime a relativeFillingConstant *
            ∑ p : SourcePlaquette B, (field p) ^ 2 +
          (20 * Real.pi ^ 2 / a ^ 2) * (((4 * (N + 1) ^ 4 : ℕ) : ℝ) *
            Real.exp (-((a - 7) * (m : ℝ)))) :=
        add_le_add (sum_relativeMajorants_le S hdisj a ha0 field)
          (mul_le_mul_of_nonneg_left (sum_longMajorants_le S hdisj m N hBmax a ha)
            (by positivity))
    _ = _ := by ring

end

end FroehlichSpencer.FS82.Wilson

end
