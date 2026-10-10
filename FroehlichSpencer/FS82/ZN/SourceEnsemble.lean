/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.SourceState
public import FroehlichSpencer.FS82.ZN.JensenPacking

/-!
# the lower bound for one separated ensemble on a centred cube

`state_lower_bound`: for one separated ensemble of `Nℤ`-valued currents of the §2 expansion on the
dual links of a centred cube, with the Wilson weight on any set `Q` of dual plaquettes and the
sheet twist `φ = (ξ/N) σ`,

`∫ ∏ (1 + K cos 2π(ϱ, θ)) W_φ ≥ e^{−E(β,N) (ξ/N)² (L+T)} ∫ ∏ (1 + K cos 2π(ϱ, θ)) W_0`.

This is FS82 (3.49)–(3.50) for one `γ`.

`znStateError β N = 72 D(a, N) + 24π² (β/2 + 7 c₁(β) e^{−a})`, `a = znActivityRate β N`,
`c₁(β) = 6β(e−1) + 72β²(e−1)²`.
The source residual satisfies `‖ε‖² ≤ 24π² (ξ/N)² (L+T)` in radians. This upper bound
replaces the printed lower bound (3.53) in deriving (3.54).
-/

open scoped BigOperators
open MeasureTheory
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.CurrentDecay
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Root.MomentComparisonAssembly
open FroehlichSpencer.FS82.ZN.Torus
open FroehlichSpencer.FS82.ZN.Renormalization

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

local instance sourceEnsemble_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance sourceEnsemble_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {B : Box 4}

/-! ### The selected links of a lineage current (FS82 (3.31)) -/

/-- The colour class selected for a lineage current. -/
def selColor (q : Link B → ℤ) (h : ExpansionLineage B) : Fin 8 :=
  Classical.choose (selectedCurrentLinks_l1 (lineageJ q h))

/-- The selected links `ℬ_ϱ` of a lineage current. -/
def selLinks (q : Link B → ℤ) (h : ExpansionLineage B) : Finset (Link B) :=
  colorClass (lineageJ q h).support linkColor (selColor q h)

/-- The shift vector of a lineage current: `sign(ϱ_x)` on its selected links. -/
def selShift (q : Link B → ℤ) (h : ExpansionLineage B) : Link B → ℝ :=
  linkShift (lineageCurrent q h) (selLinks q h)

theorem selLinks_subset (q : Link B → ℤ) (h : ExpansionLineage B) :
    selLinks q h ⊆ (lineageJ q h).support := by
  unfold selLinks colorClass
  exact Finset.filter_subset _ _

theorem selLinks_mass (q : Link B → ℤ) (h : ExpansionLineage B) :
    sourceCurrentL1Mass (lineageJ q h) / 18 ≤
      ∑ x ∈ selLinks q h, |(lineageCurrent q h x : ℝ)| := by
  have hspec := (Classical.choose_spec (selectedCurrentLinks_l1 (lineageJ q h))).1
  unfold classMass at hspec
  refine hspec.trans (le_of_eq ?_)
  unfold selLinks selColor
  exact Finset.sum_congr rfl fun x _ => by
    beta_reduce
    rw [lineageJ_apply]

theorem selLinks_within (q : Link B → ℤ) (h : ExpansionLineage B) :
    ∀ e ∈ selLinks q h, ∀ f ∈ selLinks q h,
      ¬ (e ≠ f ∧ ∃ p : SourceDualTwoCells B,
        linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) :=
  (Classical.choose_spec (selectedCurrentLinks_l1 (lineageJ q h))).2

/-! ### One state -/

/-- The properties of a terminal state of the expansion used below. -/
structure StateHyp (N : ℕ) (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B) : Prop where
  sep : IsSeparatedCurrentState q s
  valid : IsValidCurrentState q s
  Kpos : ∀ h ∈ s, 0 < lineageCoefficient q z h
  Kenv : ∀ h ∈ s, lineageCoefficient q z h ≤ sourceFourierKEnvelope (N : ℝ) (lineageJ q h)
  mult : ∀ h ∈ s, IsNMultipleSourceCurrent N (lineageJ q h)

section State

variable {N : ℕ} {q : Link B → ℤ} {z : ℤ → ℝ} {s : CurrentState B}

theorem StateHyp.support_nonempty (H : StateHyp N q z s) (i : {h : ExpansionLineage B // h ∈ s}) :
    (lineageJ q i.1).support.Nonempty := by
  rw [lineageJ_support_eq_stateCurrent q s i]
  exact stateCurrent_support_nonempty H.valid i

theorem StateHyp.disjoint (H : StateHyp N q z s) (i j : {h : ExpansionLineage B // h ∈ s})
    (hij : i ≠ j) : Disjoint (lineageJ q i.1).support (lineageJ q j.1).support := by
  rw [lineageJ_support_eq_stateCurrent q s i, lineageJ_support_eq_stateCurrent q s j]
  exact state_hdisjoint H.sep i j hij

theorem StateHyp.lineageJ_injective (H : StateHyp N q z s) :
    Function.Injective fun i : {h : ExpansionLineage B // h ∈ s} => lineageJ q i.1 := by
  intro i j hij
  by_contra hne
  obtain ⟨e, he⟩ := H.support_nonempty i
  have hf : e ∈ (lineageJ q j.1).support := by
    have : lineageJ q i.1 = lineageJ q j.1 := hij
    rw [← this]
    exact he
  exact Finset.disjoint_left.mp (H.disjoint i j hne) he hf

/-- `hcross`: the shift of one current does not see another current of the state. -/
theorem StateHyp.cross (H : StateHyp N q z s) (i j : {h : ExpansionLineage B // h ∈ s})
    (hij : i ≠ j) :
    ∑ x : Link B, (lineageCurrent q i.1 x : ℝ) * selShift q j.1 x = 0 := by
  refine sum_mul_linkShift_eq_zero _ _ _ fun x hx => ?_
  have hxj : x ∈ (lineageJ q j.1).support := selLinks_subset q j.1 hx
  have hxi : x ∉ (lineageJ q i.1).support := fun h =>
    Finset.disjoint_left.mp (H.disjoint i j hij) h hxj
  have := Finsupp.notMem_support_iff.mp hxi
  simpa using this

/-- `hplaq`: no plaquette is shifted by two currents of the state. -/
theorem StateHyp.plaq (H : StateHyp N q z s) (Q : Finset (SourceDualTwoCells B))
    (p : {p : SourceDualTwoCells B // p ∈ Q}) (i j : {h : ExpansionLineage B // h ∈ s})
    (hij : i ≠ j) :
    plaqShift (modelInc Q) (selShift q i.1) p = 0 ∨
      plaqShift (modelInc Q) (selShift q j.1) p = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hxinc⟩ := exists_incident_of_plaqShift_ne_zero Q _ _ p hcon.1
  obtain ⟨y, hy, hyinc⟩ := exists_incident_of_plaqShift_ne_zero Q _ _ p hcon.2
  have hxs := selLinks_subset q i.1 hx
  have hys := selLinks_subset q j.1 hy
  rw [lineageJ_support_eq_stateCurrent q s i] at hxs
  rw [lineageJ_support_eq_stateCurrent q s j] at hys
  exact state_hplaq H.sep i j hij x hxs y hys ⟨p.1, hxinc, hyinc⟩

/-- **The activity of one current** (FS82 (3.37)–(3.40)): `K A ≤ e^{−a(‖ϱ‖₁/N + |ϱ|)}`. -/
theorem StateHyp.activity_le (H : StateHyp N q z s) (Q : Finset (SourceDualTwoCells B))
    {β : ℝ} (hβ : 0 ≤ β) (hN : 0 < N) (hrate : 0 ≤ znActivityRate β N)
    (i : {h : ExpansionLineage B // h ∈ s}) :
    lineageCoefficient q z i.1 *
        attenuation β (modelInc Q) (lineageCurrent q i.1) (selShift q i.1) ≤
      Real.exp (-(znActivityRate β N *
        (currentL1Norm (lineageJ q i.1) / (N : ℝ) + currentLength (lineageJ q i.1)))) := by
  classical
  have hK0 := (H.Kpos i.1 i.2).le
  have hatt := attenuation_le hβ (modelInc Q) (lineageCurrent q i.1) (selShift q i.1)
    (6 * (selLinks q i.1).card)
    (abs_plaqShift_le_one Q _ _ (selLinks_within q i.1))
    (card_plaqShift_ne_zero_le Q _ _)
  have hcard : ((selLinks q i.1).card : ℝ) ≤ ((lineageJ q i.1).support.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (selLinks_subset q i.1)
  have hcosh : 0 ≤ Real.cosh 1 - 1 := by linarith [Real.one_le_cosh (1 : ℝ)]
  have hexp : Real.exp (β * (Real.cosh 1 - 1) * ((6 * (selLinks q i.1).card : ℕ) : ℝ) -
        ∑ x, (lineageCurrent q i.1 x : ℝ) * selShift q i.1 x) ≤
      Real.exp (6 * β * (Real.cosh 1 - 1) * ((lineageJ q i.1).support.card : ℝ) -
        ∑ x ∈ selLinks q i.1, |(lineageCurrent q i.1 x : ℝ)|) := by
    apply Real.exp_le_exp.mpr
    rw [show (∑ x, (lineageCurrent q i.1 x : ℝ) * selShift q i.1 x) =
      ∑ x ∈ selLinks q i.1, |(lineageCurrent q i.1 x : ℝ)| from sum_mul_linkShift _ _]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcard (mul_nonneg hβ hcosh)]
  calc lineageCoefficient q z i.1 *
        attenuation β (modelInc Q) (lineageCurrent q i.1) (selShift q i.1)
      ≤ lineageCoefficient q z i.1 *
          Real.exp (6 * β * (Real.cosh 1 - 1) * ((lineageJ q i.1).support.card : ℝ) -
            ∑ x ∈ selLinks q i.1, |(lineageCurrent q i.1 x : ℝ)|) :=
        mul_le_mul_of_nonneg_left (hatt.trans hexp) hK0
    _ = sourceLocalActivity β ((lineageJ q i.1).support.card : ℝ) (lineageCoefficient q z i.1)
          (∑ x ∈ selLinks q i.1, |(lineageCurrent q i.1 x : ℝ)|) := rfl
    _ ≤ _ := sourceLocalActivity_le_l1Envelope β N _ _ (lineageJ q i.1) hβ hN hrate
        (H.mult i.1 i.2) (H.Kenv i.1 i.2) (selLinks_mass q i.1)

/-- The envelope times `1 + 6|ϱ|` is at most `7 e^{−a}`. -/
theorem StateHyp.envelope_mul_le (H : StateHyp N q z s) (hN : 0 < N) {a : ℝ} (ha : 1 ≤ a)
    (i : {h : ExpansionLineage B // h ∈ s}) :
    Real.exp (-(a * (currentL1Norm (lineageJ q i.1) / (N : ℝ) + currentLength (lineageJ q i.1)))) *
        (1 + ((6 * (selLinks q i.1).card : ℕ) : ℝ)) ≤ 7 * Real.exp (-a) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨Lr, hLr⟩ : ∃ Lr : ℝ, Lr = ((lineageJ q i.1).support.card : ℝ) := ⟨_, rfl⟩
  have hL1 : (1 : ℝ) ≤ Lr := by
    rw [hLr]
    exact_mod_cast Finset.card_pos.mpr (H.support_nonempty i)
  have hsel : ((selLinks q i.1).card : ℝ) ≤ Lr := by
    rw [hLr]
    exact_mod_cast Finset.card_le_card (selLinks_subset q i.1)
  have hmass : Lr ≤ currentL1Norm (lineageJ q i.1) / (N : ℝ) := by
    have h := sourceCurrentL1Mass_ge_support_mul_N N (lineageJ q i.1) (H.mult i.1 i.2)
    rw [le_div_iff₀ hNR, hLr]
    rw [sourceCurrentL1Mass_eq_currentL1Norm] at h
    linarith
  have hlen : currentLength (lineageJ q i.1) = Lr := hLr.symm
  have hexp1 : Real.exp (-(a * (currentL1Norm (lineageJ q i.1) / (N : ℝ) +
      currentLength (lineageJ q i.1)))) ≤ Real.exp (-a) * Real.exp (-Lr) := by
    rw [← Real.exp_add, hlen]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by linarith : (0 : ℝ) ≤ Lr - 1),
      mul_le_mul_of_nonneg_left hmass (by linarith : (0 : ℝ) ≤ a)]
  have hLexp : Lr * Real.exp (-Lr) ≤ 1 := by
    have h1 := Real.add_one_le_exp Lr
    have hpos : 0 < Real.exp Lr := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
    linarith
  have hfac : (1 + ((6 * (selLinks q i.1).card : ℕ) : ℝ)) ≤ 7 * Lr := by
    push_cast
    linarith
  calc _ ≤ (Real.exp (-a) * Real.exp (-Lr)) * (7 * Lr) :=
        mul_le_mul hexp1 hfac (by positivity) (by positivity)
    _ = 7 * Real.exp (-a) * (Lr * Real.exp (-Lr)) := by ring
    _ ≤ 7 * Real.exp (-a) * 1 := mul_le_mul_of_nonneg_left hLexp (by positivity)
    _ = _ := by ring

end State

/-! ### The lower bound for one ensemble on a centred cube -/

/-- The error coefficient of one ensemble:
`72 D(a, N) + 24π² (β/2 + 7 c₁(β) e^{−a})`. -/
def znStateError (β : ℝ) (N : ℕ) : ℝ :=
  72 * znPackingCoefficient (znActivityRate β N) N +
    24 * Real.pi ^ 2 * (β / 2 +
      7 * (6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2) *
        Real.exp (-(znActivityRate β N)))


theorem sum_sq_residual_le {L T M N ξ : ℕ} (hM : max L T + 1 ≤ M)
    (Q : Finset (SourceDualTwoCells (cube M))) :
    ∑ p : {p : SourceDualTwoCells (cube M) // p ∈ Q},
        (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) *
          loopFieldResidual (sourceLatticeComplex (B := cube M)) (cubeSheet L T M) p.1)) ^ 2 ≤
      24 * Real.pi ^ 2 * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, r = loopFieldResidual (sourceLatticeComplex (B := cube M))
    (cubeSheet L T M) := ⟨_, rfl⟩
  rw [← hr]
  have hrle : ‖r‖ ^ 2 ≤ 6 * ((L : ℝ) + T) := by
    rw [hr]
    exact cube_loopField_normSq_le hM
  have hnorm : (∑ f : SourceDualTwoCells (cube M), (r f) ^ 2) = ‖r‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have h1 : ∑ p : {p : SourceDualTwoCells (cube M) // p ∈ Q},
      (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) * r p.1)) ^ 2 =
      ∑ p ∈ Q, (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) * r p)) ^ 2 :=
    Finset.sum_coe_sort Q fun p => (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) * r p)) ^ 2
  have h2 : ∑ p ∈ Q, (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) * r p)) ^ 2 ≤
      ∑ p : SourceDualTwoCells (cube M), (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) * r p)) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun p => sq_nonneg _
  have h3 : ∑ p : SourceDualTwoCells (cube M), (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) * r p)) ^ 2 =
      (2 * Real.pi * ((ξ : ℝ) / (N : ℝ))) ^ 2 * ‖r‖ ^ 2 := by
    rw [← hnorm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h1]
  refine h2.trans ?_
  rw [h3]
  have hc : 0 ≤ (2 * Real.pi * ((ξ : ℝ) / (N : ℝ))) ^ 2 := sq_nonneg _
  calc (2 * Real.pi * ((ξ : ℝ) / (N : ℝ))) ^ 2 * ‖r‖ ^ 2
      ≤ (2 * Real.pi * ((ξ : ℝ) / (N : ℝ))) ^ 2 * (6 * ((L : ℝ) + T)) :=
        mul_le_mul_of_nonneg_left hrle hc
    _ = _ := by ring

/-- **The lower bound for one ensemble** (FS82 (3.49)–(3.50) on a centred cube). -/
theorem state_lower_bound {L T M N ξ : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hM : max L T + 1 ≤ M)
    (hN : 0 < N) (hξ : 1 ≤ ξ) {β : ℝ} (hβ : 0 ≤ β) (ha : 11 ≤ znActivityRate β N)
    (Q : Finset (SourceDualTwoCells (cube M)))
    (t : EuclideanSpace ℝ (SourceDualOneCells (cube M)))
    (ht : (sourceLatticeComplex (B := cube M)).d₁ t =
      cubeSheet L T M -
        loopFieldResidual (sourceLatticeComplex (B := cube M)) (cubeSheet L T M))
    {q : Link (cube M) → ℤ} {z : ℤ → ℝ} {s : CurrentState (cube M)} (H : StateHyp N q z s) :
    Real.exp (-(znStateError β N * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) *
        ∫ θ : Link (cube M) → UnitAddCircle,
          (∏ i : {h : ExpansionLineage (cube M) // h ∈ s},
            cosFactor (lineageCoefficient q z i.1) (lineageCurrent q i.1) 0 θ) *
          wilsonWeight β (modelInc Q) (fun _ => 0) θ ≤
      ∫ θ : Link (cube M) → UnitAddCircle,
        (∏ i : {h : ExpansionLineage (cube M) // h ∈ s},
          cosFactor (lineageCoefficient q z i.1) (lineageCurrent q i.1) 0 θ) *
        wilsonWeight β (modelInc Q) (fun p => (ξ : ℝ) / (N : ℝ) * cubeSheet L T M p.1) θ := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpi := Real.pi_pos
  obtain ⟨a, haeq⟩ : ∃ a : ℝ, a = znActivityRate β N := ⟨_, rfl⟩
  have ha' : 11 ≤ a := by rw [haeq]; exact ha

  obtain ⟨θ, hθ, hθsum⟩ := cube_zn_phase_bound hL hT hM hN hξ ha'
    ((Finset.univ.filter fun i : {h : ExpansionLineage (cube M) // h ∈ s} =>
      currentDivergence (lineageJ q i.1) = 0).image fun i => lineageJ q i.1)
    (by
      intro ρ hρ
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
      exact H.mult i.1 i.2)
    (by
      intro ρ hρ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hρ
      exact (Finset.mem_filter.mp hi).2)
    (by
      intro ρ₁ h₁ ρ₂ h₂ hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h₂
      exact H.disjoint i j fun h => hne (by rw [h]))
    (fun ρ => Real.exp (-(a * (currentL1Norm ρ / (N : ℝ) + currentLength ρ))))
    (fun ρ => Real.exp (-(a * (currentL1Norm ρ / (N : ℝ) + currentLength ρ))))
    (fun ρ _ _ => by
      have := Real.exp_pos (-(a * (currentL1Norm ρ / (N : ℝ) + currentLength ρ)))
      linarith)
    (fun ρ _ => le_rfl) t ht
  have hzle : ∀ i : {h : ExpansionLineage (cube M) // h ∈ s},
      lineageCoefficient q z i.1 *
          attenuation β (modelInc Q) (lineageCurrent q i.1) (selShift q i.1) ≤
        Real.exp (-(a * (currentL1Norm (lineageJ q i.1) / (N : ℝ) +
          currentLength (lineageJ q i.1)))) := by
    intro i
    rw [haeq]
    exact H.activity_le Q hβ hN (by linarith) i
  have hz0 : ∀ i : {h : ExpansionLineage (cube M) // h ∈ s},
      0 ≤ lineageCoefficient q z i.1 *
        attenuation β (modelInc Q) (lineageCurrent q i.1) (selShift q i.1) := fun i =>
    mul_nonneg (H.Kpos i.1 i.2).le (attenuation_pos _ _ _ _).le
  have hzhalf : ∀ i : {h : ExpansionLineage (cube M) // h ∈ s},
      Real.exp (-(a * (currentL1Norm (lineageJ q i.1) / (N : ℝ) +
        currentLength (lineageJ q i.1)))) ≤ 1 / 2 := by
    intro i
    have hlen : 1 ≤ currentLength (lineageJ q i.1) := by
      unfold currentLength
      exact_mod_cast Finset.card_pos.mpr (H.support_nonempty i)
    exact activity_z_le_half_positive a (currentL1Norm (lineageJ q i.1) / (N : ℝ))
      (currentLength (lineageJ q i.1)) _ (by linarith)
      (div_nonneg (currentL1Norm_nonneg _) hNR.le) hlen le_rfl
  refine ensemble_lower_bound hβ (modelInc Q) (fun p => (ξ : ℝ) / (N : ℝ) * cubeSheet L T M p.1)
    (fun p => (ξ : ℝ) / (N : ℝ) *
      loopFieldResidual (sourceLatticeComplex (B := cube M)) (cubeSheet L T M) p.1)
    (twistedLinkField ((-(ξ : ℝ) / (N : ℝ)) • t)) ?_
    (fun i : {h : ExpansionLineage (cube M) // h ∈ s} => lineageCoefficient q z i.1)
    (fun i => lineageCurrent q i.1)
    (fun i => currentDivergence (lineageJ q i.1) = 0)
    (fun i => stateGaugeDir q i.1)
    (fun i _ p => sum_curlInt_stateGaugeDir q i.1 p.1)
    (fun i hi => sum_mul_stateGaugeDir_ne_zero q i.1 hi)
    (fun i j _ hji => sum_mul_stateGaugeDir_eq_zero H.sep i j hji)
    (fun i => selShift q i.1)
    (fun i j _ _ hij => H.cross i j hij)
    (fun p i j _ _ hij => H.plaq Q p i j hij)
    (fun i _ => (H.Kpos i.1 i.2).le)
    (fun i _ => (hzle i).trans (hzhalf i))
    (fun i => -(θ (lineageJ q i.1)) / (2 * Real.pi)) ?_ _ ?_
  · -- the translation
    intro p
    have h := sum_curlInt_twistedLinkField ((-(ξ : ℝ) / (N : ℝ)) • t) p.1
    rw [map_smul, ht] at h
    have h' : ∑ e : Link (cube M), ((modelInc Q p e : ℤ) : ℝ) *
        twistedLinkField ((-(ξ : ℝ) / (N : ℝ)) • t) e =
        ((-(ξ : ℝ) / (N : ℝ)) • (cubeSheet L T M -
          loopFieldResidual (sourceLatticeComplex (B := cube M)) (cubeSheet L T M))) p.1 := h
    rw [h']
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  · -- the phase representatives
    intro i hi
    obtain ⟨n, hn⟩ := hθ (lineageJ q i.1)
      (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
    refine ⟨n, ?_⟩
    unfold sourceCurrentPhase at hn
    have hsum : ∑ e : Link (cube M), twistedLinkField ((-(ξ : ℝ) / (N : ℝ)) • t) e *
          (2 * Real.pi * ((lineageJ q i.1 e : ℤ) : ℝ)) =
        2 * Real.pi * ∑ e : Link (cube M), (lineageCurrent q i.1 e : ℝ) *
          twistedLinkField ((-(ξ : ℝ) / (N : ℝ)) • t) e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [lineageJ_apply]
      ring
    rw [hsum] at hn
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    have hx : 2 * Real.pi * (-(θ (lineageJ q i.1)) / (2 * Real.pi) + (n : ℝ)) =
        -(θ (lineageJ q i.1)) + 2 * Real.pi * (n : ℝ) := by
      field_simp
    exact mul_left_cancel₀ h2pi (by rw [hx]; linarith)
  · -- the error budget
    have hsubsum : ∀ f : {h : ExpansionLineage (cube M) // h ∈ s} → ℝ,
        ∑ i ∈ Finset.univ.filter (fun i : {h : ExpansionLineage (cube M) // h ∈ s} =>
          currentDivergence (lineageJ q i.1) = 0), f i =
        ∑ i : {i : {h : ExpansionLineage (cube M) // h ∈ s} //
          currentDivergence (lineageJ q i.1) = 0}, f i.1 := fun f =>
      Finset.sum_subtype _ (fun i => by simp) f
    rw [hsubsum]
    have hbudget := error_budget_le hβ (modelInc Q)
      (fun p => (ξ : ℝ) / (N : ℝ) *
        loopFieldResidual (sourceLatticeComplex (B := cube M)) (cubeSheet L T M) p.1)
      (fun i : {i : {h : ExpansionLineage (cube M) // h ∈ s} //
          currentDivergence (lineageJ q i.1) = 0} =>
        lineageCoefficient q z i.1.1 *
          attenuation β (modelInc Q) (lineageCurrent q i.1.1) (selShift q i.1.1))
      (fun i => hz0 i.1) (fun i => selShift q i.1.1)
      (fun i => -(θ (lineageJ q i.1.1)) / (2 * Real.pi))
      (fun i => 6 * (selLinks q i.1.1).card)
      (fun i p => abs_plaqShift_le_one Q _ _ (selLinks_within q i.1.1) p)
      (fun p i j hij => H.plaq Q p i.1 j.1 fun h => hij (Subtype.ext h))
      (fun i => card_plaqShift_ne_zero_le Q _ _)
      (7 * Real.exp (-a)) (by positivity)
      (fun i => (mul_le_mul_of_nonneg_right (hzle i.1) (by positivity)).trans
        (H.envelope_mul_le hN (by linarith) i.1))
    have hres := sum_sq_residual_le (N := N) (ξ := ξ) hM Q
    have hphase : ∑ i : {i : {h : ExpansionLineage (cube M) // h ∈ s} //
          currentDivergence (lineageJ q i.1) = 0},
        lineageCoefficient q z i.1.1 *
          attenuation β (modelInc Q) (lineageCurrent q i.1.1) (selShift q i.1.1) *
          (2 * Real.pi * (-(θ (lineageJ q i.1.1)) / (2 * Real.pi))) ^ 2 ≤
        znPackingCoefficient a N * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T) := by
      refine le_trans ?_ hθsum
      rw [Finset.sum_image (fun i _ j _ h => H.lineageJ_injective h),
        hsubsum (fun i => Real.exp (-(a * (currentL1Norm (lineageJ q i.1) / (N : ℝ) +
          currentLength (lineageJ q i.1)))) * θ (lineageJ q i.1) ^ 2)]
      refine Finset.sum_le_sum fun i _ => ?_
      have hsq : (2 * Real.pi * (-(θ (lineageJ q i.1.1)) / (2 * Real.pi))) ^ 2 =
          θ (lineageJ q i.1.1) ^ 2 := by
        field_simp
      rw [hsq]
      exact mul_le_mul_of_nonneg_right (hzle i.1) (sq_nonneg _)
    have hc₁ : 0 ≤ 6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2 := by
      have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      positivity
    have hsumnn : 0 ≤ ∑ p : {p : SourceDualTwoCells (cube M) // p ∈ Q},
        (2 * Real.pi * ((ξ : ℝ) / (N : ℝ) *
          loopFieldResidual (sourceLatticeComplex (B := cube M)) (cubeSheet L T M) p.1)) ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hZ0 : 0 ≤ (6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2) *
        (7 * Real.exp (-a)) := by positivity
    have e1 := mul_le_mul_of_nonneg_left hres hZ0
    have e2 := mul_le_mul_of_nonneg_left hres (by positivity : (0 : ℝ) ≤ β / 2)
    unfold znStateError
    rw [← haeq]
    nlinarith [hbudget, hphase, e1, e2]

end

end FroehlichSpencer.FS82.ZN

end
