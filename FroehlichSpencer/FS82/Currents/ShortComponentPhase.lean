/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
public import FroehlichSpencer.FS82.Currents.ComponentPackingFamily
public import FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
public import FroehlichSpencer.FS82.Currents.LongCurrentEstimate

/-!
# FS82 ShortComponentPhase: the ShortPhase phase bound on every short incidence component

For a co-closed integer current `j`, a link field `τ` on `Λ*` and a short incidence component
`c` of `j`, this module assembles the premises of ShortPhase's `short_current_phase_bound`:

* the zero-extended primal one-form `sourcePrimalOneForm τ` vanishes on the exterior shell;
* the component has a lower corner `lo` and lies in the source cube of side `2 L`;
* the component is `SourceCurrentConnected` (PackingFamily) and co-closed;
* the source phase of the component is `2π` times the chain pairing of the one-form with the
  C2-twisted lattice chain.

The result is `component_sourcePhase_le`.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Currents.ShortComponentPhase

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.ComponentPacking
open FroehlichSpencer.FS82.Currents.PackingFamily
open FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Moment.SourceCoercivity

noncomputable section

variable {B : Box 4}

/-! ### The zero-extended one-form -/

/-- The zero-extended one-form vanishes on every cell that is not a `Λ*` link. -/
theorem sourcePrimalOneForm_eq_zero (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (c : Cell 4 (bumpedBox B)) (hc : ∀ e : Link B, c ≠ lambdaCellToBumpedBox e.1) :
    sourcePrimalOneForm τ c = 0 := by
  unfold sourcePrimalOneForm
  apply Cubical.lambdaStarRealZeroExtension_vanishes_outside
  rintro ⟨e, he⟩
  rw [← bumpedCellEmbedding_lambdaCellToBumpedBox e] at he
  exact hc e ((boxCellEmbedding (fun _ : Fin 4 => 0)).injective he).symm

/-- The zero-extended one-form vanishes on the exterior shell of the bumped box. -/
theorem sourcePrimalOneForm_shell (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (c : Cell 4 (bumpedBox B)) (h : ∃ i, sourceExteriorCellCoord c i) :
    sourcePrimalOneForm τ c = 0 := by
  apply sourcePrimalOneForm_eq_zero
  rintro e rfl
  obtain ⟨i, hi⟩ := h
  unfold sourceExteriorCellCoord lambdaCellToBumpedBox at hi
  cases hei : e.1 i with
  | inl v =>
    rw [hei] at hi
    rcases hi with hi | hi
    · have := congrArg Fin.val (Sum.inl.inj hi)
      simp at this
    · have := congrArg Fin.val (Sum.inl.inj hi)
      simp only [sourceUpperBoundaryAnchorValue] at this
      have hv := v.isLt
      omega
  | inr t =>
    rw [hei] at hi
    rcases hi with hi | hi <;> cases hi

/-! ### The local curvature -/

theorem chainPairing_basisChain_sub (α : Cell 4 (bumpedBox B) → ℝ)
    (u l : Cell 4 (bumpedBox B)) :
    chainPairing α (basisChain u - basisChain l) = α u - α l := by
  classical
  have hu : chainPairing α (basisChain u) = α u := by
    unfold chainPairing basisChain
    rw [Finset.sum_eq_single u]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · intro h
      exact (h (Finset.mem_univ u)).elim
  have hl : chainPairing α (basisChain l) = α l := by
    unfold chainPairing basisChain
    rw [Finset.sum_eq_single l]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · intro h
      exact (h (Finset.mem_univ l)).elim
  have hneg : basisChain u - basisChain l = basisChain u + (-1 : ℤ) • basisChain l := by
    simp [sub_eq_add_neg]
  rw [hneg, chainPairing_add, chainPairing_smul, hu, hl]
  push_cast
  ring

/-- The local curvature at a cell is the signed sum of the one-form over the faces. -/
theorem chainCoboundary_eq_sum_faces (α : Cell 4 (bumpedBox B) → ℝ)
    (p : Cell 4 (bumpedBox B)) :
    chainCoboundary α p =
      ∑ i : Fin 4, match p i with
        | Sum.inl _ => 0
        | Sum.inr e =>
            ((-1 : ℤ) ^ cellRankBefore p i : ℤ) *
              (α (upperFace p i e) - α (lowerFace p i e)) := by
  unfold chainCoboundary boundaryBasis
  rw [chainPairing_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases p i with
  | inl v => simp [chainPairing]
  | inr e =>
    simp only
    rw [chainPairing_smul, chainPairing_basisChain_sub]

/-- The local curvature of the zero-extended one-form vanishes on every plaquette outside the
image of the dual plaquettes. -/
theorem chainCoboundary_sourcePrimalOneForm_eq_zero
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (p : SourcePlaquette B)
    (hp : ¬sourcePlaquetteInDualImage p) :
    chainCoboundary (sourcePrimalOneForm τ) p.1 = 0 := by
  have hface : ∀ (i : Fin 4) (e : Fin ((bumpedBox B) i)), p.1 i = Sum.inr e →
      ∀ c : Cell 4 (bumpedBox B), (∀ j, j ≠ i → c j = p.1 j) →
        sourcePrimalOneForm τ c = 0 := by
    intro i e hpi c hc
    apply sourcePrimalOneForm_eq_zero
    rintro f rfl
    apply hp
    intro j
    cases hpj : p.1 j with
    | inr t => trivial
    | inl v =>
      have hji : j ≠ i := by
        rintro rfl
        rw [hpi] at hpj
        cases hpj
      have hcj := hc j hji
      rw [hpj] at hcj
      unfold lambdaCellToBumpedBox at hcj
      cases hfj : f.1 j with
      | inl w =>
        rw [hfj] at hcj
        have hval := congrArg Fin.val (Sum.inl.inj hcj)
        simp only at hval
        have hw := w.isLt
        constructor <;> omega
      | inr t =>
        rw [hfj] at hcj
        cases hcj
  rw [chainCoboundary_eq_sum_faces]
  refine Finset.sum_eq_zero fun i _ => ?_
  cases hpi : p.1 i with
  | inl v => rfl
  | inr e =>
    simp only
    rw [hface i e hpi (upperFace p.1 i e) (fun j hj => upperFace_apply_of_ne p.1 i j e hj),
      hface i e hpi (lowerFace p.1 i e) (fun j hj => lowerFace_apply_of_ne p.1 i j e hj)]
    simp

theorem dualCellOrientationSign_two_sq (f : SourceDualTwoCells B) :
    dualCellOrientationSign f.1 ^ 2 = 1 := by
  unfold dualCellOrientationSign axisSetOrientationSign
  rw [pow_two, ← mul_pow]
  norm_num

/-- The square of the local curvature is the square of the Gaussian source differential,
extended by zero to all plaquettes of the bumped box. -/
theorem chainCoboundary_sq_eq_dualField_sq
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (p : SourcePlaquette B) :
    (chainCoboundary (sourcePrimalOneForm τ) p.1) ^ 2 =
      (sourceDualFieldOnPlaquettes
        (fun f => (latticeExactOneComplex (B := B) originZero).d₁ τ f) p) ^ 2 := by
  by_cases hp : sourcePlaquetteInDualImage p
  · obtain ⟨q, rfl⟩ := (sourcePlaquetteInDualImage_iff_exists p).mp hp
    rw [sourceDualFieldOnPlaquettes_eq]
    change (chainCoboundary (sourcePrimalOneForm τ) (lambdaCellToBumpedBox q.1)) ^ 2 = _
    rw [chainCoboundary_sourcePrimalOneForm_signed, mul_pow, dualCellOrientationSign_two_sq,
      one_mul]
  · rw [chainCoboundary_sourcePrimalOneForm_eq_zero τ p hp]
    unfold sourceDualFieldOnPlaquettes
    simp [hp]

/-- The total energy of the local curvature is the energy of `d₁ τ`. -/
theorem sum_chainCoboundary_sq (τ : EuclideanSpace ℝ (SourceDualOneCells B)) :
    (∑ p : SourcePlaquette B, (chainCoboundary (sourcePrimalOneForm τ) p.1) ^ 2) =
      ∑ f : SourceDualTwoCells B,
        ((latticeExactOneComplex (B := B) originZero).d₁ τ f) ^ 2 := by
  rw [← sourceDualFieldOnPlaquettes_energy
    (fun f => (latticeExactOneComplex (B := B) originZero).d₁ τ f)]
  exact Finset.sum_congr rfl fun p _ => chainCoboundary_sq_eq_dualField_sq τ p

/-! ### The source phase as a chain pairing -/

/-- The link field `e ↦ sign(e) τ_e`: the C2 twist of `τ`, as a function on links. -/
def twistedLinkField (τ : EuclideanSpace ℝ (SourceDualOneCells B)) : Link B → ℝ :=
  fun e => dualCellOrientationSign e.1 * τ e

theorem sourceCurrentOrientationSign_cast (e : Link B) :
    ((sourceCurrentOrientationSign e : ℤ) : ℝ) = dualCellOrientationSign e.1 := by
  simp [sourceCurrentOrientationSign, sourceDualT, dualAxisSum, dualCellOrientationSign,
    axisSetOrientationSign, Int.cast_pow]

theorem sourceCurrentLatticeChain_support (q : IntegerCurrent B) :
    (sourceCurrentLatticeChain q).support = q.support.map lambdaStarCellEmbedding := by
  classical
  rw [sourceCurrentLatticeChain, sourceCurrentChain, Finsupp.support_embDomain,
    sourceCurrentOrientationTwist_support]

/-- The pairing of the zero-extended one-form with the C2-twisted lattice chain of a current. -/
theorem chainPairing_sourceCurrentLatticeChain
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (q : IntegerCurrent B) :
    chainPairing (sourcePrimalOneForm τ) (sourceCurrentLatticeChain q) =
      ∑ e : Link B, twistedLinkField τ e * (q e : ℝ) := by
  classical
  rw [chainPairing_eq_support_sum, sourceCurrentLatticeChain_support, Finset.sum_map]
  have hterm : ∀ e : Link B,
      sourcePrimalOneForm τ (lambdaStarCellEmbedding e) *
          ((sourceCurrentLatticeChain q (lambdaStarCellEmbedding e) : ℤ) : ℝ) =
        twistedLinkField τ e * (q e : ℝ) := by
    intro e
    change sourcePrimalOneForm τ (lambdaCellToBumpedBox e.1) *
      ((sourceCurrentLatticeChain q (lambdaCellToBumpedBox e.1) : ℤ) : ℝ) = _
    rw [sourcePrimalOneForm_link, sourceCurrentLatticeChain_apply]
    push_cast
    rw [sourceCurrentOrientationSign_cast]
    unfold twistedLinkField
    ring
  rw [Finset.sum_congr rfl fun e _ => hterm e]
  refine Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_
  simp [Finsupp.notMem_support_iff.mp he]

/-- The source phase of a current against the twisted field is `2π` times the chain pairing. -/
theorem sourceCurrentPhase_twistedLinkField
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (q : IntegerCurrent B) :
    sourceCurrentPhase (twistedLinkField τ) q =
      (2 * Real.pi) * chainPairing (sourcePrimalOneForm τ) (sourceCurrentLatticeChain q) := by
  rw [chainPairing_sourceCurrentLatticeChain, Finset.mul_sum]
  unfold sourceCurrentPhase
  exact Finset.sum_congr rfl fun e _ => by ring

theorem sourcePhysicalCurrentVector_apply_r3c (j : IntegerCurrent B)
    (e : SourceDualOneCells B) :
    sourcePhysicalCurrentVector j e = (2 * Real.pi) * (j e : ℝ) := by
  simp only [sourcePhysicalCurrentVector, finsuppToEuclidean_apply,
    compressDualSubtype_apply, physicalCurrent]
  change Finsupp.embDomain
      (⟨Subtype.val, Subtype.val_injective⟩ : Link B ↪ Cubical.DualCell 4 B)
      _ ((⟨Subtype.val, Subtype.val_injective⟩ :
        Link B ↪ Cubical.DualCell 4 B) e) = _
  rw [Finsupp.embDomain_apply_self]
  simp

/-- The C2-oriented physical phase `⟨T(2πj), τ⟩` is the source phase against the twisted field. -/
theorem inner_sourceDualTLinear_physicalCurrent
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) (j : IntegerCurrent B) :
    inner ℝ (sourceDualTLinear (sourcePhysicalCurrentVector j)) τ =
      sourceCurrentPhase (twistedLinkField τ) j := by
  rw [PiLp.inner_apply]
  unfold sourceCurrentPhase twistedLinkField
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sourceDualTLinear_apply, sourcePhysicalCurrentVector_apply_r3c]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-! ### Energy, length and mass -/

theorem currentEnergy_eq_integerCurrentNormSq (j : IntegerCurrent B) :
    currentEnergy j = integerCurrentNormSq (fun e : Link B => j e) := by
  unfold currentEnergy integerCurrentNormSq
  refine Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_
  simp [Finsupp.notMem_support_iff.mp he]

theorem currentSupport_eq_support (j : IntegerCurrent B) :
    currentSupport (fun e : Link B => j e) = j.support := by
  ext e
  simp [currentSupport, Finsupp.mem_support_iff]

theorem currentLength_eq_currentSupport_card (j : IntegerCurrent B) :
    currentLength j = ((currentSupport (fun e : Link B => j e)).card : ℝ) := by
  rw [currentSupport_eq_support]
  rfl

/-- The coefficient mass of the twisted lattice chain is at most the current energy. -/
theorem chainL1_sourceCurrentLatticeChain_le_energy (q : IntegerCurrent B) :
    (chainL1 (sourceCurrentLatticeChain q) : ℝ) ≤ currentEnergy q := by
  classical
  unfold chainL1 currentEnergy
  rw [sourceCurrentLatticeChain_support, Finset.sum_map]
  push_cast
  refine Finset.sum_le_sum fun e _ => ?_
  change (((sourceCurrentLatticeChain q (lambdaCellToBumpedBox e.1)).natAbs : ℕ) : ℝ) ≤ _
  rw [sourceCurrentLatticeChain_apply, Int.natAbs_mul]
  have hs : (sourceCurrentOrientationSign e).natAbs = 1 := by
    change (sourceDualT e).natAbs = 1
    rcases sourceDualT_is_pm_one e with h | h <;> simp [h]
  rw [hs, one_mul]
  have h := Int.natAbs_le_self_sq (q e)
  have h' : (((q e).natAbs : ℤ) : ℝ) ≤ (((q e) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
  simpa using h'

/-! ### Localization of a component -/

/-- Two links of one incidence component have base points at coordinate distance at most the
size of the component. -/
theorem component_base_gap (j : IntegerCurrent B) (c : CurrentComponentClass j)
    {e f : Link B} (he : e ∈ currentComponentSupport j c)
    (hf : f ∈ currentComponentSupport j c) (k : Fin 4) :
    Int.natAbs (((base e k).val : ℤ) - (base f k).val) ≤
      (currentComponentSupport j c).card := by
  classical
  obtain ⟨p, hp, _⟩ := currentComponent_has_bounded_link_path j c he hf
  have hlt : p.length < (currentComponentSupport j c).card := by
    simpa [componentLinkGraph] using hp.length_lt
  obtain ⟨n, hn, hpath⟩ := SourceVertexPath.of_linkWalk j c (currentComponentCurrent j c)
    (by rw [currentComponentCurrent_support]) (u := ⟨e, he⟩) (v := ⟨f, hf⟩)
    (a := base e) (b := base f) (Or.inl rfl) (Or.inl rfl) p
  have hbound := sourceVertexPath_coordinate_bound (currentComponentCurrent j c) hpath k
  omega

/-- Every incidence component has a lower corner whose source cube of side twice the component
size contains it. -/
theorem exists_component_cube (j : IntegerCurrent B) {c : CurrentComponentClass j}
    (hc : c ∈ currentComponents j) :
    ∃ lo : Fin 4 → ℕ, (∀ i, lo i ≤ B i + 1) ∧
      supportInSourceCube (currentComponentSupport j c) lo
        (2 * (currentComponentSupport j c).card) := by
  classical
  have hne := currentComponentSupport_nonempty j hc
  have hpos : 1 ≤ (currentComponentSupport j c).card := Finset.card_pos.mpr hne
  choose e₀ he₀ hmin using fun k : Fin 4 =>
    Finset.exists_min_image (currentComponentSupport j c) (fun e => (base e k).val) hne
  refine ⟨fun k => (base (e₀ k) k).val, ?_, ?_⟩
  · intro i
    have h := (base (e₀ i) i).isLt
    simp only [bumpedBox] at h
    change (base (e₀ i) i).val ≤ B i + 1
    omega
  · intro k e he
    have hgap := component_base_gap j c he (he₀ k) k
    have hlow := hmin k e he
    change (base (e₀ k) k).val ≤ (base e k).val ∧
      (base e k).val + (if axis e = k then 1 else 0) ≤
        (base (e₀ k) k).val + 2 * (currentComponentSupport j c).card
    refine ⟨hlow, ?_⟩
    split_ifs <;> omega

/-! ### The phase bound on a short component -/

/-- **ShortPhase on a short incidence component.** For a co-closed current, every incidence component
shorter than the box threshold has source phase against the twisted field bounded by
`C L κ E L⁴`, with `C = 50π·10⁴`, `L` the size of the component, `E` its energy and `κ` the
maximum of the local curvature on the plaquettes of its source cube. -/
theorem component_sourcePhase_le (j : IntegerCurrent B) (hdiv : currentDivergence j = 0)
    {c : CurrentComponentClass j} (hc : c ∈ currentComponents j)
    (m : ℕ) (hmin : ∀ i, m ≤ B i) (hshort : (currentComponentSupport j c).card < m)
    (lo : Fin 4 → ℕ) (hlo : ∀ i, lo i ≤ B i + 1)
    (hcube : supportInSourceCube (currentComponentSupport j c) lo
      (2 * (currentComponentSupport j c).card))
    (τ : EuclideanSpace ℝ (SourceDualOneCells B)) :
    |sourceCurrentPhase (twistedLinkField τ) (currentComponentCurrent j c)| ≤
      (50 * Real.pi * 10000) * ((currentComponentSupport j c).card : ℝ) *
        sourceOmegaMax lo (2 * (currentComponentSupport j c).card)
          (fun p => chainCoboundary (sourcePrimalOneForm τ) p.1) *
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
  obtain ⟨ε, μ, -, -, -, -, -, -, -, -, -, -, hbound⟩ :=
    short_current_phase_bound (currentComponentCurrent j c) hco hconn m hmin hL
      (by rw [hqs]; exact hshort) lo hlo (by rw [hqs]; exact hcube)
      (sourcePrimalOneForm τ) (sourcePrimalOneForm_shell τ)
  rw [hqs] at hbound
  rw [sourceCurrentPhase_twistedLinkField]
  have hmass := chainL1_sourceCurrentLatticeChain_le_energy (currentComponentCurrent j c)
  have hκ := sourceOmegaMax_nonneg lo (2 * (currentComponentSupport j c).card)
    (fun p : SourcePlaquette B => chainCoboundary (sourcePrimalOneForm τ) p.1)
  have hLr : (0 : ℝ) ≤ ((currentComponentSupport j c).card : ℝ) := by positivity
  refine hbound.trans ?_
  have hcoef : 0 ≤ (50 * Real.pi * 10000) *
      sourceOmegaMax lo (2 * (currentComponentSupport j c).card)
        (fun p : SourcePlaquette B => chainCoboundary (sourcePrimalOneForm τ) p.1) *
      ((currentComponentSupport j c).card : ℝ) ^ 5 := by
    have hpi := Real.pi_pos
    positivity
  calc (50 * Real.pi * 10000) *
        sourceOmegaMax lo (2 * (currentComponentSupport j c).card)
          (fun p : SourcePlaquette B => chainCoboundary (sourcePrimalOneForm τ) p.1) *
        ((currentComponentSupport j c).card : ℝ) ^ 5 *
        (chainL1 (sourceCurrentLatticeChain (currentComponentCurrent j c)) : ℝ)
      ≤ (50 * Real.pi * 10000) *
        sourceOmegaMax lo (2 * (currentComponentSupport j c).card)
          (fun p : SourcePlaquette B => chainCoboundary (sourcePrimalOneForm τ) p.1) *
        ((currentComponentSupport j c).card : ℝ) ^ 5 *
        currentEnergy (currentComponentCurrent j c) :=
        mul_le_mul_of_nonneg_left hmass hcoef
    _ = _ := by ring

end

end FroehlichSpencer.FS82.Currents.ShortComponentPhase
