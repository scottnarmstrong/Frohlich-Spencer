/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.WiredBoxCarrier
public import FroehlichSpencer.BKT.Bridge.VillainMeasure
public import FroehlichSpencer.BKT.Lattice2D.LogLowerBound
import FroehlichSpencer.BKT.Surface.SquareZeroConnected
public import FroehlichSpencer.BKT.Villain.GraphIsomorphism
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
#  Villain law on the internal wired carrier

The product measure, including its pinned root coordinate, is the pushforward of the
rooted angle-box measure.

The edge product then transports through the wired-carrier
isomorphism (KP (1.4), p. 4; Proposition 6.1, §6.1).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.BKT

namespace Duality

abbrev SourceVertex (L : ℕ) := Option (Fin L × Fin L)

private instance villainSourceBaseCoordinate_isFiniteMeasure (L : ℕ)
    (j : SourceVertex L) : IsFiniteMeasure
      (if j = none then Measure.dirac (0 : ℝ)
       else volume.restrict (Set.Ico (-Real.pi) Real.pi)) := by
  classical
  split_ifs with h
  · subst j
    infer_instance
  · refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top

def sourceFreeIndexEquiv (L : ℕ) :
    Villain.FreeVertices (SourceVertex L) none ≃ (Fin L × Fin L) where
  toFun j := by
    cases j with
    | mk v hv =>
      cases v with
      | none => exact False.elim (hv rfl)
      | some x => exact x
  invFun x := ⟨some x, by simp⟩
  left_inv j := by
    apply Subtype.ext
    cases j with
    | mk v hv =>
      cases v with
      | none => exact False.elim (hv rfl)
      | some x => rfl
  right_inv _ := rfl

def sourceFreeAngleEquiv (L : ℕ) :
    Villain.FreeAngles (SourceVertex L) none ≃ᵐ ((Fin L × Fin L) → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin L × Fin L => ℝ)
    (sourceFreeIndexEquiv L)

def sourcePinnedAngle (L : ℕ)
    (θ : Villain.FreeAngles (SourceVertex L) none) : SourceVertex L → ℝ :=
  Villain.pinnedAngle none θ

private theorem coe_sourcePiOption {α : Type*}
    (β : Option α → Type*) [∀ i, MeasurableSpace (β i)] :
    ⇑(MeasurableEquiv.piOptionEquivProd β) =
      fun f => (fun i => f (some i), f none) := by
  funext f
  apply Prod.ext
  · funext i
    rfl
  · rfl

@[simp] theorem sourceFreeAngleEquiv_apply (L : ℕ)
    (θ : Villain.FreeAngles (SourceVertex L) none) (x : Fin L × Fin L) :
    sourceFreeAngleEquiv L θ x = θ ((sourceFreeIndexEquiv L).symm x) := by
  simp [sourceFreeAngleEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply]

theorem sourcePinnedAngle_eq_piOption (L : ℕ)
    (θ : Villain.FreeAngles (SourceVertex L) none) :
    sourcePinnedAngle L θ =
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin L × Fin L) => ℝ)).symm
        (sourceFreeAngleEquiv L θ, 0) := by
  let M := MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin L × Fin L) => ℝ)
  have hM : M (sourcePinnedAngle L θ) = (sourceFreeAngleEquiv L θ, 0) := by
    rw [coe_sourcePiOption]
    apply Prod.ext
    · funext x
      simp [sourcePinnedAngle, sourceFreeAngleEquiv_apply,
        Villain.pinnedAngle, sourceFreeIndexEquiv]
    · simp [sourcePinnedAngle]
  calc
    sourcePinnedAngle L θ = M.symm (M (sourcePinnedAngle L θ)) := by simp
    _ = M.symm (sourceFreeAngleEquiv L θ, 0) := congrArg M.symm hM

theorem sourcePinnedAngle_measurable (L : ℕ) :
    Measurable (sourcePinnedAngle L) := by
  have hfun : sourcePinnedAngle L =
      (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin L × Fin L) => ℝ)).symm ∘
        fun θ => (sourceFreeAngleEquiv L θ, (0 : ℝ)) := by
    funext θ
    exact sourcePinnedAngle_eq_piOption L θ
  rw [hfun]
  exact (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin L × Fin L) => ℝ)).symm.measurable.comp
      (Measurable.prodMk (sourceFreeAngleEquiv L).measurable measurable_const)

/--
Extending a free  angle by the root value zero pushes the rooted product measure to
the root-Dirac product measure.
-/
theorem villainBaseMeasure_map_sourcePinnedAngle (L : ℕ) :
    Measure.map (sourcePinnedAngle L) (Villain.rootedAngleMeasure none) =
      villainBaseMeasure L := by
  classical
  let e := sourceFreeIndexEquiv L
  let A := sourceFreeAngleEquiv L
  let μ := Villain.rootedAngleMeasure (V := SourceVertex L) none
  have hA : Measure.map A μ =
      Measure.pi (fun _ : Fin L × Fin L => volume.restrict
        (Set.Ico (-Real.pi) Real.pi)) := by
    change Measure.map (⇑(MeasurableEquiv.piCongrLeft
      (fun _ : Fin L × Fin L => ℝ) e))
        (Measure.pi fun _ : Villain.FreeVertices (SourceVertex L) none =>
          volume.restrict (Set.Ico (-Real.pi) Real.pi)) = _
    exact (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Fin L × Fin L =>
        volume.restrict (Set.Ico (-Real.pi) Real.pi)) e).map_eq
  have hpair : Measure.map (fun θ => (A θ, (0 : ℝ))) μ =
      (Measure.pi (fun _ : Fin L × Fin L => volume.restrict
        (Set.Ico (-Real.pi) Real.pi))).prod (Measure.dirac 0) := by
    rw [Measure.prod_dirac, ← hA]
    change Measure.map (fun θ => (A θ, (0 : ℝ))) μ =
      Measure.map (fun x => (x, (0 : ℝ))) (Measure.map A μ)
    rw [Measure.map_map measurable_prodMk_right A.measurable]
    exact congrArg (fun f => Measure.map f μ) (by funext θ; rfl)
  let M := MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin L × Fin L) => ℝ)
  have hfun : sourcePinnedAngle L = M.symm ∘ (fun θ => (A θ, (0 : ℝ))) := by
    funext θ
    exact sourcePinnedAngle_eq_piOption L θ
  rw [hfun, ← Measure.map_map M.symm.measurable
    (Measurable.prodMk A.measurable measurable_const), hpair]
  unfold villainBaseMeasure
  exact Measure.pi_map_piOptionEquivProd
    (fun j : Option (Fin L × Fin L) =>
      if j = none then Measure.dirac (0 : ℝ)
      else volume.restrict (Set.Ico (-Real.pi) Real.pi))

private theorem villainDensity_eq_sourceRealDensity (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (θ : Villain.FreeAngles (SourceVertex L) none) :
    villainDensity L β (sourcePinnedAngle L θ) =
      ENNReal.ofReal (Villain.villainRealDensity (squareZero L) none β θ) := by
  rw [villainDensity_eq_weight_prod L β hβ]
  unfold Villain.villainRealDensity
  rw [ENNReal.ofReal_prod_of_nonneg]
  · rfl
  · intro e he
    exact (VillainWeight.villainWeight_pos hβ _).le

/--
The edge product is the internal real density after the carrier isomorphism and
root pinning.
-/
theorem villainDensity_eq_wiredBoxDensity (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (θ : Villain.FreeAngles (SourceVertex L) none) :
    villainDensity L β (sourcePinnedAngle L θ) =
      ENNReal.ofReal (Villain.villainRealDensity (wiredBoxGraph L) none β θ) := by
  rw [villainDensity_eq_sourceRealDensity L β hβ θ]
  have hangle : Villain.rootedAngleIso (FroehlichSpencer.BKT.Duality.squareZeroWiredBoxGraphIsomorphism L)
      none none rfl θ = θ := by
    ext j
    rfl
  rw [← Villain.villainRealDensity_rootedAngleIso
      (FroehlichSpencer.BKT.Duality.squareZeroWiredBoxGraphIsomorphism L)
      none none rfl β θ, hangle]

/--
The unnormalized  Villain measure is the pushforward of the rooted measure on the
 carrier.
-/
theorem villainDensityMeasure_map_sourcePinnedAngle (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    Measure.map (sourcePinnedAngle L) (Villain.rootedVillainDensityMeasure
      (wiredBoxGraph L) none β) = villainDensityMeasure L β := by
  classical
  let pin := sourcePinnedAngle L
  let μ := Villain.rootedAngleMeasure (V := SourceVertex L) none
  let ν := villainBaseMeasure L
  let ρ : Villain.FreeAngles (SourceVertex L) none → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (Villain.villainRealDensity (wiredBoxGraph L) none β θ)
  let σ : (VillainVertex L → ℝ) → ℝ≥0∞ := fun θ => villainDensity L β θ
  have hμ : MeasurePreserving pin μ ν :=
    ⟨sourcePinnedAngle_measurable L, villainBaseMeasure_map_sourcePinnedAngle L⟩
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact ENNReal.measurable_ofReal.comp
      (Villain.continuous_villainRealDensity (wiredBoxGraph L) none β hβ).measurable
  have hσ : Measurable σ := by
    dsimp [σ]
    rw [show (fun θ : VillainVertex L → ℝ => villainDensity L β θ) =
        fun θ => ∏ e : VillainEdge L, ENNReal.ofReal
          (villainWeight β (θ ((squareZero L).src e) - θ ((squareZero L).tgt e)) ) from by
          funext θ
          exact villainDensity_eq_weight_prod L β hβ θ]
    apply Finset.measurable_prod
    intro e he
    apply ENNReal.measurable_ofReal.comp
    exact (Villain.continuous_villainWeight β hβ).measurable.comp
      ((measurable_pi_apply ((squareZero L).src e)).sub
        (measurable_pi_apply ((squareZero L).tgt e)))
  have hinv (θ : Villain.FreeAngles (SourceVertex L) none) : σ (pin θ) = ρ θ := by
    exact villainDensity_eq_wiredBoxDensity L β hβ θ
  change Measure.map pin (μ.withDensity ρ) = ν.withDensity σ
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hμ.measurable hs,
    MeasureTheory.withDensity_apply σ hs,
    MeasureTheory.withDensity_apply ρ (hs.preimage hμ.measurable)]
  calc
    (∫⁻ θ in pin ⁻¹' s, ρ θ ∂μ) =
        ∫⁻ θ, (pin ⁻¹' s).indicator ρ θ ∂μ :=
      (MeasureTheory.lintegral_indicator (hs.preimage hμ.measurable) ρ).symm
    _ = ∫⁻ θ, s.indicator σ (pin θ) ∂μ := by
      congr 1
      funext θ
      by_cases hθ : pin θ ∈ s <;> simp [Set.indicator, hθ, hinv θ]
    _ = ∫⁻ θ, s.indicator σ θ ∂ν := hμ.lintegral_comp (hσ.indicator hs)
    _ = ∫⁻ θ in s, σ θ ∂ν := MeasureTheory.lintegral_indicator hs σ

/--
The Villain law is the pushforward of the rooted Villain measure on the
carrier (KP (1.4), p. 4).
-/
theorem villainLaw_map_sourcePinnedAngle (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    Measure.map (sourcePinnedAngle L)
        (Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ) = villainLaw L β hβ := by
  have hmap := villainDensityMeasure_map_sourcePinnedAngle L β hβ
  have hm := congrArg (fun μ : Measure (SourceVertex L → ℝ) => μ Set.univ)
    hmap
  have hmass : Villain.rootedVillainDensityMeasure (wiredBoxGraph L) none β Set.univ =
      villainDensityMeasure L β Set.univ := by
    simpa [Measure.map_apply (sourcePinnedAngle_measurable L) MeasurableSet.univ] using hm
  have hZ : ENNReal.ofReal
      (Villain.villainPartitionFunction (wiredBoxGraph L) none β) =
      villainDensityMeasure L β Set.univ := by
    rw [← Villain.rootedVillainDensityMeasure_mass (wiredBoxGraph L) none β hβ]
    exact hmass
  rw [Villain.rootedVillainMeasure,
    Measure.map_smul (ENNReal.ofReal
      (Villain.villainPartitionFunction (wiredBoxGraph L) none β))⁻¹
      (sourcePinnedAngle_measurable L).aemeasurable,
    hmap, villainLaw_eq_normalizedDensityMeasure L β hβ, hZ]

/--
The cosine integral equals the internal rooted Villain expectation at the
corresponding free site.
-/
theorem villainLaw_cosIntegral_eq_villainCosExpectation (L : ℕ) (β : ℝ)
    (hβ : 0 < β) (x : Fin L × Fin L) :
    (∫ θ, Real.cos (θ (some x)) ∂villainLaw L β hβ) =
      Villain.villainCosExpectation (wiredBoxGraph L) none β
        ⟨some x, Option.some_ne_none _⟩ := by
  let pin := sourcePinnedAngle L
  let site : Villain.FreeVertices (SourceVertex L) none :=
    ⟨some x, Option.some_ne_none _⟩
  have hcont : Continuous (fun θ : SourceVertex L → ℝ => Real.cos (θ (some x))) := by
    fun_prop
  calc
    (∫ θ, Real.cos (θ (some x)) ∂villainLaw L β hβ) =
        ∫ θ, Real.cos ((pin θ) (some x))
          ∂Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ := by
            rw [← villainLaw_map_sourcePinnedAngle L β hβ]
            exact (MeasureTheory.integral_map
              (sourcePinnedAngle_measurable L).aemeasurable
              hcont.aestronglyMeasurable)
    _ = Villain.villainCosExpectation (wiredBoxGraph L) none β site := by
      have hpin (θ : Villain.FreeAngles (WiredVertex L) none) :
          pin θ (some x) = θ site := by
        simp [pin, site, sourcePinnedAngle, Villain.pinnedAngle]
      rw [show (fun θ : Villain.FreeAngles (WiredVertex L) none =>
          Real.cos (pin θ (some x))) = fun θ => Real.cos (θ site) from by
            funext θ
            rw [hpin]]
      exact Villain.rootedVillainMeasure_cosIntegral_eq_villainCosExpectation
        (wiredBoxGraph L) none β hβ site
    _ = Villain.villainCosExpectation (wiredBoxGraph L) none β
          ⟨some x, Option.some_ne_none _⟩ := rfl

/-- A free-square edge crossed into the dual wired box retains the same endpoint pair, up to
orientation. -/
theorem crossInternalFreeEdge_endpoints (L : ℕ) (e : Lattice2D.SquareFreeEdge L) :
    ((wiredBoxGraph L).src (crossInternalFreeEdge L e) =
        some ((Lattice2D.squareFreeGraph L).src e) ∧
      (wiredBoxGraph L).tgt (crossInternalFreeEdge L e) =
        some ((Lattice2D.squareFreeGraph L).tgt e)) ∨
    ((wiredBoxGraph L).src (crossInternalFreeEdge L e) =
        some ((Lattice2D.squareFreeGraph L).tgt e) ∧
      (wiredBoxGraph L).tgt (crossInternalFreeEdge L e) =
        some ((Lattice2D.squareFreeGraph L).src e)) := by
  cases e with
  | inl e =>
      left
      have hi : e.1.1.val + 1 < L := e.1.2
      simp [crossInternalFreeEdge, wiredBoxFinSuccCast, wiredBoxGraph,
        wiredBoxSrc, wiredBoxTgt, verticalPrimalSrc, verticalPrimalTgt,
        verticalFaceY, verticalDualEdge, verticalDualEdgeData,
        Lattice2D.squareFreeGraph, hi]
  | inr e =>
      right
      have hj : e.2.1.val + 1 < L := e.2.2
      simp [crossInternalFreeEdge, wiredBoxFinSuccCast, wiredBoxGraph,
        wiredBoxSrc, wiredBoxTgt, horizontalPrimalSrc, horizontalPrimalTgt,
        horizontalFaceX, horizontalDualEdge, horizontalDualEdgeData,
        Lattice2D.squareFreeGraph, hj]

/-- Embed the free square as the free vertices of the wired graph. -/
private theorem wiredFreeAdj_of_freeAdj (L : ℕ) (p q : Lattice2D.SquareFreeVertex L)
    (h : (Lattice2D.squareFreeGraph L).Adj p q) :
    (wiredBoxGraph L).Adj (some p) (some q) := by
  rcases h with ⟨e, h | h⟩
  · rcases crossInternalFreeEdge_endpoints L e with he | he
    · exact ⟨crossInternalFreeEdge L e, Or.inl
        ⟨he.1.trans (congrArg some h.1), he.2.trans (congrArg some h.2)⟩⟩
    · exact ⟨crossInternalFreeEdge L e, Or.inr
        ⟨he.1.trans (congrArg some h.2), he.2.trans (congrArg some h.1)⟩⟩
  · rcases crossInternalFreeEdge_endpoints L e with he | he
    · exact ⟨crossInternalFreeEdge L e, Or.inr
        ⟨he.1.trans (congrArg some h.1), he.2.trans (congrArg some h.2)⟩⟩
    · exact ⟨crossInternalFreeEdge L e, Or.inl
        ⟨he.1.trans (congrArg some h.2), he.2.trans (congrArg some h.1)⟩⟩

def wiredFreeGraphHom (L : ℕ) :
    (Lattice2D.squareFreeGraph L).toSimpleGraph →g (wiredBoxGraph L).toSimpleGraph where
  toFun := some
  map_rel' := by
    intro p q hpq
    change (SimpleGraph.fromRel (Lattice2D.squareFreeGraph L).Adj).Adj p q at hpq
    rcases (SimpleGraph.fromRel_adj _ _ _).mp hpq with ⟨hpqne, hAdj | hAdj⟩
    · have hwired := wiredFreeAdj_of_freeAdj L p q hAdj
      change (SimpleGraph.fromRel (wiredBoxGraph L).Adj).Adj (some p) (some q)
      exact ⟨fun h => hpqne (Option.some.inj h), Or.inl hwired⟩
    · have hwired := wiredFreeAdj_of_freeAdj L q p hAdj
      change (SimpleGraph.fromRel (wiredBoxGraph L).Adj).Adj (some p) (some q)
      exact ⟨fun h => hpqne (Option.some.inj h), Or.inr hwired⟩

private theorem wiredBoundaryDepth_unitStep {L : ℕ} {p q : Fin L × Fin L}
    (hx : p.1.val ≤ q.1.val + 1 ∧ q.1.val ≤ p.1.val + 1)
    (hy : p.2.val ≤ q.2.val + 1 ∧ q.2.val ≤ p.2.val + 1) :
    wiredBoundaryDepth L p ≤ wiredBoundaryDepth L q + 1 ∧
      wiredBoundaryDepth L q ≤ wiredBoundaryDepth L p + 1 := by
  constructor
  · rcases wiredBoundaryDepth_eq_one_side L q with h | h | h | h
    · calc
        wiredBoundaryDepth L p ≤ p.1.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_left _ _).trans (Nat.min_le_left _ _)
        _ ≤ q.1.val + 1 := hx.1
        _ = wiredBoundaryDepth L q + 1 := by omega
    · calc
        wiredBoundaryDepth L p ≤ p.2.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_left _ _).trans (Nat.min_le_right _ _)
        _ ≤ q.2.val + 1 := hy.1
        _ = wiredBoundaryDepth L q + 1 := by omega
    · calc
        wiredBoundaryDepth L p ≤ L - 1 - p.1.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
        _ ≤ L - 1 - q.1.val + 1 := by omega
        _ = wiredBoundaryDepth L q + 1 := by omega
    · calc
        wiredBoundaryDepth L p ≤ L - 1 - p.2.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
        _ ≤ L - 1 - q.2.val + 1 := by omega
        _ = wiredBoundaryDepth L q + 1 := by omega
  · rcases wiredBoundaryDepth_eq_one_side L p with h | h | h | h
    · calc
        wiredBoundaryDepth L q ≤ q.1.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_left _ _).trans (Nat.min_le_left _ _)
        _ ≤ p.1.val + 1 := hx.2
        _ = wiredBoundaryDepth L p + 1 := by omega
    · calc
        wiredBoundaryDepth L q ≤ q.2.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_left _ _).trans (Nat.min_le_right _ _)
        _ ≤ p.2.val + 1 := hy.2
        _ = wiredBoundaryDepth L p + 1 := by omega
    · calc
        wiredBoundaryDepth L q ≤ L - 1 - q.1.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
        _ ≤ L - 1 - p.1.val + 1 := by omega
        _ = wiredBoundaryDepth L p + 1 := by omega
    · calc
        wiredBoundaryDepth L q ≤ L - 1 - q.2.val := by
          unfold wiredBoundaryDepth
          exact (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
        _ ≤ L - 1 - p.2.val + 1 := by omega
        _ = wiredBoundaryDepth L p + 1 := by omega

private def wiredBoxHeight (L : ℕ) : WiredVertex L → ℕ
  | none => 0
  | some p => wiredBoundaryDepth L p + 1

private theorem wiredBoxEdge_height_step (L : ℕ) (hL : 1 < L) (e : WiredEdge L) :
    wiredBoxHeight L ((wiredBoxGraph L).src e) ≤
        wiredBoxHeight L ((wiredBoxGraph L).tgt e) + 1 ∧
      wiredBoxHeight L ((wiredBoxGraph L).tgt e) ≤
        wiredBoxHeight L ((wiredBoxGraph L).src e) + 1 := by
  cases e with
  | inl e =>
      have hx : e.1.1.val < L := by have h := e.1.2; omega
      by_cases hzero : e.2.val = 0
      · have hjlt : e.2.val < L := by omega
        let p : Fin L × Fin L := (horizontalFaceX e, ⟨0, by omega⟩)
        have hs : (wiredBoxGraph L).src (Sum.inl e) = some p := by
          simp [p, wiredBoxGraph, wiredBoxSrc, horizontalPrimalSrc, hzero]
          omega
        have ht : (wiredBoxGraph L).tgt (Sum.inl e) = none := by
          simp [wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt, hzero]
        have hd : wiredBoundaryDepth L p = 0 := by
          simp [wiredBoundaryDepth, p]
        rw [hs, ht]
        simp [wiredBoxHeight, hd]
      · by_cases hlast : e.2.val = L
        · let q : Fin L × Fin L := (horizontalFaceX e, ⟨L - 1, by omega⟩)
          have hs : (wiredBoxGraph L).src (Sum.inl e) = none := by
            simp [wiredBoxGraph, wiredBoxSrc, horizontalPrimalSrc, hlast]
          have ht : (wiredBoxGraph L).tgt (Sum.inl e) = some q := by
            simp [q, wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt, hlast]
            omega
          have hd : wiredBoundaryDepth L q = 0 := by
            simp [wiredBoundaryDepth, q]
          rw [hs, ht]
          simp [wiredBoxHeight, hd]
        · have hrow : e.2.val < L := by have h := e.2.isLt; omega
          let p : Fin L × Fin L := (horizontalFaceX e, ⟨e.2.val, hrow⟩)
          let q : Fin L × Fin L :=
            (horizontalFaceX e, ⟨e.2.val - 1, by have h := e.2.isLt; omega⟩)
          have hs : (wiredBoxGraph L).src (Sum.inl e) = some p := by
            simp [p, wiredBoxGraph, wiredBoxSrc, horizontalPrimalSrc, hrow]
          have ht : (wiredBoxGraph L).tgt (Sum.inl e) = some q := by
            simp [q, wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt, hzero]
          have hd := wiredBoundaryDepth_unitStep (p := p) (q := q)
            (by constructor <;> simp [p, q])
            (by constructor <;> simp [p, q] <;> omega)
          rw [hs, ht]
          simp only [wiredBoxHeight]
          omega
  | inr e =>
      have hy : e.2.1.val < L := by have h := e.2.2; omega
      by_cases hzero : e.1.val = 0
      · have hcol : e.1.val < L := by omega
        let p : Fin L × Fin L := (⟨0, by omega⟩, verticalFaceY e)
        have hs : (wiredBoxGraph L).src (Sum.inr e) = none := by
          simp [wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, hzero]
        have ht : (wiredBoxGraph L).tgt (Sum.inr e) = some p := by
          simp [p, wiredBoxGraph, wiredBoxTgt, verticalPrimalTgt, hcol]
          apply Fin.ext
          exact hzero
        have hd : wiredBoundaryDepth L p = 0 := by
          simp [wiredBoundaryDepth, p]
        rw [hs, ht]
        simp [wiredBoxHeight, hd]
      · by_cases hlast : e.1.val = L
        · let p : Fin L × Fin L := (⟨L - 1, by omega⟩, verticalFaceY e)
          have hs : (wiredBoxGraph L).src (Sum.inr e) = some p := by
            simp [p, wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, hlast]
            omega
          have ht : (wiredBoxGraph L).tgt (Sum.inr e) = none := by
            simp [wiredBoxGraph, wiredBoxTgt, verticalPrimalTgt, hlast]
          have hd : wiredBoundaryDepth L p = 0 := by
            simp [wiredBoundaryDepth, p]
          rw [hs, ht]
          simp [wiredBoxHeight, hd]
        · have hcol : e.1.val < L := by have h := e.1.isLt; omega
          let p : Fin L × Fin L :=
            (⟨e.1.val - 1, by have h := e.1.isLt; omega⟩, verticalFaceY e)
          let q : Fin L × Fin L := (⟨e.1.val, hcol⟩, verticalFaceY e)
          have hs : (wiredBoxGraph L).src (Sum.inr e) = some p := by
            simp [p, wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, hzero]
          have ht : (wiredBoxGraph L).tgt (Sum.inr e) = some q := by
            simp [q, wiredBoxGraph, wiredBoxTgt, verticalPrimalTgt, hcol]
          have hd := wiredBoundaryDepth_unitStep (p := p) (q := q)
            (by constructor <;> simp [p, q] <;> omega)
            (by constructor <;> simp [p, q])
          rw [hs, ht]
          simp only [wiredBoxHeight]
          omega

private theorem wiredBoxAdj_height_step (L : ℕ) (hL : 1 < L)
    {u v : WiredVertex L} (h : (wiredBoxGraph L).Adj u v) :
    wiredBoxHeight L u ≤ wiredBoxHeight L v + 1 ∧
      wiredBoxHeight L v ≤ wiredBoxHeight L u + 1 := by
  rcases h with ⟨e, h | h⟩
  · have he := wiredBoxEdge_height_step L hL e
    constructor
    · calc
        wiredBoxHeight L u = wiredBoxHeight L ((wiredBoxGraph L).src e) := by rw [h.1]
        _ ≤ wiredBoxHeight L ((wiredBoxGraph L).tgt e) + 1 := he.1
        _ = wiredBoxHeight L v + 1 := by rw [h.2]
    · calc
        wiredBoxHeight L v = wiredBoxHeight L ((wiredBoxGraph L).tgt e) := by rw [h.2]
        _ ≤ wiredBoxHeight L ((wiredBoxGraph L).src e) + 1 := he.2
        _ = wiredBoxHeight L u + 1 := by rw [h.1]
  · have he := wiredBoxEdge_height_step L hL e
    constructor
    · calc
        wiredBoxHeight L u = wiredBoxHeight L ((wiredBoxGraph L).tgt e) := by rw [h.2]
        _ ≤ wiredBoxHeight L ((wiredBoxGraph L).src e) + 1 := he.2
        _ = wiredBoxHeight L v + 1 := by rw [h.1]
    · calc
        wiredBoxHeight L v = wiredBoxHeight L ((wiredBoxGraph L).src e) := by rw [h.1]
        _ ≤ wiredBoxHeight L ((wiredBoxGraph L).tgt e) + 1 := he.1
        _ = wiredBoxHeight L u + 1 := by rw [h.2]

private theorem wiredBoxWalk_height_le (L : ℕ) (hL : 1 < L)
    {u v : WiredVertex L} (w : (wiredBoxGraph L).toSimpleGraph.Walk u v) :
    wiredBoxHeight L u ≤ wiredBoxHeight L v + w.length := by
  induction w with
  | nil => simp [wiredBoxHeight]
  | @cons a b c hab tail ih =>
      have hadj : (wiredBoxGraph L).Adj a b := by
        rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, h | h⟩
        · exact h
        · exact (wiredBoxGraph L).adj_symm h
      have hstep := wiredBoxAdj_height_step L hL hadj
      simp only [SimpleGraph.Walk.length_cons]
      omega

private theorem exists_wired_boundary_point (L : ℕ) (hL : 1 < L)
    (x : Fin L × Fin L) :
    ∃ q : Fin L × Fin L,
      (Lattice2D.squareFreeGraph L).toSimpleGraph.dist x q ≤ wiredBoundaryDepth L x ∧
        (wiredBoxGraph L).Adj (some q) none := by
  rcases wiredBoundaryDepth_eq_one_side L x with h | h | h | h
  · let q : Fin L × Fin L := (⟨0, by omega⟩, x.2)
    refine ⟨q, ?_, ?_⟩
    · have hr : Lattice2D.freeRadius x q = wiredBoundaryDepth L x := by
        simp [Lattice2D.freeRadius, q, Nat.dist]
        omega
      calc
        _ ≤ Lattice2D.freeRadius x q := Lattice2D.squareFree_distance_le_radius x q
        _ = wiredBoundaryDepth L x := hr
    · refine ⟨verticalDualEdge (⟨0, by omega⟩ : Fin (L + 1)) q.2, Or.inr ?_⟩
      constructor <;> simp [q, show 0 < L by omega]
  · let q : Fin L × Fin L := (x.1, ⟨0, by omega⟩)
    refine ⟨q, ?_, ?_⟩
    · have hr : Lattice2D.freeRadius x q = wiredBoundaryDepth L x := by
        simp [Lattice2D.freeRadius, q, Nat.dist]
        omega
      calc
        _ ≤ Lattice2D.freeRadius x q := Lattice2D.squareFree_distance_le_radius x q
        _ = wiredBoundaryDepth L x := hr
    · refine ⟨horizontalDualEdge q.1 (⟨0, by omega⟩ : Fin (L + 1)), Or.inl ?_⟩
      constructor <;> simp [q, show 0 < L by omega]
  · let q : Fin L × Fin L := (⟨L - 1, by omega⟩, x.2)
    refine ⟨q, ?_, ?_⟩
    · have hr : Lattice2D.freeRadius x q = wiredBoundaryDepth L x := by
        simp [Lattice2D.freeRadius, q, Nat.dist]
        omega
      calc
        _ ≤ Lattice2D.freeRadius x q := Lattice2D.squareFree_distance_le_radius x q
        _ = wiredBoundaryDepth L x := hr
    · refine ⟨verticalDualEdge (⟨L, by omega⟩ : Fin (L + 1)) q.2, Or.inl ?_⟩
      constructor
      · simp [q]
        omega
      · simp [q]
  · let q : Fin L × Fin L := (x.1, ⟨L - 1, by omega⟩)
    refine ⟨q, ?_, ?_⟩
    · have hr : Lattice2D.freeRadius x q = wiredBoundaryDepth L x := by
        simp [Lattice2D.freeRadius, q, Nat.dist]
        omega
      calc
        _ ≤ Lattice2D.freeRadius x q := Lattice2D.squareFree_distance_le_radius x q
        _ = wiredBoundaryDepth L x := hr
    · refine ⟨horizontalDualEdge q.1 (⟨L, by omega⟩ : Fin (L + 1)), Or.inr ?_⟩
      constructor
      · simp [q]
      · simp [q]
        omega

/-- Internal wired distance is the nearest-side depth plus the final edge to the wired root.
This is the graph metric on KP's wired square `Λ_L^zero` (p. 2). -/
theorem wiredBoxGraph_dist_root_eq (L : ℕ) (hL : 1 < L) (x : Fin L × Fin L) :
    (wiredBoxGraph L).toSimpleGraph.dist (some x) none = wiredBoundaryDepth L x + 1 := by
  apply Nat.le_antisymm
  · obtain ⟨q, hdist, hadj⟩ := exists_wired_boundary_point L hL x
    have hreach :
        (Lattice2D.squareFreeGraph L).toSimpleGraph.Reachable x q :=
      (Lattice2D.squareFreeGraph_connected (by omega)).preconnected x q
    obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
    let w' := w.map (wiredFreeGraphHom L)
    have hadj' : (wiredBoxGraph L).toSimpleGraph.Adj (some q) none := by
      change (SimpleGraph.fromRel (wiredBoxGraph L).Adj).Adj _ _
      exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨by simp, Or.inl hadj⟩
    let wlast := SimpleGraph.Walk.cons hadj' SimpleGraph.Walk.nil
    have hq : some q = (wiredFreeGraphHom L) q := rfl
    let wlast' := wlast.copy hq rfl
    let wfull := w'.append wlast'
    have hlen : wfull.length =
        (Lattice2D.squareFreeGraph L).toSimpleGraph.dist x q + 1 := by
      calc
        wfull.length = w'.length + wlast'.length := by
          change (w'.append wlast').length = _
          rw [SimpleGraph.Walk.length_append]
        _ = w.length + 1 := by simp [w', wlast', wlast]
        _ = (Lattice2D.squareFreeGraph L).toSimpleGraph.dist x q + 1 := by rw [hw]
    calc
      (wiredBoxGraph L).toSimpleGraph.dist (some x) none ≤ wfull.length :=
        SimpleGraph.dist_le wfull
      _ = (Lattice2D.squareFreeGraph L).toSimpleGraph.dist x q + 1 := hlen
      _ ≤ wiredBoundaryDepth L x + 1 := Nat.add_le_add_right hdist 1
  · have hconn : (wiredBoxGraph L).Connected :=
      (squareZeroWiredBoxGraphIsomorphism L).connected_iff.mp
        (squareZero_connected L hL)
    have hreach :
        (wiredBoxGraph L).toSimpleGraph.Reachable (some x) none :=
      hconn.preconnected (some x) none
    obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
    have hpotential := wiredBoxWalk_height_le L hL w
    have hlower : wiredBoundaryDepth L x + 1 ≤ w.length := by
      simpa [wiredBoxHeight] using hpotential
    rw [hw] at hlower
    exact hlower

/--
The wired distance formula on the carrier, transported from its internal dual-square
model (KP p. 2).
-/
theorem squareZero_dist_root_eq (L : ℕ) (hL : 1 < L) (x : Fin L × Fin L) :
    (squareZero L).toSimpleGraph.dist (some x) none = wiredBoundaryDepth L x + 1 := by
  calc
    (squareZero L).toSimpleGraph.dist (some x) none =
        (wiredBoxGraph L).toSimpleGraph.dist (some x) none := by
          have h := (squareZeroWiredBoxGraphIsomorphism L).dist_transport (some x) none
          have hV : (squareZeroWiredBoxGraphIsomorphism L).vertices = Equiv.refl _ := rfl
          rw [hV] at h
          simpa using h.symm
    _ = wiredBoundaryDepth L x + 1 := wiredBoxGraph_dist_root_eq L hL x

/--
KP Proposition 6.1 restated directly for the Villain law.

The cosine observable
is the rooted IGFF line-source exponential moment on the side-`L+1` dual square (§6.1, pp. 32–34).
-/
theorem villainLaw_cosIntegral_eq_kpProposition61 (L : ℕ) (hL : 1 < L)
    (β : ℝ) (hβ : 0 < β) (x : Fin L × Fin L) :
    (∫ θ, Real.cos (θ (some x)) ∂villainLaw L β hβ) =
      igffExpectation (dualBoxGraph L) (dualBoxGraph_connected (by omega)) (1 / β)
        (one_div_pos.mpr hβ) (dualBoxRoot L) (kpPrintedLineSourceObservable β x) := by
  rw [villainLaw_cosIntegral_eq_villainCosExpectation L β hβ x]
  exact villainCosExpectation_eq_kpProposition61 hL β hβ x

end Duality

end FroehlichSpencer.BKT

end
