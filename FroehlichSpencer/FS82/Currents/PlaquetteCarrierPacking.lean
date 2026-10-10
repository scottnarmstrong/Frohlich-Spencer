/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.SourceFilling
public import FroehlichSpencer.FS82.Currents.ComponentPacking
public import FroehlichSpencer.FS82.Currents.SourcePacking
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import FroehlichSpencer.FS82.Moment.SourceJensen

/-!
# FS82 PlaquetteCarrierPacking plaquette carrier bridge

The source filling plaquettes are cells of the bumped primal box.  The
Gaussian curvature lives on the finite dual two-cell carrier.  The latter
embeds as exactly the interior-coordinate source plaquettes.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking

open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Moment.SourceJensen

abbrev SourceInteriorCoord (B : Box 4) (i : Fin 4) :=
  {x : Coord (bumpedBox B) i // match x with
    | Sum.inl v => 0 < v.val ∧ v.val ≤ B i
    | Sum.inr _ => True}

def sourceDualCoordToInterior {B : Box 4} (i : Fin 4) :
    DualCoord B i → SourceInteriorCoord B i
  | Sum.inl v => ⟨Sum.inl ⟨v.val + 1, by dsimp [bumpedBox]; omega⟩, by
      change 0 < v.val + 1 ∧ v.val + 1 ≤ B i
      omega⟩
  | Sum.inr e => ⟨Sum.inr e, by trivial⟩

def sourceInteriorToDualCoord {B : Box 4} (i : Fin 4) :
    SourceInteriorCoord B i → DualCoord B i := fun x =>
  match h : x.1 with
  | Sum.inl v => Sum.inl ⟨v.val - 1, by
      have hv := x.2
      rw [h] at hv
      change 0 < v.val ∧ v.val ≤ B i at hv
      omega⟩
  | Sum.inr e => Sum.inr e

theorem sourceDualCoordToInterior_left_inv {B : Box 4} (i : Fin 4)
    (x : DualCoord B i) :
    sourceInteriorToDualCoord i (sourceDualCoordToInterior i x) = x := by
  cases x with
  | inl v =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp
  | inr e => rfl

theorem sourceDualCoordToInterior_right_inv {B : Box 4} (i : Fin 4)
    (x : SourceInteriorCoord B i) :
    sourceDualCoordToInterior i (sourceInteriorToDualCoord i x) = x := by
  apply Subtype.ext
  cases x with
  | mk val hvalProp =>
      cases val with
      | inl v =>
          have hv := hvalProp
          change 0 < v.val ∧ v.val ≤ B i at hv
          simp [sourceInteriorToDualCoord, sourceDualCoordToInterior,
            Nat.sub_add_cancel (Nat.succ_le_iff.mpr hv.1)]
      | inr e => simp [sourceInteriorToDualCoord, sourceDualCoordToInterior]

def sourceDualCellInteriorEquiv {B : Box 4} :
    DualCell 4 B ≃ {c : Cell 4 (bumpedBox B) //
      ∀ i, match c i with
        | Sum.inl v => 0 < v.val ∧ v.val ≤ B i
        | Sum.inr _ => True} where
  toFun c := ⟨fun i => (sourceDualCoordToInterior i (c i)).1, fun i =>
    (sourceDualCoordToInterior i (c i)).2⟩
  invFun c := fun i => sourceInteriorToDualCoord i ⟨c.1 i, c.2 i⟩
  left_inv c := by
    funext i
    exact sourceDualCoordToInterior_left_inv i (c i)
  right_inv c := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val
      (sourceDualCoordToInterior_right_inv i ⟨c.1 i, c.2 i⟩)

theorem sourceDualCellInteriorEquiv_val {B : Box 4} (c : DualCell 4 B) :
    (sourceDualCellInteriorEquiv c).1 = lambdaCellToBumpedBox c := by
  funext i
  change (sourceDualCoordToInterior i (c i)).1 =
    lambdaCellToBumpedBox c i
  cases h : c i with
  | inl v => simp [sourceDualCoordToInterior, lambdaCellToBumpedBox, h]
  | inr e =>
      simp only [sourceDualCoordToInterior, lambdaCellToBumpedBox, h]
      apply congrArg Sum.inr
      apply Fin.ext
      rfl

def sourcePlaquetteInDualImage {B : Box 4} (p : SourcePlaquette B) : Prop :=
  ∀ i, match p.1 i with
    | Sum.inl v => 0 < v.val ∧ v.val ≤ B i
    | Sum.inr _ => True

def sourceDualTwoPlaquette {B : Box 4}
    (q : SourceDualTwoCells B) : SourcePlaquette B :=
  ⟨lambdaCellToBumpedBox q.1, by
    rw [lambdaCellToBumpedBox_degree]
    exact q.2⟩

theorem sourceDualTwoPlaquette_injective {B : Box 4} :
    Function.Injective (@sourceDualTwoPlaquette B) := by
  intro q r h
  apply Subtype.ext
  exact lambdaCellToBumpedBox_injective (congrArg Subtype.val h)

theorem sourceDualTwoPlaquette_interior {B : Box 4}
    (q : SourceDualTwoCells B) :
    sourcePlaquetteInDualImage (sourceDualTwoPlaquette q) := by
  intro i
  have h := (sourceDualCellInteriorEquiv q.1).2 i
  simpa [sourceDualTwoPlaquette, sourceDualCellInteriorEquiv_val] using h

theorem sourcePlaquetteInDualImage_iff_exists {B : Box 4}
    (p : SourcePlaquette B) :
    sourcePlaquetteInDualImage p ↔ ∃ q : SourceDualTwoCells B,
      sourceDualTwoPlaquette q = p := by
  constructor
  · intro hp
    let interior : {c : Cell 4 (bumpedBox B) //
        ∀ i, match c i with
          | Sum.inl v => 0 < v.val ∧ v.val ≤ B i
          | Sum.inr _ => True} := ⟨p.1, hp⟩
    let c : DualCell 4 B := sourceDualCellInteriorEquiv.symm interior
    have hc : lambdaCellToBumpedBox c = p.1 := by
      calc
        lambdaCellToBumpedBox c = (sourceDualCellInteriorEquiv c).1 :=
          (sourceDualCellInteriorEquiv_val c).symm
        _ = p.1 := congrArg Subtype.val
          (sourceDualCellInteriorEquiv.right_inv interior)
    have hdegree : dualCellDegree c = 2 := by
      have h := p.2
      rw [← hc, lambdaCellToBumpedBox_degree] at h
      exact h
    refine ⟨⟨c, hdegree⟩, ?_⟩
    apply Subtype.ext
    exact hc
  · rintro ⟨q, rfl⟩
    exact sourceDualTwoPlaquette_interior q

noncomputable def sourcePlaquetteDualPreimage {B : Box 4}
    (p : SourcePlaquette B) (hp : sourcePlaquetteInDualImage p) :
    SourceDualTwoCells B :=
  Classical.choose (sourcePlaquetteInDualImage_iff_exists p |>.mp hp)

def sourceDualTwoPlaquetteEmbedding {B : Box 4} :
    SourceDualTwoCells B ↪ SourcePlaquette B where
  toFun := sourceDualTwoPlaquette
  inj' := sourceDualTwoPlaquette_injective

theorem sourceDualTwoPlaquette_range {B : Box 4}
    (p : SourcePlaquette B) :
    p ∈ Set.range (@sourceDualTwoPlaquetteEmbedding B) ↔
      sourcePlaquetteInDualImage p := by
  rw [Set.mem_range]
  rw [sourcePlaquetteInDualImage_iff_exists]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, hq⟩

noncomputable def sourceDualFieldOnPlaquettes {B : Box 4}
    (f : SourceDualTwoCells B → ℝ) (p : SourcePlaquette B) : ℝ := by
  classical
  exact if hp : sourcePlaquetteInDualImage p then
    f (sourcePlaquetteDualPreimage p hp) else 0

theorem sourceDualFieldOnPlaquettes_eq {B : Box 4}
    (f : SourceDualTwoCells B → ℝ) (q : SourceDualTwoCells B) :
    sourceDualFieldOnPlaquettes f (sourceDualTwoPlaquette q) = f q := by
  classical
  have hp := sourceDualTwoPlaquette_interior q
  have hpre : sourcePlaquetteDualPreimage (sourceDualTwoPlaquette q) hp = q := by
    apply sourceDualTwoPlaquette_injective
    exact Classical.choose_spec
      (sourcePlaquetteInDualImage_iff_exists
        (sourceDualTwoPlaquette q) |>.mp hp)
  simp [sourceDualFieldOnPlaquettes, hp, hpre]

/-- Extending a dual two-cell field by zero preserves its full squared norm:
the nonzero plaquette carrier is exactly the characterized image above. -/
theorem sourceDualFieldOnPlaquettes_energy {B : Box 4}
    (f : SourceDualTwoCells B → ℝ) :
    (∑ p : SourcePlaquette B, (sourceDualFieldOnPlaquettes f p)^2) =
      ∑ q : SourceDualTwoCells B, (f q)^2 := by
  classical
  let image : Finset (SourcePlaquette B) :=
    Finset.univ.image sourceDualTwoPlaquette
  have hsumAll :
      (∑ p : SourcePlaquette B, (sourceDualFieldOnPlaquettes f p)^2) =
        ∑ p ∈ image, (sourceDualFieldOnPlaquettes f p)^2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ image)
    intro p hp hpNot
    have hpNotRange : p ∉ Set.range (@sourceDualTwoPlaquetteEmbedding B) := by
      intro hpRange
      obtain ⟨q, hq⟩ := hpRange
      apply hpNot
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩
    have hpNotInterior : ¬ sourcePlaquetteInDualImage p := by
      intro hpInterior
      exact hpNotRange ((sourceDualTwoPlaquette_range p).2 hpInterior)
    simp [sourceDualFieldOnPlaquettes, hpNotInterior]
  have hmap :
      (∑ q : SourceDualTwoCells B,
        (sourceDualFieldOnPlaquettes f (sourceDualTwoPlaquette q))^2) =
        ∑ p ∈ image, (sourceDualFieldOnPlaquettes f p)^2 := by
    symm
    simpa [image] using
      (Finset.sum_image (s := Finset.univ)
        (g := sourceDualTwoPlaquette)
        (f := fun p : SourcePlaquette B =>
          (sourceDualFieldOnPlaquettes f p)^2)
        (sourceDualTwoPlaquette_injective.injOn))
  calc
    (∑ p : SourcePlaquette B, (sourceDualFieldOnPlaquettes f p)^2) =
        ∑ p ∈ image, (sourceDualFieldOnPlaquettes f p)^2 := hsumAll
    _ = ∑ q : SourceDualTwoCells B,
        (sourceDualFieldOnPlaquettes f (sourceDualTwoPlaquette q))^2 := hmap.symm
    _ = ∑ q : SourceDualTwoCells B, (f q)^2 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [sourceDualFieldOnPlaquettes_eq]

/-- The whole source-current Jensen error transfers to the sum of its
incidence-component majorants.  The component maximum is the cube side `L`
times the maximizing curvature magnitude; this turns ShortPhase's `L^5` phase loss
into SourcePacking's corrected `L^10` activity. -/
theorem sourceCurrent_jensen_error_le_componentActivityL5
    {B : Box 4} (j : IntegerCurrent B)
    (phase : Link B → ℝ)
    (a C z : ℝ)
    (hz0 : 0 ≤ z) (hzHalf : z ≤ 1 / 2)
    (ha : 1 ≤ a) (hC : 0 ≤ C)
    (curvatureMax : CurrentComponentClass j → ℝ)
    (hCurvatureMax : ∀ c ∈ currentComponents j, 0 ≤ curvatureMax c)
    (hDecay : z ≤ Real.exp (-(a * (currentEnergy j + currentLength j))))
    (hPhase : ∀ c ∈ currentComponents j,
      |currentPhase phase (currentComponentCurrent j c)| ≤
        C * ((currentComponentSupport j c).card : ℝ) *
          curvatureMax c *
          currentEnergy (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ)^4) :
    sourceJensenGamma z * (currentPhase phase j)^2 ≤
      ∑ c ∈ currentComponents j,
        FroehlichSpencer.FS82.Currents.SourcePacking.sourceComponentActivityL5
          a C (currentComponentSupport j c).card *
          curvatureMax c^2 := by
  let componentMax : CurrentComponentClass j → ℝ := fun c =>
    ((currentComponentSupport j c).card : ℝ) * curvatureMax c
  have hMax : ∀ c ∈ currentComponents j, 0 ≤ componentMax c := by
    intro c hc
    dsimp [componentMax]
    exact mul_nonneg (by positivity) (hCurvatureMax c hc)
  have hphase' : ∀ c ∈ currentComponents j,
      |currentPhase phase (currentComponentCurrent j c)| ≤
        C * componentMax c *
          currentEnergy (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ)^4 := by
    intro c hc
    simpa [componentMax, mul_assoc, mul_left_comm, mul_comm] using hPhase c hc
  have hgamma : sourceJensenGamma z ≤ 5 * z :=
    sourceJensenGamma_le_five_mul hz0 hzHalf
  have hcomp := currentPhase_jensen_error_le_componentMajorants
    j phase a C z (sourceJensenGamma z) componentMax
    ha hC hMax hgamma hDecay hphase'
  calc
    sourceJensenGamma z * (currentPhase phase j)^2 ≤
        ∑ c ∈ currentComponents j,
          (20 * C^2 / a^2) *
            ((currentComponentSupport j c).card : ℝ)^8 *
              Real.exp (- (a * ((currentComponentSupport j c).card : ℝ))) *
                componentMax c^2 := hcomp
    _ = ∑ c ∈ currentComponents j,
          FroehlichSpencer.FS82.Currents.SourcePacking.sourceComponentActivityL5
            a C (currentComponentSupport j c).card *
              curvatureMax c^2 := by
          apply Finset.sum_congr rfl
          intro c hc
          simp only [componentMax,
            FroehlichSpencer.FS82.Currents.SourcePacking.sourceComponentActivityL5]
          ring

/-- The same transfer in the source's physical-current normalization.  The
field `tau` is paired with `2π j`, exactly as in the source Jensen input. -/
theorem sourceCurrent_jensen_error_le_componentActivityL5_ofSourcePhase
    {B : Box 4} (j : IntegerCurrent B)
    (tau : Link B → ℝ)
    (a C z : ℝ)
    (hz0 : 0 ≤ z) (hzHalf : z ≤ 1 / 2)
    (ha : 1 ≤ a) (hC : 0 ≤ C)
    (curvatureMax : CurrentComponentClass j → ℝ)
    (hCurvatureMax : ∀ c ∈ currentComponents j, 0 ≤ curvatureMax c)
    (hDecay : z ≤ Real.exp (-(a * (currentEnergy j + currentLength j))))
    (hPhase : ∀ c ∈ currentComponents j,
      |sourceCurrentPhase tau (currentComponentCurrent j c)| ≤
        C * ((currentComponentSupport j c).card : ℝ) *
          curvatureMax c *
          currentEnergy (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ)^4) :
    sourceJensenGamma z * (sourceCurrentPhase tau j)^2 ≤
      ∑ c ∈ currentComponents j,
        FroehlichSpencer.FS82.Currents.SourcePacking.sourceComponentActivityL5
          a C (currentComponentSupport j c).card *
          curvatureMax c^2 := by
  have hPhase' : ∀ c ∈ currentComponents j,
      |currentPhase (fun e => (2 * Real.pi) * tau e)
          (currentComponentCurrent j c)| ≤
        C * ((currentComponentSupport j c).card : ℝ) *
          curvatureMax c *
          currentEnergy (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ)^4 := by
    intro c hc
    rw [currentPhase_eq_sourceCurrentPhase]
    exact hPhase c hc
  have h := sourceCurrent_jensen_error_le_componentActivityL5
    j (fun e => (2 * Real.pi) * tau e) a C z hz0 hzHalf ha hC
    curvatureMax hCurvatureMax hDecay hPhase'
  simpa only [currentPhase_eq_sourceCurrentPhase] using h


end FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
