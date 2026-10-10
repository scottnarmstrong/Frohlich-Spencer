/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib

-- Reset the auxiliary-lemma cache between copied source modules.
-- This preserves generated proof names without changing definitions or assumptions.
-- Four matchers are written explicitly to preserve their original module-local names.
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
noncomputable section
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
structure RectBox4 where
  origin : Fin 4 → ℤ
  side : Fin 4 → ℕ
  side_pos : ∀ i, 0 < side i
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
def RectBox4.shortestSide (R : RectBox4) : ℕ := Finset.univ.inf' Finset.univ_nonempty R.side
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def RectBox4.longestSide (R : RectBox4) : ℕ := Finset.univ.sup' Finset.univ_nonempty R.side
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def IsLogThickRectBox4 (R : RectBox4) : Prop := Real.log ((R.longestSide + 1 : ℕ) : ℝ) ≤ (R.shortestSide : ℝ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev DualCoord (R : RectBox4) (i : Fin 4) := Sum (Fin (R.side i)) (Fin (R.side i + 1))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev DualCell (R : RectBox4) := (i : Fin 4) → DualCoord R i
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def dualCellAxes (R : RectBox4) (c : DualCell R) : Finset (Fin 4) := Finset.univ.filter fun i => (c i).isRight
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def dualCellDegree (R : RectBox4) (c : DualCell R) : ℕ := (dualCellAxes R c).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev DualVertices (R : RectBox4) := {c : DualCell R // dualCellDegree R c = 0}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev DualLinks (R : RectBox4) := {c : DualCell R // dualCellDegree R c = 1}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[instance_reducible] noncomputable def dualLinksFintype (R : RectBox4) : Fintype (DualLinks R) := Fintype.ofFinite _
attribute [instance] dualLinksFintype
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev LatticeCoord := Sum ℤ ℤ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev LatticeCell := (i : Fin 4) → LatticeCoord
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev LatticeChain := LatticeCell →₀ ℤ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev RealLatticeChain := LatticeCell →₀ ℝ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def dualEmbedCoordC1 (R : RectBox4) (i : Fin 4) :
    DualCoord R i ↪ LatticeCoord where
  toFun := fun x => match x with
    | Sum.inl v => Sum.inl (R.origin i + v.val + 1)
    | Sum.inr e => Sum.inr (R.origin i + e.val)
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [Sum.inl.injEq] at h
        have hv : (x.val : ℤ) = y.val := by omega
        exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hv))
      | inr y => cases h
    | inr x =>
      cases y with
      | inl y => cases h
      | inr y =>
        simp only [Sum.inr.injEq] at h
        have hv : (x.val : ℤ) = y.val := Int.add_left_cancel h
        exact congrArg Sum.inr (Fin.ext (by exact_mod_cast hv))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def dualCellEmbeddingC1 (R : RectBox4) : DualCell R ↪ LatticeCell where
  toFun c i := dualEmbedCoordC1 R i (c i)
  inj' := by
    intro c₁ c₂ h
    funext i
    exact (dualEmbedCoordC1 R i).injective (congrFun h i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def lambdaStarEmbeddingC1 (R : RectBox4) : DualLinks R ↪ LatticeCell := Function.Embedding.trans (Function.Embedding.subtype _) (dualCellEmbeddingC1 R)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def latticeIsEdge (x : LatticeCoord) : Prop := x.isRight
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeRankBefore (c : LatticeCell) (i : Fin 4) : ℕ := by
  classical
  exact (Finset.univ.filter fun j : Fin 4 => j < i ∧ latticeIsEdge (c j)).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeBasis (c : LatticeCell) : LatticeChain := Finsupp.single c 1
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeEdgeCell (c : LatticeCell) (i : Fin 4) (t : ℤ) : LatticeCell := Function.update c i (Sum.inr t)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeUpperFace (c : LatticeCell) (i : Fin 4) (t : ℤ) : LatticeCell := Function.update c i (Sum.inl (t + 1))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeLowerFace (c : LatticeCell) (i : Fin 4) (t : ℤ) : LatticeCell := Function.update c i (Sum.inl t)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeBoundaryBasis (c : LatticeCell) : LatticeChain :=
  ∑ i : Fin 4, match c i with
    | Sum.inl _ => 0
    | Sum.inr t =>
        ((-1 : ℤ) ^ latticeRankBefore c i) •
          (latticeBasis (latticeUpperFace c i t) - latticeBasis (latticeLowerFace c i t))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeCoboundaryBasis (c : LatticeCell) : LatticeChain :=
  ∑ i : Fin 4, match c i with
    | Sum.inr _ => 0
    | Sum.inl t =>
        ((-1 : ℤ) ^ latticeRankBefore c i) •
          (latticeBasis (latticeEdgeCell c i (t - 1)) - latticeBasis (latticeEdgeCell c i t))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeBoundary : LatticeChain →ₗ[ℤ] LatticeChain := Finsupp.linearCombination ℤ latticeBoundaryBasis
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeCoboundary : LatticeChain →ₗ[ℤ] LatticeChain := Finsupp.linearCombination ℤ latticeCoboundaryBasis
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def latticeDeltaD : LatticeChain →ₗ[ℤ] LatticeChain := latticeBoundary ∘ₗ latticeCoboundary
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def castLatticeChain (q : LatticeChain) : RealLatticeChain := Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def realifyLatticeLinearMap (T : LatticeChain →ₗ[ℤ] LatticeChain) : RealLatticeChain →ₗ[ℝ] RealLatticeChain := Finsupp.linearCombination ℝ (fun c : LatticeCell => castLatticeChain (T (latticeBasis c)))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def realLatticeBoundary : RealLatticeChain →ₗ[ℝ] RealLatticeChain := realifyLatticeLinearMap latticeBoundary
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def realLatticeDeltaD : RealLatticeChain →ₗ[ℝ] RealLatticeChain := realifyLatticeLinearMap latticeDeltaD
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev LambdaStarRealChain (R : RectBox4) := DualLinks R →₀ ℝ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev RealDualField (R : RectBox4) := EuclideanSpace ℝ (DualLinks R)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev _root_.FroehlichSpencer.FS82.Surface.IsInteriorDualLink.match_1.{u_1} : (motive : FroehlichSpencer.FS82.Surface.LatticeCoord → Sort u_1) → (x : FroehlichSpencer.FS82.Surface.LatticeCoord) → (h_1 : (t : Int) → motive (@Sum.inl.{0, 0} Int Int t)) → (h_2 : (t : Int) → motive (@Sum.inr.{0, 0} Int Int t)) → motive x :=
fun (motive : FroehlichSpencer.FS82.Surface.LatticeCoord → Sort u_1) (x : FroehlichSpencer.FS82.Surface.LatticeCoord) (h_1 : (t : Int) → motive (@Sum.inl.{0, 0} Int Int t)) (h_2 : (t : Int) → motive (@Sum.inr.{0, 0} Int Int t)) => @Sum.casesOn.{u_1, 0, 0} Int Int (fun (x : FroehlichSpencer.FS82.Surface.LatticeCoord) => motive x) x (fun (val : Int) => h_1 val) fun (val : Int) => h_2 val
def IsInteriorDualLink (R : RectBox4) (e : DualLinks R) : Prop := ∀ i : Fin 4, IsInteriorDualLink.match_1 (fun _ => Prop) ((lambdaStarEmbeddingC1 R e) i) (fun t => R.origin i < t ∧ t < R.origin i + R.side i) (fun t => R.origin i < t ∧ t + 1 < R.origin i + R.side i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def IsInteriorSupported (R : RectBox4) (μ : RealDualField R) : Prop := ∀ e : DualLinks R, μ e ≠ 0 → IsInteriorDualLink R e
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def euclideanToFinsupp (R : RectBox4) :
    RealDualField R →ₗ[ℝ] LambdaStarRealChain R where
  toFun x := (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R)).symm x.ofLp
  map_add' x y := by
    apply (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R)).injective
    simp only [map_add, LinearEquiv.apply_symm_apply, WithLp.ofLp_add]
  map_smul' a x := by
    apply (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R)).injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, WithLp.ofLp_smul, RingHom.id_apply]
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def finsuppToEuclidean (R : RectBox4) :
    LambdaStarRealChain R →ₗ[ℝ] RealDualField R where
  toFun q := WithLp.toLp 2 (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R) q)
  map_add' q r := by
    ext a
    simp only [WithLp.ofLp_add, Pi.add_apply]
    simp [Finsupp.linearEquivFunOnFinite]
  map_smul' c q := by
    ext a
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp [Finsupp.linearEquivFunOnFinite]
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def lambdaStarRealZeroExtension (R : RectBox4) : LambdaStarRealChain R →ₗ[ℝ] RealLatticeChain := Finsupp.linearCombination ℝ (fun e : DualLinks R => Finsupp.single (lambdaStarEmbeddingC1 R e) 1)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def lambdaStarRealCompression (R : RectBox4) :
    RealLatticeChain →ₗ[ℝ] LambdaStarRealChain R where
  toFun q := Finsupp.comapDomain (lambdaStarEmbeddingC1 R) q
    (lambdaStarEmbeddingC1 R).injective.injOn
  map_add' q₁ q₂ := Finsupp.comapDomain_add_of_injective
    (lambdaStarEmbeddingC1 R).injective q₁ q₂
  map_smul' a q := by ext e; simp
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def piLambdaStarDeltaDReal (R : RectBox4) : LambdaStarRealChain R →ₗ[ℝ] LambdaStarRealChain R := lambdaStarRealCompression R ∘ₗ realLatticeDeltaD ∘ₗ lambdaStarRealZeroExtension R
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def finiteLatticeHodgeOperator (R : RectBox4) : RealDualField R →ₗ[ℝ] RealDualField R := (finsuppToEuclidean R).comp ((piLambdaStarDeltaDReal R).comp (euclideanToFinsupp R))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def fullLatticeDivergence (R : RectBox4) : RealDualField R →ₗ[ℝ] RealLatticeChain := realLatticeBoundary ∘ₗ lambdaStarRealZeroExtension R ∘ₗ euclideanToFinsupp R
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def lambdaStarVertexRestriction (R : RectBox4) :
    RealLatticeChain →ₗ[ℝ] EuclideanSpace ℝ (DualVertices R) where
  toFun q := WithLp.toLp 2 fun v => q (dualCellEmbeddingC1 R v.1)
  map_add' q q' := by ext v; rfl
  map_smul' a q := by ext v; simp [smul_eq_mul]
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def lambdaStarVertexDivergence (R : RectBox4) : RealDualField R →ₗ[ℝ] EuclideanSpace ℝ (DualVertices R) := (lambdaStarVertexRestriction R).comp (fullLatticeDivergence R)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable abbrev GlobalCoClosed (R : RectBox4) : Submodule ℝ (RealDualField R) := (fullLatticeDivergence R).ker
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable abbrev W (R : RectBox4) : Submodule ℝ (RealDualField R) := (lambdaStarVertexDivergence R).ker
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev IntegerDualField (R : RectBox4) := DualLinks R → ℤ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev LatticeVertices4 := Fin 4 → ℤ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev _root_.FroehlichSpencer.FS82.Surface.latticePotentialGradient.match_1.{u_1} : (motive : FroehlichSpencer.FS82.Surface.LatticeCoord → Sort u_1) → (x : FroehlichSpencer.FS82.Surface.LatticeCoord) → (h_1 : (val : Int) → motive (@Sum.inl.{0, 0} Int Int val)) → (h_2 : (t : Int) → motive (@Sum.inr.{0, 0} Int Int t)) → motive x :=
fun (motive : FroehlichSpencer.FS82.Surface.LatticeCoord → Sort u_1) (x : FroehlichSpencer.FS82.Surface.LatticeCoord) (h_1 : (val : Int) → motive (@Sum.inl.{0, 0} Int Int val)) (h_2 : (t : Int) → motive (@Sum.inr.{0, 0} Int Int t)) => @Sum.casesOn.{u_1, 0, 0} Int Int (fun (x : FroehlichSpencer.FS82.Surface.LatticeCoord) => motive x) x (fun (val : Int) => h_1 val) fun (val : Int) => h_2 val
noncomputable def latticePotentialGradient (γ : LatticeVertices4 → ℤ) (c : LatticeCell) : ℤ := if _hdeg : (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card = 1 then ∑ i : Fin 4, latticePotentialGradient.match_1 (fun _ => ℤ) (c i) (fun _ => 0) (fun t => γ (fun j => if j = i then t + 1 else Sum.elim id id (c j)) - γ (fun j => if j = i then t else Sum.elim id id (c j))) else 0
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def sourceIntegerGaugeRelation (R : RectBox4) (α α' : IntegerDualField R) : Prop := ∃ γ : LatticeVertices4 → ℤ, (∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 → c ∈ Set.range (lambdaStarEmbeddingC1 R)) ∧ ∀ e : DualLinks R, α' e = α e + latticePotentialGradient γ (lambdaStarEmbeddingC1 R e)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def lambdaStarIntegerZeroExtension (R : RectBox4) : (DualLinks R →₀ ℤ) →ₗ[ℤ] LatticeChain := Finsupp.linearCombination ℤ (fun e : DualLinks R => Finsupp.single (lambdaStarEmbeddingC1 R e) 1)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def integerLatticeCurl (R : RectBox4) (α : IntegerDualField R) : LatticeChain := latticeCoboundary (lambdaStarIntegerZeroExtension R (Finsupp.equivFunOnFinite.symm α))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def integerDualFieldWeight (R : RectBox4) (β : ℝ) (_hβ : 0 < β) (α : IntegerDualField R) : ℝ := Real.exp (-(1 / (2 * β)) * ∑ c ∈ (integerLatticeCurl R α).support, ((integerLatticeCurl R α c : ℝ) ^ 2))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def betaDoublePrime (cPack : ℝ → ℝ) (β : ℝ) : ℝ := β * (1 - 2 * β * cPack β)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem finiteLatticeHodgeOperator_preservesCoClosed (R : RectBox4) (μ : W R) : Surface.finiteLatticeHodgeOperator R (μ : RealDualField R) ∈ W R := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def finiteLatticeHodgeOperatorOnCoClosed (R : RectBox4) :
    W R →ₗ[ℝ] W R where
  toFun μ := ⟨finiteLatticeHodgeOperator R (μ : RealDualField R),
    finiteLatticeHodgeOperator_preservesCoClosed R μ⟩
  map_add' μ ν := by
    apply Subtype.ext
    exact map_add (finiteLatticeHodgeOperator R) (μ : RealDualField R) (ν : RealDualField R)
  map_smul' a μ := by
    apply Subtype.ext
    exact map_smul (finiteLatticeHodgeOperator R) a (μ : RealDualField R)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem existsUnique_finiteLatticeHodgeInverse (R : RectBox4) : ∃! V : W R →ₗ[ℝ] W R, ∀ μ : W R, Surface.finiteLatticeHodgeOperatorOnCoClosed R (V μ) = μ := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def finiteLatticeHodgeInverse (R : RectBox4) : W R →ₗ[ℝ] W R := Classical.choose (existsUnique_finiteLatticeHodgeInverse R).exists
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem sourceIntegerGaugeRelation_isEquivalence (R : RectBox4) : Equivalence (sourceIntegerGaugeRelation R) := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceIntegerGaugeRelationSetoid (R : RectBox4) : Setoid (IntegerDualField R) := ⟨sourceIntegerGaugeRelation R, sourceIntegerGaugeRelation_isEquivalence R⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev IntegerDualGaugeQuotient (R : RectBox4) := Quotient (sourceIntegerGaugeRelationSetoid R)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
instance integerDualGaugeQuotientMeasurableSpace (R : RectBox4) : MeasurableSpace (IntegerDualGaugeQuotient R) := ⊤
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem integerDualFieldWeight_respectsGauge (R : RectBox4) (β : ℝ) (hβ : 0 < β) (α α' : IntegerDualField R) (hα : sourceIntegerGaugeRelation R α α') : integerDualFieldWeight R β hβ α = integerDualFieldWeight R β hβ α' := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def integerDualGaugeWeight (R : RectBox4) (β : ℝ) (hβ : 0 < β) : IntegerDualGaugeQuotient R → ℝ := Quotient.lift (integerDualFieldWeight R β hβ) (fun α α' hα => integerDualFieldWeight_respectsGauge R β hβ α α' hα)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem integerDualPairing_respectsGauge (R : RectBox4) (μ : W R) (α α' : IntegerDualField R) (h : sourceIntegerGaugeRelation R α α') : (∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) = ∑ e : DualLinks R, (α' e : ℝ) * (μ : RealDualField R) e := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def integerDualPairing (R : RectBox4) (μ : W R) : IntegerDualGaugeQuotient R → ℝ := Quotient.lift (fun α => ∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) (integerDualPairing_respectsGauge R μ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem existsUnique_integerDualPartitionFunction (R : RectBox4) (β : ℝ) (hβ : 0 < β) : ∃! Z : ℝ, HasSum (integerDualGaugeWeight R β hβ) Z ∧ 0 < Z := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def integerDualPartitionFunction (R : RectBox4) (β : ℝ) (hβ : 0 < β) : ℝ := Classical.choose (existsUnique_integerDualPartitionFunction R β hβ).exists
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def discreteDualMeasure (R : RectBox4) (β : ℝ) (hβ : 0 < β) : MeasureTheory.Measure (IntegerDualGaugeQuotient R) := MeasureTheory.Measure.sum fun c => ENNReal.ofReal (integerDualGaugeWeight R β hβ c / integerDualPartitionFunction R β hβ) • MeasureTheory.Measure.dirac c
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def discreteDualMoment (R : RectBox4) (β : ℝ) (hβ : 0 < β) (ε : ℝ) (μ : W R) : ENNReal := ∫⁻ c, ENNReal.ofReal (Real.exp (ε * integerDualPairing R μ c)) ∂discreteDualMeasure R β hβ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem interiorSupported_coClosed_iff (R : RectBox4) (μ : RealDualField R) (hμ : Surface.IsInteriorSupported R μ) : μ ∈ Surface.GlobalCoClosed R ↔ μ ∈ Surface.W R := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceTestToW (R : RectBox4) (μ : RealDualField R) (hμ : IsInteriorSupported R μ) (hglobal : μ ∈ GlobalCoClosed R) : W R := ⟨μ, (interiorSupported_coClosed_iff R μ hμ).mp hglobal⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def finiteLatticeCovarianceQuadratic (R : RectBox4) (μ : W R) : ℝ := inner ℝ μ (finiteLatticeHodgeInverse R μ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev DualPlaquettes (R : RectBox4) := {c : DualCell R // dualCellDegree R c = 2}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev SourceClosedIntegerCurrent (R : RectBox4) := {q : LatticeChain // latticeCoboundary q = 0 ∧ ∀ c : LatticeCell, c ∈ q.support → ∃ p : DualPlaquettes R, dualCellEmbeddingC1 R p.1 = c}
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
noncomputable def cubeRegion (N : ℕ) (hN : 0 < N) : RectBox4 where
  origin := fun _ => -(N : ℤ)
  side := fun _ => 2 * N
  side_pos := fun _ => by omega
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
noncomputable def globalPlaquetteAxes (c : LatticeCell) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun i => latticeIsEdge (c i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev GlobalPlaquette := {c : LatticeCell // (globalPlaquetteAxes c).card = 2}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def inCube (R : RectBox4) (p : GlobalPlaquette) : Prop := ∃ d : DualPlaquettes R, dualCellEmbeddingC1 R d.1 = p.1
end FroehlichSpencer.FS82.SurfaceInfinite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem existsUnique_sourceGaugeClass_closedCurrentEquiv (R : RectBox4) : ∃! e : IntegerDualGaugeQuotient R ≃ SourceClosedIntegerCurrent R, ∀ α : IntegerDualField R, (e (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 = integerLatticeCurl R α := by sorry
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
noncomputable def sourceCurrentEquiv (R : RectBox4) : IntegerDualGaugeQuotient R ≃ SourceClosedIntegerCurrent R := Classical.choose (existsUnique_sourceGaugeClass_closedCurrentEquiv R).exists
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
def sourceIntegerCellSign (c : LatticeCell) : ℤ := (-1 : ℤ) ^ ((globalPlaquetteAxes c).sum (fun i => i.val) + (globalPlaquetteAxes c).card)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def cubeCurvatureMap (R : RectBox4) (P : Finset GlobalPlaquette) (hP : ∀ p ∈ P, inCube R p) : IntegerDualGaugeQuotient R → P → ℤ := fun c p => sourceIntegerCellSign p.1 * (sourceCurrentEquiv R c).1 (dualCellEmbeddingC1 R (Classical.choose (hP p.1 p.2)).1)
end FroehlichSpencer.FS82.SurfaceInfinite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem discreteDualMeasure_isProbabilityMeasure (R : RectBox4) (β : ℝ) (hβ : 0 < β) : MeasureTheory.IsProbabilityMeasure (discreteDualMeasure R β hβ) := by sorry
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
noncomputable def cubeCurvatureLaw (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (P : Finset GlobalPlaquette) (hP : ∀ p ∈ P, inCube R p) : PMF (P → ℤ) := by
  letI : IsProbabilityMeasure (discreteDualMeasure R β hβ) :=
    discreteDualMeasure_isProbabilityMeasure R β hβ
  exact ((discreteDualMeasure R β hβ).map (cubeCurvatureMap R P hP)).toPMF
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
structure CubeCurvatureLimitState (β : ℝ) (hβ : 0 < β) where
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  tailStart : Finset GlobalPlaquette → ℕ
  law : (P : Finset GlobalPlaquette) → PMF (P → ℤ)
  positiveCube : ∀ P k, 0 < subsequence (tailStart P + k)
  contained : ∀ P k p, p ∈ P →
    inCube (cubeRegion (subsequence (tailStart P + k)) (positiveCube P k)) p
  pointwise : ∀ P x, Tendsto
    (fun k => (cubeCurvatureLaw
      (cubeRegion (subsequence (tailStart P + k)) (positiveCube P k)) β hβ P
      (fun p hp => contained P k p hp) x).toReal) atTop
    (𝓝 ((law P x).toReal))
  consistent : ∀ (P₀ P₁ : Finset GlobalPlaquette) (hP : P₀ ⊆ P₁),
    PMF.map (fun x p => x ⟨p.1, hP p.2⟩) (law P₁) = law P₀
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev LatticePoint := ℤ × (ℤ × (ℤ × ℤ))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev Torus4 := AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def cellDegree (c : LatticeCell) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin 4 => latticeIsEdge (c i)).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev GlobalLinkField := {q : RealLatticeChain // ∀ c ∈ q.support, cellDegree c = 1}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def cellBaseCoordinate (c : LatticeCell) (i : Fin 4) : ℤ := Sum.elim id id (c i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def cellPoint (c : LatticeCell) : LatticePoint := (cellBaseCoordinate c 0, (cellBaseCoordinate c 1, (cellBaseCoordinate c 2, cellBaseCoordinate c 3)))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def linkAxisCell (c : LatticeCell) (i : Fin 4) : Prop := latticeIsEdge (c i) ∧ ∀ j, j ≠ i → ¬ latticeIsEdge (c j)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def globalLinkAxisSupport (μ : GlobalLinkField) (i : Fin 4) :
    Finset LatticeCell := by
  classical
  exact μ.1.support.filter (fun c => linkAxisCell c i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def latticeCharacter (x : LatticePoint) (k : Torus4) : ℂ := fourier (-x.1) k.1 * (fourier (-x.2.1) k.2.1 * (fourier (-x.2.2.1) k.2.2.1 * fourier (-x.2.2.2) k.2.2.2))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def torus4Haar : Measure Torus4 :=
  let ν : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle
  ν.prod (ν.prod (ν.prod ν))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def globalLinkFourierComponent (μ : GlobalLinkField) (i : Fin 4) (k : Torus4) : ℂ := ∑ c ∈ globalLinkAxisSupport μ i, (μ.1 c : ℂ) * latticeCharacter (cellPoint c) k
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def fourierLaplacianSymbol (k : Torus4) : ℝ :=
  ∑ i : Fin 4, ‖(1 : ℂ) - fourier 1 (match i.val with
    | 0 => k.1 | 1 => k.2.1 | 2 => k.2.2.1 | _ => k.2.2.2)‖ ^ 2
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def fourierGreenDensity (μ : GlobalLinkField) (k : Torus4) : ℝ := ∑ i : Fin 4, ‖globalLinkFourierComponent μ i k‖ ^ 2 / fourierLaplacianSymbol k
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def fourierGreenQuadratic (μ : GlobalLinkField) : ℝ := ∫ k : Torus4, fourierGreenDensity μ k ∂torus4Haar
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def cellOrientationSign (c : LatticeCell) : ℝ := (-1 : ℝ) ^ ((globalPlaquetteAxes c).sum (fun i => i.val) + (globalPlaquetteAxes c).card)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev GlobalPlaquetteField := {q : RealLatticeChain // ∀ c ∈ q.support, cellDegree c = 2}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def fillingPlaquetteEmbedding (σ : GlobalPlaquetteField) :
    {c : LatticeCell // c ∈ σ.1.support} ↪ GlobalPlaquette where
  toFun c := ⟨c.1, σ.2 c.1 c.2⟩
  inj' := by
    intro a b h
    exact Subtype.ext (congrArg (fun p : GlobalPlaquette => p.1) h)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def fillingCurvatureIndexSet (σ : GlobalPlaquetteField) : Finset GlobalPlaquette := σ.1.support.attach.map (fillingPlaquetteEmbedding σ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def fillingCurvaturePairing (σ : GlobalPlaquetteField) (x : fillingCurvatureIndexSet σ → ℤ) : ℝ := ∑ p : fillingCurvatureIndexSet σ, cellOrientationSign p.1.1 * σ.1 p.1.1 * (x p : ℝ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev _root_.FroehlichSpencer.FS82.SurfaceInfinite.sourcePointCoordinate.match_1.{u_1} : (motive : Nat → Sort u_1) → (x : Nat) → (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) → (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) → (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) → (h_4 : (x : Nat) → motive x) → motive x :=
fun (motive : Nat → Sort u_1) (x : Nat) (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (h_4 : (x : Nat) → motive x) => @dite.{u_1} (motive x) (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (instDecidableEqNat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Eq.ndrec_symm.{u_1, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (x : Nat) => motive x) (h_1 Unit.unit) x) fun (h_1 : Not (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) => @dite.{u_1} (motive x) (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (instDecidableEqNat x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Eq.ndrec_symm.{u_1, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (fun (x : Nat) => motive x) (h_2 Unit.unit) x) fun (h_2 : Not (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) => @dite.{u_1} (motive x) (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (instDecidableEqNat x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@Eq.ndrec_symm.{u_1, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (fun (x : Nat) => motive x) (h_3 Unit.unit) x) fun (h_3 : Not (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) => h_4 x
def sourcePointCoordinate (p : LatticePoint) (i : Fin 4) : ℤ := sourcePointCoordinate.match_1 (fun _ => ℤ) i.val (fun (_ : Unit) => p.1) (fun (_ : Unit) => p.2.1) (fun (_ : Unit) => p.2.2.1) (fun _ => p.2.2.2)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def dualCurvatureCell (x : LatticePoint) : LatticeCell := fun i => if i = 0 ∨ i = 1 then Sum.inr (sourcePointCoordinate x i) else Sum.inl (sourcePointCoordinate x i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def dualCurvatureAt (x : LatticePoint) : GlobalPlaquette := by
  refine ⟨dualCurvatureCell x, ?_⟩
  classical
  have haxes : globalPlaquetteAxes (dualCurvatureCell x) = {0, 1} := by
    classical
    ext i
    change i ∈ Finset.univ.filter (fun j : Fin 4 =>
      latticeIsEdge (dualCurvatureCell x j)) ↔ i ∈ ({0, 1} : Finset (Fin 4))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : i = 0 ∨ i = 1
    · simp [dualCurvatureCell, hi, latticeIsEdge]
    · simp [dualCurvatureCell, hi, latticeIsEdge]
  rw [haxes]
  decide
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def pairPlaquettes (x y : LatticePoint) : Finset GlobalPlaquette := insert (dualCurvatureAt x) {dualCurvatureAt y}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def pairProduct (x y : LatticePoint) (ω : pairPlaquettes x y → ℤ) : ℝ := (ω ⟨dualCurvatureAt x, by simp [pairPlaquettes]⟩ : ℝ) * (ω ⟨dualCurvatureAt y, by simp [pairPlaquettes]⟩ : ℝ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
structure CurvatureCylinderState where
  law : (P : Finset GlobalPlaquette) → PMF (P → ℤ)
  consistent : ∀ (P₀ P₁ : Finset GlobalPlaquette) (hP : P₀ ⊆ P₁),
    PMF.map (fun x p => x ⟨p.1, hP p.2⟩) (law P₁) = law P₀
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def dualCurvatureCorrelation (S : CurvatureCylinderState) (d : LatticePoint) : ℝ := ∫ ω, pairProduct 0 d ω ∂ (S.law (pairPlaquettes 0 d)).toMeasure
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def AbsolutelySummableCorrelation (C : LatticePoint → ℝ) : Prop := Summable fun d => |C d|
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev SourceLatticeShift := Fin 4 → ℤ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def sourceTranslateCoordinate (a : ℤ) : LatticeCoord → LatticeCoord := Sum.map (fun z => z + a) (fun z => z + a)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def sourceTranslateCell (a : SourceLatticeShift) (c : LatticeCell) : LatticeCell := fun i => sourceTranslateCoordinate (a i) (c i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem sourceTranslateCell_add (a b : SourceLatticeShift) (c : LatticeCell) : sourceTranslateCell a (sourceTranslateCell b c) = sourceTranslateCell (a + b) c := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem sourceTranslateCell_zero (c : LatticeCell) : sourceTranslateCell 0 c = c := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem sourceGlobalPlaquetteAxes_translate (a : SourceLatticeShift) (c : LatticeCell) : globalPlaquetteAxes (sourceTranslateCell a c) = globalPlaquetteAxes c := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceTranslatePlaquetteEquiv (a : SourceLatticeShift) :
    GlobalPlaquette ≃ GlobalPlaquette where
  toFun p := ⟨sourceTranslateCell a p.1, by
    rw [sourceGlobalPlaquetteAxes_translate]
    exact p.2⟩
  invFun p := ⟨sourceTranslateCell (-a) p.1, by
    rw [sourceGlobalPlaquetteAxes_translate]
    exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    change sourceTranslateCell (-a) (sourceTranslateCell a p.1) = p.1
    rw [sourceTranslateCell_add]
    simp [sourceTranslateCell_zero]
  right_inv p := by
    apply Subtype.ext
    change sourceTranslateCell a (sourceTranslateCell (-a) p.1) = p.1
    rw [sourceTranslateCell_add]
    simp [sourceTranslateCell_zero]
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceTranslatePlaquettes (a : SourceLatticeShift) (P : Finset GlobalPlaquette) : Finset GlobalPlaquette := P.map (sourceTranslatePlaquetteEquiv a).toEmbedding
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceTranslatePlaquetteIndex (a : SourceLatticeShift) (P : Finset GlobalPlaquette) (p : P) : sourceTranslatePlaquettes a P := ⟨sourceTranslatePlaquetteEquiv a p.1, Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceUntranslateCurvatureAssignment (a : SourceLatticeShift) (P : Finset GlobalPlaquette) (x : sourceTranslatePlaquettes a P → ℤ) : P → ℤ := fun p => x (sourceTranslatePlaquetteIndex a P p)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceTranslateCylinderLaw (S : CurvatureCylinderState) (a : SourceLatticeShift) (P : Finset GlobalPlaquette) : PMF (P → ℤ) := (S.law (sourceTranslatePlaquettes a P)).map (sourceUntranslateCurvatureAssignment a P)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceCubeStateToCylinderState {β : ℝ} {hβ : 0 < β}
    (L : CubeCurvatureLimitState β hβ) : CurvatureCylinderState where
  law := L.law
  consistent := L.consistent
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceShiftBoxSet (n : ℕ) : Set SourceLatticeShift := {a | ∀ i, a i ∈ Set.Icc (-(n : ℤ)) (n : ℤ)}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem sourceShiftBoxSet_finite (n : ℕ) : (sourceShiftBoxSet n).Finite := Set.Finite.pi' (fun _ : Fin 4 => Set.finite_Icc (-(n : ℤ)) (n : ℤ))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceShiftBox (n : ℕ) : Finset SourceLatticeShift := (sourceShiftBoxSet_finite n).toFinset
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceShiftUniform (n : ℕ) : PMF SourceLatticeShift := by
  classical
  letI := (sourceShiftBoxSet_finite n).to_subtype
  let S := {a : SourceLatticeShift // a ∈ sourceShiftBox n}
  let m := Fintype.card S
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨0, by
    rw [sourceShiftBox, Set.Finite.mem_toFinset (sourceShiftBoxSet_finite n)]
    intro i
    simp⟩⟩
  let p : PMF S := PMF.ofFintype (fun _ => ((m : ℕ) : ENNReal)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hm))
      (ENNReal.natCast_ne_top _))
  exact p.map Subtype.val
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceFiniteShiftAverage {α : Type*} [DecidableEq α] (n : ℕ) (f : SourceLatticeShift → PMF α) : PMF α := PMF.bind (sourceShiftUniform n) f
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def sourceAveragedCylinderLaw (S : CurvatureCylinderState) (n : ℕ) (P : Finset GlobalPlaquette) : PMF (P → ℤ) := sourceFiniteShiftAverage n (fun a => sourceTranslateCylinderLaw S a P)
end FroehlichSpencer.FS82.SurfaceInfinite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
abbrev PrimalCoord (R : RectBox4) (i : Fin 4) := Sum (Fin (R.side i + 1)) (Fin (R.side i))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
abbrev PrimalCell (R : RectBox4) := (i : Fin 4) → PrimalCoord R i
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def primalCellDegree (R : RectBox4) (c : PrimalCell R) : ℕ := (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev PrimalLinks (R : RectBox4) := {c : PrimalCell R // primalCellDegree R c = 1}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[instance_reducible] noncomputable def primalLinksFintype (R : RectBox4) : Fintype (PrimalLinks R) := Fintype.ofFinite _
attribute [instance] primalLinksFintype
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev PrimalPlaquettes (R : RectBox4) := {c : PrimalCell R // primalCellDegree R c = 2}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def primalCellEmbedding (R : RectBox4) (c : PrimalCell R) : LatticeCell :=
  fun i => match c i with
    | Sum.inl v => Sum.inl (R.origin i + v.val)
    | Sum.inr e => Sum.inr (R.origin i + e.val)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def primalPlaquetteCurl (R : RectBox4) (θ : PrimalLinks R → ℝ) (p : PrimalPlaquettes R) : ℝ := ∑ ℓ : PrimalLinks R, ((latticeBoundaryBasis (primalCellEmbedding R p.1) (primalCellEmbedding R ℓ.1) : ℤ) : ℝ) * θ ℓ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[instance_reducible] noncomputable def primalPlaquettesFintype (R : RectBox4) : Fintype (PrimalPlaquettes R) := Fintype.ofFinite _
attribute [instance] primalPlaquettesFintype
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def primalVillainLaw (R : RectBox4) (β : ℝ) (_hβ : 0 < β) :
    MeasureTheory.Measure (PrimalLinks R → ℝ) :=
  let μ : MeasureTheory.Measure (PrimalLinks R → ℝ) :=
    (MeasureTheory.Measure.pi fun _ : PrimalLinks R =>
        MeasureTheory.volume.restrict (Set.Ico (-Real.pi) Real.pi)).withDensity
      fun θ => ∏ p : PrimalPlaquettes R,
        ∑' n : ℤ, ENNReal.ofReal
          (Real.exp (-(β / 2) * (primalPlaquetteCurl R θ p + 2 * Real.pi * n) ^ 2))
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
noncomputable def sourcePrimalFieldStrength (R : Surface.RectBox4) (β : ℝ)
    (_hβ : 0 < β) (θ : Surface.PrimalLinks R → ℝ)
    (p : Surface.PrimalPlaquettes R) : ℂ :=
  let φ : ℝ → ℝ := fun x => ∑' n : ℤ,
    Real.exp (-(β / 2) * (x + 2 * Real.pi * n) ^ 2)
  (-Complex.I) * ((deriv φ (Surface.primalPlaquetteCurl R θ p) : ℝ) : ℂ) /
    (φ (Surface.primalPlaquetteCurl R θ p) : ℂ)
end FroehlichSpencer.FS82.SurfaceInfinite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
def centredCube (N : ℕ) (hN : 0 < N) : RectBox4 where
  origin := fun _ => -(N : ℤ)
  side := fun _ => 2 * N
  side_pos := fun _ => Nat.mul_pos Nat.zero_lt_two hN
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
abbrev _root_.FroehlichSpencer.FS82.SurfaceInfinite.sourceC4PrimalFace.match_1.{u_1} : (R : FroehlichSpencer.FS82.Surface.RectBox4) → (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → (motive : FroehlichSpencer.FS82.Surface.DualCoord R i → Sort u_1) → (x : FroehlichSpencer.FS82.Surface.DualCoord R i) → (h_1 : (v : Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) → motive (@Sum.inl.{0, 0} (Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) v)) → (h_2 : (e : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) → motive (@Sum.inr.{0, 0} (Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) e)) → motive x :=
fun (R : FroehlichSpencer.FS82.Surface.RectBox4) (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (motive : FroehlichSpencer.FS82.Surface.DualCoord R i → Sort u_1) (x : FroehlichSpencer.FS82.Surface.DualCoord R i) (h_1 : (v : Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) → motive (@Sum.inl.{0, 0} (Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) v)) (h_2 : (e : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) → motive (@Sum.inr.{0, 0} (Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) e)) => @Sum.casesOn.{u_1, 0, 0} (Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (fun (x : FroehlichSpencer.FS82.Surface.DualCoord R i) => motive x) x (fun (val : Fin (FroehlichSpencer.FS82.Surface.RectBox4.side R i)) => h_1 val) fun (val : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (FroehlichSpencer.FS82.Surface.RectBox4.side R i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) => h_2 val
noncomputable def sourceC4PrimalFace (N : ℕ) (hN : 0 < N)
    (p : GlobalPlaquette)
    (hp : inCube (Surface.centredCube N hN) p) :
    Surface.PrimalPlaquettes (Surface.centredCube N hN) := by
  let R := Surface.centredCube N hN
  let d : Surface.DualPlaquettes R := Classical.choose hp
  let c : Surface.PrimalCell R := fun i =>
    sourceC4PrimalFace.match_1 R i (fun _ => Surface.PrimalCoord R i) (d.1 i)
      (fun v => Sum.inr v) (fun e => Sum.inl e)
  refine ⟨c, ?_⟩
  have haxes :
      (Finset.univ.filter fun i : Fin 4 => (c i).isRight) =
    (Finset.univ.filter fun i : Fin 4 => ¬ (d.1 i).isRight) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases hi : d.1 i <;> simp [c, hi, sourceC4PrimalFace.match_1]
  have hcomp :
      (Finset.univ.filter fun i : Fin 4 => ¬ (d.1 i).isRight) =
    (Finset.univ.filter fun i : Fin 4 => (d.1 i).isRight)ᶜ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  have hcard :
      (Finset.univ.filter fun i : Fin 4 => ¬ (d.1 i).isRight).card =
        4 - Surface.dualCellDegree R d := by
    rw [hcomp, Finset.card_compl]
    change 4 - (Finset.univ.filter (fun i : Fin 4 => (d.1 i).isRight)).card =
      4 - (Finset.univ.filter (fun i : Fin 4 => (d.1 i).isRight)).card
    rfl
  have hd : Surface.dualCellDegree R d = 2 := d.2
  rw [Surface.primalCellDegree, haxes]
  rw [hcard, hd]
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
theorem sourceCurrentEquiv_spec (R : RectBox4) : ∀ α : IntegerDualField R, (sourceCurrentEquiv R (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 = integerLatticeCurl R α := Classical.choose_spec (existsUnique_sourceGaugeClass_closedCurrentEquiv R).exists
end FroehlichSpencer.FS82.SurfaceInfinite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
noncomputable def wilsonLoopObservable (R : RectBox4) (loop : LatticeChain) (θ : PrimalLinks R → ℝ) : ℂ := ∏ ℓ : PrimalLinks R, Complex.exp (Complex.I * (((loop (primalCellEmbedding R ℓ.1) : ℤ) : ℝ) * θ ℓ : ℝ))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
noncomputable def wilsonLoopExpectation (R : RectBox4) (β : ℝ) (hβ : 0 < β) (loop : LatticeChain) : ℂ := ∫ θ, wilsonLoopObservable R loop θ ∂primalVillainLaw R β hβ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def rectangularLoop (L T : ℕ) : LatticeChain := (∑ k ∈ Finset.range L, (Finsupp.single (![Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0, Sum.inl 0] : LatticeCell) (1 : ℤ) - Finsupp.single (![Sum.inr (k : ℤ), Sum.inl (T : ℤ), Sum.inl 0, Sum.inl 0] : LatticeCell) (1 : ℤ))) + ∑ k ∈ Finset.range T, (Finsupp.single (![Sum.inl (L : ℤ), Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0] : LatticeCell) (1 : ℤ) - Finsupp.single (![Sum.inl 0, Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0] : LatticeCell) (1 : ℤ))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable def wilsonCubeSequence (β : ℝ) (hβ : 0 < β) (L T : ℕ) : ℕ → ℝ := fun n => (wilsonLoopExpectation (centredCube (n + 1) (Nat.succ_pos n)) β hβ (rectangularLoop L T)).re
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
namespace FroehlichSpencer.FS82.SurfaceZN
open Classical
abbrev Box4 := Fin 4 → ℕ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
abbrev Cell4 (B : Box4) := (i : Fin 4) → Sum (Fin (B i + 1)) (Fin (B i))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev Chain4 (B : Box4) := Cell4 B →₀ ℤ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def centeredCubeSide (M : ℕ) : Box4 := fun _ => 2 * M
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def coordIsEdge {B : Box4} {i : Fin 4} (x : Sum (Fin (B i + 1)) (Fin (B i))) : Prop := x.isRight
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def cellRankBefore {B : Box4} (c : Cell4 B) (i : Fin 4) : ℕ := (Finset.univ.filter fun j : Fin 4 => j < i ∧ coordIsEdge (c j)).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def cellAxes {B : Box4} (c : Cell4 B) : Finset (Fin 4) := Finset.univ.filter fun i => coordIsEdge (c i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def cellDegree {B : Box4} (c : Cell4 B) : ℕ := (cellAxes c).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def basisChain {B : Box4} (c : Cell4 B) : Chain4 B := Finsupp.single c 1
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def vertexUpdate {B : Box4} (c : Cell4 B) (i : Fin 4) (v : Fin (B i + 1)) : Cell4 B := Function.update c i (Sum.inl v)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def edgeCell {B : Box4} (c : Cell4 B) (i : Fin 4) (t : Fin (B i)) : Cell4 B := Function.update c i (Sum.inr t)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def lowerFace {B : Box4} (c : Cell4 B) (i : Fin 4) (e : Fin (B i)) : Cell4 B := vertexUpdate c i ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def upperFace {B : Box4} (c : Cell4 B) (i : Fin 4) (e : Fin (B i)) : Cell4 B := vertexUpdate c i ⟨e.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def axisBoundaryBasis {B : Box4} (c : Cell4 B) (i : Fin 4) : Chain4 B :=
  match c i with
  | Sum.inl _ => 0
  | Sum.inr e => ((-1 : ℤ) ^ cellRankBefore c i) •
      (basisChain (upperFace c i e) - basisChain (lowerFace c i e))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def axisBoundary {B : Box4} (i : Fin 4) : Chain4 B →ₗ[ℤ] Chain4 B := Finsupp.linearCombination ℤ (axisBoundaryBasis · i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def boundary {B : Box4} : Chain4 B →ₗ[ℤ] Chain4 B := ∑ i : Fin 4, axisBoundary i
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev Links (B : Box4) := {c : Cell4 B // cellDegree c = 1}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev Plaquettes (B : Box4) := {c : Cell4 B // cellDegree c = 2}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev Config (B : Box4) := Links B → UnitAddCircle
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable instance linksFintype (B : Box4) : Fintype (Links B) := Fintype.ofFinite _
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
noncomputable instance plaquettesFintype (B : Box4) : Fintype (Plaquettes B) := Fintype.ofFinite _
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
instance positivePeriodFact : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def circleCosCharacter (n : ℕ) (z : UnitAddCircle) : ℝ := (fourier (T := (1 : ℝ)) (n : ℤ) z).re
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def circleChainPairing {B : Box4} (q : Chain4 B) (f : Cell4 B → UnitAddCircle) : UnitAddCircle := Finsupp.linearCombination ℤ f q
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def primalCircleCochain {B : Box4} (θ : Config B) : Cell4 B → UnitAddCircle := fun c => if h : cellDegree c = 1 then θ ⟨c, h⟩ else 0
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def primalPlaquetteFlux {B : Box4} (θ : Config B) (p : Plaquettes B) : UnitAddCircle := circleChainPairing (boundary (Finsupp.single p.1 1)) (primalCircleCochain θ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def wilsonPlaquetteFactor (β : ℝ) (z : UnitAddCircle) : ℝ := Real.exp (β * circleCosCharacter 1 z)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def wilsonActionDensity {B : Box4} (β : ℝ) (θ : Config B) : ℝ := ∏ p : Plaquettes B, wilsonPlaquetteFactor β (primalPlaquetteFlux θ p)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def pinningNormalizer (N : ℕ) (h : NNReal) : ℝ := ∫ z : UnitAddCircle, Real.exp ((h : ℝ) * circleCosCharacter N z) ∂AddCircle.haarAddCircle
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def pinningNormalization (N : ℕ) (h : NNReal) : ℝ := (pinningNormalizer N h)⁻¹
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def znPinningFactor (N : ℕ) (h : NNReal) (z : UnitAddCircle) : ℝ := pinningNormalization N h * Real.exp ((h : ℝ) * circleCosCharacter N z)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def znPinningDensity {B : Box4} (N : ℕ) (h : NNReal) (θ : Config B) : ℝ := ∏ e : Links B, znPinningFactor N h (θ e)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def finiteZNWeight {B : Box4} (β : ℝ) (N : ℕ) (h : NNReal) (θ : Config B) : ℝ := wilsonActionDensity β θ * znPinningDensity N h θ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def finiteZNPartitionFunction {B : Box4} (β : ℝ) (N : ℕ) (h : NNReal) : ℝ := ∫ θ : Config B, finiteZNWeight β N h θ ∂(Measure.pi fun _ : Links B => AddCircle.haarAddCircle)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev ZNConfig (B : Box4) (N : ℕ) := Links B → Fin N
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def znRoot (N : ℕ) (k : Fin N) : UnitAddCircle := ((k.val : ℝ) / (N : ℝ) : UnitAddCircle)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def znConfigAsCircle {B : Box4} (N : ℕ) (a : ZNConfig B N) : Config B := fun e => znRoot N (a e)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def discreteZNWeight {B : Box4} (β : ℝ) (N : ℕ) (a : ZNConfig B N) : ℝ := wilsonActionDensity β (znConfigAsCircle N a)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def discreteZNPartitionFunction {B : Box4} (β : ℝ) (N : ℕ) : ℝ := ∑ a : ZNConfig B N, discreteZNWeight β N a
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def rectangleBaseCell (B : Box4) : Cell4 B := fun k => Sum.inl ⟨0, Nat.zero_lt_succ (B k)⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def rectangularTwistPlaquetteAt {B : Box4} {L T : ℕ} (x₀ x₁ x₂ x₃ : ℕ) (hx₀ : x₀ + L ≤ B 0 + 1) (hx₁ : x₁ + T ≤ B 1 + 1) (hx₂ : x₂ < B 2) (hx₃ : x₃ < B 3) (i : Fin L) (j : Fin T) : Cell4 B := edgeCell (edgeCell (vertexUpdate (vertexUpdate (rectangleBaseCell B) 0 ⟨x₀ + i.val, by omega⟩) 1 ⟨x₁ + j.val, by omega⟩) 2 ⟨x₂, hx₂⟩) 3 ⟨x₃, hx₃⟩
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def centeredRectangularTwistPlaquette {L T M : ℕ} (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) (i : Fin L) (j : Fin T) : Cell4 (centeredCubeSide M) := rectangularTwistPlaquetteAt (M + 1) (M + 1) M M (by simp [centeredCubeSide]; omega) (by simp [centeredCubeSide]; omega) (by simp [centeredCubeSide]; omega) (by simp [centeredCubeSide]; omega) i j
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def rectangularTwistSheetSupport {B : Box4} {L T : ℕ} (plaq : Fin L → Fin T → Cell4 B) (c : Cell4 B) : Prop := ∃ i j, plaq i j = c
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def centeredRectangularTwistSheet {L T M : ℕ} (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) : Chain4 (centeredCubeSide M) := Finsupp.equivFunOnFinite.symm (fun c => if rectangularTwistSheetSupport (centeredRectangularTwistPlaquette hL hT hM) c then (1 : ℤ) else 0)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def disorderTwistedFlux {B : Box4} (N ξ : ℕ) (S : Chain4 B) (θ : Config B) (p : Plaquettes B) : UnitAddCircle := primalPlaquetteFlux θ p + ((((S p.1 : ℝ) * (ξ : ℝ) / (N : ℝ)) : ℝ) : UnitAddCircle)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def twistedWilsonActionDensity {B : Box4} (β : ℝ) (N ξ : ℕ) (S : Chain4 B) (θ : Config B) : ℝ := ∏ p : Plaquettes B, Real.exp (β * circleCosCharacter 1 (disorderTwistedFlux N ξ S θ p))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def finiteDisorderNumerator {B : Box4} (β : ℝ) (N ξ : ℕ) (h : NNReal) (S : Chain4 B) : ℝ := ∫ θ : Config B, twistedWilsonActionDensity β N ξ S θ * znPinningDensity N h θ ∂(Measure.pi fun _ : Links B => AddCircle.haarAddCircle)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def finiteDisorderExpectation {B : Box4} (β : ℝ) (N ξ : ℕ) (h : NNReal) (S : Chain4 B) : ℝ := finiteDisorderNumerator β N ξ h S / finiteZNPartitionFunction (B := B) β N h
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def finiteCenteredDisorderExpectation (β : ℝ) (N ξ L T M : ℕ) (h : NNReal) (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) : ℝ := finiteDisorderExpectation β N ξ h (centeredRectangularTwistSheet hL hT hM)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def discreteDisorderNumerator {B : Box4} (β : ℝ) (N ξ : ℕ) (S : Chain4 B) : ℝ := ∑ a : ZNConfig B N, twistedWilsonActionDensity β N ξ S (znConfigAsCircle N a)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def discreteDisorderExpectation {B : Box4} (β : ℝ) (N ξ : ℕ) (S : Chain4 B) : ℝ := discreteDisorderNumerator β N ξ S / discreteZNPartitionFunction (B := B) β N
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def discreteCenteredDisorderExpectation (β : ℝ) (N ξ L T M : ℕ) (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) : ℝ := discreteDisorderExpectation β N ξ (centeredRectangularTwistSheet hL hT hM)
end FroehlichSpencer.FS82.SurfaceZN
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
namespace FroehlichSpencer.FS82.SurfaceXY
open Classical
abbrev XYBox (D : ℕ) := Fin D → ℕ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
abbrev XYCoord {D : ℕ} (B : XYBox D) (i : Fin D) := Sum (Fin (B i + 1)) (Fin (B i))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev XYCell {D : ℕ} (B : XYBox D) := (i : Fin D) → XYCoord B i
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev XYChain {D : ℕ} (B : XYBox D) := XYCell B →₀ ℤ
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev xyCoordIsEdge {D : ℕ} {B : XYBox D} {i : Fin D} (x : XYCoord B i) : Prop := x.isRight
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev xyCellRankBefore {D : ℕ} {B : XYBox D} (c : XYCell B) (i : Fin D) : ℕ := (Finset.univ.filter fun j : Fin D => j < i ∧ xyCoordIsEdge (c j)).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev xyCellAxes {D : ℕ} {B : XYBox D} (c : XYCell B) : Finset (Fin D) := Finset.univ.filter fun i : Fin D => xyCoordIsEdge (c i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev xyCellDegree {D : ℕ} {B : XYBox D} (c : XYCell B) : ℕ := (xyCellAxes c).card
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev XYSite {D : ℕ} (B : XYBox D) := {c : XYCell B // xyCellDegree c = 0}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev XYBond {D : ℕ} (B : XYBox D) := {c : XYCell B // xyCellDegree c = 1}
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev XYAngleConfig {D : ℕ} (B : XYBox D) := XYSite B → UnitAddCircle
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyBasisChain {D : ℕ} {B : XYBox D} (c : XYCell B) : XYChain B := Finsupp.single c 1
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyLowerFace {D : ℕ} {B : XYBox D} (c : XYCell B) (i : Fin D) (e : Fin (B i)) : XYCell B := Function.update c i (Sum.inl ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyUpperFace {D : ℕ} {B : XYBox D} (c : XYCell B) (i : Fin D) (e : Fin (B i)) : XYCell B := Function.update c i (Sum.inl ⟨e.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyAxisBoundaryBasis {D : ℕ} {B : XYBox D} (c : XYCell B) (i : Fin D) : XYChain B :=
  match c i with
    | Sum.inl _ => 0
    | Sum.inr e =>
        ((-1 : ℤ) ^ xyCellRankBefore c i) •
          (xyBasisChain (xyUpperFace c i e) - xyBasisChain (xyLowerFace c i e))
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyAxisBoundary {D : ℕ} {B : XYBox D} (i : Fin D) : XYChain B →ₗ[ℤ] XYChain B := Finsupp.linearCombination ℤ (xyAxisBoundaryBasis · i)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyBoundary {D : ℕ} {B : XYBox D} : XYChain B →ₗ[ℤ] XYChain B := ∑ i : Fin D, xyAxisBoundary i
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyCircleChainPairing {D : ℕ} {B : XYBox D} (q : XYChain B) (f : XYCell B → UnitAddCircle) : UnitAddCircle := Finsupp.linearCombination ℤ f q
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyAngleCochain {D : ℕ} {B : XYBox D} (θ : XYAngleConfig B) : XYCell B → UnitAddCircle := fun c => if h : xyCellDegree c = 0 then θ ⟨c, h⟩ else 0
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyBondDifference {D : ℕ} {B : XYBox D} (θ : XYAngleConfig B) (b : XYBond B) : UnitAddCircle := xyCircleChainPairing (xyBoundary (Finsupp.single b.1 1)) (xyAngleCochain θ)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyCircleRepresentative (z : UnitAddCircle) : ℝ :=
  letI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  (AddCircle.equivIoc (1 : ℝ) (-1 / 2) z).1
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyVillainWeight (β : ℝ) (z : UnitAddCircle) : ℝ := ∑' n : ℤ, Real.exp (-(β / 2) * (2 * Real.pi * xyCircleRepresentative z + 2 * Real.pi * (n : ℝ)) ^ 2)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
attribute [-instance] FroehlichSpencer.FS82.SurfaceZN.positivePeriodFact
def xyAngleHaarMeasure {D : ℕ} (B : XYBox D) : Measure (XYAngleConfig B) := Measure.pi (fun _ : XYSite B => AddCircle.haarAddCircle)
attribute [instance] FroehlichSpencer.FS82.SurfaceZN.positivePeriodFact
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyVillainDensity {D : ℕ} {B : XYBox D} (β : ℝ) (θ : XYAngleConfig B) : ℝ := ∏ b : XYBond B, xyVillainWeight β (xyBondDifference θ b)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyVillainPartition {D : ℕ} {B : XYBox D} (β : ℝ) : ℝ := ∫ θ : XYAngleConfig B, xyVillainDensity (B := B) β θ ∂xyAngleHaarMeasure B
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xySpinCharacter {D : ℕ} {B : XYBox D} (θ : XYAngleConfig B) (x y : XYSite B) : ℂ := fourier (T := (1 : ℝ)) 1 (θ x - θ y)
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xySpinDot {D : ℕ} {B : XYBox D} (θ : XYAngleConfig B) (x y : XYSite B) : ℝ := (xySpinCharacter θ x y).re
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xySpinCorrelation {D : ℕ} {B : XYBox D} (β : ℝ) (x y : XYSite B) : ℝ := (∫ θ : XYAngleConfig B, xyVillainDensity (B := B) β θ * xySpinDot θ x y ∂xyAngleHaarMeasure B) / xyVillainPartition (B := B) β
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def xyCubeFamily (D : ℕ) : ℕ → XYBox D := fun N _ => 2 * N
end FroehlichSpencer.FS82.SurfaceXY
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82FiniteVillainDualMomentComparisonLogThick :
∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ, (∀ β : ℝ, β₀.val ≤ β → 0 < cPack β) ∧ Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (nhds 0) ∧ (∀ β : ℝ, β₀.val ≤ β → 0 < betaDoublePrime cPack β ∧ betaDoublePrime cPack β < β) ∧ Tendsto (betaDoublePrime cPack) atTop atTop ∧ ∀ β : ℝ, (hβRange : β₀.val ≤ β) → ∀ R : RectBox4, IsLogThickRectBox4 R → ∀ μ : RealDualField R, ∀ hglobal : μ ∈ GlobalCoClosed R, ∀ hinterior : IsInteriorSupported R μ, ∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε ^ 2 * betaDoublePrime cPack β / 2 * finiteLatticeCovarianceQuadratic R (sourceTestToW R μ hinterior hglobal))) ≤ discreteDualMoment R β (by have := β₀.property; linarith [hβRange]) ε (sourceTestToW R μ hinterior hglobal) ∧ discreteDualMoment R β (by have := β₀.property; linarith [hβRange]) ε (sourceTestToW R μ hinterior hglobal) ≤ ENNReal.ofReal (Real.exp (ε ^ 2 * β / 2 * finiteLatticeCovarianceQuadratic R (sourceTestToW R μ hinterior hglobal))) := by sorry
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
theorem _root_.FSComparator.FS82.source_infiniteVolume_momentComparison : ∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ, (∀ β, β₀.val ≤ β → 0 < cPack β) ∧ Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (𝓝 0) ∧ (∀ β, β₀.val ≤ β → 0 < Surface.betaDoublePrime cPack β ∧ Surface.betaDoublePrime cPack β < β) ∧ Tendsto (Surface.betaDoublePrime cPack) atTop atTop ∧ ∀ β (hβ : β₀.val ≤ β), ∀ L : SurfaceInfinite.CubeCurvatureLimitState β (lt_of_lt_of_le β₀.property hβ), ∀ μ : SurfaceInfinite.GlobalLinkField, Surface.realLatticeBoundary (μ : Surface.RealLatticeChain) = 0 → ∀ σ : SurfaceInfinite.GlobalPlaquetteField, Surface.realLatticeBoundary (σ : Surface.RealLatticeChain) = (μ : Surface.RealLatticeChain) → ∀ t : ℝ, Real.exp ((t ^ 2 * Surface.betaDoublePrime cPack β / 2) * SurfaceInfinite.fourierGreenQuadratic μ) ≤ ∫ x, Real.exp (t * SurfaceInfinite.fillingCurvaturePairing σ x) ∂ (L.law (SurfaceInfinite.fillingCurvatureIndexSet σ)).toMeasure ∧ (∫ x, Real.exp (t * SurfaceInfinite.fillingCurvaturePairing σ x) ∂ (L.law (SurfaceInfinite.fillingCurvatureIndexSet σ)).toMeasure) ≤ Real.exp ((t ^ 2 * β / 2) * SurfaceInfinite.fourierGreenQuadratic μ) := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.source_curvatureCorrelation_nonsummable : ∃ β₁ : {b : ℝ // 0 < b}, ∀ β (hβ : β₁.val ≤ β), ∃ L : SurfaceInfinite.CubeCurvatureLimitState β (lt_of_lt_of_le β₁.property hβ), ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ S : SurfaceInfinite.CurvatureCylinderState, (∀ P x, Tendsto (fun k => (SurfaceInfinite.sourceAveragedCylinderLaw (SurfaceInfinite.sourceCubeStateToCylinderState L) (s k) P x).toReal) atTop (𝓝 ((S.law P x).toReal))) ∧ (∀ a P, SurfaceInfinite.sourceTranslateCylinderLaw S a P = S.law P) ∧ ¬ SurfaceInfinite.AbsolutelySummableCorrelation (SurfaceInfinite.dualCurvatureCorrelation S) := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
theorem _root_.FSComparator.FS82.source_primalFieldStrength_nonsummable : ∃ β₁ : {b : ℝ // 0 < b}, ∀ β (hβ : β₁.val ≤ β), ∃ L : CubeCurvatureLimitState β (lt_of_lt_of_le β₁.property hβ), ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ S : CurvatureCylinderState, (∀ P x, Tendsto (fun k => (sourceAveragedCylinderLaw (sourceCubeStateToCylinderState L) (s k) P x).toReal) atTop (𝓝 ((S.law P x).toReal))) ∧ (∀ a P, sourceTranslateCylinderLaw S a P = S.law P) ∧ (∃ m : ℕ → ℕ, StrictMono m ∧ ∀ d : LatticePoint, d ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k ≥ k₀, ∃ hN : 0 < L.subsequence (m k), ∃ hvalid : ∀ a ∈ sourceShiftBox (s k), ∀ p ∈ pairPlaquettes (a 0, a 1, a 2, a 3) (d + (a 0, a 1, a 2, a 3)), inCube (Surface.centredCube (L.subsequence (m k)) hN) p, dist ((Fintype.card {a : SourceLatticeShift // a ∈ sourceShiftBox (s k)} : ℝ)⁻¹ * ∑ a : {a : SourceLatticeShift // a ∈ sourceShiftBox (s k)}, (∫ θ : Surface.PrimalLinks (Surface.centredCube (L.subsequence (m k)) hN) → ℝ, sourcePrimalFieldStrength _ β (lt_of_lt_of_le β₁.property hβ) θ (sourceC4PrimalFace (L.subsequence (m k)) hN (dualCurvatureAt (a.val 0, a.val 1, a.val 2, a.val 3)) (hvalid a.val a.property _ (by simp [pairPlaquettes]))) * sourcePrimalFieldStrength _ β (lt_of_lt_of_le β₁.property hβ) θ (sourceC4PrimalFace (L.subsequence (m k)) hN (dualCurvatureAt (d + (a.val 0, a.val 1, a.val 2, a.val 3))) (hvalid a.val a.property _ (by simp [pairPlaquettes]))) ∂Surface.primalVillainLaw _ β (lt_of_lt_of_le β₁.property hβ)).re) (dualCurvatureCorrelation S d) < ε) ∧ ¬ AbsolutelySummableCorrelation (dualCurvatureCorrelation S) := by sorry
end FroehlichSpencer.FS82.SurfaceInfinite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82WilsonLoopPerimeterLawCube : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧ ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N → (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧ Real.exp (-(d * ((L : ℝ) + T))) ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open Filter
theorem _root_.FSComparator.FS82.fs82WilsonLoopPerimeterLawCubeLimit : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧ ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → (∃ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T)) ∧ (∀ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T) → Real.exp (-(d * ((L : ℝ) + T))) ≤ x) ∧ Real.exp (-(d * ((L : ℝ) + T))) ≤ Filter.liminf (wilsonCubeSequence β hβ L T) atTop ∧ ∀ w : ℝ, Tendsto (wilsonCubeSequence β hβ L T) atTop (nhds w) → Real.exp (-(d * ((L : ℝ) + T))) ≤ w := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem _root_.FSComparator.FS82.fs82WilsonLoopAreaLawCube : ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N → (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧ 0 ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ∧ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ≤ Real.exp (-(c * ((L : ℝ) * T))) := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem _root_.FSComparator.FS82.fs82WilsonLoopAreaLawCubeLimit : ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → (∃ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T)) ∧ (∀ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T) → 0 ≤ x ∧ x ≤ Real.exp (-(c * ((L : ℝ) * T)))) ∧ Filter.limsup (wilsonCubeSequence β hβ L T) atTop ≤ Real.exp (-(c * ((L : ℝ) * T))) ∧ ∀ w : ℝ, Tendsto (wilsonCubeSequence β hβ L T) atTop (nhds w) → 0 ≤ w ∧ w ≤ Real.exp (-(c * ((L : ℝ) * T))) := by sorry
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem _root_.FSComparator.FS82.fs82WilsonLoopTransitionCube : ∃ β₀ β₁ c : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧ 0 < c ∧ (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N → (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧ 0 ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ∧ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ≤ Real.exp (-(c * ((L : ℝ) * T)))) ∧ (∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∃ d : ℝ, 0 ≤ d ∧ ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N → (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧ Real.exp (-(d * ((L : ℝ) + T))) ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re) := by sorry
end FroehlichSpencer.FS82.Surface
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
namespace FroehlichSpencer.FS82.SurfaceZN
open Classical
theorem _root_.FSComparator.FS82.fs82_zn_disorder_perimeter_root : ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℕ, 1 ≤ ξ → ξ < N → ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (M : ℕ) (hL : L ≤ M) (hT : T ≤ M) (hbox : 0 < M), (∀ h : NNReal, Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤ finiteCenteredDisorderExpectation β N ξ L T M h hL hT hbox) ∧ Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤ discreteCenteredDisorderExpectation β N ξ L T M hL hT hbox := by sorry
end FroehlichSpencer.FS82.SurfaceZN
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
namespace FroehlichSpencer.FS82.SurfaceXY
open Classical
theorem _root_.FSComparator.FS82.fs82_xy_spinCorrelation_root : ∀ D : ℕ, 3 ≤ D → ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β → ∀ N : ℕ, ∀ x y : XYSite (xyCubeFamily D N), Real.exp (-(C / β)) ≤ xySpinCorrelation β x y := by sorry
end FroehlichSpencer.FS82.SurfaceXY
end
end
