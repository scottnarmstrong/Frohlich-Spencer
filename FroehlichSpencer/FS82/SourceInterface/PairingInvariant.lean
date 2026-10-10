module
public import FroehlichSpencer.FS82.SourceInterface.BridgeOperators

public import FroehlichSpencer.FS82.SourceInterface.GaugeAdapter
public import FroehlichSpencer.FS82.Gaussian.LatticeOperator

@[expose] public section

open scoped BigOperators
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SourcePairingInvariant

open Classical

private theorem literalBasisTranspose (c f : LatticeCell) :
    latticeCoboundaryBasis c f = latticeBoundaryBasis f c := by
  change FroehlichSpencer.FS82.Cubical.latticeCoboundaryBasis c f =
    FroehlichSpencer.FS82.Cubical.latticeBoundaryBasis f c
  exact FroehlichSpencer.FS82.Gaussian.latticeCoboundaryBasis_transpose c f

private theorem literalCoboundaryBasis_apply (c e : LatticeCell) :
    (latticeCoboundary (latticeBasis c)) e = latticeCoboundaryBasis c e := by
  simp [latticeCoboundary, latticeBasis, Finsupp.linearCombination_single]

private theorem literalBoundaryBasis_apply (e c : LatticeCell) :
    (latticeBoundary (latticeBasis e)) c = latticeBoundaryBasis e c := by
  simp [latticeBoundary, latticeBasis, Finsupp.linearCombination_single]

private theorem finsetSumChain_apply {α : Type*} (s : Finset α)
    (f : α → RealLatticeChain) (c : LatticeCell) :
    (∑ a ∈ s, f a) c = ∑ a ∈ s, f a c := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha]

private theorem pairing_sbp (p q : RealLatticeChain) :
    (∑ e ∈ q.support, realLatticeCoboundary p e * q e) =
      ∑ v ∈ p.support, p v * realLatticeBoundary q v := by
  classical
  simp only [realLatticeCoboundary, realLatticeBoundary,
    Surface.realifyLatticeLinearMap, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Surface.castLatticeChain]
  simp only [finsetSumChain_apply, Finsupp.smul_apply,
    Finsupp.mapRange_apply, literalCoboundaryBasis_apply,
    literalBoundaryBasis_apply, smul_eq_mul]
  calc
    (∑ e ∈ q.support,
        (∑ v ∈ p.support, p v * latticeCoboundaryBasis v e) * q e) =
      ∑ e ∈ q.support, ∑ v ∈ p.support,
        p v * latticeCoboundaryBasis v e * q e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_mul]
    _ = ∑ v ∈ p.support, ∑ e ∈ q.support,
        p v * latticeCoboundaryBasis v e * q e := by
          rw [Finset.sum_comm]
    _ = ∑ v ∈ p.support, p v *
        (∑ e ∈ q.support, q e * latticeBoundaryBasis e v) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [literalBasisTranspose]
          ring

private theorem realify_cast_latticeChain
    (T : FroehlichSpencer.FS82.Cubical.LatticeChain 4 →ₗ[ℤ]
      FroehlichSpencer.FS82.Cubical.LatticeChain 4)
    (q : FroehlichSpencer.FS82.Cubical.LatticeChain 4) :
    FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap T
        (FroehlichSpencer.FS82.Cubical.castLatticeChain q) =
      FroehlichSpencer.FS82.Cubical.castLatticeChain (T q) := by
  induction q using Finsupp.induction_linear with
  | zero => simp [FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap,
      FroehlichSpencer.FS82.Cubical.castLatticeChain]
  | add q r hq hr =>
      have hcast (a b : FroehlichSpencer.FS82.Cubical.LatticeChain 4) :
          FroehlichSpencer.FS82.Cubical.castLatticeChain (a + b) =
            FroehlichSpencer.FS82.Cubical.castLatticeChain a +
              FroehlichSpencer.FS82.Cubical.castLatticeChain b := by
        ext c
        simp [FroehlichSpencer.FS82.Cubical.castLatticeChain,
          Finsupp.mapRange_apply]
      calc
        _ = FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap T
            (FroehlichSpencer.FS82.Cubical.castLatticeChain q +
              FroehlichSpencer.FS82.Cubical.castLatticeChain r) := by rw [hcast]
        _ = FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap T
            (FroehlichSpencer.FS82.Cubical.castLatticeChain q) +
              FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap T
                (FroehlichSpencer.FS82.Cubical.castLatticeChain r) := map_add _ _ _
        _ = FroehlichSpencer.FS82.Cubical.castLatticeChain (T q) +
              FroehlichSpencer.FS82.Cubical.castLatticeChain (T r) := by rw [hq, hr]
        _ = FroehlichSpencer.FS82.Cubical.castLatticeChain (T (q + r)) := by
          rw [map_add, hcast]
  | single c a =>
      have hsingle : (Finsupp.single c a : FroehlichSpencer.FS82.Cubical.LatticeChain 4) =
          (a : ℤ) • Finsupp.single c 1 := by
        ext x
        simp
      have hcastSmul (b : ℤ) (u : FroehlichSpencer.FS82.Cubical.LatticeChain 4) :
          FroehlichSpencer.FS82.Cubical.castLatticeChain (b • u) =
            (b : ℝ) • FroehlichSpencer.FS82.Cubical.castLatticeChain u := by
        ext x
        simp [FroehlichSpencer.FS82.Cubical.castLatticeChain,
          Finsupp.mapRange_apply, Int.cast_mul]
      have hbase :
          FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap T
              (FroehlichSpencer.FS82.Cubical.castLatticeChain
                (Finsupp.single c (1 : ℤ))) =
            FroehlichSpencer.FS82.Cubical.castLatticeChain
              (T (Finsupp.single c (1 : ℤ))) := by
        simp [FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap,
          FroehlichSpencer.FS82.Cubical.castLatticeChain,
          Finsupp.linearCombination_apply,
          FroehlichSpencer.FS82.Cubical.latticeBasis]
      calc
        _ = FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap T
            ((a : ℝ) • FroehlichSpencer.FS82.Cubical.castLatticeChain
              (Finsupp.single c (1 : ℤ))) := by
            rw [hsingle, hcastSmul]
        _ = (a : ℝ) • FroehlichSpencer.FS82.Cubical.realifyLatticeLinearMap T
            (FroehlichSpencer.FS82.Cubical.castLatticeChain
              (Finsupp.single c (1 : ℤ))) := map_smul _ _ _
        _ = (a : ℝ) • FroehlichSpencer.FS82.Cubical.castLatticeChain
            (T (Finsupp.single c (1 : ℤ))) := by rw [hbase]
        _ = FroehlichSpencer.FS82.Cubical.castLatticeChain
            (T (a • Finsupp.single c (1 : ℤ))) := by
            rw [map_smul]
            exact (hcastSmul a (T (Finsupp.single c (1 : ℤ)))).symm
        _ = FroehlichSpencer.FS82.Cubical.castLatticeChain
            (T (Finsupp.single c a)) := by rw [← hsingle]

private theorem realLatticeCoboundary_cast (q : LatticeChain) :
    Surface.realLatticeCoboundary (Surface.castLatticeChain q) =
      Surface.castLatticeChain
        (FroehlichSpencer.FS82.Cubical.latticeCoboundary q) := by
  exact realify_cast_latticeChain FroehlichSpencer.FS82.Cubical.latticeCoboundary q

private theorem finite_pairing_zero_extension
    (R : RectBox4) (μ : RealDualField R)
    (g : LatticeCell → ℝ) :
    (∑ e : DualLinks R, g (lambdaStarEmbeddingC1 R e) * μ e) =
      ∑ c ∈ (lambdaStarRealZeroExtension R (euclideanToFinsupp R μ)).support,
        g c * (lambdaStarRealZeroExtension R (euclideanToFinsupp R μ)) c := by
  classical
  let q : LambdaStarRealChain R := euclideanToFinsupp R μ
  let emb : DualLinks R ↪ LatticeCell := lambdaStarEmbeddingC1 R
  have hcoeff (e : DualLinks R) : q e = μ e := by
    rfl
  rw [show lambdaStarRealZeroExtension R q = Finsupp.embDomain emb q by
    simpa [emb] using FroehlichSpencer.FS82.Surface.lambdaStarRealZeroExtension_eq_embDomain R q]
  calc
    (∑ e : DualLinks R, g (emb e) * μ e) =
        ∑ e : DualLinks R, g (emb e) * q e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hcoeff]
    _ = q.sum (fun e a => g (emb e) * a) := by
      symm
      exact Finsupp.sum_fintype q (fun e a => g (emb e) * a)
        (by intro e; simp)
    _ = (Finsupp.embDomain emb q).sum (fun c a => g c * a) := by
      rw [Finsupp.sum_embDomain]
    _ = ∑ c ∈ (Finsupp.embDomain emb q).support,
        g c * (Finsupp.embDomain emb q) c := rfl

theorem integerDualPairing_respectsGauge
    (R : RectBox4) (μ : W R) (α α' : IntegerDualField R)
    (h : sourceIntegerGaugeRelation R α α') :
    (∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) =
      ∑ e : DualLinks R, (α' e : ℝ) * (μ : RealDualField R) e := by
  classical
  obtain ⟨γ, hgradientSupport, hshift⟩ := h
  obtain ⟨γ₀, hsameGradient, hfinite, hvertices, _hexterior, _hunique⟩ :=
    normalizeIntegerGaugePotential_connectedExterior_internal R γ hgradientSupport
  let p : LatticeVertices4 →₀ ℤ := Finsupp.ofSupportFinite γ₀ hfinite
  have hpFunction : (p : LatticeVertices4 → ℤ) = γ₀ := by
    exact Finsupp.ofSupportFinite_coe
  have hpotential : (fun x : LatticeVertices4 => p x) = γ₀ := by
    funext x
    exact congrFun hpFunction x
  have hgrad (c : LatticeCell) :
      latticePotentialGradient γ c = latticePotentialGradient (fun x => p x) c := by
    calc
      latticePotentialGradient γ c = latticePotentialGradient γ₀ c :=
        (hsameGradient c).symm
      _ = latticePotentialGradient (fun x => p x) c := by rw [← hpotential]
  have hdiff (e : DualLinks R) :
      (α' e : ℝ) - (α e : ℝ) =
        (latticePotentialGradient (fun x => p x)
          (lambdaStarEmbeddingC1 R e) : ℝ) := by
    rw [hshift e]
    push_cast
    rw [hgrad]
    ring

  let z : LatticeChain := latticePotentialVertexFinsupp p
  let P : RealLatticeChain := Surface.castLatticeChain z
  let q : LambdaStarRealChain R := euclideanToFinsupp R (μ : RealDualField R)
  let Q : RealLatticeChain := lambdaStarRealZeroExtension R q
  have hgradReal (e : DualLinks R) :
      (latticePotentialGradient (fun x => p x)
        (lambdaStarEmbeddingC1 R e) : ℝ) = realLatticeCoboundary P
          (lambdaStarEmbeddingC1 R e) := by
    have hInt := latticePotentialGradient_vertexFinsupp_eq_coboundary p
      (lambdaStarEmbeddingC1 R e)
    rw [show P = Surface.castLatticeChain z by rfl,
      realLatticeCoboundary_cast]
    simpa [Surface.castLatticeChain,
      FroehlichSpencer.FS82.Cubical.castLatticeChain,
      Finsupp.mapRange_apply] using
      congrArg (fun n : ℤ => (n : ℝ)) hInt
  have hpair :
      (∑ e : DualLinks R,
        realLatticeCoboundary P (lambdaStarEmbeddingC1 R e) *
          (μ : RealDualField R) e) =
      ∑ c ∈ Q.support, realLatticeCoboundary P c * Q c := by
    simpa [Q, q] using finite_pairing_zero_extension R
      (μ : RealDualField R) (realLatticeCoboundary P)
  have hdivAtSupport (c : LatticeCell) (hc : c ∈ P.support) :
      Surface.realLatticeBoundary Q c = 0 := by
    have hcP : P c ≠ 0 := Finsupp.mem_support_iff.mp hc
    have hcZ : z c ≠ 0 := by
      intro hz
      apply hcP
      simp [P, z, Surface.castLatticeChain, hz]
    have hzsupp : c ∈ z.support := Finsupp.mem_support_iff.mpr hcZ
    have hcEmb : c ∈ (Finsupp.embDomain latticePotentialVertexEmbedding p).support := by
      simpa [z, latticePotentialVertexFinsupp] using hzsupp
    rw [Finsupp.support_embDomain] at hcEmb
    obtain ⟨x, hxSupport, hxc⟩ := Finset.mem_map.mp hcEmb
    have hpx : p x ≠ 0 := Finsupp.mem_support_iff.mp hxSupport
    obtain ⟨v, hv⟩ := hvertices x hpx
    have hcell : dualCellEmbeddingC1 R v.1 = c := by
      simpa [latticePotentialVertexEmbedding] using hv.trans hxc
    have hW := congrFun (congrArg WithLp.ofLp μ.property) v
    have hW' : Surface.fullLatticeDivergence R (μ : RealDualField R)
        (dualCellEmbeddingC1 R v.1) = 0 := by
      simpa [lambdaStarVertexDivergence, lambdaStarVertexRestriction] using hW
    rw [← hcell]
    change Surface.realLatticeBoundary
      (lambdaStarRealZeroExtension R
        (euclideanToFinsupp R (μ : RealDualField R)))
      (dualCellEmbeddingC1 R v.1) = 0
    simpa [Surface.fullLatticeDivergence, LinearMap.comp_apply] using hW'
  have hsumZero :
      (∑ e : DualLinks R,
        ((α' e : ℝ) - (α e : ℝ)) * (μ : RealDualField R) e) = 0 := by
    calc
      _ = ∑ e : DualLinks R,
          ((α' e : ℝ) - (α e : ℝ)) * (μ : RealDualField R) e := by
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ e : DualLinks R,
          realLatticeCoboundary P (lambdaStarEmbeddingC1 R e) *
            (μ : RealDualField R) e := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hdiff e, hgradReal e]
      _ = ∑ c ∈ Q.support, realLatticeCoboundary P c * Q c := hpair
      _ = 0 := by
        rw [pairing_sbp]
        apply Finset.sum_eq_zero
        intro c hc
        rw [hdivAtSupport c hc]
        simp
  calc
    (∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e) =
        (∑ e : DualLinks R,
          (α' e : ℝ) * (μ : RealDualField R) e) := by
      have hdiffPair :
          (∑ e : DualLinks R, (α' e : ℝ) * (μ : RealDualField R) e) -
            ∑ e : DualLinks R, (α e : ℝ) * (μ : RealDualField R) e = 0 := by
        calc
          _ = ∑ e : DualLinks R,
              ((α' e : ℝ) - (α e : ℝ)) * (μ : RealDualField R) e := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro e he
            ring
          _ = 0 := hsumZero
      exact (sub_eq_zero.mp hdiffPair).symm


end FroehlichSpencer.FS82.SourcePairingInvariant
