/- Finite source operator and physical lattice stencil comparison. -/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeBridgeHigher
public import FroehlichSpencer.FS82.Cubical.DualStencil

/-!
# The sign-conjugated lattice operator

Operator bridge for the physical half-lattice embedding and orientation signs.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open FroehlichSpencer.FS82.Cubical
open scoped InnerProductSpace

theorem latticeRankBefore_eq_of_eq_away_axis {d : ℕ} (c f : LatticeCell d)
    (i : Fin d) (h : ∀ j, j ≠ i → c j = f j) :
    latticeRankBefore c i = latticeRankBefore f i := by
  unfold latticeRankBefore
  congr 1
  ext j
  by_cases hj : j < i
  · have hji : j ≠ i := ne_of_lt hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h j hji]
  · simp [Finset.mem_filter, hj]

theorem latticeCoboundaryBasis_transpose {d : ℕ}
    (c f : LatticeCell d) :
    latticeCoboundaryBasis c f = latticeBoundaryBasis f c := by
  classical
  simp only [latticeCoboundaryBasis, latticeBoundaryBasis,
    Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl t =>
    cases hfi : f i with
    | inl s =>
        have hne₀ : latticeEdgeCell c i (t - 1) ≠ f := by
          intro h
          have hc := congrFun h i
          simp [latticeEdgeCell, hfi] at hc
        have hne₁ : latticeEdgeCell c i t ≠ f := by
          intro h
          have hc := congrFun h i
          simp [latticeEdgeCell, hfi] at hc
        have hne₀' : Function.update c i (Sum.inr (t - 1)) ≠ f := by
          simpa [latticeEdgeCell] using hne₀
        have hne₁' : Function.update c i (Sum.inr t) ≠ f := by
          simpa [latticeEdgeCell] using hne₁
        simp [latticeBasis, 
          latticeEdgeCell, hne₀', hne₁']
    | inr s =>
        by_cases hrest : ∀ j, j ≠ i → c j = f j
        · have hupper : Function.update c i (Sum.inr (t - 1)) = f ↔
              Function.update f i (Sum.inl (s + 1)) = c := by
            rw [Function.update_eq_iff, Function.update_eq_iff]
            constructor
            · rintro ⟨hv, hcoords⟩
              have hv' : t - 1 = s := by simpa [hfi] using hv
              refine ⟨?_, ?_⟩
              · rw [hci]
                exact congrArg Sum.inl (by omega)
              · intro j hj
                exact (hcoords j hj).symm
            · rintro ⟨hv, hcoords⟩
              have hv' : s + 1 = t := by simpa [hci] using hv
              refine ⟨?_, ?_⟩
              · rw [hfi]
                exact congrArg Sum.inr (by omega)
              · intro j hj
                exact (hcoords j hj).symm
          have hlower : Function.update c i (Sum.inr t) = f ↔
              Function.update f i (Sum.inl s) = c := by
            rw [Function.update_eq_iff, Function.update_eq_iff]
            constructor
            · rintro ⟨hv, hcoords⟩
              have hv' : t = s := by simpa [hfi] using hv
              refine ⟨?_, ?_⟩
              · rw [hci]
                exact congrArg Sum.inl hv'.symm
              · intro j hj
                exact (hcoords j hj).symm
            · rintro ⟨hv, hcoords⟩
              have hv' : s = t := by simpa [hci] using hv
              refine ⟨?_, ?_⟩
              · rw [hfi]
                exact congrArg Sum.inr hv'.symm
              · intro j hj
                exact (hcoords j hj).symm
          have hrank := latticeRankBefore_eq_of_eq_away_axis c f i hrest
          simp [latticeBasis, Finsupp.single_apply, 
            latticeEdgeCell, latticeUpperFace, latticeLowerFace,
            hupper, hlower, hrank]
        · push Not at hrest
          obtain ⟨j, hji, hneq⟩ := hrest
          have hneL₀ : Function.update c i (Sum.inr (t - 1)) ≠ f := by
            intro h
            have h' := congrFun h j
            simp [hji] at h'
            exact hneq h'
          have hneL₁ : Function.update c i (Sum.inr t) ≠ f := by
            intro h
            have h' := congrFun h j
            simp [hji] at h'
            exact hneq h'
          have hneR₀ : Function.update f i (Sum.inl (s + 1)) ≠ c := by
            intro h
            have h' := congrFun h j
            simp [hji] at h'
            exact hneq h'.symm
          have hneR₁ : Function.update f i (Sum.inl s) ≠ c := by
            intro h
            have h' := congrFun h j
            simp [hji] at h'
            exact hneq h'.symm
          simp [latticeBasis, 
            latticeEdgeCell, latticeUpperFace, latticeLowerFace,
            hneL₀, hneL₁, hneR₀, hneR₁]
  | inr t =>
    cases hfi : f i with
    | inl s => simp
    | inr s =>
        have hne₀ : Function.update f i (Sum.inl (s + 1)) ≠ c := by
          intro h
          have hc := congrFun h i
          simp [hci] at hc
        have hne₁ : Function.update f i (Sum.inl s) ≠ c := by
          intro h
          have hc := congrFun h i
          simp [hci] at hc
        simp [latticeBasis, 
          latticeUpperFace, latticeLowerFace, hne₀, hne₁]

theorem latticeDeltaD_basis_sum_of_coboundary_coefficients {d : ℕ}
    (input output : LatticeCell d) :
    latticeDeltaD (latticeBasis input) output =
      (latticeCoboundaryBasis input).sum fun c a =>
        a * latticeCoboundaryBasis output c := by
  rw [latticeDeltaD, LinearMap.comp_apply]
  rw [latticeCoboundary_basis, latticeBoundary,
    Finsupp.linearCombination_apply, Finsupp.sum_apply]
  change (latticeCoboundaryBasis input).sum
      (fun c a => a • latticeBoundaryBasis c output) = _
  apply Finsupp.sum_congr
  intro c hc
  rw [smul_eq_mul, latticeCoboundaryBasis_transpose output c]

theorem realLatticeDeltaD_basis_pairing {d : ℕ}
    (input output : LatticeCell d) :
    realLatticeDeltaD (Finsupp.single input (1 : ℝ)) output =
      (castLatticeChain (latticeCoboundaryBasis input)).sum fun c a =>
        a * castLatticeChain (latticeCoboundaryBasis output) c := by
  rw [realLatticeDeltaD_basis_localCoefficient,
    ← latticeDeltaD_basis_localCoefficient,
    latticeDeltaD_basis_sum_of_coboundary_coefficients]
  rw [castLatticeChain,
    Finsupp.sum_mapRange_index (h0 := by intro c; simp)]
  simp [castLatticeChain, Finsupp.mapRange_apply, Int.cast_mul]

theorem inner_finsuppToEuclidean_single {α : Type*} [Fintype α] [DecidableEq α]
    (x : EuclideanSpace ℝ α) (a : α) :
    inner ℝ x (finsuppToEuclidean (Finsupp.single a (1 : ℝ))) = x a := by
  rw [PiLp.inner_apply]
  simp [finsuppToEuclidean_apply, Finsupp.single_apply]

theorem inner_finsuppToEuclidean {α : Type*} [Fintype α] [DecidableEq α]
    (q r : α →₀ ℝ) :
    inner ℝ (finsuppToEuclidean q) (finsuppToEuclidean r) =
      ∑ a, q a * r a := by
  rw [PiLp.inner_apply]
  simp [finsuppToEuclidean_apply]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem latticeCellOrientationSign_sq (c : LatticeCell 4) :
    latticeCellOrientationSign c ^ 2 = 1 := by
  unfold latticeCellOrientationSign axisSetOrientationSign
  rw [pow_two, ← mul_pow]
  norm_num

theorem latticeOrientationSignTwist_involutive (q : RealLatticeChain 4) :
    latticeOrientationSignTwist (latticeOrientationSignTwist q) = q := by
  ext c
  rw [latticeOrientationSignTwist_apply, latticeOrientationSignTwist_apply]
  calc
    latticeCellOrientationSign c *
        (latticeCellOrientationSign c * q c) =
      (latticeCellOrientationSign c * latticeCellOrientationSign c) * q c := by
        ring
    _ = q c := by
      rw [← pow_two, latticeCellOrientationSign_sq]
      simp

theorem latticeOrientationSignTwist_embDomain {α : Type*} [DecidableEq α]
    (e : α ↪ LatticeCell 4) (q : α →₀ ℝ) :
    latticeOrientationSignTwist (Finsupp.embDomain e q) =
      Finsupp.embDomain e
        (Finsupp.linearCombination ℝ
          (fun a : α => Finsupp.single a
            (latticeCellOrientationSign (e a))) q) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [latticeOrientationSignTwist]
  | add q r hq hr => simp [map_add, hq, hr]
  | single a z =>
      simp [Finsupp.embDomain_single, latticeOrientationSignTwist_single,
        Finsupp.linearCombination_single, mul_comm]

@[simp] theorem sourceDualOneToChain_finsuppToEuclidean {B : SourceBox}
    (q : LambdaStarRealChain B) :
    sourceDualOneToChain (finsuppToEuclidean q) =
      embedDualSubtype sourceDualOneEmbedding q := by
  simp only [sourceDualOneToChain, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean]

theorem sourceDualTMap_single {B : SourceBox} (e : LambdaStarLinks B) (a : ℝ) :
    sourceDualTMap (Finsupp.single e a) =
      Finsupp.single e (dualCellOrientationSign e.1 * a) := by
  ext e'
  by_cases h : e' = e
  · subst e'
    simp [sourceDualTMap, Finsupp.linearCombination_single]
    ring
  · simp [sourceDualTMap, Finsupp.linearCombination_single, h]

theorem dualOrientationSignTwist_embedSourceOne {B : SourceBox}
    (q : LambdaStarRealChain B) :
    dualOrientationSignTwist (embedDualSubtype sourceDualOneEmbedding q) =
      embedDualSubtype sourceDualOneEmbedding (sourceDualTMap q) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [embedDualSubtype, dualOrientationSignTwist, sourceDualTMap]
  | add q r hq hr => simp [map_add, hq, hr]
  | single e a =>
      rw [embedDualSubtype_apply_single, dualOrientationSignTwist_single,
        sourceDualTMap_single, embedDualSubtype_apply_single]
      change Finsupp.single (sourceDualOneEmbedding e)
          (dualCellOrientationSign (sourceDualOneEmbedding e) * a) =
        Finsupp.single (sourceDualOneEmbedding e)
          (dualCellOrientationSign e.1 * a)
      rfl

theorem sourcePhysicalDualZeroExtension_embedSourceOne {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : LambdaStarRealChain B) :
    sourcePhysicalDualZeroExtension origin (embedDualSubtype sourceDualOneEmbedding q) =
      lambdaStarRealZeroExtension (B := B) origin q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [embedDualSubtype, sourcePhysicalDualZeroExtension,
      lambdaStarRealZeroExtension]
  | add q r hq hr => simp [map_add, hq, hr]
  | single e a =>
      rw [embedDualSubtype_apply_single, sourcePhysicalDualZeroExtension_single]
      simp [lambdaStarRealZeroExtension, Finsupp.linearCombination_single,
        sourceDualOneEmbedding, lambdaStarEmbedding]

theorem sourcePhysicalDualZeroExtension_sourceDualTMap {B : SourceBox}
    (origin : Fin 4 → ℤ) (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourcePhysicalDualZeroExtension origin
        (dualOrientationSignTwist (sourceDualOneToChain x)) =
      lambdaStarRealZeroExtension (B := B) origin
        (sourceDualTMap (euclideanToFinsupp x)) := by
  change sourcePhysicalDualZeroExtension origin
      (dualOrientationSignTwist
        (embedDualSubtype sourceDualOneEmbedding (euclideanToFinsupp x))) = _
  rw [dualOrientationSignTwist_embedSourceOne,
    sourcePhysicalDualZeroExtension_embedSourceOne]

theorem sourceDualD₁_physical_coefficient {B : SourceBox}
    (origin : Fin 4 → ℤ) (x : EuclideanSpace ℝ (SourceDualOneCells B))
    (f : SourceDualTwoCells B) :
    sourceDualD₁ x f = dualCellOrientationSign f.1 *
      sourceRealLatticeCoboundary
        (lambdaStarRealZeroExtension (B := B) origin
          (sourceDualTMap (euclideanToFinsupp x)))
        (dualCellEmbedding origin f.1) := by
  have hbridge := congrArg
    (fun q : RealLatticeChain 4 =>
      q (dualCellEmbedding origin f.1))
    (sourceDualD₁_physical_bridge origin x)
  have hleft :
      sourcePhysicalDualZeroExtension origin
        (sourceDualTwoToChain (sourceDualD₁ x))
        (dualCellEmbedding origin f.1) = sourceDualD₁ x f := by
    change sourcePhysicalDualZeroExtension origin
        (embedDualSubtype sourceDualTwoEmbedding
          (euclideanToFinsupp (sourceDualD₁ x)))
        (dualCellEmbedding origin f.1) = _
    rw [sourcePhysicalDualZeroExtension_embedDualSubtype]
    change Finsupp.linearCombination ℝ
        (fun a : SourceDualTwoCells B => Finsupp.single
          (sourcePhysicalDualTwoEmbedding origin a) (1 : ℝ))
        (euclideanToFinsupp (sourceDualD₁ x))
        (sourcePhysicalDualTwoEmbedding origin f) = _
    rw [linearCombination_single_embedding_hits]
    simp [euclideanToFinsupp_apply]
  have hright :
      latticeOrientationSignTwist
          (sourceRealLatticeCoboundary
            (sourcePhysicalDualZeroExtension origin
              (dualOrientationSignTwist (sourceDualOneToChain x))))
          (dualCellEmbedding origin f.1) =
        dualCellOrientationSign f.1 *
          sourceRealLatticeCoboundary
            (lambdaStarRealZeroExtension (B := B) origin
              (sourceDualTMap (euclideanToFinsupp x)))
            (dualCellEmbedding origin f.1) := by
    rw [latticeOrientationSignTwist_apply,
      sourcePhysicalDualZeroExtension_sourceDualTMap,
      latticeCellOrientationSign_physical]
  rw [hleft, hright] at hbridge
  exact hbridge

theorem sourceDualTwoToChain_physical_vanishes_outside {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (y : EuclideanSpace ℝ (SourceDualTwoCells B))
    (c : LatticeCell 4)
    (hc : c ∉ Set.range (sourcePhysicalDualTwoEmbedding (B := B) origin)) :
    sourcePhysicalDualZeroExtension origin (sourceDualTwoToChain y) c = 0 := by
  rw [show sourceDualTwoToChain y =
      embedDualSubtype sourceDualTwoEmbedding (euclideanToFinsupp y) by
    simp [sourceDualTwoToChain, LinearMap.comp_apply]]
  rw [sourcePhysicalDualZeroExtension_embedDualSubtype]
  exact linearCombination_single_embedding_vanishes
    (sourcePhysicalDualTwoEmbedding (B := B) origin) _ c hc

theorem linearCombination_single_eq_embDomain {α β : Type*}
    [DecidableEq β] (e : α ↪ β) (q : α →₀ ℝ) :
    Finsupp.linearCombination ℝ
      (fun a : α => Finsupp.single (e a) (1 : ℝ)) q =
      Finsupp.embDomain e q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [Finsupp.linearCombination]
  | add q r hq hr =>
      rw [map_add, hq, hr]
      ext b
      simp [Finsupp.embDomain_apply]
  | single a z =>
      simp [Finsupp.linearCombination_single, Finsupp.embDomain_single]

theorem sourceDualTwoPhysicalChain_repr {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (y : EuclideanSpace ℝ (SourceDualTwoCells B)) :
    sourcePhysicalDualZeroExtension origin (sourceDualTwoToChain y) =
      Finsupp.embDomain (sourcePhysicalDualTwoEmbedding (B := B) origin)
        (euclideanToFinsupp y) := by
  rw [show sourceDualTwoToChain y =
      embedDualSubtype sourceDualTwoEmbedding (euclideanToFinsupp y) by
    simp [sourceDualTwoToChain, LinearMap.comp_apply]]
  rw [sourcePhysicalDualZeroExtension_embedDualSubtype]
  simpa [sourcePhysicalDualTwoEmbedding] using
    (linearCombination_single_eq_embDomain
      (Function.Embedding.trans sourceDualTwoEmbedding
        (Cubical.dualCellEmbedding origin)) (euclideanToFinsupp y))

theorem sourceDualD₁_coboundary_as_signed_embedding {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourceRealLatticeCoboundary
      (sourcePhysicalDualZeroExtension origin
        (dualOrientationSignTwist (sourceDualOneToChain x))) =
      latticeOrientationSignTwist
        (sourcePhysicalDualZeroExtension origin
          (sourceDualTwoToChain (sourceDualD₁ x))) := by
  have h := congrArg latticeOrientationSignTwist
    (sourceDualD₁_physical_bridge origin x)
  rw [latticeOrientationSignTwist_involutive] at h
  exact h.symm


theorem embDomain_pair_sum {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (q r : α →₀ ℝ) :
    (Finsupp.embDomain e q).sum (fun b a =>
      a * Finsupp.embDomain e r b) =
        q.sum (fun x a => a * r x) := by
  rw [Finsupp.embDomain_eq_mapDomain e q,
    Finsupp.sum_mapDomain_index (h_zero := by intro b; simp)
      (h_add := by intro b x y; ring)]
  simp [Finsupp.embDomain_apply]

@[expose] def latticeChainPair (q r : RealLatticeChain 4) : ℝ :=
  q.sum fun c a => a * r c

theorem latticeChainPair_smul_left (a : ℝ) (q r : RealLatticeChain 4) :
    latticeChainPair (a • q) r = a * latticeChainPair q r := by
  unfold latticeChainPair
  rw [Finsupp.sum_smul_index (h0 := by intro c; simp)]
  calc
    q.sum (fun c x => (a * x) * r c) =
        a • q.sum (fun c x => x * r c) := by
      change (∑ c ∈ q.support, (a * q c) * r c) =
        a • (∑ c ∈ q.support, q c * r c)
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      simp only [smul_eq_mul]
      ring
    _ = a * q.sum (fun c x => x * r c) := by simp [smul_eq_mul]

theorem latticeChainPair_smul_right (a : ℝ) (q r : RealLatticeChain 4) :
    latticeChainPair q (a • r) = a * latticeChainPair q r := by
  unfold latticeChainPair
  change q.sum (fun c x => x * (a * r c)) = _
  calc
    q.sum (fun c x => x * (a * r c)) =
        q.sum (fun c x => a • (x * r c)) := by
      apply Finsupp.sum_congr
      intro c hc
      simp only [smul_eq_mul]
      ring
    _ = a • q.sum (fun c x => x * r c) := by
      change (∑ c ∈ q.support, a • (q c * r c)) =
        a • (∑ c ∈ q.support, q c * r c)
      rw [Finset.smul_sum]
    _ = a * q.sum (fun c x => x * r c) := by simp [smul_eq_mul]

@[expose] noncomputable def sourceDualTwoPhysicalSignTwist {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : SourceDualTwoCells B →₀ ℝ) :
    SourceDualTwoCells B →₀ ℝ :=
  Finsupp.linearCombination ℝ
    (fun f : SourceDualTwoCells B => Finsupp.single f
      (latticeCellOrientationSign (sourcePhysicalDualTwoEmbedding origin f))) q

theorem sourceDualTwoPhysicalSignTwist_apply {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : SourceDualTwoCells B →₀ ℝ)
    (f : SourceDualTwoCells B) :
    sourceDualTwoPhysicalSignTwist origin q f =
      latticeCellOrientationSign (sourcePhysicalDualTwoEmbedding origin f) * q f := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [sourceDualTwoPhysicalSignTwist]
  | add q r hq hr =>
      change (Finsupp.linearCombination ℝ
        (fun f : SourceDualTwoCells B => Finsupp.single f
          (latticeCellOrientationSign (sourcePhysicalDualTwoEmbedding origin f)))
        (q + r)) f = _
      rw [map_add]
      change (sourceDualTwoPhysicalSignTwist origin q) f +
        (sourceDualTwoPhysicalSignTwist origin r) f =
        latticeCellOrientationSign (sourcePhysicalDualTwoEmbedding origin f) * (q + r) f
      rw [hq, hr, Finsupp.add_apply]
      ring
  | single a z =>
      by_cases h : a = f
      · subst a
        simp [sourceDualTwoPhysicalSignTwist,
          Finsupp.linearCombination_single, mul_comm]
      · simp [sourceDualTwoPhysicalSignTwist,
          Finsupp.linearCombination_single, h]

theorem sourceDualTwoPhysicalSignTwist_pair {B : SourceBox}
    (origin : Fin 4 → ℤ) (q r : SourceDualTwoCells B →₀ ℝ) :
    (sourceDualTwoPhysicalSignTwist origin q).sum
        (fun f a => a * sourceDualTwoPhysicalSignTwist origin r f) =
      q.sum (fun f a => a * r f) := by
  classical
  rw [Finsupp.sum_fintype (h := by intro f; simp),
    Finsupp.sum_fintype (h := by intro f; simp)]
  apply Finset.sum_congr rfl
  intro f hf
  rw [sourceDualTwoPhysicalSignTwist_apply,
    sourceDualTwoPhysicalSignTwist_apply]
  calc
    latticeCellOrientationSign (sourcePhysicalDualTwoEmbedding origin f) * q f *
        (latticeCellOrientationSign (sourcePhysicalDualTwoEmbedding origin f) * r f) =
      (latticeCellOrientationSign (sourcePhysicalDualTwoEmbedding origin f) ^ 2) *
        (q f * r f) := by ring
    _ = q f * r f := by
      rw [latticeCellOrientationSign_sq]
      ring

theorem sourceDualD₁_pairing_eq_latticeCoboundaryPair {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (x y : EuclideanSpace ℝ (SourceDualOneCells B)) :
    inner ℝ (sourceDualD₁ x) (sourceDualD₁ y) =
      latticeChainPair
        (sourceRealLatticeCoboundary
          (lambdaStarRealZeroExtension (B := B) origin
            (sourceDualTMap (euclideanToFinsupp x))))
        (sourceRealLatticeCoboundary
          (lambdaStarRealZeroExtension (B := B) origin
            (sourceDualTMap (euclideanToFinsupp y)))) := by
  let q := euclideanToFinsupp (sourceDualD₁ x)
  let r := euclideanToFinsupp (sourceDualD₁ y)
  have hx : finsuppToEuclidean q = sourceDualD₁ x := by
    ext f
    simp [q]
  have hy : finsuppToEuclidean r = sourceDualD₁ y := by
    ext f
    simp [r]
  have hinner : inner ℝ (sourceDualD₁ x) (sourceDualD₁ y) =
      q.sum (fun f a => a * r f) := by
    rw [← hx, ← hy, inner_finsuppToEuclidean]
    exact (Finsupp.sum_fintype q (fun f a => a * r f)
      (by intro f; simp)).symm
  have hdX :
      sourceRealLatticeCoboundary
          (lambdaStarRealZeroExtension (B := B) origin
            (sourceDualTMap (euclideanToFinsupp x))) =
        latticeOrientationSignTwist
          (Finsupp.embDomain
            (sourcePhysicalDualTwoEmbedding (B := B) origin) q) := by
    rw [← sourcePhysicalDualZeroExtension_sourceDualTMap]
    rw [sourceDualD₁_coboundary_as_signed_embedding,
      sourceDualTwoPhysicalChain_repr]
  have hdY :
      sourceRealLatticeCoboundary
          (lambdaStarRealZeroExtension (B := B) origin
            (sourceDualTMap (euclideanToFinsupp y))) =
        latticeOrientationSignTwist
          (Finsupp.embDomain
            (sourcePhysicalDualTwoEmbedding (B := B) origin) r) := by
    rw [← sourcePhysicalDualZeroExtension_sourceDualTMap]
    rw [sourceDualD₁_coboundary_as_signed_embedding,
      sourceDualTwoPhysicalChain_repr]
  rw [hinner, hdX, hdY]
  unfold latticeChainPair
  rw [latticeOrientationSignTwist_embDomain,
    latticeOrientationSignTwist_embDomain,
    embDomain_pair_sum]
  exact (sourceDualTwoPhysicalSignTwist_pair origin q r).symm

theorem euclideanCoordinate_eq_inner_single {α : Type*} [Fintype α]
    [DecidableEq α] (x : EuclideanSpace ℝ α) (a : α) :
    x a = inner ℝ (finsuppToEuclidean (Finsupp.single a (1 : ℝ))) x := by
  rw [PiLp.inner_apply]
  simp [finsuppToEuclidean_apply, Finsupp.single_apply]

theorem sourceDualFiniteOperator_basis_coefficient {B : SourceBox}
    (origin : Fin 4 → ℤ) (input output : SourceDualOneCells B) :
    sourceDualFiniteOperator (B := B)
        (finsuppToEuclidean (Finsupp.single input (1 : ℝ))) output =
      dualCellOrientationSign (sourceDualOneEmbedding output) *
        dualCellOrientationSign (sourceDualOneEmbedding input) *
          (latticeDeltaDLocalCoefficient
            (lambdaStarEmbedding (B := B) origin input)
            (lambdaStarEmbedding (B := B) origin output) : ℝ) := by
  let bIn : EuclideanSpace ℝ (SourceDualOneCells B) :=
    finsuppToEuclidean (Finsupp.single input (1 : ℝ))
  let bOut : EuclideanSpace ℝ (SourceDualOneCells B) :=
    finsuppToEuclidean (Finsupp.single output (1 : ℝ))
  have hcoord := euclideanCoordinate_eq_inner_single
    (sourceDualFiniteOperator (bIn)) output
  unfold sourceDualFiniteOperator at hcoord
  rw [LinearMap.comp_apply] at hcoord
  rw [LinearMap.adjoint_inner_right] at hcoord
  have hpair := sourceDualD₁_pairing_eq_latticeCoboundaryPair origin bIn bOut
  have htwistIn : sourceDualTMap (euclideanToFinsupp bIn) =
      Finsupp.single input (dualCellOrientationSign (sourceDualOneEmbedding input)) := by
    simp [bIn, sourceDualTMap_single, euclideanToFinsupp_finsuppToEuclidean,
      sourceDualOneEmbedding]
  have htwistOut : sourceDualTMap (euclideanToFinsupp bOut) =
      Finsupp.single output (dualCellOrientationSign (sourceDualOneEmbedding output)) := by
    simp [bOut, sourceDualTMap_single, euclideanToFinsupp_finsuppToEuclidean,
      sourceDualOneEmbedding]
  have hdin :
      sourceRealLatticeCoboundary
        (lambdaStarRealZeroExtension (B := B) origin
          (Finsupp.single input (dualCellOrientationSign (sourceDualOneEmbedding input)))) =
        (dualCellOrientationSign (sourceDualOneEmbedding input)) •
          castLatticeChain
            (latticeCoboundaryBasis (lambdaStarEmbedding (B := B) origin input)) := by
    rw [lambdaStarRealZeroExtension]
    simp [sourceRealLatticeCoboundary_single,
      Finsupp.linearCombination_single]
  have hdout :
      sourceRealLatticeCoboundary
        (lambdaStarRealZeroExtension (B := B) origin
          (Finsupp.single output (dualCellOrientationSign (sourceDualOneEmbedding output)))) =
        (dualCellOrientationSign (sourceDualOneEmbedding output)) •
          castLatticeChain
            (latticeCoboundaryBasis (lambdaStarEmbedding (B := B) origin output)) := by
    rw [lambdaStarRealZeroExtension]
    simp [sourceRealLatticeCoboundary_single,
      Finsupp.linearCombination_single]
  have hbase :
      latticeChainPair
          (castLatticeChain (latticeCoboundaryBasis
            (lambdaStarEmbedding (B := B) origin input)))
          (castLatticeChain (latticeCoboundaryBasis
            (lambdaStarEmbedding (B := B) origin output))) =
        (latticeDeltaDLocalCoefficient
          (lambdaStarEmbedding (B := B) origin input)
          (lambdaStarEmbedding (B := B) origin output) : ℝ) := by
    calc
      latticeChainPair
          (castLatticeChain (latticeCoboundaryBasis
            (lambdaStarEmbedding (B := B) origin input)))
          (castLatticeChain (latticeCoboundaryBasis
            (lambdaStarEmbedding (B := B) origin output))) =
          realLatticeDeltaD
            (Finsupp.single (lambdaStarEmbedding (B := B) origin input) (1 : ℝ))
            (lambdaStarEmbedding (B := B) origin output) := by
        rw [realLatticeDeltaD_basis_pairing]
        rfl
      _ = _ := by rw [realLatticeDeltaD_basis_localCoefficient]
  calc
    sourceDualFiniteOperator (bIn) output = inner ℝ (sourceDualD₁ bOut)
        (sourceDualD₁ bIn) := by
      simpa [sourceDualFiniteOperator, LinearMap.comp_apply, bIn, bOut] using hcoord
    _ = inner ℝ (sourceDualD₁ bIn) (sourceDualD₁ bOut) := by
      exact real_inner_comm _ _
    _ = latticeChainPair
        (sourceRealLatticeCoboundary
          (lambdaStarRealZeroExtension (B := B) origin
            (Finsupp.single input
              (dualCellOrientationSign (sourceDualOneEmbedding input)))))
        (sourceRealLatticeCoboundary
          (lambdaStarRealZeroExtension (B := B) origin
            (Finsupp.single output
              (dualCellOrientationSign (sourceDualOneEmbedding output))))) := by
      simpa [bIn, bOut, htwistIn, htwistOut, sourceDualTMap_single,
        sourceDualOneEmbedding] using hpair
    _ = (dualCellOrientationSign (sourceDualOneEmbedding output)) *
        (dualCellOrientationSign (sourceDualOneEmbedding input)) *
          latticeChainPair
            (castLatticeChain (latticeCoboundaryBasis
              (lambdaStarEmbedding (B := B) origin input)))
            (castLatticeChain (latticeCoboundaryBasis
              (lambdaStarEmbedding (B := B) origin output))) := by
      rw [hdin, hdout, latticeChainPair_smul_left, latticeChainPair_smul_right]
      ring
    _ = _ := by rw [hbase]

/-- The source finite adjoint product is the C2 conjugate of the full-lattice
stencil compressed to the physical `Λ*` link set. -/
theorem sourceDualFiniteOperator_eq_conj_piLambdaStarDeltaDReal
    {B : SourceBox} (origin : Fin 4 → ℤ) :
    sourceDualFiniteOperator (B := B) =
      (finsuppToEuclidean).comp
        ((sourceDualTMap (B := B)).comp
          ((Cubical.piLambdaStarDeltaDReal (B := B) origin).comp
            ((sourceDualTMap (B := B)).comp euclideanToFinsupp))) := by
  let rhs : EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) :=
    (finsuppToEuclidean).comp
      ((sourceDualTMap (B := B)).comp
          ((Cubical.piLambdaStarDeltaDReal (B := B) origin).comp
            ((sourceDualTMap (B := B)).comp euclideanToFinsupp)))
  have hbasis (input : SourceDualOneCells B) :
      sourceDualFiniteOperator (B := B)
          (finsuppToEuclidean (Finsupp.single input (1 : ℝ))) =
        rhs (finsuppToEuclidean (Finsupp.single input (1 : ℝ))) := by
    ext output
    rw [sourceDualFiniteOperator_basis_coefficient (origin := origin)]
    simp only [rhs, LinearMap.comp_apply, euclideanToFinsupp_finsuppToEuclidean,
      finsuppToEuclidean_apply]
    rw [sourceDualTMap_single]
    simp only [mul_one]
    rw [sourceDualTMap_apply, Cubical.piLambdaStarDeltaDReal_single_apply]
    rw [show sourceDualOneEmbedding input = input.1 from rfl,
      show sourceDualOneEmbedding output = output.1 from rfl]
    ring
  have hcomp : (sourceDualFiniteOperator (B := B)).comp finsuppToEuclidean =
      rhs.comp finsuppToEuclidean := by
    apply LinearMap.ext
    intro q
    induction q using Finsupp.induction_linear with
    | zero => simp [rhs]
    | add q r hq hr => simp only [map_add, hq, hr]
    | single input a =>
        rw [show Finsupp.single input a = a • Finsupp.single input (1 : ℝ) by
          ext e
          simp]
        simp only [map_smul]
        exact congrArg (fun z => a • z) (hbasis input)
  apply LinearMap.ext
  intro x
  have hx : finsuppToEuclidean (euclideanToFinsupp x) = x := by
    ext e
    simp
  rw [← hx]
  exact congrArg (fun F : (SourceDualOneCells B →₀ ℝ) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) => F (euclideanToFinsupp x)) hcomp

end FroehlichSpencer.FS82.Gaussian

end
