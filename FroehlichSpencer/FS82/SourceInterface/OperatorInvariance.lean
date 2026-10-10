module
public import FroehlichSpencer.FS82.Cubical.DualStencil
public import FroehlichSpencer.FS82.SourceInterface.BridgeOperators
public import FroehlichSpencer.FS82.SourceInterface.LiteralSurface
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
public import FroehlichSpencer.FS82.Gaussian.IntegerExactness
public import FroehlichSpencer.FS82.Gaussian.IntegerGauge
public import FroehlichSpencer.FS82.Poisson.TiltedPoisson
public import FroehlichSpencer.FS82.Poisson.GaussianSummable
@[expose] public section
open scoped BigOperators
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.Surface

private theorem latticePotentialGradient_zero (c : LatticeCell) :
    latticePotentialGradient (0 : LatticeVertices4 → ℤ) c = 0 := by
  classical
  by_cases h : (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card = 1
  · simp only [latticePotentialGradient, dite_eq_left h, Pi.zero_apply, sub_self]
    apply Finset.sum_eq_zero
    intro i hi
    cases c i <;> simp
  · simp only [latticePotentialGradient, dite_eq_right h]

private theorem latticePotentialGradient_add (γ η : LatticeVertices4 → ℤ)
    (c : LatticeCell) :
    latticePotentialGradient (γ + η) c =
      latticePotentialGradient γ c + latticePotentialGradient η c := by
  classical
  by_cases h : (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card = 1
  · simp only [latticePotentialGradient, dite_eq_left h]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases hc : c i with
    | inl t => simp
    | inr t => simp only [Pi.add_apply]; ring
  · simp only [latticePotentialGradient, dite_eq_right h, add_zero]

private theorem latticePotentialGradient_neg (γ : LatticeVertices4 → ℤ)
    (c : LatticeCell) :
    latticePotentialGradient (-γ) c = -latticePotentialGradient γ c := by
  classical
  by_cases h : (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card = 1
  · simp only [latticePotentialGradient, dite_eq_left h]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases hc : c i with
    | inl t => simp
    | inr t => simp only [Pi.neg_apply]; ring
  · simp only [latticePotentialGradient, dite_eq_right h, neg_zero]

theorem realLinearMap_linearCombination
    {α : Type*} [DecidableEq α]
    (T : RealLatticeChain →ₗ[ℝ] RealLatticeChain)
    (f : α → RealLatticeChain) (q : α →₀ ℝ) :
    T (Finsupp.linearCombination ℝ f q) =
      Finsupp.linearCombination ℝ (fun a => T (f a)) q := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add, hq, hr]
  | single a z => simp only [Finsupp.linearCombination_single, map_smul]

theorem realLinearCombination_support_witness
    {α : Type*} [DecidableEq α] (f : α → RealLatticeChain)
    (q : α →₀ ℝ) (x : LatticeCell)
    (hx : x ∈ (Finsupp.linearCombination ℝ f q).support) :
    ∃ a ∈ q.support, x ∈ (f a).support := by
  rw [Finsupp.linearCombination_apply] at hx
  have hsum := Finsupp.support_sum hx
  rcases Finset.mem_biUnion.mp hsum with ⟨a, ha, hxa⟩
  refine ⟨a, ha, ?_⟩
  rw [Finsupp.mem_support_iff] at hxa ⊢
  intro hzero
  apply hxa
  simp [hzero]

theorem realLatticeBoundary_single (c : LatticeCell) :
    realLatticeBoundary (Finsupp.single c 1) =
      castLatticeChain (latticeBoundaryBasis c) := by
  simp [realLatticeBoundary, realifyLatticeLinearMap,
    Finsupp.linearCombination_single, latticeBoundary, latticeBasis]

/-- A spatially constant integer potential has zero literal gradient. -/
theorem latticePotentialGradient_const (z : ℤ) (c : LatticeCell) :
    latticePotentialGradient (fun _ : LatticeVertices4 => z) c = 0 := by
  classical
  by_cases h : (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card = 1
  · simp only [latticePotentialGradient, dite_eq_left h]
    apply Finset.sum_eq_zero
    intro i hi
    cases c i <;> simp
  · simp only [latticePotentialGradient, dite_eq_right h]

/-- Subtracting a constant changes no link difference. -/
theorem latticePotentialGradient_sub_const (γ : LatticeVertices4 → ℤ)
    (z : ℤ) (c : LatticeCell) :
    latticePotentialGradient (fun x => γ x - z) c =
      latticePotentialGradient γ c := by
  have hsub : (fun x => γ x - z) = γ + fun _ => -z := by
    funext x
    dsimp
    ring
  rw [hsub, latticePotentialGradient_add, latticePotentialGradient_const]
  simp

/-- Every nonzero vertex coefficient of the boundary of a finite `Λ*`
link field lies in the literal finite vertex halo. -/
theorem lambdaStarRealBoundary_embDomain_eq_zero_outside_halo
    (R : RectBox4) (q : LambdaStarRealChain R) (c : LatticeCell)
    (hc : c ∉ lambdaStarVertexHaloFinset R) :
    realLatticeBoundary
      (Finsupp.embDomain (lambdaStarEmbeddingC1 R) q) c = 0 := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
      rw [Finsupp.embDomain_add, map_add]
      change realLatticeBoundary (Finsupp.embDomain (lambdaStarEmbeddingC1 R) q) c +
        realLatticeBoundary (Finsupp.embDomain (lambdaStarEmbeddingC1 R) r) c = 0
      rw [hq, hr]
      simp
  | single e a =>
      have hnot : c ∉
          (realLatticeBoundary
            (Finsupp.single (lambdaStarEmbeddingC1 R e) 1)).support := by
        intro hmem
        exact hc (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, hmem⟩)
      have hzero :
          realLatticeBoundary
            (Finsupp.single (lambdaStarEmbeddingC1 R e) 1) c = 0 := by
        by_contra hne
        exact hnot (Finsupp.mem_support_iff.mpr hne)
      have hsingle : (Finsupp.single (lambdaStarEmbeddingC1 R e) a :
          RealLatticeChain) = a • Finsupp.single (lambdaStarEmbeddingC1 R e) 1 := by
        ext x
        by_cases hx : x = lambdaStarEmbeddingC1 R e <;> simp [hx]
      rw [Finsupp.embDomain_single, hsingle, map_smul]
      simp [hzero]

/-- A supported term of a lattice link boundary is one of its two endpoint
vertices. -/
theorem latticeBoundaryBasis_support_endpoint (c x : LatticeCell)
    (hx : x ∈ (latticeBoundaryBasis c).support) :
    ∃ i t, c i = Sum.inr t ∧
      (x = latticeUpperFace c i t ∨ x = latticeLowerFace c i t) := by
  classical
  unfold latticeBoundaryBasis at hx
  have hval := Finsupp.mem_support_iff.mp hx
  rw [Finset.sum_apply'] at hval
  obtain ⟨i, hi, htermval⟩ := Finset.exists_ne_zero_of_sum_ne_zero hval
  have hterm := Finsupp.mem_support_iff.mpr htermval
  cases hci : c i with
  | inl v => simp [hci] at hterm
  | inr t =>
      have hterm' :
          (((-1 : ℤ) ^ latticeRankBefore c i) •
            (latticeBasis (latticeUpperFace c i t) -
              latticeBasis (latticeLowerFace c i t))) x ≠ 0 := by
        simpa [hci] using Finsupp.mem_support_iff.mp hterm
      have hdiff :
          (latticeBasis (latticeUpperFace c i t) -
            latticeBasis (latticeLowerFace c i t)) x ≠ 0 := by
        intro hz
        apply hterm'
        rw [Finsupp.smul_apply, hz]
        simp
      have hend : x = latticeUpperFace c i t ∨
          x = latticeLowerFace c i t := by
        by_cases hu : x = latticeUpperFace c i t
        · exact Or.inl hu
        · right
          by_contra hl
          apply hdiff
          simp [latticeBasis, hu, hl]
      exact ⟨i, t, hci, hend⟩

/-- Every endpoint of an interior `Λ*` link stays strictly inside the
rectangular vertex bounds. -/
theorem interiorLink_boundary_endpoint_bounds (R : RectBox4)
    (e : DualLinks R) (he : IsInteriorDualLink R e)
    (x : LatticeCell)
    (hx : x ∈ (latticeBoundaryBasis (lambdaStarEmbeddingC1 R e)).support) :
    ∀ j : Fin 4, ∃ z : ℤ,
      x j = Sum.inl z ∧ R.origin j < z ∧ z < R.origin j + R.side j := by
  classical
  obtain ⟨i, t, hci, hxend⟩ :=
    latticeBoundaryBasis_support_endpoint (lambdaStarEmbeddingC1 R e) x hx
  have hciCoord : dualEmbedCoordC1 R i (e.1 i) = Sum.inr t := hci
  have hright : ∃ u, e.1 i = Sum.inr u := by
    cases hi : e.1 i with
    | inl v =>
        rw [hi] at hciCoord
        simp [dualEmbedCoordC1] at hciCoord
    | inr u => exact ⟨u, rfl⟩
  obtain ⟨u, hu⟩ := hright
  have ht : t = R.origin i + u.val := by
    rw [hu] at hciCoord
    simp [dualEmbedCoordC1] at hciCoord
    have h := hciCoord
    exact h.symm
  have hiAxis : i ∈ dualCellAxes R e.1 := by
    change i ∈ Finset.univ.filter (fun j : Fin 4 => (e.1 j).isRight)
    simp [hu]
  have haxisUnique : ∀ j, j ∈ dualCellAxes R e.1 → j = i := by
    intro j hj
    by_contra hji
    have hij : i ≠ j := Ne.symm hji
    have hsubset : ({i, j} : Finset (Fin 4)) ⊆ dualCellAxes R e.1 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hiAxis
      · exact hj
    have hcard : 2 ≤ (dualCellAxes R e.1).card := by
      calc
        2 = ({i, j} : Finset (Fin 4)).card := by simp [hij]
        _ ≤ (dualCellAxes R e.1).card := Finset.card_le_card hsubset
    rw [← dualCellDegree, e.2] at hcard
    omega
  have hleft : ∀ j, j ≠ i → ∃ v, e.1 j = Sum.inl v := by
    intro j hji
    cases h : e.1 j with
    | inl v => exact ⟨v, rfl⟩
    | inr v =>
        have hj : j ∈ dualCellAxes R e.1 := by
          change j ∈ Finset.univ.filter (fun k : Fin 4 => (e.1 k).isRight)
          simp [h]
        exact (hji (haxisUnique j hj)).elim
  have hiInterior : R.origin i < t ∧ t + 1 < R.origin i + R.side i := by
    have h := he i
    rw [hci] at h
    exact h
  intro j
  by_cases hji : j = i
  · subst j
    rcases hxend with hxup | hxlow
    · refine ⟨t + 1, ?_, ?_, ?_⟩
      · simp [hxup, latticeUpperFace]
      · omega
      · omega
    · refine ⟨t, ?_, ?_, ?_⟩
      · simp [hxlow, latticeLowerFace]
      · exact hiInterior.1
      · omega
  · obtain ⟨v, hv⟩ := hleft j hji
    have hbounds :
        R.origin j < R.origin j + (v.val : ℤ) + 1 ∧
        R.origin j + (v.val : ℤ) + 1 < R.origin j + R.side j := by
      have h := he j
      have hcoord : (lambdaStarEmbeddingC1 R e) j =
          Sum.inl (R.origin j + (v.val : ℤ) + 1) := by
        change dualEmbedCoordC1 R j (e.1 j) = _
        rw [hv]
        rfl
      rw [hcoord] at h
      simpa using h
    refine ⟨R.origin j + (v.val : ℤ) + 1, ?_, hbounds.1, hbounds.2⟩
    rcases hxend with hxup | hxlow
    · rw [hxup]
      change Function.update (lambdaStarEmbeddingC1 R e) i
        (Sum.inl (t + 1)) j = _
      rw [Function.update_of_ne hji]
      simp [lambdaStarEmbeddingC1, dualCellEmbeddingC1, dualEmbedCoordC1, hv]
    · rw [hxlow]
      change Function.update (lambdaStarEmbeddingC1 R e) i
        (Sum.inl t) j = _
      rw [Function.update_of_ne hji]
      simp [lambdaStarEmbeddingC1, dualCellEmbeddingC1, dualEmbedCoordC1, hv]

/-- An endpoint of an interior link is represented by the literal finite
dual-vertex carrier. -/
theorem interiorLink_boundary_endpoint_isDualVertex (R : RectBox4)
    (e : DualLinks R) (he : IsInteriorDualLink R e)
    (x : LatticeCell)
    (hx : x ∈ (latticeBoundaryBasis (lambdaStarEmbeddingC1 R e)).support) :
    ∃ v : DualVertices R, dualCellEmbeddingC1 R v.1 = x := by
  classical
  have hb := interiorLink_boundary_endpoint_bounds R e he x hx
  let z : LatticeVertices4 := fun j => Classical.choose (hb j)
  have hz (j : Fin 4) :
      x j = Sum.inl (z j) ∧ R.origin j < z j ∧
        z j < R.origin j + R.side j := Classical.choose_spec (hb j)
  let c : DualCell R := fun j =>
    Sum.inl ⟨Int.toNat (z j - R.origin j - 1), by
      have hzj := hz j
      have hnonneg : 0 ≤ z j - R.origin j - 1 := by omega
      have hlt : z j - R.origin j - 1 < (R.side j : ℤ) := by omega
      have hnat : Int.toNat (z j - R.origin j - 1) < R.side j := by
        have hltcast :
            ((Int.toNat (z j - R.origin j - 1) : ℕ) : ℤ) <
              (R.side j : ℤ) := by
          rw [Int.toNat_of_nonneg hnonneg]
          exact hlt
        exact_mod_cast hltcast
      exact hnat⟩
  have hcdegree : dualCellDegree R c = 0 := by
    simp [dualCellDegree, dualCellAxes, c]
  refine ⟨⟨c, hcdegree⟩, ?_⟩
  funext j
  have hzj := hz j
  have hnonneg : 0 ≤ z j - R.origin j - 1 := by omega
  have hcast : ((Int.toNat (z j - R.origin j - 1) : ℕ) : ℤ) =
      z j - R.origin j - 1 := Int.toNat_of_nonneg hnonneg
  have hcoord :
      dualEmbedCoordC1 R j (c j) = Sum.inl (z j) := by
    change Sum.inl
        (R.origin j + (Int.toNat (z j - R.origin j - 1) : ℤ) + 1) =
      Sum.inl (z j)
    apply congrArg Sum.inl
    calc
      R.origin j + (Int.toNat (z j - R.origin j - 1) : ℤ) + 1 =
          R.origin j + (z j - R.origin j - 1) + 1 := by
            rw [Int.toNat_of_nonneg hnonneg]
      _ = z j := by omega
  rw [hzj.1]
  exact hcoord

/-- The full divergence of an interior-supported link field is supported on
the literal finite dual vertices. -/
theorem interiorFullDivergence_support_dualVertex (R : RectBox4)
    (μ : RealDualField R) (hμ : IsInteriorSupported R μ)
    (x : LatticeCell)
    (hx : x ∈ (fullLatticeDivergence R μ).support) :
    ∃ v : DualVertices R, dualCellEmbeddingC1 R v.1 = x := by
  classical
  let q : LambdaStarRealChain R := euclideanToFinsupp R μ
  have hrepr : fullLatticeDivergence R μ =
      Finsupp.linearCombination ℝ
        (fun e : DualLinks R =>
          realLatticeBoundary
            (Finsupp.single (lambdaStarEmbeddingC1 R e) 1)) q := by
    change realLatticeBoundary (lambdaStarRealZeroExtension R q) = _
    change realLatticeBoundary
        (Finsupp.linearCombination ℝ
          (fun e : DualLinks R =>
            Finsupp.single (lambdaStarEmbeddingC1 R e) 1) q) = _
    rw [realLinearMap_linearCombination]
  have hx' : x ∈ (Finsupp.linearCombination ℝ
      (fun e : DualLinks R =>
        realLatticeBoundary
          (Finsupp.single (lambdaStarEmbeddingC1 R e) 1)) q).support := by
    rw [← hrepr]
    exact hx
  obtain ⟨e, heq, hxe⟩ := realLinearCombination_support_witness _ q x hx'
  have hcoeff : q e = μ e := by
    simp [q, euclideanToFinsupp]
  have hμe : μ e ≠ 0 := by
    rw [← hcoeff]
    exact Finsupp.mem_support_iff.mp heq
  have hxeInt : x ∈ (latticeBoundaryBasis (lambdaStarEmbeddingC1 R e)).support := by
    rw [Finsupp.mem_support_iff] at hxe ⊢
    intro hzero
    apply hxe
    rw [realLatticeBoundary_single]
    simp [castLatticeChain, hzero]
  exact interiorLink_boundary_endpoint_isDualVertex R e (hμ e hμe) x hxeInt

/-- The finite halo restriction detects vanishing of the full divergence of a
literal zero-extended `Λ*` field. -/
theorem latticeDivergence_eq_zero_iff_full_internal (R : RectBox4)
    (μ : RealDualField R) :
    lambdaStarVertexHaloRestriction R (fullLatticeDivergence R μ) = 0 ↔
      fullLatticeDivergence R μ = 0 := by
  constructor
  · intro h
    apply Finsupp.ext
    intro c
    by_cases hc : c ∈ lambdaStarVertexHaloFinset R
    · have hval := congrFun
        (congrArg WithLp.ofLp h) ⟨c, hc⟩
      simpa [lambdaStarVertexHaloRestriction] using hval
    · have hsupp := lambdaStarRealBoundary_embDomain_eq_zero_outside_halo R
        (euclideanToFinsupp R μ) c hc
      have hdiv : fullLatticeDivergence R μ c = 0 := by
        change realLatticeBoundary
          (lambdaStarRealZeroExtension R (euclideanToFinsupp R μ)) c = 0
        rw [FroehlichSpencer.FS82.Surface.lambdaStarRealZeroExtension_eq_embDomain]
        exact hsupp
      exact hdiv
  · intro h
    simp [h]

/-- For interior-supported tests, full-lattice co-closedness is equivalent to
the source finite-vertex `W` condition. -/
theorem interiorSupported_coClosed_iff_internal (R : RectBox4)
    (μ : RealDualField R) (hμ : IsInteriorSupported R μ) :
    μ ∈ GlobalCoClosed R ↔ μ ∈ W R := by
  change fullLatticeDivergence R μ = 0 ↔
    lambdaStarVertexDivergence R μ = 0
  constructor
  · intro h
    simp [lambdaStarVertexDivergence, lambdaStarVertexRestriction, h]
    ext v
    rfl
  · intro hW
    apply Finsupp.ext
    intro c
    by_cases hc : ∃ v : DualVertices R, dualCellEmbeddingC1 R v.1 = c
    · obtain ⟨v, hv⟩ := hc
      have hval : fullLatticeDivergence R μ
          (dualCellEmbeddingC1 R v.1) = 0 := by
        have h' := congrFun (congrArg WithLp.ofLp hW) v
        simpa [lambdaStarVertexDivergence,
          lambdaStarVertexRestriction] using h'
      change fullLatticeDivergence R μ c = 0
      rw [← hv]
      exact hval
    · by_contra hne
      have hmem : c ∈ (fullLatticeDivergence R μ).support :=
        Finsupp.mem_support_iff.mpr hne
      obtain ⟨v, hv⟩ := interiorFullDivergence_support_dualVertex
        R μ hμ c hmem
      exact hc ⟨v, hv⟩


theorem latticePotentialGradient_edge_formula (γ : LatticeVertices4 → ℤ)
    (x : LatticeVertices4) (i : Fin 4) (t : ℤ) :
    latticePotentialGradient γ
        (latticeEdgeCell (latticePotentialVertexCell x) i t) =
      γ (Function.update x i (t + 1)) - γ (Function.update x i t) := by
  classical
  have haxes :
      (Finset.univ.filter fun j : Fin 4 =>
        (latticeEdgeCell (latticePotentialVertexCell x) i t j).isRight) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hji : j = i
    · subst j
      simp [latticeEdgeCell]
    · change (Function.update (latticePotentialVertexCell x) i
        (Sum.inr t) j).isRight = true ↔ j = i
      rw [Function.update_of_ne hji]
      simp [hji, latticePotentialVertexCell]
  have hdegree :
      (Finset.univ.filter fun j : Fin 4 =>
        (latticeEdgeCell (latticePotentialVertexCell x) i t j).isRight).card = 1 := by
    rw [haxes]
    simp
  unfold latticePotentialGradient
  rw [dite_eq_left hdegree]
  have hsum :
      (∑ j : Fin 4, match
        (latticeEdgeCell (latticePotentialVertexCell x) i t) j with
        | Sum.inl _ => 0
        | Sum.inr s =>
            γ (fun k => if k = j then s + 1 else
              Sum.elim id id ((latticeEdgeCell (latticePotentialVertexCell x) i t) k)) -
            γ (fun k => if k = j then s else
              Sum.elim id id ((latticeEdgeCell (latticePotentialVertexCell x) i t) k))) =
      γ (Function.update x i (t + 1)) - γ (Function.update x i t) := by
    rw [Finset.sum_eq_single i]
    · have hup :
          (fun k => if k = i then t + 1 else
            Sum.elim id id
              (Function.update (latticePotentialVertexCell x) i (Sum.inr t) k)) =
            Function.update x i (t + 1) := by
        funext k
        by_cases hki : k = i
        · subst k
          simp
        · simp [latticePotentialVertexCell, hki]
      have hlow :
          (fun k => if k = i then t else
            Sum.elim id id
              (Function.update (latticePotentialVertexCell x) i (Sum.inr t) k)) =
            Function.update x i t := by
        funext k
        by_cases hki : k = i
        · subst k
          simp
        · simp [latticePotentialVertexCell, hki]
      simp only [latticeEdgeCell, Function.update_self]
      rw [hup, hlow]
    · intro j hj hji
      simp [latticeEdgeCell, latticePotentialVertexCell,
        Function.update_of_ne hji]
    · simp
  exact hsum

/-- A left coordinate of a literal `Λ*` link is a finite dual-vertex
coordinate. -/
theorem lambdaStarLink_left_coordinate_bounds (R : RectBox4)
    (e : DualLinks R) (k : Fin 4) (z : ℤ)
    (hz : (lambdaStarEmbeddingC1 R e) k = Sum.inl z) :
    R.origin k < z ∧ z ≤ R.origin k + R.side k := by
  cases hk : e.1 k with
  | inl v =>
      have hz' : R.origin k + (v.val : ℤ) + 1 = z := by
        simpa [lambdaStarEmbeddingC1, dualCellEmbeddingC1,
          dualEmbedCoordC1, hk] using hz
      have hv : v.val < R.side k := v.isLt
      omega
  | inr v =>
      simp [lambdaStarEmbeddingC1, dualCellEmbeddingC1,
        dualEmbedCoordC1, hk] at hz

/-- An edge with a fixed exterior coordinate cannot be in the finite
`Λ*` link carrier, so a supported potential has zero difference there. -/
theorem latticePotentialGradient_zero_of_outside_coordinate
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R))
    (x : LatticeVertices4) (i k : Fin 4) (t : ℤ) (hki : k ≠ i)
    (hout : x k ≤ R.origin k ∨ R.origin k + R.side k < x k) :
    latticePotentialGradient γ
        (latticeEdgeCell (latticePotentialVertexCell x) i t) = 0 := by
  by_contra hne
  obtain ⟨e, heq⟩ := hsupp _ hne
  have hcoord : (lambdaStarEmbeddingC1 R e) k = Sum.inl (x k) := by
    rw [heq]
    simp [latticeEdgeCell, latticePotentialVertexCell, hki]
  have hb := lambdaStarLink_left_coordinate_bounds R e k (x k) hcoord
  rcases hout with hlo | hhi
  · omega
  · omega

/-- Along any coordinate line with a fixed exterior coordinate, the
potential is constant. The proof walks one lattice edge at a time. -/
theorem latticePotential_eq_update_of_outside_coordinate
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R))
    (x : LatticeVertices4) (i k : Fin 4) (hki : k ≠ i)
    (hout : x k ≤ R.origin k ∨ R.origin k + R.side k < x k)
    (a b : ℤ) :
    γ (Function.update x i a) = γ (Function.update x i b) := by
  have hzero (t : ℤ) :=
    latticePotentialGradient_zero_of_outside_coordinate
      R γ hsupp x i k t hki hout
  have hforward : ∀ a b : ℤ, a ≤ b →
      γ (Function.update x i a) = γ (Function.update x i b) := by
    intro a b hab
    let P : (n : ℤ) → a ≤ n → Prop := fun n _ =>
      γ (Function.update x i a) = γ (Function.update x i n)
    have hP : P b hab := Int.leInduction (m := a) (motive := P)
      (by rfl)
      (by
        intro n hn ih
        change γ (Function.update x i a) = γ (Function.update x i n) at ih
        change γ (Function.update x i a) = γ (Function.update x i (n + 1))
        have hgrad := latticePotentialGradient_edge_formula γ x i n
        have hzero' := hzero n
        rw [hgrad] at hzero'
        calc
          γ (Function.update x i a) = γ (Function.update x i n) := ih
          _ = γ (Function.update x i (n + 1)) := by omega)
      b hab
    exact hP
  by_cases hab : a ≤ b
  · exact hforward a b hab
  · have hba : b ≤ a := by omega
    exact (hforward b a hba).symm


/-- Any two potentials on the same exterior coordinate hyperplane have the
same value when their gradients are supported on `Λ*`. -/
theorem latticePotential_eq_of_same_exterior_coordinate_aux
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R))
    (k : Fin 4) :
    ∀ (S : Finset (Fin 4)) (x y : LatticeVertices4),
      (∀ j, j ∈ S ↔ x j ≠ y j) → k ∉ S → x k = y k →
      (x k ≤ R.origin k ∨ R.origin k + R.side k < x k) → γ x = γ y := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro x y hS hkS hxy hout
      have hxyFun : x = y := by
        funext j
        by_contra hne
        have hj : j ∈ (∅ : Finset (Fin 4)) := (hS j).mpr hne
        simp at hj
      simp [hxyFun]
  | @insert a S ha ih =>
      intro x y hS hkS hxy hout
      have hka : k ≠ a := by
        intro h
        subst a
        exact hkS (Finset.mem_insert.mpr (Or.inl rfl))
      have hkS' : k ∉ S := by
        intro hk
        exact hkS (Finset.mem_insert.mpr (Or.inr hk))
      have hxa : x a ≠ y a := (hS a).mp (Finset.mem_insert.mpr (Or.inl rfl))
      let x' : LatticeVertices4 := Function.update x a (y a)
      have hout' : x' k ≤ R.origin k ∨ R.origin k + R.side k < x' k := by
        simpa [x', Function.update_of_ne hka] using hout
      have hxy' : x' k = y k := by
        simpa [x', Function.update_of_ne hka] using hxy
      have hS' : ∀ j, j ∈ S ↔ x' j ≠ y j := by
        intro j
        by_cases hja : j = a
        · subst j
          simp [x', ha]
        · have hjS : j ∈ S ↔ x j ≠ y j := by
            have hj := hS j
            simpa [Finset.mem_insert, hja] using hj
          simpa [x', Function.update_of_ne hja] using hjS
      have hstep : γ x = γ x' := by
        simpa [x'] using
          latticePotential_eq_update_of_outside_coordinate
            R γ hsupp x a k hka hout (x a) (y a)
      exact hstep.trans (ih x' y hS' hkS' hxy' hout')

/-- Any two potentials on the same exterior coordinate hyperplane have the
same value when their gradients are supported on `Λ*`. -/
theorem latticePotential_eq_of_same_exterior_coordinate
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R))
    (k : Fin 4) (x y : LatticeVertices4)
    (hxy : x k = y k)
    (hout : x k ≤ R.origin k ∨ R.origin k + R.side k < x k) :
    γ x = γ y := by
  classical
  let S : Finset (Fin 4) := Finset.univ.filter fun j => x j ≠ y j
  have hS : ∀ j, j ∈ S ↔ x j ≠ y j := by
    intro j
    simp [S]
  have hkS : k ∉ S := by
    simp [S, hxy]
  exact latticePotential_eq_of_same_exterior_coordinate_aux
    R γ hsupp k S x y hS hkS hxy hout


/-- The exterior of the finite dual-vertex rectangle has constant potential.
The path first moves a second coordinate to the lower exterior face, then
uses that face as a firewall while moving the remaining coordinates. -/
theorem latticePotential_eq_origin_of_exterior
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R))
    (x : LatticeVertices4) (hx : isExteriorVertex R x) :
    γ x = γ (fun i => R.origin i) := by
  obtain ⟨i, hi⟩ := hx
  let j : Fin 4 := if i = 0 then 1 else 0
  have hj : j ≠ i := by
    by_cases hi0 : i = 0
    · subst i
      norm_num [j]
    · intro hji
      have h0 : (0 : Fin 4) = i := by simpa [j, hi0] using hji
      exact hi0 h0.symm
  let y : LatticeVertices4 := Function.update x j (R.origin j)
  have hxi : x i = y i := by
    simp [y, Function.update_of_ne hj.symm]
  have hyi := latticePotential_eq_of_same_exterior_coordinate
    R γ hsupp i x y hxi hi
  have hyj : y j = R.origin j := by simp [y]
  have hyext : y j ≤ R.origin j ∨ R.origin j + R.side j < y j := by
    rw [hyj]
    exact Or.inl le_rfl
  have hyo := latticePotential_eq_of_same_exterior_coordinate
    R γ hsupp j y (fun k => R.origin k) hyj hyext
  exact hyi.trans hyo

/-- Subtracting the exterior constant normalizes the potential without
changing its literal gradient. -/
def normalizeIntegerGaugePotential (R : RectBox4)
    (γ : LatticeVertices4 → ℤ) : LatticeVertices4 → ℤ :=
  fun x => γ x - γ (fun i => R.origin i)

theorem normalizeIntegerGaugePotential_gradient (R : RectBox4)
    (γ : LatticeVertices4 → ℤ) (c : LatticeCell) :
    latticePotentialGradient (normalizeIntegerGaugePotential R γ) c =
      latticePotentialGradient γ c := by
  exact latticePotentialGradient_sub_const γ (γ (fun i => R.origin i)) c

theorem normalizeIntegerGaugePotential_zero_on_exterior
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R))
    (x : LatticeVertices4) (hx : isExteriorVertex R x) :
    normalizeIntegerGaugePotential R γ x = 0 := by
  simp [normalizeIntegerGaugePotential,
    latticePotential_eq_origin_of_exterior R γ hsupp x hx]


/-- The potential is constant along any coordinate line when its full
literal gradient vanishes. -/
theorem latticePotential_eq_update_of_zero_gradient
    (γ : LatticeVertices4 → ℤ)
    (hzero : ∀ c : LatticeCell, latticePotentialGradient γ c = 0)
    (x : LatticeVertices4) (i : Fin 4) (a b : ℤ) :
    γ (Function.update x i a) = γ (Function.update x i b) := by
  have hforward : ∀ a b : ℤ, a ≤ b →
      γ (Function.update x i a) = γ (Function.update x i b) := by
    intro a b hab
    let P : (n : ℤ) → a ≤ n → Prop := fun n _ =>
      γ (Function.update x i a) = γ (Function.update x i n)
    have hP : P b hab := Int.leInduction (m := a) (motive := P)
      (by rfl)
      (by
        intro n hn ih
        change γ (Function.update x i a) = γ (Function.update x i n) at ih
        change γ (Function.update x i a) = γ (Function.update x i (n + 1))
        have hgrad := latticePotentialGradient_edge_formula γ x i n
        have hzero' := hzero (latticeEdgeCell
          (latticePotentialVertexCell x) i n)
        rw [hgrad] at hzero'
        calc
          γ (Function.update x i a) = γ (Function.update x i n) := ih
          _ = γ (Function.update x i (n + 1)) := by omega)
      b hab
    exact hP
  by_cases hab : a ≤ b
  · exact hforward a b hab
  · have hba : b ≤ a := by omega
    exact (hforward b a hba).symm

private theorem latticePotentialGradient_sub (γ η : LatticeVertices4 → ℤ)
    (c : LatticeCell) :
    latticePotentialGradient (fun x => γ x - η x) c =
      latticePotentialGradient γ c - latticePotentialGradient η c := by
  have hfun : (fun x => γ x - η x) = γ + (-η) := by
    funext x
    rfl
  rw [hfun, latticePotentialGradient_add, latticePotentialGradient_neg]
  ring

/-- The closed integer coordinate rectangle is exactly represented by the
literal finite dual-vertex carrier. -/
theorem latticePotentialVertexCell_eq_dualVertex_of_inside
    (R : RectBox4) (x : LatticeVertices4)
    (hbound : ∀ j, R.origin j < x j ∧ x j ≤ R.origin j + R.side j) :
    ∃ v : DualVertices R,
      dualCellEmbeddingC1 R v.1 = latticePotentialVertexCell x := by
  classical
  have hnonneg (j : Fin 4) : 0 ≤ x j - R.origin j - 1 := by
    have hb := hbound j
    omega
  let c : DualCell R := fun j => Sum.inl ⟨
    Int.toNat (x j - R.origin j - 1), by
      have hlt : x j - R.origin j - 1 < (R.side j : ℤ) := by
        have hb := hbound j
        omega
      have hltNat : Int.toNat (x j - R.origin j - 1) < R.side j := by
        have hltCast :
            ((Int.toNat (x j - R.origin j - 1) : ℕ) : ℤ) <
              (R.side j : ℤ) := by
          rw [Int.toNat_of_nonneg (hnonneg j)]
          exact hlt
        exact_mod_cast hltCast
      exact hltNat⟩
  have hcdegree : dualCellDegree R c = 0 := by
    simp [dualCellDegree, dualCellAxes, c]
  refine ⟨⟨c, hcdegree⟩, ?_⟩
  funext j
  have hb := hbound j
  have hn := hnonneg j
  change Sum.inl (R.origin j +
    (Int.toNat (x j - R.origin j - 1) : ℤ) + 1) = Sum.inl (x j)
  congr 1
  rw [Int.toNat_of_nonneg hn]
  omega

/-- The normalized potential has finite support, contained in the literal
finite dual-vertex rectangle. -/
theorem normalizeIntegerGaugePotential_finite_support
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R)) :
    (Set.Finite {x : LatticeVertices4 |
      normalizeIntegerGaugePotential R γ x ≠ 0}) := by
  classical
  let coords : DualVertices R → LatticeVertices4 := fun v j =>
    match v.1 j with
    | Sum.inl u => R.origin j + (u.val : ℤ) + 1
    | Sum.inr _ => R.origin j
  have hsub : {x : LatticeVertices4 |
      normalizeIntegerGaugePotential R γ x ≠ 0} ⊆ Set.range coords := by
    intro x hx
    have hout : ¬ isExteriorVertex R x := by
      intro hext
      have hzero := normalizeIntegerGaugePotential_zero_on_exterior
        R γ hsupp x hext
      exact hx hzero
    have hbound : ∀ j, R.origin j < x j ∧ x j ≤ R.origin j + R.side j := by
      intro j
      have hnot : ¬(x j ≤ R.origin j ∨ R.origin j + R.side j < x j) := by
        intro hj
        exact hout ⟨j, hj⟩
      omega
    obtain ⟨v, hv⟩ := latticePotentialVertexCell_eq_dualVertex_of_inside R x hbound
    refine ⟨v, ?_⟩
    funext j
    dsimp [coords]
    have h := congrFun hv j
    cases hj : v.1 j with
    | inl u =>
        have h' : R.origin j + (u.val : ℤ) + 1 = x j := by
          have htemp := h
          simp [dualCellEmbeddingC1, dualEmbedCoordC1,
            latticePotentialVertexCell, hj] at htemp
          exact htemp
        simp [h']
    | inr e =>
        simp [dualCellEmbeddingC1, dualEmbedCoordC1,
          latticePotentialVertexCell, hj] at h
  exact (Set.finite_range coords).subset hsub


/-- Every nonzero coefficient of the normalized potential is represented by
one of the literal finite dual vertices. -/
theorem normalizeIntegerGaugePotential_supported_on_dualVertices
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R))
    (x : LatticeVertices4)
    (hx : normalizeIntegerGaugePotential R γ x ≠ 0) :
    ∃ v : DualVertices R,
      dualCellEmbeddingC1 R v.1 = latticePotentialVertexCell x := by
  have hout : ¬ isExteriorVertex R x := by
    intro hext
    have hzero := normalizeIntegerGaugePotential_zero_on_exterior
      R γ hsupp x hext
    exact hx hzero
  have hbound : ∀ j, R.origin j < x j ∧ x j ≤ R.origin j + R.side j := by
    intro j
    have hnot : ¬(x j ≤ R.origin j ∨ R.origin j + R.side j < x j) := by
      intro hj
      exact hout ⟨j, hj⟩
    omega
  exact latticePotentialVertexCell_eq_dualVertex_of_inside R x hbound

/-- Connected-exterior normalization for the arbitrary source potential.
The normalized potential is finitely supported on the dual vertices and is
unique among potentials with the same full gradient that vanish on the
exterior. -/
theorem normalizeIntegerGaugePotential_connectedExterior_internal
    (R : RectBox4) (γ : LatticeVertices4 → ℤ)
    (hsupp : ∀ c : LatticeCell, latticePotentialGradient γ c ≠ 0 →
      c ∈ Set.range (lambdaStarEmbeddingC1 R)) :
    ∃ γ₀ : LatticeVertices4 → ℤ,
      (∀ c : LatticeCell, latticePotentialGradient γ₀ c =
        latticePotentialGradient γ c) ∧
      Set.Finite {x : LatticeVertices4 | γ₀ x ≠ 0} ∧
      (∀ x : LatticeVertices4, γ₀ x ≠ 0 →
        ∃ v : DualVertices R,
          dualCellEmbeddingC1 R v.1 = latticePotentialVertexCell x) ∧
      (∀ x : LatticeVertices4, isExteriorVertex R x → γ₀ x = 0) ∧
      ∀ η : LatticeVertices4 → ℤ,
        (∀ c : LatticeCell, latticePotentialGradient η c =
          latticePotentialGradient γ c) →
        (∀ x : LatticeVertices4, isExteriorVertex R x → η x = 0) →
        η = γ₀ := by
  refine ⟨normalizeIntegerGaugePotential R γ,
    normalizeIntegerGaugePotential_gradient R γ,
    normalizeIntegerGaugePotential_finite_support R γ hsupp,
    ?_, ?_, ?_⟩
  · intro x hx
    exact normalizeIntegerGaugePotential_supported_on_dualVertices
      R γ hsupp x hx
  · intro x hx
    exact normalizeIntegerGaugePotential_zero_on_exterior R γ hsupp x hx
  · intro η hη hηzero
    have hdiff : ∀ c : LatticeCell,
        latticePotentialGradient (fun x => η x -
          normalizeIntegerGaugePotential R γ x) c = 0 := by
      intro c
      rw [latticePotentialGradient_sub]
      rw [hη c, normalizeIntegerGaugePotential_gradient R γ c]
      ring
    funext x
    let i : Fin 4 := 0
    let y : LatticeVertices4 := Function.update x i (R.origin i)
    have hyext : isExteriorVertex R y := by
      refine ⟨i, ?_⟩
      simp [y, i]
    have hline := latticePotential_eq_update_of_zero_gradient
      (fun z => η z - normalizeIntegerGaugePotential R γ z) hdiff x i
      (x i) (R.origin i)
    have hdiffxy : η x - normalizeIntegerGaugePotential R γ x =
        η y - normalizeIntegerGaugePotential R γ y := by
      simpa [y, i] using hline
    have hyzero : η y - normalizeIntegerGaugePotential R γ y = 0 := by
      rw [hηzero y hyext,
        normalizeIntegerGaugePotential_zero_on_exterior R γ hsupp y hyext]
      simp
    have hxzero : η x - normalizeIntegerGaugePotential R γ x = 0 :=
      hdiffxy.trans hyzero
    exact sub_eq_zero.mp hxzero

theorem sourceIntegerGaugeRelation_isEquivalence_internal (R : RectBox4) :
    Equivalence (sourceIntegerGaugeRelation R) := by
  constructor
  · intro α
    refine ⟨0, ?_, ?_⟩
    · intro c hc
      exact (hc (latticePotentialGradient_zero c)).elim
    · intro e
      simp [latticePotentialGradient_zero]
  · intro α α' hα
    obtain ⟨γ, hsupp, hshift⟩ := hα
    refine ⟨-γ, ?_, ?_⟩
    · intro c hc
      apply hsupp
      simpa [latticePotentialGradient_neg] using hc
    · intro e
      calc
        α e = α e + latticePotentialGradient γ (lambdaStarEmbeddingC1 R e) +
            latticePotentialGradient (-γ) (lambdaStarEmbeddingC1 R e) := by
          rw [latticePotentialGradient_neg]
          ring
        _ = α' e + latticePotentialGradient (-γ) (lambdaStarEmbeddingC1 R e) := by
          rw [hshift e]
  · intro α α' α'' hαα' hα'α''
    obtain ⟨γ, hsuppγ, hshiftγ⟩ := hαα'
    obtain ⟨η, hsuppη, hshiftη⟩ := hα'α''
    refine ⟨γ + η, ?_, ?_⟩
    · intro c hc
      by_contra hnot
      have hγzero : latticePotentialGradient γ c = 0 := by
        by_contra hγ
        exact hnot (hsuppγ c hγ)
      have hηzero : latticePotentialGradient η c = 0 := by
        by_contra hη
        exact hnot (hsuppη c hη)
      rw [latticePotentialGradient_add, hγzero, hηzero] at hc
      exact hc rfl
    · intro e
      calc
        α'' e = α' e + latticePotentialGradient η (lambdaStarEmbeddingC1 R e) :=
          hshiftη e
        _ = α e + latticePotentialGradient γ (lambdaStarEmbeddingC1 R e) +
            latticePotentialGradient η (lambdaStarEmbeddingC1 R e) := by
          rw [hshiftγ e]
        _ = α e + latticePotentialGradient (γ + η)
            (lambdaStarEmbeddingC1 R e) := by
          rw [latticePotentialGradient_add]
          ring

end FroehlichSpencer.FS82.Surface
end
