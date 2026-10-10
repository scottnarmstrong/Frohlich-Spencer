module

public import FroehlichSpencer.FS82.SourceInterface.CarrierIdentities
public import FroehlichSpencer.FS82.SourceInterface.OperatorInvariance
public import FroehlichSpencer.FS82.SourceInterface.SourceOperators
public import FroehlichSpencer.FS82.Gaussian.IntegerExactness
public import FroehlichSpencer.FS82.Gaussian.IntegerGauge

/-!
# FS82 arbitrary-potential gauge adapter
-/

@[expose] public section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.Surface

noncomputable def latticePotentialVertexEmbedding :
    LatticeVertices4 ↪ LatticeCell where
  toFun := latticePotentialVertexCell
  inj' := by
    intro x y h
    funext i
    exact Sum.inl.inj (congrFun h i)

noncomputable def latticePotentialVertexFinsupp
    (p : LatticeVertices4 →₀ ℤ) : LatticeChain :=
  Finsupp.embDomain latticePotentialVertexEmbedding p

theorem latticePotentialVertexFinsupp_eq_zero_of_not_vertex
    (p : LatticeVertices4 →₀ ℤ) (c : LatticeCell)
    (hc : ¬ sourceLatticeVertex c) :
    latticePotentialVertexFinsupp p c = 0 := by
  have hnot : c ∉ Set.range latticePotentialVertexEmbedding := by
    rintro ⟨x, hx⟩
    have hv : sourceLatticeVertex (latticePotentialVertexCell x) := by
      intro i
      simp [latticePotentialVertexCell]
    apply hc
    rw [← hx]
    exact hv
  exact Finsupp.embDomain_of_notMem_range
    latticePotentialVertexEmbedding p c hnot


theorem vertex_edge_equality_lower (x y : LatticeVertices4)
    (i : Fin 4) (t : ℤ) :
    Function.update (latticePotentialVertexCell y) i (Sum.inr (y i - 1)) =
      Function.update (latticePotentialVertexCell x) i (Sum.inr t) ↔
    y = Function.update x i (t + 1) := by
  constructor
  · intro h
    funext j
    by_cases hji : j = i
    · subst j
      have hcoord := congrFun h i
      simp only [Function.update_self] at hcoord
      have hnum : y i - 1 = t := Sum.inr.inj hcoord
      simp only [Function.update_self]
      omega
    · have hcoord := congrFun h j
      rw [Function.update_of_ne hji, Function.update_of_ne hji] at hcoord
      change Sum.inl (y j) = Sum.inl (x j) at hcoord
      have hval : y j = x j := Sum.inl.inj hcoord
      simpa [Function.update_of_ne hji] using hval
  · intro h
    subst y
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update_self]
    · simp [latticePotentialVertexCell, Function.update_of_ne hji]

theorem vertex_edge_equality_upper (x y : LatticeVertices4)
    (i : Fin 4) (t : ℤ) :
    Function.update (latticePotentialVertexCell y) i (Sum.inr (y i)) =
      Function.update (latticePotentialVertexCell x) i (Sum.inr t) ↔
    y = Function.update x i t := by
  constructor
  · intro h
    funext j
    by_cases hji : j = i
    · subst j
      have hcoord := congrFun h i
      simp only [Function.update_self] at hcoord
      simp only [Function.update_self]
      exact Sum.inr.inj hcoord
    · have hcoord := congrFun h j
      rw [Function.update_of_ne hji, Function.update_of_ne hji] at hcoord
      change Sum.inl (y j) = Sum.inl (x j) at hcoord
      have hval : y j = x j := Sum.inl.inj hcoord
      simpa [Function.update_of_ne hji] using hval
  · intro h
    subst y
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update_self]
    · simp [latticePotentialVertexCell, Function.update_of_ne hji]

theorem latticeCoboundary_vertexBasis_apply_edge
    (x y : LatticeVertices4) (i : Fin 4) (t : ℤ) :
    Cubical.latticeCoboundaryBasis (latticePotentialVertexCell y)
        (Cubical.latticeEdgeCell (latticePotentialVertexCell x) i t) =
      (if y = Function.update x i (t + 1) then 1 else 0) -
        (if y = Function.update x i t then 1 else 0) := by
  classical
  unfold Cubical.latticeCoboundaryBasis
  simp only [Finset.sum_apply', latticePotentialVertexCell]
  rw [Finset.sum_eq_single i]
  · have hrank : Cubical.latticeRankBefore
        (latticePotentialVertexCell y) i = 0 := by
      simp [Cubical.latticeRankBefore, Cubical.latticeIsEdge,
        latticePotentialVertexCell]
    rw [hrank]
    simp [Cubical.latticeEdgeCell, Cubical.latticeBasis,
      Finsupp.single_apply, vertex_edge_equality_lower,
      vertex_edge_equality_upper]
  · intro j hj hji
    have hjneq : j ≠ i := hji
    have hne₁ : Function.update (latticePotentialVertexCell y) j
        (Sum.inr (y j - 1)) ≠
          Function.update (latticePotentialVertexCell x) i (Sum.inr t) := by
      intro h
      have hcoord := congrFun h j
      simp only [Function.update_self] at hcoord
      rw [Function.update_of_ne hjneq] at hcoord
      cases hcoord
    have hne₂ : Function.update (latticePotentialVertexCell y) j
        (Sum.inr (y j)) ≠
          Function.update (latticePotentialVertexCell x) i (Sum.inr t) := by
      intro h
      have hcoord := congrFun h j
      simp only [Function.update_self] at hcoord
      rw [Function.update_of_ne hjneq] at hcoord
      cases hcoord
    simp only [Cubical.latticeEdgeCell, Cubical.latticeBasis]
    simp [hne₁, hne₂]
  · simp

theorem latticeCoboundary_vertexFinsupp_apply_edge
    (p : LatticeVertices4 →₀ ℤ) (x : LatticeVertices4)
    (i : Fin 4) (t : ℤ) :
    Cubical.latticeCoboundary (latticePotentialVertexFinsupp p)
        (Cubical.latticeEdgeCell (latticePotentialVertexCell x) i t) =
      p (Function.update x i (t + 1)) - p (Function.update x i t) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero =>
      change Cubical.latticeCoboundary
        (Finsupp.embDomain latticePotentialVertexEmbedding (0 : LatticeVertices4 →₀ ℤ)) _ = _
      simp
  | add p q hp hq =>
      change Cubical.latticeCoboundary
        (Finsupp.embDomain latticePotentialVertexEmbedding (p + q)) _ = _
      change Cubical.latticeCoboundary
        (Finsupp.embDomain latticePotentialVertexEmbedding p) _ = _ at hp
      change Cubical.latticeCoboundary
        (Finsupp.embDomain latticePotentialVertexEmbedding q) _ = _ at hq
      rw [Finsupp.embDomain_add, map_add]
      simp only [Finsupp.add_apply]
      rw [hp, hq]
      abel_nf
  | single y z =>
      change Cubical.latticeCoboundary
        (Finsupp.embDomain latticePotentialVertexEmbedding (Finsupp.single y z)) _ = _
      rw [Finsupp.embDomain_single]
      change Cubical.latticeCoboundary
        (Finsupp.single (latticePotentialVertexCell y) z) _ = _
      rw [show (Finsupp.single (latticePotentialVertexCell y) z : LatticeChain) =
          z • Finsupp.single (latticePotentialVertexCell y) 1 by
        ext c
        by_cases hc : c = latticePotentialVertexCell y <;> simp [hc]]
      rw [map_smul]
      change z • (Cubical.latticeCoboundary
        (Cubical.latticeBasis (latticePotentialVertexCell y))) _ = _
      rw [Cubical.latticeCoboundary_basis]
      change z * (Cubical.latticeCoboundaryBasis
        (latticePotentialVertexCell y)
        (Cubical.latticeEdgeCell (latticePotentialVertexCell x) i t)) = _
      rw [latticeCoboundary_vertexBasis_apply_edge]
      simp only [Finsupp.single_apply]
      have hneq : Function.update x i (1 + t) ≠
          Function.update x i t := by
        intro h
        have hcoord := congrFun h i
        simp only [Function.update_self] at hcoord
        omega
      have hneq' : Function.update x i t ≠
          Function.update x i (t + 1) := by
        intro h
        have hcoord := congrFun h i
        simp only [Function.update_self] at hcoord
        omega
      by_cases h₁ : y = Function.update x i (1 + t)
      · by_cases h₂ : y = Function.update x i t
        · exact False.elim (hneq (h₁.symm.trans h₂))
        · simp [h₁, hneq]
      · by_cases h₂ : y = Function.update x i t
        · simp [h₂, hneq']
        · simp [h₂]

theorem latticeCoboundary_vertexBasis_support_oneCell
    (x : LatticeVertices4) (c : LatticeCell)
    (hc : Cubical.latticeCoboundaryBasis
      (latticePotentialVertexCell x) c ≠ 0) :
    (Finset.univ.filter fun j : Fin 4 => (c j).isRight).card = 1 := by
  classical
  let b : LatticeChain := Cubical.latticeCoboundaryBasis
    (latticePotentialVertexCell x)
  have hmem : c ∈ b.support := Finsupp.mem_support_iff.mpr hc
  unfold b at hmem
  unfold Cubical.latticeCoboundaryBasis at hmem
  have hval := Finsupp.mem_support_iff.mp hmem
  rw [Finset.sum_apply'] at hval
  obtain ⟨i, hi, htermval⟩ := Finset.exists_ne_zero_of_sum_ne_zero hval
  have hterm : (((-1 : ℤ) ^ Cubical.latticeRankBefore
      (latticePotentialVertexCell x) i) •
      (Finsupp.single (Cubical.latticeEdgeCell
          (latticePotentialVertexCell x) i (x i - 1)) 1 -
        Finsupp.single (Cubical.latticeEdgeCell
          (latticePotentialVertexCell x) i (x i)) 1) : LatticeChain) c ≠ 0 := by
    simpa [latticePotentialVertexCell, Cubical.latticeRankBefore,
      Cubical.latticeIsEdge, Cubical.latticeBasis] using htermval
  have hdiff : (Finsupp.single (Cubical.latticeEdgeCell
      (latticePotentialVertexCell x) i (x i - 1)) 1 -
    Finsupp.single (Cubical.latticeEdgeCell
      (latticePotentialVertexCell x) i (x i)) 1 : LatticeChain) c ≠ 0 := by
    intro hz
    apply hterm
    rw [Finsupp.smul_apply, hz]
    simp
  by_cases hlow : c = Cubical.latticeEdgeCell
      (latticePotentialVertexCell x) i (x i - 1)
  · rw [hlow]
    have haxes : (Finset.univ.filter fun j : Fin 4 =>
        (Cubical.latticeEdgeCell (latticePotentialVertexCell x) i (x i - 1) j).isRight) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases hji : j = i
      · subst j
        simp [Cubical.latticeEdgeCell]
      · simpa [Cubical.latticeEdgeCell, Function.update_of_ne hji,
          latticePotentialVertexCell] using hji
    rw [haxes]
    simp
  · by_cases hup : c = Cubical.latticeEdgeCell
        (latticePotentialVertexCell x) i (x i)
    · rw [hup]
      have haxes : (Finset.univ.filter fun j : Fin 4 =>
          (Cubical.latticeEdgeCell (latticePotentialVertexCell x) i (x i) j).isRight) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        by_cases hji : j = i
        · subst j
          simp [Cubical.latticeEdgeCell]
        · simpa [Cubical.latticeEdgeCell, Function.update_of_ne hji,
            latticePotentialVertexCell] using hji
      rw [haxes]
      simp
    · simp [hlow, hup] at hdiff

theorem latticeCoboundary_vertexFinsupp_support_oneCells
    (p : LatticeVertices4 →₀ ℤ) (c : LatticeCell)
    (hc : Cubical.latticeCoboundary (latticePotentialVertexFinsupp p) c ≠ 0) :
    (Finset.univ.filter fun j : Fin 4 => (c j).isRight).card = 1 := by
  classical
  induction p using Finsupp.induction_linear with
  | zero =>
      change Cubical.latticeCoboundary (0 : LatticeChain) c ≠ 0 at hc
      exact (hc (by simp)).elim
  | add p q hp hq =>
      change Cubical.latticeCoboundary
        (Finsupp.embDomain latticePotentialVertexEmbedding (p + q)) c ≠ 0 at hc
      rw [Finsupp.embDomain_add, map_add] at hc
      change (Cubical.latticeCoboundary (latticePotentialVertexFinsupp p) c +
        Cubical.latticeCoboundary (latticePotentialVertexFinsupp q) c) ≠ 0 at hc
      have hsplit : Cubical.latticeCoboundary (latticePotentialVertexFinsupp p) c ≠ 0 ∨
          Cubical.latticeCoboundary (latticePotentialVertexFinsupp q) c ≠ 0 := by
        by_contra h
        push Not at h
        apply hc
        rw [h.1, h.2]
        simp
      rcases hsplit with hp' | hq'
      · exact hp hp'
      · exact hq hq'
  | single x z =>
      change Cubical.latticeCoboundary
          (Finsupp.embDomain latticePotentialVertexEmbedding (Finsupp.single x z)) c ≠ 0 at hc
      rw [Finsupp.embDomain_single] at hc
      change Cubical.latticeCoboundary
          (Finsupp.single (latticePotentialVertexCell x) z) c ≠ 0 at hc
      have hsingle : (Finsupp.single (latticePotentialVertexCell x) z : LatticeChain) =
          z • Finsupp.single (latticePotentialVertexCell x) 1 := by
        ext y
        by_cases hy : y = latticePotentialVertexCell x <;> simp [hy]
      rw [hsingle, map_smul] at hc
      change (z • Cubical.latticeCoboundary
        (Cubical.latticeBasis (latticePotentialVertexCell x))) c ≠ 0 at hc
      rw [Cubical.latticeCoboundary_basis] at hc
      have hbasis : Cubical.latticeCoboundaryBasis
          (latticePotentialVertexCell x) c ≠ 0 := by
        intro hzero
        apply hc
        simp [hzero]
      exact latticeCoboundary_vertexBasis_support_oneCell x c hbasis

theorem latticePotentialGradient_vertexFinsupp_apply_edge
    (p : LatticeVertices4 →₀ ℤ) (x : LatticeVertices4)
    (i : Fin 4) (t : ℤ) :
    latticePotentialGradient (fun y => p y)
        (latticeEdgeCell (latticePotentialVertexCell x) i t) =
      Cubical.latticeCoboundary (latticePotentialVertexFinsupp p)
        (latticeEdgeCell (latticePotentialVertexCell x) i t) := by
  rw [latticePotentialGradient_edge_formula,
    (latticeCoboundary_vertexFinsupp_apply_edge p x i t).symm]
  rfl

theorem latticeCell_is_latticeEdge_of_degree_one (c : LatticeCell)
    (hdegree : (Finset.univ.filter fun j : Fin 4 => (c j).isRight).card = 1) :
    ∃ x : LatticeVertices4, ∃ i : Fin 4, ∃ t : ℤ,
      c = Cubical.latticeEdgeCell (latticePotentialVertexCell x) i t := by
  classical
  let axes := Finset.univ.filter fun j : Fin 4 => (c j).isRight
  obtain ⟨i, haxes⟩ := Finset.card_eq_one.mp (by simpa [axes] using hdegree)
  have haxes' : (Finset.univ.filter fun j : Fin 4 => (c j).isRight) = {i} := by
    simpa [axes] using haxes
  have hi : (c i).isRight := by
    have hm : i ∈ (Finset.univ.filter fun j : Fin 4 => (c j).isRight) := by
      rw [haxes']
      simp
    exact (Finset.mem_filter.mp hm).2
  cases hci : c i with
  | inl v => simp [hci] at hi
  | inr t =>
      let x : LatticeVertices4 := fun j => Sum.elim id id (c j)
      have heq : c = Cubical.latticeEdgeCell
          (latticePotentialVertexCell x) i t := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [Cubical.latticeEdgeCell, hci]
        · have hnot : j ∉ axes := by
            change j ∉ (Finset.univ.filter fun j : Fin 4 => (c j).isRight)
            rw [haxes']
            simp [hji]
          have hleft : ¬(c j).isRight := by
            intro hjr
            apply hnot
            simp [axes, hjr]
          cases hcj : c j with
          | inl s => simp [Cubical.latticeEdgeCell,
              Function.update_of_ne hji, latticePotentialVertexCell, x, hcj]
          | inr s => simp [hcj] at hleft
      exact ⟨x, i, t, heq⟩


theorem lambdaStarEmbeddingC1_apply_bridge (R : RectBox4) (e : DualLinks R) :
    lambdaStarEmbeddingC1 R e =
      Cubical.lambdaStarEmbedding (B := R.side) R.origin e := by
  exact congrArg (fun f : DualLinks R ↪ LatticeCell => f e)
    (c1LambdaStar_bridge R)

theorem lambdaStarEmbeddingC1_range_bridge (R : RectBox4) :
    Set.range (lambdaStarEmbeddingC1 R) =
      Set.range (Cubical.lambdaStarEmbedding (B := R.side) R.origin) := by
  exact congrArg (fun f : DualLinks R ↪ LatticeCell => Set.range f)
    (c1LambdaStar_bridge R)


theorem latticePotentialGradient_vertexFinsupp_eq_coboundary
    (p : LatticeVertices4 →₀ ℤ) (c : LatticeCell) :
    latticePotentialGradient (fun x => p x) c =
      Cubical.latticeCoboundary (latticePotentialVertexFinsupp p) c := by
  classical
  by_cases hdegree :
      (Finset.univ.filter fun i : Fin 4 => (c i).isRight).card = 1
  · obtain ⟨x, i, t, hc⟩ := latticeCell_is_latticeEdge_of_degree_one c hdegree
    rw [hc]
    exact latticePotentialGradient_vertexFinsupp_apply_edge p x i t
  · have hgradient : latticePotentialGradient (fun x => p x) c = 0 := by
      simp [latticePotentialGradient, hdegree]
    have hboundary : Cubical.latticeCoboundary
        (latticePotentialVertexFinsupp p) c = 0 := by
      by_contra hne
      have hdeg := latticeCoboundary_vertexFinsupp_support_oneCells p c hne
      exact hdegree hdeg
    rw [hgradient, hboundary]


 /-- The arbitrary-potential relation is exactly the finite exact-shift
condition after connected-exterior normalization and the C1/C2 transports. -/
theorem sourceIntegerGaugeRelation_iff_sourceExactShiftSupportCondition226_internal
    (R : RectBox4) (α α' : IntegerDualField R) :
    sourceIntegerGaugeRelation R α α' ↔
      sourceExactShiftSupportCondition226 R.origin
        (sourceIntegerSignTwist α') (sourceIntegerSignTwist α) := by
  constructor
  · rintro ⟨γ, hgradientSupport, hshift⟩
    obtain ⟨γ₀, hsameGradient, hfinite, hvertices, hexterior, _hunique⟩ :=
      normalizeIntegerGaugePotential_connectedExterior_internal R γ hgradientSupport
    let p : LatticeVertices4 →₀ ℤ := Finsupp.ofSupportFinite γ₀ hfinite
    have hpFunction : (p : LatticeVertices4 → ℤ) = γ₀ := by
      exact Finsupp.ofSupportFinite_coe
    have hp : ∀ x : LatticeVertices4, p x = γ₀ x := by
      intro x
      exact congrFun hpFunction x
    let ζ : SourceIntegerPotential := ⟨latticePotentialVertexFinsupp p,
      fun c hc => latticePotentialVertexFinsupp_eq_zero_of_not_vertex p c hc⟩
    have hpotential : (fun x : LatticeVertices4 => p x) = γ₀ := by
      funext x
      exact hp x
    have hgradientCoboundary (c : LatticeCell) :
        latticePotentialGradient γ c = Cubical.latticeCoboundary ζ.1 c := by
      calc
        latticePotentialGradient γ c = latticePotentialGradient γ₀ c :=
          (hsameGradient c).symm
        _ = latticePotentialGradient (fun x => p x) c := by rw [← hpotential]
        _ = Cubical.latticeCoboundary (latticePotentialVertexFinsupp p) c :=
          latticePotentialGradient_vertexFinsupp_eq_coboundary p c
        _ = Cubical.latticeCoboundary ζ.1 c := rfl
    have hsupport : ((Cubical.latticeCoboundary ζ.1).support : Set LatticeCell) ⊆
        Set.range (Cubical.lambdaStarEmbedding (B := R.side) R.origin) := by
      intro c hc
      have hgrad : latticePotentialGradient γ c ≠ 0 := by
        intro hz
        apply (Finsupp.mem_support_iff.mp hc)
        rw [← hgradientCoboundary c, hz]
      have hmem := hgradientSupport c hgrad
      rw [lambdaStarEmbeddingC1_range_bridge R] at hmem
      exact hmem
    change ∃ ζ' : SourceIntegerPotential,
      ((Cubical.latticeCoboundary ζ'.1).support : Set LatticeCell) ⊆
        Set.range (Cubical.lambdaStarEmbedding (B := R.side) R.origin) ∧
      ∀ e : SourceDualOneCells R.side,
        sourceIntegerOrientationSign e *
          (sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e) =
            Cubical.latticeCoboundary ζ'.1
              (Cubical.lambdaStarEmbedding (B := R.side) R.origin e)
    refine ⟨ζ, hsupport, ?_⟩
    intro e
    have hsign : sourceIntegerOrientationSign e *
        (sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e) =
          α' e - α e := by
      simp only [sourceIntegerSignTwist]
      have hsquare := sourceIntegerOrientationSign_sq e
      calc
        sourceIntegerOrientationSign e *
            (sourceIntegerOrientationSign e * α' e -
              sourceIntegerOrientationSign e * α e) =
            sourceIntegerOrientationSign e ^ 2 * (α' e - α e) := by ring
        _ = α' e - α e := by rw [hsquare]; ring
    calc
      sourceIntegerOrientationSign e *
          (sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e) =
          α' e - α e := hsign
      _ = latticePotentialGradient γ (lambdaStarEmbeddingC1 R e) := by
        rw [hshift e]
        ring
      _ = Cubical.latticeCoboundary ζ.1
          (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) := by
        calc
          latticePotentialGradient γ (lambdaStarEmbeddingC1 R e) =
              Cubical.latticeCoboundary ζ.1 (lambdaStarEmbeddingC1 R e) :=
            hgradientCoboundary (lambdaStarEmbeddingC1 R e)
          _ = Cubical.latticeCoboundary ζ.1
              (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) :=
            congrArg (Cubical.latticeCoboundary ζ.1)
              (lambdaStarEmbeddingC1_apply_bridge R e)
  · intro hexact
    change ∃ ζ : SourceIntegerPotential,
      ((Cubical.latticeCoboundary ζ.1).support : Set LatticeCell) ⊆
        Set.range (Cubical.lambdaStarEmbedding (B := R.side) R.origin) ∧
      ∀ e : SourceDualOneCells R.side,
        sourceIntegerOrientationSign e *
          (sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e) =
            Cubical.latticeCoboundary ζ.1
              (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) at hexact
    rcases hexact with ⟨ζ, hsupport, hshift⟩
    have hvertexSupport : (ζ.1.support : Set LatticeCell) ⊆
        Set.range latticePotentialVertexEmbedding := by
      intro c hc
      have hv : sourceLatticeVertex c := by
        by_contra hnot
        exact (Finsupp.mem_support_iff.mp hc) (ζ.2 c hnot)
      let x : LatticeVertices4 := fun i => Sum.elim id id (c i)
      refine ⟨x, ?_⟩
      funext i
      cases hci : c i with
      | inl v => simp [latticePotentialVertexEmbedding,
          latticePotentialVertexCell, x, hci]
      | inr e => have h := hv i; simp [hci] at h
    let p : LatticeVertices4 →₀ ℤ := Finsupp.comapDomain
      latticePotentialVertexEmbedding ζ.1 latticePotentialVertexEmbedding.injective.injOn
    have hp : latticePotentialVertexFinsupp p = ζ.1 := by
      dsimp [p, latticePotentialVertexFinsupp]
      exact Finsupp.embDomain_comapDomain hvertexSupport
    have hglobal (c : LatticeCell) :
        latticePotentialGradient (fun x => p x) c =
          Cubical.latticeCoboundary ζ.1 c := by
      rw [← hp]
      exact latticePotentialGradient_vertexFinsupp_eq_coboundary p c
    have hgradientSupport : ∀ c : LatticeCell,
        latticePotentialGradient (fun x => p x) c ≠ 0 →
          c ∈ Set.range (lambdaStarEmbeddingC1 R) := by
      intro c hne
      have hdc : Cubical.latticeCoboundary ζ.1 c ≠ 0 := by
        rw [← hglobal c]
        exact hne
      have hmem := hsupport (Finsupp.mem_support_iff.mpr hdc)
      rw [← lambdaStarEmbeddingC1_range_bridge R] at hmem
      exact hmem
    have hsignShift (e : SourceDualOneCells R.side) :
        α' e - α e = Cubical.latticeCoboundary ζ.1
          (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) := by
      have hsign : sourceIntegerOrientationSign e *
          (sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e) =
            α' e - α e := by
        simp only [sourceIntegerSignTwist]
        have hsquare := sourceIntegerOrientationSign_sq e
        calc
          sourceIntegerOrientationSign e *
              (sourceIntegerOrientationSign e * α' e -
                sourceIntegerOrientationSign e * α e) =
              sourceIntegerOrientationSign e ^ 2 * (α' e - α e) := by ring
          _ = α' e - α e := by rw [hsquare]; ring
      calc
        α' e - α e = sourceIntegerOrientationSign e *
            (sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e) := hsign.symm
        _ = Cubical.latticeCoboundary ζ.1
            (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) := hshift e
    refine ⟨fun x => p x, hgradientSupport, ?_⟩
    intro e
    have hgradientLink :
        latticePotentialGradient (fun x => p x) (lambdaStarEmbeddingC1 R e) =
          Cubical.latticeCoboundary ζ.1
            (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) := by
      calc
        latticePotentialGradient (fun x => p x) (lambdaStarEmbeddingC1 R e) =
            Cubical.latticeCoboundary ζ.1 (lambdaStarEmbeddingC1 R e) :=
          hglobal (lambdaStarEmbeddingC1 R e)
        _ = Cubical.latticeCoboundary ζ.1
            (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) :=
          congrArg (Cubical.latticeCoboundary ζ.1)
            (lambdaStarEmbeddingC1_apply_bridge R e)
    calc
      α' e = α e + (α' e - α e) := by ring
      _ = α e + Cubical.latticeCoboundary ζ.1
          (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) := by
        rw [hsignShift e]
      _ = α e + latticePotentialGradient (fun x => p x)
          (lambdaStarEmbeddingC1 R e) := by rw [hgradientLink]

end FroehlichSpencer.FS82.Surface
end
