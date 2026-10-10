/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.FreeVillainDisorderLimit
public import FroehlichSpencer.BKT.Surface.FreeVillainWellDefined
public import FroehlichSpencer.BKT.Bridge.FreeVillainLaw
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.TheoremD
public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
public import FroehlichSpencer.BKT.Generic.Marked.Gap
import Mathlib.Tactic

/-!
The root `freeVillain_disorderLimit_upper_bound` /(1.35)) from two inputs, both proved on main:
* `VillainDisorder.Dirichlet.RootedDirichletFejerGlobalInput` (the quantitative core, implied by the
  clause `RootedFejerMarkedExtension`);
* `GaugeInput`: on D3's free box graph `rotatorFreeGraph (sideLength R)` the expectation of the
  bond-shift ratio under the unpinned Villain law equals D3's root-pinned
  `dirichletFreeVillainDisorderExpectation` (discharged in `Bridge/FreeVillainDisorderGauge.lean`).

Everything else is proved here:
* `boxEquiv`: the box `[-R, R + 1]²` of `IsFreeVillainDisorderLimit` is D3's spin box
  `Fin (2R + 2)²` by `(i, j) ↦ (i + R, j + R)`, so D3's `center` face `(R, R)` is FS81's `0*` and
  its axial face `(R + n, R)` is `x* = (n, 0)*`;
* `map_freeVillainLaw`: `freeVillainLaw` on the box is the unpinned Villain law on D3's graph;
* `freeVillainDisorder_eq`: FS81's (1.32) is D3's bond-shift ratio for the shift `−ξ`;
* `dirichletFreeVillainDisorderExpectation_neg`: D3's expectation is even in `ξ`;
* `freeVillain_disorderLimit_upper_bound_of_inputs`: the root from the two inputs, with
  `η = min(ξ, 1 − ξ)`, `β'' = c η² β / ξ²`, `A = 2`, from
  `rootedDirichletTheoremD_thermodynamicLimit`.

The normalization gate is consumed through its **** statement
`FroehlichSpencer.BKT.isProbabilityMeasure_freeVillainLaw` (`Surface/FreeVillainWellDefined`), a
mandatory, consumed predecessor of the root (as ).

The composite stays a conditional helper
under its own name.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.FreeVillainDisorder

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap dipoleGap_pos)
open FroehlichSpencer.BKT.Bridge.FreeVillainLaw

/-! ### The box and its identification with D3's spin box -/

/-- The box `[-R, R + 1]²` of `IsFreeVillainDisorderLimit`. -/
def box (R : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(R : ℤ)) (R + 1) ×ˢ Finset.Icc (-(R : ℤ)) (R + 1)

/-- D3's spin sites. -/
abbrev Site (R : ℕ) := RotatorSpinSite (sideLength R)

/-- D3's free box graph. -/
abbrev graph' (R : ℕ) := rotatorFreeGraph (sideLength R)

theorem mem_box {R : ℕ} {p : ℤ × ℤ} :
    p ∈ box R ↔ -(R : ℤ) ≤ p.1 ∧ p.1 ≤ R + 1 ∧ -(R : ℤ) ≤ p.2 ∧ p.2 ≤ R + 1 := by
  simp [box, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- `(i, j) ↦ (i + R, j + R)`. -/
def boxEquiv (R : ℕ) : box R ≃ Site R where
  toFun p := (⟨(p.1.1 + R).toNat, by have := mem_box.1 p.2; simp only [sideLength]; omega⟩,
    ⟨(p.1.2 + R).toNat, by have := mem_box.1 p.2; simp only [sideLength]; omega⟩)
  invFun v := ⟨(((v.1 : ℕ) : ℤ) - R, ((v.2 : ℕ) : ℤ) - R), by
    have h1 := v.1.isLt; have h2 := v.2.isLt
    simp only [sideLength] at h1 h2
    rw [mem_box]; omega⟩
  left_inv p := by
    have := mem_box.1 p.2
    apply Subtype.ext; ext <;> simp <;> omega
  right_inv v := by
    ext <;> simp

theorem boxEquiv_symm_val (R : ℕ) (v : Site R) :
    (((boxEquiv R).symm v : box R) : ℤ × ℤ) = (((v.1 : ℕ) : ℤ) - R, ((v.2 : ℕ) : ℤ) - R) := rfl

theorem boxEquiv_val (R : ℕ) (p : box R) :
    (((boxEquiv R p).1 : ℕ) : ℤ) = p.1.1 + R ∧ (((boxEquiv R p).2 : ℕ) : ℤ) = p.1.2 + R := by
  have := mem_box.1 p.2
  constructor <;> simp [boxEquiv] <;> omega

/-- The transport of angle configurations. -/
def Φ (R : ℕ) : (box R → ℝ) ≃ᵐ (Site R → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Site R => ℝ) (boxEquiv R)

theorem Φ_apply (R : ℕ) (θ : box R → ℝ) (v : Site R) : Φ R θ v = θ ((boxEquiv R).symm v) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Site R => ℝ) (boxEquiv R) θ
    ((boxEquiv R).symm v)
  simpa [Φ] using h

/-! ### The unpinned Villain law on D3's graph -/

/-- Lebesgue measure on `[-π, π)` at each site of D3's box. -/
def boxBase (R : ℕ) : Measure (Site R → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Ico (-Real.pi) Real.pi)

/-- The Villain density `∏_e v_β(θ_src - θ_tgt)` over the bonds of D3's free box graph. -/
def boxDensity (R : ℕ) (β : ℝ) (θ : Site R → ℝ) : ℝ≥0∞ :=
  ∏ e, ENNReal.ofReal (villainWeight β (θ ((graph' R).src e) - θ ((graph' R).tgt e)))

/-- The unpinned free-boundary Villain law on D3's box (FS81 (1.26) on `Fin (2R + 2)²`). -/
def unpinnedBoxVillainLaw (R : ℕ) (β : ℝ) : Measure (Site R → ℝ) :=
  ((boxBase R).withDensity (boxDensity R β) Set.univ)⁻¹ • (boxBase R).withDensity (boxDensity R β)

/-- The bond-shift ratio `∏_e v_β(θ_src - θ_tgt + s_e) / v_β(θ_src - θ_tgt)` on unpinned angles. -/
def unpinnedShiftRatio (R : ℕ) (β : ℝ) (s : RotatorInternalBond (sideLength R) → ℝ)
    (θ : Site R → ℝ) : ℝ :=
  ∏ e, villainWeight β (θ ((graph' R).src e) - θ ((graph' R).tgt e) + s e) /
    villainWeight β (θ ((graph' R).src e) - θ ((graph' R).tgt e))


def GaugeInput : Prop :=
  ∀ (R n : ℕ) (hn : n ≤ R) (β : ℝ) (hβ : 0 < β) (ξ : ℝ),
    ∫ θ, unpinnedShiftRatio R β (dirichletStringShift R n hn ξ) θ ∂unpinnedBoxVillainLaw R β =
      dirichletFreeVillainDisorderExpectation R n hn β ξ hβ

/-! ### Transport of the law -/

/-- The bond of `freeVillainLaw` corresponding to a bond of D3's graph. -/
def bondOfEdge (R : ℕ) (e : RotatorInternalBond (sideLength R)) : box R × box R :=
  ((boxEquiv R).symm ((graph' R).src e), (boxEquiv R).symm ((graph' R).tgt e))

theorem bondOfEdge_mem (R : ℕ) (e : RotatorInternalBond (sideLength R)) :
    bondOfEdge R e ∈ freeBonds (box R) := by
  simp only [freeBonds, Finset.mem_filter, Finset.mem_univ, true_and, bondOfEdge,
    boxEquiv_symm_val]
  rcases e with e | e
  · left
    simp only [graph', rotatorFreeGraph, squareFreeGraph, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> push_cast <;> ring
  · right
    simp only [graph', rotatorFreeGraph, squareFreeGraph, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> push_cast <;> ring

/-- The bond of D3's graph corresponding to a bond of `freeVillainLaw` (junk off the bonds). -/
def edgeOfBond (R : ℕ) (b : box R × box R) : RotatorInternalBond (sideLength R) :=
  if h : ((boxEquiv R b.1).1 : ℕ) + 1 < sideLength R + 1 ∧
      (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) then
    .inl ⟨⟨(boxEquiv R b.1).1, h.1⟩, (boxEquiv R b.1).2⟩
  else if h' : ((boxEquiv R b.1).2 : ℕ) + 1 < sideLength R + 1 then
    .inr ⟨(boxEquiv R b.1).1, ⟨(boxEquiv R b.1).2, h'⟩⟩
  else .inl ⟨⟨⟨0, by simp [sideLength]⟩, by simp [sideLength]⟩, ⟨0, by simp [sideLength]⟩⟩

theorem bondOfEdge_edgeOfBond (R : ℕ) (b : box R × box R) (hb : b ∈ freeBonds (box R)) :
    bondOfEdge R (edgeOfBond R b) = b := by
  simp only [freeBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have h1 := mem_box.1 b.1.2
  have h2 := mem_box.1 b.2.2
  obtain ⟨hx, hy⟩ := boxEquiv_val R b.1
  rcases hb with hb | hb
  · have hc : ((boxEquiv R b.1).1 : ℕ) + 1 < sideLength R + 1 := by
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hb
      simp only [sideLength]; omega
    simp only [edgeOfBond, dite_eq_left (show _ ∧ _ from ⟨hc, hb⟩), bondOfEdge]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
      simp only [boxEquiv_symm_val, graph', rotatorFreeGraph, squareFreeGraph] <;>
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hb ⊢ <;> push_cast <;> omega
  · have hn : ¬ (((boxEquiv R b.1).1 : ℕ) + 1 < sideLength R + 1 ∧
        (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0)) := by
      rintro ⟨-, h⟩
      rw [hb] at h
      simp [Prod.ext_iff] at h
    have hc : ((boxEquiv R b.1).2 : ℕ) + 1 < sideLength R + 1 := by
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hb
      simp only [sideLength]; omega
    simp only [edgeOfBond, dite_eq_right hn, dite_eq_left hc, bondOfEdge]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
      simp only [boxEquiv_symm_val, graph', rotatorFreeGraph, squareFreeGraph] <;>
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hb ⊢ <;> push_cast <;> omega

theorem edgeOfBond_bondOfEdge (R : ℕ) (e : RotatorInternalBond (sideLength R)) :
    edgeOfBond R (bondOfEdge R e) = e := by
  rcases e with e | e
  · have h : ((boxEquiv R (bondOfEdge R (.inl e)).1).1 : ℕ) + 1 < sideLength R + 1 ∧
        ((bondOfEdge R (.inl e)).2 : ℤ × ℤ) = ((bondOfEdge R (.inl e)).1 : ℤ × ℤ) + (1, 0) := by
      refine ⟨by simpa [bondOfEdge, graph', rotatorFreeGraph, squareFreeGraph] using e.1.2, ?_⟩
      simp only [bondOfEdge, boxEquiv_symm_val, graph', rotatorFreeGraph, squareFreeGraph,
        Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> push_cast <;> ring
    simp only [edgeOfBond, dite_eq_left h]
    congr 1
    simp [bondOfEdge, graph', rotatorFreeGraph, squareFreeGraph]
  · have hn : ¬ (((boxEquiv R (bondOfEdge R (.inr e)).1).1 : ℕ) + 1 < sideLength R + 1 ∧
        ((bondOfEdge R (.inr e)).2 : ℤ × ℤ) = ((bondOfEdge R (.inr e)).1 : ℤ × ℤ) + (1, 0)) := by
      rintro ⟨-, h⟩
      simp [bondOfEdge, boxEquiv_symm_val, graph', rotatorFreeGraph, squareFreeGraph,
        Prod.ext_iff] at h
    have hc : ((boxEquiv R (bondOfEdge R (.inr e)).1).2 : ℕ) + 1 < sideLength R + 1 := by
      simpa [bondOfEdge, graph', rotatorFreeGraph, squareFreeGraph] using e.2.2
    simp only [edgeOfBond, dite_eq_right hn, dite_eq_left hc]
    congr 1
    simp [bondOfEdge, graph', rotatorFreeGraph, squareFreeGraph]

theorem freeVillainDensity_eq (R : ℕ) (β : ℝ) (hβ : 0 < β) (θ : box R → ℝ) :
    freeVillainDensity β (box R) θ = boxDensity R β (Φ R θ) := by
  unfold freeVillainDensity boxDensity
  simp_rw [villainFactor_eq_ofReal_weight β hβ, Φ_apply]
  refine Finset.prod_nbij' (edgeOfBond R) (bondOfEdge R) (fun _ _ => Finset.mem_univ _)
    (fun e _ => bondOfEdge_mem R e) (fun b hb => bondOfEdge_edgeOfBond R b hb)
    (fun e _ => edgeOfBond_bondOfEdge R e) fun b hb => ?_
  have := bondOfEdge_edgeOfBond R b hb
  simp only [bondOfEdge] at this
  have h1 := congrArg Prod.fst this
  have h2 := congrArg Prod.snd this
  simp only at h1 h2
  rw [h1, h2]

theorem measurePreserving_Φ (R : ℕ) :
    MeasurePreserving (Φ R) (freeVillainBase (box R)) (boxBase R) :=
  measurePreserving_piCongrLeft (fun _ : Site R => volume.restrict (Set.Ico (-Real.pi) Real.pi))
    (boxEquiv R)

theorem withDensity_preimage (R : ℕ) (β : ℝ) (hβ : 0 < β) (s : Set (Site R → ℝ))
    (hs : MeasurableSet s) :
    (freeVillainBase (box R)).withDensity (freeVillainDensity β (box R)) (Φ R ⁻¹' s) =
      (boxBase R).withDensity (boxDensity R β) s := by
  rw [withDensity_apply _ ((Φ R).measurable hs), withDensity_apply _ hs]
  simp_rw [freeVillainDensity_eq R β hβ]
  exact (measurePreserving_Φ R).setLIntegral_comp_preimage_emb (Φ R).measurableEmbedding _ s

/-- **`freeVillainLaw` on the box is the unpinned Villain law of D3's graph.** -/
theorem map_freeVillainLaw (R : ℕ) (β : ℝ) (hβ : 0 < β) :
    (freeVillainLaw β hβ (box R)).map (Φ R) = unpinnedBoxVillainLaw R β := by
  ext s hs
  rw [Measure.map_apply (Φ R).measurable hs, freeVillainLaw_eq, unpinnedBoxVillainLaw,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    withDensity_preimage R β hβ s hs]
  congr 2
  simpa using withDensity_preimage R β hβ Set.univ MeasurableSet.univ

/-! ### The string -/

theorem stringEdge_src (R n : ℕ) (hn : n ≤ R) (k : Fin n) :
    (((graph' R).src (dirichletStringEdge R n hn k)).1 : ℕ) = R + (k + 1) ∧
      (((graph' R).src (dirichletStringEdge R n hn k)).2 : ℕ) = R := by
  have := k.isLt
  simp only [graph', rotatorFreeGraph, squareFreeGraph, dirichletStringEdge,
    Duality.verticalDualEdgeData, Fin.val_castLE]
  refine ⟨?_, ?_⟩ <;> first | trivial | omega

theorem stringEdge_tgt (R n : ℕ) (hn : n ≤ R) (k : Fin n) :
    (((graph' R).tgt (dirichletStringEdge R n hn k)).1 : ℕ) = R + (k + 1) ∧
      (((graph' R).tgt (dirichletStringEdge R n hn k)).2 : ℕ) = R + 1 := by
  have := k.isLt
  simp only [graph', rotatorFreeGraph, squareFreeGraph, dirichletStringEdge,
    Duality.verticalDualEdgeData, Fin.val_castLE]
  refine ⟨?_, ?_⟩ <;> first | trivial | omega

theorem stringEdge_injective (R n : ℕ) (hn : n ≤ R) :
    Function.Injective (dirichletStringEdge R n hn) := by
  intro k k' h
  have h1 := (stringEdge_src R n hn k).1
  have h2 := (stringEdge_src R n hn k').1
  rw [h] at h1
  exact Fin.ext (by omega)

theorem stringShift_apply (R n : ℕ) (hn : n ≤ R) (ξ : ℝ) (k : Fin n) :
    dirichletStringShift R n hn ξ (dirichletStringEdge R n hn k) = 2 * Real.pi * ξ := by
  unfold dirichletStringShift
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    exact ite_eq_right fun h => hk' (stringEdge_injective R n hn h.symm)
  · simp

theorem stringShift_eq_zero (R n : ℕ) (hn : n ≤ R) (ξ : ℝ) (e : RotatorInternalBond (sideLength R))
    (he : e ∉ Finset.univ.image (dirichletStringEdge R n hn)) :
    dirichletStringShift R n hn ξ e = 0 := by
  unfold dirichletStringShift
  refine Finset.sum_eq_zero fun k _ => ?_
  exact ite_eq_right fun h => he (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h.symm⟩)

/-- **FS81's (1.32) is D3's bond-shift ratio for the shift `−ξ`.** -/
theorem freeVillainDisorder_eq (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ) (hβ : 0 < β)
    (hΛ : ∀ m : Fin n, (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ box R ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ box R)
    (θ : box R → ℝ) :
    freeVillainDisorder β hβ ξ (box R) n hΛ θ =
      unpinnedShiftRatio R β (dirichletStringShift R n hn (-ξ)) (Φ R θ) := by
  unfold unpinnedShiftRatio
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image (dirichletStringEdge R n hn)))
    (fun e _ he => by
      rw [stringShift_eq_zero R n hn _ e he, add_zero]
      exact div_self (VillainWeight.villainWeight_pos hβ _).ne'),
    Finset.prod_image (fun k _ k' _ h => stringEdge_injective R n hn h)]
  unfold freeVillainDisorder
  refine Finset.prod_congr rfl fun k _ => ?_
  have hsrc : (boxEquiv R).symm ((graph' R).src (dirichletStringEdge R n hn k)) =
      ⟨(((k : ℕ) : ℤ) + 1, 0), (hΛ k).1⟩ := by
    apply Subtype.ext
    rw [boxEquiv_symm_val, (stringEdge_src R n hn k).1, (stringEdge_src R n hn k).2]
    ext <;> push_cast <;> ring
  have htgt : (boxEquiv R).symm ((graph' R).tgt (dirichletStringEdge R n hn k)) =
      ⟨(((k : ℕ) : ℤ) + 1, 1), (hΛ k).2⟩ := by
    apply Subtype.ext
    rw [boxEquiv_symm_val, (stringEdge_tgt R n hn k).1, (stringEdge_tgt R n hn k).2]
    ext <;> push_cast <;> ring
  rw [stringShift_apply, Φ_apply, Φ_apply, hsrc, htgt]
  show villainWeight β _ / villainWeight β _ = villainWeight β _ / villainWeight β _
  rw [← VillainWeight.villainWeight_neg β (θ ⟨((k : ℤ) + 1, 0), _⟩ - θ ⟨((k : ℤ) + 1, 1), _⟩ +
      2 * Real.pi * -ξ),
    ← VillainWeight.villainWeight_neg β (θ ⟨((k : ℤ) + 1, 0), _⟩ - θ ⟨((k : ℤ) + 1, 1), _⟩)]
  congr 2 <;> ring

/-- D3's expectation is even in `ξ`. -/
theorem dirichletFreeVillainDisorderExpectation_neg (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ) (hβ : 0 < β) :
    dirichletFreeVillainDisorderExpectation R n hn β (-ξ) hβ =
      dirichletFreeVillainDisorderExpectation R n hn β ξ hβ := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have : dirichletStringShift R 0 hn (-ξ) = dirichletStringShift R 0 hn ξ := by
      funext e; simp [dirichletStringShift]
    simp only [dirichletFreeVillainDisorderExpectation, this]
  · have hR : 1 ≤ R := le_trans hpos hn
    rw [dirichletFreeVillainDisorderExpectation_eq_cosineExpectation R n hR hn,
      dirichletFreeVillainDisorderExpectation_eq_cosineExpectation R n hR hn]
    unfold cosineExpectation cosineNumerator
    congr 2
    funext h
    unfold dipoleCosine
    rw [show 2 * Real.pi * -ξ * _ = -(2 * Real.pi * ξ * (((h.1 (some (center R)) -
      h.1 (some (axialSite R n hn)) : ℤ) : ℝ))) by ring, Real.cos_neg]

/-- **The finite (1.32)–(1.35) identity on the box `[-R, R + 1]²`, given the gauge adapter.** -/
theorem freeVillainDisorder_expectation_eq (hG : GaugeInput) (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ)
    (hβ : 0 < β)
    (hΛ : ∀ m : Fin n,
      (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ box R ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ box R) :
    ∫ θ, freeVillainDisorder β hβ ξ (box R) n hΛ θ ∂freeVillainLaw β hβ (box R) =
      dirichletFreeVillainDisorderExpectation R n hn β ξ hβ := by
  simp_rw [freeVillainDisorder_eq R n hn β ξ hβ hΛ]
  rw [← dirichletFreeVillainDisorderExpectation_neg, ← hG R n hn β hβ (-ξ),
    ← map_freeVillainLaw R β hβ, integral_map_equiv]

/-! ### The root -/

theorem string_mem_box {R n : ℕ} (hn : n ≤ R) :
    ∀ m : Fin n, (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ box R ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ box R := by
  intro m
  have := m.isLt
  constructor <;> rw [mem_box] <;> omega


theorem freeVillain_disorderLimit_upper_bound_of_inputs
    (hD2 : RootedDirichletFejerGlobalInput) (hG : GaugeInput) :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) := by
  classical
  obtain ⟨c, hc, h3⟩ := rootedDirichletTheoremD_thermodynamicLimit hD2
  intro ξ hξ0 hξ1
  set η := dipoleGap ξ with hηdef
  have hη : 0 < η := dipoleGap_pos hξ0 hξ1
  have hηh : η ≤ 1 / 2 := by
    simp only [hηdef, dipoleGap]
    rcases le_total ξ (1 - ξ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hηξ : η ≤ ξ := min_le_left _ _
  have hη1 : η ≤ 1 - ξ := min_le_right _ _
  obtain ⟨β₀, -, hβ₀⟩ := h3 η hη hηh
  refine ⟨β₀, fun β hβ hββ₀ => ?_⟩
  have hD3 := fun n (hn1 : 1 ≤ n) => hβ₀ β hβ hββ₀ ξ hξ0 hξ1 hηξ hη1 n hn1
  -- the finite expectations on the boxes
  set E : ℕ → ℕ → ℝ := fun R n =>
    if hn : n ≤ R then
      ∫ θ, freeVillainDisorder β hβ ξ (box R) n (string_mem_box hn) θ ∂freeVillainLaw β hβ (box R)
    else 0 with hE
  have hE_eq : ∀ R n (hn : n ≤ R), 1 ≤ n → E R n = dirichletCenteredDisorder R n β ξ hβ := by
    intro R n hn _
    simp only [hE, dite_eq_left hn, dirichletCenteredDisorder]
    exact freeVillainDisorder_expectation_eq hG R n hn β ξ hβ _
  have hE0 : ∀ R, E R 0 = 1 := by
    intro R
    have := FroehlichSpencer.BKT.isProbabilityMeasure_freeVillainLaw β hβ (box R)
    simp [hE, freeVillainDisorder]
  have hEb : ∀ R n, |E R n| ≤ 1 := by
    intro R n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hE0]; simp
    · by_cases hn : n ≤ R
      · rw [hE_eq R n hn hpos]
        exact abs_le.2 ((hD3 n hpos).2.1 R)
      · simp [hE, dite_eq_right hn]
  set B : ℕ → ℝ := fun n => 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)) with hB
  have hBform : ∀ n : ℕ, B n = 2 * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * (c * η ^ 2 * β / ξ ^ 2))) := by
    intro n
    simp only [hB, Real.rpow_eq_pow]
    congr 2
    · push_cast; ring
    · field_simp
  refine ⟨?_, c * η ^ 2 * β / ξ ^ 2, by have := hβ; positivity, 2, ?_⟩
  · -- existence: a joint subsequence of the boxes
    obtain ⟨φ, hφ, D, hD⟩ := Coulomb.exists_subseq_tendsto_pointwise E (fun _ => 1) hEb
    refine ⟨D, φ, hφ.tendsto_atTop, fun n => ?_⟩
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hφ.tendsto_atTop.eventually (eventually_ge_atTop n))
    have : Nonempty {k : ℕ // n ≤ φ k} := ⟨⟨K, hK K le_rfl⟩⟩
    have hval : Tendsto (Subtype.val : {k : ℕ // n ≤ φ k} → ℕ) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨⟨max b K, hK _ (le_max_right _ _)⟩,
        fun k hk => (le_max_left b K).trans hk⟩
    refine ((hD n).comp hval).congr' (Eventually.of_forall fun k => ?_)
    simp only [Function.comp_apply, hE, dite_eq_left k.2]
    rfl
  · -- every thermodynamic limit
    rintro D ⟨Rs, hRs, hconv⟩ n
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hRs.eventually (eventually_ge_atTop n))
    have : Nonempty {k : ℕ // n ≤ Rs k} := ⟨⟨K, hK K le_rfl⟩⟩
    have hval : Tendsto (Subtype.val : {k : ℕ // n ≤ Rs k} → ℕ) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨⟨max b K, hK _ (le_max_right _ _)⟩,
        fun k hk => (le_max_left b K).trans hk⟩
    have hEk : ∀ k : {k : ℕ // n ≤ Rs k},
        ∫ θ, freeVillainDisorder β hβ ξ
            (Finset.Icc (-(Rs k : ℤ)) (Rs k + 1) ×ˢ Finset.Icc (-(Rs k : ℤ)) (Rs k + 1)) n
            (string_mem_box k.2) θ
          ∂freeVillainLaw β hβ (Finset.Icc (-(Rs k : ℤ)) (Rs k + 1) ×ˢ
            Finset.Icc (-(Rs k : ℤ)) (Rs k + 1)) = E (Rs k) n := by
      intro k
      simp only [hE, dite_eq_left k.2]
      rfl
    have hlim : Tendsto (fun k : {k : ℕ // n ≤ Rs k} => E (Rs k) n) atTop (𝓝 (D n)) :=
      (hconv n).congr fun k => hEk k
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have h1 : D 0 = 1 := tendsto_nhds_unique hlim (by simp only [hE0]; exact tendsto_const_nhds)
      rw [h1]
      simp
    · rw [← hBform]
      refine le_of_tendsto hlim ?_
      have hev := (hD3 n hpos).2.2.1
      filter_upwards [(hRs.comp hval).eventually hev] with k hk
      rw [hE_eq (Rs k) n k.2 hpos]
      exact hk.2

end FroehlichSpencer.BKT.Bridge.FreeVillainDisorder

end
