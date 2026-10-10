/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import FroehlichSpencer.FS82.Infinite.GlobalVariational

/-!
# Finite-support Fourier transforms on the four-dimensional lattice

The normalized product Haar torus models the Brillouin zone after the
coordinate change `k = 2πx`.  Finite-support link fields have componentwise
trigonometric-polynomial transforms, with exact orthogonality and Parseval.
-/

@[expose] public section


open MeasureTheory
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite
open scoped ComplexConjugate

noncomputable section

namespace FroehlichSpencer.FS82.Infinite.Fourier

attribute [local instance] Classical.propDecidable

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev LatticePoint := ℤ × (ℤ × (ℤ × ℤ))
abbrev Torus4 := AddCircle (1 : ℝ) ×
  (AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))

def torus4Haar : Measure Torus4 :=
  let μ : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle
  μ.prod (μ.prod (μ.prod μ))

local instance : IsFiniteMeasure torus4Haar := by
  dsimp [torus4Haar]
  infer_instance

def latticeCharacter (x : LatticePoint) (k : Torus4) : ℂ :=
  fourier (-x.1) k.1 * (fourier (-x.2.1) k.2.1 *
    (fourier (-x.2.2.1) k.2.2.1 * fourier (-x.2.2.2) k.2.2.2))

theorem integral_fourier (n : ℤ) :
    ∫ t : AddCircle (1 : ℝ), fourier n t ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hzero : ∫ t : AddCircle (1 : ℝ), fourier n t ∂AddCircle.haarAddCircle = 0 :=
      integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle) (by
        intro t
        rw [fourier_add_half_inv_index hn (by norm_num : (0 : ℝ) < 1)])
    simpa [hn] using hzero

theorem integral_latticeCharacter (x : LatticePoint) :
    ∫ k : Torus4, latticeCharacter x k ∂torus4Haar =
      if x = 0 then 1 else 0 := by
  have h := integral_prod_mul
    (μ := AddCircle.haarAddCircle)
    (ν := (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))).prod
      ((AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))).prod
        (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))))
    (fun t : AddCircle (1 : ℝ) => fourier (-x.1) t)
    (fun t : AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) =>
      fourier (-x.2.1) t.1 *
        (fourier (-x.2.2.1) t.2.1 * fourier (-x.2.2.2) t.2.2))
  simp only [torus4Haar, latticeCharacter] at h ⊢
  rw [h]
  have h₂ := integral_prod_mul
    (μ := AddCircle.haarAddCircle)
    (ν := (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))).prod
      (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))
    (fun t : AddCircle (1 : ℝ) => fourier (-x.2.1) t)
    (fun t : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      fourier (-x.2.2.1) t.1 * fourier (-x.2.2.2) t.2)
  rw [h₂]
  have h₃ := integral_prod_mul
    (μ := AddCircle.haarAddCircle)
    (ν := (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))
    (fun t : AddCircle (1 : ℝ) => fourier (-x.2.2.1) t)
    (fun t : AddCircle (1 : ℝ) => fourier (-x.2.2.2) t)
  rw [h₃]
  simp only [integral_fourier]
  rcases x with ⟨a, ⟨b, ⟨c, d⟩⟩⟩
  simp only [Prod.mk_eq_zero, Int.neg_eq_zero]
  split_ifs <;> simp_all

private theorem conj_fourier_neg (n : ℤ) (k : AddCircle (1 : ℝ)) :
    conj (fourier (-n) k) = fourier n k := by
  rw [fourier_neg]
  simp

theorem latticeCharacter_mul_conj (x y : LatticePoint) (k : Torus4) :
    latticeCharacter x k * conj (latticeCharacter y k) =
      latticeCharacter (x - y) k := by
  rcases x with ⟨a, ⟨b, ⟨c, d⟩⟩⟩
  rcases y with ⟨e, ⟨f, ⟨g, h⟩⟩⟩
  simp only [latticeCharacter, map_mul]
  rw [conj_fourier_neg, conj_fourier_neg, conj_fourier_neg, conj_fourier_neg]
  calc
    _ = (fourier (-a) k.1 * fourier e k.1) *
        ((fourier (-b) k.2.1 * fourier f k.2.1) *
          ((fourier (-c) k.2.2.1 * fourier g k.2.2.1) *
            (fourier (-d) k.2.2.2 * fourier h k.2.2.2))) := by ring_nf
    _ = latticeCharacter ((a, b, c, d) - (e, f, g, h)) k := by
      rw [← fourier_add, ← fourier_add, ← fourier_add, ← fourier_add]
      have ha : -a + e = -((a, b, c, d) - (e, f, g, h)).1 := by simp; ring
      have hb : -b + f = -((a, b, c, d) - (e, f, g, h)).2.1 := by simp; ring
      have hc : -c + g = -((a, b, c, d) - (e, f, g, h)).2.2.1 := by simp; ring
      have hd : -d + h = -((a, b, c, d) - (e, f, g, h)).2.2.2 := by simp; ring
      rw [latticeCharacter, ha, hb, hc, hd]

theorem integral_latticeCharacter_mul_conj (x y : LatticePoint) :
    ∫ k : Torus4, latticeCharacter x k * conj (latticeCharacter y k)
      ∂torus4Haar = if x = y then 1 else 0 := by
  rw [show (fun k : Torus4 => latticeCharacter x k * conj (latticeCharacter y k)) =
      fun k => latticeCharacter (x - y) k by funext k; exact latticeCharacter_mul_conj x y k]
  rw [integral_latticeCharacter]
  simp only [sub_eq_zero]


private theorem integrable_of_continuous (f : Torus4 → ℂ)
    (hf : Continuous f) (hm : Measurable f) :
    Integrable f torus4Haar := by
  have hcompact : IsCompact (Set.range fun k : Torus4 => ‖f k‖) := by
    simpa [Function.comp_def] using isCompact_univ.image (continuous_norm.comp hf)
  rcases hcompact.bddAbove with ⟨C, hC⟩
  change ∀ b ∈ Set.range (fun k : Torus4 => ‖f k‖), b ≤ C at hC
  apply Integrable.of_bound hm.aestronglyMeasurable C
  filter_upwards with k
  exact hC _ ⟨k, rfl⟩


def finiteFourierPolynomialOn {α : Type*} (s : Finset α)
    (site : α → LatticePoint) (a : α → ℂ) (k : Torus4) : ℂ :=
  ∑ x ∈ s, a x * latticeCharacter (site x) k


private theorem integral_fourierTermCrossOn {α : Type*} (site : α → LatticePoint)
    (a b : α → ℂ) (x y : α) :
    ∫ k : Torus4,
      (a x * latticeCharacter (site x) k) *
        conj (b y * latticeCharacter (site y) k) ∂torus4Haar =
      a x * conj (b y) * (if site x = site y then 1 else 0) := by
  calc
    _ = ∫ k : Torus4, (a x * conj (b y)) *
        (latticeCharacter (site x) k * conj (latticeCharacter (site y) k))
          ∂torus4Haar := by
      congr 1
      funext k
      simp only [map_mul]
      ring
    _ = a x * conj (b y) *
        (∫ k : Torus4,
          latticeCharacter (site x) k * conj (latticeCharacter (site y) k)
            ∂torus4Haar) := by rw [integral_const_mul]
    _ = _ := by rw [integral_latticeCharacter_mul_conj]

/-- The polarized finite orthogonality identity for two Fourier polynomials
with the same injective frequency labels. -/
theorem finiteFourierCrossOn {α : Type*} (s : Finset α)
    (site : α → LatticePoint) (a b : α → ℂ)
    (hinj : ∀ ⦃x y⦄, x ∈ s → y ∈ s → site x = site y → x = y) :
    ∫ k : Torus4,
      finiteFourierPolynomialOn s site a k *
        conj (finiteFourierPolynomialOn s site b k) ∂torus4Haar =
      ∑ x ∈ s, a x * conj (b x) := by
  classical
  have hterm (x y : α) :
      Integrable (fun k : Torus4 =>
        (a x * latticeCharacter (site x) k) *
          conj (b y * latticeCharacter (site y) k)) torus4Haar := by
    apply integrable_of_continuous
    fun_prop [latticeCharacter]
    fun_prop [latticeCharacter]
  calc
    _ = ∫ k : Torus4, ∑ x ∈ s, ∑ y ∈ s,
        (a x * latticeCharacter (site x) k) *
          conj (b y * latticeCharacter (site y) k) ∂torus4Haar := by
      congr 1
      funext k
      have hconj : conj (∑ y ∈ s, b y * latticeCharacter (site y) k) =
          ∑ y ∈ s, conj (b y * latticeCharacter (site y) k) :=
        map_sum (starRingEnd ℂ) (fun y => b y * latticeCharacter (site y) k) s
      change (∑ x ∈ s, a x * latticeCharacter (site x) k) *
        conj (∑ y ∈ s, b y * latticeCharacter (site y) k) = _
      rw [hconj]
      simp only [map_mul]
      rw [Finset.sum_mul_sum]
    _ = ∑ x ∈ s, ∑ y ∈ s,
        ∫ k : Torus4,
          (a x * latticeCharacter (site x) k) *
            conj (b y * latticeCharacter (site y) k) ∂torus4Haar := by
      rw [integral_finsetSum s (fun x hx =>
        integrable_finsetSum s (fun y hy => hterm x y))]
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_finsetSum s (fun y hy => hterm x y)]
    _ = _ := by
      simp_rw [integral_fourierTermCrossOn]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_eq_single x]
      · simp
      · intro y hy hne
        have hxy : site x ≠ site y := by
          intro hxy
          exact hne (hinj (x := x) (y := y) hx hy hxy).symm
        simp [hxy]
      · intro hnot
        exact (hnot hx).elim

def latticeCellBaseCoordinate (c : LatticeCell 4) (i : Fin 4) : ℤ :=
  Sum.elim id id (c i)

def latticeCellPoint (c : LatticeCell 4) : LatticePoint :=
  (latticeCellBaseCoordinate c 0,
    (latticeCellBaseCoordinate c 1,
      (latticeCellBaseCoordinate c 2, latticeCellBaseCoordinate c 3)))

def latticeLinkAxisCell (c : LatticeCell 4) (i : Fin 4) : Prop :=
  latticeIsEdge (c i) ∧ ∀ j, j ≠ i → ¬ latticeIsEdge (c j)

noncomputable def latticeCellAxes (c : LatticeCell 4) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter (fun i => latticeIsEdge (c i))

def latticePointCoordinate (p : LatticePoint) (i : Fin 4) : ℤ :=
  match i.val with
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2.1
  | _ => p.2.2.2

theorem latticeCellPoint_coordinate (c : LatticeCell 4) (i : Fin 4) :
    latticePointCoordinate (latticeCellPoint c) i = latticeCellBaseCoordinate c i := by
  fin_cases i <;> rfl

theorem latticeCellPoint_injective_of_axes_eq
    {c d : LatticeCell 4} (haxes : latticeCellAxes c = latticeCellAxes d)
    (hp : latticeCellPoint c = latticeCellPoint d) : c = d := by
  funext i
  have hcoord : latticeCellBaseCoordinate c i = latticeCellBaseCoordinate d i := by
    have h := congrArg (fun p => latticePointCoordinate p i) hp
    simpa only [latticeCellPoint_coordinate] using h
  have hedge : latticeIsEdge (c i) ↔ latticeIsEdge (d i) := by
    have hmem : i ∈ latticeCellAxes c ↔ i ∈ latticeCellAxes d := by rw [haxes]
    simpa [latticeCellAxes] using hmem
  cases hc : c i with
  | inl x =>
      have hd : ¬ latticeIsEdge (d i) := by
        intro he
        have hcEdge : latticeIsEdge (c i) := hedge.mpr he
        simp [latticeIsEdge, hc] at hcEdge
      cases hdi : d i with
      | inl y =>
          have hxy : x = y := by simpa [latticeCellBaseCoordinate, hc, hdi] using hcoord
          exact congrArg Sum.inl hxy
      | inr y => simp [latticeIsEdge, hdi] at hd
  | inr x =>
      have hd : latticeIsEdge (d i) := hedge.mp (by simp [latticeIsEdge, hc])
      cases hdi : d i with
      | inl y => simp [latticeIsEdge, hdi] at hd
      | inr y =>
          have hxy : x = y := by simpa [latticeCellBaseCoordinate, hc, hdi] using hcoord
          exact congrArg Sum.inr hxy

theorem existsUnique_latticeLinkAxis_of_degree_one (c : LatticeCell 4)
    (hc : latticeCellDegree c = 1) : ∃! i, latticeLinkAxisCell c i := by
  classical
  have hcard : (latticeCellAxes c).card = 1 := by
    simpa [latticeCellAxes, latticeCellDegree] using hc
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_, ?_⟩
  · constructor
    · have hi' : i ∈ latticeCellAxes c := by rw [hi]; simp
      simpa [latticeCellAxes] using hi'
    · intro j hji hed
      have hj : j ∈ latticeCellAxes c := by simp [latticeCellAxes, hed]
      rw [hi] at hj
      simp only [Finset.mem_singleton] at hj
      exact hji hj
  · intro j hj
    have hj' : j ∈ latticeCellAxes c := by
      simp [latticeCellAxes, hj.1]
    rw [hi] at hj'
    exact Finset.mem_singleton.mp hj'

private theorem sum_single_linkAxis (c : LatticeCell 4) (q : ℂ)
    (hc : latticeCellDegree c = 1) :
    ∑ i : Fin 4, (if latticeLinkAxisCell c i then q else 0) = q := by
  classical
  obtain ⟨i, hi, huniq⟩ := existsUnique_latticeLinkAxis_of_degree_one c hc
  have hfilter : Finset.univ.filter (fun j : Fin 4 => latticeLinkAxisCell c j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨huniq j, fun hj => by simpa [hj] using hi⟩
  calc
    ∑ j : Fin 4, (if latticeLinkAxisCell c j then q else 0) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin 4 => latticeLinkAxisCell c j), q := by
      rw [← Finset.sum_filter]
    _ = q := by rw [hfilter]; simp

theorem latticeCellPoint_injective_on_linkAxis (i : Fin 4)
    {c d : LatticeCell 4} (hc : latticeLinkAxisCell c i)
    (hd : latticeLinkAxisCell d i) (hp : latticeCellPoint c = latticeCellPoint d) :
    c = d := by
  funext j
  fin_cases j
  · by_cases hji : (0 : Fin 4) = i
    · subst i
      have hce : latticeIsEdge (c 0) := hc.1
      have hde : latticeIsEdge (d 0) := hd.1
      cases hci : c 0 with
      | inl v => simp [latticeIsEdge, hci] at hce
      | inr e =>
        cases hdi : d 0 with
        | inl v => simp [latticeIsEdge, hdi] at hde
        | inr f =>
          have hval := congrArg Prod.fst hp
          have hv : e = f := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst f
          exact hci.trans hdi.symm
    · have hcn := hc.2 0 hji
      have hdn := hd.2 0 hji
      cases hci : c 0 with
      | inl v =>
        cases hdi : d 0 with
        | inl w =>
          have hval := congrArg Prod.fst hp
          have hv : v = w := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst w
          exact hci.trans hdi.symm
        | inr f => simp [latticeIsEdge, hdi] at hdn
      | inr e => simp [latticeIsEdge, hci] at hcn
  · by_cases hji : (1 : Fin 4) = i
    · subst i
      have hce : latticeIsEdge (c 1) := hc.1
      have hde : latticeIsEdge (d 1) := hd.1
      cases hci : c 1 with
      | inl v => simp [latticeIsEdge, hci] at hce
      | inr e =>
        cases hdi : d 1 with
        | inl v => simp [latticeIsEdge, hdi] at hde
        | inr f =>
          have hval := congrArg (fun p : LatticePoint => p.2.1) hp
          have hv : e = f := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst f
          exact hci.trans hdi.symm
    · have hcn := hc.2 1 hji
      have hdn := hd.2 1 hji
      cases hci : c 1 with
      | inl v =>
        cases hdi : d 1 with
        | inl w =>
          have hval := congrArg (fun p : LatticePoint => p.2.1) hp
          have hv : v = w := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst w
          exact hci.trans hdi.symm
        | inr f => simp [latticeIsEdge, hdi] at hdn
      | inr e => simp [latticeIsEdge, hci] at hcn
  · by_cases hji : (2 : Fin 4) = i
    · subst i
      have hce : latticeIsEdge (c 2) := hc.1
      have hde : latticeIsEdge (d 2) := hd.1
      cases hci : c 2 with
      | inl v => simp [latticeIsEdge, hci] at hce
      | inr e =>
        cases hdi : d 2 with
        | inl v => simp [latticeIsEdge, hdi] at hde
        | inr f =>
          have hval := congrArg (fun p : LatticePoint => p.2.2.1) hp
          have hv : e = f := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst f
          exact hci.trans hdi.symm
    · have hcn := hc.2 2 hji
      have hdn := hd.2 2 hji
      cases hci : c 2 with
      | inl v =>
        cases hdi : d 2 with
        | inl w =>
          have hval := congrArg (fun p : LatticePoint => p.2.2.1) hp
          have hv : v = w := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst w
          exact hci.trans hdi.symm
        | inr f => simp [latticeIsEdge, hdi] at hdn
      | inr e => simp [latticeIsEdge, hci] at hcn
  · by_cases hji : (3 : Fin 4) = i
    · subst i
      have hce : latticeIsEdge (c 3) := hc.1
      have hde : latticeIsEdge (d 3) := hd.1
      cases hci : c 3 with
      | inl v => simp [latticeIsEdge, hci] at hce
      | inr e =>
        cases hdi : d 3 with
        | inl v => simp [latticeIsEdge, hdi] at hde
        | inr f =>
          have hval := congrArg (fun p : LatticePoint => p.2.2.2) hp
          have hv : e = f := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst f
          exact hci.trans hdi.symm
    · have hcn := hc.2 3 hji
      have hdn := hd.2 3 hji
      cases hci : c 3 with
      | inl v =>
        cases hdi : d 3 with
        | inl w =>
          have hval := congrArg (fun p : LatticePoint => p.2.2.2) hp
          have hv : v = w := by
            simpa [latticeCellPoint, latticeCellBaseCoordinate, hci, hdi] using hval
          subst w
          exact hci.trans hdi.symm
        | inr f => simp [latticeIsEdge, hdi] at hdn
      | inr e => simp [latticeIsEdge, hci] at hcn

noncomputable def globalLinkAxisSupport (μ : GlobalLinkField) (i : Fin 4) :
    Finset (LatticeCell 4) := by
  classical
  exact μ.1.support.filter (fun c => latticeLinkAxisCell c i)

noncomputable def globalLinkFourierComponent (μ : GlobalLinkField) (i : Fin 4)
    (k : Torus4) : ℂ :=
  ∑ c ∈ globalLinkAxisSupport μ i,
    (μ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k


private theorem globalLinkFourierComponent_cross_parseval
    (μ ν : GlobalLinkField) (i : Fin 4) :
    ∫ k : Torus4, globalLinkFourierComponent μ i k *
        conj (globalLinkFourierComponent ν i k) ∂torus4Haar =
      ∑ c ∈ globalLinkAxisSupport μ i ∪ globalLinkAxisSupport ν i,
        (μ.1 c : ℂ) * conj (ν.1 c : ℂ) := by
  classical
  let s := globalLinkAxisSupport μ i ∪ globalLinkAxisSupport ν i
  have hμ : finiteFourierPolynomialOn s latticeCellPoint (fun c => (μ.1 c : ℂ)) =
      globalLinkFourierComponent μ i := by
    funext k
    unfold finiteFourierPolynomialOn globalLinkFourierComponent
    change (∑ c ∈ s, (μ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k) = _
    symm
    apply Finset.sum_subset (Finset.subset_union_left)
    intro c hc hnot
    have hμnot : c ∉ globalLinkAxisSupport μ i := by
      intro hmem
      exact hnot hmem
    have hzero : μ.1 c = 0 := by
      by_contra hz
      have hm : c ∈ μ.1.support := Finsupp.mem_support_iff.mpr hz
      have hother : c ∈ globalLinkAxisSupport ν i := by
        rcases Finset.mem_union.mp hc with h | h
        · exact (hμnot h).elim
        · exact h
      have haxis : latticeLinkAxisCell c i := by
        have h' : ¬ ν.1 c = 0 ∧ latticeLinkAxisCell c i := by
          simpa [globalLinkAxisSupport] using hother
        exact h'.2
      have hmem : c ∈ globalLinkAxisSupport μ i := by
        simp [globalLinkAxisSupport, hm, haxis]
      exact hμnot hmem
    simp [hzero]
  have hν : finiteFourierPolynomialOn s latticeCellPoint (fun c => (ν.1 c : ℂ)) =
      globalLinkFourierComponent ν i := by
    funext k
    unfold finiteFourierPolynomialOn globalLinkFourierComponent
    change (∑ c ∈ s, (ν.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k) = _
    symm
    apply Finset.sum_subset (Finset.subset_union_right)
    intro c hc hnot
    have hνnot : c ∉ globalLinkAxisSupport ν i := by
      intro hmem
      exact hnot hmem
    have hzero : ν.1 c = 0 := by
      by_contra hz
      have hm : c ∈ ν.1.support := Finsupp.mem_support_iff.mpr hz
      have hother : c ∈ globalLinkAxisSupport μ i := by
        rcases Finset.mem_union.mp hc with h | h
        · exact h
        · exact (hνnot h).elim
      have haxis : latticeLinkAxisCell c i := by
        have h' : ¬ μ.1 c = 0 ∧ latticeLinkAxisCell c i := by
          simpa [globalLinkAxisSupport] using hother
        exact h'.2
      have hmem : c ∈ globalLinkAxisSupport ν i := by
        simp [globalLinkAxisSupport, hm, haxis]
      exact hνnot hmem
    simp [hzero]
  have hinj : ∀ ⦃c d⦄, c ∈ s → d ∈ s → latticeCellPoint c = latticeCellPoint d → c = d := by
    intro c d hc hd hp
    have hcaxis : latticeLinkAxisCell c i := by
      rcases Finset.mem_union.mp hc with h | h
      · have h' : c ∈ globalLinkAxisSupport μ i := h
        have h'' : ¬ μ.1 c = 0 ∧ latticeLinkAxisCell c i := by
          simpa [globalLinkAxisSupport] using h'
        exact h''.2
      · have h' : c ∈ globalLinkAxisSupport ν i := h
        have h'' : ¬ ν.1 c = 0 ∧ latticeLinkAxisCell c i := by
          simpa [globalLinkAxisSupport] using h'
        exact h''.2
    have hdaxis : latticeLinkAxisCell d i := by
      rcases Finset.mem_union.mp hd with h | h
      · have h' : d ∈ globalLinkAxisSupport μ i := h
        have h'' : ¬ μ.1 d = 0 ∧ latticeLinkAxisCell d i := by
          simpa [globalLinkAxisSupport] using h'
        exact h''.2
      · have h' : d ∈ globalLinkAxisSupport ν i := h
        have h'' : ¬ ν.1 d = 0 ∧ latticeLinkAxisCell d i := by
          simpa [globalLinkAxisSupport] using h'
        exact h''.2
    exact latticeCellPoint_injective_on_linkAxis i hcaxis hdaxis hp
  rw [← hμ, ← hν]
  exact finiteFourierCrossOn s latticeCellPoint
    (fun c => (μ.1 c : ℂ)) (fun c => (ν.1 c : ℂ)) hinj

theorem globalLinkFourierCrossParseval (μ ν : GlobalLinkField) :
    ∑ i : Fin 4, ∫ k : Torus4, globalLinkFourierComponent μ i k *
        conj (globalLinkFourierComponent ν i k) ∂torus4Haar =
      (globalPairing (μ : RealLatticeChain 4) (ν : RealLatticeChain 4) : ℂ) := by
  classical
  let s := μ.1.support ∪ ν.1.support
  have hs (i : Fin 4) :
      globalLinkAxisSupport μ i ∪ globalLinkAxisSupport ν i =
        s.filter (fun c => latticeLinkAxisCell c i) := by
    simp [s, globalLinkAxisSupport, Finset.filter_union]
  calc
    _ = ∑ i : Fin 4,
        ∑ c ∈ globalLinkAxisSupport μ i ∪ globalLinkAxisSupport ν i,
          (μ.1 c : ℂ) * conj (ν.1 c : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact globalLinkFourierComponent_cross_parseval μ ν i
    _ = ∑ i : Fin 4, ∑ c ∈ s.filter (fun c => latticeLinkAxisCell c i),
          (μ.1 c : ℂ) * conj (ν.1 c : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hs i]
    _ = ∑ c ∈ s, ∑ i : Fin 4,
          (if latticeLinkAxisCell c i then
            (μ.1 c : ℂ) * conj (ν.1 c : ℂ) else 0) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ c ∈ s, (μ.1 c : ℂ) * conj (ν.1 c : ℂ) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hdegree : latticeCellDegree c = 1 := by
        rcases Finset.mem_union.mp hc with h | h
        · exact μ.2 c h
        · exact ν.2 c h
      exact sum_single_linkAxis c
        ((μ.1 c : ℂ) * conj (ν.1 c : ℂ)) hdegree
    _ = (globalPairing (μ : RealLatticeChain 4) (ν : RealLatticeChain 4) : ℂ) := by
      rw [globalPairing_eq_union]
      dsimp [s]
      simp only [Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Fourier transform of an arbitrary finitely supported lattice chain, split
by its set of edge axes. -/
def latticeChainFourierComponent (q : RealLatticeChain 4)
    (axes : Finset (Fin 4)) (k : Torus4) : ℂ :=
  ∑ c ∈ q.support.filter (fun c => latticeCellAxes c = axes),
    (q c : ℂ) * latticeCharacter (latticeCellPoint c) k

noncomputable def latticeChainFourierFunctional (axes : Finset (Fin 4))
    (k : Torus4) : RealLatticeChain 4 →ₗ[ℝ] ℂ :=
  Finsupp.linearCombination ℝ (fun c : LatticeCell 4 =>
    if latticeCellAxes c = axes then latticeCharacter (latticeCellPoint c) k else 0)

theorem latticeChainFourierComponent_eq_functional (q : RealLatticeChain 4)
    (axes : Finset (Fin 4)) (k : Torus4) :
    latticeChainFourierComponent q axes k = latticeChainFourierFunctional axes k q := by
  classical
  unfold latticeChainFourierComponent latticeChainFourierFunctional
  rw [Finsupp.linearCombination_apply]
  change (∑ c ∈ q.support.filter (fun c => latticeCellAxes c = axes),
      (q c : ℂ) * latticeCharacter (latticeCellPoint c) k) =
    ∑ c ∈ q.support, (q c : ℂ) *
      (if latticeCellAxes c = axes then latticeCharacter (latticeCellPoint c) k else 0)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases haxes : latticeCellAxes c = axes <;> simp [haxes]

private theorem latticeChainFourierComponent_cross_parseval
    (q r : RealLatticeChain 4) (axes : Finset (Fin 4)) :
    ∫ k : Torus4, latticeChainFourierComponent q axes k *
        conj (latticeChainFourierComponent r axes k) ∂torus4Haar =
      ∑ c ∈ (q.support.filter (fun c => latticeCellAxes c = axes)) ∪
          (r.support.filter (fun c => latticeCellAxes c = axes)),
        (q c : ℂ) * conj (r c : ℂ) := by
  classical
  let sq := q.support.filter (fun c => latticeCellAxes c = axes)
  let sr := r.support.filter (fun c => latticeCellAxes c = axes)
  let s := sq ∪ sr
  have hq : finiteFourierPolynomialOn s latticeCellPoint (fun c => (q c : ℂ)) =
      latticeChainFourierComponent q axes := by
    funext k
    unfold finiteFourierPolynomialOn latticeChainFourierComponent
    change (∑ c ∈ s, (q c : ℂ) * latticeCharacter (latticeCellPoint c) k) = _
    symm
    apply Finset.sum_subset (Finset.subset_union_left)
    intro c hc hnot
    have hqnot : c ∉ sq := hnot
    have hother : c ∈ sr := (Finset.mem_union.mp hc).resolve_left hqnot
    have haxes : latticeCellAxes c = axes := (Finset.mem_filter.mp hother).2
    have hzero : q c = 0 := by
      by_contra hne
      have hmem : c ∈ q.support := Finsupp.mem_support_iff.mpr hne
      have hsmall : c ∈ sq := Finset.mem_filter.mpr ⟨hmem, haxes⟩
      exact hqnot hsmall
    simp [hzero]
  have hr : finiteFourierPolynomialOn s latticeCellPoint (fun c => (r c : ℂ)) =
      latticeChainFourierComponent r axes := by
    funext k
    unfold finiteFourierPolynomialOn latticeChainFourierComponent
    change (∑ c ∈ s, (r c : ℂ) * latticeCharacter (latticeCellPoint c) k) = _
    symm
    apply Finset.sum_subset (Finset.subset_union_right)
    intro c hc hnot
    have hrnot : c ∉ sr := hnot
    have hother : c ∈ sq := (Finset.mem_union.mp hc).resolve_right hrnot
    have haxes : latticeCellAxes c = axes := (Finset.mem_filter.mp hother).2
    have hzero : r c = 0 := by
      by_contra hne
      have hmem : c ∈ r.support := Finsupp.mem_support_iff.mpr hne
      have hsmall : c ∈ sr := Finset.mem_filter.mpr ⟨hmem, haxes⟩
      exact hrnot hsmall
    simp [hzero]
  have hinj : ∀ ⦃c d⦄, c ∈ s → d ∈ s →
      latticeCellPoint c = latticeCellPoint d → c = d := by
    intro c d hc hd hp
    have hca : latticeCellAxes c = axes := by
      rcases Finset.mem_union.mp hc with h | h
      · exact (Finset.mem_filter.mp h).2
      · exact (Finset.mem_filter.mp h).2
    have hda : latticeCellAxes d = axes := by
      rcases Finset.mem_union.mp hd with h | h
      · exact (Finset.mem_filter.mp h).2
      · exact (Finset.mem_filter.mp h).2
    exact latticeCellPoint_injective_of_axes_eq (hca.trans hda.symm) hp
  rw [← hq, ← hr]
  exact finiteFourierCrossOn s latticeCellPoint
    (fun c => (q c : ℂ)) (fun c => (r c : ℂ)) hinj

/-- Parseval for compact lattice chains, with the cubical orientation label
retained as a finite component index. -/
theorem latticeChainFourierCrossParseval (q r : RealLatticeChain 4) :
    ∑ axes : Finset (Fin 4),
      ∫ k : Torus4, latticeChainFourierComponent q axes k *
        conj (latticeChainFourierComponent r axes k) ∂torus4Haar =
      (globalPairing q r : ℂ) := by
  classical
  let s := q.support ∪ r.support
  have hs (axes : Finset (Fin 4)) :
      q.support.filter (fun c => latticeCellAxes c = axes) ∪
        r.support.filter (fun c => latticeCellAxes c = axes) =
      s.filter (fun c => latticeCellAxes c = axes) := by
    simp [s, Finset.filter_union]
  calc
    _ = ∑ axes : Finset (Fin 4),
        ∑ c ∈ q.support.filter (fun c => latticeCellAxes c = axes) ∪
            r.support.filter (fun c => latticeCellAxes c = axes),
          (q c : ℂ) * conj (r c : ℂ) := by
      apply Finset.sum_congr rfl
      intro axes haxes
      exact latticeChainFourierComponent_cross_parseval q r axes
    _ = ∑ axes : Finset (Fin 4), ∑ c ∈ s.filter
          (fun c => latticeCellAxes c = axes), (q c : ℂ) * conj (r c : ℂ) := by
      apply Finset.sum_congr rfl
      intro axes haxes
      rw [hs axes]
    _ = ∑ c ∈ s, ∑ axes : Finset (Fin 4),
          (if latticeCellAxes c = axes then (q c : ℂ) * conj (r c : ℂ) else 0) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ c ∈ s, (q c : ℂ) * conj (r c : ℂ) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_eq_single (latticeCellAxes c)]
      · simp
      · intro axes haxes hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    _ = (globalPairing q r : ℂ) := by
      rw [globalPairing_eq_union]
      dsimp [s]
      simp only [Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]


/-- Select a coordinate of the product torus. -/
def torus4Coord (k : Torus4) (i : Fin 4) : AddCircle (1 : ℝ) :=
  match i.val with
  | 0 => k.1
  | 1 => k.2.1
  | 2 => k.2.2.1
  | _ => k.2.2.2

/-- The nonnegative Fourier symbol of the positive lattice Laplacian.

Under the coordinate change `k_j = 2π x_j`, this is
`Σ_j 4 sin²(k_j / 2)`. -/
def fourierLaplacianSymbol (k : Torus4) : ℝ :=
  ∑ i : Fin 4, ‖(1 : ℂ) - fourier 1 (torus4Coord k i)‖ ^ 2

theorem fourierLaplacianSymbol_nonneg (k : Torus4) :
    0 ≤ fourierLaplacianSymbol k := by
  unfold fourierLaplacianSymbol
  apply Finset.sum_nonneg
  intro i hi
  exact sq_nonneg _

/-- The Green multiplier applied to a finite-support link field.  At the single
zero-frequency point the quotient uses Lean's totalized real division; that
point has Haar measure zero and does not affect an integrable representative. -/
def fourierGreenDensity (μ : GlobalLinkField) (k : Torus4) : ℝ :=
  ∑ i : Fin 4,
    ‖globalLinkFourierComponent μ i k‖ ^ 2 / fourierLaplacianSymbol k

theorem fourierGreenDensity_nonneg (μ : GlobalLinkField) (k : Torus4) :
    0 ≤ fourierGreenDensity μ k := by
  unfold fourierGreenDensity
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (sq_nonneg _) (fourierLaplacianSymbol_nonneg k)

/-- The normalized four-torus integral of the lattice Green multiplier.  Haar
measure is normalized to mass one, so this is `(2π)⁻⁴` times Lebesgue measure
on `[-π, π]⁴` under `k = 2πx`.  Its integrability for arbitrary finite support
is the four-dimensional singular-integrability gate. -/
noncomputable def fourierGreenQuadratic (μ : GlobalLinkField) : ℝ :=
  ∫ k : Torus4, fourierGreenDensity μ k ∂torus4Haar

end Fourier
