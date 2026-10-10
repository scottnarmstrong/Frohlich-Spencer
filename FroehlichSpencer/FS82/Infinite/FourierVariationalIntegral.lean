/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.FourierVariational
public import FroehlichSpencer.FS82.Infinite.FourierGreen

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Infinite.FourierVariational
open scoped ComplexConjugate

@[expose] public section


open MeasureTheory
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Infinite.FourierVariational
open scoped ComplexConjugate

namespace FroehlichSpencer.FS82.Infinite.FourierVariationalIntegral

abbrev PairI := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev AxesI := {s : Finset (Fin 4) // s.card = 2}

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : BorelSpace (AddCircle (1 : ℝ) ×
    (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by infer_instance
local instance : BorelSpace Torus4 := by
  dsimp [Torus4]
  infer_instance
local instance : IsFiniteMeasure torus4Haar := by
  dsimp [torus4Haar]
  infer_instance

private theorem integrable_complex_of_continuous (f : Torus4 → ℂ)
    (hf : Continuous f) (hm : Measurable f) : Integrable f torus4Haar := by
  have hcompact : IsCompact (Set.range fun k : Torus4 => ‖f k‖) := by
    simpa [Function.comp_def] using isCompact_univ.image (continuous_norm.comp hf)
  rcases hcompact.bddAbove with ⟨C, hC⟩
  change ∀ b ∈ Set.range (fun k : Torus4 => ‖f k‖), b ≤ C at hC
  apply Integrable.of_bound hm.aestronglyMeasurable C
  filter_upwards with k
  exact hC _ ⟨k, rfl⟩

private theorem integrable_real_of_continuous (f : Torus4 → ℝ)
    (hf : Continuous f) (hm : Measurable f) : Integrable f torus4Haar := by
  have hcompact : IsCompact (Set.range fun k : Torus4 => ‖f k‖) := by
    simpa [Function.comp_def] using isCompact_univ.image (continuous_norm.comp hf)
  rcases hcompact.bddAbove with ⟨C, hC⟩
  change ∀ b ∈ Set.range (fun k : Torus4 => ‖f k‖), b ≤ C at hC
  apply Integrable.of_bound hm.aestronglyMeasurable C
  filter_upwards with k
  exact hC _ ⟨k, rfl⟩

@[fun_prop] private theorem continuous_fourier_char (n : ℤ) :
    Continuous (fun t : AddCircle (1 : ℝ) => fourier n t) :=
  map_continuous (fourier n)


private theorem continuous_latticeCharacter (x : LatticePoint) :
    Continuous (latticeCharacter x) := by
  unfold latticeCharacter
  fun_prop [continuous_fourier_char]

private theorem continuous_chainComponent (q : RealLatticeChain 4)
    (axes : Finset (Fin 4)) :
    Continuous (latticeChainFourierComponent q axes) := by
  unfold latticeChainFourierComponent
  apply continuous_finsetSum
  intro c hc
  exact continuous_const.mul (continuous_latticeCharacter (latticeCellPoint c))

private theorem continuous_linkComponent (μ : GlobalLinkField) (i : Fin 4) :
    Continuous (globalLinkFourierComponent μ i) := by
  unfold globalLinkFourierComponent
  apply continuous_finsetSum
  intro c hc
  exact continuous_const.mul (continuous_latticeCharacter (latticeCellPoint c))

private theorem continuous_component_normSq (q : RealLatticeChain 4)
    (axes : Finset (Fin 4)) :
    Continuous (fun k : Torus4 => Complex.normSq
      (latticeChainFourierComponent q axes k)) := by
  have hc := continuous_chainComponent q axes
  have heq : (fun k : Torus4 => Complex.normSq
      (latticeChainFourierComponent q axes k)) =
      fun k => ‖latticeChainFourierComponent q axes k‖ ^ 2 := by
    funext k
    exact Complex.normSq_eq_norm_sq _
  rw [heq]
  exact (continuous_norm.comp hc).pow 2


private theorem integrable_linkCross (μ ν : GlobalLinkField) (i : Fin 4) :
    Integrable (fun k : Torus4 => globalLinkFourierComponent μ i k *
      conj (globalLinkFourierComponent ν i k)) torus4Haar := by
  apply integrable_complex_of_continuous
  · exact (continuous_linkComponent μ i).mul (continuous_linkComponent ν i).star
  · exact ((continuous_linkComponent μ i).mul
      (continuous_linkComponent ν i).star).measurable

private theorem continuous_curlEnergy (φ : GlobalLinkField) :
    Continuous (fourierFourierCurlEnergy φ) := by
  unfold fourierFourierCurlEnergy
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  by_cases hij : i < j
  · simpa [hij] using continuous_component_normSq
      (globalCoboundary (φ : RealLatticeChain 4)) {i,j}
  · simpa [hij] using (continuous_const : Continuous (fun _ : Torus4 => (0 : ℝ)))

private theorem integrable_component_normSq (q : RealLatticeChain 4)
    (axes : Finset (Fin 4)) :
    Integrable (fun k : Torus4 => Complex.normSq
      (latticeChainFourierComponent q axes k)) torus4Haar := by
  exact integrable_real_of_continuous _ (continuous_component_normSq q axes)
    (continuous_component_normSq q axes).measurable

private theorem integrable_curlEnergy (φ : GlobalLinkField) :
    Integrable (fourierFourierCurlEnergy φ) torus4Haar :=
  integrable_real_of_continuous (fourierFourierCurlEnergy φ) (continuous_curlEnergy φ)
    (continuous_curlEnergy φ).measurable


theorem ae_symbol_positive : ∀ᵐ k : Torus4 ∂torus4Haar,
    0 < fourierLaplacianSymbol k := by
  filter_upwards [Fourier.ae_torus4Coord_ne_zero 0] with k hk
  unfold fourierLaplacianSymbol
  apply Finset.sum_pos'
  · intro i hi
    exact sq_nonneg _
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have hfourier : fourier 1 (torus4Coord k 0) ≠ 1 := by
      intro h
      have hcircleCoe : (AddCircle.toCircle (torus4Coord k 0) : ℂ) =
          (AddCircle.toCircle (0 : AddCircle (1 : ℝ)) : ℂ) := by
        simpa [fourier_one] using h
      have hcircle : AddCircle.toCircle (torus4Coord k 0) =
          AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := Circle.coe_inj.mp hcircleCoe
      exact hk (AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hcircle)
    have hne : (1 : ℂ) - fourier 1 (torus4Coord k 0) ≠ 0 :=
      sub_ne_zero.mpr hfourier.symm
    have hnorm : 0 < ‖(1 : ℂ) - fourier 1 (torus4Coord k 0)‖ := norm_pos_iff.mpr hne
    positivity

noncomputable def axesMin (s : AxesI) : Fin 4 := s.val.min' (by
  have : 0 < s.val.card := by omega
  exact Finset.card_pos.mp this)
noncomputable def axesMax (s : AxesI) : Fin 4 := s.val.max' (by
  have : 0 < s.val.card := by omega
  exact Finset.card_pos.mp this)
theorem axesMin_lt_max (s : AxesI) : axesMin s < axesMax s := by
  unfold axesMin axesMax
  have hcard : 1 < s.val.card := by omega
  exact Finset.min'_lt_max'_of_card s.val hcard
theorem axesPair_eq (s : AxesI) : ({axesMin s, axesMax s} : Finset (Fin 4)) = s.val := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · subst x
      exact Finset.min'_mem _ _
    · subst x
      exact Finset.max'_mem _ _
  · rw [Finset.card_pair (ne_of_lt (axesMin_lt_max s)), s.property]
noncomputable def axesPairEquiv : PairI ≃ AxesI where
  toFun p := ⟨{p.val.1, p.val.2}, Finset.card_pair (ne_of_lt p.property)⟩
  invFun s := ⟨(axesMin s, axesMax s), axesMin_lt_max s⟩
  left_inv p := by
    classical
    rcases p with ⟨⟨i,j⟩, hij⟩
    apply Subtype.ext
    simp only [axesMin, axesMax]
    have hs : ({i,j} : Finset (Fin 4)).Nonempty := by simp
    have hmin : ({i,j} : Finset (Fin 4)).min' hs = i := by
      rw [Finset.min'_eq_iff]
      constructor
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · subst x; exact le_rfl
        · subst x; exact hij.le
    have hmax : ({i,j} : Finset (Fin 4)).max' hs = j := by
      rw [Finset.max'_eq_iff]
      constructor
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · subst x; exact hij.le
        · subst x; exact le_rfl
    exact Prod.ext hmin hmax
  right_inv s := by
    apply Subtype.ext
    exact axesPair_eq s

private theorem sum_axes_eq_pairs {M : Type} [AddCommMonoid M]
    (f : Finset (Fin 4) → M)
    (hzero : ∀ axes, axes.card ≠ 2 → f axes = 0) :
    (∑ axes : Finset (Fin 4), f axes) =
      ∑ i : Fin 4, ∑ j : Fin 4, if i < j then f {i,j} else 0 := by
  classical
  let p : Finset (Finset (Fin 4)) := Finset.univ.filter (fun s => s.card = 2)
  have hfilter : (∑ s ∈ p, f s) = ∑ s : Finset (Fin 4), f s := by
    apply Finset.sum_subset (Finset.subset_univ p)
    intro s hs hnot
    have hcard : s.card ≠ 2 := by
      intro hc
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    exact hzero s hcard
  have hsubtype : (∑ s ∈ p, f s) = ∑ s : AxesI, f s.val := by
    exact Finset.sum_subtype p (by intro s; simp [p]) f
  have hequiv : (∑ p : PairI, f {p.val.1, p.val.2}) =
      ∑ s : AxesI, f s.val := by
    exact Fintype.sum_equiv axesPairEquiv
      (fun q : PairI => f {q.val.1,q.val.2})
      (fun s : AxesI => f s.val)
      (by intro q; rfl)
  have hpairs : (∑ q : PairI, f {q.val.1, q.val.2}) =
      ∑ i : Fin 4, ∑ j : Fin 4, if i < j then f {i,j} else 0 := by
    calc
      _ = ∑ q ∈ (Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2)),
          f {q.1,q.2} := by
        symm
        exact Finset.sum_subtype _ (by intro q; simp) (fun q : Fin 4 × Fin 4 => f {q.1,q.2})
      _ = ∑ q : Fin 4 × Fin 4, if q.1 < q.2 then f {q.1,q.2} else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ i : Fin 4, ∑ j : Fin 4, if i < j then f {i,j} else 0 := by
        rw [Fintype.sum_prod_type]
  calc
    (∑ axes : Finset (Fin 4), f axes) = ∑ s ∈ p, f s := hfilter.symm
    _ = ∑ s : AxesI, f s.val := hsubtype
    _ = ∑ q : PairI, f {q.val.1,q.val.2} := hequiv.symm
    _ = _ := hpairs

theorem curl_parseval (φ : GlobalLinkField) :
    globalNormSq (globalCoboundary (φ : RealLatticeChain 4)) =
      ∫ k : Torus4, fourierFourierCurlEnergy φ k ∂torus4Haar := by
  classical
  let q : RealLatticeChain 4 := globalCoboundary (φ : RealLatticeChain 4)
  have hparseval0 := latticeChainFourierCrossParseval
    (globalCoboundary (φ : RealLatticeChain 4))
    (globalCoboundary (φ : RealLatticeChain 4))
  have hparseval :
      (∑ axes : Finset (Fin 4), ∫ k : Torus4,
        latticeChainFourierComponent q axes k *
          conj (latticeChainFourierComponent q axes k) ∂torus4Haar) =
        (globalPairing q q : ℂ) := by
    simpa only [q] using hparseval0
  have hsumzero (axes : Finset (Fin 4)) (hcard : axes.card ≠ 2) :
      (∫ k : Torus4, latticeChainFourierComponent q axes k *
        conj (latticeChainFourierComponent q axes k) ∂torus4Haar) = 0 := by
    have hzero (k : Torus4) := coboundaryFourierComponent_zero_of_axes_card_ne_two φ axes k hcard
    simp [q, hzero]
  have hsum := sum_axes_eq_pairs
    (fun axes => ∫ k : Torus4, latticeChainFourierComponent q axes k *
      conj (latticeChainFourierComponent q axes k) ∂torus4Haar) hsumzero
  have hpair (i j : Fin 4) (hij : i < j) :
      (∫ k : Torus4, latticeChainFourierComponent q {i,j} k *
        conj (latticeChainFourierComponent q {i,j} k) ∂torus4Haar) =
      ↑(∫ k : Torus4, Complex.normSq
        (latticeChainFourierComponent q {i,j} k) ∂torus4Haar) := by
    calc
      _ = ∫ k : Torus4, (Complex.normSq
          (latticeChainFourierComponent q {i,j} k) : ℂ) ∂torus4Haar := by
        apply integral_congr_ae
        filter_upwards with k
        rw [Complex.mul_conj]
      _ = _ := integral_complex_ofReal
  have hparseval' :
      (∑ i : Fin 4, ∑ j : Fin 4, if i < j then
        ↑(∫ k : Torus4, Complex.normSq (latticeChainFourierComponent q {i,j} k)
          ∂torus4Haar) else 0) =
       (globalPairing q q : ℂ) := by
    calc
      _ = ∑ i : Fin 4, ∑ j : Fin 4, if i < j then
          (∫ k : Torus4, latticeChainFourierComponent q {i,j} k *
            conj (latticeChainFourierComponent q {i,j} k) ∂torus4Haar) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i < j
        · simp only [hij]
          rw [hpair i j hij]
        · simp [hij]
      _ = ∑ axes : Finset (Fin 4),
          ∫ k : Torus4, latticeChainFourierComponent q axes k *
            conj (latticeChainFourierComponent q axes k) ∂torus4Haar := hsum.symm
      _ = (globalPairing q q : ℂ) := hparseval
  have henergy :
      (∑ i : Fin 4, ∑ j : Fin 4, if i < j then
        ∫ k : Torus4, Complex.normSq
          (latticeChainFourierComponent q {i,j} k) ∂torus4Haar else 0) =
       globalNormSq q := by
    have hreal := congrArg Complex.re hparseval'
    simp only [Complex.re_sum] at hreal
    have hrecast (i j : Fin 4) :
        (if i < j then
          (↑(∫ k : Torus4, Complex.normSq
            (latticeChainFourierComponent q {i,j} k) ∂torus4Haar) : ℂ)
          else 0).re =
        if i < j then ∫ k : Torus4, Complex.normSq
          (latticeChainFourierComponent q {i,j} k) ∂torus4Haar else 0 := by
      by_cases hij : i < j <;> simp [hij, Complex.ofReal_re]
    have hsumreal :
        (∑ i : Fin 4, ∑ j : Fin 4, if i < j then
          ∫ k : Torus4, Complex.normSq
            (latticeChainFourierComponent q {i,j} k) ∂torus4Haar else 0) =
        ∑ i : Fin 4, ∑ j : Fin 4, (if i < j then
          (↑(∫ k : Torus4, Complex.normSq
            (latticeChainFourierComponent q {i,j} k) ∂torus4Haar) : ℂ)
          else 0).re := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (hrecast i j).symm
    rw [← hsumreal] at hreal
    simpa [globalNormSq] using hreal
  have hintegral :
      (∫ k : Torus4, fourierFourierCurlEnergy φ k ∂torus4Haar) =
      ∑ i : Fin 4, ∑ j : Fin 4, if i < j then
        ∫ k : Torus4, Complex.normSq
          (latticeChainFourierComponent q {i,j} k) ∂torus4Haar else 0 := by
    change (∫ k : Torus4, ∑ i : Fin 4, ∑ j : Fin 4,
      if i < j then Complex.normSq
        (latticeChainFourierComponent q {i,j} k) else 0 ∂torus4Haar) = _
    rw [integral_finsetSum Finset.univ (fun i hi =>
      integrable_finsetSum Finset.univ (fun j hj => by
        by_cases hij : i < j
        · simp only [hij]
          exact integrable_component_normSq q {i,j}
        · simp [hij]))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum Finset.univ (fun j hj => by
      by_cases hij : i < j
      · simp only [hij]
        exact integrable_component_normSq q {i,j}
      · simp [hij])]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij]
      rfl
    · simp [hij]
  rw [hintegral]
  exact henergy.symm

theorem linear_pairing_parseval (μ φ : GlobalLinkField) :
    globalPairing (μ : RealLatticeChain 4) (φ : RealLatticeChain 4) =
      ∑ i : Fin 4, ∫ k : Torus4,
        (globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar := by
  classical
  have hcross := globalLinkFourierCrossParseval φ μ
  have hreal := congrArg Complex.re hcross
  rw [Complex.re_sum] at hreal
  have hpoint (i : Fin 4) :
      (∫ k : Torus4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k) ∂torus4Haar).re =
      ∫ k : Torus4,
        (globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar := by
    exact (integral_re (integrable_linkCross φ μ i)).symm
  have hreal' : (globalPairing (φ : RealLatticeChain 4)
      (μ : RealLatticeChain 4) : ℝ) =
      ∑ i : Fin 4, ∫ k : Torus4,
        (globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar := by
    simpa [hpoint] using hreal.symm
  rw [globalPairing_symm] at hreal'
  exact hreal'

theorem variational_objective_integral (μ φ : GlobalLinkField) :
    globalVariationalObjective μ φ =
      ∫ k : Torus4,
        (2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re -
          fourierFourierCurlEnergy φ k) ∂torus4Haar := by
  unfold globalVariationalObjective
  have hlinear := linear_pairing_parseval μ φ
  have hcurl := curl_parseval φ
  have hcomplexcont : Continuous (fun k : Torus4 =>
      ∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)) := by
    apply continuous_finsetSum
    intro i hi
    exact (continuous_linkComponent φ i).mul (continuous_linkComponent μ i).star
  have hlincont : Continuous (fun k : Torus4 =>
      2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re) := by
    exact (Complex.continuous_re.comp hcomplexcont).const_mul 2
  have hlinmeas := hlincont.measurable
  have hlinint := integrable_real_of_continuous
    (fun k : Torus4 => 2 * (∑ i : Fin 4,
      globalLinkFourierComponent φ i k * conj (globalLinkFourierComponent μ i k)).re)
    hlincont hlinmeas
  have hcurlint := integrable_curlEnergy φ
  have hrealComponent (i : Fin 4) :
      Integrable (fun k : Torus4 =>
        (globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re) torus4Haar := by
    have hc := Complex.continuous_re.comp
      ((continuous_linkComponent φ i).mul (continuous_linkComponent μ i).star)
    exact integrable_real_of_continuous _ hc hc.measurable
  have hlin_sum :
      (∫ k : Torus4, 2 * ∑ i : Fin 4,
        (globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar) =
      2 * ∑ i : Fin 4, ∫ k : Torus4,
        (globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar := by
    calc
      _ = ∫ k : Torus4, 2 * (∑ i : Fin 4,
          globalLinkFourierComponent φ i k *
            conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar := by
        apply integral_congr_ae
        filter_upwards with k
        rw [Complex.re_sum]
      _ = ∫ k : Torus4, 2 * ∑ i : Fin 4,
          (globalLinkFourierComponent φ i k *
            conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar := by
        apply integral_congr_ae
        filter_upwards with k
        rw [Complex.re_sum]
      _ = 2 * ∑ i : Fin 4, ∫ k : Torus4,
          (globalLinkFourierComponent φ i k *
            conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar := by
        rw [integral_const_mul, integral_finsetSum Finset.univ
          (fun i hi => hrealComponent i)]
  calc
    _ = 2 * globalPairing (μ : RealLatticeChain 4) (φ : RealLatticeChain 4) -
        globalNormSq (globalCoboundary (φ : RealLatticeChain 4)) := rfl
    _ = 2 * ∑ i : Fin 4, ∫ k : Torus4,
          (globalLinkFourierComponent φ i k *
            conj (globalLinkFourierComponent μ i k)).re ∂torus4Haar -
        ∫ k : Torus4, fourierFourierCurlEnergy φ k ∂torus4Haar := by
      rw [hlinear, hcurl]
    _ = (∫ k : Torus4, 2 * (∑ i : Fin 4,
          (globalLinkFourierComponent φ i k *
            conj (globalLinkFourierComponent μ i k)).re) ∂torus4Haar) -
        ∫ k : Torus4, fourierFourierCurlEnergy φ k ∂torus4Haar := by
      rw [hlin_sum.symm]
    _ = ∫ k : Torus4,
        (2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)).re -
          fourierFourierCurlEnergy φ k) ∂torus4Haar := by
      rw [integral_sub hlinint hcurlint]
      congr 1

private theorem integrable_variational_integrand (μ φ : GlobalLinkField) :
    Integrable (fun k : Torus4 =>
      2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re -
        fourierFourierCurlEnergy φ k) torus4Haar := by
  have hc : Continuous (fun k : Torus4 =>
      ∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)) := by
    apply continuous_finsetSum
    intro i hi
    exact (continuous_linkComponent φ i).mul
      (continuous_linkComponent μ i).star
  have hl : Continuous (fun k : Torus4 =>
      2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re) :=
    (Complex.continuous_re.comp hc).const_mul 2
  have hi : Integrable (fun k : Torus4 =>
      2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re) torus4Haar :=
    integrable_real_of_continuous _ hl hl.measurable
  exact hi.sub (integrable_curlEnergy φ)

theorem globallyCoClosed_variational_fourier_upper
    (μ φ : GlobalLinkField) (hμ : globallyCoClosed μ) :
    globalVariationalObjective μ φ ≤ fourierGreenQuadratic μ := by
  rw [variational_objective_integral μ φ, fourierGreenQuadratic]
  apply integral_mono_ae (integrable_variational_integrand μ φ)
    (Fourier.integrable_fourierGreenDensity μ)
  filter_upwards [ae_symbol_positive] with k hk
  exact globallyCoClosed_fourier_pointwise_bound μ φ hμ k hk

theorem globallyCoClosed_covariance_fourier_upper
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ) :
    globalVariationalCovariance μ ≤ fourierGreenQuadratic μ := by
  rw [globalVariationalCovariance]
  apply csSup_le
  · refine ⟨globalVariationalObjective μ ⟨0, by simp [latticeCellDegree]⟩, ?_⟩
    exact ⟨⟨0, by simp [latticeCellDegree]⟩, rfl⟩
  · intro r hr
    rcases hr with ⟨φ, rfl⟩
    exact globallyCoClosed_variational_fourier_upper μ φ hμ

/-- Completing the square in the finite-dimensional Fourier Hodge form. -/
theorem fourierPairCurlEnergy_completion (a m u : Fin 4 → ℂ)
    (hLam : 0 < fourierHodgeNormSq a) :
    2 * (fourierHodgePair u m).re - fourierPairCurlEnergy a u =
      fourierHodgeNormSq m / fourierHodgeNormSq a -
        fourierHodgeNormSq a * fourierHodgeNormSq
          (fun i => u i - m i / (fourierHodgeNormSq a : ℂ)) +
        Complex.normSq (fourierHodgeInner a u) := by
  let lam := fourierHodgeNormSq a
  have hlam' : 0 < lam := hLam
  have hpoint (i : Fin 4) :
      Complex.normSq (u i - m i / (lam : ℂ)) =
        Complex.normSq (u i) + Complex.normSq (m i) / lam ^ 2 -
          2 * (u i * conj (m i)).re / lam := by
    rw [Complex.normSq_sub]
    simp only [Complex.normSq_div, Complex.normSq_ofReal]
    have hc : conj (m i / (lam : ℂ)) = conj (m i) / (lam : ℂ) := by simp
    rw [hc, ← mul_div_assoc, Complex.div_ofReal_re]
    field_simp [ne_of_gt hlam']
  have hnorm : lam * fourierHodgeNormSq (fun i => u i - m i / (lam : ℂ)) =
      lam * fourierHodgeNormSq u + fourierHodgeNormSq m / lam -
        2 * (fourierHodgePair u m).re := by
    unfold fourierHodgeNormSq fourierHodgePair
    have hscaled (i : Fin 4) :
        lam * Complex.normSq (u i - m i / (lam : ℂ)) =
          lam * Complex.normSq (u i) + Complex.normSq (m i) / lam -
            2 * (u i * conj (m i)).re := by
      rw [hpoint i]
      field_simp [ne_of_gt hlam']
    calc
      lam * ∑ i : Fin 4, Complex.normSq (u i - m i / (lam : ℂ)) =
          ∑ i : Fin 4, lam * Complex.normSq (u i - m i / (lam : ℂ)) := by
        rw [Finset.mul_sum]
      _ = ∑ i : Fin 4, (lam * Complex.normSq (u i) +
            Complex.normSq (m i) / lam - 2 * (u i * conj (m i)).re) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hscaled i
      _ = lam * ∑ i : Fin 4, Complex.normSq (u i) +
            (∑ i : Fin 4, Complex.normSq (m i)) / lam -
            2 * (∑ i : Fin 4, (u i * conj (m i)).re) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.sum_div, ← Finset.mul_sum]
        simp_rw [← Finset.mul_sum]
  have hcurl := fourierPairCurlEnergy_identity a u
  rw [hcurl]
  change 2 * (fourierHodgePair u m).re -
      (lam * fourierHodgeNormSq u - Complex.normSq (fourierHodgeInner a u)) =
    fourierHodgeNormSq m / lam -
      lam * fourierHodgeNormSq (fun i => u i - m i / (lam : ℂ)) +
      Complex.normSq (fourierHodgeInner a u)
  rw [hnorm]
  ring

end FourierVariationalIntegral
