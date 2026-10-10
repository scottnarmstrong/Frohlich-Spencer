/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Duality
public import FroehlichSpencer.BKT.VillainDisorder.FejerCos
public import FroehlichSpencer.BKT.Coulomb.TheoremBSubGaussian
public import FroehlichSpencer.BKT.Duality.LineSourceField
public import FroehlichSpencer.BKT.Bridge.FreeGFFLaw
public import FroehlichSpencer.BKT.SpinWaves.ShellPacking
public import FroehlichSpencer.BKT.Reduction.T62ImpliesT13
public import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

/-!
# FS81 Theorem D for the Villain model

FS81 Theorem D (J p. 534): "For each ξ∈(0,1) there exists some finite β₀(ξ) such that for
β>β₀(ξ) ⟨D^ξ_{0x}⟩(β) ≤ const(1+|x|)^{−ξ²β″}, for some positive β″ = β″(ξ, β)". The proof
follows FS81 p. 572: "From (1.22) and (1.38) we see that Theorem D for the Villain model is a
special case of Theorem B for a general Coulomb gas."

1. **Duality** (`villainLaw_disorder_eq_igff`). `⟨D^ξ⟩` is the dual IGFF expectation
   `⟨cos(2πξ(h(x*) − h(0*)))⟩`, at inverse temperature `1/β`.
2. **Fejér cutoff** (`tendsto_gffFejerCosRatio_igff`). This expectation is the `N → ∞` limit of
   the GFF expectations of `cos(ξ(φ_{0*} − φ_{x*}))` with Fejér weights `∏_j F_N(φ_j)`, at
   `β_f = 1/((2π)² β)`. These are the fractional correlations `G_ξ` of the Villain gas
   (`λ ≡ 1`) with cutoff `N`.
3. **Theorem B** (`markedSquareBoundSubGaussian_exists`; Fejér weights are
   `(1, 0, 0)`-sub-Gaussian). On the dual free square, where `|0* − x*| = n`, it bounds each
   cutoff ratio by `2 exp(-(cB η²/β_f) log₂(n + 1))`. The bound passes to the limit.

* **`villainDisorder_bound`**: `0 ≤ ⟨D^ξ⟩_{Λ_L^zero}(β) ≤ 2 (n + 1)^{-c η² β}`.
  - The constants are `c = (2π)² cB / log 2` and `β₀ = 1/((2π)² β₁(1, η))`.
  - It holds for `β > β₀`, `min(ξ, 1 − ξ) ≥ η`, every wired box, and every string of `n ≥ 1` bonds.
* `CentredFits`, `centredDisorderInternal`: the string at a fixed `a ∈ ℤ²`, in the centred wired
  box of side `L`.
* **`villainDisorder_thermodynamicLimit`**: as `L → ∞`,
  - the same bound holds for every `L`;
  - a convergent subsequence exists;
  - every limit point satisfies the bound.

**Reading of the source.**
- FS81's exponent is `ξ²β''`; here it is `c η² β`, with `η ≤ min(ξ, 1 − ξ)`. So
  `β'' = c η² β / ξ² > 0`, and `β'' → ∞` as `β → ∞`.
- The threshold `β₀ = O(η⁻²)` depends only on `η`, and is uniform over `ξ ∈ [η, 1 − η]`
  (FS81: `β₀(ξ)`). The prefactor `2` is absolute.
- `|x| = n`, as in FS81's axial `x = (n, 0)`. The bound uses `n + 1`, as FS81 uses `1 + |x|`.
- The boxes are wired primal boxes (dual free squares); see `VillainDisorder/Duality`.
- Uniqueness of the thermodynamic limit is not claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FroehlichSpencer.BKT.VillainDisorder

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Duality FroehlichSpencer.BKT.Lattice2D
  FroehlichSpencer.BKT.Coulomb FroehlichSpencer.BKT.Generic.Marked

variable {L : ℕ}

/-- The real dipole `δ_{0'} − δ_{x'}` at the two dual faces at the ends of the string. -/
def stringDipole (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) :
    SquareFreeVertex (L + 1) → ℝ :=
  fun p => (if p = stringFace o n hfit 0 then 1 else 0) -
    (if p = stringFace o n hfit n then 1 else 0)

theorem pairing_stringDipole (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (φ : SquareFreeVertex (L + 1) → ℝ) :
    Multigraph.pairing φ (stringDipole o n hfit) =
      φ (stringFace o n hfit 0) - φ (stringFace o n hfit n) := by
  unfold Multigraph.pairing stringDipole
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

theorem stringFace_ne (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L)
    (hn : 0 < n) : stringFace o n hfit 0 ≠ stringFace o n hfit n := by
  intro h
  have := congrArg (fun p : SquareFreeVertex (L + 1) => p.1.val) h
  simp only [stringFace] at this
  omega

theorem latticeDistance_stringFace (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) :
    latticeDistance .free (L + 1) (stringFace o n hfit 0) (stringFace o n hfit n) = n := by
  show (squareFree (L + 1)).toSimpleGraph.dist _ _ = n
  rw [SpinWaves.squareFree_dist_eq_freeRadius (by omega)]
  simp only [freeRadius, stringFace, Nat.dist]
  omega

/-- **FS81 Theorem D on the wired boxes** (the Villain model, FS81 (1.32) with `f_β = v_β`).
There is an absolute `c > 0` such that for every `η > 0` there is `β₀` with: for every Villain
inverse temperature `β > β₀`, every `ξ` with `min(ξ, 1 − ξ) ≥ η`, every wired box `Λ_L^zero`
and every disorder string of `n ≥ 1` bonds in it,
`0 ≤ ⟨D^ξ_{0x}⟩_{Λ_L^zero}(β) ≤ 2 (n + 1)^{-c η² β}`. The constant is
`c = (2π)² cB / log 2` with `cB` the constant of Theorem B (`markedSquareBoundSubGaussian_exists`);
`β₀ = O(η⁻²)`. -/
theorem villainDisorder_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (L : ℕ) (β : ℝ) (hβ : 0 < β), β₀ < β → ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
        ∀ (o : Fin L × Fin L) (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L), 0 < n →
          0 ≤ ∫ θ, villainDisorderInternal β ξ o n hfit θ ∂villainLaw L β hβ ∧
            ∫ θ, villainDisorderInternal β ξ o n hfit θ ∂villainLaw L β hβ ≤
              2 * ((n : ℝ) + 1) ^ (-(c * η ^ 2 * β)) := by
  obtain ⟨cB, hcB, hB⟩ := markedSquareBoundSubGaussian_exists
  have hπ : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  refine ⟨(2 * Real.pi) ^ 2 * cB / Real.log 2,
    div_pos (mul_pos hπ hcB) (Real.log_pos (by norm_num)), fun η hη => ?_⟩
  obtain ⟨β₁, hβ₁, hB'⟩ := hB 1 η hη
  refine ⟨1 / ((2 * Real.pi) ^ 2 * β₁), by positivity, ?_⟩
  intro L β hβ hββ₀ ξ hξ0 hξ1 hηξ o n hfit hn
  have hL0 : 0 < L := by have := o.1.isLt; omega
  have hD0 : ∀ θ, 0 ≤ villainDisorderInternal β ξ o n hfit θ := fun θ =>
    Finset.prod_nonneg fun m _ => div_nonneg (VillainWeight.villainWeight_pos hβ _).le
      (VillainWeight.villainWeight_pos hβ _).le
  refine ⟨integral_nonneg hD0, ?_⟩
  -- the Fejér inverse temperature of the dual field
  set βf : ℝ := 1 / ((2 * Real.pi) ^ 2 * β) with hβfdef
  have hβf : 0 < βf := by positivity
  have hβfβ₁ : βf < β₁ := by
    rw [hβfdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hββ₀
    calc (1 : ℝ) < β * ((2 * Real.pi) ^ 2 * β₁) := hββ₀
      _ = β₁ * ((2 * Real.pi) ^ 2 * β) := by ring
  have hβeq : (2 * Real.pi) ^ 2 * βf = 1 / β := by
    rw [hβfdef]
    field_simp
  have hLf : 1 < L + 1 := by omega
  have hG : (squareFreeGraph (L + 1)).Connected := squareFreeGraph_connected (by omega)
  set p₀ := stringFace o n hfit 0 with hp₀
  set p₁ := stringFace o n hfit n with hp₁
  set f := stringDipole o n hfit with hf
  set ε : ℝ := 2 * Real.exp (-(cB * η ^ 2 / βf) * Real.logb 2 ((n : ℝ) + 1)) with hε
  -- Theorem B with the Fejér weights bounds every Fejér ratio
  have hratio : ∀ N : ℕ, 0 < N →
      (∫ φ, Real.cos (ξ * Multigraph.pairing φ f) * gffFejerWeight N φ
          ∂gffMeasure (squareFreeGraph (L + 1)) hG βf hβf (dualBoxRoot L)) /
        (∫ φ, gffFejerWeight N φ ∂gffMeasure (squareFreeGraph (L + 1)) hG βf hβf (dualBoxRoot L))
        ≤ ε := by
    intro N hN
    obtain ⟨hZ, hI⟩ := (hB' (L + 1) hLf).1 (dualBoxRoot L) βf hβf hβfβ₁
      (fun _ => fejerPolynomial N) (fun _ => isSubGaussian_fejerPolynomial N hN βf) p₀ p₁
      (stringFace_ne o n hfit hn) ξ hξ0 hξ1 hηξ
    rw [gffLaw_squareFree_eq_squareFreeGraph hLf hG] at hZ hI
    rw [latticeDistance_stringFace] at hI
    have hnum : ∫ φ, Real.cos (ξ * Multigraph.pairing φ f) * gffFejerWeight N φ
        ∂gffMeasure (squareFreeGraph (L + 1)) hG βf hβf (dualBoxRoot L) =
        ∫ φ, Real.cos (ξ * (φ p₀ - φ p₁)) * ∏ j, fejerPolynomial N (φ j)
          ∂gffLaw (squareFreeGraph (L + 1)) hG βf hβf (dualBoxRoot L) := by
      rw [gffLaw_eq_gffMeasure (squareFreeGraph (L + 1)) hG]
      refine integral_congr_ae (ae_of_all _ fun φ => ?_)
      simp only [hf, pairing_stringDipole, gffFejerWeight]
      rfl
    have hden : ∫ φ, gffFejerWeight N φ
        ∂gffMeasure (squareFreeGraph (L + 1)) hG βf hβf (dualBoxRoot L) =
        ∫ φ, ∏ j, fejerPolynomial N (φ j)
          ∂gffLaw (squareFreeGraph (L + 1)) hG βf hβf (dualBoxRoot L) := by
      rw [gffLaw_eq_gffMeasure (squareFreeGraph (L + 1)) hG]
      rfl
    rw [hnum, hden, div_le_iff₀ hZ]
    refine (le_abs_self _).trans (hI.trans (le_of_eq ?_))
    simp only [hε]
  -- the cell limit and the duality
  have hlim := tendsto_gffFejerCosRatio_igff (squareFreeGraph (L + 1)) hG βf hβf (dualBoxRoot L)
    ξ f
  have htarget : igffExpectation (squareFreeGraph (L + 1)) hG ((2 * Real.pi) ^ 2 * βf)
      (mul_pos (sq_pos_of_ne_zero (by positivity)) hβf) (dualBoxRoot L)
      (fun m => Real.cos (2 * Real.pi * ξ * Multigraph.pairing (fun j => (m.1 j : ℝ)) f)) =
      ∫ θ, villainDisorderInternal β ξ o n hfit θ ∂villainLaw L β hβ := by
    rw [villainLaw_disorder_eq_igff hL0 β hβ ξ o n hfit]
    rw [Reduction.igffExpectation_congr_beta _ _ hβeq _ (one_div_pos.mpr hβ)]
    unfold igffExpectation
    congr 1
    refine tsum_congr fun m => ?_
    congr 1
    dsimp only
    rw [pairing_stringDipole, ← Real.cos_neg]
    congr 1
    ring
  rw [← htarget]
  have hbound := le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => hratio N hN⟩)
  refine hbound.trans (le_of_eq ?_)
  -- the power law
  simp only [hε]
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.rpow_def_of_pos hd, Real.logb, hβfdef]
  congr 1
  field_simp

/-- The disorder string at `a ∈ ℤ²` with `n` bonds fits in the wired box of side `L` once `ℤ²` is
placed in the box by `(i, j) ↦ (i + ⌊L/2⌋, j + ⌊L/2⌋)`. -/
def CentredFits (L : ℕ) (a : ℤ × ℤ) (n : ℕ) : Prop :=
  0 ≤ a.1 + (L / 2 : ℕ) ∧ 0 ≤ a.2 + (L / 2 : ℕ) ∧
    (a.1 + (L / 2 : ℕ)).toNat + n < L ∧ (a.2 + (L / 2 : ℕ)).toNat + 1 < L

open Classical in
/-- **FS81's `⟨D^ξ_{0x}⟩` in the centred wired box** (FS81 (1.32), `f_β = v_β`): the
expectation, in the wired box of side `L` with `ℤ²` placed by `(i, j) ↦ (i + ⌊L/2⌋, j + ⌊L/2⌋)`,
of the disorder operator on the string of the `n` vertical bonds
`((a₁ + m, a₂), (a₁ + m, a₂ + 1))`, `m = 1, …, n`, of `ℤ²` (for `a = 0` the string of FS81
(1.32) from `0*` to `x* = (n, 0)*`); `0` when the string does not fit. -/
def centredDisorderInternal (L : ℕ) (β : ℝ) (hβ : 0 < β) (ξ : ℝ) (a : ℤ × ℤ) (n : ℕ) : ℝ :=
  if h : CentredFits L a n then
    ∫ θ, villainDisorderInternal β ξ
      (⟨(a.1 + (L / 2 : ℕ)).toNat, by have := h.2.2.1; omega⟩,
        ⟨(a.2 + (L / 2 : ℕ)).toNat, by have := h.2.2.2; omega⟩) n ⟨h.2.2.1, h.2.2.2⟩ θ
      ∂villainLaw L β hβ
  else 0

/-- Every disorder string fits in all large centred boxes. -/
theorem eventually_centredFits (a : ℤ × ℤ) (n : ℕ) : ∀ᶠ L in atTop, CentredFits L a n := by
  refine eventually_atTop.2 ⟨2 * (a.1.natAbs + a.2.natAbs + n + 2), fun L hL => ?_⟩
  unfold CentredFits
  omega

/-- **FS81 Theorem D in the thermodynamic limit** (the Villain model, `0 < ξ < 1`). There is an
absolute `c > 0` such that for every `η > 0` there is `β₀` with: for `β > β₀`,
`min(ξ, 1 − ξ) ≥ η` and every disorder string at `a ∈ ℤ²` of `n ≥ 1` bonds, the centred
wired-box expectations `⟨D^ξ⟩_L` (genuine for all large `L`) satisfy
`0 ≤ ⟨D^ξ⟩_L ≤ B = 2 (n + 1)^{-c η² β}`, have a convergent subsequence, and every limit point
`ℓ` (every thermodynamic-limit value) satisfies `0 ≤ ℓ ≤ B`. -/
theorem villainDisorder_thermodynamicLimit :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (β : ℝ) (hβ : 0 < β), β₀ < β → ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
        ∀ (a : ℤ × ℤ) (n : ℕ), 0 < n →
          (∀ᶠ L in atTop, CentredFits L a n) ∧
          (∀ L, 0 ≤ centredDisorderInternal L β hβ ξ a n ∧
            centredDisorderInternal L β hβ ξ a n ≤ 2 * ((n : ℝ) + 1) ^ (-(c * η ^ 2 * β))) ∧
          (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => centredDisorderInternal (φ k) β hβ ξ a n) atTop (𝓝 ℓ)) ∧
          ∀ ℓ : ℝ, MapClusterPt ℓ atTop (fun L => centredDisorderInternal L β hβ ξ a n) →
            0 ≤ ℓ ∧ ℓ ≤ 2 * ((n : ℝ) + 1) ^ (-(c * η ^ 2 * β)) := by
  obtain ⟨c, hc, hD⟩ := villainDisorder_bound
  refine ⟨c, hc, fun η hη => ?_⟩
  obtain ⟨β₀, hβ₀, hD'⟩ := hD η hη
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ ξ hξ0 hξ1 hηξ a n hn => ?_⟩
  set B : ℝ := 2 * ((n : ℝ) + 1) ^ (-(c * η ^ 2 * β)) with hB
  have hk : ∀ L, 0 ≤ centredDisorderInternal L β hβ ξ a n ∧
      centredDisorderInternal L β hβ ξ a n ≤ B := by
    intro L
    unfold centredDisorderInternal
    split_ifs with h
    · exact hD' L β hβ hββ₀ ξ hξ0 hξ1 hηξ _ n _ hn
    · exact ⟨le_rfl, by positivity⟩
  have hmem : ∀ L, centredDisorderInternal L β hβ ξ a n ∈ Set.Icc 0 B := fun L => hk L
  refine ⟨eventually_centredFits a n, hk, ?_,
    fun ℓ hℓ => isClosed_Icc.mem_of_mapClusterPt hℓ (Eventually.of_forall hmem)⟩
  obtain ⟨ℓ, -, φ, hφ, hT⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 B) hmem
  exact ⟨ℓ, φ, hφ, hT⟩

end FroehlichSpencer.BKT.VillainDisorder
