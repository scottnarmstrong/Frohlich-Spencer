/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Reduction.T16ImpliesT13
public import FroehlichSpencer.BKT.Duality.Expectation
public import FroehlichSpencer.BKT.Surface.SquareZero
public import FroehlichSpencer.BKT.Surface.VillainLaw
public import FroehlichSpencer.BKT.Villain.SquareSymmetry
public import Mathlib.Combinatorics.SimpleGraph.Metric
import FroehlichSpencer.BKT.Bridge.FreeGFFLaw
import FroehlichSpencer.BKT.Bridge.GFFMeasure
import FroehlichSpencer.BKT.Bridge.WiredBoxSymmetry
import FroehlichSpencer.BKT.Bridge.WiredVillainModel
import FroehlichSpencer.BKT.Duality.LineSourceField
import FroehlichSpencer.BKT.Gaussian.FejerAverage
import FroehlichSpencer.BKT.Gaussian.FejerCellLimit
import FroehlichSpencer.BKT.Lattice2D.C64Transfer

/-!
Neither KP Theorem 1.3 nor 1.6 is
imported; `t62Statement` is the corrected KP Theorem 6.2 (`Reduction/T16ImpliesT13.lean`).

Write `β` for the Villain inverse temperature, `β_height = 1/β` and
`β_field = β_height / (2π)²`.

For a free vertex `x = (x₀, x₁)` of `Λ_L^zero`:

1. **T6.2 with Fejér weights.** On the free `(L+1)`-box, at `β_field`, with root the lower-left
   dual face, `y₀ = x₀ + 1`, `y₁ = x₁` and the weights `F_N` (which are `(1, 0, 0)`-sub-Gaussian),
   T6.2 bounds the Fejér ratio of the line observable below by `(L − x₀ + 1)^{−c β_field}`.

The
    free square and the internal dual box `squareFreeGraph (L+1)` have the same GFF law
   (`gffLaw_squareFree_eq_squareFreeGraph`).
2. **Cell limit.** As `N → ∞` the ratio tends to the rooted IGFF expectation at
   `(2π)² β_field = β_height` (`tendsto_gffFejerRatio_igff`), which is KP Proposition 6.1's line
   observable (`kpPrintedLineSourceFieldObservable_eq`).
3. **Proposition 6.1** (`villainCosExpectation_eq_kpProposition61`) turns this into the internal
   wired-box Villain cosine expectation; with `C = c / (2π)²` the bound is
   `(L − x₀ + 1)^{−C/β}` (`villainCos_line_bound_of_t62`).
4. **Symmetries.** On the right-side class `L − x₀ = depth(x) + 1`, so the base is
   `depth(x) + 2`; `wiredBox_allFree_villainCosExpectation_bound_of_rightSide` extends the
   bound to every free vertex.
5. **Carrier identification.** The proved `villainWiredBridgeStatement_proved`  identifies the
    wired distance (`dist (x, z) = depth(x) + 1`) and the Villain cosine expectation
   with the internal ones.

At the wired vertex the angle is pinned (`integral_cos_none_villainLaw`).

`t13_of_t62` proves the statement of the `villain_powerLaw_lower_bound` from
`t62Statement` and the bridge, with `β₀ = 1 / ((2π)² β₀^{6.2}(1, 0, 0))`.

`t13_of_t16Statement` composes it with `t62Statement_of_t16Statement`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Reduction

open MeasureTheory Filter Topology


def villainWiredBridgeStatement : Prop :=
  ∀ (L : ℕ), 1 < L → ∀ (β : ℝ) (hβ : 0 < β) (x : Fin L × Fin L),
    (squareZero L).toSimpleGraph.dist (some x) none = wiredBoundaryDepth L x + 1 ∧
    ∫ θ, Real.cos (θ (some x)) ∂(villainLaw L β hβ) =
      Villain.villainCosExpectation (Duality.wiredBoxGraph L) none β
        ⟨some x, Option.some_ne_none _⟩

/--
The wired-distance and Villain-law bridge follows from the explicit carrier
isomorphism and the pushforward of the pinned angle measure (KP p. 2, §6.1).
-/
theorem villainWiredBridgeStatement_proved : villainWiredBridgeStatement := by
  intro L hL β hβ x
  exact ⟨Duality.squareZero_dist_root_eq L hL x,
    Duality.villainLaw_cosIntegral_eq_villainCosExpectation L β hβ x⟩

/-- The rooted IGFF expectation depends on the inverse temperature only through its value. -/
theorem igffExpectation_congr_beta {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) {β β' : ℝ} (h : β = β') (hβ : 0 < β) (hβ' : 0 < β')
    (root : V) (F : pinnedIntegerField V root → ℝ) :
    igffExpectation G hG β hβ root F = igffExpectation G hG β' hβ' root F := by
  subst h
  rfl

/-- **T6.2 ⇒ the line bound on the internal wired box** ( with  and KP
Proposition 6.1): there are `β₀, C > 0` such that for `β > β₀` the Villain cosine expectation at
every free vertex `x` of the internal wired box is at least `(L − x₀ + 1)^{−C/β}`. -/
theorem villainCos_line_bound_of_t62 (hT62 : t62Statement) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧ ∀ (L : ℕ), 1 < L → ∀ β : ℝ, β₀ < β →
      ∀ site : Lattice2D.SquareFreeVertex L,
        ((L - site.1.val + 1 : ℕ) : ℝ) ^ (-C / β) ≤
          Villain.villainCosExpectation (Duality.wiredBoxGraph L) none β
            ⟨some site, Option.some_ne_none _⟩ := by
  obtain ⟨c, hc, hT⟩ := hT62
  obtain ⟨βf₀, hβf₀, hT'⟩ := hT 1 one_pos 0 0 le_rfl (by norm_num)
  have ha : 0 < (2 * Real.pi) ^ 2 := by positivity
  refine ⟨1 / ((2 * Real.pi) ^ 2 * βf₀), c / (2 * Real.pi) ^ 2, by positivity, by positivity, ?_⟩
  intro L hL β hββ site
  have hβ : 0 < β := lt_trans (by positivity) hββ
  set βf : ℝ := 1 / ((2 * Real.pi) ^ 2 * β) with hβfdef
  have hβf : 0 < βf := by positivity
  have hβflt : βf < βf₀ := by
    rw [hβfdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hββ
    calc (1 : ℝ) < β * ((2 * Real.pi) ^ 2 * βf₀) := hββ
      _ = βf₀ * ((2 * Real.pi) ^ 2 * β) := by ring
  have hβeq : (2 * Real.pi) ^ 2 * βf = 1 / β := by
    rw [hβfdef]
    field_simp
  have hLf : 1 < L + 1 := by omega
  have hG : (Lattice2D.squareFreeGraph (L + 1)).Connected :=
    Lattice2D.squareFreeGraph_connected (by omega)
  set root : Lattice2D.SquareFreeVertex (L + 1) := Duality.dualBoxRoot L with hroot
  have hy₀ : site.1.val + 1 < L + 1 := by have := site.1.isLt; omega
  have hy₁ : site.2.val + 1 < L + 1 := by have := site.2.isLt; omega
  set fy := Lattice2D.squareFreeLineSource (L + 1) (site.1.val + 1) site.2.val with hfy
  set g : Lattice2D.SquareFreeVertex (L + 1) → ℝ := fun j => -(2 * Real.pi * βf) * fy j with hg
  set Nn : ℕ := L + 1 - (site.1.val + 1) with hNn
  set K := Real.exp (-(2 * Real.pi ^ 2 * βf * (Nn : ℝ))) with hK
  -- Step 1: T6.2 with Fejér weights bounds every Fejér ratio.
  have hfejer : ∀ N : ℕ, 0 < N → ((L + 1 - (site.1.val + 1) + 1 : ℕ) : ℝ) ^ (-(c * βf)) ≤
      K * gffFejerRatio (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root g N := by
    intro N hN
    have h := hT' (L + 1) hLf root βf hβf hβflt (fun _ => fejerPolynomial N)
      (fun _ => isSubGaussian_fejerPolynomial N hN βf) (site.1.val + 1) site.2.val hy₀ hy₁
    rw [gffLaw_squareFree_eq_squareFreeGraph hLf hG] at h
    have hnum : ∫ φ, Real.exp (-2 * Real.pi * βf * ∑ t : Fin (L + 1) with site.1.val + 1 ≤ t.val,
          (φ (t, ⟨site.2.val, by omega⟩) - φ (t, ⟨site.2.val + 1, hy₁⟩) + 2 * Real.pi / 2)) *
          ∏ j, fejerPolynomial N (φ j)
          ∂(gffLaw (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root) =
        K * gffFejerAverage (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root g N := by
      rw [gffFejerAverage_eq_integral, gffLaw_eq_gffMeasure _ hG, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun φ => ?_)
      simp only
      rw [lineObservable_eq (L + 1) (site.1.val + 1) site.2.val hy₁ βf φ]
      simp only [Multigraph.pairing, hg, hK, hNn]
      ring
    have hden : ∫ φ, ∏ j, fejerPolynomial N (φ j)
          ∂(gffLaw (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root) =
        gffFejerAverage (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root (fun _ => 0) N := by
      rw [gffFejerAverage_eq_integral, gffLaw_eq_gffMeasure _ hG]
      refine integral_congr_ae (ae_of_all _ fun φ => ?_)
      simp [Multigraph.pairing]
    rw [hnum, hden] at h
    unfold gffFejerRatio
    rwa [mul_div_assoc] at h
  -- Step 2: the cell limit.
  have hlim := (tendsto_gffFejerRatio_igff (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root
    g).const_mul K
  have hbound : ((L + 1 - (site.1.val + 1) + 1 : ℕ) : ℝ) ^ (-(c * βf)) ≤
      K * gffFejerIGFFTarget (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root g :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => hfejer N hN⟩)
  -- Step 3: the limit is KP Proposition 6.1's line expectation.
  have htarget : K * gffFejerIGFFTarget (Lattice2D.squareFreeGraph (L + 1)) hG βf hβf root g =
      Villain.villainCosExpectation (Duality.wiredBoxGraph L) none β
        ⟨some site, Option.some_ne_none _⟩ := by
    rw [Duality.villainCosExpectation_eq_kpProposition61 hL β hβ site]
    unfold gffFejerIGFFTarget
    rw [← igffExpectation_const_mul]
    have hobs : (fun m : pinnedIntegerField (Lattice2D.SquareFreeVertex (L + 1)) root =>
        K * Real.exp (Multigraph.pairing (fun j => (m.1 j : ℝ)) (fun j => 2 * Real.pi * g j))) =
        Duality.kpPrintedLineSourceObservable β site := by
      funext m
      rw [Duality.kpPrintedLineSourceObservable_eq_field, kpPrintedLineSourceFieldObservable_eq]
      have hp : (fun j => 2 * Real.pi * g j) = fun j => -(1 / β) * fy j := by
        funext j
        simp only [hg]
        rw [← hβeq]
        ring
      have hKeq : K = Real.exp (-(((L - site.1.val : ℕ) : ℝ) / (2 * β))) := by
        rw [hK, hNn]
        congr 1
        have hn : L + 1 - (site.1.val + 1) = L - site.1.val := by omega
        rw [hn, hβfdef]
        field_simp
      rw [hp, hKeq, mul_comm]
    rw [hobs]
    exact igffExpectation_congr_beta _ _ hβeq _ _ _ _
  rw [← htarget]
  have hbase : L + 1 - (site.1.val + 1) + 1 = L - site.1.val + 1 := by omega
  have hexp : -(c * βf) = -(c / (2 * Real.pi) ^ 2) / β := by
    rw [hβfdef]
    field_simp
  rw [hbase, hexp] at hbound
  exact hbound

/--
**KP Theorem 6.2 implies KP Theorem 1.3**, conditional on the carrier bridge
proposition.

`villainWiredBridgeStatement_proved` supplies it in this module.

The conclusion is
the statement of the statement `villain_powerLaw_lower_bound`, copied verbatim.
-/
theorem t13_of_t62 (hT62 : t62Statement) (hbridge : villainWiredBridgeStatement) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) := by
  obtain ⟨β₀, C, hβ₀, hC, hline⟩ := villainCos_line_bound_of_t62 hT62
  refine ⟨β₀, C, hβ₀, hC, fun L hL β hβ hββ j => ?_⟩
  cases j with
  | none =>
    rw [integral_cos_none_villainLaw, SimpleGraph.dist_self]
    simp
  | some x =>
    obtain ⟨hdist, hint⟩ := hbridge L hL β hβ x
    rw [hint, hdist]
    have hside : ∀ site : Lattice2D.SquareFreeVertex L, wiredRightSide L site →
        ((wiredBoundaryDepth L site + 2 : ℝ) ^ (-C / β) ≤
          Villain.villainCosExpectation (Duality.wiredBoxGraph L) none β
            ⟨some site, Option.some_ne_none _⟩) := by
      intro site hs
      have h := hline L hL β hββ site
      have hn : L - site.1.val + 1 = wiredBoundaryDepth L site + 2 := by
        unfold wiredRightSide at hs
        omega
      rw [hn] at h
      push_cast at h
      exact h
    have hall := Duality.wiredBox_allFree_villainCosExpectation_bound_of_rightSide L β C hβ hside x
    have hcast : ((wiredBoundaryDepth L x + 1 : ℕ) : ℝ) + 1 = (wiredBoundaryDepth L x : ℝ) + 2 := by
      push_cast
      ring
    rw [hcast]
    exact hall

/--
**KP Theorem 1.6 implies KP Theorem 1.3**, conditional on the independent inputs: the
reflected-energy inequality and KP Claim 6.4 , and the -carrier bridge
.

The `t13_of_t16Statement_with_wiredBridge` corollary supplies the proved bridge
automatically.

The conclusion is the statement of the `villain_powerLaw_lower_bound`.
-/
theorem t13_of_t16Statement (h : t16Statement) (hrefl : c63ReflectedEnergyStatement) (D₅ : ℝ)
    (hD₅ : 0 ≤ D₅) (hc64 : c64Statement D₅) (hbridge : villainWiredBridgeStatement) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) :=
  t13_of_t62 (t62Statement_of_t16Statement h hrefl D₅ hD₅ hc64) hbridge

/--
**T1.6 ⇒ T1.3 with the wired bridge discharged.** The only remaining inputs are the
independent reflected-energy and KP Claim 6.4 interfaces used to derive T6.2; the reflected-energy estimate supplies the
carrier and law identification internally.
-/
theorem t13_of_t16Statement_with_wiredBridge (h : t16Statement)
    (hrefl : c63ReflectedEnergyStatement) (D₅ : ℝ) (hD₅ : 0 ≤ D₅)
    (hc64 : c64Statement D₅) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) :=
  t13_of_t16Statement h hrefl D₅ hD₅ hc64 villainWiredBridgeStatement_proved

/--
**KP Theorem 1.6 implies the KP Theorem 1.3.** The reflected-energy
input and Claim 6.4 are discharged by the internal free-square proofs from
; the wired-carrier bridge is proved above.

The conclusion is copied
verbatim from the `villain_powerLaw_lower_bound` statement.
-/
theorem t13_of_t16Statement_final (h : t16Statement) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) := by
  exact t13_of_t16Statement_with_wiredBridge h
    Lattice2D.c63ReflectedEnergyStatement_proof 656 (by norm_num)
    Lattice2D.c64Statement_656_proof

end FroehlichSpencer.BKT.Reduction

end
