/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import FroehlichSpencer.BKT.Charges.Covers
public import FroehlichSpencer.BKT.Charges.DensityNeighbourhood
public import FroehlichSpencer.BKT.SpinWaves.Defs
public import FroehlichSpencer.BKT.Surface.ChargeEnsemble
public import FroehlichSpencer.BKT.Surface.DensityCenter
public import FroehlichSpencer.BKT.Surface.DensityDomain
public import FroehlichSpencer.BKT.Surface.Laplacian
public import FroehlichSpencer.BKT.Surface.SquareFree
public import FroehlichSpencer.BKT.Surface.SquarePeriodic

/-!
# KP Proposition 2.1, Theorem 2.2 and Proposition 2.4 as exact propositions

The three propositions `p21Statement`,
`t22Statement` and `p24Statement` are the inputs of the conditional assembly
`Reduction.t16_of_t22_p24` (`Reduction/T16Assembly.lean`) of KP Theorem 1.6.

The covers, expansion, and spin-wave propositions are stated here for use in the reductions.

The following conventions specify the carriers and cover selection.

* `α = 7/4` and `M = 2^16` are `chargeCoverExponent` and `chargeCoverScale` (KP (2.1)).
* Squares, minimum covers `𝒮_k(ϱ)`, `A(ϱ)` (2.2) and `𝒮_k^sep(ϱ)` (2.4) are the square-cover
  objects `kpSquare`, `IsMinimumSquareCover`, `chargeCoverCost` and `separatedSquares`.

`|𝒮_k^sep(ϱ)|` depends on which minimum cover is chosen (KP p. 9).

A `MinimumCoverSelection`
  fixes one minimum cover per density and scale `k ≥ 1`.

P2.1 is stated for every selection,
  since Lemma 4.1 applies to any minimum cover.

P2.4 asserts that
  some selection works (the coherent selector `sharedMinimumSquareCover`).

The assembly uses the P2.4 selection in both.
* `∑_{k ≥ 1} |𝒮_k^sep(ϱ)|` is `separatedSquareTotal`, the sum over `1 ≤ k ≤ L`.

All later
  terms vanish (`separatedSquares_eq_empty_of_lt_two_pow`), so this is the full series
  (`hasSum_separatedSquareCount`).
* Diameters and distances in T2.2 use the charge API (`chargeDiameter`, `densityDistance`),
  which is the graph distance of `squareFree L` / `squarePeriodic L`
  (`chargeDiameter_free`, `chargeDiameter_periodic`).

The density sets of P2.4 use the
  canonical multigraph objects `Multigraph.densityDomain` (KP (1.11)),
  `Multigraph.densityDomainPlus` (2.16), `Multigraph.comparableDensities` (2.15) and
  `neutralPart` (2.13).
* An ensemble is indexed as in the T1.6: a `Fin n`-indexed family that keeps duplicate
  ensembles together with their own coefficients .
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

/-! ## Selected minimum covers and the separated-square total -/

/-- A choice of one minimum cover `𝒮_k(ϱ)` of the support of every density `ϱ` at every scale
`k ≥ 1` (KP p. 8: "the precise choice of `𝒮_k(ϱ)` … is described later"). -/
abbrev MinimumCoverSelection (boundary : SquareBoundary) (L : ℕ) : Type :=
  ∀ (ϱ : ChargeDensity L) (k : {k : ℕ // 1 ≤ k}),
    {C : Finset (Finset (Fin L × Fin L)) // IsMinimumSquareCover boundary L k.val ϱ C}

/-- `separatedSquareCount boundary L cover ϱ k = |𝒮_{k+1}^sep(ϱ)|` for the selected cover at
scale `k + 1` (the shift keeps the scale `≥ 1`, where (2.4) defines `𝒮^sep`). -/
def separatedSquareCount (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ϱ : ChargeDensity L) (k : ℕ) : ℕ :=
  (separatedSquares boundary L ϱ ⟨k + 1, Nat.le_add_left 1 k⟩
    (cover ϱ ⟨k + 1, Nat.le_add_left 1 k⟩)).card

/-- `∑_{k=1}^{∞} |𝒮_k^sep(ϱ)|` (KP (2.5), (2.10), (2.17)), written as the finite sum over
`1 ≤ k ≤ L`; `hasSum_separatedSquareCount` identifies it with the full series. -/
def separatedSquareTotal (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ϱ : ChargeDensity L) : ℕ :=
  ∑ k ∈ Finset.range L, separatedSquareCount boundary L cover ϱ k

/-- Above side `L` every square is the whole domain, so a minimum cover has at most one square
and no separated squares (KP p. 9, after (2.5)). -/
theorem separatedSquares_eq_empty_of_lt_two_pow (boundary : SquareBoundary) (L : ℕ)
    (ϱ : ChargeDensity L) (k : {k : ℕ // 1 ≤ k})
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ϱ C})
    (hk : L < 2 ^ k.val) : separatedSquares boundary L ϱ k C = ∅ := by
  classical
  have hsquares : kpSquares boundary L k.val ⊆ {Finset.univ} := by
    intro s hs
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Finset.mem_singleton]
    cases boundary with
    | free => simp [kpSquare, squareSide, hk]
    | periodic => simp [kpSquare, squareSide, hk.le]
  have hcard : C.val.card ≤ 1 :=
    (Finset.card_le_card (C.property.1.1.trans hsquares)).trans
      (Finset.card_singleton _).le
  unfold separatedSquares
  exact Finset.filter_false_of_mem fun s _ hs => absurd hs.1 (by omega)

/-- `|𝒮_{k+1}^sep(ϱ)| = 0` for `k ≥ L` (the scale `k + 1` exceeds `L`). -/
theorem separatedSquareCount_eq_zero (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ϱ : ChargeDensity L) {k : ℕ} (hk : L ≤ k) :
    separatedSquareCount boundary L cover ϱ k = 0 := by
  have hlt : L < 2 ^ (k + 1) :=
    lt_of_le_of_lt hk ((Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num)
      (Nat.lt_succ_self k)))
  rw [separatedSquareCount, separatedSquares_eq_empty_of_lt_two_pow boundary L ϱ _ _ hlt,
    Finset.card_empty]

/-- `separatedSquareTotal` is the full series `∑_{k=1}^{∞} |𝒮_k^sep(ϱ)|`. -/
theorem hasSum_separatedSquareCount (boundary : SquareBoundary) (L : ℕ)
    (cover : MinimumCoverSelection boundary L) (ϱ : ChargeDensity L) :
    HasSum (fun k => (separatedSquareCount boundary L cover ϱ k : ℝ))
      (separatedSquareTotal boundary L cover ϱ : ℝ) := by
  rw [separatedSquareTotal, Nat.cast_sum]
  refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
  rw [separatedSquareCount_eq_zero boundary L cover ϱ (not_lt.mp (Finset.mem_range.not.mp hk)),
    Nat.cast_zero]

/-!
## The charge-API diameter is the graph diameter
-/

/--
`chargeDiameter` is the `Multigraph.densityDiameter` of any multigraph whose graph
distance is the lattice distance of the boundary condition.
-/
theorem chargeDiameter_eq_densityDiameter (boundary : SquareBoundary) {L : ℕ} {E : Type}
    (Λ : Multigraph (Fin L × Fin L) E)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (ϱ : ChargeDensity L) : chargeDiameter boundary L ϱ = Λ.densityDiameter ϱ := by
  classical
  unfold chargeDiameter squareDiameter Multigraph.densityDiameter
  split_ifs with h
  · apply le_antisymm
    · refine Finset.max'_le _ _ _ fun d hd => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
      rw [hdist]
      exact Finset.le_sup (f := fun p : (Fin L × Fin L) × (Fin L × Fin L) =>
        Λ.toSimpleGraph.dist p.1 p.2) hp
    · refine Finset.sup_le fun p hp => ?_
      rw [← hdist]
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem
        (fun p : (Fin L × Fin L) × (Fin L × Fin L) => latticeDistance boundary L p.1 p.2) hp)
  · have hempty : ((Finset.univ.filter fun j : Fin L × Fin L => ϱ j ≠ 0) ×ˢ
        (Finset.univ.filter fun j : Fin L × Fin L => ϱ j ≠ 0)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty, Finset.sup_empty]
    rfl

/--
On the free square, `chargeDiameter` is the diameter of `squareFree L`.
-/
theorem chargeDiameter_free (L : ℕ) (ϱ : ChargeDensity L) :
    chargeDiameter .free L ϱ = (squareFree L).densityDiameter ϱ :=
  chargeDiameter_eq_densityDiameter .free (squareFree L) (fun _ _ => rfl) ϱ

/--
On the periodic square, `chargeDiameter` is the diameter of `squarePeriodic L`.
-/
theorem chargeDiameter_periodic (L : ℕ) (ϱ : ChargeDensity L) :
    chargeDiameter .periodic L ϱ = (squarePeriodic L).densityDiameter ϱ :=
  chargeDiameter_eq_densityDiameter .periodic (squarePeriodic L) (fun _ _ => rfl) ϱ

/-! ## Properties (a)–(c) of KP Theorem 2.2 -/

/-- KP Theorem 2.2(a): there is at most one non-neutral density in `𝒩`. -/
def AtMostOneNonNeutral {V : Type*} [Fintype V] (N : Finset (V → ℤ)) : Prop :=
  ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ∑ j, ϱ₁ j ≠ 0 → ∑ j, ϱ₂ j ≠ 0 → ϱ₁ = ϱ₂

/-- KP Theorem 2.2(b): distinct `ϱ₁, ϱ₂ ∈ 𝒩` satisfy
`dist(ϱ₁, ϱ₂) ≥ M [min(d(ϱ₁), d(ϱ₂))]^α`; if `𝒩` contains a non-neutral `ϱ_c`, then
`dist(ϱ, ϱ_c) ≥ M [d(ϱ)]^α` for every other `ϱ ∈ 𝒩`. -/
def IsScaleSeparated (boundary : SquareBoundary) (L : ℕ) (N : Finset (ChargeDensity L)) :
    Prop :=
  (∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ →
    (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) : ℕ) : ℝ) ^
          chargeCoverExponent ≤
      densityDistance boundary L ϱ₁ ϱ₂) ∧
  ∀ ϱc ∈ N, ∑ j, ϱc j ≠ 0 → ∀ ϱ ∈ N, ϱ ≠ ϱc →
    (chargeCoverScale : ℝ) * (chargeDiameter boundary L ϱ : ℝ) ^ chargeCoverExponent ≤
      densityDistance boundary L ϱ ϱc

/-- KP Theorem 2.2(c): for each decomposition `ϱ = ϱ₁ + ϱ₂` of a neutral `ϱ ∈ 𝒩` into
densities (nonzero) with disjoint supports, if `dist(ϱ₁, ϱ₂) ≥ 2M [min(d(ϱ₁), d(ϱ₂))]^α` then
`ϱ₁` and `ϱ₂` are non-neutral. -/
def NeutralSplitsAreCharged (boundary : SquareBoundary) (L : ℕ)
    (N : Finset (ChargeDensity L)) : Prop :=
  ∀ ϱ ∈ N, ∑ j, ϱ j = 0 → ∀ ϱ₁ ϱ₂ : ChargeDensity L, ϱ₁ ≠ 0 → ϱ₂ ≠ 0 →
    Disjoint (Function.support ϱ₁) (Function.support ϱ₂) → ϱ = ϱ₁ + ϱ₂ →
    2 * (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) : ℕ) : ℝ) ^
          chargeCoverExponent ≤
      densityDistance boundary L ϱ₁ ϱ₂ →
    ∑ j, ϱ₁ j ≠ 0 ∧ ∑ j, ϱ₂ j ≠ 0

namespace Reduction

/-! ## The three propositions -/

/-- The body of KP Theorem 2.2 (pp. 9–10, (2.6)–(2.7)) on one square domain, with constant
`D₂`. The site weights `lam j` are real, even, normalized trigonometric polynomials (KP p. 4):
`lam j φ = 1 + 2 ∑_{q=1}^{Nq j} lamHat j q cos (q φ)` with `Nq j > 0` and `lamHat j q = 0` for
`q > Nq j`. There are a finite `Fin n`-indexed family of ensembles `N i`, positive `c i` summing
to `1` and reals `K i ϱ` such that (2.6) holds for every `ψ`, and each `N i` satisfies (a), (b),
(c) and (d) (2.7): `|K i ϱ| ≤ e^{D₂ A(ϱ)} ∏_{j ∈ supp ϱ} e^{ϱ(j)²} |lamHat j |ϱ(j)||` for neutral
`ϱ ∈ N i`. -/
def T22Step (boundary : SquareBoundary) (L : ℕ) (D₂ : ℝ) : Prop :=
  ∀ (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ)
    (lamHat : Fin L × Fin L → ℕ → ℝ),
    (∀ j, 0 < Nq j) → (∀ j q, Nq j < q → lamHat j q = 0) →
    (∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ)) →
    ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
      (K : Fin n → (Fin L × Fin L → ℤ) → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
      (∀ ψ : Fin L × Fin L → ℝ,
        ∏ j, lam j (ψ j) = ∑ i, c i * ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, ψ j * ϱ j))) ∧
      ∀ i, AtMostOneNonNeutral (N i) ∧ IsScaleSeparated boundary L (N i) ∧
        NeutralSplitsAreCharged boundary L (N i) ∧
        ∀ ϱ ∈ N i, ∑ j, ϱ j = 0 →
          |K i ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
            ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|

/-- KP Theorem 2.2 (pp. 9–10): there is a positive absolute constant `D₂` such that, on every
square domain (free; periodic with `L` even; `L > 1`), every family of real, even, normalized
trigonometric polynomials has the convex expansion (2.6) into ensembles with properties
(a)–(d). Fixed internal choice `α = 7/4`, `M = 2^16` (Theorem 2.2). -/
def t22Statement : Prop :=
  ∃ D₂ : ℝ, 0 < D₂ ∧ ∀ L : ℕ, 1 < L →
    T22Step .free L D₂ ∧ (Even L → T22Step .periodic L D₂)

/-- The body of KP Proposition 2.1 (p. 9, (2.5)) on one square domain, with constant `D₁`, for
a given selection of minimum covers: for every density `ϱ`,
`log₂(d(ϱ) + 1) ≤ A(ϱ) ≤ D₁ (|𝒮₀(ϱ)| + ∑_{k ≥ 1} |𝒮_k^sep(ϱ)|)`. -/
def P21Step (boundary : SquareBoundary) (L : ℕ) (D₁ : ℝ) : Prop :=
  ∀ (cover : MinimumCoverSelection boundary L) (ϱ : Fin L × Fin L → ℤ), ϱ ≠ 0 →
    Real.logb 2 (chargeDiameter boundary L ϱ + 1) ≤ chargeCoverCost boundary L ϱ ∧
      (chargeCoverCost boundary L ϱ : ℝ) ≤
        D₁ * (squareCoverNumber boundary L 0 ϱ + separatedSquareTotal boundary L cover ϱ)

/-- KP Proposition 2.1 (p. 9): there is a positive absolute constant `D₁` such that (2.5) holds
on every square domain, for every density and every selection of minimum covers (the source's
selection is one of them; , P2.1 and  -/
def p21Statement : Prop :=
  ∃ D₁ : ℝ, 0 < D₁ ∧ ∀ L : ℕ, 1 < L →
    P21Step .free L D₁ ∧ (Even L → P21Step .periodic L D₁)

/-- The body of KP Proposition 2.4 (pp. 11–12) on one square domain `Λ`, with constant `D₃`.
For every admissible center choice (KP p. 5) there is a selection of minimum covers (
such that for every `β > 0`, every ensemble `𝒩` with properties (a)–(c) of Theorem 2.2, and
every `ϱ ∈ 𝒩₀` (the neutral part, (2.13)), one function `a = a_{ϱ,𝒩₀}` satisfies:
(1) `a` is constant on `D⁺(ϱ')` for every `ϱ' ∈ 𝒩₀(ϱ)` (2.15)–(2.16); (2) `supp a ⊆ D(ϱ)`;
(3) `supp (Δ a) ⊆ D(ϱ)`; (4) (2.17)
`E_β(a, ϱ) ≥ β⁻¹ (‖ϱ‖₂² / 16 + D₃ ∑_{k ≥ 1} |𝒮_k^sep(ϱ)|)`. -/
def P24Step (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (D₃ : ℝ) : Prop :=
  ∀ centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L,
    (∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ)) →
    ∃ cover : MinimumCoverSelection boundary L,
      ∀ β : ℝ, 0 < β → ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N →
        AtMostOneNonNeutral N → IsScaleSeparated boundary L N →
        NeutralSplitsAreCharged boundary L N →
        ∀ ϱ ∈ neutralPart N, ∃ a : Fin L × Fin L → ℝ,
          (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) ϱ,
            ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), a j = c) ∧
          Function.support a ⊆ Λ.densityDomain ϱ (centerOf ϱ) ∧
          Function.support (Λ.laplacian a) ⊆ Λ.densityDomain ϱ (centerOf ϱ) ∧
          1 / β * (1 / 16 * ∑ j, (ϱ j : ℝ) ^ 2 +
              D₃ * separatedSquareTotal boundary L cover ϱ) ≤
            SpinWaves.energyFunctional Λ β a ϱ

/-- KP Proposition 2.4 (Spin Wave Existence, pp. 11–12): there is a positive absolute constant
`D₃` (independent of the ensemble) such that `P24Step` holds on every square domain (free;
periodic with `L` even; `L > 1`). The witness `a` is chosen before any shift `σ` appears, so it
is independent of `σ`. Fixed internal choice `α = 7/4`, `M = 2^16` (Proposition 2.4). -/
def p24Statement : Prop :=
  ∃ D₃ : ℝ, 0 < D₃ ∧ ∀ L : ℕ, 1 < L →
    P24Step .free (squareFree L) D₃ ∧ (Even L → P24Step .periodic (squarePeriodic L) D₃)

end Reduction

end FroehlichSpencer.BKT

end
