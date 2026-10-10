/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Reduction.T16AssemblyStatements
public import FroehlichSpencer.BKT.SpinWaves.Components

/-!
# KP Lemma 4.6 and Proposition 4.7 as exact propositions

Both are stated in the §4.3 context of
`Reduction.P24Step`: a square domain `Λ` (free; periodic with `L` even; `L > 1`), an admissible
center choice, an ensemble `𝒩` with properties (a)–(c) of Theorem 2.2, its neutral part
`𝒩₀ = neutralPart 𝒩` and `ϱ* ∈ 𝒩₀`.

`𝒩₀(ϱ*)` is `Multigraph.comparableDensities` (2.15), and the
components are those of the graph induced on `⋃_{ϱ' ∈ 𝒩₀(ϱ*)} D⁺(ϱ')` (`DensityPlusComponent`).

`M = 2^16` and `α = 7/4` are `chargeCoverScale` and `chargeCoverExponent`.

* `l46Statement` (KP Lemma 4.6): component separation, separation from `ϱ*`, and the boundary
  bound `|∂^ext E| ≤ 64 d(E)`, jointly for every component.

The plateau radius
  `⌈2^{k-3}⌉` is written literally as `⌈(2 : ℝ) ^ ((k : ℤ) - 3)⌉₊`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SpinWaves

open Reduction

/-- The body of KP Lemma 4.6 (p. 24) on one square domain `Λ`: for every admissible center
choice, every ensemble `𝒩` with properties (a)–(c) of Theorem 2.2 and every `ϱ* ∈ 𝒩₀`, every
connected component `E` of `⋃_{ϱ' ∈ 𝒩₀(ϱ*)} D⁺(ϱ')` satisfies
(1) `(M/25) [min(d(E), d(E'))]^α ≤ dist(E, E') + d(E) + d(E')` for every other component `E'`;
(2) `(M/128) d(E)^α ≤ dist(E, ϱ*)`; (3) `|∂^ext E| ≤ 64 d(E)`. -/
def L46Step (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) : Prop :=
  ∀ centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L,
    (∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ)) →
    ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N →
      AtMostOneNonNeutral N → IsScaleSeparated boundary L N →
      NeutralSplitsAreCharged boundary L N →
      ∀ ϱstar ∈ neutralPart N,
      ∀ c : DensityPlusComponent Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf,
        (∀ c' : DensityPlusComponent Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf,
            c ≠ c' →
            (chargeCoverScale : ℝ) / 25 *
                ((min (densityPlusComponentDiameter Λ
                    (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c)
                  (densityPlusComponentDiameter Λ
                    (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c') : ℕ) : ℝ) ^
                  chargeCoverExponent ≤
              ((densityPlusComponentDistance Λ
                  (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c c' +
                densityPlusComponentDiameter Λ
                  (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c +
                densityPlusComponentDiameter Λ
                  (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c' : ℕ) : ℝ)) ∧
        (chargeCoverScale : ℝ) / 128 *
            (densityPlusComponentDiameter Λ
              (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c : ℝ) ^
              chargeCoverExponent ≤
          (densityPlusComponentRootDistance Λ
            (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c ϱstar : ℝ) ∧
        (densityPlusExternalBoundary Λ
            (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c).card ≤
          64 * densityPlusComponentDiameter Λ
            (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c

/-- KP Lemma 4.6 (p. 24) on every square domain (free; periodic with `L` even; `L > 1`). -/
def l46Statement : Prop :=
  ∀ L : ℕ, 1 < L →
    L46Step .free (squareFree L) ∧ (Even L → L46Step .periodic (squarePeriodic L))

/-- Clauses (1) and (2) of KP Lemma 4.6 on one domain. -/
def L46SeparationStep (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) : Prop :=
  ∀ centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L,
    (∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ)) →
    ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N →
      AtMostOneNonNeutral N → IsScaleSeparated boundary L N →
      NeutralSplitsAreCharged boundary L N →
      ∀ ϱstar ∈ neutralPart N,
      ∀ c : DensityPlusComponent Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf,
        (∀ c' : DensityPlusComponent Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf,
            c ≠ c' →
            (chargeCoverScale : ℝ) / 25 *
                ((min (densityPlusComponentDiameter Λ
                    (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c)
                  (densityPlusComponentDiameter Λ
                    (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c') : ℕ) : ℝ) ^
                  chargeCoverExponent ≤
              ((densityPlusComponentDistance Λ
                  (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c c' +
                densityPlusComponentDiameter Λ
                  (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c +
                densityPlusComponentDiameter Λ
                  (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c' : ℕ) : ℝ)) ∧
        (chargeCoverScale : ℝ) / 128 *
            (densityPlusComponentDiameter Λ
              (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c : ℝ) ^
              chargeCoverExponent ≤
          (densityPlusComponentRootDistance Λ
            (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c ϱstar : ℝ)

/-- Clause (3) of KP Lemma 4.6 on one domain: `|∂^ext E| ≤ 64 d(E)`. -/
def L46BoundaryStep (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) : Prop :=
  ∀ centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L,
    (∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ)) →
    ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N →
      AtMostOneNonNeutral N → IsScaleSeparated boundary L N →
      NeutralSplitsAreCharged boundary L N →
      ∀ ϱstar ∈ neutralPart N,
      ∀ c : DensityPlusComponent Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf,
        (densityPlusExternalBoundary Λ
            (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c).card ≤
          64 * densityPlusComponentDiameter Λ
            (Λ.comparableDensities (neutralPart N) ϱstar) centerOf c

/-- Clauses (1)–(2) of KP Lemma 4.6 on every square domain. -/
def l46SeparationStatement : Prop :=
  ∀ L : ℕ, 1 < L →
    L46SeparationStep .free (squareFree L) ∧
      (Even L → L46SeparationStep .periodic (squarePeriodic L))

/-- Clause (3) of KP Lemma 4.6 on every square domain. -/
def l46BoundaryStatement : Prop :=
  ∀ L : ℕ, 1 < L →
    L46BoundaryStep .free (squareFree L) ∧
      (Even L → L46BoundaryStep .periodic (squarePeriodic L))

theorem L46Step_iff (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) :
    L46Step boundary Λ ↔ L46SeparationStep boundary Λ ∧ L46BoundaryStep boundary Λ := by
  constructor
  · intro h
    exact ⟨fun cf hcf N h1 h2 h3 h4 ϱ hϱ c => ⟨(h cf hcf N h1 h2 h3 h4 ϱ hϱ c).1,
        (h cf hcf N h1 h2 h3 h4 ϱ hϱ c).2.1⟩,
      fun cf hcf N h1 h2 h3 h4 ϱ hϱ c => (h cf hcf N h1 h2 h3 h4 ϱ hϱ c).2.2⟩
  · rintro ⟨h, h'⟩ cf hcf N h1 h2 h3 h4 ϱ hϱ c
    exact ⟨(h cf hcf N h1 h2 h3 h4 ϱ hϱ c).1, (h cf hcf N h1 h2 h3 h4 ϱ hϱ c).2,
      h' cf hcf N h1 h2 h3 h4 ϱ hϱ c⟩

/-- KP Lemma 4.6 is the conjunction of its separation clauses and its boundary clause. -/
theorem l46Statement_iff :
    l46Statement ↔ l46SeparationStatement ∧ l46BoundaryStatement := by
  constructor
  · intro h
    refine ⟨fun L hL => ?_, fun L hL => ?_⟩
    · exact ⟨((L46Step_iff _ _).1 (h L hL).1).1,
        fun he => ((L46Step_iff _ _).1 ((h L hL).2 he)).1⟩
    · exact ⟨((L46Step_iff _ _).1 (h L hL).1).2,
        fun he => ((L46Step_iff _ _).1 ((h L hL).2 he)).2⟩
  · rintro ⟨h, h'⟩ L hL
    exact ⟨(L46Step_iff _ _).2 ⟨(h L hL).1, (h' L hL).1⟩,
      fun he => (L46Step_iff _ _).2 ⟨(h L hL).2 he, (h' L hL).2 he⟩⟩

/-- The body of KP Proposition 4.7 (p. 25) on one square domain `Λ`, with constant `D₃`. In the
§4.3 context, for every `β > 0`, every scale `k ≥ 1`, every minimum cover `C` at scale `k` and
every separated square `s ∈ 𝒮_k^sep(ϱ*)` of `C`, one function `a = a_{s,ϱ*}` satisfies:
(1) `supp a ⊆ {j : dist(j, s) ≤ 2^{k-1}}`; (2) `a` is constant on
`{j : dist(j, s) ≤ ⌈2^{k-3}⌉}`; (3) `a` is constant on `D⁺(ϱ')` for every `ϱ' ∈ 𝒩₀(ϱ*)`;
(4) `E_β(a, ϱ*) ≥ D₃ / β`. The distance from `j` to the square `s` is the minimum graph distance,
written as "some `y ∈ s` with `dist(j, y) ≤ R`". -/
def P47Step (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (D₃ : ℝ) : Prop :=
  ∀ centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L,
    (∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ)) →
    ∀ β : ℝ, 0 < β → ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N →
      AtMostOneNonNeutral N → IsScaleSeparated boundary L N →
      NeutralSplitsAreCharged boundary L N →
      ∀ ϱstar ∈ neutralPart N, ∀ k : {k : ℕ // 1 ≤ k},
      ∀ C : {C : Finset (Finset (Fin L × Fin L)) //
        IsMinimumSquareCover boundary L k.val ϱstar C},
      ∀ s ∈ separatedSquares boundary L ϱstar k C,
      ∃ a : Fin L × Fin L → ℝ,
        (∀ j, a j ≠ 0 → ∃ y ∈ s, Λ.toSimpleGraph.dist j y ≤ 2 ^ (k.val - 1)) ∧
        (∃ c : ℝ, ∀ j, (∃ y ∈ s, Λ.toSimpleGraph.dist j y ≤ ⌈(2 : ℝ) ^ ((k.val : ℤ) - 3)⌉₊) →
          a j = c) ∧
        (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) ϱstar,
          ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), a j = c) ∧
        D₃ / β ≤ energyFunctional Λ β a ϱstar

/-- KP Proposition 4.7 (p. 25): there is a positive absolute constant `D₃` such that `P47Step`
holds on every square domain (free; periodic with `L` even; `L > 1`). Fixed internal choice
`α = 7/4`, `M = 2^16`. -/
def p47Statement : Prop :=
  ∃ D₃ : ℝ, 0 < D₃ ∧ ∀ L : ℕ, 1 < L →
    P47Step .free (squareFree L) D₃ ∧ (Even L → P47Step .periodic (squarePeriodic L) D₃)

/-- `⌈2^{k-3}⌉ = 2^{k-3}` in `ℕ` (truncated subtraction): both are `1` for `k ≤ 3`. -/
theorem ceil_two_zpow_sub_three (k : ℕ) :
    ⌈(2 : ℝ) ^ ((k : ℤ) - 3)⌉₊ = 2 ^ (k - 3) := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · have hpos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℤ) - 3) := zpow_pos (by norm_num) _
    have hle : (2 : ℝ) ^ ((k : ℤ) - 3) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    rw [show k - 3 = 0 by omega, pow_zero]
    apply le_antisymm
    · exact Nat.ceil_le.mpr (by simpa using hle)
    · exact Nat.lt_ceil.mpr (by simpa using hpos)
  · have hz : ((k : ℤ) - 3) = ((k - 3 : ℕ) : ℤ) := by omega
    rw [hz, zpow_natCast]
    exact_mod_cast Nat.ceil_natCast (2 ^ (k - 3))

end FroehlichSpencer.BKT.SpinWaves

end
