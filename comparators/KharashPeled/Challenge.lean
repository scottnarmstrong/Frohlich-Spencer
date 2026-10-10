/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib

-- Reset the auxiliary-lemma cache between copied source modules.
-- This preserves generated proof names without changing definitions or assumptions.
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
structure Multigraph (V : Type u) (E : Type v) where
  src : E → V
  tgt : E → V
  src_ne_tgt : ∀ e, src e ≠ tgt e
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
def Multigraph.toSimpleGraph {V : Type u} {E : Type v} (G : Multigraph V E) : SimpleGraph V :=
  SimpleGraph.fromRel fun j ℓ => ∃ e, (G.src e = j ∧ G.tgt e = ℓ) ∨ (G.src e = ℓ ∧ G.tgt e = j)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
noncomputable def integerGFFLaw {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (_hG : G.toSimpleGraph.Connected) (β : ℝ)
    (_hβ : 0 < β) (v : V) : Measure (V → ℤ) :=
  let μ : Measure (V → ℤ) :=
    (Measure.pi fun j => if j = v then Measure.dirac 0 else Measure.count).withDensity
      fun m => ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, ((m (G.src e) : ℝ) - m (G.tgt e)) ^ 2))
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
def Multigraph.laplacian {V : Type u} {E : Type v} (G : Multigraph V E) [Fintype E]
    [DecidableEq V] {R : Type*} [AddCommGroup R] (f : V → R) (j : V) : R :=
  ∑ e, ((if G.src e = j then f (G.tgt e) - f j else 0) +
    (if G.tgt e = j then f (G.src e) - f j else 0))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
def Multigraph.IsLaplacianPseudoinverse {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) : Prop :=
  (∀ f : V → ℝ, ∑ j, f j = 0 → G.laplacian (T f) = f ∧ T (G.laplacian f) = f) ∧
    ∀ c : ℝ, T (fun _ => c) = 0
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
abbrev SquareFreeEdge (L : ℕ) : Type :=
  {p : (Fin L × Fin L) × (Fin L × Fin L) //
    toLex p.1 < toLex p.2 ∧
      ({|((p.1.1 : ℕ) : ℤ) - (p.2.1 : ℕ)|, |((p.1.2 : ℕ) : ℤ) - (p.2.2 : ℕ)|} : Finset ℤ) = {0, 1}}
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def squareFree (L : ℕ) : Multigraph (Fin L × Fin L) (SquareFreeEdge L) where
  src e := e.1.1
  tgt e := e.1.2
  src_ne_tgt e h := lt_irrefl (toLex e.1.2) (h ▸ e.2.1)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
theorem squareFree_connected (L : ℕ) (hL : 1 < L) : (squareFree L).toSimpleGraph.Connected := by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
abbrev SquarePeriodicEdge (L : ℕ) : Type :=
  {p : (Fin L × Fin L) × (Fin L × Fin L) //
    toLex p.1 < toLex p.2 ∧
      ((p.1.1 = p.2.1 ∧ (((p.1.2 : ℕ) : ℤ) ≡ (p.2.2 : ℕ) + 1 [ZMOD L] ∨
          ((p.2.2 : ℕ) : ℤ) ≡ (p.1.2 : ℕ) + 1 [ZMOD L])) ∨
        (p.1.2 = p.2.2 ∧ (((p.1.1 : ℕ) : ℤ) ≡ (p.2.1 : ℕ) + 1 [ZMOD L] ∨
          ((p.2.1 : ℕ) : ℤ) ≡ (p.1.1 : ℕ) + 1 [ZMOD L])))}
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def squarePeriodic (L : ℕ) : Multigraph (Fin L × Fin L) (SquarePeriodicEdge L) where
  src e := e.1.1
  tgt e := e.1.2
  src_ne_tgt e h := lt_irrefl (toLex e.1.2) (h ▸ e.2.1)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
theorem squarePeriodic_connected (L : ℕ) (hL : 1 < L) :
    (squarePeriodic L).toSimpleGraph.Connected := by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def squareZero (L : ℕ) : Multigraph (Option (Fin L × Fin L))
    (SquareFreeEdge L ⊕ Σ j : Fin L × Fin L,
      Fin (4 - (Finset.univ.filter fun e : SquareFreeEdge L =>
        (squareFree L).src e = j ∨ (squareFree L).tgt e = j).card)) where
  src := Sum.elim (fun e => some ((squareFree L).src e)) (fun b => some b.1)
  tgt := Sum.elim (fun e => some ((squareFree L).tgt e)) (fun _ => none)
  src_ne_tgt
    | .inl e => Option.some_injective _ |>.ne ((squareFree L).src_ne_tgt e)
    | .inr _ => Option.some_ne_none _
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def villainLaw (L : ℕ) (β : ℝ) (_hβ : 0 < β) :
    Measure (Option (Fin L × Fin L) → ℝ) :=
  let μ : Measure (Option (Fin L × Fin L) → ℝ) :=
    (Measure.pi fun j =>
        if j = none then Measure.dirac 0
        else volume.restrict (Set.Ico (-Real.pi) Real.pi)).withDensity
      fun θ => ∏ e, ∑' m : ℤ,
        ENNReal.ofReal (Real.exp (-(β / 2) *
          (θ ((squareZero L).src e) - θ ((squareZero L).tgt e) + 2 * Real.pi * m) ^ 2))
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
noncomputable def gffLaw {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (_hG : G.toSimpleGraph.Connected) (β : ℝ) (_hβ : 0 < β) (v : V) :
    Measure (V → ℝ) :=
  let μ : Measure (V → ℝ) :=
    (Measure.pi fun _ : V => (volume : Measure ℝ)).withDensity fun φ =>
      ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2) *
        (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v))
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def IsSubGaussian (Γ η θ β : ℝ) (lam : ℝ → ℝ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ lamHat : ℕ → ℝ, (∀ q : ℕ, N < q → lamHat q = 0) ∧
    (∀ φ : ℝ, lam φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 N, lamHat q * Real.cos (q * φ)) ∧
    ∀ q : ℕ, 1 ≤ q → |lamHat q| ≤ Γ * Real.exp ((η + θ / β) * q ^ 2)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u
noncomputable def _root_.FroehlichSpencer.BKT.IsChargeEnsemble : {V : Type u} → (N : Finset.{u} (V → Int)) → Prop :=
fun {V : Type u} (N : Finset.{u} (V → Int)) =>
  And
    (∀ (ϱ : V → Int),
      @Membership.mem.{u, u} (V → Int) (Finset.{u} (V → Int))
          (@SetLike.instMembership.{u, u} (Finset.{u} (V → Int)) (V → Int) (@Finset.instSetLike.{u} (V → Int))) N ϱ →
        @Ne.{u + 1} (V → Int) ϱ
          (@OfNat.ofNat.{u} (V → Int) (nat_lit 0)
            (@Zero.toOfNat0.{u} (V → Int)
              (@Pi.instZero.{u, 0} V (fun (a : V) => Int) fun (i : V) =>
                @Zero.ofOfNat0.{0} Int (@instOfNat (nat_lit 0))))))
    (∀ (ϱ₁ : V → Int),
      @Membership.mem.{u, u} (V → Int) (Finset.{u} (V → Int))
          (@SetLike.instMembership.{u, u} (Finset.{u} (V → Int)) (V → Int) (@Finset.instSetLike.{u} (V → Int))) N ϱ₁ →
        ∀ (ϱ₂ : V → Int),
          @Membership.mem.{u, u} (V → Int) (Finset.{u} (V → Int))
              (@SetLike.instMembership.{u, u} (Finset.{u} (V → Int)) (V → Int) (@Finset.instSetLike.{u} (V → Int))) N
              ϱ₂ →
            @Ne.{u + 1} (V → Int) ϱ₁ ϱ₂ →
              @Disjoint.{u} (Set.{u} V)
                (@SemilatticeInf.toPartialOrder.{u} (Set.{u} V)
                  (@Lattice.toSemilatticeInf.{u} (Set.{u} V)
                    (@GeneralizedCoheytingAlgebra.toLattice.{u} (Set.{u} V)
                      (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u} (Set.{u} V)
                        (@BiheytingAlgebra.toCoheytingAlgebra.{u} (Set.{u} V)
                          (@BooleanAlgebra.toBiheytingAlgebra.{u} (Set.{u} V) (@Set.instBooleanAlgebra.{u} V)))))))
                (@HeytingAlgebra.toOrderBot.{u} (Set.{u} V)
                  (@BiheytingAlgebra.toHeytingAlgebra.{u} (Set.{u} V)
                    (@BooleanAlgebra.toBiheytingAlgebra.{u} (Set.{u} V) (@Set.instBooleanAlgebra.{u} V))))
                (@Function.support.{u, 0} V Int (@Zero.ofOfNat0.{0} Int (@instOfNat (nat_lit 0))) ϱ₁)
                (@Function.support.{u, 0} V Int (@Zero.ofOfNat0.{0} Int (@instOfNat (nat_lit 0))) ϱ₂))

end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
noncomputable def Multigraph.densityDiameter {V : Type u} {E : Type v} [Fintype V] (G : Multigraph V E)
    (ϱ : V → ℤ) : ℕ :=
  ((Finset.univ.filter fun j => ϱ j ≠ 0) ×ˢ (Finset.univ.filter fun j => ϱ j ≠ 0)).sup
    fun p => G.toSimpleGraph.dist p.1 p.2
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
def Multigraph.IsDensityCenter {V : Type u} {E : Type v} [Fintype V] (G : Multigraph V E)
    (ϱ : V → ℤ) (j : V) : Prop :=
  ϱ j ≠ 0 ∧ ∃ k : V, ϱ k ≠ 0 ∧ G.densityDiameter ϱ = G.toSimpleGraph.dist j k
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
def Multigraph.densityDomain {V : Type u} {E : Type v} [Fintype V] (G : Multigraph V E)
    (ϱ : V → ℤ) (j : V) : Set V :=
  {ℓ | G.toSimpleGraph.dist ℓ j < 2 * G.densityDiameter ϱ}
end FroehlichSpencer.BKT
end


run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.integerGFF_delocalization :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let bounds : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          (∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ, Λ.IsLaplacianPseudoinverse T →
            ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
              ENNReal.ofReal (Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β))) ≤
                  ∫⁻ m, ENNReal.ofReal (Real.exp (∑ j, (m j : ℝ) * f j))
                    ∂(integerGFFLaw Λ hΛ β hβ v) ∧
                ENNReal.ofReal ((∑ j, f j * -(T f j)) / ((1 + ε) * β)) ≤
                  ∫⁻ m, ENNReal.ofReal ((∑ j, (m j : ℝ) * f j) ^ 2)
                    ∂(integerGFFLaw Λ hΛ β hβ v)) ∧
          ∀ j k : Fin L × Fin L,
            ENNReal.ofReal (c / β * Real.log (Λ.toSimpleGraph.dist j k + 1)) ≤
              ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - m k) ^ 2) ∂(integerGFFLaw Λ hΛ β hβ v)
      bounds (squareFree L) (squareFree_connected L hL) ∧
        (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.villain_powerLaw_lower_bound :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.weightedGFF_expMoment_lower_bound :
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 → ∀ ε : ℝ, 0 < ε →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let bounds : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
            0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) ∧
            ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ, Λ.IsLaplacianPseudoinverse T →
              ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
                Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β)) ≤
                  (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) /
                    ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)
      bounds (squareFree L) (squareFree_connected L hL) ∧
        (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.KharashPeled.weightedGFF_renormalization :
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 →
      ∃ β₀ c₁ : ℝ, 0 < β₀ ∧ 0 < c₁ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let step : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
          ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
            (z : Fin n → (Fin L × Fin L → ℤ) → ℝ)
            (ϱbar : Fin n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
            (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
            (∀ σ : Fin L × Fin L → ℝ,
              ∫ φ, ∏ j, lam j (φ j + σ j) ∂(gffLaw Λ hΛ β hβ v) =
                ∑ i, c i * ∫ φ, ∏ ϱ ∈ N i,
                  (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j))
                    ∂(gffLaw Λ hΛ β hβ v)) ∧
            ∀ i,
              (∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
              (∀ ϱ ∈ N i, |z i ϱ| ≤ Real.exp (-(c₁ / β) *
                (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)))) ∧
              ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
                Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
                Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
                ∀ j₁ j₂ : Fin L × Fin L, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
                  Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅
      step (squareFree L) (squareFree_connected L hL) ∧
        (Even L → step (squarePeriodic L) (squarePeriodic_connected L hL)) :=
  by sorry
end FroehlichSpencer.BKT
end
