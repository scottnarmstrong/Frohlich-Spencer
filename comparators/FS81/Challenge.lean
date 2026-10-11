/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def planeRotatorLaw (β : ℝ) (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  let μ : Measure (Λ → ℝ) :=
    (Measure.pi fun _ : Λ => volume.restrict (Set.Ico (-Real.pi) Real.pi)).withDensity
      fun θ => ∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ENNReal.ofReal (Real.exp (β * Real.cos (θ b.1 - θ b.2)))
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
@[expose] public section
namespace FroehlichSpencer.BKT
theorem existsUnique_tendsto_planeRotatorTwoPoint (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) :
    ∃! c : ℝ, Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂planeRotatorLaw β Λ.1) atTop (𝓝 c) := by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
@[expose] noncomputable def planeRotatorCorrelation (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) : ℝ :=
  Classical.choose (existsUnique_tendsto_planeRotatorTwoPoint β hβ ξ j ℓ).exists
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def IsConditionLambda (C α ε β : ℝ) (lam : ℤ → ℝ) : Prop :=
  ε < 1 / 16 ∧ ∀ q : ℤ, lam q = lam (-q) ∧ |lam q| ≤ C * Real.exp ((α + ε * β) * (q : ℝ) ^ 2)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def coulombPotential (x : ℤ × ℤ) : ℝ :=
  -(((2 * Real.pi) ^ 2)⁻¹ *
    ∫ k in Set.Ico 0 (2 * Real.pi) ×ˢ Set.Ico 0 (2 * Real.pi),
      (1 - Real.cos (k.1 * x.1 + k.2 * x.2)) /
        (2 * (1 - Real.cos k.1) + 2 * (1 - Real.cos k.2)))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def coulombGasWeight (β : ℝ) (lam : ℤ → ℝ) (Λ : Finset (ℤ × ℤ)) (q : Λ → ℤ) : ℝ :=
  if ∑ j, q j = 0 then
    (∏ j, lam (q j)) *
      Real.exp (-β * ((∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) * coulombPotential ((i : ℤ × ℤ) - j)) / 2))
  else 0
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def IsCoulombGasSummable (β : ℝ) (lam : ℤ → ℝ) : Prop :=
  ∀ (Λ : Finset (ℤ × ℤ)) (t : ℝ),
    Summable fun q : Λ → ℤ => coulombGasWeight β lam Λ q * Real.exp (t * ∑ j, |(q j : ℝ)|)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def coulombGasPartition (β : ℝ) (lam : ℤ → ℝ) (_hS : IsCoulombGasSummable β lam)
    (Λ : Finset (ℤ × ℤ)) : ℝ :=
  ∑' q : Λ → ℤ, coulombGasWeight β lam Λ q
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def conditionLambdaSecondMoment (β : ℝ) (_hβ : 0 < β) (lam : ℤ → ℝ)
    (_hlam : ∀ q, 0 ≤ lam q) (_hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam)
    (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (_hgΛ : g.support ⊆ Λ)
    (_hg : (g.sum fun _ a => a) = 0) : ℝ :=
  (∑' q : Λ → ℤ, coulombGasWeight β lam Λ q *
      (β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) -
        β ^ 2 * (∑ i, (q i : ℝ) * g.sum fun y b => b * coulombPotential ((i : ℤ × ℤ) - y)) ^ 2)) /
    coulombGasPartition β lam hS Λ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter Topology
@[expose] public section
namespace FroehlichSpencer.BKT
def IsConditionLambdaSecondMomentLimit (β : ℝ) (hβ : 0 < β) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (M : (ℤ × ℤ →₀ ℝ) → ℝ) : Prop :=
  ∃ Λs : ℕ → Finset (ℤ × ℤ), Tendsto Λs atTop atTop ∧
    ∀ (g : ℤ × ℤ →₀ ℝ) (hg : (g.sum fun _ a => a) = 0),
      Tendsto (fun k : {k : ℕ // g.support ⊆ Λs k} =>
        conditionLambdaSecondMoment β hβ lam hlam hlam0 hS (Λs k) g k.2 hg) atTop (𝓝 (M g))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def conditionLambdaFracCorrelation (β : ℝ) (lam : ℤ → ℝ) (_hlam : ∀ q, 0 ≤ lam q)
    (_hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (ξ : ℝ) (Λ : Finset (ℤ × ℤ))
    (a b : Λ) : ℝ :=
  let E : (Λ → ℝ) → ℝ := fun ρ =>
    (∑ i, ∑ j, ρ i * ρ j * coulombPotential ((i : ℤ × ℤ) - j)) / 2
  let f : Λ → ℝ := fun j => (if j = a then ξ else 0) - (if j = b then ξ else 0)
  (∑' q : Λ → ℤ, (if ∑ j, q j = 0 then ∏ j, lam (q j) else 0) *
      Real.exp (-β * E (fun j => (q j : ℝ) + f j))) /
    coulombGasPartition β lam hS Λ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter Topology
@[expose] public section
namespace FroehlichSpencer.BKT
def IsConditionLambdaFracCorrelationLimit (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (ξ : ℝ) (G : ℤ × ℤ → ℝ) : Prop :=
  ∃ Λs : ℕ → Finset (ℤ × ℤ), Tendsto Λs atTop atTop ∧
    ∀ x : ℤ × ℤ, Tendsto (fun k : {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k} =>
      conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ (Λs k) ⟨0, k.2.1⟩ ⟨x, k.2.2⟩) atTop
      (𝓝 (G x))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def clockLaw (n : ℕ) (_hn : 0 < n) (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    Measure (Λ → ℝ) :=
  let μ : Measure (Λ → ℝ) :=
    (Measure.pi fun _ : Λ => ∑ k : Fin n, Measure.dirac (2 * Real.pi * (k : ℝ) / n)).withDensity
      fun θ => ∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ENNReal.ofReal (Real.exp (β * Real.cos (θ b.1 - θ b.2)))
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
@[expose] public section
namespace FroehlichSpencer.BKT
attribute [local instance 1100] NormedField.toNormedSpace
theorem existsUnique_tendsto_clockTwoPoint (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) :
    ∃! c : ℝ, Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂clockLaw n hn β Λ.1) atTop (𝓝 c) := by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
@[expose] noncomputable def clockCorrelation (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) : ℝ :=
  Classical.choose (existsUnique_tendsto_clockTwoPoint n hn β hβ ξ j ℓ).exists
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def IsClockExpDecay (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) : Prop :=
  ∃ C m : ℝ, 0 < m ∧ ∀ x : ℤ × ℤ,
    clockCorrelation n hn β hβ ξ 0 x ≤
      C * Real.exp (-m * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def IsClockLongRangeOrder (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ R : ℝ, ∃ x : ℤ × ℤ,
    R ≤ Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ∧ ε ≤ clockCorrelation n hn β hβ ξ 0 x
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
def IsClockIntermediatePhase (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (q b : ℝ) : Prop :=
  (0 < b ∧ ∀ ξ : ℤ, 1 ≤ ξ → ξ ≤ (n : ℤ) - 1 → ∃ A : ℝ, 0 < A ∧ ∀ x : ℤ × ℤ,
      A * (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * b))) ≤
        clockCorrelation n hn β hβ ξ 0 x) ∧
    ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, 0 < A ∧ ∀ ξ : ℤ, 1 ≤ ξ → ξ ≤ (n : ℤ) - 1 →
      q ≤ min ((ξ : ℝ) / n) (1 - (ξ : ℝ) / n) → ∀ x : ℤ × ℤ,
        clockCorrelation n hn β hβ ξ 0 x ≤
          A * (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^
            (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'')))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def clockDisorderOperator (β ξ : ℝ) (Λ : Finset (ℤ × ℤ)) (r : ℕ)
    (hΛ : ∀ m : Fin r, (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ Λ ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ Λ)
    (θ : Λ → ℝ) : ℝ :=
  ∏ m : Fin r,
    Real.exp (β * Real.cos (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ -
        θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩ + 2 * Real.pi * ξ)) /
      Real.exp (β * Real.cos (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ -
        θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
@[expose] public section
namespace FroehlichSpencer.BKT
attribute [local instance 1100] NormedField.toNormedSpace
def IsClockDisorderLimit (n : ℕ) (hn : 0 < n) (β ξ : ℝ) (D : ℕ → ℝ) : Prop :=
  ∃ Ls : ℕ → ℕ, Tendsto Ls atTop atTop ∧ ∀ r : ℕ,
    Tendsto (fun k : {k : ℕ // r ≤ Ls k} =>
      ∫ θ, clockDisorderOperator β ξ
          (Finset.Icc (-(Ls k : ℤ)) (Ls k) ×ˢ Finset.Icc (-(Ls k : ℤ)) (Ls k)) r
          (fun m =>
            have hm : (m : ℕ) < Ls k := Nat.lt_of_lt_of_le m.isLt k.2
            have h0 : (0 : ℤ) ≤ Ls k := Int.natCast_nonneg _
            have hn : -(Ls k : ℤ) ≤ 0 := Int.neg_nonpos_of_nonneg h0
            have hx : -(Ls k : ℤ) ≤ (m : ℕ) + 1 ∧ ((m : ℕ) : ℤ) + 1 ≤ Ls k :=
              ⟨Int.le_trans hn (Int.le_add_one (Int.natCast_nonneg _)),
                Int.add_one_le_of_lt (Int.ofNat_lt.2 hm)⟩
            ⟨Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2 ⟨hn, h0⟩⟩,
              Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2
                ⟨Int.le_trans hn (Int.le_add_one (Int.le_refl 0)),
                  Int.add_one_le_of_lt
                    (Int.ofNat_lt.2 (Nat.lt_of_le_of_lt (Nat.zero_le _) hm))⟩⟩⟩) θ
        ∂clockLaw n hn β (Finset.Icc (-(Ls k : ℤ)) (Ls k) ×ˢ Finset.Icc (-(Ls k : ℤ)) (Ls k)))
      atTop (𝓝 (D r))
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def freeVillainLaw (β : ℝ) (_hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  let μ : Measure (Λ → ℝ) :=
    (Measure.pi fun _ : Λ => volume.restrict (Set.Ico (-Real.pi) Real.pi)).withDensity
      fun θ => ∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) * (θ b.1 - θ b.2 + 2 * Real.pi * m) ^ 2))
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT
noncomputable def freeVillainDisorder (β : ℝ) (_hβ : 0 < β) (ξ : ℝ) (Λ : Finset (ℤ × ℤ)) (n : ℕ)
    (hΛ : ∀ m : Fin n, (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ Λ ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ Λ)
    (θ : Λ → ℝ) : ℝ :=
  let v : ℝ → ℝ := fun t => ∑' m : ℤ, Real.exp (-(β / 2) * (t + 2 * Real.pi * m) ^ 2)
  ∏ m : Fin n,
    v (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ - θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩ +
        2 * Real.pi * ξ) /
      v (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ - θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
@[expose] public section
namespace FroehlichSpencer.BKT
def IsFreeVillainDisorderLimit (β : ℝ) (hβ : 0 < β) (ξ : ℝ) (D : ℕ → ℝ) : Prop :=
  ∃ Rs : ℕ → ℕ, Tendsto Rs atTop atTop ∧ ∀ n : ℕ,
    Tendsto (fun k : {k : ℕ // n ≤ Rs k} =>
      ∫ θ, freeVillainDisorder β hβ ξ
          (Finset.Icc (-(Rs k : ℤ)) (Rs k + 1) ×ˢ Finset.Icc (-(Rs k : ℤ)) (Rs k + 1)) n
          (fun m =>
            have hm : (m : ℕ) < Rs k := Nat.lt_of_lt_of_le m.isLt k.2
            have h0 : (0 : ℤ) ≤ Rs k := Int.natCast_nonneg _
            have hn : -(Rs k : ℤ) ≤ 0 := Int.neg_nonpos_of_nonneg h0
            have hx : -(Rs k : ℤ) ≤ (m : ℕ) + 1 ∧ ((m : ℕ) : ℤ) + 1 ≤ Rs k + 1 :=
              ⟨Int.le_trans hn (Int.le_add_one (Int.natCast_nonneg _)),
                Int.add_le_add_right (Int.ofNat_le.2 (Nat.le_of_lt hm)) 1⟩
            ⟨Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2 ⟨hn, Int.le_add_one h0⟩⟩,
              Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2
                ⟨Int.le_trans hn (Int.le_add_one (Int.le_refl 0)), Int.add_le_add_right h0 1⟩⟩⟩) θ
        ∂freeVillainLaw β hβ
          (Finset.Icc (-(Rs k : ℤ)) (Rs k + 1) ×ˢ Finset.Icc (-(Rs k : ℤ)) (Rs k + 1)))
      atTop (𝓝 (D n))
end FroehlichSpencer.BKT
end

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
noncomputable def sosDirichletLaw (L : ℕ) (β : ℝ) (_hβ : 0 < β) : Measure (Fin L × Fin L → ℤ) :=
  let μ : Measure (Fin L × Fin L → ℤ) := Measure.sum fun n : Fin L × Fin L → ℤ =>
    ENNReal.ofReal (∏ e, Real.exp (-(β * |((((squareZero L).src e).elim 0 n -
      ((squareZero L).tgt e).elim 0 n : ℤ) : ℝ)|))) • Measure.dirac n
  (μ Set.univ)⁻¹ • μ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
namespace FroehlichSpencer.BKT
noncomputable def villainClockModel (N : ℕ) (_hN : 0 < N) (β : ℝ) (_hβ : 0 < β)
    (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  let μ : Measure (Λ → ℝ) :=
    Measure.pi fun _ : Λ => ∑ k : Fin N, Measure.dirac (2 * Real.pi * (k : ℝ) / N)
  let w : (Λ → ℝ) → ℝ := fun θ =>
    ∏ b : Λ × Λ,
      (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
        (fun x : ℝ => ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))
      else fun _ => 1) (θ b.1 - θ b.2)
  μ.withDensity fun θ => ENNReal.ofReal (w θ / ∫ θ, w θ ∂μ)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def latticeAngleLiteral {Λ : Finset (ℤ × ℤ)} (θ : Λ → ℝ) (z : ℤ × ℤ) : ℝ :=
  if h : z ∈ Λ then θ ⟨z, h⟩ else 0
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def freeBox (L : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
noncomputable section
namespace FroehlichSpencer.BKT.Surface.VillainClock
noncomputable def villainContinuousCorrelation (β : ℝ) (_hβ : 0 < β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : ℝ :=
  let μ : Measure (Λ → ℝ) :=
    Measure.pi fun _ : Λ => volume.restrict (Set.Ico (-Real.pi) Real.pi)
  let w : (Λ → ℝ) → ℝ := fun θ =>
    ∏ b : Λ × Λ,
      (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
        (fun x : ℝ => ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))
      else fun _ => 1) (θ b.1 - θ b.2)
  (∫ θ, Real.cos (ξ *
      (latticeAngleLiteral θ u - latticeAngleLiteral θ v)) * w θ ∂μ) /
    ∫ θ, w θ ∂μ
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter
namespace FroehlichSpencer.BKT.Surface.VillainClock
noncomputable def villainContinuousLimit (β : ℝ) (hβ : 0 < β) (ξ : ℤ)
    (u v : ℤ × ℤ) : ℝ :=
  Filter.limsup (fun L : ℕ =>
    villainContinuousCorrelation β hβ ξ (freeBox L) u v) atTop
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
abbrev rotatorSpinSite (L : ℕ) := Fin (L + 1) × Fin (L + 1)
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def siteToZ {L : ℕ} (p : rotatorSpinSite L) : ℤ × ℤ :=
  ((p.1.val : ℤ), (p.2.val : ℤ))
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def squareBoxZ (L : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (0 : ℤ) L ×ˢ Finset.Icc (0 : ℤ) L
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def boxRadius (z : ℤ × ℤ) : ℕ := max z.1.natAbs z.2.natAbs
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def l1Dist (u v : ℤ × ℤ) : ℕ := (u.1 - v.1).natAbs + (u.2 - v.2).natAbs
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def freeRadius {L : ℕ} (p x : Fin L × Fin L) : ℕ :=
  Nat.dist p.1.val x.1.val + Nat.dist p.2.val x.2.val
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer.BKT.Surface.VillainClock
def dipoleGap (ξ : ℝ) : ℝ := min ξ (1 - ξ)
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT
noncomputable def villainClockDisorderObservable (β : ℝ) (_hβ : 0 < β) (ξ : ℝ)
    (L r : ℕ) (Λ : Finset (ℤ × ℤ))
    (hΛ : ∀ m : Fin r,
      ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ)) ∈ Λ ∧
        ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1) ∈ Λ)
    (θ : Λ → ℝ) : ℝ :=
  let v : ℝ → ℝ := fun t => ∑' m : ℤ, Real.exp (-(β / 2) * (t + 2 * Real.pi * m) ^ 2)
  ∏ m : Fin r,
    v (θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1), (hΛ m).2⟩ -
      θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ)), (hΛ m).1⟩ + 2 * Real.pi * ξ) /
      v (θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1), (hΛ m).2⟩ -
        θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ)), (hΛ m).1⟩)
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
namespace FroehlichSpencer.BKT
noncomputable def villainClockDisorderExpectation (N : ℕ) (hN : 0 < N) (β : ℝ)
    (hβ : 0 < β) (ξ : ℝ) (L r : ℕ) (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  let Λ := Finset.Icc (0 : ℤ) ((2 * L : ℕ) : ℤ) ×ˢ Finset.Icc (0 : ℤ) ((2 * L : ℕ) : ℤ)
  ∫ θ, villainClockDisorderObservable β hβ ξ L r Λ
    (fun m =>
      have h2 : L + L ≤ 2 * L := Nat.le_of_eq (Nat.two_mul L).symm
      have hx : (0 : ℤ) ≤ ((L + m.val + 1 : ℕ) : ℤ) ∧
          ((L + m.val + 1 : ℕ) : ℤ) ≤ ((2 * L : ℕ) : ℤ) :=
        ⟨Int.natCast_nonneg _,
          Int.ofNat_le.2 (Nat.le_trans (Nat.add_le_add_left (Nat.lt_of_lt_of_le m.isLt hr) L) h2)⟩
      ⟨Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2
          ⟨Int.natCast_nonneg L, Int.ofNat_le.2 (Nat.le_trans (Nat.le_add_right L L) h2)⟩⟩,
        Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2
          ⟨Int.le_add_one (Int.natCast_nonneg L),
            Int.ofNat_le.2 (Nat.le_trans (Nat.add_le_add_left hL L) h2)⟩⟩⟩) θ
    ∂villainClockModel N hN β hβ Λ
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter Topology
namespace FroehlichSpencer.BKT
def IsVillainClockDisorderExhaustingLimitPoint (N r : ℕ) (β ξ c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) : Prop :=
  ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto s atTop atTop ∧
    Tendsto (fun t => villainClockDisorderExpectation N hN β hβ ξ (r + s t) r
      (Nat.lt_of_lt_of_le hr (Nat.le_add_right r (s t))) (Nat.le_add_right r (s t))) atTop (𝓝 c)
end FroehlichSpencer.BKT
end


run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.planeRotator_powerLaw_lower_bound :
    ∃ β₀ : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ < β → 1 / (4 * Real.pi) < β' β ∧
        ∃ A : ℝ, 0 < A ∧ ∀ j ℓ : ℤ × ℤ,
          A * (1 + Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) ^
              (-(1 / (2 * Real.pi * β' β))) ≤
            planeRotatorCorrelation β hβ 1 j ℓ :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.planeRotator_kosterlitzThouless_transition :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), β < βc →
        ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), βc < β →
        (¬ ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ j ℓ : ℤ × ℤ,
          R ≤ Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2) →
            planeRotatorCorrelation β hβ 1 j ℓ ≤ ε) :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.conditionLambdaGas_secondMomentLimit_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ C α ε ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
      ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
      ∃ hS : IsCoulombGasSummable β lam,
        (∃ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsConditionLambdaSecondMomentLimit β hβ lam hlam hlam0 hS M) ∧
        ∀ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsConditionLambdaSecondMomentLimit β hβ lam hlam hlam0 hS M →
          ∀ g : ℤ × ℤ →₀ ℝ, (g.sum fun _ a => a) = 0 →
            (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
              M g :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.conditionLambdaGas_fracCorrelationLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ C α ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
        ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
        ∃ hS : IsCoulombGasSummable β lam,
          (∃ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G) ∧
          ∀ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G →
            ∀ x : ℤ × ℤ, x ≠ 0 →
              0 ≤ G x ∧ G x ≤ A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.clock_phase_diagram :
    ∃ βh β₀ : ℝ, 0 < βh ∧ βh ≤ β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧ ∃ βbar : ℕ → ℝ,
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), β < βh →
        IsClockExpDecay n hn β hβ 1) ∧
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), βbar n < β →
        ∀ ξ : ℤ, IsClockLongRangeOrder n hn β hβ ξ) ∧
      ∀ q : ℝ, 0 < q → q < 1 → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧ ∃ n₁ : ℕ,
        ∀ (n : ℕ) (hn : 0 < n), n₁ ≤ n → β₀ < β₁ n ∧ β₁ n ≤ βbar n ∧
          ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
            IsClockIntermediatePhase n hn β hβ q (β' β) :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.clock_disorder_lowerBound :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (n : ℕ) (hn : 0 < n), n₁ β ≤ n →
        (∀ k : ℕ, 1 ≤ k → k < n → ∃ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D) ∧
        ∃ β''' : ℝ, 0 ≤ β''' ∧ ∃ C : ℝ, 0 < C ∧
          ∀ k : ℕ, 1 ≤ k → k < n → ∀ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D →
            ∀ r : ℕ, 0 < r →
              C * (1 + (r : ℝ)) ^ (-(((k : ℝ) / n) ^ 2 * β''' / (2 * Real.pi))) ≤ D r :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.freeVillain_disorderLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.sos_theorem73_dirichlet :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' (𝓝[>] 0) (𝓝 0) ∧ ∃ L₀ : ℕ,
      ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → 0 < β' β ∧
        ∀ L : ℕ, L₀ ≤ L → ∀ u v : Fin L × Fin L,
          let r : ℝ := min
            (Real.sqrt ((((u.1 : ℕ) : ℝ) - v.1) ^ 2 + (((u.2 : ℕ) : ℝ) - v.2) ^ 2))
            ((min (min ((u.1 : ℕ) + 1) (L - u.1)) (min ((u.2 : ℕ) + 1) (L - u.2)) : ℕ) : ℝ)
          (∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + r))) ≤
            ∫⁻ n, ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) ∂sosDirichletLaw L β hβ) ∧
          ENNReal.ofReal (Real.log (1 + r) / β' β) ≤
            ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ ∧
          ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ < ⊤ :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.sos_roughening_transition :
    ∃ β₀ β₁ : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧
      (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → ∀ K : ℝ, ∃ (L : ℕ) (u v : Fin L × Fin L),
        ENNReal.ofReal K < ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ) ∧
      ∃ C : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∀ (L : ℕ) (u v : Fin L × Fin L),
        ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ ≤ ENNReal.ofReal C :=
  by sorry
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter Topology MeasureTheory
namespace FroehlichSpencer.BKT.Surface.VillainClock
theorem _root_.FSComparator.FS81.villain_clock_theorem71_1 :
    ∀ (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β),
      ∀ (ξ : ℕ), 1 ≤ ξ → ξ < N →
        (∀ (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ), u ∈ Λ → v ∈ Λ →
          VillainClock.villainContinuousCorrelation β hβ (ξ : ℤ) Λ u v ≤
            ∫ θ, Real.cos ((ξ : ℤ) *
              (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
              ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ Λ) ∧
        ∀ x : ℤ × ℤ,
          VillainClock.villainContinuousLimit β hβ (ξ : ℤ) (0, 0) x ≤
            Filter.limsup
              (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                (VillainClock.latticeAngleLiteral θ (0, 0) - VillainClock.latticeAngleLiteral θ x))
                ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L))
              atTop :=
  by sorry
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter Topology MeasureTheory
namespace FroehlichSpencer.BKT.Surface.VillainClock
theorem _root_.FSComparator.FS81.villain_clock_theorem71_2 :
    ∃ n₀ : ℝ → ℝ → ℕ, ∃ β'' : ℝ → ℕ → ℝ → ℝ,
      (∀ q : ℝ, 0 < q →
        Tendsto (fun β : ℝ => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, Tendsto (fun q : ℝ => n₀ β q) (𝓝[>] 0) atTop) ∧
      (∀ (β : ℝ) (N : ℕ) (q : ℝ), n₀ β q ≤ N →
        0 < β'' β N q) ∧
      ∀ q : ℝ, 0 < q →
        ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ), n₀ β q ≤ N →
          ∀ (hN : 0 < N) (ξ : ℕ), 0 < ξ → ξ < N →
            q ≤ VillainClock.dipoleGap ((ξ : ℝ) / N) →
              ((∀ (L : ℕ) (a b : VillainClock.rotatorSpinSite L),
                  ∫ θ, Real.cos ((ξ : ℤ) *
                    (VillainClock.latticeAngleLiteral θ (VillainClock.siteToZ a) -
                      VillainClock.latticeAngleLiteral θ (VillainClock.siteToZ b)))
                    ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.squareBoxZ L) ≤
                    2 * ((↑(VillainClock.freeRadius a b) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
                (∀ (L : ℕ) (u v : ℤ × ℤ),
                  VillainClock.boxRadius u ≤ L → VillainClock.boxRadius v ≤ L →
                    ∫ θ, Real.cos ((ξ : ℤ) *
                      (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
                      ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L) ≤
                      2 * ((↑(VillainClock.l1Dist u v) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
              ∀ (u v : ℤ × ℤ),
                Filter.limsup
                    (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                      (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
                      ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L))
                    atTop ≤
                  2 * ((↑(VillainClock.l1Dist u v) : ℝ) + 1) ^
                    (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) :=
  by sorry
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.villainClock_disorder_lowerBound_grid_exhausting :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N),
        n₁ β ≤ N →
          ∃ (β''' : ℝ), 0 ≤ β''' ∧
            ∃ C : ℝ, 0 < C ∧
              ∀ k : ℕ, 1 ≤ k → k < N →
                ∀ (r : ℕ) (hr : 0 < r) (c : ℝ),
                  IsVillainClockDisorderExhaustingLimitPoint
                    N r β ((k : ℝ) / N) c hβ hN hr →
                  C * (1 + (r : ℝ)) ^
                    (-(((k : ℝ) / N) ^ 2 * β''' / (2 * Real.pi))) ≤ c :=
  by sorry
end FroehlichSpencer.BKT
end
