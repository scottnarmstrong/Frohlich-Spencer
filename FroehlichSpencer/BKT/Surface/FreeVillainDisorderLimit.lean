/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import FroehlichSpencer.BKT.Surface.FreeVillainLaw
public import FroehlichSpencer.BKT.Surface.FreeVillainDisorder

/-! # Thermodynamic limits of the free-boundary Villain disorder expectations -/

open MeasureTheory Filter Topology

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `D` is a thermodynamic limit of FS81's disorder expectations `⟨D^ξ_{0x}⟩(β)`, `x = (n, 0)`, of
the free-boundary Villain model (FS81 (1.26), (1.32)) along the boxes `[-R, R + 1]²` (side `2R + 2`,
central dual face `0*`): along some sequence of radii `R_k → ∞`, the expectation
`⟨D^ξ_{0x}⟩_{[-R_k, R_k + 1]²}(β)` converges to `D n`, for every `n` (the terms whose box contains
the string, `n ≤ R_k`, which are all but finitely many). -/
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
