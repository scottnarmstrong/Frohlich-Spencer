/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import FroehlichSpencer.BKT.Surface.ClockLaw
public import FroehlichSpencer.BKT.Surface.ClockDisorderOperator

/-! # Thermodynamic limits of the disorder expectations of the clock model -/

open MeasureTheory Filter Topology

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `D` is a thermodynamic limit of FS81's disorder expectations `⟨D^ξ_{0x}⟩^{(n)}(β)`,
`x = (r, 0)`, of the `ℤ_n` clock model with free boundary conditions (FS81 (7.1)–(7.2), `clockLaw`;
(1.32)) along the centred boxes `[-L, L]²`: along some sequence of radii `L_k → ∞`, the expectation
`⟨D^ξ_{0x}⟩_{[-L_k, L_k]²}` converges to `D r`, for every `r` (the terms whose box contains the
string, `r ≤ L_k`, which are all but finitely many). -/
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
