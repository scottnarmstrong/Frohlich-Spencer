/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.DensityCenter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common

/-! # Every charge density has an admissible center -/

public section

namespace FroehlichSpencer.BKT

universe u v

/-- Every charge density `ϱ ≠ 0` has an admissible center (KP p. 5), so the center choices
quantified in KP Theorem 1.6 exist. -/
theorem Multigraph.exists_isDensityCenter {V : Type u} {E : Type v} [Fintype V]
    (G : Multigraph V E) (ϱ : V → ℤ) (hϱ : ϱ ≠ 0) : ∃ j : V, G.IsDensityCenter ϱ j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hϱ
  have hne : ((Finset.univ.filter fun j => ϱ j ≠ 0) ×ˢ
      (Finset.univ.filter fun j => ϱ j ≠ 0)).Nonempty :=
    ⟨(i, i), Finset.mem_product.2 ⟨by simpa using hi, by simpa using hi⟩⟩
  obtain ⟨p, hp, hsup⟩ := Finset.exists_mem_eq_sup _ hne fun p => G.toSimpleGraph.dist p.1 p.2
  rw [Finset.mem_product] at hp
  exact ⟨p.1, (Finset.mem_filter.1 hp.1).2, p.2, (Finset.mem_filter.1 hp.2).2, hsup⟩

end FroehlichSpencer.BKT

end
