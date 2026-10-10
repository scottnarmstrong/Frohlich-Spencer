/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Duality
public import FroehlichSpencer.FS82.XY.DualComplexD

/-!
# Integral filling at the higher dual degree

The real exactness of the grounded dual complex has an integral counterpart:
every integral primal 2-cycle in a rectangular box is the boundary of an
integral primal 3-chain. This is the lattice exactness input needed when the
degree-generic quotient is related to XY cycle modes.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

/-- Every positive-degree integral cubical cycle in a rectangular box has an
integral filling one degree higher. -/
theorem integer_positiveDegree_filling {d : ℕ} {B : Box d}
    (q : Chain d B) (k : ℕ) (hk : 0 < k)
    (hq : homogeneousSupport q k) (hcycle : boundary q = 0) :
    homogeneousSupport (fillingOperator
      (fun i : Fin d => ⟨0, Nat.zero_lt_succ (B i)⟩) q) (k + 1) ∧
      boundary (fillingOperator
        (fun i : Fin d => ⟨0, Nat.zero_lt_succ (B i)⟩) q) = q := by
  let anchor : Anchor d B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
  have hpositive : ∀ c ∈ q.support, 0 < cellDegree c := by
    intro c hc
    rw [hq c hc]
    exact hk
  have hprojection : finalProjection anchor q = 0 :=
    orderedPrismProjection_kills_positiveSupport anchor q hpositive
  have hprism := congrArg
    (fun T : Chain d B →ₗ[ℤ] Chain d B => T q)
    (fillingOperator_prism_identity anchor)
  change boundary (fillingOperator anchor q) +
      fillingOperator anchor (boundary q) =
    q - finalProjection anchor q at hprism
  rw [hcycle, map_zero, hprojection, sub_zero, add_zero] at hprism
  constructor
  · exact fillingOperator_homogeneousSupport anchor q k hq
  · exact hprism


end
end FroehlichSpencer.FS82.XY
