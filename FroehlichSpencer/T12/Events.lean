/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Multiscale.Singular
public import FroehlichSpencer.Surface.ConfigurationSpace

/-!
# Gentle classes and gentle-component events
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


def gentleClasses {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν))
    (S₀ : Set (Site ν)) (v : Site ν → ℝ) (j : ℕ) : Set (Set (Site ν)) :=
  {C | C ∈ chainClusters (siteDist ν) (singularSetsGen P blk S₀ v j) (2 * scaleR P.K₀ j) ∧
    IsGentle P blk j v C}

/-- `V_{D,i}`: `D` is a gentle component of `S_i^Λ(v)`
(Λ-restricted model). -/
def gentleEventIn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) (i : ℕ) : Set (Configuration ν) :=
  {v | (D : Set (Site ν)) ∈ gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v i}

/-- `V_D = ⋃_i V_{D,i}`. -/
def gentleEventAnyIn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) : Set (Configuration ν) :=
  ⋃ i, gentleEventIn P Λ D i

/-- Unfolded membership in `V_{D,i}`. -/
theorem mem_gentleEventIn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) (i : ℕ)
    (v : Site ν → ℝ) :
    v ∈ gentleEventIn P Λ D i ↔
      (D : Set (Site ν)) ∈ chainClusters (siteDist ν) (singularSetsIn P Λ v i)
        (2 * scaleR P.K₀ i) ∧ IsGentle P (fun B => B ∩ Λ) i v D :=
  Iff.rfl

end FroehlichSpencer.T12

end
