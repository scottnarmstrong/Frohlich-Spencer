/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.Padding

/-!
# FS82 finite branch type and activity envelope

The source mode-energy definitions below provide only the finite envelope interface.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents


open FroehlichSpencer.FS82.Cubical

/-- The source Gaussian rate for the positive modes `2π (n+1)`. -/
@[expose] noncomputable def sourceModeRate (beta0 : ℝ) : ℝ :=
  beta0 * (2 * Real.pi) ^ 2


/- Source mode energies used to bound the finite branch activity envelope. -/
namespace ModeEnergy


end ModeEnergy


/--
Source choice `z_m = exp(β₀ (2πm)²)` from (2.73), evaluated on the
integer mode labels of the current expansion.
-/
@[expose] noncomputable def sourceActivityParameter (beta0 : ℝ) (m : ℤ) : ℝ :=
  Real.exp (sourceModeRate beta0 * (m : ℝ) ^ 2)


end FroehlichSpencer.FS82.Currents

end
