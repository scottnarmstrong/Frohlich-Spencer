/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.DualStencil

/-!
A kernel-checked enumeration of all ordered local coefficient incidences for the side-one 4D dual box.

Source: FS82 journal finite-support and zero-Dirichlet convention (2.32)–(2.35), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical


@[expose] def originZero : Fin 4 → ℤ := fun _ => 0


end
end FroehlichSpencer.FS82.Cubical

end
