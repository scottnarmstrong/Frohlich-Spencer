/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finsupp.Basic

/-!
# Rectangular cubical carriers

The common rectangular primal and full-lattice cell and chain carriers used by the FS82 cubical development.

Source: FS82 journal (2.9)–(2.12), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Cubical

abbrev Box (d : ℕ) := Fin d → ℕ

abbrev Anchor (d : ℕ) (B : Box d) := (i : Fin d) → Fin (B i + 1)

abbrev Coord {d : ℕ} (B : Box d) (i : Fin d) := Sum (Fin (B i + 1)) (Fin (B i))

abbrev Cell (d : ℕ) (B : Box d) := (i : Fin d) → Coord B i

abbrev Chain (d : ℕ) (B : Box d) := Cell d B →₀ ℤ

abbrev LatticeCoord := Sum ℤ ℤ

abbrev LatticeCell (d : ℕ) := (i : Fin d) → LatticeCoord

abbrev LatticeChain (d : ℕ) := LatticeCell d →₀ ℤ
end FroehlichSpencer.FS82.Cubical

end
