/- Unit-box path and divergence example for the Λ* constraint. -/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeBridgeHigher
public import FroehlichSpencer.FS82.Cubical.UnitBox

/-!
# A unit-box test supported on the finite dual link set

The two-link path has zero divergence at the unique finite dual vertex and
nonzero divergence at its two exterior endpoints.

It witnesses that the
co-closed test condition is imposed only on Λ* vertices.

Source: FS82 journal (2.34), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open FroehlichSpencer.FS82.Cubical
open scoped InnerProductSpace

noncomputable def realLatticeBoundary {d : ℕ} :
    RealLatticeChain d →ₗ[ℝ] RealLatticeChain d :=
  realifyLatticeLinearMap latticeBoundary

theorem realLatticeBoundary_basis (c : LatticeCell 4) :
    realLatticeBoundary (Finsupp.single c (1 : ℝ)) =
      castLatticeChain (latticeBoundaryBasis c) := by
  simp [realLatticeBoundary, realifyLatticeLinearMap,
    Finsupp.linearCombination_single]

theorem castLatticeChain_apply {d : ℕ} (q : LatticeChain d) (c : LatticeCell d) :
    castLatticeChain q c = (q c : ℝ) := by
  simp [castLatticeChain]


end FroehlichSpencer.FS82.Gaussian

end
