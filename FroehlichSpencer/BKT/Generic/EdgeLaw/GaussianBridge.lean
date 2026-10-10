/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Defs
public import FroehlichSpencer.BKT.Generic.StripWeightScaling

/-!
# The Gaussian edge law is the KP law (generic core)

The rooted edge law `edgeLaw G w v` (`Generic/EdgeLaw/Defs.lean`) was built as KP's rooted law
`gffLaw` (`Surface/GFFLaw.lean`; KP (1.3), p. 2) with the Gaussian bond weight replaced by a strip
weight.

For the Gaussian bond weight `w(z) = e^{-βz²/2}` (`gaussianWeight`) the two densities agree
pointwise, `∏_e e^{-β ∇φ(e)²/2} = e^{-(β/2) ∑_e ∇φ(e)²}`, so the two laws coincide
(`edgeLaw_gaussianWeight`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

variable {V : Type*} [Fintype V] {E : Type*} [Fintype E]

omit [Fintype V] in
/-- The Gaussian edge density is KP's: `∏_e e^{-β ∇φ(e)²/2} = e^{-(β/2) ∑_e ∇φ(e)²}`. -/
theorem prod_gaussianWeight_re (G : Multigraph V E) (β : ℝ) (φ : V → ℝ) :
    ∏ e, (gaussianWeight β ((G.grad φ e : ℝ) : ℂ)).re =
      Real.exp (-(β / 2) * ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [gaussianWeight_ofReal, Complex.ofReal_re]
  rfl

/--
The rooted edge law with the Gaussian bond weight is the KP law.
-/
theorem edgeLaw_gaussianWeight (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (v : V) : edgeLaw G (gaussianWeight β) v = gffLaw G hG β hβ v := by
  simp only [edgeLaw, gffLaw, prod_gaussianWeight_re]

end FroehlichSpencer.BKT.Generic

end
