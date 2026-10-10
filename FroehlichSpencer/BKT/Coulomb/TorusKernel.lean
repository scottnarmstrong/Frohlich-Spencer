/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.RiemannSum
public import FroehlichSpencer.BKT.Lattice2D.TorusFourier
public import FroehlichSpencer.BKT.Bridge.SquareCarriers
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
import Mathlib.Tactic

/-!
# Kernel convergence: periodic squares to the whole-plane potential

Here the boxes are the even periodic squares `Λ_L^per`,
`L = L_n = 2n + 4` (`torusSideInternal`).

* `torusGreenKernel_difference_eq_riemannSum`: the torus Green difference
  `G_L(0,0) - G_L(z,0)` is exactly the Riemann sum `R_L(z)` of the potential kernel
  (`Coulomb/RiemannSum.lean`), from the existing finite Fourier formula of
  `Lattice2D/TorusFourier.lean`.
* `squarePeriodic_neg_pseudoinverse_delta`: for **every** KP (1.2) pseudoinverse `T` of the
   `squarePeriodic L`, `-(T δ_{y})(x)` at reduced lattice points is the torus Green kernel
  (transport along `squarePeriodicTorusIsomorphism`).
* `squarePeriodic_pairing_latticePush` (exact): for sites `V` with positions `pos : V → ℤ²`,
  pushed to `Λ_L^per` by reduction mod `L` (`latticePushInternal`), and zero-sum `f`,
  `⟨push g, -T (push f)⟩ = -∑_{u,v} g(u) f(v) R_L(pos u - pos v)`.

The divergent constant
  `G_L(0,0)` cancels by neutrality.
* `tendsto_pairing_latticePush` (**the branch mixture**): as `n → ∞` this converges to
  `-∑_{u,v} g(u) f(v) a(pos u - pos v) = ∑_{u,v} g(u) f(v) C(pos u - pos v)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Lattice2D Filter Topology

/-- Reduction of a lattice point modulo `n`. -/
def torusPointInternal (n : ℕ) (z : ℤ × ℤ) : TorusVertex n := ((z.1 : ZMod n), (z.2 : ZMod n))

section TorusFourier

variable {n : ℕ} [NeZero n]

theorem torusCharacter_natCast_re (m₁ m₂ : ℕ) (z : ℤ × ℤ) :
    (torusCharacter ((m₁ : ZMod n), (m₂ : ZMod n)) (torusPointInternal n z)).re =
      Real.cos (2 * Real.pi * m₁ / n * z.1 + 2 * Real.pi * m₂ / n * z.2) := by
  have hcast : (m₁ : ZMod n) * (z.1 : ZMod n) + (m₂ : ZMod n) * (z.2 : ZMod n) =
      (((m₁ : ℤ) * z.1 + (m₂ : ℤ) * z.2 : ℤ) : ZMod n) := by push_cast; ring
  simp only [torusCharacter, torusPointInternal]
  rw [hcast, ZMod.stdAddChar_coe]
  rw [show (2 * Real.pi * Complex.I * (((m₁ : ℤ) * z.1 + (m₂ : ℤ) * z.2 : ℤ) : ℂ) / n : ℂ) =
      ((2 * Real.pi * m₁ / n * z.1 + 2 * Real.pi * m₂ / n * z.2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_ofReal_mul_I_re]

theorem cos_torusFrequencyAngle_natCast (m : ℕ) :
    Real.cos (torusFrequencyAngle (m : ZMod n)) = Real.cos (2 * Real.pi * m / n) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h := ZMod.coe_valMinAbs (m : ZMod n)
  have h' : (((m : ZMod n).valMinAbs : ℤ) : ZMod n) = ((m : ℤ) : ZMod n) := by
    rw [h]; push_cast; rfl
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h'
  have hv : ((m : ZMod n).valMinAbs : ℝ) = m - n * t := by
    have : ((m : ℤ) - (m : ZMod n).valMinAbs : ℤ) = n * t := ht
    have : ((m : ℤ) - (m : ZMod n).valMinAbs : ℝ) = n * t := by exact_mod_cast this
    push_cast at this
    linarith
  unfold torusFrequencyAngle
  rw [hv, show 2 * Real.pi * ((m : ℝ) - n * t) / n = 2 * Real.pi * m / n + (-t : ℤ) * (2 * Real.pi) by
    push_cast; field_simp; ring, Real.cos_add_int_mul_two_pi]

theorem torusFourierEigenvalue_natCast (m₁ m₂ : ℕ) :
    torusFourierEigenvalue ((m₁ : ZMod n), (m₂ : ZMod n)) =
      latticeSymbolInternal (2 * Real.pi * m₁ / n, 2 * Real.pi * m₂ / n) := by
  simp only [torusFourierEigenvalue, latticeSymbolInternal, cos_torusFrequencyAngle_natCast]

/-- Reindexing a sum over torus frequencies by integer representatives in `[0, n)²`. -/
theorem sum_torusVertex_eq_sum_range (F : TorusVertex n → ℝ) :
    ∑ k : TorusVertex n, F k =
      ∑ m ∈ Finset.range n ×ˢ Finset.range n, F ((m.1 : ZMod n), (m.2 : ZMod n)) := by
  refine Finset.sum_nbij' (fun k => (k.1.val, k.2.val)) (fun m => ((m.1 : ZMod n), (m.2 : ZMod n)))
    ?_ ?_ ?_ ?_ ?_
  · intro k _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  · intro m _
    exact Finset.mem_univ _
  · intro k _
    exact Prod.ext (ZMod.natCast_zmod_val _) (ZMod.natCast_zmod_val _)
  · intro m hm
    simp only [Finset.mem_product, Finset.mem_range] at hm
    exact Prod.ext (ZMod.val_cast_of_lt hm.1) (ZMod.val_cast_of_lt hm.2)
  · intro k _
    simp only [ZMod.natCast_zmod_val]

/-- The torus Green difference is the Riemann sum of the potential kernel. -/
theorem torusGreenKernel_difference_eq_riemannSum (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (z : ℤ × ℤ) :
    torusGreenKernel hn hG (0, 0) (0, 0) - torusGreenKernel hn hG (torusPointInternal n z) (0, 0) =
      latticeRiemannSumInternal n z := by
  rw [torusGreenKernel_difference_eq_fourier_sum hn hG]
  have hzero : (1 - (torusCharacter ((0, 0) : TorusVertex n) (torusPointInternal n z)).re) /
      torusFourierEigenvalue ((0, 0) : TorusVertex n) = 0 := by
    simp [torusCharacter]
  rw [Finset.sum_erase Finset.univ (f := fun k : TorusVertex n =>
      (1 - (torusCharacter k (torusPointInternal n z)).re) / torusFourierEigenvalue k) hzero,
    sum_torusVertex_eq_sum_range, latticeRiemannSumInternal]
  have hcard : (Fintype.card (TorusVertex n) : ℝ) = (n : ℝ) ^ 2 := by
    exact_mod_cast torusVertex_card
  rw [hcard]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [torusCharacter_natCast_re, torusFourierEigenvalue_natCast, potentialKernelIntegrandInternal]

/-- The torus Green kernel between reduced lattice points. -/
theorem torusGreenKernel_torusPoint (hn : 2 < n) (hG : (torusGraph n hn).Connected)
    (x y : ℤ × ℤ) :
    torusGreenKernel hn hG (torusPointInternal n x) (torusPointInternal n y) =
      torusGreenKernel hn hG (0, 0) (0, 0) - latticeRiemannSumInternal n (x - y) := by
  have htr := torusGreenKernel_translation hn hG (torusPointInternal n y)
    (torusPointInternal n (x - y)) (0, 0)
  have h1 : torusPointInternal n (x - y) + torusPointInternal n y = torusPointInternal n x := by
    simp [torusPointInternal]
  have h2 : ((0, 0) : TorusVertex n) + torusPointInternal n y = torusPointInternal n y := by
    simp
  rw [h1, h2] at htr
  rw [htr, ← torusGreenKernel_difference_eq_riemannSum hn hG]
  ring

end TorusFourier

/-! ### The even periodic squares `Λ_L^per`, `L = 2n + 4` -/

/-- The even torus sides `L_n = 2n + 4` of the periodic approximation. -/
def torusSideInternal (n : ℕ) : ℕ := 2 * n + 4

instance (n : ℕ) : NeZero (torusSideInternal n) := ⟨by unfold torusSideInternal; omega⟩

theorem two_lt_torusSide (n : ℕ) : 2 < torusSideInternal n := by
  unfold torusSideInternal; omega

theorem one_lt_torusSide (n : ℕ) : 1 < torusSideInternal n := by
  unfold torusSideInternal; omega

theorem even_torusSide (n : ℕ) : Even (torusSideInternal n) :=
  ⟨n + 2, by unfold torusSideInternal; ring⟩

theorem tendsto_torusSide : Tendsto torusSideInternal atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by unfold torusSideInternal; omega⟩

/--
Reduction `ℤ² → Fin L × Fin L` modulo `L`, through the residue-class presentation of the
 periodic square.
-/
def latticeToSquareInternal (L : ℕ) [NeZero L] (z : ℤ × ℤ) : Fin L × Fin L :=
  (squareTorusVertexEquiv L).symm (torusPointInternal L z)

/--
The periodic-square pseudoinverse at reduced lattice points is the torus Green
kernel.
-/
theorem squarePeriodic_neg_pseudoinverse_delta {L : ℕ} [NeZero L] (hL : 2 < L)
    (T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ)
    (hT : (squarePeriodic L).IsLaplacianPseudoinverse T) (x y : ℤ × ℤ) :
    -(T (deltaAt (latticeToSquareInternal L y)) (latticeToSquareInternal L x)) =
      torusGreenKernel hL (torusGraph_connected L hL) (torusPointInternal L x)
        (torusPointInternal L y) := by
  have hG := squarePeriodic_connected L (by omega)
  have hTg : T = (squarePeriodic L).greenOp hG :=
    (squarePeriodic L).greenOp_unique hG T hT.1 hT.2
  subst hTg
  let I := squarePeriodicTorusIsomorphism hL
  have h := congrFun (I.greenOp_transport hG (deltaAt (latticeToSquareInternal L y)))
    (torusPointInternal L x)
  have hpush : I.pushField (deltaAt (latticeToSquareInternal L y)) =
      deltaAt (torusPointInternal L y) := by
    funext t
    simp only [Multigraph.Isomorphism.pushField, deltaAt, I, squarePeriodicTorusIsomorphism,
      latticeToSquareInternal]
    congr 1
    exact propext (Equiv.symm_apply_eq _ |>.trans (by simp))
  rw [hpush] at h
  simp only [Multigraph.Isomorphism.pushField, I, squarePeriodicTorusIsomorphism] at h
  unfold torusGreenKernel
  rw [Pi.neg_apply, ← h]
  rfl

/-- Push a function on sites `V` with lattice positions `pos` forward to `Λ_L^per`. -/
def latticePushInternal (L : ℕ) [NeZero L] {V : Type*} [Fintype V] (pos : V → ℤ × ℤ)
    (f : V → ℝ) (w : Fin L × Fin L) : ℝ :=
  ∑ v, if latticeToSquareInternal L (pos v) = w then f v else 0

section Push

variable {L : ℕ} [NeZero L] {V : Type*} [Fintype V] (pos : V → ℤ × ℤ)

theorem sum_latticePush_mul (g : V → ℝ) (h : Fin L × Fin L → ℝ) :
    ∑ w, latticePushInternal L pos g w * h w = ∑ v, g v * h (latticeToSquareInternal L (pos v)) := by
  simp only [latticePushInternal, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem sum_latticePush (f : V → ℝ) : ∑ w, latticePushInternal L pos f w = ∑ v, f v := by
  simpa using sum_latticePush_mul pos f (fun _ => 1)

theorem latticePush_eq_sum (f : V → ℝ) :
    latticePushInternal L pos f = ∑ v, f v • deltaAt (latticeToSquareInternal L (pos v)) := by
  funext w
  simp only [latticePushInternal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, deltaAt]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : latticeToSquareInternal L (pos v) = w
  · simp [h]
  · simp [h, Ne.symm h]

/-- **the branch mixture, exact identity.** On `Λ_L^per`, for zero-sum `f`, the Green bilinear form of pushed
functions is `-∑_{u,v} g(u) f(v) R_L(pos u - pos v)`. -/
theorem squarePeriodic_pairing_latticePush (hL : 2 < L)
    (T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ)
    (hT : (squarePeriodic L).IsLaplacianPseudoinverse T) (g f : V → ℝ) (hf : ∑ v, f v = 0) :
    ∑ w, latticePushInternal L pos g w * -(T (latticePushInternal L pos f) w) =
      -∑ u, ∑ v, g u * f v * latticeRiemannSumInternal L (pos u - pos v) := by
  have hTf : ∀ w, -(T (latticePushInternal L pos f) w) =
      ∑ v, f v * -(T (deltaAt (latticeToSquareInternal L (pos v))) w) := by
    intro w
    rw [latticePush_eq_sum, map_sum, Finset.sum_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_neg]
  simp_rw [hTf]
  rw [sum_latticePush_mul]
  simp_rw [squarePeriodic_neg_pseudoinverse_delta hL T hT,
    torusGreenKernel_torusPoint hL (torusGraph_connected L hL)]
  set G0 := torusGreenKernel hL (torusGraph_connected L hL) (0, 0) (0, 0)
  have : ∀ u, g u * ∑ v, f v * (G0 - latticeRiemannSumInternal L (pos u - pos v)) =
      g u * G0 * ∑ v, f v - ∑ v, g u * f v * latticeRiemannSumInternal L (pos u - pos v) := by
    intro u
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  simp_rw [this, hf, mul_zero, zero_sub, Finset.sum_neg_distrib]

end Push

/-- **the branch mixture: kernel convergence.** On the even periodic squares `Λ_{L_n}^per`, the Green bilinear
form of pushed functions converges, for zero-sum `f`, to the whole-plane form
`∑_{u,v} g(u) f(v) C(pos u - pos v)` with `C = -a` (FS81 p. 529 (i)). -/
theorem tendsto_pairing_latticePush {V : Type*} [Fintype V] (pos : V → ℤ × ℤ) (g f : V → ℝ)
    (hf : ∑ v, f v = 0) :
    Tendsto (fun n : ℕ => ∑ w, latticePushInternal (torusSideInternal n) pos g w *
        -((squarePeriodic (torusSideInternal n)).greenOp
          (squarePeriodic_connected _ (one_lt_torusSide n))
          (latticePushInternal (torusSideInternal n) pos f) w)) atTop
      (𝓝 (-∑ u, ∑ v, g u * f v * potentialKernelInternal (pos u - pos v))) := by
  have hid : ∀ n : ℕ, ∑ w, latticePushInternal (torusSideInternal n) pos g w *
        -((squarePeriodic (torusSideInternal n)).greenOp
          (squarePeriodic_connected _ (one_lt_torusSide n))
          (latticePushInternal (torusSideInternal n) pos f) w) =
      -∑ u, ∑ v, g u * f v * latticeRiemannSumInternal (torusSideInternal n) (pos u - pos v) := by
    intro n
    have hG := squarePeriodic_connected _ (one_lt_torusSide n)
    exact squarePeriodic_pairing_latticePush pos (two_lt_torusSide n) _
      ⟨fun f hf => ⟨(squarePeriodic _).laplacian_greenOp_of_sum_eq_zero hG f hf,
        (squarePeriodic _).greenOp_laplacian_of_sum_eq_zero hG f hf⟩,
       (squarePeriodic _).greenOp_const hG⟩ g f hf
  simp_rw [hid]
  refine (tendsto_finsetSum _ fun u _ => tendsto_finsetSum _ fun v _ => ?_).neg
  exact ((tendsto_latticeRiemannSum _).comp tendsto_torusSide).const_mul _

end FroehlichSpencer.BKT.Coulomb
