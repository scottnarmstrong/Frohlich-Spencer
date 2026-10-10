/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.SumRule
import Mathlib.Tactic

/-!
# The periodic thermodynamic limit: translation-invariant limits (/)

FS81 p. 529 (iii) (periodic b.c.), p. 531 ((1.14) "also holds" for periodic rectangles) and p. 567
("in each translation-invariant thermodynamic limit"). The hard-core gas on the whole even
periodic square `Λ_{L_n}^per` (all sites carry the hard-core weight) is translation invariant,
so its thermodynamic limit points are translation-invariant states.

* `chargeEnergy_squarePeriodic`: the energy through the torus Green kernel at arbitrary vertices;
  `chargeEnergy_comp_translation`: it is invariant under every torus translation.
* `periodicChargeCorrelation_translate`: the periodic two-point functions
  `⟨q(x) q(y)⟩_{L_n}` are translation invariant (`= s_n(y - x)`).
* `squarePeriodic_energy_periodicTest`: for a test function `g` supported in `[-R,R]²`, the
  Dirichlet energy on `Λ_L^per` of its push-forward is `D(g)` once `L > 2(R+2)`; with the neutral gas's
  periodic bound this gives `periodic_chargeFluctuation_le`.
* **`periodic_thermodynamic_limit`**: translation-invariant limit points exist (compactness), every
  limit satisfies `0 ≤ ∑ g(x)g(y)s(y-x) ≤ (δ/κ) D(g)`, and if the screening hypothesis
  `∑ (1 + |w|²)|s(w)| < ∞` holds then `0 ≤ ŝ(k) ≤ (δ/κ) ε(k)`, `∑ s = 0` and
  `M(κ) ≤ 4δ/κ` (`Coulomb/SumRule.lean`; the screening sum-rule comparison alternatives there).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology Lattice2D Finset

section Kernel

variable {L : ℕ} [NeZero L]

/--
The periodic-square pseudoinverse at arbitrary vertices is the torus Green kernel.
-/
theorem squarePeriodic_neg_pseudoinverse_delta_vertex (hL : 2 < L)
    (T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ)
    (hT : (squarePeriodic L).IsLaplacianPseudoinverse T) (w w' : Fin L × Fin L) :
    -(T (deltaAt w') w) =
      torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L w)
        (squareTorusVertexEquiv L w') := by
  have h := squarePeriodic_neg_pseudoinverse_delta hL T hT
  have hG := squarePeriodic_connected L (by omega)
  have hTg : T = (squarePeriodic L).greenOp hG :=
    (squarePeriodic L).greenOp_unique hG T hT.1 hT.2
  subst hTg
  let I := squarePeriodicTorusIsomorphism hL
  have hh := congrFun (I.greenOp_transport hG (deltaAt w')) (squareTorusVertexEquiv L w)
  have hpush : I.pushField (deltaAt w') = deltaAt (squareTorusVertexEquiv L w') := by
    funext t
    simp only [Multigraph.Isomorphism.pushField, deltaAt, I, squarePeriodicTorusIsomorphism]
    congr 1
    exact propext (Equiv.symm_apply_eq _)
  rw [hpush] at hh
  simp only [Multigraph.Isomorphism.pushField, I, squarePeriodicTorusIsomorphism,
    Equiv.symm_apply_apply] at hh
  unfold torusGreenKernel
  rw [Pi.neg_apply, ← hh]

/-- The energy of a charge configuration on `Λ_L^per` through the torus Green kernel. -/
theorem chargeEnergy_squarePeriodic (hL : 2 < L)
    (T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ)
    (hT : (squarePeriodic L).IsLaplacianPseudoinverse T) (q : Fin L × Fin L → ℤ) :
    chargeEnergyInternal T q =
      (∑ w, ∑ w', (q w : ℝ) * q w' *
        torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L w)
          (squareTorusVertexEquiv L w')) / 2 := by
  unfold chargeEnergyInternal
  congr 1
  have hdec : (fun i => (q i : ℝ)) = ∑ w', (q w' : ℝ) • deltaAt w' := by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, deltaAt, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hdec, map_sum, Finset.sum_apply, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_neg, ← squarePeriodic_neg_pseudoinverse_delta_vertex hL T hT]
  ring

/-- Translation of `Λ_L^per` by the reduction of `a ∈ ℤ²`. -/
def squareTranslationInternal (L : ℕ) [NeZero L] (a : ℤ × ℤ) : (Fin L × Fin L) ≃ (Fin L × Fin L) :=
  (squareTorusVertexEquiv L).trans ((Equiv.addRight (torusPointInternal L a)).trans
    (squareTorusVertexEquiv L).symm)

theorem squareTranslation_apply_equiv (a : ℤ × ℤ) (w : Fin L × Fin L) :
    squareTorusVertexEquiv L (squareTranslationInternal L a w) =
      squareTorusVertexEquiv L w + torusPointInternal L a := by
  simp [squareTranslationInternal]

theorem squareTranslation_latticeToSquare (a x : ℤ × ℤ) :
    squareTranslationInternal L a (latticeToSquareInternal L x) = latticeToSquareInternal L (x + a) := by
  simp only [squareTranslationInternal, latticeToSquareInternal, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.coe_addRight]
  congr 1
  unfold torusPointInternal
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]

theorem chargeEnergy_comp_translation (hL : 2 < L)
    (T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ)
    (hT : (squarePeriodic L).IsLaplacianPseudoinverse T) (a : ℤ × ℤ) (q : Fin L × Fin L → ℤ) :
    chargeEnergyInternal T (fun w => q (squareTranslationInternal L a w)) = chargeEnergyInternal T q := by
  rw [chargeEnergy_squarePeriodic hL T hT, chargeEnergy_squarePeriodic hL T hT]
  congr 1
  set τ := squareTranslationInternal L a
  have hK : ∀ w w', torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L w)
      (squareTorusVertexEquiv L w') =
      torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L (τ w))
        (squareTorusVertexEquiv L (τ w')) := by
    intro w w'
    rw [squareTranslation_apply_equiv, squareTranslation_apply_equiv,
      torusGreenKernel_translation]
  calc ∑ w, ∑ w', (q (τ w) : ℝ) * q (τ w') *
        torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L w)
          (squareTorusVertexEquiv L w')
      = ∑ w, ∑ w', (q (τ w) : ℝ) * q (τ w') *
        torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L (τ w))
          (squareTorusVertexEquiv L (τ w')) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by rw [hK]
    _ = ∑ w, ∑ w', (q (τ w) : ℝ) * q w' *
        torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L (τ w))
          (squareTorusVertexEquiv L w') :=
        Finset.sum_congr rfl fun w _ => Equiv.sum_comp τ (fun w' => (q (τ w) : ℝ) * q w' *
          torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L (τ w))
            (squareTorusVertexEquiv L w'))
    _ = ∑ w, ∑ w', (q w : ℝ) * q w' *
        torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L w)
          (squareTorusVertexEquiv L w') :=
        Equiv.sum_comp τ (fun w => ∑ w', (q w : ℝ) * q w' *
          torusGreenKernel hL (torusGraph_connected L hL) (squareTorusVertexEquiv L w)
            (squareTorusVertexEquiv L w'))

end Kernel

/-! ### The periodic hard-core gas and its translation invariance -/

section PeriodicGas

/-- The periodic two-point function `⟨q(x) q(y)⟩` of the hard-core gas on the whole periodic
square `Λ_{L_n}^per` (FS81 (iii), periodic b.c.), at lattice points `x, y ∈ ℤ²` (reduced
mod `L_n`). -/
def periodicChargeCorrelationInternal (κ z : ℝ) (n : ℕ) (x y : ℤ × ℤ) : ℝ :=
  gasExpectationInternal 1 (torusGreenOpInternal n) κ (fun _ => hardCoreWeightInternal z)
    (fun q => (q (latticeToSquareInternal (torusSideInternal n) x) : ℝ) *
      q (latticeToSquareInternal (torusSideInternal n) y))

theorem gasExpectation_comp_translation (n : ℕ) (κ : ℝ) (lam : ℤ → ℝ) (a : ℤ × ℤ)
    (F : (Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℤ) → ℝ) :
    gasExpectationInternal 1 (torusGreenOpInternal n) κ (fun _ => lam)
        (fun q => F (fun w => q (squareTranslationInternal (torusSideInternal n) a w))) =
      gasExpectationInternal 1 (torusGreenOpInternal n) κ (fun _ => lam) F := by
  set τ := squareTranslationInternal (torusSideInternal n) a
  have hw : ∀ q, gasWeightInternal (torusGreenOpInternal n) κ (fun _ => lam) (fun w => q (τ w)) =
      gasWeightInternal (torusGreenOpInternal n) κ (fun _ => lam) q := by
    intro q
    unfold gasWeightInternal
    rw [chargeEnergy_comp_translation (two_lt_torusSide n) _ (isLaplacianPseudoinverse_torusGreenOp n),
      Equiv.sum_comp τ q, Equiv.prod_comp τ (fun w => lam (q w))]
  have hsum : ∀ G : (Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℤ) → ℝ,
      ∑ q ∈ chargeConfigsInternal _ 1, G (fun w => q (τ w)) =
        ∑ q ∈ chargeConfigsInternal _ 1, G q := by
    intro G
    refine Finset.sum_nbij' (fun q w => q (τ w)) (fun q w => q (τ.symm w)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [chargeConfigsInternal, Fintype.mem_piFinset] at hq ⊢
      exact fun w => hq (τ w)
    · intro q hq
      simp only [chargeConfigsInternal, Fintype.mem_piFinset] at hq ⊢
      exact fun w => hq (τ.symm w)
    · intro q _; funext w; simp
    · intro q _; funext w; simp
    · intro q _; rfl
  unfold gasExpectationInternal
  congr 1
  rw [← hsum (fun q => gasWeightInternal (torusGreenOpInternal n) κ (fun _ => lam) q * F q)]
  exact Finset.sum_congr rfl fun q _ => by rw [hw]

/-- **Translation invariance of the periodic states.** -/
theorem periodicChargeCorrelation_translate (κ z : ℝ) (n : ℕ) (x y a : ℤ × ℤ) :
    periodicChargeCorrelationInternal κ z n (x + a) (y + a) =
      periodicChargeCorrelationInternal κ z n x y := by
  unfold periodicChargeCorrelationInternal
  conv_rhs => rw [← gasExpectation_comp_translation n κ _ a]
  simp only [squareTranslation_latticeToSquare]

theorem periodicChargeCorrelation_eq (κ z : ℝ) (n : ℕ) (x y : ℤ × ℤ) :
    periodicChargeCorrelationInternal κ z n x y =
      periodicChargeCorrelationInternal κ z n 0 (y - x) := by
  have := periodicChargeCorrelation_translate κ z n 0 (y - x) x
  rw [zero_add, sub_add_cancel] at this
  exact this

theorem abs_periodicChargeCorrelation_le (κ : ℝ) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) (x y : ℤ × ℤ) :
    |periodicChargeCorrelationInternal κ z n x y| ≤ 1 := by
  unfold periodicChargeCorrelationInternal
  have hZ : 0 < gasPartitionInternal 1 (torusGreenOpInternal n) κ (fun _ => hardCoreWeightInternal z) :=
    gasPartition_pos 1 _ κ _ (fun _ n => hardCoreWeight_nonneg hz n)
      (fun _ => by simp [hardCoreWeightInternal])
  refine abs_gasExpectation_le 1 _ κ _ (fun _ n => hardCoreWeight_nonneg hz n) hZ fun q hq => ?_
  simp only [chargeConfigsInternal, Fintype.mem_piFinset, Finset.mem_Icc] at hq
  have hb : ∀ w, |(q w : ℝ)| ≤ 1 := by
    intro w
    have := hq w
    rw [abs_le]; constructor <;> exact_mod_cast (by omega)
  rw [abs_mul]
  calc |(q _ : ℝ)| * |(q _ : ℝ)| ≤ 1 * 1 := mul_le_mul (hb _) (hb _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end PeriodicGas

/-! ### Test functions on the periodic squares -/

section PeriodicTest

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
theorem torusPoint_injOn {S : ℕ} (hL : 2 * S < L) {x y : ℤ × ℤ} (hx : x ∈ boxInternal S)
    (hy : y ∈ boxInternal S) (h : torusPointInternal L x = torusPointInternal L y) : x = y := by
  rw [mem_box_iff] at hx hy
  simp only [torusPointInternal, Prod.mk.injEq] at h
  have hcoord : ∀ a b : ℤ, |a| ≤ S → |b| ≤ S → (a : ZMod L) = b → a = b := by
    intro a b ha hb hab
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b L).1 hab
    have hL' : (2 * S : ℤ) < L := by exact_mod_cast hL
    have : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]; constructor <;> linarith [abs_le.1 ha, abs_le.1 hb])
    omega
  exact Prod.ext (hcoord _ _ hx.1 hy.1 h.1) (hcoord _ _ hx.2 hy.2 h.2)

theorem add_mem_box_succ {S : ℕ} {x e : ℤ × ℤ} (hx : x ∈ boxInternal S)
    (he : |e.1| ≤ 1 ∧ |e.2| ≤ 1) : x + e ∈ boxInternal (S + 1) := by
  rw [mem_box_iff] at hx ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  constructor
  · calc |x.1 + e.1| ≤ |x.1| + |e.1| := abs_add_le _ _
      _ ≤ S + 1 := by linarith [hx.1, he.1]
  · calc |x.2 + e.2| ≤ |x.2| + |e.2| := abs_add_le _ _
      _ ≤ S + 1 := by linarith [hx.2, he.2]

/-- The test function `g` pushed to `Λ_L^per` (summed over the box `[-(R+2), R+2]²`). -/
def periodicTestInternal (L : ℕ) [NeZero L] (R : ℕ) (g : ℤ × ℤ → ℝ) : Fin L × Fin L → ℝ :=
  latticePushInternal L (Subtype.val : boxInternal (R + 2) → ℤ × ℤ) (fun v => g v.1)

theorem sum_mul_periodicTest (R : ℕ) {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g)
    (q : Fin L × Fin L → ℤ) :
    ∑ w, (q w : ℝ) * periodicTestInternal L R g w =
      ∑ x ∈ boxInternal R, g x * q (latticeToSquareInternal L x) := by
  simp_rw [mul_comm (q _ : ℝ)]
  rw [periodicTestInternal, sum_latticePush_mul,
    Finset.sum_coe_sort (boxInternal (R + 2)) (fun x => g x * q (latticeToSquareInternal L x))]
  exact sum_box_eq_of_supported (by omega) (fun x hx => by simp [hg x hx])

/-- **Energy matching**: the periodic-square Dirichlet energy of the pushed test function is
`D(g)` once `L > 2(R + 2)`. -/
theorem squarePeriodic_energy_periodicTest (hL : 2 < L) {R : ℕ} (hLR : 2 * (R + 2) < L)
    {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    ∑ e, (periodicTestInternal L R g ((squarePeriodic L).src e) -
        periodicTestInternal L R g ((squarePeriodic L).tgt e)) ^ 2 =
      latticeDirichletInternal g := by
  set gW := periodicTestInternal L R g
  let I := squarePeriodicTorusIsomorphism hL
  have hen := I.energy_transport gW
  unfold Multigraph.energy Multigraph.grad at hen
  rw [← hen]
  set h : TorusVertex L → ℝ := I.pushField gW with hh
  have hval : ∀ t, h t = ∑ x ∈ boxInternal (R + 2),
      if torusPointInternal L x = t then g x else 0 := by
    intro t
    simp only [hh, Multigraph.Isomorphism.pushField, I, squarePeriodicTorusIsomorphism, gW,
      periodicTestInternal, latticePushInternal, latticeToSquareInternal]
    rw [← Finset.sum_coe_sort (boxInternal (R + 2))]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    exact propext ⟨fun h' => by simpa using congrArg (squareTorusVertexEquiv L) h',
      fun h' => by rw [h']⟩
  have hinj : ∀ x ∈ boxInternal (R + 2), ∀ y ∈ boxInternal (R + 2),
      torusPointInternal L x = torusPointInternal L y → x = y :=
    fun x hx y hy hxy => torusPoint_injOn hLR hx hy hxy
  have hpt : ∀ y ∈ boxInternal (R + 2), h (torusPointInternal L y) = g y := by
    intro y hy
    rw [hval, Finset.sum_eq_single y (fun x hx hxy => by
      rw [ite_eq_right]; exact fun h' => hxy (hinj x hx y hy h')) (fun h' => absurd hy h')]
    simp
  have hzero : ∀ t, (∀ y ∈ boxInternal R, torusPointInternal L y ≠ t) → h t = 0 := by
    intro t ht
    rw [hval]
    refine Finset.sum_eq_zero fun x hx => ?_
    split_ifs with hxt
    · by_cases hxR : x ∈ boxInternal R
      · exact absurd hxt (ht x hxR)
      · exact hg x hxR
    · rfl
  -- the torus energy as a sum over vertices
  have hsplit : ∑ e : TorusEdge L, (h ((torusGraph L hL).src e) - h ((torusGraph L hL).tgt e)) ^ 2 =
      ∑ p : TorusVertex L, ((h p - h (p + (1, 0))) ^ 2 + (h p - h (p + (0, 1))) ^ 2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_bool]
    have e1 : p + (1, 0) = (p.1 + 1, p.2) := Prod.ext (by simp) (by simp)
    have e2 : p + (0, 1) = (p.1, p.2 + 1) := Prod.ext (by simp) (by simp)
    simp only [torusGraph_src, torusGraph_tgt, torusStep, ite_true, Bool.false_eq_true,
      ite_false, e1, e2]
    ring
  rw [hsplit]
  set F : TorusVertex L → ℝ := fun p => (h p - h (p + (1, 0))) ^ 2 + (h p - h (p + (0, 1))) ^ 2
  have hsuppF : ∀ p ∉ (boxInternal (R + 1)).image (torusPointInternal L), F p = 0 := by
    intro p hp
    have h0 : h p = 0 := hzero p fun y hy hyp =>
      hp (Finset.mem_image.2 ⟨y, box_mono (Nat.le_succ R) hy, hyp⟩)
    have he : ∀ e : TorusVertex L, e = (1, 0) ∨ e = (0, 1) → h (p + e) = 0 := by
      intro e he
      refine hzero _ fun y hy hyp => hp (Finset.mem_image.2 ?_)
      rcases he with rfl | rfl
      · refine ⟨y - (1, 0), mem_box_succ_of_add_mem (e := (1, 0)) unit_bounds_e1
          (by simpa using hy), ?_⟩
        rw [show p = torusPointInternal L y - (1, 0) by rw [hyp]; abel]
        refine Prod.ext ?_ ?_ <;> simp [torusPointInternal]
      · refine ⟨y - (0, 1), mem_box_succ_of_add_mem (e := (0, 1)) unit_bounds_e2
          (by simpa using hy), ?_⟩
        rw [show p = torusPointInternal L y - (0, 1) by rw [hyp]; abel]
        refine Prod.ext ?_ ?_ <;> simp [torusPointInternal]
    simp only [F, h0, he (1, 0) (Or.inl rfl), he (0, 1) (Or.inr rfl)]
    ring
  rw [← Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hsuppF p hp),
    Finset.sum_image (fun x hx y hy hxy => hinj x (box_mono (Nat.le_succ _) hx) y
      (box_mono (Nat.le_succ _) hy) hxy)]
  have hD : SupportedInBox (R + 1) fun x =>
      (g x - g (x + (1, 0))) ^ 2 + (g x - g (x + (0, 1))) ^ 2 := by
    intro x hx
    have h0 := (hg.mono (Nat.le_succ R)) x hx
    simp [h0, hg.shift unit_bounds_e1 x hx, hg.shift unit_bounds_e2 x hx]
  rw [latticeDirichletInternal, hD.finsum_eq_sum subset_rfl]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx2 : x ∈ boxInternal (R + 2) := box_mono (Nat.le_succ _) hx
  have h1 : torusPointInternal L x + (1, 0) = torusPointInternal L (x + (1, 0)) := by
    simp [torusPointInternal]
  have h2 : torusPointInternal L x + (0, 1) = torusPointInternal L (x + (0, 1)) := by
    simp [torusPointInternal]
  have hx1 : x + (1, 0) ∈ boxInternal (R + 2) := add_mem_box_succ hx unit_bounds_e1
  have hx1' : x + (0, 1) ∈ boxInternal (R + 2) := add_mem_box_succ hx unit_bounds_e2
  simp only [F, h1, h2, hpt x hx2, hpt _ hx1, hpt _ hx1']

end PeriodicTest

/-! ### The periodic thermodynamic limit -/

section PeriodicLimit

theorem regionWeight_univ {V : Type*} [Fintype V] [DecidableEq V] (lam : ℤ → ℝ) :
    regionWeightInternal (Finset.univ : Finset V) lam = fun _ => lam := by
  funext j n; simp [regionWeightInternal]

theorem periodic_sq_eq_sum (κ z : ℝ) (n : ℕ) {R : ℕ} {g : ℤ × ℤ → ℝ} :
    gasExpectationInternal 1 (torusGreenOpInternal n) κ (fun _ => hardCoreWeightInternal z)
        (fun q => (∑ x ∈ boxInternal R, g x * q (latticeToSquareInternal (torusSideInternal n) x)) ^ 2) =
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
        g x * g y * periodicChargeCorrelationInternal κ z n x y := by
  have hexp : ∀ q : Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℤ,
      (∑ x ∈ boxInternal R, g x * q (latticeToSquareInternal (torusSideInternal n) x)) ^ 2 =
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y *
        ((q (latticeToSquareInternal (torusSideInternal n) x) : ℝ) *
          q (latticeToSquareInternal (torusSideInternal n) y)) := by
    intro q
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  simp_rw [hexp]
  rw [gasExpectation_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [gasExpectation_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact gasExpectation_const_mul _ _ _ _ _ _

/-- The periodic screening bound in finite volume: `0 ≤ ⟨⟨q, g⟩²⟩_{L_n} ≤ (δ/κ) D(g)` once
`L_n > 2(R+2)`. -/
theorem periodic_chargeFluctuation_le {δ α κ₀ : ℝ}
    (h : ∀ L : ℕ, 1 < L → Even L →
      HardCoreChargeFluctuationBoundInternal (squarePeriodic L) δ α κ₀)
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z) (hzκ : z ≤ Real.exp (κ / 17 + α))
    (n : ℕ) {R : ℕ} (hLR : 2 * (R + 2) < torusSideInternal n) {g : ℤ × ℤ → ℝ}
    (hg : SupportedInBox R g) :
    0 ≤ ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * periodicChargeCorrelationInternal κ z n x y ∧
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y *
        periodicChargeCorrelationInternal κ z n x y ≤ δ / κ * latticeDirichletInternal g := by
  rw [← periodic_sq_eq_sum]
  constructor
  · exact gasExpectation_nonneg _ _ _ _ (fun _ m => hardCoreWeight_nonneg hz m) fun q => sq_nonneg _
  · have hb := h (torusSideInternal n) (one_lt_torusSide n) (even_torusSide n) Finset.univ κ hκ
      hκκ₀ z hz hzκ (torusGreenOpInternal n) (isLaplacianPseudoinverse_torusGreenOp n)
      (periodicTestInternal (torusSideInternal n) R g)
    rw [regionWeight_univ, squarePeriodic_energy_periodicTest (two_lt_torusSide n) hLR hg] at hb
    simp_rw [sum_mul_periodicTest R hg] at hb
    exact hb

theorem eventually_periodic_large (R : ℕ) : ∀ᶠ n in atTop, 2 * (R + 2) < torusSideInternal n :=
  (eventually_ge_atTop (R + 2)).mono fun n hn => by unfold torusSideInternal; omega

/-- **, periodic boundary conditions: translation-invariant thermodynamic limits exist and
violate the screening sum rule.** For `δ > 0` and `α` there is `κ₀` such that for `κ > κ₀`,
`0 ≤ z ≤ e^{κ/17 + α}`: (existence) along a subsequence of the even periodic squares the
two-point functions `⟨q(0) q(w)⟩` converge for every `w`; (every limit) the limit `s` is the
translation-invariant two-point function of the limit (`⟨q(x)q(y)⟩ → s(y - x)`), satisfies
`0 ≤ ∑ g(x) g(y) s(y-x) ≤ (δ/κ) D(g)`, and, if `∑ (1 + |w|²)|s(w)| < ∞`, then
`0 ≤ ŝ(k) ≤ (δ/κ) ε(k)`, `∑ s = 0` and `M(κ) = -∑ |w|² s(w) ≤ 4δ/κ`. -/
theorem periodic_thermodynamic_limit (δ : ℝ) (hδ : 0 < δ) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ s : ℤ × ℤ → ℝ,
        ∀ w, Tendsto (fun k => periodicChargeCorrelationInternal κ z (φ k) 0 w) atTop (𝓝 (s w))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ s : ℤ × ℤ → ℝ,
        (∀ w, Tendsto (fun k => periodicChargeCorrelationInternal κ z (φ k) 0 w) atTop
          (𝓝 (s w))) →
        (∀ x y, Tendsto (fun k => periodicChargeCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (s (y - x)))) ∧
        (∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g →
          0 ≤ ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x) ∧
          ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x) ≤
            δ / κ * latticeDirichletInternal g) ∧
        (Summable (fun w : ℤ × ℤ => (1 + (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2) * |s w|) →
          (∀ k : ℝ × ℝ, 0 ≤ ∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2) ∧
            ∑' w : ℤ × ℤ, s w * Real.cos (k.1 * w.1 + k.2 * w.2) ≤
              δ / κ * latticeSymbolInternal k) ∧
          ∑' w, s w = 0 ∧
          -∑' w : ℤ × ℤ, ((w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2) * s w ≤ 4 * (δ / κ)) := by
  obtain ⟨κ₀, hκ₀, h⟩ := hardCore_chargeFluctuation_bound δ hδ α
  have h' : ∀ L : ℕ, 1 < L → Even L →
      HardCoreChargeFluctuationBoundInternal (squarePeriodic L) δ α κ₀ :=
    fun L hL hE => (h L hL).2 hE
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ z hz hzκ => ⟨?_, ?_⟩⟩
  · obtain ⟨φ, hφ, l, hl⟩ := exists_subseq_tendsto_pointwise
      (fun n w => periodicChargeCorrelationInternal κ z n 0 w) (fun _ => 1)
      (fun n w => abs_periodicChargeCorrelation_le κ hz n 0 w)
    exact ⟨φ, hφ, l, hl⟩
  · intro φ hφ s hs
    have hκ : 0 < κ := hκ₀.trans hκκ₀
    have hxy : ∀ x y, Tendsto (fun k => periodicChargeCorrelationInternal κ z (φ k) x y) atTop
        (𝓝 (s (y - x))) := fun x y => by
      simp_rw [periodicChargeCorrelation_eq κ z _ x y]
      exact hs (y - x)
    have hbd : ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g →
        0 ≤ ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x) ∧
        ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x) ≤
          δ / κ * latticeDirichletInternal g := by
      intro R g hg
      have hlim : Tendsto (fun k => ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
          g x * g y * periodicChargeCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * s (y - x))) :=
        tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => (hxy x y).const_mul _
      have hev := hφ.tendsto_atTop.eventually (eventually_periodic_large R)
      exact ⟨ge_of_tendsto hlim (hev.mono fun k hk =>
          (periodic_chargeFluctuation_le h' κ hκ hκκ₀ z hz hzκ (φ k) hk hg).1),
        le_of_tendsto hlim (hev.mono fun k hk =>
          (periodic_chargeFluctuation_le h' κ hκ hκκ₀ z hz hzκ (φ k) hk hg).2)⟩
    refine ⟨hxy, hbd, fun hs2 => ?_⟩
    have hc : 0 ≤ δ / κ := div_nonneg hδ.le hκ.le
    have habs : Summable fun w => |s w| := Summable.of_nonneg_of_le (fun w => abs_nonneg _)
      (fun w => by nlinarith [abs_nonneg (s w), sq_nonneg (w.1 : ℝ), sq_nonneg (w.2 : ℝ)]) hs2
    exact ⟨fourier_bound_of_dirichlet s habs hc (fun R g hg => (hbd R g hg).1)
        (fun R g hg => (hbd R g hg).2),
      sumRule_of_dirichlet s hs2 hc (fun R g hg => (hbd R g hg).1) (fun R g hg => (hbd R g hg).2)⟩

end PeriodicLimit

end FroehlichSpencer.BKT.Coulomb
