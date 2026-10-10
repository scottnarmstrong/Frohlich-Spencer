/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Laplacian
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Mean-zero inverse of the finite graph Laplacian

This file constructs the real mean-zero subspace and the inverse of the
finite-difference Laplacian on it, following KP (1.2), p. 2.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

open Multigraph

/-- The subspace of real vertex functions whose sum is zero, the source
carrier for KP's pseudoinverse (1.2), p. 2. -/
def zeroSumSubmodule (V : Type u) [Fintype V] : Submodule ℝ (V → ℝ) where
  carrier := {f | ∑ v, f v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change ∑ v, (f v + g v) = 0
    rw [Finset.sum_add_distrib, hf, hg, zero_add]
  smul_mem' := by
    intro a f hf
    change ∑ v, a * f v = 0
    rw [← Finset.mul_sum, hf, mul_zero]

/-- Membership in the zero-sum submodule is exactly the zero-sum condition. -/
theorem mem_zeroSumSubmodule_iff {V : Type u} [Fintype V] (f : V → ℝ) :
    f ∈ zeroSumSubmodule V ↔ ∑ v, f v = 0 := by
  change (∑ v, f v = 0) ↔ _
  rfl

/-- The arithmetic mean of a real-valued function on a nonempty finite type. -/
noncomputable def vertexMean (V : Type u) [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ v, f v) / (Fintype.card V : ℝ)

/-- The mean of a constant function is that constant. -/
theorem vertexMean_const {V : Type u} [Fintype V] (hV : Nonempty V) (c : ℝ) :
    vertexMean V (fun _ => c) = c := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (Fintype.card_pos_iff.mpr hV))
  dsimp [vertexMean]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

/-- The mean is additive. -/
theorem vertexMean_add {V : Type u} [Fintype V] (f g : V → ℝ) :
    vertexMean V (f + g) = vertexMean V f + vertexMean V g := by
  simp only [vertexMean, Pi.add_apply, Finset.sum_add_distrib, add_div]

/-- The mean commutes with scalar multiplication. -/
theorem vertexMean_smul {V : Type u} [Fintype V] (a : ℝ) (f : V → ℝ) :
    vertexMean V (a • f) = a * vertexMean V f := by
  simp only [vertexMean, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  exact mul_div_assoc _ _ _

/-- Remove the constant mode by subtracting the arithmetic mean. -/
noncomputable def zeroSumProjection {V : Type u} [Fintype V] (hV : Nonempty V) :
    (V → ℝ) →ₗ[ℝ] zeroSumSubmodule V where
  toFun f := ⟨fun v => f v - vertexMean V f, by
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast (Fintype.card_pos_iff.mpr hV))
    change ∑ v, (f v - vertexMean V f) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_univ, nsmul_eq_mul]
    dsimp [vertexMean]
    field_simp [hcard]
    ring⟩
  map_add' f g := by
    apply Subtype.ext
    funext v
    change f v + g v - vertexMean V (f + g) =
      (f v - vertexMean V f) + (g v - vertexMean V g)
    rw [vertexMean_add]
    ring
  map_smul' a f := by
    apply Subtype.ext
    funext v
    change a * f v - vertexMean V (a • f) =
      a * (f v - vertexMean V f)
    rw [vertexMean_smul]
    ring

/-- Pointwise formula for the zero-sum projection. -/
@[simp]
theorem zeroSumProjection_apply {V : Type u} [Fintype V] (hV : Nonempty V)
    (f : V → ℝ) (v : V) :
    (zeroSumProjection hV f : V → ℝ) v = f v - vertexMean V f := rfl

/-- The zero-sum projection fixes every zero-sum function. -/
@[simp]
theorem zeroSumProjection_apply_of_sum_eq_zero {V : Type u} [Fintype V]
    (hV : Nonempty V) (f : V → ℝ) (hf : ∑ v, f v = 0) :
    zeroSumProjection hV f = ⟨f, hf⟩ := by
  apply Subtype.ext
  funext v
  simp [zeroSumProjection, vertexMean, hf]

/-- The zero-sum projection kills constant functions. -/
@[simp]
theorem zeroSumProjection_const {V : Type u} [Fintype V]
    (hV : Nonempty V) (c : ℝ) :
    zeroSumProjection hV (fun _ => c) = 0 := by
  apply Subtype.ext
  funext v
  simp [zeroSumProjection, vertexMean_const hV]

/-- Pairing is linear in subtraction in its first argument. -/
theorem pairing_sub_left {V : Type u} [Fintype V]
    (f g h : V → ℝ) :
    pairing (f - g) h = pairing f h - pairing g h := by
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  exact sub_mul _ _ _

/-- Pairing a constant function against a field is its constant times the sum
of that field. -/
theorem pairing_const_left {V : Type u} [Fintype V] (c : ℝ) (f : V → ℝ) :
    pairing (fun _ => c) f = c * ∑ v, f v := by
  unfold pairing
  rw [← Finset.mul_sum]

/-- Pairing is linear in negation in its second argument. -/
theorem pairing_neg_right {V : Type u} [Fintype V] (f g : V → ℝ) :
    pairing f (-g) = -pairing f g := by
  simp [pairing]

/-- A zero-sum field pairs equally with itself and its projection away from
the constant mode. -/
theorem pairing_zeroSumProjection_left_eq {V : Type u} [Fintype V]
    (hV : Nonempty V) (f g : V → ℝ) (hg : ∑ v, g v = 0) :
    pairing (zeroSumProjection hV f) g = pairing f g := by
  have hfun : (zeroSumProjection hV f : V → ℝ) =
      f - fun _ => vertexMean V f := by
    funext v
    simp
  rw [hfun, pairing_sub_left, pairing_const_left, hg, mul_zero, sub_zero]

namespace Multigraph

variable {V : Type u} {E : Type v}

/-- Restrict the graph Laplacian to the invariant subspace of zero-sum fields. -/
def laplacianOnZeroSum (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] : zeroSumSubmodule V →ₗ[ℝ] zeroSumSubmodule V where
  toFun f := ⟨G.laplacian (f : V → ℝ), G.sum_laplacian_eq_zero (f : V → ℝ)⟩
  map_add' f g := by
    apply Subtype.ext
    funext j
    exact congrFun ((G.laplacianₗ ℝ).map_add (f : V → ℝ) (g : V → ℝ)) j
  map_smul' a f := by
    apply Subtype.ext
    funext j
    exact congrFun ((G.laplacianₗ ℝ).map_smul a (f : V → ℝ)) j

/-- The Laplacian is injective on the zero-sum subspace of a connected graph. -/
theorem laplacianOnZeroSum_injective (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) :
    Function.Injective (G.laplacianOnZeroSum) := by
  intro f g h
  apply Subtype.ext
  have hΔ : G.laplacian (f : V → ℝ) = G.laplacian (g : V → ℝ) :=
    congrArg Subtype.val h
  have hsub : G.laplacian ((f : V → ℝ) - (g : V → ℝ)) = 0 := by
    have hm := (G.laplacianₗ ℝ).map_sub (f : V → ℝ) (g : V → ℝ)
    change G.laplacian ((f : V → ℝ) - (g : V → ℝ)) =
      G.laplacian (f : V → ℝ) - G.laplacian (g : V → ℝ) at hm
    rw [hΔ] at hm
    exact hm.trans (sub_self _)
  obtain ⟨c, hc⟩ := (G.laplacian_eq_zero_iff_exists_const hG
    ((f : V → ℝ) - (g : V → ℝ))).mp hsub
  have hsum : ∑ v, ((f : V → ℝ) v - (g : V → ℝ) v) = 0 := by
    rw [Finset.sum_sub_distrib, f.property, g.property, sub_self]
  have hsumc : ∑ v : V, c = 0 := by
    calc
      ∑ v : V, c = ∑ v, ((f : V → ℝ) v - (g : V → ℝ) v) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (congrFun hc v).symm
      _ = 0 := hsum
  have hcardc : (Fintype.card V : ℝ) * c = 0 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsumc
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (Fintype.card_pos_iff.mpr hG.nonempty))
  rcases mul_eq_zero.mp hcardc with hzero | hc0
  · exact (hcard hzero).elim
  · have hfg : (f : V → ℝ) - (g : V → ℝ) = 0 := by
      calc
        _ = fun _ => c := hc
        _ = 0 := by funext v; simp [hc0]
    exact sub_eq_zero.mp hfg

/-- The Laplacian is a linear equivalence of the zero-sum subspace for a
connected finite graph. -/
noncomputable def laplacianZeroSumEquiv (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) :
    zeroSumSubmodule V ≃ₗ[ℝ] zeroSumSubmodule V :=
  LinearEquiv.ofBijective (G.laplacianOnZeroSum)
    ⟨G.laplacianOnZeroSum_injective hG,
      LinearMap.injective_iff_surjective.mp (G.laplacianOnZeroSum_injective hG)⟩

/-- KP's mean-zero inverse of the finite-difference Laplacian, extended
linearly to all fields by first removing their constant mode; see KP (1.2),
p. 2. -/
noncomputable def greenOp (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  (zeroSumSubmodule V).subtype.comp
    ((G.laplacianZeroSumEquiv hG).symm.toLinearMap.comp
      (zeroSumProjection hG.nonempty))

/-- The mean-zero inverse is the inverse of the restricted Laplacian after
projection onto zero-sum fields. -/
@[simp]
theorem greenOp_apply (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (f : V → ℝ) :
    G.greenOp hG f =
      ((G.laplacianZeroSumEquiv hG).symm (zeroSumProjection hG.nonempty f) :
        V → ℝ) := rfl

/-- The mean-zero inverse always has zero sum. -/
theorem greenOp_sum_eq_zero (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (f : V → ℝ) :
    ∑ v, G.greenOp hG f v = 0 := by
  change ∑ v, ((G.laplacianZeroSumEquiv hG).symm
    (zeroSumProjection hG.nonempty f) : V → ℝ) v = 0
  exact (mem_zeroSumSubmodule_iff _).mp
    ((G.laplacianZeroSumEquiv hG).symm
      (zeroSumProjection hG.nonempty f)).property

/-- On zero-sum inputs the Laplacian of the mean-zero inverse recovers the
input, KP (1.2), p. 2. -/
theorem laplacian_greenOp_of_sum_eq_zero (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∑ v, f v = 0) : G.laplacian (G.greenOp hG f) = f := by
  change G.laplacian
    (((G.laplacianZeroSumEquiv hG).symm
      (zeroSumProjection hG.nonempty f) : zeroSumSubmodule V) : V → ℝ) = f
  rw [zeroSumProjection_apply_of_sum_eq_zero hG.nonempty f hf]
  exact congrArg Subtype.val
    ((G.laplacianZeroSumEquiv hG).apply_symm_apply ⟨f, hf⟩)

/-- On zero-sum fields the mean-zero inverse is a two-sided inverse of the
Laplacian, KP (1.2), p. 2. -/
theorem greenOp_laplacian_of_sum_eq_zero (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∑ v, f v = 0) : G.greenOp hG (G.laplacian f) = f := by
  have hΔsum := G.sum_laplacian_eq_zero f
  change ((G.laplacianZeroSumEquiv hG).symm
    (zeroSumProjection hG.nonempty (G.laplacian f)) : V → ℝ) = f
  rw [zeroSumProjection_apply_of_sum_eq_zero hG.nonempty _ hΔsum]
  have he :
      G.laplacianZeroSumEquiv hG ⟨f, hf⟩ =
        ⟨G.laplacian f, hΔsum⟩ := by
    apply Subtype.ext
    rfl
  have hinv :
      (G.laplacianZeroSumEquiv hG).symm ⟨G.laplacian f, hΔsum⟩ =
        ⟨f, hf⟩ := by
    rw [← he]
    simp
  exact congrArg Subtype.val hinv

/-- The mean-zero inverse annihilates constant inputs, KP (1.2), p. 2. -/
@[simp]
theorem greenOp_const (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (c : ℝ) :
    G.greenOp hG (fun _ => c) = 0 := by
  simp [greenOp]

/-- Applying the Laplacian to the mean-zero inverse returns the zero-sum
projection of an arbitrary field. -/
theorem laplacian_greenOp_eq_zeroSumProjection (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (f : V → ℝ) :
    G.laplacian (G.greenOp hG f) =
      (zeroSumProjection hG.nonempty f : V → ℝ) := by
  change G.laplacian
    (((G.laplacianZeroSumEquiv hG).symm
      (zeroSumProjection hG.nonempty f) : zeroSumSubmodule V) : V → ℝ) =
      (zeroSumProjection hG.nonempty f : V → ℝ)
  exact congrArg Subtype.val
    ((G.laplacianZeroSumEquiv hG).apply_symm_apply
      (zeroSumProjection hG.nonempty f))

/-- A field lies in the range of the finite graph Laplacian exactly when it
has zero sum. -/
theorem exists_laplacian_preimage_iff_sum_eq_zero (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (f : V → ℝ) :
    (∃ u, G.laplacian u = f) ↔ ∑ v, f v = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact G.sum_laplacian_eq_zero u
  · intro hf
    exact ⟨G.greenOp hG f, G.laplacian_greenOp_of_sum_eq_zero hG f hf⟩

/-- The mean-zero inverse is symmetric for the vertex pairing. -/
theorem pairing_greenOp_comm (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (f g : V → ℝ) :
    pairing f (G.greenOp hG g) = pairing (G.greenOp hG f) g := by
  have hf := G.greenOp_sum_eq_zero hG f
  have hg := G.greenOp_sum_eq_zero hG g
  calc
    pairing f (G.greenOp hG g) =
        pairing (zeroSumProjection hG.nonempty f) (G.greenOp hG g) :=
      (pairing_zeroSumProjection_left_eq hG.nonempty f _ hg).symm
    _ = pairing (G.laplacian (G.greenOp hG f)) (G.greenOp hG g) := by
      rw [G.laplacian_greenOp_eq_zeroSumProjection hG f]
    _ = pairing (G.greenOp hG f) (G.laplacian (G.greenOp hG g)) :=
      (G.pairing_laplacian_comm (G.greenOp hG f) (G.greenOp hG g)).symm
    _ = pairing (G.greenOp hG f) (zeroSumProjection hG.nonempty g) := by
      rw [G.laplacian_greenOp_eq_zeroSumProjection hG g]
    _ = pairing (G.greenOp hG f) g := by
      calc
        pairing (G.greenOp hG f) (zeroSumProjection hG.nonempty g) =
            pairing (zeroSumProjection hG.nonempty g) (G.greenOp hG f) :=
          pairing_comm _ _
        _ = pairing g (G.greenOp hG f) :=
          pairing_zeroSumProjection_left_eq hG.nonempty g _ hf
        _ = pairing (G.greenOp hG f) g := pairing_comm _ _

/-- The Green quadratic form on zero-sum inputs equals the energy of the
mean-zero inverse. -/
theorem pairing_eq_energy_greenOp (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∑ v, f v = 0) :
    pairing f (-G.greenOp hG f) = G.energy (G.greenOp hG f) := by
  have hΔ := G.laplacian_greenOp_of_sum_eq_zero hG f hf
  have hE := G.energy_eq_neg_pairing_laplacian (G.greenOp hG f)
  rw [hΔ] at hE
  calc
    pairing f (-G.greenOp hG f) = -pairing f (G.greenOp hG f) :=
      pairing_neg_right _ _
    _ = -pairing (G.greenOp hG f) f := by rw [pairing_comm]
    _ = G.energy (G.greenOp hG f) := hE.symm

/-- The Green quadratic form is nonnegative on zero-sum inputs. -/
theorem pairing_greenOp_nonneg (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∑ v, f v = 0) :
    0 ≤ pairing f (-G.greenOp hG f) := by
  rw [G.pairing_eq_energy_greenOp hG f hf]
  exact G.energy_nonneg (G.greenOp hG f)

/-- Equality in the Green quadratic form for a zero-sum field forces that
field to vanish. -/
theorem pairing_greenOp_eq_zero_iff (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∑ v, f v = 0) :
    pairing f (-G.greenOp hG f) = 0 ↔ f = 0 := by
  constructor
  · intro hq
    have hE : G.energy (G.greenOp hG f) = 0 := by
      rw [← G.pairing_eq_energy_greenOp hG f hf]
      exact hq
    obtain ⟨c, hc⟩ := (G.energy_eq_zero_iff_exists_const hG
      (G.greenOp hG f)).mp hE
    have huSum := G.greenOp_sum_eq_zero hG f
    have hsumc : ∑ v : V, c = 0 := by
      calc
        ∑ v : V, c = ∑ v, G.greenOp hG f v := by
          apply Finset.sum_congr rfl
          intro v hv
          exact (congrFun hc v).symm
        _ = 0 := huSum
    have hcardc : (Fintype.card V : ℝ) * c = 0 := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hsumc
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast (Fintype.card_pos_iff.mpr hG.nonempty))
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp hcardc with hzero | hc0
      · exact (hcard hzero).elim
      · exact hc0
    have hu0 : G.greenOp hG f = 0 := by
      funext v
      rw [hc]
      simp [hc0]
    have hΔ := G.laplacian_greenOp_of_sum_eq_zero hG f hf
    rw [hu0] at hΔ
    have h0 : G.laplacian (0 : V → ℝ) = 0 := by
      change (G.laplacianₗ ℝ) 0 = 0
      exact map_zero _
    exact hΔ.symm.trans h0
  · intro hf0
    simp [hf0, pairing]

/-- The mean-zero inverse is uniquely characterized among linear maps by its
two inverse identities on zero-sum fields and its action on constants,
KP (1.2), p. 2. -/
theorem greenOp_unique (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (T : (V → ℝ) →ₗ[ℝ] (V → ℝ))
    (hT : ∀ f, (∑ v, f v = 0) →
      G.laplacian (T f) = f ∧ T (G.laplacian f) = f)
    (hTc : ∀ c, T (fun _ => c) = 0) : T = G.greenOp hG := by
  apply LinearMap.ext
  intro f
  funext v
  let p := zeroSumProjection hG.nonempty f
  let u : V → ℝ := p
  have hu : ∑ j, u j = 0 := by
    exact (mem_zeroSumSubmodule_iff _).mp p.property
  have hdecomp : f = u + fun _ => vertexMean V f := by
    funext j
    dsimp [u, p]
    ring
  have hTdecomp : T f = T u := by
    calc
      T f = T (u + fun _ => vertexMean V f) := congrArg T hdecomp
      _ = T u + T (fun _ => vertexMean V f) := T.map_add _ _
      _ = T u := by rw [hTc]; exact add_zero _
  have hGdecomp : G.greenOp hG f = G.greenOp hG u := by
    calc
      G.greenOp hG f =
          G.greenOp hG (u + fun _ => vertexMean V f) := congrArg (G.greenOp hG) hdecomp
      _ = G.greenOp hG u + G.greenOp hG (fun _ => vertexMean V f) :=
        (G.greenOp hG).map_add _ _
      _ = G.greenOp hG u := by simp
  let w : V → ℝ := G.greenOp hG u
  have hw : ∑ j, w j = 0 := G.greenOp_sum_eq_zero hG u
  have hTw : T (G.laplacian w) = w := (hT w hw).2
  rw [G.laplacian_greenOp_of_sum_eq_zero hG u hu] at hTw
  change T f v = G.greenOp hG f v
  rw [hTdecomp, hGdecomp, hTw]

end Multigraph

end FroehlichSpencer.BKT
