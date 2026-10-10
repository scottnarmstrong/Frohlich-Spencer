/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Shell3

/-!
# relative fillings of co-closed dual-link currents in three dimensions

Let `J` be a co-closed integer current on the dual links of `B`.

Its chain in the bumped box is a
cycle relative to the shell: the boundary is supported on the outer endpoints of the boundary
links of `J`.

If the statement of the cubical prism operator has the extreme coordinate `0`, resp.

`B k + 1`, in every direction `k` in which `J` uses a lower, resp. upper, boundary link, then the
cone over that boundary stays in the shell.

The prism identity then gives an integer field `F` on
the dual plaquettes with

`d₁† F = J`,

supported in every coordinate rectangle that contains `J` and the statement, with
`|F(p)| ≤ ‖J‖₁`.

This is the relative filling of FS82 (2.56), in the form needed for the phase
representatives of (4.35)–(4.38).

* `relativeFilling`, `relativeFilling_spec`, `relativeFilling_support`,
  `relativeFilling_natAbs_le`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.XY.Renormalization3

variable {B : Dual3Box}

/-! ## Boundaries in coordinates -/

theorem boundary_eq_sum_boundaryBasis {B' : Box 3} (μ : Chain 3 B') :
    boundary μ = ∑ y ∈ μ.support, μ y • boundaryBasis y := by
  conv_lhs => rw [← Finsupp.sum_single μ]
  unfold Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hsingle : Finsupp.single y (μ y) = μ y • basisChain y := by
    ext x
    by_cases hx : x = y <;> simp [basisChain, hx]
  rw [hsingle, map_smul, boundary_basis]

theorem boundary_apply_eq_sum {B' : Box 3} (μ : Chain 3 B') (x : Cell 3 B') :
    boundary μ x = ∑ y ∈ μ.support, μ y * boundaryBasis y x := by
  rw [boundary_eq_sum_boundaryBasis, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun y _ => by simp

theorem boundary_currentChain (J : Dual3Links B → ℤ) :
    boundary (currentChain J) =
      ∑ e : Dual3Links B, (sgnCell e.1 * J e) • boundaryBasis (bumpCell e.1) := by
  unfold currentChain
  rw [map_sum]
  exact Finset.sum_congr rfl fun e _ => by rw [map_smul, boundary_basis]

theorem boundary_currentChain_apply (J : Dual3Links B → ℤ) (x : Cell 3 (bumpedBox3 B)) :
    boundary (currentChain J) x =
      ∑ e : Dual3Links B, sgnCell e.1 * J e * boundaryBasis (bumpCell e.1) x := by
  rw [boundary_currentChain, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun e _ => by simp

/-! ## The boundary of the chain of a co-closed current lies in the shell -/

theorem boundaryBasis_bump_cast (c c' : DualCell 3 B) :
    ((boundaryBasis (bumpCell c') (bumpCell c) : ℤ) : ℝ) =
      -((sgnCell c * sgnCell c' : ℤ) : ℝ) * dualExteriorDifferenceStencilBasis c c' := by
  rw [stencilBasis_eq_boundaryBasis]
  have h := sgnCell_sq_cast c
  have h' := sgnCell_sq_cast c'
  push_cast
  calc ((boundaryBasis (bumpCell c') (bumpCell c) : ℤ) : ℝ)
      = ((sgnCell c : ℤ) : ℝ) * ((sgnCell c : ℤ) : ℝ) *
          (((sgnCell c' : ℤ) : ℝ) * ((sgnCell c' : ℤ) : ℝ)) *
          ((boundaryBasis (bumpCell c') (bumpCell c) : ℤ) : ℝ) := by rw [h, h']; ring
    _ = _ := by ring

theorem dualCellDegree_eq_zero_of_stencil_link_ne_zero {c : DualCell 3 B} {e : Dual3Links B}
    (h : dualExteriorDifferenceStencilBasis c e.1 ≠ 0) : dualCellDegree c = 0 := by
  rw [stencilBasis_apply] at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  unfold stencilAxisTerm at hi
  cases hc : c i with
  | inr u => simp [hc] at hi
  | inl ε =>
    simp only [hc] at hi
    have hface : dualUpperFace c i ε = e.1 ∨ dualLowerFace c i ε = e.1 := by
      by_contra hcon
      push Not at hcon
      simp [hcon.1, hcon.2] at hi
    have hoff : ∀ j, j ≠ i → c j = e.1 j := by
      intro j hj
      rcases hface with hf | hf
      · rw [← hf]
        simp [dualUpperFace, Function.update_of_ne hj]
      · rw [← hf]
        simp [dualLowerFace, Function.update_of_ne hj]
    have hei : (e.1 i).isRight = true := by
      rcases hface with hf | hf
      · rw [← hf]
        simp [dualUpperFace]
      · rw [← hf]
        simp [dualLowerFace]
    have hall : ∀ j, ¬ (c j).isRight = true := by
      intro j hjr
      by_cases hj : j = i
      · subst hj
        simp [hc] at hjr
      · rw [hoff j hj] at hjr
        have h1 : j = linkDirection e := (linkCoord_isRight_iff e j).mp hjr
        have h2 : i = linkDirection e := (linkCoord_isRight_iff e i).mp hei
        exact hj (h1.trans h2.symm)
    unfold dualCellDegree dualCellAxes
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun j _ => hall j

theorem sgnCell_vertex (v : Dual3Vertices B) : sgnCell v.1 = 1 := by
  have h : dualCellAxes v.1 = ∅ := Finset.card_eq_zero.mp v.2
  simp [sgnCell, h]

/-- The boundary of the chain of a co-closed current vanishes at every cell that is not in the
shell. -/
theorem boundary_currentChain_bump (J : Dual3Links B → ℤ)
    (hJ : currentVector J ∈ coClosed (dual3ExactOneComplex B)) (c : DualCell 3 B) :
    boundary (currentChain J) (bumpCell c) = 0 := by
  rw [boundary_currentChain_apply]
  by_cases hdeg : dualCellDegree c = 0
  · let v : Dual3Vertices B := ⟨c, hdeg⟩
    have hker : (dual3ExactOneComplex B).d₀.adjoint (currentVector J) = 0 :=
      LinearMap.mem_ker.mp hJ
    have h0 := congrFun (congrArg (fun a : EuclideanSpace ℝ (Dual3Vertices B) => a.ofLp) hker) v
    change ((dual3ExactOneComplex B).d₀.adjoint (currentVector J)) v = 0 at h0
    rw [d0_adjoint_apply] at h0
    have hcast : ((∑ e : Dual3Links B, sgnCell e.1 * J e *
        boundaryBasis (bumpCell e.1) (bumpCell c) : ℤ) : ℝ) = 0 := by
      rw [Int.cast_sum, ← neg_eq_zero, ← h0, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Int.cast_mul, boundaryBasis_bump_cast c e.1]
      have hv : sgnCell c = 1 := sgnCell_vertex v
      have hs := sgnCell_sq_cast e.1
      rw [hv, currentVector_apply]
      push_cast
      calc -(((sgnCell e.1 : ℤ) : ℝ) * (J e : ℝ) *
            (-(1 * ((sgnCell e.1 : ℤ) : ℝ)) * dualExteriorDifferenceStencilBasis c e.1))
          = ((sgnCell e.1 : ℤ) : ℝ) * ((sgnCell e.1 : ℤ) : ℝ) *
              ((J e : ℝ) * dualExteriorDifferenceStencilBasis c e.1) := by ring
        _ = (J e : ℝ) * dualExteriorDifferenceStencilBasis v.1 e.1 := by rw [hs, one_mul]
    exact_mod_cast hcast
  · refine Finset.sum_eq_zero fun e _ => ?_
    have hst : dualExteriorDifferenceStencilBasis c e.1 = 0 := by
      by_contra hne
      exact hdeg (dualCellDegree_eq_zero_of_stencil_link_ne_zero hne)
    have hb : boundaryBasis (bumpCell e.1) (bumpCell c) = 0 := by
      have h := boundaryBasis_bump_cast c e.1
      rw [hst, mul_zero] at h
      exact_mod_cast h
    rw [hb, mul_zero]

theorem isShell_of_mem_support_boundary_currentChain (J : Dual3Links B → ℤ)
    (hJ : currentVector J ∈ coClosed (dual3ExactOneComplex B)) {w : Cell 3 (bumpedBox3 B)}
    (hw : w ∈ (boundary (currentChain J)).support) : IsShell w := by
  by_contra hns
  obtain ⟨c, rfl⟩ := exists_bumpCell_of_not_isShell hns
  exact (Finsupp.mem_support_iff.mp hw) (boundary_currentChain_bump J hJ c)

/-! ## The statement condition -/

/-- The statement has the extreme coordinate in every direction in which the current uses a
boundary link. -/
def AnchorAtBoundary (anchor : Anchor 3 (bumpedBox3 B)) (J : Dual3Links B → ℤ) : Prop :=
  ∀ e : Dual3Links B, J e ≠ 0 → ∀ (i : Fin 3) (u : Fin (B i + 1)), e.1 i = Sum.inr u →
    (u.val = 0 → (anchor i).val = 0) ∧ (u.val = B i → (anchor i).val = B i + 1)

theorem exists_anchor_coord_of_mem_support_boundary (anchor : Anchor 3 (bumpedBox3 B))
    (J : Dual3Links B → ℤ) (hJ : currentVector J ∈ coClosed (dual3ExactOneComplex B))
    (hanch : AnchorAtBoundary anchor J) {w : Cell 3 (bumpedBox3 B)}
    (hw : w ∈ (boundary (currentChain J)).support) :
    ∃ k : Fin 3, w k = Sum.inl (anchor k) ∧
      ((anchor k).val = 0 ∨ (anchor k).val = B k + 1) := by
  have hshell := isShell_of_mem_support_boundary_currentChain J hJ hw
  have hne := Finsupp.mem_support_iff.mp hw
  rw [boundary_currentChain_apply] at hne
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hJe : J e ≠ 0 := fun h0 => he (by rw [h0]; ring)
  have hbb : boundaryBasis (bumpCell e.1) w ≠ 0 := fun h0 => he (by rw [h0]; ring)
  rw [boundaryBasis_apply_eq_sum] at hbb
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbb
  unfold boundaryAxisTerm at hi
  cases hei : e.1 i with
  | inl v => simp [bumpCell_inl hei] at hi
  | inr u =>
    simp only [bumpCell_inr hei] at hi
    have hface : upperFace (bumpCell e.1) i ⟨u.val, u.isLt⟩ = w ∨
        lowerFace (bumpCell e.1) i ⟨u.val, u.isLt⟩ = w := by
      by_contra hcon
      push Not at hcon
      simp [hcon.1, hcon.2] at hi
    have hdir : i = linkDirection e := (linkCoord_isRight_iff e i).mp (by simp [hei])
    have hoff : ∀ j, j ≠ i → ∃ v : Fin (B j), w j =
        Sum.inl ⟨v.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt v.isLt)⟩ := by
      intro j hj
      obtain ⟨v, hv⟩ := linkCoord_isLeft_of_ne_direction e (fun h => hj (h.trans hdir.symm))
      refine ⟨v, ?_⟩
      rcases hface with hf | hf
      · rw [← hf, upperFace_apply_of_ne _ i j _ hj, bumpCell_inl hv]
      · rw [← hf, lowerFace_apply_of_ne _ i j _ hj, bumpCell_inl hv]
    obtain ⟨k, v, hkv, hext⟩ := hshell
    have hki : k = i := by
      by_contra hk
      obtain ⟨v', hv'⟩ := hoff k hk
      rw [hv'] at hkv
      have hval : v'.val + 1 = v.val := congrArg Fin.val (Sum.inl.inj hkv)
      have := v'.isLt
      omega
    subst hki
    have ha := hanch e hJe k u hei
    rcases hface with hf | hf
    · have hwk : w k = Sum.inl ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩ := by
        rw [← hf]
        simp [upperFace, vertexUpdate]
      rw [hwk] at hkv
      have hval : u.val + 1 = v.val := congrArg Fin.val (Sum.inl.inj hkv)
      have hu : u.val = B k := by omega
      refine ⟨k, ?_, Or.inr (ha.2 hu)⟩
      rw [hwk]
      exact congrArg Sum.inl (Fin.ext (by simp only; rw [ha.2 hu]; omega))
    · have hwk : w k = Sum.inl ⟨u.val, Nat.lt_succ_of_lt u.isLt⟩ := by
        rw [← hf]
        simp [lowerFace, vertexUpdate]
      rw [hwk] at hkv
      have hval : u.val = v.val := congrArg Fin.val (Sum.inl.inj hkv)
      have hu : u.val = 0 := by
        have := u.isLt
        omega
      refine ⟨k, ?_, Or.inl (ha.1 hu)⟩
      rw [hwk]
      exact congrArg Sum.inl (Fin.ext (by simp only; rw [ha.1 hu]; exact hu))

/-! ## Cones over shell vertices stay in the shell -/

theorem cellCoordUpper_le_side {B' : Box 3} (x : Cell 3 B') (j : Fin 3) :
    cellCoordUpper x j ≤ B' j := by
  unfold cellCoordUpper
  cases hx : x j with
  | inl v =>
    simp only [coordBase, coordIsEdge, Sum.elim_inl, Sum.isRight_inl, Bool.false_eq_true,
      ↓reduceIte, add_zero]
    exact Nat.lt_succ_iff.mp v.isLt
  | inr e =>
    simp only [coordBase, coordIsEdge, Sum.elim_inr, Sum.isRight_inr, ↓reduceIte]
    exact e.isLt

theorem isShell_of_mem_support_fillingOperator_basis (anchor : Anchor 3 (bumpedBox3 B))
    {w : Cell 3 (bumpedBox3 B)} {k : Fin 3} (hk : w k = Sum.inl (anchor k))
    (hext : (anchor k).val = 0 ∨ (anchor k).val = B k + 1) {x : Cell 3 (bumpedBox3 B)}
    (hx : x ∈ (fillingOperator anchor (basisChain w)).support) : IsShell x := by
  let lo : Fin 3 → ℕ := fun j => if j = k then (anchor k).val else 0
  let hi : Fin 3 → ℕ := fun j => if j = k then (anchor k).val else bumpedBox3 B j
  have hbasis : supportedInRect (basisChain w) lo hi := by
    intro y hy j
    have hyw : y = w := by
      have := Finsupp.mem_support_iff.mp hy
      by_contra hne
      exact this (by simp [basisChain, Ne.symm hne])
    subst hyw
    by_cases hj : j = k
    · subst hj
      simp [lo, hi, cellCoordLower, cellCoordUpper, coordBase, coordIsEdge, hk]
    · simp only [lo, hi, hj, ↓reduceIte]
      exact ⟨Nat.zero_le _, cellCoordUpper_le_side y j⟩
  have hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp [lo, hi]
    · simp only [lo, hi, hj, ↓reduceIte]
      exact ⟨Nat.zero_le _, Nat.lt_succ_iff.mp (anchor j).isLt⟩
  have hsupp := fillingOperator_supportedInRect anchor (basisChain w) lo hi hanchor hbasis x hx k
  simp only [lo, hi, ↓reduceIte] at hsupp
  obtain ⟨hlow, hup⟩ := hsupp
  unfold cellCoordLower at hlow
  unfold cellCoordUpper at hup
  cases hxk : x k with
  | inl v =>
    rw [hxk] at hlow hup
    simp only [coordBase, coordIsEdge, Sum.elim_inl, Sum.isRight_inl, Bool.false_eq_true,
      ↓reduceIte, add_zero] at hlow hup
    have hv : v.val = (anchor k).val := le_antisymm hup hlow
    exact ⟨k, v, hxk, by rcases hext with h | h <;> [left; right] <;> omega⟩
  | inr e =>
    rw [hxk] at hlow hup
    simp only [coordBase, coordIsEdge, Sum.elim_inr, Sum.isRight_inr, ↓reduceIte] at hlow hup
    omega

/-- The cone over the boundary of the chain of a co-closed current vanishes off the shell. -/
theorem fillingOperator_boundary_currentChain_bump (anchor : Anchor 3 (bumpedBox3 B))
    (J : Dual3Links B → ℤ) (hJ : currentVector J ∈ coClosed (dual3ExactOneComplex B))
    (hanch : AnchorAtBoundary anchor J) (c : DualCell 3 B) :
    fillingOperator anchor (boundary (currentChain J)) (bumpCell c) = 0 := by
  set bq := boundary (currentChain J) with hbq
  have hdecomp : fillingOperator anchor bq =
      ∑ w ∈ bq.support, bq w • fillingOperator anchor (basisChain w) := by
    conv_lhs => rw [← Finsupp.sum_single bq]
    unfold Finsupp.sum
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hsingle : Finsupp.single w (bq w) = bq w • basisChain w := by
      ext x
      by_cases hx : x = w <;> simp [basisChain, hx]
    rw [hsingle, map_smul]
  rw [hdecomp, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨k, hk, hext⟩ := exists_anchor_coord_of_mem_support_boundary anchor J hJ hanch hw
  have hzero : fillingOperator anchor (basisChain w) (bumpCell c) = 0 := by
    by_contra hne
    exact not_isShell_bumpCell c (isShell_of_mem_support_fillingOperator_basis anchor hk hext
      (Finsupp.mem_support_iff.mpr hne))
  simp [hzero]

/-! ## The relative filling -/

/-- The relative filling of an integer dual-link current with a given statement, as an integer
field on the dual plaquettes. -/
noncomputable def relativeFilling (anchor : Anchor 3 (bumpedBox3 B)) (J : Dual3Links B → ℤ)
    (p : Dual3Plaquettes B) : ℤ :=
  -(sgnCell p.1) * fillingOperator anchor (currentChain J) (bumpCell p.1)

/-- The boundary of the cone over the chain of a co-closed current, off the shell. -/
theorem boundary_fillingOperator_currentChain_bump (anchor : Anchor 3 (bumpedBox3 B))
    (J : Dual3Links B → ℤ) (hJ : currentVector J ∈ coClosed (dual3ExactOneComplex B))
    (hanch : AnchorAtBoundary anchor J) (e : Dual3Links B) :
    boundary (fillingOperator anchor (currentChain J)) (bumpCell e.1) = sgnCell e.1 * J e := by
  have hprism := congrArg (fun T : Chain 3 (bumpedBox3 B) →ₗ[ℤ] Chain 3 (bumpedBox3 B) =>
    T (currentChain J)) (fillingOperator_prism_identity anchor)
  change boundary (fillingOperator anchor (currentChain J)) +
      fillingOperator anchor (boundary (currentChain J)) =
    currentChain J - finalProjection anchor (currentChain J) at hprism
  have hpos : positiveDegreeSupport (currentChain J) := fun x hx => by
    rw [currentChain_homogeneous J x hx]
    exact Nat.one_pos
  have hproj : finalProjection anchor (currentChain J) = 0 :=
    orderedPrismProjection_kills_positiveSupport anchor _ hpos
  rw [hproj, sub_zero] at hprism
  have hval := congrArg (fun q : Chain 3 (bumpedBox3 B) => q (bumpCell e.1)) hprism
  simp only [Finsupp.add_apply] at hval
  rw [fillingOperator_boundary_currentChain_bump anchor J hJ hanch e.1, add_zero,
    currentChain_apply_bump] at hval
  exact hval

/-- **The relative filling fills.** -/
theorem relativeFilling_spec (anchor : Anchor 3 (bumpedBox3 B)) (J : Dual3Links B → ℤ)
    (hJ : currentVector J ∈ coClosed (dual3ExactOneComplex B))
    (hanch : AnchorAtBoundary anchor J) :
    (dual3ExactOneComplex B).d₁.adjoint
        (WithLp.toLp 2 fun p => ((relativeFilling anchor J p : ℤ) : ℝ)) =
      currentVector J := by
  classical
  ext e
  rw [d1_adjoint_apply, currentVector_apply]
  set μ := fillingOperator anchor (currentChain J) with hμ
  have hμhom : homogeneousSupport μ 2 :=
    fillingOperator_homogeneousSupport anchor _ 1 (currentChain_homogeneous J)
  have hterm : ∀ p : Dual3Plaquettes B,
      ((relativeFilling anchor J p : ℤ) : ℝ) * dual3ChartIncidence p e =
        ((sgnCell e.1 : ℤ) : ℝ) *
          ((μ (bumpCell p.1) * boundaryBasis (bumpCell p.1) (bumpCell e.1) : ℤ) : ℝ) := by
    intro p
    have hinc : dual3ChartIncidence p e = dualExteriorDifferenceStencilBasis e.1 p.1 :=
      dual3ChartIncidence_eq_coordinateStencil p e
    rw [hinc, stencilBasis_eq_boundaryBasis]
    unfold relativeFilling
    have hs := sgnCell_sq_cast p.1
    push_cast
    calc -((sgnCell p.1 : ℤ) : ℝ) * ((μ (bumpCell p.1) : ℤ) : ℝ) *
          (-(((sgnCell e.1 : ℤ) : ℝ) * ((sgnCell p.1 : ℤ) : ℝ)) *
            ((boundaryBasis (bumpCell p.1) (bumpCell e.1) : ℤ) : ℝ))
        = ((sgnCell p.1 : ℤ) : ℝ) * ((sgnCell p.1 : ℤ) : ℝ) *
            (((sgnCell e.1 : ℤ) : ℝ) * (((μ (bumpCell p.1) : ℤ) : ℝ) *
              ((boundaryBasis (bumpCell p.1) (bumpCell e.1) : ℤ) : ℝ))) := by ring
      _ = _ := by rw [hs, one_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Int.cast_sum]
  have hsum : ∑ p : Dual3Plaquettes B,
      μ (bumpCell p.1) * boundaryBasis (bumpCell p.1) (bumpCell e.1) =
      boundary μ (bumpCell e.1) := by
    rw [boundary_apply_eq_sum]
    have hinj : Set.InjOn (fun p : Dual3Plaquettes B => bumpCell p.1)
        (Finset.univ : Finset (Dual3Plaquettes B)) := fun p _ p' _ h =>
      Subtype.ext (bumpCell_injective h)
    set T := (Finset.univ : Finset (Dual3Plaquettes B)).image fun p => bumpCell p.1 with hT
    have hleft : ∑ p : Dual3Plaquettes B,
        μ (bumpCell p.1) * boundaryBasis (bumpCell p.1) (bumpCell e.1) =
        ∑ y ∈ T, μ y * boundaryBasis y (bumpCell e.1) :=
      (Finset.sum_image (f := fun y => μ y * boundaryBasis y (bumpCell e.1)) hinj).symm
    rw [hleft]
    have h1 : ∑ y ∈ T, μ y * boundaryBasis y (bumpCell e.1) =
        ∑ y ∈ T ∪ μ.support, μ y * boundaryBasis y (bumpCell e.1) := by
      refine Finset.sum_subset Finset.subset_union_left fun y hy hyT => ?_
      have hyS : y ∈ μ.support := by
        rcases Finset.mem_union.mp hy with h | h
        · exact absurd h hyT
        · exact h
      have hdeg := hμhom y hyS
      by_cases hsh : IsShell y
      · have hb : boundaryBasis y (bumpCell e.1) = 0 := by
          by_contra hne
          exact not_isShell_bumpCell e.1 (isShell_of_boundaryBasis_ne_zero hsh hne)
        rw [hb, mul_zero]
      · obtain ⟨c, rfl⟩ := exists_bumpCell_of_not_isShell hsh
        rw [cellDegree_bumpCell] at hdeg
        exact absurd (Finset.mem_image.mpr
          ⟨(⟨c, hdeg⟩ : Dual3Plaquettes B), Finset.mem_univ _, rfl⟩) hyT
    have h2 : ∑ y ∈ μ.support, μ y * boundaryBasis y (bumpCell e.1) =
        ∑ y ∈ T ∪ μ.support, μ y * boundaryBasis y (bumpCell e.1) := by
      refine Finset.sum_subset Finset.subset_union_right fun y _ hyS => ?_
      rw [Finsupp.notMem_support_iff.mp hyS, zero_mul]
    rw [h1, h2]
  rw [hsum, hμ, boundary_fillingOperator_currentChain_bump anchor J hJ hanch e]
  have hs := sgnCell_sq_cast e.1
  push_cast
  rw [← mul_assoc, hs, one_mul]

/-- The relative filling is supported in every rectangle that contains the current and the
statement. -/
theorem relativeFilling_support (anchor : Anchor 3 (bumpedBox3 B)) (J : Dual3Links B → ℤ)
    (lo hi : Fin 3 → ℕ)
    (hrect : ∀ e : Dual3Links B, J e ≠ 0 → ∀ i,
      lo i ≤ cellCoordLower (bumpCell e.1) i ∧ cellCoordUpper (bumpCell e.1) i ≤ hi i)
    (hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j)
    {p : Dual3Plaquettes B} (hp : relativeFilling anchor J p ≠ 0) (i : Fin 3) :
    lo i ≤ cellCoordLower (bumpCell p.1) i ∧ cellCoordUpper (bumpCell p.1) i ≤ hi i := by
  have hsupp := fillingOperator_supportedInRect anchor (currentChain J) lo hi hanchor
    (currentChain_supportedInRect J lo hi hrect)
  refine hsupp (bumpCell p.1) (Finsupp.mem_support_iff.mpr fun h0 => hp ?_) i
  unfold relativeFilling
  rw [h0, mul_zero]

/-- The relative filling is bounded, plaquette by plaquette, by the `ℓ¹` norm of the current. -/
theorem relativeFilling_natAbs_le (anchor : Anchor 3 (bumpedBox3 B)) (J : Dual3Links B → ℤ)
    (p : Dual3Plaquettes B) :
    (relativeFilling anchor J p).natAbs ≤ ∑ e : Dual3Links B, (J e).natAbs := by
  unfold relativeFilling
  rw [Int.natAbs_mul, Int.natAbs_neg]
  have hs : (sgnCell p.1).natAbs = 1 := by
    have h := congrArg Int.natAbs (sgnCell_mul_self p.1)
    rw [Int.natAbs_mul] at h
    have : (sgnCell p.1).natAbs * (sgnCell p.1).natAbs = 1 := by simpa using h
    exact Nat.eq_one_of_mul_eq_one_left this
  rw [hs, one_mul]
  exact (fillingOperator_coefficientwise_le_l1 anchor (currentChain J) _).trans
    (chainL1_currentChain_le J)

end FroehlichSpencer.FS82.XY

end
