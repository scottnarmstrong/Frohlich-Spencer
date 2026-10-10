/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.FiniteGreen
public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Infra.Green.APriori
public import FroehlichSpencer.Infra.Green.PathExpansion

/-!
# "`v = +∞` outside `Λ`" as a resolvent limit
-/

@[expose] public section

open Filter Topology Matrix

namespace FroehlichSpencer.T12

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}

/-- Entrywise a-priori bound `‖G_Λ(x, y)‖ ≤ 1/|Im z|` for a Hermitian kernel. -/
theorem norm_resolventColumn_le_inv (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0) (y x : X) :
    ‖Infra.resolventColumn a v Λ z y x‖ ≤ 1 / |z.im| := by
  have h1 := Infra.tsum_norm_sq_resolventColumn_le ha v Λ hz y
  have hs : Summable fun x => ‖Infra.resolventColumn a v Λ z y x‖ ^ 2 :=
    summable_of_ne_finset_zero (s := Λ) fun x hx => by
      simp [Infra.resolventColumn_of_notMem_left a v z y hx]
  have h2 := hs.le_tsum x fun j _ => by positivity
  have h3 : (1 / |z.im|) ^ 2 = 1 / z.im ^ 2 := by rw [div_pow, sq_abs, one_pow]
  exact le_of_sq_le_sq (h2.trans (h1.trans_eq h3.symm)) (by positivity)

/-- Congruence: the resolvent column on `B` only sees the potential on `B`. -/
theorem resolventColumn_congr {v v' : X → ℝ} (B : Finset X) (hv : ∀ k ∈ B, v k = v' k)
    (z : ℂ) (y x : X) :
    Infra.resolventColumn a v B z y x = Infra.resolventColumn a v' B z y x := by
  have h : Infra.restrictedOp a v B = Infra.restrictedOp a v' B := by
    ext p q
    simp only [Infra.restrictedOp_apply]
    by_cases hpq : p = q
    · subst hpq; rw [hv p p.2]
    · simp [hpq]
  unfold Infra.resolventColumn
  rw [h]

/-- Second resolvent identity between `B ⊆ A` for `y ∈ B`:
`G_A(x, y) = G_B(x, y) - ∑_{k ∈ B, k' ∈ A \ B} G_B(x, k) a(k, k') G_A(k', y)`. -/
theorem resolventColumn_eq_sub_sum_coupling_of_mem (ha : ∀ x y, a y x = star (a x y))
    (v : X → ℝ) {A B : Finset X} (hBA : B ⊆ A) {z : ℂ} (hz : z.im ≠ 0) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) :
    Infra.resolventColumn a v A z y x =
      Infra.resolventColumn a v B z y x -
        ∑ k ∈ B, ∑ k' ∈ A \ B, Infra.resolventColumn a v B z k x * a k k' *
          Infra.resolventColumn a v A z y k' := by
  have hA : IsUnit (Infra.restrictedOp a v A - z • (1 : Matrix A A ℂ)) :=
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (Infra.isHermitian_restrictedOp ha v A) z hz
  have hB : IsUnit (Infra.restrictedOp a v B - z • (1 : Matrix B B ℂ)) :=
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (Infra.isHermitian_restrictedOp ha v B) z hz
  set g := Infra.resolventColumn a v A z y with hg
  set M := Infra.restrictedOp a v B - z • (1 : Matrix B B ℂ) with hM
  let r : B → ℂ := fun u => ∑ k' ∈ A \ B, a u k' * g k'
  have hMg : M *ᵥ (fun w : B => g w) = Pi.single ⟨y, hy⟩ 1 - r := by
    funext u
    have hrow := Infra.resolventColumn_row_of_isUnit (a := a) v A hA (hBA hy) (hBA u.2)
    rw [← Finset.sum_sdiff hBA (f := fun w => a u w * g w)] at hrow
    rw [hM, Infra.restrictedOp_sub_smul_mulVec_apply]
    simp only [r, Pi.sub_apply, Pi.single_apply, Subtype.ext_iff]
    rw [← hg] at hrow
    linear_combination hrow
  have hgB : (fun w : B => g w) =
      M⁻¹ *ᵥ Pi.single ⟨y, hy⟩ 1 - M⁻¹ *ᵥ r := by
    rw [← Matrix.mulVec_sub, ← hMg, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hB), Matrix.one_mulVec]
  have h1 := congrFun hgB ⟨x, hx⟩
  rw [Pi.sub_apply, Matrix.mulVec_single_one] at h1
  simp only [Matrix.mulVec, dotProduct] at h1
  change g x = _ at h1
  have e : ∀ k ∈ B, ∑ k' ∈ A \ B, Infra.resolventColumn a v B z k x * a k k' * g k' =
      Infra.resolventColumn a v B z k x * ∑ k' ∈ A \ B, a k k' * g k' := fun k _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl e, h1, ← Finset.sum_coe_sort B]
  congr 1
  · rw [Infra.resolventColumn_of_mem a v z hx hy]; rfl
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Infra.resolventColumn_of_mem a v z hx k.2]

/-- Bridge `finiteGreen` to `resolventColumn`. -/
theorem finiteGreen_eq_resolventColumn {ν : ℕ} (B : Finset (Site ν)) (v : Site ν → ℝ)
    (E ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ B}) :
    finiteGreen ν B v E ε hε x y =
      Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) B
        ((E : ℂ) + (ε : ℂ) * Complex.I) y x := by
  rw [Infra.resolventColumn_of_mem _ _ _ x.2 y.2]
  unfold finiteGreen
  rw [hamiltonian_eq_restrictedOp]

private theorem im_pt (E ε : ℝ) (hε : ε ≠ 0) : ((E : ℂ) + (ε : ℂ) * Complex.I).im ≠ 0 := by
  simpa using hε


theorem norm_finiteGreen_exterior_entry_le {ν : ℕ} (A Λ : Finset (Site ν)) (v : Site ν → ℝ)
    (E ε : ℝ) (hε : ε ≠ 0) (w y : {x // x ∈ A}) (hw : (w : Site ν) ∉ Λ) {M : ℝ}
    (hM : 0 < M + (v w + 2 * ν - E)) :
    ‖finiteGreen ν A (fun z => v z + if z ∈ Λ then 0 else M) E ε hε w y‖ ≤
      (1 + 2 * ν / |ε|) / (M + (v w + 2 * ν - E)) := by
  set z0 : ℂ := (E : ℂ) + (ε : ℂ) * Complex.I with hz0
  have hz : z0.im ≠ 0 := im_pt E ε hε
  have hzim : z0.im = ε := by simp [hz0]
  have hzre : z0.re = E := by simp [hz0]
  set C : ℝ := 1 + 2 * ν / |ε| with hC
  set c : ℝ := v w + 2 * ν - E with hc
  rw [finiteGreen_eq_resolventColumn]
  set V : Site ν → ℝ := fun x => (v x + if x ∈ Λ then 0 else M) + 2 * (ν : ℝ) with hV
  have hspec := Infra.resolventColumn_spec (a := hoppingKernel ν) (hoppingKernel_symm ν) V A
    hz w.2 y.2
  have hsum : ∑' u, hoppingKernel ν w u * Infra.resolventColumn (hoppingKernel ν) V A z0 y u =
      ∑ u ∈ A, hoppingKernel ν w u * Infra.resolventColumn (hoppingKernel ν) V A z0 y u :=
    tsum_eq_sum fun u hu => by
      simp [Infra.resolventColumn_of_notMem_left _ V z0 y hu]
  rw [hsum] at hspec
  set g := Infra.resolventColumn (hoppingKernel ν) V A z0 y with hg
  have hVw : V w = v w + M + 2 * ν := by simp [hV, hw]
  have h1 : ‖((V w : ℂ) - z0) * g w‖ ≤ C := by
    have e : ((V w : ℂ) - z0) * g w =
        (Pi.single (y : Site ν) 1 : Site ν → ℂ) w -
          ∑ u ∈ A, hoppingKernel ν w u * g u := by
      linear_combination hspec
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖(Pi.single (y : Site ν) 1 : Site ν → ℂ) w‖ ≤ 1 := by
      by_cases h : w = (y : Site ν)
      · simp [h]
      · simp [Pi.single_eq_of_ne h]
    have h3 : ‖∑ u ∈ A, hoppingKernel ν w u * g u‖ ≤ 2 * ν / |ε| := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ u ∈ A, ‖hoppingKernel ν w u * g u‖
          ≤ ∑ u ∈ A, ‖hoppingKernel ν w u‖ * (1 / |ε|) := by
            refine Finset.sum_le_sum fun u _ => ?_
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have := norm_resolventColumn_le_inv (hoppingKernel_symm ν) V A hz y u
            rwa [hzim] at this
        _ = (∑ u ∈ A, ‖hoppingKernel ν w u‖) * (1 / |ε|) := by rw [Finset.sum_mul]
        _ ≤ (2 * ν) * (1 / |ε|) :=
            mul_le_mul_of_nonneg_right (sum_norm_hoppingKernel_le ν _ _) (by positivity)
        _ = 2 * ν / |ε| := by ring
    linarith
  have h4 : M + c ≤ ‖(V w : ℂ) - z0‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have : (((V w : ℝ) : ℂ) - z0).re = V w - E := by simp [hzre]
    rw [this, hVw]
    refine le_trans ?_ (le_abs_self _)
    rw [hc]; linarith
  rw [norm_mul] at h1
  rw [le_div_iff₀ hM]
  calc ‖g w‖ * (M + c) ≤ ‖g w‖ * ‖(V w : ℂ) - z0‖ :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = ‖(V w : ℂ) - z0‖ * ‖g w‖ := by ring
    _ ≤ C := h1


theorem tendsto_finiteGreen_exterior_entry {ν : ℕ} (A Λ : Finset (Site ν)) (v : Site ν → ℝ)
    (E ε : ℝ) (hε : ε ≠ 0) (w y : {x // x ∈ A}) (hw : (w : Site ν) ∉ Λ) :
    Tendsto (fun M : ℝ => finiteGreen ν A (fun z => v z + if z ∈ Λ then 0 else M) E ε hε w y)
      atTop (𝓝 0) := by
  set C : ℝ := 1 + 2 * ν / |ε| with hC
  set c : ℝ := v w + 2 * ν - E with hc
  have hbound : ∀ M : ℝ, 0 < M + c →
      ‖finiteGreen ν A (fun z => v z + if z ∈ Λ then 0 else M) E ε hε w y‖ ≤ C / (M + c) :=
    fun M hM => norm_finiteGreen_exterior_entry_le A Λ v E ε hε w y hw hM
  have hlim : Tendsto (fun M : ℝ => C / (M + c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ c tendsto_id)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (-c)] with M hM
  have := hbound M (by linarith)
  simpa using this


theorem tendsto_finiteGreen_exterior {ν : ℕ} (A Λ : Finset (Site ν)) (v : Site ν → ℝ) (E ε : ℝ)
    (hε : ε ≠ 0) (x y : {x // x ∈ A ∩ Λ}) :
    Tendsto (fun M : ℝ => finiteGreen ν A (fun z => v z + if z ∈ Λ then 0 else M) E ε hε
        ⟨x, (Finset.mem_inter.1 x.2).1⟩ ⟨y, (Finset.mem_inter.1 y.2).1⟩)
      atTop (𝓝 (finiteGreen ν (A ∩ Λ) v E ε hε x y)) := by
  set z0 : ℂ := (E : ℂ) + (ε : ℂ) * Complex.I with hz0
  have hz : z0.im ≠ 0 := im_pt E ε hε
  have hBA : A ∩ Λ ⊆ A := Finset.inter_subset_left
  set a := hoppingKernel ν with ha
  set V0 : Site ν → ℝ := fun x => v x + 2 * (ν : ℝ) with hV0
  set VM : ℝ → Site ν → ℝ :=
    fun M x => (v x + if x ∈ Λ then 0 else M) + 2 * (ν : ℝ) with hVM
  have hxB : (x : Site ν) ∈ (A ∩ Λ) := x.2
  have hyB : (y : Site ν) ∈ (A ∩ Λ) := y.2
  have hid : ∀ M : ℝ, finiteGreen ν A (fun z => v z + if z ∈ Λ then 0 else M) E ε hε
      ⟨x, (Finset.mem_inter.1 x.2).1⟩ ⟨y, (Finset.mem_inter.1 y.2).1⟩ =
      Infra.resolventColumn a V0 (A ∩ Λ) z0 y x -
        ∑ k ∈ A ∩ Λ, ∑ k' ∈ A \ (A ∩ Λ), Infra.resolventColumn a V0 (A ∩ Λ) z0 k x * a k k' *
          Infra.resolventColumn a (VM M) A z0 y k' := by
    intro M
    rw [finiteGreen_eq_resolventColumn]
    have h1 := resolventColumn_eq_sub_sum_coupling_of_mem (a := a) (hoppingKernel_symm ν)
      (VM M) hBA hz hxB hyB
    have hc : ∀ p q : Site ν, Infra.resolventColumn a (VM M) (A ∩ Λ) z0 q p =
        Infra.resolventColumn a V0 (A ∩ Λ) z0 q p := fun p q =>
      resolventColumn_congr (A ∩ Λ) (fun k hk => by
        simp [hVM, hV0, (Finset.mem_inter.1 hk).2]) z0 q p
    simp only [hc] at h1
    exact h1
  have hconst : Infra.resolventColumn a V0 (A ∩ Λ) z0 y x =
      finiteGreen ν (A ∩ Λ) v E ε hε x y :=
    (finiteGreen_eq_resolventColumn (A ∩ Λ) v E ε hε x y).symm
  rw [← hconst]
  refine Tendsto.congr (fun M => (hid M).symm) ?_
  have hz1 : Tendsto (fun M : ℝ => ∑ k ∈ A ∩ Λ, ∑ k' ∈ A \ (A ∩ Λ),
      Infra.resolventColumn a V0 (A ∩ Λ) z0 k x * a k k' * Infra.resolventColumn a (VM M) A z0 y k')
      atTop (𝓝 0) := by
    have : (0 : ℂ) = ∑ k ∈ A ∩ Λ, ∑ k' ∈ A \ (A ∩ Λ),
        Infra.resolventColumn a V0 (A ∩ Λ) z0 k x * a k k' * 0 := by
      simp
    rw [this]
    refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun k' hk' => ?_
    refine tendsto_const_nhds.mul ?_
    have hk'A := (Finset.mem_sdiff.1 hk').1
    have hk'B := (Finset.mem_sdiff.1 hk').2
    have hk'Λ : k' ∉ Λ := fun h => hk'B (Finset.mem_inter.2 ⟨hk'A, h⟩)
    have := tendsto_finiteGreen_exterior_entry A Λ v E ε hε ⟨k', hk'A⟩
      ⟨y, (Finset.mem_inter.1 y.2).1⟩ hk'Λ
    refine this.congr fun M => ?_
    rw [finiteGreen_eq_resolventColumn]
  simpa using tendsto_const_nhds.sub hz1

end FroehlichSpencer.T12

end
