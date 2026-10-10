/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Prop47Statements
public import FroehlichSpencer.BKT.Charges.SharedSeparatedParentSelector
public import FroehlichSpencer.BKT.SpinWaves.Initial
import FroehlichSpencer.BKT.SpinWaves.Prop47
import FroehlichSpencer.BKT.SpinWaves.InitialSupport
import FroehlichSpencer.BKT.SpinWaves.SquareGeometry
import FroehlichSpencer.BKT.Reduction.T22SeparationBridge
import FroehlichSpencer.BKT.Charges.ParentBall
import FroehlichSpencer.BKT.Charges.ParentScaleEstimates
import FroehlichSpencer.BKT.Charges.SeparatedPatch
import FroehlichSpencer.BKT.Charges.PatchIsolation
import FroehlichSpencer.BKT.Charges.DensityRouting
import FroehlichSpencer.BKT.FiniteGraph.Laplacian
import Mathlib.Algebra.BigOperators.Option

/-!
# KP Proposition 2.4 from Lemma 4.6 (the spin-wave assembly)

The P2.4 cover selection is
the shared  selector `sharedMinimumSquareCover` .

For `ϱ* ∈ 𝒩₀` the spin wave is
`a = a₀ + ∑_{k ≥ 1} ∑_{s ∈ 𝒮_k^sep(ϱ*)} a_s`, with `a₀` from KP Lemma 4.5 (`InitialSupport.lean`,
whose separation input is discharged from Theorem 2.2(b)) and `a_s` from KP Proposition 4.7
(`p47Step_of_l46Step`).

* Clause (1): every summand is constant on each `D⁺(ϱ')`, `ϱ' ∈ 𝒩₀(ϱ*)`.
* Clauses (2)–(3): every summand and its Laplacian live within `2^{k-1} + 1` of the square, which
  lies in `D(ϱ*)` because `d(ϱ*) > 32·2^k` (
* Clause (4): no edge carries a nonzero gradient of two summands, so the energy is
  additive and `E_β(a, ϱ*) ≥ β⁻¹(‖ϱ*‖²/16 + D₃ ∑_k |𝒮_k^sep(ϱ*)|)`.

The cross-scale case uses the
  four selected ancestors of / for scale gaps `1–4` and the plateau of the larger wave
  for gaps `≥ 5`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Reduction

open SpinWaves SpinWaves.P47

/-! ## Energy additivity -/

section Generic

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] (G : Multigraph V E)

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem sq_sum_eq_sum_sq_of_pairwise {ι : Type} [DecidableEq ι] (F : Finset ι) (x : ι → ℝ)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → x i = 0 ∨ x j = 0) :
    (∑ i ∈ F, x i) ^ 2 = ∑ i ∈ F, x i ^ 2 := by
  by_cases hz : ∀ i ∈ F, x i = 0
  · rw [Finset.sum_eq_zero hz, Finset.sum_eq_zero fun i hi => by rw [hz i hi]; ring]
    ring
  · push Not at hz
    obtain ⟨i₀, hi₀, hx⟩ := hz
    have hothers : ∀ j ∈ F, j ≠ i₀ → x j = 0 := fun j hj hji =>
      (h i₀ hi₀ j hj (Ne.symm hji)).resolve_left hx
    rw [Finset.sum_eq_single i₀ hothers (fun h => absurd hi₀ h),
      Finset.sum_eq_single i₀ (fun j hj hji => by rw [hothers j hj hji]; ring)
        (fun h => absurd hi₀ h)]

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem grad_finset_sum {ι : Type} (F : Finset ι) (g : ι → V → ℝ) (e : E) :
    G.grad (fun v => ∑ i ∈ F, g i v) e = ∑ i ∈ F, G.grad (g i) e := by
  simp only [Multigraph.grad, Finset.sum_sub_distrib]

omit [Fintype V] [DecidableEq V] in
/-- The energy of a sum of fields is the sum of their energies when no edge carries a nonzero
gradient of two of them. -/
theorem energy_finset_sum_of_disjoint {ι : Type} [DecidableEq ι] (F : Finset ι)
    (g : ι → V → ℝ)
    (h : ∀ e, ∀ i ∈ F, ∀ j ∈ F, i ≠ j → G.grad (g i) e = 0 ∨ G.grad (g j) e = 0) :
    G.energy (fun v => ∑ i ∈ F, g i v) = ∑ i ∈ F, G.energy (g i) := by
  unfold Multigraph.energy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [grad_finset_sum G F g e]
  exact sq_sum_eq_sum_sq_of_pairwise F (fun i => G.grad (g i) e) (h e)

omit [DecidableEq V] [Fintype E] in
theorem pairing_finset_sum {ι : Type} (F : Finset ι) (g : ι → V → ℝ) (ϱ : V → ℤ) :
    Multigraph.pairing (fun v => ∑ i ∈ F, g i v) (fun j => (ϱ j : ℝ)) =
      ∑ i ∈ F, Multigraph.pairing (g i) (fun j => (ϱ j : ℝ)) := by
  unfold Multigraph.pairing
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

omit [Fintype V] in
theorem laplacian_finset_sum {ι : Type} (F : Finset ι) (g : ι → V → ℝ) (j : V) :
    G.laplacian (fun v => ∑ i ∈ F, g i v) j = ∑ i ∈ F, G.laplacian (g i) j := by
  have hsum : (fun v => ∑ i ∈ F, g i v) = ∑ i ∈ F, g i := by
    funext v
    simp [Finset.sum_apply]
  rw [hsum]
  change G.laplacianₗ ℝ (∑ i ∈ F, g i) j = _
  rw [map_sum, Finset.sum_apply]
  rfl

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem ne_zero_of_grad_ne_zero (f : V → ℝ) (e : E) (h : G.grad f e ≠ 0) :
    f (G.src e) ≠ 0 ∨ f (G.tgt e) ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by simp [Multigraph.grad, hc.1, hc.2])

end Generic

/-! ## Gradient disjointness ( -/

section Disjoint

variable {V E : Type} [DecidableEq V] (G : Multigraph V E)

/-- The support and plateau clauses of a P4.7 wave for a square `s` at scale `m`. -/
structure IsSquareWave (s : Finset V) (m : ℕ) (w : V → ℝ) : Prop where
  supp : ∀ j, w j ≠ 0 → ∃ y ∈ s, G.toSimpleGraph.dist j y ≤ 2 ^ (m - 1)
  plateau : ∃ c, ∀ j, (∃ y ∈ s, G.toSimpleGraph.dist j y ≤ 2 ^ (m - 3)) → w j = c

omit [DecidableEq V] in
/-- A wave has zero gradient on an edge whose endpoints both lie in its plateau. -/
theorem IsSquareWave.grad_eq_zero {s : Finset V} {m : ℕ} {w : V → ℝ}
    (hw : IsSquareWave G s m w) (e : E)
    (hsrc : ∃ y ∈ s, G.toSimpleGraph.dist (G.src e) y ≤ 2 ^ (m - 3))
    (htgt : ∃ y ∈ s, G.toSimpleGraph.dist (G.tgt e) y ≤ 2 ^ (m - 3)) : G.grad w e = 0 := by
  obtain ⟨c, hc⟩ := hw.plateau
  simp [Multigraph.grad, hc _ hsrc, hc _ htgt]

/-- Endpoints of an edge are at distance one. -/
theorem dist_src_tgt (e : E) : G.toSimpleGraph.dist (G.src e) (G.tgt e) = 1 :=
  SimpleGraph.dist_eq_one_iff_adj.mpr (adj_toSimpleGraph G ⟨e, Or.inl ⟨rfl, rfl⟩⟩)

/-- Two waves with far-apart squares have no common nonzero-gradient edge. -/
theorem IsSquareWave.grad_disjoint_of_far (hG : G.toSimpleGraph.Connected) {s s' : Finset V}
    {m m' : ℕ} {w w' : V → ℝ} (hw : IsSquareWave G s m w) (hw' : IsSquareWave G s' m' w')
    (hfar : ∀ y ∈ s, ∀ y' ∈ s', 2 ^ (m - 1) + 2 ^ (m' - 1) + 1 < G.toSimpleGraph.dist y y')
    (e : E) : G.grad w e = 0 ∨ G.grad w' e = 0 := by
  by_contra hc
  push Not at hc
  have h1 := dist_src_tgt G e
  have hnear : ∀ x x' : V, (x = G.src e ∨ x = G.tgt e) → (x' = G.src e ∨ x' = G.tgt e) →
      G.toSimpleGraph.dist x x' ≤ 1 := by
    rintro x x' (rfl | rfl) (rfl | rfl)
    · simp
    · omega
    · rw [SimpleGraph.dist_comm]; omega
    · simp
  obtain ⟨x, hx, hwx⟩ : ∃ x, (x = G.src e ∨ x = G.tgt e) ∧ w x ≠ 0 := by
    rcases ne_zero_of_grad_ne_zero G w e hc.1 with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  obtain ⟨x', hx', hwx'⟩ : ∃ x', (x' = G.src e ∨ x' = G.tgt e) ∧ w' x' ≠ 0 := by
    rcases ne_zero_of_grad_ne_zero G w' e hc.2 with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  obtain ⟨y, hy, hxy⟩ := hw.supp x hwx
  obtain ⟨y', hy', hxy'⟩ := hw'.supp x' hwx'
  have hxx' := hnear x x' hx hx'
  have t1 := hG.dist_triangle (u := y) (v := x) (w := y')
  have t2 := hG.dist_triangle (u := x) (v := x') (w := y')
  rw [SimpleGraph.dist_comm] at hxy
  have := hfar y hy y' hy'
  omega

/-- The base wave (supported on `supp ϱ*`) and a square wave have no common nonzero-gradient
edge: inside the square the edge lies in the plateau; outside it the support is far
(base and square cases). -/
theorem IsSquareWave.grad_disjoint_base (hG : G.toSimpleGraph.Connected) {s : Finset V}
    {m : ℕ} {w a₀ : V → ℝ} {ϱ : V → ℤ} (hw : IsSquareWave G s m w)
    (ha₀ : ∀ j, a₀ j ≠ 0 → ϱ j ≠ 0)
    (hfar : ∀ x, ϱ x ≠ 0 → x ∉ s → ∀ y ∈ s, 2 ^ (m - 1) + 1 < G.toSimpleGraph.dist x y)
    (e : E) : G.grad a₀ e = 0 ∨ G.grad w e = 0 := by
  by_contra hc
  push Not at hc
  have h1 := dist_src_tgt G e
  obtain ⟨x, hx, hax⟩ : ∃ x, (x = G.src e ∨ x = G.tgt e) ∧ a₀ x ≠ 0 := by
    rcases ne_zero_of_grad_ne_zero G a₀ e hc.1 with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hϱx := ha₀ x hax
  have hone : 1 ≤ 2 ^ (m - 3) := Nat.one_le_two_pow
  by_cases hxs : x ∈ s
  · apply hc.2
    refine hw.grad_eq_zero G e ⟨x, hxs, ?_⟩ ⟨x, hxs, ?_⟩
    · rcases hx with rfl | rfl
      · simp
      · omega
    · rcases hx with rfl | rfl
      · rw [SimpleGraph.dist_comm]; omega
      · simp
  · obtain ⟨x', hx', hwx'⟩ : ∃ x', (x' = G.src e ∨ x' = G.tgt e) ∧ w x' ≠ 0 := by
      rcases ne_zero_of_grad_ne_zero G w e hc.2 with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    obtain ⟨y, hy, hxy⟩ := hw.supp x' hwx'
    have hxx' : G.toSimpleGraph.dist x x' ≤ 1 := by
      rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
      · simp
      · omega
      · rw [SimpleGraph.dist_comm]; omega
      · simp
    have t := hG.dist_triangle (u := x) (v := x') (w := y)
    have := hfar x hϱx hxs y hy
    omega

end Disjoint

/-! ## The cross-scale case -/

section CrossScale

variable (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L) {E : Type}
  (Λ : Multigraph (Fin L × Fin L) E)

include hL in
/-- , cross-scale case: let `s` (scale `m`) and `s'` (scale `m' > m`) be separated squares of
the shared selection, and let an edge `e` have an endpoint within `2^{m-1}` of `s` and an endpoint
within `2^{m'-1}` of `s'`. Then both endpoints of `e` lie in the plateau `dist(·, s') ≤ 2^{m'-3}` of
the larger square. The patch of `s` lies in `s'`; for gaps `≥ 5` the edge is within the plateau
radius of that patch, and for gaps `1–4` the minimum cover forces `s'` to be the selected
ancestor `P_{m'-m}(s)`, which contains the `2^{m-1}`-neighbourhood of `s`. -/
theorem cross_scale_endpoints_near
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (hΛ : Λ.toSimpleGraph.Connected) (ϱ : ChargeDensity L) {m m' : ℕ} (hm : 1 ≤ m)
    (hmm' : m < m') {s s' : Finset (Fin L × Fin L)}
    (hs : s ∈ separatedSquares boundary L ϱ ⟨m, hm⟩
      (sharedMinimumSquareCover boundary L ϱ (by omega) ⟨m, hm⟩))
    (hs' : s' ∈ separatedSquares boundary L ϱ ⟨m', by omega⟩
      (sharedMinimumSquareCover boundary L ϱ (by omega) ⟨m', by omega⟩))
    (e : E) {x x' y y' : Fin L × Fin L} (hx : x = Λ.src e ∨ x = Λ.tgt e)
    (hx' : x' = Λ.src e ∨ x' = Λ.tgt e) (hy : y ∈ s)
    (hxy : Λ.toSimpleGraph.dist x y ≤ 2 ^ (m - 1)) (hy' : y' ∈ s')
    (hxy' : Λ.toSimpleGraph.dist x' y' ≤ 2 ^ (m' - 1)) :
    (∃ z ∈ s', Λ.toSimpleGraph.dist (Λ.src e) z ≤ 2 ^ (m' - 3)) ∧
      (∃ z ∈ s', Λ.toSimpleGraph.dist (Λ.tgt e) z ≤ 2 ^ (m' - 3)) := by
  classical
  have hL0 : 0 < L := by omega
  have he1 := dist_src_tgt Λ e
  -- distances between the endpoints
  have hend : ∀ a b : Fin L × Fin L, (a = Λ.src e ∨ a = Λ.tgt e) →
      (b = Λ.src e ∨ b = Λ.tgt e) → Λ.toSimpleGraph.dist a b ≤ 1 := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · simp
    · omega
    · rw [SimpleGraph.dist_comm]; omega
    · simp
  -- powers of two
  have hpm : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [← pow_succ']; congr 1; omega
  have hpm' : 2 * 2 ^ (m' - 1) = 2 ^ m' := by
    rw [← pow_succ']; congr 1; omega
  have hmle : 2 ^ m ≤ 2 ^ (m' - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the patch of `s`
  obtain ⟨z₀, hz₀⟩ := separatedSquare_patch_nonempty boundary L ϱ ⟨m, hm⟩ _ s hs
  obtain ⟨hz₀s, hz₀supp⟩ := Finset.mem_inter.mp hz₀
  have hz₀0 : ϱ z₀ ≠ 0 := (Finset.mem_filter.mp hz₀supp).2
  have hdiam_s : Λ.toSimpleGraph.dist y z₀ ≤ 2 * (2 ^ m - 1) := by
    rw [← hdist]
    exact P47.latticeDistance_le_of_mem_separatedSquare boundary hL hs hy hz₀s
  have hx'x := hend x' x hx' hx
  -- Claim 1: the patch point lies in `s'`
  have hz₀s' : z₀ ∈ s' := by
    by_contra hns
    have hfar : 32 * 2 ^ m' < latticeDistance boundary L y' z₀ :=
      P47.thirtyTwo_mul_lt_latticeDistance boundary hs' hy' hz₀0 hns
    rw [hdist] at hfar
    have t1 := hΛ.dist_triangle (u := y') (v := x') (w := z₀)
    have t2 := hΛ.dist_triangle (u := x') (v := x) (w := z₀)
    have t3 := hΛ.dist_triangle (u := x) (v := y) (w := z₀)
    rw [SimpleGraph.dist_comm] at hxy'
    have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  rcases Nat.lt_or_ge (m' - m) 5 with hgap | hgap
  · -- gaps 1–4: `s'` is the selected ancestor `P_{m'-m}(s)`
    set j : ParentOffset := ⟨m' - m, by omega, by omega⟩ with hj
    set P := ancestorParent boundary L ⟨m, hm⟩ j hL0 s with hP
    set C' := sharedMinimumSquareCover boundary L ϱ hL0 ⟨m', by omega⟩
    have hscale : (⟨ancestorScale ⟨m, hm⟩ j, by simp [ancestorScale]; omega⟩ :
        PositiveSquareScale) = ⟨m', by omega⟩ := Subtype.ext (by
      simp only [ancestorScale, hj]
      omega)
    have hPmem : P ∈ C'.val := by
      have h := sharedMinimumSquareCover_contains_separated_parents boundary L ϱ hL0 ⟨m, hm⟩ j
        s hs
      rw [hscale] at h
      exact h
    have hs'C : s' ∈ C'.val := (Finset.mem_filter.mp hs').1
    have hsC : s ∈ (sharedMinimumSquareCover boundary L ϱ hL0 ⟨m, hm⟩).val :=
      (Finset.mem_filter.mp hs).1
    have hsq : s ∈ kpSquares boundary L m :=
      (sharedMinimumSquareCover boundary L ϱ hL0 ⟨m, hm⟩).property.1.1 hsC
    have hside := squareSide_le_domain_of_mem_separatedSquares boundary L ϱ ⟨m, hm⟩ _ s hs
    have hPsq : P ∈ kpSquares boundary L (ancestorScale ⟨m, hm⟩ j) :=
      ancestorParent_mem_kpSquares boundary L ⟨m, hm⟩ j hL0 s
    have hs'sq : s' ∈ kpSquares boundary L (ancestorScale ⟨m, hm⟩ j) := by
      have h := C'.property.1.1 hs'C
      have : ancestorScale ⟨m, hm⟩ j = m' := by simp only [ancestorScale, hj]; omega
      rw [this]
      exact h
    have hPsupp : P ∩ chargeSupport ϱ = s ∩ chargeSupport ϱ :=
      separatedSquare_parent_inter_support_eq_patch boundary L ϱ ⟨m, hm⟩ j hL0 _ s hs hside
        (ancestorScaleSquare_diameter_lt_threshold boundary L hL ⟨m, hm⟩ j P hPsq)
    -- the support in `s'` is the patch of `s`
    have hs'supp : ∀ w ∈ s', ϱ w ≠ 0 → w ∈ s := by
      intro w hw hw0
      by_contra hws
      have hsep := pointwise_separation_of_separatedSquare boundary L ϱ ⟨m, hm⟩ _ s hs z₀ hz₀s
        w (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw0⟩, hws⟩)
      have hdiam := ancestorScaleSquare_diameter_lt_threshold boundary L hL ⟨m, hm⟩ j s' hs'sq
      have hle := latticeDistance_le_squareDiameter_real_of_mem boundary L s' z₀ w hz₀s' hw
      linarith
    -- minimality forces `s' = P`
    have hs'P : s' = P := by
      by_contra hne
      have hDcover : IsSquareCover boundary L m' ϱ (C'.val.erase s') := by
        refine ⟨fun t ht => C'.property.1.1 (Finset.mem_erase.mp ht).2, fun w hw => ?_⟩
        obtain ⟨t, ht, hwt⟩ := C'.property.1.2 w hw
        by_cases hts : t = s'
        · subst hts
          have hws := hs'supp w hwt (Finset.mem_filter.mp hw).2
          have hwP : w ∈ P := by
            have : w ∈ P ∩ chargeSupport ϱ := by
              rw [hPsupp]; exact Finset.mem_inter.mpr ⟨hws, hw⟩
            exact (Finset.mem_inter.mp this).1
          exact ⟨P, Finset.mem_erase.mpr ⟨fun h => hne h.symm, hPmem⟩, hwP⟩
        · exact ⟨t, Finset.mem_erase.mpr ⟨hts, ht⟩, hwt⟩
      have hmin := C'.property.2 _ hDcover
      rw [Finset.card_erase_of_mem hs'C] at hmin
      have hpos : 0 < C'.val.card := Finset.card_pos.mpr ⟨s', hs'C⟩
      omega
    -- the endpoint `x` lies in `P = s'`
    have hxP : x ∈ s' := by
      rw [hs'P]
      have hrad : 2 ^ (m - 1) ≤ ancestorRadius ⟨m, hm⟩ j := by
        unfold ancestorRadius
        have : 1 ≤ 2 ^ j.val - 1 := by
          have : 2 ≤ 2 ^ j.val := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ j.val := Nat.pow_le_pow_right (by norm_num) j.property.1
          omega
        calc 2 ^ (m - 1) = 1 * 2 ^ (m - 1) := (one_mul _).symm
          _ ≤ (2 ^ j.val - 1) * 2 ^ (m - 1) := Nat.mul_le_mul_right _ this
      have hball : ∃ y ∈ s, latticeDistance boundary L x y ≤ ancestorRadius ⟨m, hm⟩ j :=
        ⟨y, hy, by rw [hdist]; exact hxy.trans hrad⟩
      cases boundary with
      | free => exact free_graphBall_subset_ancestorParent L ⟨m, hm⟩ j hL0 hL s hsq hside x hball
      | periodic =>
        exact periodic_graphBall_subset_ancestorParent L ⟨m, hm⟩ j hL0 hL s hsq hside x hball
    have hone : 1 ≤ 2 ^ (m' - 3) := Nat.one_le_two_pow
    exact ⟨⟨x, hxP, by rw [SimpleGraph.dist_comm]; exact (hend x _ hx (Or.inl rfl)).trans hone⟩,
      ⟨x, hxP, by rw [SimpleGraph.dist_comm]; exact (hend x _ hx (Or.inr rfl)).trans hone⟩⟩
  · -- gaps `≥ 5`: the edge is within the plateau radius of the patch point
    have hplat : 2 ^ (m + 2) ≤ 2 ^ (m' - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
    have hnear : ∀ a, (a = Λ.src e ∨ a = Λ.tgt e) →
        Λ.toSimpleGraph.dist a z₀ ≤ 2 ^ (m' - 3) := by
      intro a ha
      have hax := hend a x ha hx
      have t1 := hΛ.dist_triangle (u := a) (v := x) (w := z₀)
      have t2 := hΛ.dist_triangle (u := x) (v := y) (w := z₀)
      have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    exact ⟨⟨z₀, hz₀s', hnear _ (Or.inl rfl)⟩, ⟨z₀, hz₀s', hnear _ (Or.inr rfl)⟩⟩

end CrossScale

/-! ## Proposition 2.4 on one domain -/

section Assembly

variable (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L) {E : Type} [Fintype E]
  (Λ : Multigraph (Fin L × Fin L) E)

omit [Fintype E] in
/-- Two support points are at most `d(ϱ)` apart. -/
theorem dist_le_densityDiameter_of_mem {ϱ : Fin L × Fin L → ℤ} {x y : Fin L × Fin L}
    (hx : ϱ x ≠ 0) (hy : ϱ y ≠ 0) : Λ.toSimpleGraph.dist x y ≤ Λ.densityDiameter ϱ := by
  have hmem : (x, y) ∈ (Finset.univ.filter fun j => ϱ j ≠ 0) ×ˢ
      (Finset.univ.filter fun j => ϱ j ≠ 0) := by simp [hx, hy]
  unfold Multigraph.densityDiameter
  exact Finset.le_sup (f := fun p : (Fin L × Fin L) × (Fin L × Fin L) =>
    Λ.toSimpleGraph.dist p.1 p.2) hmem

omit [Fintype E] in
include hL in
/-- : points within `2^{m-1} + 1` of a separated square of `ϱ` lie in `D(ϱ)`, because
`d(ϱ) > 32·2^m`. -/
theorem mem_densityDomain_of_near_separatedSquare
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (hΛ : Λ.toSimpleGraph.Connected) {ϱ : ChargeDensity L} {center : Fin L × Fin L}
    (hcenter : Λ.IsDensityCenter ϱ center) {m : ℕ} (hm : 1 ≤ m)
    {C : {C : Finset (Finset (Fin L × Fin L)) // IsMinimumSquareCover boundary L m ϱ C}}
    {s : Finset (Fin L × Fin L)} (hs : s ∈ separatedSquares boundary L ϱ ⟨m, hm⟩ C)
    {j y : Fin L × Fin L} (hy : y ∈ s) (hjy : Λ.toSimpleGraph.dist j y ≤ 2 ^ (m - 1) + 1) :
    j ∈ Λ.densityDomain ϱ center := by
  obtain ⟨z, hz⟩ := separatedSquare_patch_nonempty boundary L ϱ ⟨m, hm⟩ C s hs
  obtain ⟨hzs, hzsupp⟩ := Finset.mem_inter.mp hz
  have hz0 : ϱ z ≠ 0 := (Finset.mem_filter.mp hzsupp).2
  obtain ⟨x, hx0, hxs⟩ := P47.exists_support_not_mem_separatedSquare boundary hs
  have hfar : 32 * 2 ^ m < latticeDistance boundary L z x :=
    P47.thirtyTwo_mul_lt_latticeDistance boundary hs hzs hx0 hxs
  rw [hdist] at hfar
  have hdzx := dist_le_densityDiameter_of_mem Λ hz0 hx0
  have hdzc := dist_le_densityDiameter_of_mem Λ hz0 hcenter.1
  have hyz : Λ.toSimpleGraph.dist y z ≤ 2 * (2 ^ m - 1) := by
    rw [← hdist]
    exact P47.latticeDistance_le_of_mem_separatedSquare boundary hL hs hy hzs
  have t1 := hΛ.dist_triangle (u := j) (v := y) (w := center)
  have t2 := hΛ.dist_triangle (u := y) (v := z) (w := center)
  have hpm : 2 * 2 ^ (m - 1) = 2 ^ m := by rw [← pow_succ']; congr 1; omega
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  show Λ.toSimpleGraph.dist j center < 2 * Λ.densityDiameter ϱ
  generalize 2 ^ m = P at hfar hyz hpm h2m
  generalize 2 ^ (m - 1) = Q at hjy hpm
  omega

/-- The Theorem 2.2(b) input of Lemma 4.5 (`InitialWaveSeparation`): every point of `D(ϱ')`,
`ϱ' ∈ 𝒩₀(ϱ*)`, is at distance more than two from `supp ϱ*`, since
`2^16 (d(ϱ')/2)^{7/4} ≥ 16384 d(ϱ') > 2 d(ϱ') + 2`. -/
theorem initialWaveSeparation_of_scaleSeparated
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (hΛ : Λ.toSimpleGraph.Connected) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hN : IsScaleSeparated boundary L N) (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {ϱ : ChargeDensity L} (hϱ : ϱ ∈ neutralPart N) :
    InitialWaveSeparation Λ (neutralPart N) ϱ centerOf := by
  intro ϱ' hϱ' j hj k hk
  obtain ⟨hϱ'N₀, hscale, hne⟩ := Λ.mem_comparableDensities.mp hϱ'
  obtain ⟨hϱ'N, hϱ'n⟩ := mem_neutralPart.mp hϱ'N₀
  have hϱN := (mem_neutralPart.mp hϱ).1
  have hϱ'0 := hens.1 ϱ' hϱ'N
  have hc' := hcenter ϱ' hϱ'0
  have hbridge := IsScaleSeparated.half_le_densitySupportDistance boundary Λ hdist hN hϱ'N hϱN
    (Ne.symm hne) hscale
  have hle := SpinWaves.densitySupportDistance_le Λ ϱ' ϱ hc'.1 hk
  have hd1 := Λ.one_le_densityDiameter_of_neutral hΛ ϱ' hϱ'0 hϱ'n
  have hj' : Λ.toSimpleGraph.dist j (centerOf ϱ') < 2 * Λ.densityDiameter ϱ' := hj
  have t := hΛ.dist_triangle (u := centerOf ϱ') (v := j) (w := k)
  rw [SimpleGraph.dist_comm (u := centerOf ϱ') (v := j)] at t
  -- `2^16 (d/2)^{7/4} ≥ 16384 d`
  set d : ℝ := (Λ.densityDiameter ϱ' : ℝ) with hd
  have hd1R : (1 : ℝ) ≤ d := by rw [hd]; exact_mod_cast hd1
  have hpow : d / 4 ≤ (d / 2) ^ (7 / 4 : ℝ) := by
    rw [Real.div_rpow (by linarith) (by norm_num)]
    have h1 : d ≤ d ^ (7 / 4 : ℝ) := Real.self_le_rpow_of_one_le hd1R (by norm_num)
    have h2 : (2 : ℝ) ^ (7 / 4 : ℝ) ≤ 4 := by
      calc (2 : ℝ) ^ (7 / 4 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := by norm_num
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (7 / 4 : ℝ) := by positivity
    rw [le_div_iff₀ h2pos]
    nlinarith
  have hlow : (16384 : ℝ) * d ≤ SpinWaves.densitySupportDistance Λ ϱ' ϱ := by
    have : (2 ^ 16 : ℝ) * (d / 4) ≤ (2 ^ 16 : ℝ) * (d / 2) ^ (7 / 4 : ℝ) := by gcongr
    linarith
  have hleR : (SpinWaves.densitySupportDistance Λ ϱ' ϱ : ℝ) ≤
      Λ.toSimpleGraph.dist (centerOf ϱ') k := by exact_mod_cast hle
  have tR : (Λ.toSimpleGraph.dist (centerOf ϱ') k : ℝ) ≤
      Λ.toSimpleGraph.dist j (centerOf ϱ') + Λ.toSimpleGraph.dist j k := by exact_mod_cast t
  have hj'R : (Λ.toSimpleGraph.dist j (centerOf ϱ') : ℝ) + 1 ≤ 2 * d := by
    have : Λ.toSimpleGraph.dist j (centerOf ϱ') + 1 ≤ 2 * Λ.densityDiameter ϱ' := hj'
    rw [hd]; exact_mod_cast this
  have : (2 : ℝ) < Λ.toSimpleGraph.dist j k := by linarith
  exact_mod_cast this

include hL in
/-- KP Proposition 2.4 on one square domain from Proposition 4.7 on that domain (–,
 The cover selection is the shared  selector. -/
theorem p24Step_of_p47Step
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (hΛ : Λ.toSimpleGraph.Connected) (B : BipartiteDegreeFour Λ) {D₃ : ℝ}
    (h47 : P47Step boundary Λ D₃) : P24Step boundary Λ D₃ := by
  classical
  intro centerOf hcenter
  have hL0 : 0 < L := by omega
  refine ⟨fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k, ?_⟩
  intro β hβ N hens hNa hNb hNc ϱ hϱ
  obtain ⟨hϱN, hneutral⟩ := mem_neutralPart.mp hϱ
  have hϱ0 : ϱ ≠ 0 := hens.1 ϱ hϱN
  -- the separated squares, scale `k + 1` for `k < L`
  set sep : ℕ → Finset (Finset (Fin L × Fin L)) := fun k =>
    separatedSquares boundary L ϱ ⟨k + 1, by omega⟩
      (sharedMinimumSquareCover boundary L ϱ hL0 ⟨k + 1, by omega⟩) with hsep
  set T : Finset (Σ _ : ℕ, Finset (Fin L × Fin L)) := (Finset.range L).sigma sep with hT
  -- the square waves (Proposition 4.7)
  have hW : ∀ t ∈ T, ∃ w : Fin L × Fin L → ℝ, IsSquareWave Λ t.2 (t.1 + 1) w ∧
      (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) ϱ,
        ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), w j = c) ∧
      D₃ / β ≤ energyFunctional Λ β w ϱ := by
    intro t ht
    have ht2 : t.2 ∈ sep t.1 := (Finset.mem_sigma.mp ht).2
    obtain ⟨w, h1, ⟨c, h2⟩, h3, h4⟩ := h47 centerOf hcenter β hβ N hens hNa hNb hNc ϱ hϱ
      ⟨t.1 + 1, by omega⟩ (sharedMinimumSquareCover boundary L ϱ hL0 ⟨t.1 + 1, by omega⟩) t.2 ht2
    refine ⟨w, ⟨h1, c, fun j hj => h2 j ?_⟩, h3, h4⟩
    rw [ceil_two_zpow_sub_three]
    exact hj
  choose! w hw using hW
  -- the initial wave (Lemma 4.5)
  obtain ⟨a₀, ha₀supp, ha₀D, ha₀Δ, ha₀plus, ha₀E⟩ := exists_initialSpinWave_support Λ hΛ B
    (neutralPart N) ϱ (centerOf ϱ) centerOf β (hcenter ϱ hϱ0) hneutral hβ
    (initialWaveSeparation_of_scaleSeparated boundary Λ hdist hΛ hens hNb centerOf hcenter hϱ)
  -- the family
  set g : Option (Σ _ : ℕ, Finset (Fin L × Fin L)) → Fin L × Fin L → ℝ :=
    fun o => Option.elim o a₀ w with hg
  set F := T.insertNone with hF
  -- geometric facts for a member of `T`
  have hsepmem : ∀ t ∈ T, t.2 ∈ separatedSquares boundary L ϱ ⟨t.1 + 1, by omega⟩
      (sharedMinimumSquareCover boundary L ϱ hL0 ⟨t.1 + 1, by omega⟩) :=
    fun t ht => (Finset.mem_sigma.mp ht).2
  have hnearD : ∀ t ∈ T, ∀ j y, y ∈ t.2 → Λ.toSimpleGraph.dist j y ≤ 2 ^ t.1 + 1 →
      j ∈ Λ.densityDomain ϱ (centerOf ϱ) := by
    intro t ht j y hy hjy
    exact mem_densityDomain_of_near_separatedSquare boundary hL Λ hdist hΛ (hcenter ϱ hϱ0)
      (by omega) (hsepmem t ht) hy (by simpa using hjy)
  refine ⟨fun v => ∑ o ∈ F, g o v, ?_, ?_, ?_, ?_⟩
  · -- clause (1): constant on every `D⁺(ϱ')`
    intro ϱ' hϱ'
    have hc : ∀ o ∈ F, ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), g o j = c := by
      intro o ho
      rcases o with _ | t
      · exact ⟨0, fun j hj => ha₀plus ϱ' hϱ' j hj⟩
      · exact (hw t (Finset.some_mem_insertNone.mp ho)).2.1 ϱ' hϱ'
    choose! cs hcs using hc
    exact ⟨∑ o ∈ F, cs o, fun j hj => Finset.sum_congr rfl fun o ho => hcs o ho j hj⟩
  · -- clause (2): `supp a ⊆ D(ϱ)`
    intro j hj
    obtain ⟨o, ho, hoj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
    rcases o with _ | t
    · exact ha₀D j hoj
    · have ht := Finset.some_mem_insertNone.mp ho
      obtain ⟨y, hy, hjy⟩ := (hw t ht).1.supp j hoj
      exact hnearD t ht j y hy (by simpa using Nat.le_succ_of_le hjy)
  · -- clause (3): `supp Δa ⊆ D(ϱ)`
    intro j hj
    have hj' : ∑ o ∈ F, Λ.laplacian (g o) j ≠ 0 := by
      rwa [← laplacian_finset_sum Λ F g j]
    obtain ⟨o, ho, hoj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
    rcases o with _ | t
    · exact ha₀Δ j hoj
    · have ht := Finset.some_mem_insertNone.mp ho
      rcases laplacian_ne_zero_has_neighbor Λ (w t) j hoj with h0 | ⟨k, hk, hadj⟩
      · obtain ⟨y, hy, hjy⟩ := (hw t ht).1.supp j h0
        exact hnearD t ht j y hy (by simpa using Nat.le_succ_of_le hjy)
      · obtain ⟨y, hy, hky⟩ := (hw t ht).1.supp k hk
        have hjk : Λ.toSimpleGraph.dist j k = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (adj_toSimpleGraph Λ hadj)
        have tri := hΛ.dist_triangle (u := j) (v := k) (w := y)
        exact hnearD t ht j y hy (by simp only [Nat.add_sub_cancel] at hky; omega)
  · -- clause (4): energy additivity and the gains
    have hdisj : ∀ e, ∀ o ∈ F, ∀ o' ∈ F, o ≠ o' →
        Λ.grad (g o) e = 0 ∨ Λ.grad (g o') e = 0 := by
      -- base/square far-support fact
      have hbasefar : ∀ t ∈ T, ∀ x, ϱ x ≠ 0 → x ∉ t.2 → ∀ y ∈ t.2,
          2 ^ (t.1 + 1 - 1) + 1 < Λ.toSimpleGraph.dist x y := by
        intro t ht x hx hxs y hy
        have h : 32 * 2 ^ (t.1 + 1) < latticeDistance boundary L y x :=
          P47.thirtyTwo_mul_lt_latticeDistance boundary (hsepmem t ht) hy hx hxs
        rw [hdist, SimpleGraph.dist_comm] at h
        simp only [Nat.add_sub_cancel]
        have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
        omega
      have hbase : ∀ e, ∀ t ∈ T, Λ.grad a₀ e = 0 ∨ Λ.grad (w t) e = 0 := fun e t ht =>
        IsSquareWave.grad_disjoint_base Λ hΛ (hw t ht).1 ha₀supp (hbasefar t ht) e
      -- two squares
      have hpair : ∀ e, ∀ t ∈ T, ∀ t' ∈ T, t.1 < t'.1 →
          Λ.grad (w t) e = 0 ∨ Λ.grad (w t') e = 0 := by
        intro e t ht t' ht' hlt
        by_contra hc
        push Not at hc
        obtain ⟨x, hx, hwx⟩ : ∃ x, (x = Λ.src e ∨ x = Λ.tgt e) ∧ w t x ≠ 0 := by
          rcases ne_zero_of_grad_ne_zero Λ (w t) e hc.1 with h | h
          · exact ⟨_, Or.inl rfl, h⟩
          · exact ⟨_, Or.inr rfl, h⟩
        obtain ⟨x', hx', hwx'⟩ : ∃ x', (x' = Λ.src e ∨ x' = Λ.tgt e) ∧ w t' x' ≠ 0 := by
          rcases ne_zero_of_grad_ne_zero Λ (w t') e hc.2 with h | h
          · exact ⟨_, Or.inl rfl, h⟩
          · exact ⟨_, Or.inr rfl, h⟩
        obtain ⟨y, hy, hxy⟩ := (hw t ht).1.supp x hwx
        obtain ⟨y', hy', hxy'⟩ := (hw t' ht').1.supp x' hwx'
        obtain ⟨hsrc, htgt⟩ := cross_scale_endpoints_near boundary hL Λ hdist hΛ ϱ
          (by omega : 1 ≤ t.1 + 1) (by omega : t.1 + 1 < t'.1 + 1) (hsepmem t ht)
          (hsepmem t' ht') e hx hx' hy hxy hy' hxy'
        exact hc.2 ((hw t' ht').1.grad_eq_zero Λ e hsrc htgt)
      intro e o ho o' ho' hoo'
      rcases o with _ | t <;> rcases o' with _ | t'
      · exact absurd rfl hoo'
      · exact hbase e t' (Finset.some_mem_insertNone.mp ho')
      · exact (hbase e t (Finset.some_mem_insertNone.mp ho)).symm
      · have ht := Finset.some_mem_insertNone.mp ho
        have ht' := Finset.some_mem_insertNone.mp ho'
        have htt' : t ≠ t' := fun h => hoo' (h ▸ rfl)
        rcases lt_trichotomy t.1 t'.1 with hlt | heq | hgt
        · exact hpair e t ht t' ht' hlt
        · -- the same scale: distinct separated squares of one cover are far apart
          have hs2 : t.2 ≠ t'.2 := fun h => htt' (Sigma.ext heq (heq_of_eq h))
          refine IsSquareWave.grad_disjoint_of_far Λ hΛ (hw t ht).1 (hw t' ht').1 ?_ e
          intro y hy y' hy'
          have hsC : t'.2 ∈ (sharedMinimumSquareCover boundary L ϱ hL0
              ⟨t.1 + 1, by omega⟩).val := by
            have := (Finset.mem_filter.mp (hsepmem t' ht')).1
            rwa [show (⟨t'.1 + 1, by omega⟩ : {k : ℕ // 1 ≤ k}) = ⟨t.1 + 1, by omega⟩ from
              Subtype.ext (by simp [heq])] at this
          have h32' : 32 * 2 ^ (t.1 + 1) < Λ.toSimpleGraph.dist y y' := by
            rw [← hdist]
            exact P47.thirtyTwo_mul_lt_latticeDistance_of_mem_cover boundary (hsepmem t ht) hsC
              (Ne.symm hs2) hy hy'
          simp only [Nat.add_sub_cancel]
          rw [← heq]
          have : 2 ^ t.1 ≤ 2 ^ (t.1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
          omega
        · exact (hpair e t' ht' t ht hgt).symm
    have hE : energyFunctional Λ β (fun v => ∑ o ∈ F, g o v) ϱ =
        ∑ o ∈ F, energyFunctional Λ β (g o) ϱ := by
      unfold energyFunctional
      rw [pairing_finset_sum, energy_finset_sum_of_disjoint Λ F g hdisj, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
    rw [hE, hF, Finset.sum_insertNone]
    have hsum : ∑ t ∈ T, energyFunctional Λ β (g (some t)) ϱ ≥ ∑ _t ∈ T, D₃ / β :=
      Finset.sum_le_sum fun t ht => (hw t ht).2.2
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard : (T.card : ℝ) = (separatedSquareTotal boundary L
        (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) ϱ : ℝ) := by
      rw [hT, Finset.card_sigma]
      rfl
    have h0 : energyFunctional Λ β (g none) ϱ = energyFunctional Λ β a₀ ϱ := rfl
    rw [h0]
    rw [hcard] at hsum
    have : 1 / β * (1 / 16 * ∑ j, (ϱ j : ℝ) ^ 2 +
        D₃ * (separatedSquareTotal boundary L
          (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) ϱ : ℝ)) =
        (1 / 16 : ℝ) / β * (∑ j, (ϱ j : ℝ) ^ 2) +
          (separatedSquareTotal boundary L
            (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) ϱ : ℝ) * (D₃ / β) := by
      field_simp
    rw [this]
    linarith

end Assembly

/-- **KP Proposition 2.4 from KP Lemma 4.6** (KP §4.3, pp. 23–28): `p24Statement` follows from
`l46Statement`, through Proposition 4.7 (`P47.p47_of_l46`) and the assembly above. -/
theorem p24_of_l46 : l46Statement → p24Statement := by
  intro h46
  obtain ⟨D₃, hD₃, h47⟩ := P47.p47_of_l46 h46
  refine ⟨D₃, hD₃, fun L hL => ⟨?_, fun hEven => ?_⟩⟩
  · exact p24Step_of_p47Step .free hL (squareFree L) (fun _ _ => rfl) (squareFree_connected L hL)
      (squareFreeBipartiteDegreeFour L hL) (h47 L hL).1
  · exact p24Step_of_p47Step .periodic hL (squarePeriodic L) (fun _ _ => rfl)
      (squarePeriodic_connected L hL) (squarePeriodicBipartiteDegreeFour L hEven hL)
      ((h47 L hL).2 hEven)

end FroehlichSpencer.BKT.Reduction

end
