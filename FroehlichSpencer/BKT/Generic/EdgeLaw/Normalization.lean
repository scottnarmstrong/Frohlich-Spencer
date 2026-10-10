/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Defs
public import FroehlichSpencer.BKT.Generic.EdgeLaw.Shear
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Normalization of the rooted edge law (generic core)

For a strip weight `w` on a finite connected multigraph, the rooted edge law `edgeLaw G w v` is a
probability measure (`isProbabilityMeasure_edgeLaw`): its density
`∏_e w(∇φ(e)) · 𝟙_{[-π, π)}(φ(v))` has positive finite mass.

* **Positivity.** The density is positive wherever `φ(v) ∈ (-π, π)`, a set of positive volume.
* **Finiteness.** Every vertex `u ≠ v` has a parent `p(u)`, adjacent and strictly closer to `v`,
  joined to `u` by a multigraph edge `e(u)`; the edges `e(u)` are distinct.

Bounding the factors of
  the tree edges by the majorant `B` of the weight and the others by its bound `M` gives
  `density(φ) ≤ M^{|E|} 𝟙(φ(v)) ∏_{u ≠ v} B(φ(u) - φ(p(u)))`.

The increment map
  `φ ↦ (φ(v), (φ(u) - φ(p(u)))_{u ≠ v})` is a composition of shears taken in order of decreasing
  distance to `v` (`incrementMap_apply`), so it preserves Lebesgue measure
  (`measurePreserving_incrementMap`), and the bound becomes a product of one-variable integrable
  functions.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory

/-! ## Increment maps -/

section Increment

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One increment step `φ ↦ φ - φ(p(u)) δ_u`, a shear. -/
def incrementStep (p : V → V) (u : V) : (V → ℝ) → (V → ℝ) :=
  shear (p u) (-Pi.single u 1)

/-- The composite of the increment steps along a list, the head applied first. -/
def incrementMap (p : V → V) : List V → (V → ℝ) → (V → ℝ)
  | [] => id
  | u :: L => incrementMap p L ∘ incrementStep p u

omit [Fintype V] in
theorem incrementStep_apply (p : V → V) (u : V) (φ : V → ℝ) (x : V) :
    incrementStep p u φ x = if x = u then φ u - φ (p u) else φ x := by
  unfold incrementStep
  rw [shear_apply_apply]
  by_cases hx : x = u
  · subst hx; simp only [Pi.neg_apply, Pi.single_eq_same, ite_true]; ring
  · simp only [Pi.neg_apply, Pi.single_eq_of_ne hx, neg_zero, mul_zero, add_zero, hx, ite_false]

/-- An increment map preserves Lebesgue measure. -/
theorem measurePreserving_incrementMap (p : V → V) :
    ∀ L : List V, (∀ u ∈ L, p u ≠ u) →
      MeasurePreserving (incrementMap p L) (volume : Measure (V → ℝ)) volume
  | [], _ => MeasurePreserving.id _
  | u :: L, hp => by
    have hu : (-Pi.single u (1 : ℝ) : V → ℝ) (p u) = 0 := by
      rw [Pi.neg_apply, Pi.single_eq_of_ne (hp u List.mem_cons_self), neg_zero]
    exact (measurePreserving_incrementMap p L fun x hx => hp x (List.mem_cons_of_mem u hx)).comp
      (measurePreserving_shear hu)

omit [Fintype V] in
/-- Along a duplicate-free list in which no parent occurs before its child, the increment map
replaces the listed coordinates by their increments. -/
theorem incrementMap_apply (p : V → V) :
    ∀ L : List V, L.Nodup → L.Pairwise (fun a b => p b ≠ a) → ∀ (φ : V → ℝ) (x : V),
      incrementMap p L φ x = if x ∈ L then φ x - φ (p x) else φ x
  | [], _, _, φ, x => by simp [incrementMap]
  | u :: L, hnd, hpw, φ, x => by
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have ih := incrementMap_apply p L hnd.2 hpw.2 (incrementStep p u φ) x
    simp only [incrementMap, Function.comp_apply]
    rw [ih]
    by_cases hxL : x ∈ L
    · have hxu : x ≠ u := fun h => hnd.1 (h ▸ hxL)
      have hpx : p x ≠ u := hpw.1 x hxL
      rw [ite_eq_left hxL, ite_eq_left (List.mem_cons_of_mem u hxL), incrementStep_apply,
        incrementStep_apply, ite_eq_right hxu, ite_eq_right hpx]
    · rw [ite_eq_right hxL, incrementStep_apply]
      by_cases hxu : x = u
      · subst hxu; rw [ite_eq_left rfl, ite_eq_left List.mem_cons_self]
      · rw [ite_eq_right hxu, ite_eq_right]
        rw [List.mem_cons]
        rintro (h | h)
        · exact hxu h
        · exact hxL h

end Increment

/-! ## Parents and tree edges -/

section Tree

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

omit [Fintype V] [DecidableEq V] in
/-- In a connected graph every vertex other than `v` has a neighbour strictly closer to `v`. -/
theorem exists_parent {H : SimpleGraph V} (hH : H.Connected) (v u : V) (hu : u ≠ v) :
    ∃ x, H.Adj u x ∧ H.dist x v < H.dist u v := by
  obtain ⟨w, hw⟩ := hH.exists_walk_length_eq_dist u v
  cases w with
  | nil => exact absurd rfl hu
  | cons h w' =>
    refine ⟨_, h, ?_⟩
    have := SimpleGraph.dist_le w'
    rw [SimpleGraph.Walk.length_cons] at hw
    omega

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- An edge of the underlying simple graph is carried by a multigraph edge. -/
theorem exists_edge_of_adj (G : Multigraph V E) {u x : V} (h : G.toSimpleGraph.Adj u x) :
    ∃ e, (G.src e = u ∧ G.tgt e = x) ∨ (G.src e = x ∧ G.tgt e = u) := by
  rw [Multigraph.toSimpleGraph_eq_fromRel_adj, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨e, he⟩ | ⟨e, he⟩
  · exact ⟨e, he⟩
  · exact ⟨e, he.symm⟩

end Tree

/-! ## Normalization -/

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

omit [DecidableEq V] in
/-- The rooted density has positive mass. -/
theorem densityMass_edgeDensity_ne_zero (G : Multigraph V E) {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight w W c) (v : V) : densityMass (edgeDensity G w v) ≠ 0 := by
  classical
  intro h0
  have hmeas : Measurable fun φ => ENNReal.ofReal (edgeDensity G w v φ) :=
    (measurable_edgeDensity G hw v).ennreal_ofReal
  rw [densityMass, lintegral_eq_zero_iff hmeas, Filter.EventuallyEq, ae_iff] at h0
  set S : Set (V → ℝ) := Set.univ.pi fun j => if j = v then Set.Ioo (-Real.pi) Real.pi else Set.univ
  have hS : S ⊆ {φ | ¬ ENNReal.ofReal (edgeDensity G w v φ) = (0 : (V → ℝ) → ENNReal) φ} := by
    intro φ hφ
    have hv : φ v ∈ Set.Ioo (-Real.pi) Real.pi := by
      have := hφ v (Set.mem_univ v)
      simpa using this
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
    unfold edgeDensity
    rw [Set.indicator_of_mem (Set.Ioo_subset_Ico_self hv), Pi.one_apply, mul_one]
    exact Finset.prod_pos fun e _ => hw.ofReal_re_pos _
  have hSpos : volume S ≠ 0 := by
    rw [volume_pi_pi]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    by_cases hj : j = v
    · rw [ite_eq_left hj, Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])).ne'
    · rw [ite_eq_right hj, Real.volume_univ]
      exact ENNReal.top_ne_zero
  exact hSpos (measure_mono_null hS h0)

/-- The rooted density is integrable on a connected multigraph. -/
theorem integrable_edgeDensity (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) (v : V) :
    Integrable (edgeDensity G w v) := by
  classical
  -- the weight bounds
  obtain ⟨M, -, hM⟩ := hw.exists_re_le
  obtain ⟨B, hBint, -, hB⟩ := hw.majorant
  have hW0 : |(0 : ℝ)| ≤ W := by rw [abs_zero]; exact hw.width_nonneg
  have hBx : ∀ x : ℝ, ‖w x‖ ≤ B x := fun x => by
    have := hB x 0 hW0
    rwa [Complex.ofReal_zero, zero_mul, add_zero] at this
  have hre : ∀ x : ℝ, (w x).re ≤ B x := fun x => (Complex.re_le_norm _).trans (hBx x)
  have heven : ∀ x : ℝ, w ((-x : ℝ) : ℂ) = w x := fun x => by
    rw [Complex.ofReal_neg]
    exact hw.even _ (by simpa using hw.width_nonneg)
  have hpos : ∀ x : ℝ, 0 ≤ (w x).re := fun x => (hw.ofReal_re_pos x).le
  set M' : ℝ := max M 1 with hM'
  have hM'1 : 1 ≤ M' := le_max_right _ _
  have hMM' : ∀ x : ℝ, (w x).re ≤ M' := fun x => (hM x).trans (le_max_left _ _)
  -- distances, parents and tree edges
  set d : V → ℕ := fun x => G.toSimpleGraph.dist x v with hd
  have hpar : ∀ u, ∃ x, u ≠ v → G.toSimpleGraph.Adj u x ∧ d x < d u := by
    intro u
    by_cases hu : u = v
    · exact ⟨v, fun h => absurd hu h⟩
    · obtain ⟨x, hx⟩ := exists_parent hG v u hu
      exact ⟨x, fun _ => hx⟩
  choose p hp using hpar
  have hedge : ∀ u : {u // u ≠ v}, ∃ e,
      (G.src e = u ∧ G.tgt e = p u) ∨ (G.src e = p u ∧ G.tgt e = u) :=
    fun u => exists_edge_of_adj G (hp u u.2).1
  choose eOf heOf using hedge
  have hinj : Function.Injective eOf := by
    intro u u' h
    have h1 := heOf u
    have h2 := heOf u'
    rw [h] at h1
    have hdu := (hp u u.2).2
    have hdu' := (hp u' u'.2).2
    apply Subtype.ext
    rcases h1 with ⟨h1s, h1t⟩ | ⟨h1s, h1t⟩ <;> rcases h2 with ⟨h2s, h2t⟩ | ⟨h2s, h2t⟩
    · exact h1s.symm.trans h2s
    · exfalso
      rw [h1s] at h2s; rw [h1t] at h2t
      rw [← h2s] at hdu'; rw [h2t] at hdu
      omega
    · exfalso
      rw [h1s] at h2s; rw [h1t] at h2t
      rw [h2s] at hdu; rw [← h2t] at hdu'
      omega
    · exact h1t.symm.trans h2t
  -- the tree-edge bound
  have htree : ∀ φ : V → ℝ, (∏ e, (w ((G.grad φ e : ℝ) : ℂ)).re) ≤
      (∏ u : {u // u ≠ v}, B (φ u - φ (p u))) * M' ^ Fintype.card E := by
    intro φ
    set f : E → ℝ := fun e => (w ((G.grad φ e : ℝ) : ℂ)).re with hf
    set S : Finset E := Finset.univ.image eOf with hS
    have hf0 : ∀ e, 0 ≤ f e := fun e => hpos _
    rw [← Finset.prod_mul_prod_compl S f]
    have hS1 : ∏ e ∈ S, f e ≤ ∏ u : {u // u ≠ v}, B (φ u - φ (p u)) := by
      rw [hS, Finset.prod_image fun x _ y _ h => hinj h]
      refine Finset.prod_le_prod₀ (fun u _ => hf0 _) fun u _ => ?_
      simp only [hf, Multigraph.grad]
      rcases heOf u with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rw [hs, ht]; exact hre _
      · rw [hs, ht, show φ (p u) - φ u = -(φ u - φ (p u)) by ring, heven]
        exact hre _
    have hS2 : ∏ e ∈ Sᶜ, f e ≤ M' ^ Fintype.card E := by
      calc ∏ e ∈ Sᶜ, f e ≤ ∏ _e ∈ Sᶜ, M' :=
            Finset.prod_le_prod₀ (fun e _ => hf0 e) fun e _ => hMM' _
        _ = M' ^ Sᶜ.card := Finset.prod_const _
        _ ≤ M' ^ Fintype.card E := pow_le_pow_right₀ hM'1 (Finset.card_le_univ _)
    exact mul_le_mul hS1 hS2 (Finset.prod_nonneg fun e _ => hf0 e)
      (Finset.prod_nonneg fun u _ => (norm_nonneg _).trans (hBx _))
  -- the non-root vertices in order of decreasing distance to `v`
  set L : List V := ((Finset.univ.erase v).toList).mergeSort (fun a b => decide (d b ≤ d a))
    with hL
  have hLmem : ∀ x, x ∈ L ↔ x ≠ v := by
    intro x
    rw [hL, List.mem_mergeSort, Finset.mem_toList, Finset.mem_erase]
    exact and_iff_left (Finset.mem_univ x)
  have hLnd : L.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  have hLsorted : L.Pairwise (fun a b => decide (d b ≤ d a) = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
  have hLpw : L.Pairwise (fun a b => p b ≠ a) := by
    refine List.Pairwise.imp_of_mem (fun {a b} _ hb hab hpb => ?_) hLsorted
    have hbv : b ≠ v := (hLmem b).mp hb
    have hlt := (hp b hbv).2
    simp only [decide_eq_true_eq] at hab
    rw [hpb] at hlt
    omega
  have hLp : ∀ u ∈ L, p u ≠ u := fun u hu => ((hp u ((hLmem u).mp hu)).1).ne.symm
  have hT := measurePreserving_incrementMap p L hLp
  have hTapp := incrementMap_apply p L hLnd hLpw
  -- the dominating function
  set h : V → ℝ → ℝ := fun x => if x = v then (Set.Ico (-Real.pi) Real.pi).indicator 1 else B
    with hh
  have hhint : ∀ x, Integrable (h x) := by
    intro x
    by_cases hx : x = v
    · simp only [hh, hx, ite_true]
      exact (integrableOn_const (C := (1 : ℝ)) measure_Ico_lt_top.ne).integrable_indicator
        measurableSet_Ico
    · simp only [hh, hx, ite_false]
      exact hBint
  set g : (V → ℝ) → ℝ := fun y => M' ^ Fintype.card E * ∏ x, h x (y x) with hg
  have hgint : Integrable g := by
    have := Integrable.fintype_prod (μ := fun _ : V => (volume : Measure ℝ)) hhint
    rw [← volume_pi] at this
    exact this.const_mul _
  have hgT : Integrable (g ∘ incrementMap p L) := (hT.integrable_comp hgint.aestronglyMeasurable).mpr hgint
  refine hgT.mono' (measurable_edgeDensity G hw v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (edgeDensity_nonneg G hw v φ)]
  have hgφ : (g ∘ incrementMap p L) φ = M' ^ Fintype.card E *
      ((Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) * ∏ u : {u // u ≠ v}, B (φ u - φ (p u))) := by
    simp only [Function.comp_apply, hg]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
    congr 1
    · rw [hTapp, ite_eq_right fun h => (hLmem v).mp h rfl]
      simp only [hh, ite_true]
    · rw [Finset.prod_subtype (p := fun x => x ≠ v) (Finset.univ.erase v)
        (fun x => by simp [Finset.mem_erase])]
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [hTapp, ite_eq_left ((hLmem u).mpr u.2)]
      simp only [hh, u.2, ite_false]
  rw [hgφ]
  have hind : 0 ≤ (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) (φ v) := by
    by_cases hv : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hv]
  unfold edgeDensity
  calc (∏ e, (w ((G.grad φ e : ℝ) : ℂ)).re) * (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v)
      ≤ ((∏ u : {u // u ≠ v}, B (φ u - φ (p u))) * M' ^ Fintype.card E) *
          (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) :=
        mul_le_mul_of_nonneg_right (htree φ) hind
    _ = M' ^ Fintype.card E * ((Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
          ∏ u : {u // u ≠ v}, B (φ u - φ (p u))) := by ring

/-- The rooted density has finite mass on a connected multigraph. -/
theorem densityMass_edgeDensity_ne_top (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) (v : V) :
    densityMass (edgeDensity G w v) ≠ ⊤ :=
  (integrable_edgeDensity G hG hw v).lintegral_lt_top.ne

/-- **Normalization.** On a finite connected multigraph, the rooted edge law of a strip weight is a
probability measure. -/
theorem isProbabilityMeasure_edgeLaw (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) (v : V) :
    IsProbabilityMeasure (edgeLaw G w v) := by
  rw [edgeLaw_eq_densityLaw]
  exact isProbabilityMeasure_densityLaw (densityMass_edgeDensity_ne_zero G hw v)
    (densityMass_edgeDensity_ne_top G hG hw v)

end FroehlichSpencer.BKT.Generic

end
