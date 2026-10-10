/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Renormalization.Assembly

/-!
# The rooted edge law with real edge offsets (generic core)

This module supplies the corresponding law for the generic core:
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Reduction (gffCharacter)
open FroehlichSpencer.BKT.Rotator.Contour (glue glue_self glue_of_ne
  integral_eq_integral_integral_glue)
open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-! ## The offset density and its law -/

/-- The rooted density with real edge offsets: `∏_e w(∇φ(e) + θ(e)) · 𝟙_{[-π,π)}(φ(v))`. -/
def offsetEdgeDensity (G : Multigraph V E) (w : ℂ → ℂ) (θ : E → ℝ) (v : V) (φ : V → ℝ) : ℝ :=
  (∏ e, (w ((G.grad φ e + θ e : ℝ) : ℂ)).re) * (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v)

/-- The rooted law with real edge offsets `θ`. -/
def offsetEdgeLaw (G : Multigraph V E) (w : ℂ → ℂ) (θ : E → ℝ) (v : V) : Measure (V → ℝ) :=
  densityLaw (offsetEdgeDensity G w θ v)

instance isFiniteMeasure_offsetEdgeLaw (G : Multigraph V E) (w : ℂ → ℂ) (θ : E → ℝ) (v : V) :
    IsFiniteMeasure (offsetEdgeLaw G w θ v) :=
  isFiniteMeasure_densityLaw _

omit [Fintype V] [DecidableEq V] in
theorem offsetEdgeDensity_zero (G : Multigraph V E) (w : ℂ → ℂ) (v : V) :
    offsetEdgeDensity G w 0 v = edgeDensity G w v := by
  funext φ
  simp only [offsetEdgeDensity, edgeDensity, Pi.zero_apply, add_zero]

omit [DecidableEq V] in
theorem offsetEdgeLaw_zero (G : Multigraph V E) (w : ℂ → ℂ) (v : V) :
    offsetEdgeLaw G w 0 v = edgeLaw G w v := by
  rw [offsetEdgeLaw, offsetEdgeDensity_zero, edgeLaw_eq_densityLaw]

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

omit [Fintype V] [DecidableEq V] in
theorem offsetEdgeDensity_nonneg (G : Multigraph V E) (hw : IsStripWeight w W c) (θ : E → ℝ)
    (v : V) (φ : V → ℝ) : 0 ≤ offsetEdgeDensity G w θ v φ := by
  unfold offsetEdgeDensity
  refine mul_nonneg (Finset.prod_nonneg fun e _ => (hw.ofReal_re_pos _).le) ?_
  by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [h]

omit [DecidableEq V] in
theorem measurable_offsetEdgeDensity (G : Multigraph V E) (hw : IsStripWeight w W c)
    (θ : E → ℝ) (v : V) : Measurable (offsetEdgeDensity G w θ v) := by
  unfold offsetEdgeDensity
  refine Measurable.mul ?_ ?_
  · refine (continuous_finsetProd _ fun e _ => ?_).measurable
    have hg : Continuous fun φ : V → ℝ => G.grad φ e + θ e := by
      unfold Multigraph.grad; fun_prop
    exact Complex.continuous_re.comp (hw.continuous_ofReal.comp hg)
  · exact (measurable_const.indicator measurableSet_Ico).comp (measurable_pi_apply v)

omit [DecidableEq V] in
/-- The offset density has positive mass. -/
theorem densityMass_offsetEdgeDensity_ne_zero (G : Multigraph V E) (hw : IsStripWeight w W c)
    (θ : E → ℝ) (v : V) : densityMass (offsetEdgeDensity G w θ v) ≠ 0 := by
  classical
  intro h0
  have hmeas : Measurable fun φ => ENNReal.ofReal (offsetEdgeDensity G w θ v φ) :=
    (measurable_offsetEdgeDensity G hw θ v).ennreal_ofReal
  rw [densityMass, lintegral_eq_zero_iff hmeas, Filter.EventuallyEq, ae_iff] at h0
  set S : Set (V → ℝ) :=
    Set.univ.pi fun j => if j = v then Set.Ioo (-Real.pi) Real.pi else Set.univ
  have hS : S ⊆ {φ | ¬ ENNReal.ofReal (offsetEdgeDensity G w θ v φ) =
      (0 : (V → ℝ) → ENNReal) φ} := by
    intro φ hφ
    have hv : φ v ∈ Set.Ioo (-Real.pi) Real.pi := by
      have := hφ v (Set.mem_univ v)
      simpa using this
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
    unfold offsetEdgeDensity
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

/-- The offset density is integrable on a connected multigraph: the parent-tree increments of
`integrable_edgeDensity`, with each tree factor translated by its offset. -/
theorem integrable_offsetEdgeDensity (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V) : Integrable (offsetEdgeDensity G w θ v) := by
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
  -- the signed offset of the tree edge of `u`
  set t : {u // u ≠ v} → ℝ := fun u =>
    if G.src (eOf u) = (u : V) then θ (eOf u) else -θ (eOf u) with ht
  -- the tree-edge bound
  have htree : ∀ φ : V → ℝ, (∏ e, (w ((G.grad φ e + θ e : ℝ) : ℂ)).re) ≤
      (∏ u : {u // u ≠ v}, B (φ u - φ (p u) + t u)) * M' ^ Fintype.card E := by
    intro φ
    set f : E → ℝ := fun e => (w ((G.grad φ e + θ e : ℝ) : ℂ)).re with hf
    set S : Finset E := Finset.univ.image eOf with hS
    have hf0 : ∀ e, 0 ≤ f e := fun e => hpos _
    rw [← Finset.prod_mul_prod_compl S f]
    have hS1 : ∏ e ∈ S, f e ≤ ∏ u : {u // u ≠ v}, B (φ u - φ (p u) + t u) := by
      rw [hS, Finset.prod_image fun x _ y _ h => hinj h]
      refine Finset.prod_le_prod₀ (fun u _ => hf0 _) fun u _ => ?_
      simp only [hf, Multigraph.grad]
      rcases heOf u with ⟨hs, htg⟩ | ⟨hs, htg⟩
      · have htu : t u = θ (eOf u) := by simp only [ht, hs, ite_true]
        rw [hs, htg, htu]; exact hre _
      · have hne : p u ≠ (u : V) := ((hp u u.2).1).ne.symm
        have htu : t u = -θ (eOf u) := by
          simp only [ht]; rw [hs, ite_eq_right hne]
        rw [hs, htg, htu, show φ (p u) - φ u + θ (eOf u) =
          -(φ u - φ (p u) + -θ (eOf u)) by ring, heven]
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
  set h : V → ℝ → ℝ := fun x =>
    if hx : x = v then (Set.Ico (-Real.pi) Real.pi).indicator 1 else fun y => B (y + t ⟨x, hx⟩)
    with hh
  have hhint : ∀ x, Integrable (h x) := by
    intro x
    by_cases hx : x = v
    · simp only [hh, hx, dite_true]
      exact (integrableOn_const (C := (1 : ℝ)) measure_Ico_lt_top.ne).integrable_indicator
        measurableSet_Ico
    · simp only [hh, hx, dite_false]
      exact hBint.comp_add_right _
  set g : (V → ℝ) → ℝ := fun y => M' ^ Fintype.card E * ∏ x, h x (y x) with hg
  have hgint : Integrable g := by
    have := Integrable.fintype_prod (μ := fun _ : V => (volume : Measure ℝ)) hhint
    rw [← volume_pi] at this
    exact this.const_mul _
  have hgT : Integrable (g ∘ incrementMap p L) :=
    (hT.integrable_comp hgint.aestronglyMeasurable).mpr hgint
  refine hgT.mono' (measurable_offsetEdgeDensity G hw θ v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (offsetEdgeDensity_nonneg G hw θ v φ)]
  have hgφ : (g ∘ incrementMap p L) φ = M' ^ Fintype.card E *
      ((Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
        ∏ u : {u // u ≠ v}, B (φ u - φ (p u) + t u)) := by
    simp only [Function.comp_apply, hg]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
    congr 1
    · rw [hTapp, ite_eq_right fun h => (hLmem v).mp h rfl]
      simp only [hh, dite_true]
    · rw [Finset.prod_subtype (p := fun x => x ≠ v) (Finset.univ.erase v)
        (fun x => by simp [Finset.mem_erase])]
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [hTapp, ite_eq_left ((hLmem u).mpr u.2)]
      simp only [hh, u.2, dite_false]
  rw [hgφ]
  have hind : 0 ≤ (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) (φ v) := by
    by_cases hv : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hv]
  unfold offsetEdgeDensity
  calc (∏ e, (w ((G.grad φ e + θ e : ℝ) : ℂ)).re) *
        (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v)
      ≤ ((∏ u : {u // u ≠ v}, B (φ u - φ (p u) + t u)) * M' ^ Fintype.card E) *
          (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) :=
        mul_le_mul_of_nonneg_right (htree φ) hind
    _ = M' ^ Fintype.card E * ((Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
          ∏ u : {u // u ≠ v}, B (φ u - φ (p u) + t u)) := by ring

/-- The offset density has finite mass on a connected multigraph. -/
theorem densityMass_offsetEdgeDensity_ne_top (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V) :
    densityMass (offsetEdgeDensity G w θ v) ≠ ⊤ :=
  (integrable_offsetEdgeDensity G hG hw θ v).lintegral_lt_top.ne

/-- **Normalization** of the offset law on a connected multigraph. -/
theorem isProbabilityMeasure_offsetEdgeLaw (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V) :
    IsProbabilityMeasure (offsetEdgeLaw G w θ v) :=
  isProbabilityMeasure_densityLaw (densityMass_offsetEdgeDensity_ne_zero G hw θ v)
    (densityMass_offsetEdgeDensity_ne_top G hG hw θ v)

/-! ## Character translation and charged vanishing -/

/-- **The offset law admits character translations** with offsets `r = θ` (FS81 Lemma 4.3 under
the shifted weights `I(∇φ + θ)`). -/
theorem characterTranslation_offsetEdgeLaw (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V) :
    CharacterTranslation (offsetEdgeLaw G w θ v) (gradLinear G) w θ W := by
  set h : (V → ℝ) → ℝ := fun φ => (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) with hh
  have hlaw : offsetEdgeLaw G w θ v =
      densityLaw (fun φ => h φ * ∏ e, (w ((gradLinear G φ e + θ e : ℝ) : ℂ)).re) := by
    rw [offsetEdgeLaw]
    congr 1
    funext φ
    simp only [offsetEdgeDensity, gradLinear_apply, hh]
    ring
  have hh_meas : Measurable h :=
    (measurable_const.indicator measurableSet_Ico).comp (measurable_pi_apply v)
  have hh0 : ∀ φ, 0 ≤ h φ := fun φ => by
    simp only [hh]; by_cases hφ : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hφ]
  have hh1 : ∀ φ, h φ ≤ 1 := fun φ => by
    simp only [hh]; by_cases hφ : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hφ]
  rw [hlaw]
  refine ⟨fun τ a _ haW => integrable_character_mul_edgeRatio hw _ _ _ τ a haW,
    fun τ a hτ haW => ?_⟩
  -- replace `a` by `a - a(v)`, which fixes the root and changes neither `∇a` nor `⟨a, τ⟩`
  set a' : V → ℝ := fun j => a j - a v with ha'
  have hDa' : gradLinear G a' = gradLinear G a := by
    funext e
    simp only [gradLinear_apply, Multigraph.grad, ha']
    ring
  have hpair : ∑ j, a' j * τ j = ∑ j, a j * τ j := by
    simp only [ha', sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hτ, mul_zero, sub_zero]
  rw [← hDa', ← hpair]
  have haW' : ∀ e, |gradLinear G a' e| ≤ W := by rw [hDa']; exact haW
  have hinv : ∀ (φ : V → ℝ) (s : ℝ), h (φ + s • a') = h φ := by
    intro φ s
    simp only [hh, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha', sub_self, mul_zero, add_zero]
  have hedge : a' ≠ 0 → ∃ e, gradLinear G a' e ≠ 0 := by
    intro ha0
    by_contra hc
    push Not at hc
    have hE : G.energy a' = 0 := by
      simp only [Multigraph.energy]
      exact Finset.sum_eq_zero fun e _ => by rw [← gradLinear_apply, hc e]; ring
    obtain ⟨k, hk⟩ := (Multigraph.energy_eq_zero_iff_exists_const G hG a').mp hE
    have hk0 : k = 0 := by
      have := congrFun hk v
      simp only [ha', sub_self] at this
      exact this.symm
    exact ha0 (by rw [hk, hk0]; rfl)
  exact translate_densityLaw hw (gradLinear G) θ h hh_meas hh0 hh1 τ a' haW' hinv hedge

/-- **FS81 (6.3) for integer charges under the offset law**: a charged character times a bounded
measurable shift-invariant observable integrates to zero. -/
theorem integral_character_mul_offsetEdgeLaw_eq_zero_of_invariant (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V)
    (τ : V → ℤ) (hτ : ∑ j, τ j ≠ 0) (g : (V → ℝ) → ℂ) (hg : Measurable g)
    (hbdd : ∃ M : ℝ, ∀ φ, ‖g φ‖ ≤ M) (hinv : ∀ (φ : V → ℝ) (s : ℝ), g (fun j => φ j + s) = g φ) :
    ∫ φ, gffCharacter (fun j => (τ j : ℝ)) φ * g φ ∂offsetEdgeLaw G w θ v = 0 := by
  obtain ⟨M, hM⟩ := hbdd
  rw [offsetEdgeLaw, integral_densityLaw (offsetEdgeDensity_nonneg G hw θ v)
    (measurable_offsetEdgeDensity G hw θ v)]
  suffices h : ∫ φ, ((offsetEdgeDensity G w θ v φ : ℝ) : ℂ) *
      (gffCharacter (fun j => (τ j : ℝ)) φ * g φ) = 0 by
    rw [h, mul_zero]
  set Q : ℤ := ∑ j, τ j with hQ
  set u : V → ℝ := fun j => if j = v then 0 else 1 with hu_def
  have hu : u v = 0 := by simp [hu_def]
  set f : (V → ℝ) → ℂ := fun φ => ((offsetEdgeDensity G w θ v φ : ℝ) : ℂ) *
    (gffCharacter (fun j => (τ j : ℝ)) φ * g φ) with hf
  have hf_int : Integrable f := by
    have hint := (integrable_offsetEdgeDensity G hG hw θ v).ofReal (𝕜 := ℂ)
    refine hint.mul_of_top_left (memLp_top_of_bound ?_ M (Filter.Eventually.of_forall fun φ => ?_))
    · exact ((Reduction.continuous_gffCharacter _).aestronglyMeasurable).mul
        hg.aestronglyMeasurable
    · rw [norm_mul, Reduction.norm_gffCharacter, one_mul]; exact hM _
  have hshear : ∀ (ψ : {j // j ≠ v} → ℝ) (x : ℝ),
      shear v u (glue v ψ x) = fun j => glue v ψ 0 j + x := by
    intro ψ x
    funext j
    rw [shear_apply_apply, glue_self]
    by_cases h : j = v
    · subst h; simp [glue_self, hu]
    · simp [glue_of_ne _ _ h, hu_def, h]
  have hpt : ∀ (ψ : {j // j ≠ v} → ℝ) (x : ℝ), f (shear v u (glue v ψ x)) =
      (((∏ e, (w ((G.grad (glue v ψ 0) e + θ e : ℝ) : ℂ)).re : ℝ) : ℂ) *
        gffCharacter (fun j => (τ j : ℝ)) (glue v ψ 0) * g (glue v ψ 0)) *
      ((((Set.Ico (-Real.pi) Real.pi).indicator 1 x : ℝ) : ℂ) *
        Complex.exp (I * ((Q : ℂ) * (x : ℂ)))) := by
    intro ψ x
    rw [hshear]
    have hgr : G.grad (fun j => glue v ψ 0 j + x) = G.grad (glue v ψ 0) := by
      funext e; simp only [Multigraph.grad]; ring
    have hv : glue v ψ 0 v + x = x := by rw [glue_self, zero_add]
    have hchar : gffCharacter (fun j => (τ j : ℝ)) (fun j => glue v ψ 0 j + x) =
        gffCharacter (fun j => (τ j : ℝ)) (glue v ψ 0) *
          Complex.exp (I * ((Q : ℂ) * (x : ℂ))) := by
      unfold gffCharacter
      rw [← Complex.exp_add]
      congr 1
      simp only [hQ]
      push_cast
      rw [Finset.sum_mul, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hf, offsetEdgeDensity, hgr, hv, hchar, hinv]
    push_cast
    ring
  rw [← integral_comp_shear hu f,
    integral_eq_integral_integral_glue v ((integrable_comp_shear_iff hu).mpr hf_int)]
  simp_rw [hpt, integral_const_mul, integral_indicator_mul_exp_eq_zero hτ, mul_zero,
    integral_zero]

/-! ## The renormalization identity for an abstract rooted law -/

/-- The two properties of a rooted law used by the renormalization identity: character
translation with offsets `r`, and the vanishing of charged characters against shift-invariant
observables. -/
def IsRootedTranslationLaw (μ : Measure (V → ℝ)) (G : Multigraph V E) (w : ℂ → ℂ) (r : E → ℝ)
    (W : ℝ) : Prop :=
  CharacterTranslation μ (gradLinear G) w r W ∧
    ∀ τ : V → ℤ, ∑ j, τ j ≠ 0 → ∀ g : (V → ℝ) → ℂ, Measurable g →
      (∃ M : ℝ, ∀ φ, ‖g φ‖ ≤ M) → (∀ (φ : V → ℝ) (s : ℝ), g (fun j => φ j + s) = g φ) →
        ∫ φ, gffCharacter (fun j => (τ j : ℝ)) φ * g φ ∂μ = 0

theorem isRootedTranslationLaw_offsetEdgeLaw (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V) :
    IsRootedTranslationLaw (offsetEdgeLaw G w θ v) G w θ W :=
  ⟨characterTranslation_offsetEdgeLaw G hG hw θ v,
    fun τ hτ g hg hbdd hinv =>
      integral_character_mul_offsetEdgeLaw_eq_zero_of_invariant G hG hw θ v τ hτ g hg hbdd hinv⟩

omit [DecidableEq V] in
/-- Rewriting a sum of the form `∑ (φ + σ) ϱ`. -/
lemma sum_add_mul_eq (φ σ : V → ℝ) (ϱ : V → ℤ) :
    ∑ j, (φ j + σ j) * (ϱ j : ℝ) = ∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ) := by
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq V] in

theorem integral_ensemble_eq_of_law (G : Multigraph V E) (μ : Measure (V → ℝ))
    [IsFiniteMeasure μ] (hw : IsStripWeight w W c) (r : E → ℝ)
    (hμ : IsRootedTranslationLaw μ G w r W)
    (N : Finset (V → ℤ)) (hNa : AtMostOneNonNeutral N) (K : (V → ℤ) → ℝ) (σ : V → ℝ)
    (centerOf : (V → ℤ) → V) (a : (V → ℤ) → V → ℝ)
    (hconst : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ G.comparableDensities (neutralPart N) ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), a ϱ j = c)
    (hsupp : ∀ ϱ ∈ neutralPart N, Function.support (a ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ))
    (horth : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ neutralPart N, ϱ ≠ ϱ' →
      ∑ j, a ϱ j * (ϱ' j : ℝ) = 0)
    (hW : ∀ ϱ ∈ neutralPart N, ∀ e, |G.grad (a ϱ) e| ≤ W) :
    ∫ φ, ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) ∂μ =
      ∫ φ, ∏ ϱ ∈ neutralPart N, ((1 : ℂ) +
        ((K ϱ * Real.exp (-translationEnergy c (gradLinear G) (a ϱ) fun j => (ϱ j : ℝ)) : ℝ) :
          ℂ) * localFactor w c (gradLinear G (a ϱ)) (gradLinear G φ + r)
            (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂μ := by
  classical
  set P := neutralPart N with hPdef
  have hPneutral : ∀ ϱ ∈ P, ∑ j, ϱ j = 0 := fun ϱ hϱ => (mem_neutralPart.mp hϱ).2
  set Rest : (V → ℝ) → ℝ := fun φ =>
    ∏ ϱ ∈ P, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) with hRest
  -- Step 1: the non-neutral density drops out
  have hdrop : ∫ φ, ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)
      ∂μ = ∫ φ, ((Rest φ : ℝ) : ℂ) ∂μ := by
    by_cases hch : ∃ ϱc ∈ N, ∑ j, ϱc j ≠ 0
    · obtain ⟨ϱc, hϱc, hne⟩ := hch
      have hcP : ϱc ∉ P := fun h => hne (hPneutral ϱc h)
      have hN : N = insert ϱc P := by
        ext ϱ
        simp only [Finset.mem_insert, hPdef, mem_neutralPart]
        constructor
        · intro hϱ
          by_cases h0 : ∑ j, ϱ j = 0
          · exact Or.inr ⟨hϱ, h0⟩
          · exact Or.inl (hNa ϱ hϱ ϱc hϱc h0 hne)
        · rintro (rfl | ⟨hϱ, _⟩)
          · exact hϱc
          · exact hϱ
      have hpt : ∀ φ : V → ℝ,
          ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) =
            ((Rest φ : ℝ) : ℂ) + ((K ϱc / 2 : ℝ) : ℂ) *
              (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)) *
                  (gffCharacter (fun j => (ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) +
                Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))) *
                  (gffCharacter (fun j => ((-ϱc) j : ℝ)) φ * ((Rest φ : ℝ) : ℂ))) := by
        intro φ
        rw [hN, Finset.prod_insert hcP]
        change (((1 + K ϱc * Real.cos (∑ j, (φ j + σ j) * (ϱc j : ℝ))) * Rest φ : ℝ) : ℂ) = _
        generalize Rest φ = R
        rw [sum_add_mul_eq]
        have hc1 : gffCharacter (fun j => (ϱc j : ℝ)) φ =
            Complex.exp (I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ)) := by
          unfold gffCharacter; congr 1; push_cast; ring
        have hc2 : gffCharacter (fun j => ((-ϱc) j : ℝ)) φ =
            Complex.exp (-(I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ))) := by
          unfold gffCharacter; congr 1
          simp only [Pi.neg_apply, Int.cast_neg]
          push_cast
          rw [← mul_neg, ← Finset.sum_neg_distrib]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hc1, hc2]
        generalize (∑ j, φ j * (ϱc j : ℝ)) = θ₀
        generalize (∑ j, σ j * (ϱc j : ℝ)) = s
        have h1 : Complex.exp (((θ₀ : ℂ) + (s : ℂ)) * I) =
            Complex.exp (I * (s : ℂ)) * Complex.exp (I * (θ₀ : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; ring
        have h2 : Complex.exp (-((θ₀ : ℂ) + (s : ℂ)) * I) =
            Complex.exp (-(I * (s : ℂ))) * Complex.exp (-(I * (θ₀ : ℂ))) := by
          rw [← Complex.exp_add]; congr 1; ring
        push_cast
        rw [Complex.cos, h1, h2]
        ring
      simp_rw [hpt]
      have hRest_meas : Measurable Rest := by
        refine (continuous_finsetProd _ fun ϱ _ => ?_).measurable
        fun_prop
      have hRest_bdd : ∃ M : ℝ, ∀ φ, ‖((Rest φ : ℝ) : ℂ)‖ ≤ M :=
        ⟨∏ ϱ ∈ P, (1 + |K ϱ|), fun φ => norm_prod_one_add_mul_cos_le P K _⟩
      have hRest_inv : ∀ (φ : V → ℝ) (s : ℝ), ((Rest fun j => φ j + s : ℝ) : ℂ) =
          ((Rest φ : ℝ) : ℂ) := by
        intro φ s
        simp only [hRest]
        rw [prod_neutral_shift_invariant P hPneutral K σ φ s]
      have hz₁ := hμ.2 ϱc hne (fun φ => ((Rest φ : ℝ) : ℂ))
        (Complex.measurable_ofReal.comp hRest_meas) hRest_bdd hRest_inv
      have hneg : ∑ j, (-ϱc) j ≠ 0 := by
        simp only [Pi.neg_apply, Finset.sum_neg_distrib, neg_ne_zero]; exact hne
      have hz₂ := hμ.2 (-ϱc) hneg (fun φ => ((Rest φ : ℝ) : ℂ))
        (Complex.measurable_ofReal.comp hRest_meas) hRest_bdd hRest_inv
      have hint₀ : Integrable (fun φ => ((Rest φ : ℝ) : ℂ)) μ :=
        Integrable.of_bound (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable
          _ (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le P K _)
      have hintχ : ∀ τ : V → ℤ, Integrable
          (fun φ => gffCharacter (fun j => (τ j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) μ :=
        fun τ => Integrable.of_bound
          (((Reduction.continuous_gffCharacter _).aestronglyMeasurable).mul
            (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable)
          (∏ ϱ ∈ P, (1 + |K ϱ|)) (Filter.Eventually.of_forall fun φ => by
            rw [norm_mul, Reduction.norm_gffCharacter, one_mul]
            exact norm_prod_one_add_mul_cos_le P K _)
      have hA := (hintχ ϱc).const_mul (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)))
      have hB := (hintχ (-ϱc)).const_mul
        (Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))))
      have hAB : Integrable (fun φ => ((K ϱc / 2 : ℝ) : ℂ) *
          (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)) *
              (gffCharacter (fun j => (ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) +
            Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))) *
              (gffCharacter (fun j => ((-ϱc) j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)))) μ :=
        (hA.add hB).const_mul _
      rw [integral_add hint₀ hAB, integral_const_mul, integral_add hA hB, integral_const_mul,
        integral_const_mul, hz₁, hz₂]
      simp
    · push Not at hch
      have hN : N = P := by
        ext ϱ
        simp only [hPdef, mem_neutralPart]
        exact ⟨fun h => ⟨h, hch ϱ h⟩, fun h => h.1⟩
      rw [hN]
  rw [hdrop]
  -- Step 2: translate the neutral densities
  have hdisj := grad_disjoint_of_spinWave_clauses G P centerOf a hconst hsupp
  have key := integral_prod_add_mul_cos_eq_localFactor μ (gradLinear G) w c hw.cost_even r
    hw.width_nonneg hμ.1 hw.ofReal_ne_zero
    (ι := P) (fun ϱ j => ((ϱ : V → ℤ) j : ℝ))
    (fun ϱ => by exact_mod_cast hPneutral ϱ ϱ.2) (fun _ => 1) (fun ϱ => K ϱ)
    (fun ϱ => ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ)) (fun ϱ => a ϱ)
    (fun ϱ ϱ' hne => horth ϱ ϱ.2 ϱ' ϱ'.2 fun h => hne (Subtype.ext h))
    (fun ϱ ϱ' hne e => hdisj ϱ ϱ.2 ϱ' ϱ'.2 (fun h => hne (Subtype.ext h)) e)
    (fun ϱ e => hW ϱ ϱ.2 e)
  have hl : ∀ φ : V → ℝ, ((Rest φ : ℝ) : ℂ) =
      ((∏ ϱ : P, (1 + K ϱ * Real.cos (∑ j, φ j * ((ϱ : V → ℤ) j : ℝ) +
        ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    simp only [hRest]
    rw [← Finset.prod_coe_sort P]
    congr 2
    funext ϱ
    congr 3
    exact sum_add_mul_eq φ σ ϱ
  simp_rw [hl]
  rw [key]
  congr 1
  funext φ
  rw [← Finset.prod_coe_sort P]
  rfl

variable {G : Multigraph V E} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}


theorem renormalization_identity_of_law (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (r : E → ℝ) (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i))
    (hw : IsStripWeight w W c) (hμ : IsRootedTranslationLaw μ G w r W) {κ : ℝ} (hκ : 0 < κ)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    (hW1 : 1 ≤ W) (k₀ : ℕ) (σ : V → ℝ) :
    ∫ φ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) ∂μ =
      ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i, ((1 : ℂ) +
        ((CL.K i ϱ * Real.exp (-translationEnergy c (gradLinear G) (layerSpinWave CL κ amp k₀ i ϱ)
          fun j => (ϱ j : ℝ)) : ℝ) : ℂ) *
        localFactor w c (gradLinear G (layerSpinWave CL κ amp k₀ i ϱ)) (gradLinear G φ + r)
          (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂μ := by
  classical
  -- the gradient bound
  have hgrad : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, |G.grad (layerSpinWave CL κ amp k₀ i ϱ) e| ≤ W := by
    intro i ϱ hϱ e
    obtain ⟨-, hK0, hK1, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
    simp only [layerSpinWave, dite_eq_left hϱ]
    refine (abs_grad_envelopeWave_le _ hκ (by rw [hK0]; exact hK₀) (by rw [hK1]; exact hK₁)
      hamp k₀ e).trans ?_
    rw [hK1]
    exact max_le hampW hW1
  have hpt : ∀ φ : V → ℝ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) =
      ∑ i, (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
        (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    rw [CL.expand fun j => φ j + σ j]
    push_cast
    rfl
  have hint : ∀ i, Integrable (fun φ : V → ℝ => (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
      (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)) μ := by
    intro i
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound ?_ (∏ ϱ ∈ CL.N i, (1 + |CL.K i ϱ|))
      (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le _ _ _)
    refine (Complex.continuous_ofReal.comp
      (continuous_finsetProd _ fun ϱ _ => ?_)).aestronglyMeasurable
    fun_prop
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  obtain ⟨hR, hNa⟩ := hroot i
  obtain ⟨hconst, hsupp, horth⟩ := layerSpinWave_clauses CL κ amp k₀ i
  rw [hR] at hconst hsupp horth
  have key := integral_ensemble_eq_of_law G μ hw r hμ (CL.N i) hNa (CL.K i) σ centerOf
    (layerSpinWave CL κ amp k₀ i) hconst hsupp horth
    (fun ϱ hϱ e => hgrad i ϱ (by rw [hR]; exact hϱ) e)
  rw [key, hR]


theorem offsetEdgeLaw_renormalization_identity (hG : G.toSimpleGraph.Connected) (v : V)
    (θ : E → ℝ) (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i))
    (hw : IsStripWeight w W c) {κ : ℝ} (hκ : 0 < κ)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    (hW1 : 1 ≤ W) (k₀ : ℕ) (σ : V → ℝ) :
    ∫ φ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) ∂offsetEdgeLaw G w θ v =
      ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i, ((1 : ℂ) +
        ((CL.K i ϱ * Real.exp (-translationEnergy c (gradLinear G) (layerSpinWave CL κ amp k₀ i ϱ)
          fun j => (ϱ j : ℝ)) : ℝ) : ℂ) *
        localFactor w c (gradLinear G (layerSpinWave CL κ amp k₀ i ϱ)) (gradLinear G φ + θ)
          (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂offsetEdgeLaw G w θ v :=
  renormalization_identity_of_law (offsetEdgeLaw G w θ v) θ CL hroot hw
    (isRootedTranslationLaw_offsetEdgeLaw G hG hw θ v) hκ hK₀ hK₁ hamp hampW hW1 k₀ σ

end FroehlichSpencer.BKT.Generic

end
