/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Translate
public import FroehlichSpencer.BKT.SOS.Tilt.Phased
public import FroehlichSpencer.BKT.Generic.Moment.Offset

/-!
# The tilted rooted law (the dipole tilt construction)

For a connected multigraph `G` with root `v`, a strip weight `w`, real edge offsets `θ` and a tilt
edge field `b`, the **tilted density** is
`e^{⟨∇φ, b⟩} ∏_e w(∇φ(e) + θ(e)) 𝟙_{[-π,π)}(φ(v))` (`tiltDensity`).

* `integrable_tiltDensity`: it is integrable when `w` has an exponential majorant `K e^{−η|t|}` and
  `|b| ≤ η/2`. This is the parent-tree argument of `integrable_offsetEdgeDensity`, factored as
  `integrable_of_tree_majorant`.
* `characterTranslationPhased_tiltLaw`: its normalized law admits phased character translations,
  with offsets `θ` and phase `ψ(a) = ⟨∇a, b⟩` (`tiltLinear`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Reduction (gffCharacter)

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-! ## The tree majorant -/

/-- **Integrability from an edge majorant.** On a connected multigraph, a nonnegative measurable
function bounded by `𝟙_{[-π,π)}(φ(v)) ∏_e g(∇φ(e))`, with `g` even, bounded and integrable, is
integrable (the parent-tree increments of `integrable_offsetEdgeDensity`). -/
theorem integrable_of_tree_majorant (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (v : V)
    (f : (V → ℝ) → ℝ) (hf_meas : Measurable f) (hf0 : ∀ φ, 0 ≤ f φ) (g : ℝ → ℝ)
    (hg_int : Integrable g) (hg0 : ∀ x, 0 ≤ g x) {M : ℝ} (hgM : ∀ x, g x ≤ M)
    (hgeven : ∀ x, g (-x) = g x)
    (hfle : ∀ φ, f φ ≤ (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) * ∏ e, g (G.grad φ e)) :
    Integrable f := by
  classical
  set M' : ℝ := max M 1 with hM'
  have hM'1 : 1 ≤ M' := le_max_right _ _
  have hgM' : ∀ x, g x ≤ M' := fun x => (hgM x).trans (le_max_left _ _)
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
  have htree : ∀ φ : V → ℝ, (∏ e, g (G.grad φ e)) ≤
      (∏ u : {u // u ≠ v}, g (φ u - φ (p u))) * M' ^ Fintype.card E := by
    intro φ
    set f' : E → ℝ := fun e => g (G.grad φ e) with hf'
    set S : Finset E := Finset.univ.image eOf with hS
    have hf0' : ∀ e, 0 ≤ f' e := fun e => hg0 _
    rw [← Finset.prod_mul_prod_compl S f']
    have hS1 : ∏ e ∈ S, f' e ≤ ∏ u : {u // u ≠ v}, g (φ u - φ (p u)) := by
      rw [hS, Finset.prod_image fun x _ y _ h => hinj h]
      refine le_of_eq (Finset.prod_congr rfl fun u _ => ?_)
      simp only [hf', Multigraph.grad]
      rcases heOf u with ⟨hs, htg⟩ | ⟨hs, htg⟩
      · rw [hs, htg]
      · rw [hs, htg, show φ (p u) - φ u = -(φ u - φ (p u)) by ring, hgeven]
    have hS2 : ∏ e ∈ Sᶜ, f' e ≤ M' ^ Fintype.card E := by
      calc ∏ e ∈ Sᶜ, f' e ≤ ∏ _e ∈ Sᶜ, M' :=
            Finset.prod_le_prod₀ (fun e _ => hf0' e) fun e _ => hgM' _
        _ = M' ^ Sᶜ.card := Finset.prod_const _
        _ ≤ M' ^ Fintype.card E := pow_le_pow_right₀ hM'1 (Finset.card_le_univ _)
    exact mul_le_mul hS1 hS2 (Finset.prod_nonneg fun e _ => hf0' e)
      (Finset.prod_nonneg fun u _ => hg0 _)
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
  set h : V → ℝ → ℝ := fun x =>
    if x = v then (Set.Ico (-Real.pi) Real.pi).indicator 1 else g with hh
  have hhint : ∀ x, Integrable (h x) := by
    intro x
    by_cases hx : x = v
    · simp only [hh, hx, ite_true]
      exact (integrableOn_const (C := (1 : ℝ)) measure_Ico_lt_top.ne).integrable_indicator
        measurableSet_Ico
    · simp only [hh, hx, ite_false]
      exact hg_int
  set gg : (V → ℝ) → ℝ := fun y => M' ^ Fintype.card E * ∏ x, h x (y x) with hgg
  have hgint : Integrable gg := by
    have := Integrable.fintype_prod (μ := fun _ : V => (volume : Measure ℝ)) hhint
    rw [← volume_pi] at this
    exact this.const_mul _
  have hgT : Integrable (gg ∘ incrementMap p L) :=
    (hT.integrable_comp hgint.aestronglyMeasurable).mpr hgint
  refine hgT.mono' hf_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 φ)]
  have hgφ : (gg ∘ incrementMap p L) φ = M' ^ Fintype.card E *
      ((Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
        ∏ u : {u // u ≠ v}, g (φ u - φ (p u))) := by
    simp only [Function.comp_apply, hgg]
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
  calc f φ ≤ (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) * ∏ e, g (G.grad φ e) := hfle φ
    _ ≤ (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
          ((∏ u : {u // u ≠ v}, g (φ u - φ (p u))) * M' ^ Fintype.card E) :=
        mul_le_mul_of_nonneg_left (htree φ) hind
    _ = M' ^ Fintype.card E * ((Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
          ∏ u : {u // u ≠ v}, g (φ u - φ (p u))) := by ring

/-! ## The tilted density -/

/-- The tilt as a linear functional `a ↦ ⟨Da, b⟩`. -/
def tiltLinear (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (b : E → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun := tiltExponent D b
  map_add' := tiltExponent_add D b
  map_smul' := fun s φ => by
    simp only [tiltExponent, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring

omit [Fintype V] [DecidableEq V] in
theorem tiltLinear_apply (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (b : E → ℝ) (a : V → ℝ) :
    tiltLinear D b a = tiltExponent D b a := rfl

/-- **The tilted rooted density** `e^{⟨∇φ, b⟩} ∏_e w(∇φ(e) + θ(e)) 𝟙_{[-π,π)}(φ(v))`. -/
def tiltDensity (G : Multigraph V E) (w : ℂ → ℂ) (θ b : E → ℝ) (v : V) (φ : V → ℝ) : ℝ :=
  Real.exp (tiltExponent (gradLinear G) b φ) * offsetEdgeDensity G w θ v φ

omit [Fintype V] [DecidableEq V] in
theorem tiltDensity_eq (G : Multigraph V E) (w : ℂ → ℂ) (θ b : E → ℝ) (v : V) :
    tiltDensity G w θ b v = fun φ => (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
      Real.exp (tiltExponent (gradLinear G) b φ) *
      ∏ e, (w ((gradLinear G φ e + θ e : ℝ) : ℂ)).re := by
  funext φ
  simp only [tiltDensity, offsetEdgeDensity, gradLinear_apply]
  ring

omit [Fintype V] [DecidableEq V] in
theorem tiltDensity_nonneg (G : Multigraph V E) (hw : IsStripWeight w W c) (θ b : E → ℝ)
    (v : V) (φ : V → ℝ) : 0 ≤ tiltDensity G w θ b v φ :=
  mul_nonneg (Real.exp_pos _).le (offsetEdgeDensity_nonneg G hw θ v φ)

omit [DecidableEq V] in
theorem measurable_tiltDensity (G : Multigraph V E) (hw : IsStripWeight w W c) (θ b : E → ℝ)
    (v : V) : Measurable (tiltDensity G w θ b v) :=
  (continuous_tiltExponent (gradLinear G) b).measurable.exp.mul
    (measurable_offsetEdgeDensity G hw θ v)

/-- **The tilted density is integrable** under an exponential majorant and `|b| ≤ η/2`. -/
theorem integrable_tiltDensity (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (hw : IsStripWeight w W c) {η K : ℝ} (hη : 0 < η) (hexp : HasExpMajorant w W η K)
    (θ b : E → ℝ) (hb : ∀ e, |b e| ≤ η / 2) (v : V) :
    Integrable (tiltDensity G w θ b v) := by
  have hW0 : |(0 : ℝ)| ≤ W := by rw [abs_zero]; exact hw.width_nonneg
  have hK0 : 0 ≤ K := by
    have h1 := hexp 0 0 hW0
    have h2 := norm_nonneg (w ((0 : ℝ) + ((0 : ℝ) : ℂ) * I))
    by_contra hK
    push Not at hK
    have : K * Real.exp (-(η * |(0 : ℝ)|)) < 0 := mul_neg_of_neg_of_pos hK (Real.exp_pos _)
    linarith
  set Θ : ℝ := ∑ e, |θ e| with hΘ
  set g : ℝ → ℝ := fun x => K * Real.exp (η * Θ) * Real.exp (-((η / 2) * |x|)) with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hgM : ∀ x, g x ≤ K * Real.exp (η * Θ) := fun x => by
    have : Real.exp (-((η / 2) * |x|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := abs_nonneg x; nlinarith)
    have h0 : 0 ≤ K * Real.exp (η * Θ) := by positivity
    calc g x = K * Real.exp (η * Θ) * Real.exp (-((η / 2) * |x|)) := rfl
      _ ≤ K * Real.exp (η * Θ) * 1 := mul_le_mul_of_nonneg_left this h0
      _ = K * Real.exp (η * Θ) := mul_one _
  have hgeven : ∀ x, g (-x) = g x := fun x => by simp only [hg, abs_neg]
  have hgint : Integrable g := (integrable_exp_neg_mul_abs (by positivity)).const_mul _
  refine integrable_of_tree_majorant G hG v _ (measurable_tiltDensity G hw θ b v)
    (tiltDensity_nonneg G hw θ b v) g hgint hg0 hgM hgeven fun φ => ?_
  -- the per-edge bound
  have hedge : ∀ e, Real.exp (b e * G.grad φ e) * (w ((G.grad φ e + θ e : ℝ) : ℂ)).re ≤
      K * Real.exp (η * |θ e|) * Real.exp (-((η / 2) * |G.grad φ e|)) := by
    intro e
    set t := G.grad φ e
    have h1 : (w ((t + θ e : ℝ) : ℂ)).re ≤ K * Real.exp (-(η * |t + θ e|)) := by
      have := hexp (t + θ e) 0 hW0
      rw [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact (Complex.re_le_norm _).trans this
    have h2 : Real.exp (b e * t) ≤ Real.exp ((η / 2) * |t|) := by
      apply Real.exp_le_exp.mpr
      calc b e * t ≤ |b e * t| := le_abs_self _
        _ = |b e| * |t| := abs_mul _ _
        _ ≤ (η / 2) * |t| := mul_le_mul_of_nonneg_right (hb e) (abs_nonneg _)
    have h3 : |t| ≤ |t + θ e| + |θ e| := by
      have := abs_sub_abs_le_abs_sub t (-θ e)
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    have hw0 : 0 ≤ (w ((t + θ e : ℝ) : ℂ)).re := (hw.ofReal_re_pos _).le
    calc Real.exp (b e * t) * (w ((t + θ e : ℝ) : ℂ)).re
        ≤ Real.exp ((η / 2) * |t|) * (K * Real.exp (-(η * |t + θ e|))) :=
          mul_le_mul h2 h1 hw0 (Real.exp_pos _).le
      _ = K * Real.exp ((η / 2) * |t| - η * |t + θ e|) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ K * Real.exp (η * |θ e| - (η / 2) * |t|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK0
      _ = K * Real.exp (η * |θ e|) * Real.exp (-((η / 2) * |t|)) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
  have hind : 0 ≤ (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) (φ v) := by
    by_cases hv : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hv]
  have hprod : Real.exp (tiltExponent (gradLinear G) b φ) *
      ∏ e, (w ((G.grad φ e + θ e : ℝ) : ℂ)).re ≤ ∏ e, g (G.grad φ e) := by
    have hsplit : Real.exp (tiltExponent (gradLinear G) b φ) *
        ∏ e, (w ((G.grad φ e + θ e : ℝ) : ℂ)).re =
        ∏ e, (Real.exp (b e * G.grad φ e) * (w ((G.grad φ e + θ e : ℝ) : ℂ)).re) := by
      rw [Finset.prod_mul_distrib, tiltExponent, Real.exp_sum]
      simp only [gradLinear_apply]
    rw [hsplit]
    calc ∏ e, (Real.exp (b e * G.grad φ e) * (w ((G.grad φ e + θ e : ℝ) : ℂ)).re)
        ≤ ∏ e, (K * Real.exp (η * |θ e|) * Real.exp (-((η / 2) * |G.grad φ e|))) :=
          Finset.prod_le_prod₀ (fun e _ => mul_nonneg (Real.exp_pos _).le
            (hw.ofReal_re_pos _).le) fun e _ => hedge e
      _ ≤ ∏ e, g (G.grad φ e) := by
          refine Finset.prod_le_prod₀ (fun e _ => by positivity) fun e _ => ?_
          simp only [hg]
          gcongr
          exact Finset.single_le_sum (f := fun e => |θ e|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ e)
  calc tiltDensity G w θ b v φ =
        (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) *
          (Real.exp (tiltExponent (gradLinear G) b φ) *
            ∏ e, (w ((G.grad φ e + θ e : ℝ) : ℂ)).re) := by
        simp only [tiltDensity, offsetEdgeDensity]; ring
    _ ≤ (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) * ∏ e, g (G.grad φ e) :=
        mul_le_mul_of_nonneg_left hprod hind

/-- The normalized tilted law. -/
def tiltLaw (G : Multigraph V E) (w : ℂ → ℂ) (θ b : E → ℝ) (v : V) : Measure (V → ℝ) :=
  densityLaw (tiltDensity G w θ b v)

instance isFiniteMeasure_tiltLaw (G : Multigraph V E) (w : ℂ → ℂ) (θ b : E → ℝ) (v : V) :
    IsFiniteMeasure (tiltLaw G w θ b v) :=
  isFiniteMeasure_densityLaw _

/-- **The tilted law admits phased character translations** (phase `ψ(a) = ⟨∇a, b⟩`). -/
theorem characterTranslationPhased_tiltLaw (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (hw : IsStripWeight w W c) {η K : ℝ} (hη : 0 < η)
    (hexp : HasExpMajorant w W η K) (θ b : E → ℝ) (hb : ∀ e, |b e| ≤ η / 2) (v : V) :
    CharacterTranslationPhased (tiltLaw G w θ b v) (gradLinear G) w θ W
      (tiltLinear (gradLinear G) b) := by
  set h : (V → ℝ) → ℝ := fun φ => (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) with hh
  have hlaw : tiltLaw G w θ b v = densityLaw (fun φ => h φ *
      Real.exp (tiltExponent (gradLinear G) b φ) *
      ∏ e, (w ((gradLinear G φ e + θ e : ℝ) : ℂ)).re) := by
    rw [tiltLaw, tiltDensity_eq]
  have hh_meas : Measurable h :=
    (measurable_const.indicator measurableSet_Ico).comp (measurable_pi_apply v)
  have hh0 : ∀ φ, 0 ≤ h φ := fun φ => by
    simp only [hh]; by_cases hφ : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hφ]
  have hh1 : ∀ φ, h φ ≤ 1 := fun φ => by
    simp only [hh]; by_cases hφ : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hφ]
  rw [hlaw]
  refine ⟨fun τ a _ haW => integrable_character_mul_edgeRatio hw _ _ _ τ a haW,
    fun τ a hτ haW => ?_⟩
  set a' : V → ℝ := fun j => a j - a v with ha'
  have hDa' : gradLinear G a' = gradLinear G a := by
    funext e
    simp only [gradLinear_apply, Multigraph.grad, ha']
    ring
  have hpair : ∑ j, a' j * τ j = ∑ j, a j * τ j := by
    simp only [ha', sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hτ, mul_zero, sub_zero]
  have htilt : tiltLinear (gradLinear G) b a' = tiltLinear (gradLinear G) b a := by
    simp only [tiltLinear_apply, tiltExponent, hDa']
  rw [← hDa', ← hpair, ← htilt, tiltLinear_apply]
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
  exact translate_densityLaw_tilt hw hη hexp (gradLinear G) θ h hh_meas hh0 hh1 b hb τ a' haW'
    hinv hedge

end FroehlichSpencer.BKT.SOS.Tilt

end
