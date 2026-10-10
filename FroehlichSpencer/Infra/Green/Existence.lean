/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.APriori
public import FroehlichSpencer.Infra.Green.CombesThomas

/-!
# Existence, uniqueness and finite-volume approximation of the `ℓ²` solution

For the pointwise equation `∑' w, a x w * ψ w + (v x - z) * ψ x = δ_y x` (generic: a Hermitian
kernel `a` of finite row support and bounded row sums, an arbitrary real potential `v`,
`Im z ≠ 0`) we prove: existence of a square-summable solution for countable index type (by
pointwise compactness of the finite-volume columns) and, with uniqueness from
`FroehlichSpencer.Infra.Green.APriori`, existence and uniqueness; convergence of the finite-volume
columns to any `ℓ²` solution (along the directed set of finite sets, uniformly, and along any
sequence eventually containing every point); Combes–Thomas decay of the solution; and the symmetry
`G(z; x, y) = conj G(conj z; y, x)`.

Motivation: Fröhlich–Spencer (1983), (1.4), (1.29),
Fröhlich–Spencer (1983).

No Green function is defined here.
-/

@[expose] public section

open Matrix Filter Topology

namespace FroehlichSpencer.Infra

section Helpers

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

omit [DecidableEq X] in
private theorem summable_norm_sq_of_memℓp {ψ : X → ℂ} (hψ : Memℓp ψ 2) :
    Summable fun x => ‖ψ x‖ ^ 2 := by
  have := hψ.summable (by simp)
  simpa using this

private theorem tendsto_tail_zero (h : X → ℝ) :
    Tendsto (fun Λ : Finset X => ∑' x, (if x ∈ Λ then 0 else h x)) atTop (𝓝 0) := by
  have e : ∀ Λ : Finset X, ∑' x, (if x ∈ Λ then 0 else h x) = ∑' x : {x // x ∉ Λ}, h x := by
    intro Λ
    have := tsum_subtype ((Λ : Set X)ᶜ) h
    rw [show (∑' x : {x // x ∉ Λ}, h x) = ∑' x : ((Λ : Set X)ᶜ : Set X), h x from rfl, this]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ Λ <;> simp [Set.indicator, hx]
  simp_rw [e]
  exact tendsto_tsum_compl_atTop_zero h

private theorem summable_resolventColumn_sq (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) (z : ℂ)
    (y : X) : Summable fun x => ‖resolventColumn a v Λ z y x‖ ^ 2 :=
  summable_of_ne_finset_zero (s := Λ) fun x hx => by
    simp [resolventColumn_of_notMem_left a v z y hx]

private theorem summable_sub_sq (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) (z : ℂ) (y : X)
    {ψ : X → ℂ} (hψ : Memℓp ψ 2) :
    Summable fun x => ‖resolventColumn a v Λ z y x - ψ x‖ ^ 2 := by
  have h1 := summable_resolventColumn_sq a v Λ z y
  have h2 := summable_norm_sq_of_memℓp hψ
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
    ((h1.add h2).mul_left 2)
  have := norm_sub_le (resolventColumn a v Λ z y x) (ψ x)
  have h0 : 0 ≤ ‖resolventColumn a v Λ z y x - ψ x‖ := norm_nonneg _
  nlinarith [norm_nonneg (resolventColumn a v Λ z y x), norm_nonneg (ψ x),
    sq_nonneg (‖resolventColumn a v Λ z y x‖ - ‖ψ x‖)]

end Helpers

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

/-- FS83 (1.29): `G_Λ → G` in `ℓ²` as `Λ ↑ X` (along the directed set of finite sets). -/
theorem tendsto_tsum_norm_sq_resolventColumn_sub_atTop (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {y : X} {ψ : X → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x) :
    Tendsto (fun Λ : Finset X => ∑' x, ‖resolventColumn a v Λ z y x - ψ x‖ ^ 2) atTop (𝓝 0) := by
  have hT : Tendsto (fun Λ : Finset X => (1 + K ^ 2 / z.im ^ 2) *
      ∑' x, (if x ∈ Λ then 0 else ‖ψ x‖ ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_tail_zero fun x => ‖ψ x‖ ^ 2).const_mul (1 + K ^ 2 / z.im ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun Λ => tsum_nonneg fun x => by positivity) ?_
  filter_upwards [eventually_ge_atTop ({y} : Finset X)] with Λ hΛ
  exact tsum_norm_sq_resolventColumn_sub_le ha hfin hK v hz
    (Finset.singleton_subset_iff.1 hΛ) hψ h

/-- … hence uniformly in `x`. -/
theorem tendstoUniformly_resolventColumn_atTop (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {y : X} {ψ : X → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x) :
    TendstoUniformly (fun (Λ : Finset X) (x : X) => resolventColumn a v Λ z y x) ψ atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h0 := tendsto_tsum_norm_sq_resolventColumn_sub_atTop ha hfin hK v hz hψ h
  filter_upwards [h0.eventually (gt_mem_nhds (pow_pos hε 2))] with Λ hΛ x
  have h1 : ‖resolventColumn a v Λ z y x - ψ x‖ ^ 2 ≤
      ∑' x, ‖resolventColumn a v Λ z y x - ψ x‖ ^ 2 :=
    (summable_sub_sq a v Λ z y hψ).le_tsum x fun j _ => by positivity
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (h1.trans_lt hΛ)

/-- Sequential version, for any sequence of finite sets eventually containing every point. -/
theorem tendsto_resolventColumn_of_eventually_mem (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {Λ : ℕ → Finset X} (hΛ : ∀ x, ∀ᶠ n in atTop, x ∈ Λ n)
    {y : X} {ψ : X → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x) :
    Tendsto (fun n => ∑' x, ‖resolventColumn a v (Λ n) z y x - ψ x‖ ^ 2) atTop (𝓝 0) ∧
      ∀ x, Tendsto (fun n => resolventColumn a v (Λ n) z y x) atTop (𝓝 (ψ x)) := by
  have hT : Tendsto Λ atTop atTop := by
    refine Filter.tendsto_atTop.2 fun F => ?_
    have := (Filter.eventually_all_finset F).2 fun x _ => hΛ x
    filter_upwards [this] with n hn
    exact fun x hx => hn x hx
  refine ⟨(tendsto_tsum_norm_sq_resolventColumn_sub_atTop ha hfin hK v hz hψ h).comp hT, ?_⟩
  intro x
  exact ((tendstoUniformly_resolventColumn_atTop ha hfin hK v hz hψ h).tendsto_at x).comp hT

/-- Combes–Thomas decay passes to the infinite-volume solution. -/
theorem norm_le_exp_of_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {d : X → X → ℝ} (hd : ∀ x y w, d x y ≤ d x w + d w y) (hd0 : ∀ x, d x x = 0)
    (hrange : ∀ x y, a x y ≠ 0 → d x y ≤ 1) (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {y : X}
    {ψ : X → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x) (x : X) :
    ‖ψ x‖ ≤ 2 / |z.im| * Real.exp (-Real.log (1 + |z.im| / (2 * (K + 1))) * d x y) := by
  have hlim : Tendsto (fun Λ : Finset X => ‖resolventColumn a v Λ z y x‖) atTop (𝓝 ‖ψ x‖) :=
    (continuous_norm.tendsto _).comp
      ((tendstoUniformly_resolventColumn_atTop ha hfin hK v hz hψ h).tendsto_at x)
  exact le_of_tendsto' hlim fun Λ => norm_resolventColumn_le_exp ha hK hd hd0 hrange v Λ hz x y

/-- Finite-volume symmetry. -/
private theorem resolventColumn_eq_star (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) (z : ℂ) (x y : X) :
    resolventColumn a v Λ z y x = star (resolventColumn a v Λ (star z) x y) := by
  by_cases hx : x ∈ Λ
  swap
  · rw [resolventColumn_of_notMem_left a v z y hx, resolventColumn_of_notMem_right a v _ y hx,
      star_zero]
  by_cases hy : y ∈ Λ
  swap
  · rw [resolventColumn_of_notMem_right a v z x hy, resolventColumn_of_notMem_left a v _ x hy,
      star_zero]
  rw [resolventColumn_of_mem a v z hx hy, resolventColumn_of_mem a v _ hy hx]
  set M := restrictedOp a v Λ - (star z) • (1 : Matrix Λ Λ ℂ) with hM
  have hMh : Mᴴ = restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ) := by
    rw [hM, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      (isHermitian_restrictedOp ha v Λ).eq, star_star]
  have := congrArg (fun N : Matrix Λ Λ ℂ => N ⟨x, hx⟩ ⟨y, hy⟩)
    (Matrix.conjTranspose_nonsing_inv M)
  simp only [Matrix.conjTranspose_apply, hMh] at this
  exact this.symm

/-- Symmetry: `G(z; x, y) = conj G(conj z; y, x)`. -/
theorem eq_star_of_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {x y : X} {ψ φ : X → ℂ}
    (hψ : Memℓp ψ 2)
    (hψeq : ∀ x', ∑' w, a x' w * ψ w + ((v x' : ℂ) - z) * ψ x' = (Pi.single y 1 : X → ℂ) x')
    (hφ : Memℓp φ 2)
    (hφeq : ∀ x', ∑' w, a x' w * φ w + ((v x' : ℂ) - star z) * φ x' =
      (Pi.single x 1 : X → ℂ) x') :
    ψ x = star (φ y) := by
  have hz' : (star z).im ≠ 0 := by simpa using hz
  have h1 : Tendsto (fun Λ : Finset X => resolventColumn a v Λ z y x) atTop (𝓝 (ψ x)) :=
    (tendstoUniformly_resolventColumn_atTop ha hfin hK v hz hψ hψeq).tendsto_at x
  have h2 : Tendsto (fun Λ : Finset X => resolventColumn a v Λ (star z) x y) atTop
      (𝓝 (φ y)) :=
    (tendstoUniformly_resolventColumn_atTop ha hfin hK v hz' hφ hφeq).tendsto_at y
  have h3 := (continuous_star.tendsto _).comp h2
  refine tendsto_nhds_unique h1 (h3.congr fun Λ => ?_)
  exact (resolventColumn_eq_star ha v Λ z x y).symm

section Existence

private theorem exists_seq_mem [Countable X] (y : X) :
    ∃ Λ : ℕ → Finset X, ∀ x, ∀ᶠ n in atTop, x ∈ Λ n := by
  have : Nonempty X := ⟨y⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat X
  refine ⟨fun n => (Finset.range n).image f, fun x => ?_⟩
  obtain ⟨m, rfl⟩ := hf x
  filter_upwards [eventually_gt_atTop m] with n hn
  exact Finset.mem_image.2 ⟨m, Finset.mem_range.2 hn, rfl⟩

private theorem norm_resolventColumn_le (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0) (x y : X) :
    ‖resolventColumn a v Λ z y x‖ ≤ 1 / |z.im| := by
  have h1 : ‖resolventColumn a v Λ z y x‖ ^ 2 ≤ ∑' x, ‖resolventColumn a v Λ z y x‖ ^ 2 :=
    (summable_resolventColumn_sq a v Λ z y).le_tsum x fun j _ => by positivity
  have h2 := tsum_norm_sq_resolventColumn_le ha v Λ hz y
  have h3 : (1 / |z.im|) ^ 2 = 1 / z.im ^ 2 := by rw [div_pow, sq_abs, one_pow]
  have hpos : 0 ≤ 1 / |z.im| := by positivity
  exact le_of_sq_le_sq (h1.trans (h2.trans_eq h3.symm)) hpos

omit [DecidableEq X] in
private theorem tsum_row_eq_sum (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (x : X) (g : X → ℂ) :
    ∑' w, a x w * g w = ∑ w ∈ (hfin x).toFinset, a x w * g w :=
  tsum_eq_sum fun w hw => by
    have : a x w = 0 := by simpa using hw
    simp [this]

/-- **Existence** (countable `X`), by pointwise compactness of finite-volume columns (no row
bound is needed for existence; it enters uniqueness). -/
theorem exists_memℓp_eq_single [Countable X] (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) (y : X) :
    ∃ ψ : X → ℂ, Memℓp ψ 2 ∧
      ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x := by
  obtain ⟨Λ, hΛ⟩ := exists_seq_mem y
  set g : ℕ → X → ℂ := fun n => resolventColumn a v (Λ n) z y with hg
  have hmem : ∀ n, g n ∈ Set.pi Set.univ (fun _ : X => Metric.closedBall (0 : ℂ) (1 / |z.im|)) :=
    fun n x _ => by
      simpa using norm_resolventColumn_le ha v (Λ n) hz x y
  have hcomp : IsCompact (Set.pi Set.univ
      (fun _ : X => Metric.closedBall (0 : ℂ) (1 / |z.im|))) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨ψ, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hmem
  have hpt : ∀ x, Tendsto (fun k => g (φ k) x) atTop (𝓝 (ψ x)) :=
    fun x => tendsto_pi_nhds.1 hlim x
  have hev : ∀ x, ∀ᶠ k in atTop, x ∈ Λ (φ k) := fun x => hφ.tendsto_atTop.eventually (hΛ x)
  refine ⟨ψ, ?_, fun x => ?_⟩
  · rw [memℓp_gen_iff (by simp)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine summable_of_sum_le (c := 1 / z.im ^ 2) (fun x => by positivity) fun F => ?_
    have hl : Tendsto (fun k => ∑ x ∈ F, ‖g (φ k) x‖ ^ 2) atTop (𝓝 (∑ x ∈ F, ‖ψ x‖ ^ 2)) :=
      tendsto_finsetSum _ fun x _ => ((continuous_norm.pow 2).tendsto _).comp (hpt x)
    refine le_of_tendsto' hl fun k => ?_
    exact ((summable_resolventColumn_sq a v (Λ (φ k)) z y).sum_le_tsum F
      fun x _ => by positivity).trans (tsum_norm_sq_resolventColumn_le ha v _ hz y)
  · set S := (hfin x).toFinset with hS
    have hevS : ∀ᶠ k in atTop, ∀ w ∈ S, w ∈ Λ (φ k) :=
      (Filter.eventually_all_finset S).2 fun w _ => hev w
    have hl : Tendsto (fun k => ∑ w ∈ S, a x w * g (φ k) w + ((v x : ℂ) - z) * g (φ k) x)
        atTop (𝓝 (∑ w ∈ S, a x w * ψ w + ((v x : ℂ) - z) * ψ x)) :=
      (tendsto_finsetSum _ fun w _ => (hpt w).const_mul _).add ((hpt x).const_mul _)
    have hc : Tendsto (fun k => ∑ w ∈ S, a x w * g (φ k) w + ((v x : ℂ) - z) * g (φ k) x)
        atTop (𝓝 ((Pi.single y 1 : X → ℂ) x)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x, hevS, hev y] with k hx hS' hy
      have := resolventColumn_spec ha v (Λ (φ k)) hz hx hy
      rw [tsum_row_eq_sum hfin] at this
      exact this.symm
    rw [tsum_row_eq_sum hfin]
    exact tendsto_nhds_unique hl hc

end Existence

/-- **Existence and uniqueness** of the square-summable solution of `(a + v - z) ψ = δ_y`. -/
theorem existsUnique_memℓp_eq_single [Countable X] (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) (y : X) :
    ∃! ψ : X → ℂ, Memℓp ψ 2 ∧
      ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x := by
  obtain ⟨ψ, hψ, hψeq⟩ := exists_memℓp_eq_single ha hfin v hz y
  refine ⟨ψ, ⟨hψ, hψeq⟩, fun φ ⟨hφ, hφeq⟩ => ?_⟩
  have hs : ∀ (g : X → ℂ) x, Summable fun w => a x w * g w := fun g x =>
    summable_of_ne_finset_zero (s := (hfin x).toFinset) fun w hw => by
      have : a x w = 0 := by simpa using hw
      simp [this]
  have h0 : φ - ψ = 0 := by
    refine eq_zero_of_eq_zero ha hfin hK v hz (hφ.sub hψ) fun x => ?_
    have e : ∑' w, a x w * (φ - ψ) w = ∑' w, a x w * φ w - ∑' w, a x w * ψ w := by
      rw [← (hs φ x).tsum_sub (hs ψ x)]
      exact tsum_congr fun w => by simp [mul_sub]
    rw [e]
    have h1 := hφeq x
    have h2 := hψeq x
    simp only [Pi.sub_apply]
    linear_combination h1 - h2
  exact sub_eq_zero.1 h0

end FroehlichSpencer.Infra
