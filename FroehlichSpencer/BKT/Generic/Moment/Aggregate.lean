/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.ExpMoment.Claim32
public import FroehlichSpencer.BKT.ExpMoment.Claim32Threshold
public import FroehlichSpencer.BKT.SpinWaves.SquareGeometry
public import FroehlichSpencer.BKT.Charges.DensityBall

/-!
# The aggregate packing estimate with linear charge norms (generic core)

Densities of one
scale have disjoint domains, and the activity decay `2^{-k}` pays for the scales.

* the activity decays in the **linear** norm `∑_x |ϱ(x)|`, not in `∑_x ϱ(x)²`, because the
  non-Gaussian energy gain is linear in the charges ;
* the per-density error has an arbitrary polynomial weight `K₀ (d+1)^p ‖ϱ‖₁^q`;
* the edge weights are summed over the edges **touching** the domain (at least one endpoint in
  `D(ϱ)`), not only the edges inside it.

Each edge touches at most two domains of one scale, which
  costs a factor two.

Statements:

* `sum_abs_mul_le_of_touching`: `∑_ϱ |z(ϱ)| P(ϱ) ≤ ε ∑_e w(e)` under the threshold
  `2K₀(d+1)^{p+1} u^q e^{-b(u + log₂(d+1))} ≤ ε` for `d ≥ 1`, `u ≥ 2`;
* `exists_touching_threshold`: that threshold holds with `ε = C e^{-b}` once `b ≥ b₀`;
* `card_edgesTouching_le` (degree four): `|∂⁺S| ≤ 4|S|`, and on KP's square domains
  `|edges touching D(ϱ)| ≤ 64 (d+1)²`.

The `claim32_of_pairing_le` is not generalized in place; its proof is adapted here.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open Finset

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E]

/-- The edges with at least one endpoint in `S`. -/
def edgesTouching (G : Multigraph V E) (S : Set V) : Finset E := by
  classical
  exact univ.filter fun e => G.src e ∈ S ∨ G.tgt e ∈ S

omit [Fintype V] in
theorem mem_edgesTouching (G : Multigraph V E) {S : Set V} {e : E} :
    e ∈ edgesTouching G S ↔ G.src e ∈ S ∨ G.tgt e ∈ S := by
  classical
  simp [edgesTouching]

omit [Fintype V] in
/-- The edges inside a set touch it. -/
theorem edgesWithin_subset_edgesTouching (G : Multigraph V E) (S : Set V) :
    G.edgesWithin S ⊆ edgesTouching G S := fun _ he =>
  (mem_edgesTouching G).mpr (Or.inl ((G.mem_edgesWithin).mp he).1)

/-- A nonzero neutral integer density has `∑_x |ϱ(x)| ≥ 2`. -/
theorem two_le_sum_abs_of_neutral (ρ : V → ℤ) (hρ : ρ ≠ 0) (hsum : ∑ x, ρ x = 0) :
    (2 : ℝ) ≤ ∑ j, |(ρ j : ℝ)| := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, ρ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hρ (funext h)
  obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ ρ y ≠ 0 := by
    by_contra h
    push Not at h
    have : ∑ j, ρ j = ρ x := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
      rw [Finset.sum_eq_zero fun j hj => h j (Finset.ne_of_mem_erase hj), zero_add]
    exact hx (this ▸ hsum)
  have h1 : (1 : ℝ) ≤ |(ρ x : ℝ)| := by
    have := Int.one_le_abs hx
    rw [← Int.cast_abs]; exact_mod_cast this
  have h2 : (1 : ℝ) ≤ |(ρ y : ℝ)| := by
    have := Int.one_le_abs hy
    rw [← Int.cast_abs]; exact_mod_cast this
  have hpair : |(ρ x : ℝ)| + |(ρ y : ℝ)| ≤ ∑ j, |(ρ j : ℝ)| := by
    have hsub : ({x, y} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => abs_nonneg (ρ j : ℝ))
    rwa [Finset.sum_pair hyx.symm] at this
  linarith

/-- An edge touches at most two domains of one scale, so the touching sums of a family with
pairwise disjoint domains add up to at most twice the total edge weight. -/
theorem sum_touching_le_two_mul (G : Multigraph V E) (wt : E → ℝ) (hwt : ∀ e, 0 ≤ wt e)
    (C : Finset (V → ℤ)) (D : (V → ℤ) → Set V)
    (hdisj : ∀ ρ ∈ C, ∀ ρ' ∈ C, ρ ≠ ρ' → D ρ ∩ D ρ' = ∅) :
    ∑ ρ ∈ C, ∑ e ∈ edgesTouching G (D ρ), wt e ≤ 2 * ∑ e, wt e := by
  classical
  have hswap : ∑ ρ ∈ C, ∑ e ∈ edgesTouching G (D ρ), wt e =
      ∑ e, wt e * ((C.filter fun ρ => e ∈ edgesTouching G (D ρ)).card : ℝ) := by
    have h1 : ∀ ρ, ∑ e ∈ edgesTouching G (D ρ), wt e =
        ∑ e, if e ∈ edgesTouching G (D ρ) then wt e else 0 := fun ρ => by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hone : ∀ x : V, (C.filter fun ρ => x ∈ D ρ).card ≤ 1 := by
    intro x
    refine Finset.card_le_one.mpr fun ρ hρ ρ' hρ' => ?_
    obtain ⟨hρC, hxρ⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hρ'C, hxρ'⟩ := Finset.mem_filter.mp hρ'
    by_contra hne
    have : x ∈ D ρ ∩ D ρ' := ⟨hxρ, hxρ'⟩
    rw [hdisj ρ hρC ρ' hρ'C hne] at this
    exact this
  have hcount : ∀ e, ((C.filter fun ρ => e ∈ edgesTouching G (D ρ)).card : ℝ) ≤ 2 := by
    intro e
    have hsub : (C.filter fun ρ => e ∈ edgesTouching G (D ρ)) ⊆
        (C.filter fun ρ => G.src e ∈ D ρ) ∪ (C.filter fun ρ => G.tgt e ∈ D ρ) := by
      intro ρ hρ
      obtain ⟨hρC, he⟩ := Finset.mem_filter.mp hρ
      rcases (mem_edgesTouching G).mp he with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hρC, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hρC, h⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 : (C.filter fun ρ => e ∈ edgesTouching G (D ρ)).card ≤ 2 := by
      have := hone (G.src e); have := hone (G.tgt e); omega
    exact_mod_cast h2
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [mul_comm 2]
  exact mul_le_mul_of_nonneg_left (hcount e) (hwt e)

/-- **The packing estimate with linear charge norms, at chosen centers** (KP Claim 3.2, ;
FS81 (6.40)–(6.44), ). For a choice `ctr` of admissible centers, if
`P(ϱ) ≤ K₀ (d+1)^p ‖ϱ‖₁^q ∑_{e touching D_{ctr ϱ}(ϱ)} w(e)`, the activities decay as
`e^{-b(‖ϱ‖₁ + log₂(d+1))}`, and the threshold holds, then `∑_ϱ |z(ϱ)| P(ϱ) ≤ ε ∑_e w(e)`. -/
theorem sum_abs_mul_le_of_touching_center (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected)
    (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (p q : ℕ) (wt : E → ℝ) (hwt : ∀ e, 0 ≤ wt e) (P : (V → ℤ) → ℝ)
    (N : Finset (V → ℤ)) (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (ctr : (V → ℤ) → V) (hctr : ∀ ρ ∈ N, G.IsDensityCenter ρ (ctr ρ))
    (hP : ∀ ρ ∈ N,
      P ρ ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ p * (∑ x, |(ρ x : ℝ)|) ^ q *
        ∑ e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)), wt e)
    (hdisj : ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
      G.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      G.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      ∀ j₁ j₂ : V, G.IsDensityCenter ϱ₁ j₁ → G.IsDensityCenter ϱ₂ j₂ →
        G.densityDomain ϱ₁ j₁ ∩ G.densityDomain ϱ₂ j₂ = ∅)
    (z : (V → ℤ) → ℝ) (b ε : ℝ)
    (hz : ∀ ρ ∈ N, |z ρ| ≤
      Real.exp (-b * (∑ x, |(ρ x : ℝ)| + Real.logb 2 (G.densityDiameter ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * K₀ * (d + 1) ^ (p + 1) * u ^ q * Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε) :
    ∑ ρ ∈ N, |z ρ| * P ρ ≤ ε * ∑ e, wt e := by
  classical
  set d : (V → ℤ) → ℕ := fun ρ => G.densityDiameter ρ with hd
  set A : (V → ℤ) → ℝ := fun ρ =>
    ∑ e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)), wt e with hA
  set T : ℝ := ∑ e, wt e with hT
  set kf : (V → ℤ) → ℕ := fun ρ => Nat.log 2 (d ρ + 1) with hkf
  have hε : 0 ≤ ε := by
    refine le_trans ?_ (hthr 1 2 le_rfl le_rfl)
    positivity
  have hd1 : ∀ ρ ∈ N, 1 ≤ d ρ := fun ρ hρ =>
    G.one_le_densityDiameter_of_neutral hG ρ (hne ρ hρ) (hneutral ρ hρ)
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => Finset.sum_nonneg fun e _ => hwt e
  have hk1 : ∀ ρ ∈ N, 1 ≤ kf ρ := fun ρ hρ =>
    Nat.log_pos (by norm_num) (by have := hd1 ρ hρ; omega)
  have hklow : ∀ ρ, 2 ^ kf ρ ≤ d ρ + 1 := fun ρ => Nat.pow_log_le_self 2 (by omega)
  have hkup : ∀ ρ, d ρ + 1 < 2 ^ (kf ρ + 1) := fun ρ => Nat.lt_pow_succ_log_self (by norm_num) _
  -- the per-density bound with the damping
  have hper : ∀ ρ ∈ N, |z ρ| * P ρ ≤ ε / 2 * ((1 / 2 : ℝ) ^ kf ρ * A ρ) := by
    intro ρ hρ
    have hdR : (1 : ℝ) ≤ (d ρ : ℝ) := by exact_mod_cast hd1 ρ hρ
    have hu := two_le_sum_abs_of_neutral ρ (hne ρ hρ) (hneutral ρ hρ)
    have hPρ := hP ρ hρ
    have hthr' := hthr (d ρ) (∑ j, |(ρ j : ℝ)|) hdR hu
    have hzρ := hz ρ hρ
    set u := ∑ j, |(ρ j : ℝ)|
    set X := Real.exp (-b * (u + Real.logb 2 ((d ρ : ℝ) + 1)))
    have hdpos : (0 : ℝ) < (d ρ : ℝ) + 1 := by linarith
    have hinv : 1 / ((d ρ : ℝ) + 1) ≤ (1 / 2 : ℝ) ^ kf ρ := by
      have h2 : ((2 ^ kf ρ : ℕ) : ℝ) ≤ (d ρ : ℝ) + 1 := by exact_mod_cast hklow ρ
      rw [Nat.cast_pow, Nat.cast_ofNat] at h2
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h2
    have hu0 : 0 ≤ u := by positivity
    have hzK : |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ p * u ^ q) ≤ ε / 2 / ((d ρ : ℝ) + 1) := by
      rw [le_div_iff₀ hdpos, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ p * u ^ q) * ((d ρ : ℝ) + 1) * 2
          = |z ρ| * (2 * K₀ * ((d ρ : ℝ) + 1) ^ (p + 1) * u ^ q) := by ring
        _ ≤ X * (2 * K₀ * ((d ρ : ℝ) + 1) ^ (p + 1) * u ^ q) :=
            mul_le_mul_of_nonneg_right hzρ (by positivity)
        _ = 2 * K₀ * ((d ρ : ℝ) + 1) ^ (p + 1) * u ^ q * X := by ring
        _ ≤ ε := hthr'
    calc |z ρ| * P ρ
        ≤ |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ p * u ^ q * A ρ) :=
          mul_le_mul_of_nonneg_left hPρ (abs_nonneg _)
      _ = (|z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ p * u ^ q)) * A ρ := by ring
      _ ≤ (ε / 2 / ((d ρ : ℝ) + 1)) * A ρ := mul_le_mul_of_nonneg_right hzK (hA0 ρ)
      _ = ε / 2 * (1 / ((d ρ : ℝ) + 1) * A ρ) := by ring
      _ ≤ ε / 2 * ((1 / 2 : ℝ) ^ kf ρ * A ρ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv (hA0 ρ)) (by positivity)
  -- within one scale every edge touches at most two domains
  have hclass : ∀ k ∈ N.image kf, ∑ ρ ∈ N with kf ρ = k, A ρ ≤ 2 * T := by
    intro k _
    refine sum_touching_le_two_mul G wt hwt _ (fun ρ => G.densityDomain ρ (ctr ρ)) ?_
    intro ρ hρ ρ' hρ' hne'
    have hρN := (Finset.mem_filter.mp hρ).1
    have hρ'N := (Finset.mem_filter.mp hρ').1
    have hkρ : kf ρ = k := (Finset.mem_filter.mp hρ).2
    have hkρ' : kf ρ' = k := (Finset.mem_filter.mp hρ').2
    have hk : 1 ≤ k := hkρ ▸ hk1 ρ hρN
    have hIcc : ∀ x ∈ N, kf x = k →
        G.densityDiameter x ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) := by
      intro x _ hkx
      have hl := hklow x
      have hu := hkup x
      rw [hkx] at hl hu
      simp only [hd] at hl hu
      generalize 2 ^ k = P at hl hu ⊢
      generalize 2 ^ (k + 1) = Q at hl hu ⊢
      exact ⟨by omega, by omega⟩
    exact hdisj ρ hρN ρ' hρ'N hne' k hk (hIcc ρ hρN hkρ) (hIcc ρ' hρ'N hkρ')
      (ctr ρ) (ctr ρ') (hctr ρ hρN) (hctr ρ' hρ'N)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun e _ => hwt e
  have hgeom : ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k ≤ 1 := by
    refine sum_half_pow_le_one _ fun k hk => ?_
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hk
    exact hk1 ρ hρ
  calc ∑ ρ ∈ N, |z ρ| * P ρ
      ≤ ∑ ρ ∈ N, ε / 2 * ((1 / 2 : ℝ) ^ kf ρ * A ρ) := Finset.sum_le_sum hper
    _ = ε / 2 * ∑ ρ ∈ N, (1 / 2 : ℝ) ^ kf ρ * A ρ := by rw [Finset.mul_sum]
    _ ≤ ε / 2 * (2 * T) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Finset.sum_fiberwise_of_maps_to (t := N.image kf)
          (fun ρ hρ => Finset.mem_image_of_mem kf hρ)]
        calc ∑ k ∈ N.image kf, ∑ ρ ∈ N with kf ρ = k, (1 / 2 : ℝ) ^ kf ρ * A ρ
            = ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k * ∑ ρ ∈ N with kf ρ = k, A ρ := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ρ hρ => ?_
              rw [(Finset.mem_filter.mp hρ).2]
          _ ≤ ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k * (2 * T) :=
              Finset.sum_le_sum fun k hk =>
                mul_le_mul_of_nonneg_left (hclass k hk) (by positivity)
          _ = (∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k) * (2 * T) := by rw [Finset.sum_mul]
          _ ≤ 1 * (2 * T) := mul_le_mul_of_nonneg_right hgeom (by positivity)
          _ = 2 * T := one_mul _
    _ = ε * T := by ring

/-- **The packing estimate with linear charge norms** (KP Claim 3.2, ; FS81 (6.40)–(6.44),
). If `P(ϱ) ≤ K₀ (d+1)^p ‖ϱ‖₁^q ∑_{e touching D_j(ϱ)} w(e)` at every admissible center,
the activities decay as `e^{-b(‖ϱ‖₁ + log₂(d+1))}`, and the threshold holds, then
`∑_ϱ |z(ϱ)| P(ϱ) ≤ ε ∑_e w(e)`. -/
theorem sum_abs_mul_le_of_touching (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (p q : ℕ) (wt : E → ℝ) (hwt : ∀ e, 0 ≤ wt e) (P : (V → ℤ) → ℝ)
    (N : Finset (V → ℤ)) (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (hP : ∀ ρ ∈ N, ∀ j : V, G.IsDensityCenter ρ j →
      P ρ ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ p * (∑ x, |(ρ x : ℝ)|) ^ q *
        ∑ e ∈ edgesTouching G (G.densityDomain ρ j), wt e)
    (hdisj : ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
      G.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      G.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      ∀ j₁ j₂ : V, G.IsDensityCenter ϱ₁ j₁ → G.IsDensityCenter ϱ₂ j₂ →
        G.densityDomain ϱ₁ j₁ ∩ G.densityDomain ϱ₂ j₂ = ∅)
    (z : (V → ℤ) → ℝ) (b ε : ℝ)
    (hz : ∀ ρ ∈ N, |z ρ| ≤
      Real.exp (-b * (∑ x, |(ρ x : ℝ)| + Real.logb 2 (G.densityDiameter ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * K₀ * (d + 1) ^ (p + 1) * u ^ q * Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε) :
    ∑ ρ ∈ N, |z ρ| * P ρ ≤ ε * ∑ e, wt e := by
  classical
  have hcenter : ∀ ρ : V → ℤ, ∃ j : V, ρ ≠ 0 → G.IsDensityCenter ρ j := by
    intro ρ
    by_cases h : ρ = 0
    · obtain ⟨j⟩ := hG.nonempty
      exact ⟨j, fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := G.exists_isDensityCenter ρ h
      exact ⟨j, fun _ => hj⟩
  choose ctr hctr using hcenter
  exact sum_abs_mul_le_of_touching_center G hG K₀ hK₀ p q wt hwt P N hne hneutral ctr
    (fun ρ hρ => hctr ρ (hne ρ hρ)) (fun ρ hρ => hP ρ hρ (ctr ρ) (hctr ρ (hne ρ hρ))) hdisj z b
    ε hz hthr

/-- `(d+1)^n ≤ exp(n log₂(d+1))` for `d ≥ 1`. -/
lemma pow_le_exp_logb {d : ℝ} (hd : 1 ≤ d) (n : ℕ) :
    (d + 1) ^ n ≤ Real.exp (n * Real.logb 2 (d + 1)) := by
  have hpos : 0 < d + 1 := by linarith
  have hl : Real.log (d + 1) ≤ Real.logb 2 (d + 1) := by
    have h2 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num)
      linarith
    have hw : 0 ≤ Real.log (d + 1) := Real.log_nonneg (by linarith)
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    nlinarith
  have : (d + 1) ^ n = Real.exp (n * Real.log (d + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  rw [this]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n))

/-- **The threshold of the packing estimate** holds with `ε = C e^{-b}` for `b ≥ p + 2`. -/
theorem exists_touching_threshold (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (p q : ℕ) :
    ∃ C b₀ : ℝ, 0 ≤ C ∧ 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * K₀ * (d + 1) ^ (p + 1) * u ^ q * Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤
        C * Real.exp (-b) := by
  refine ⟨2 * K₀ * (q.factorial : ℝ) * Real.exp ((p : ℝ) + 3), (p : ℝ) + 2, by positivity,
    by positivity, fun b hb d u hd hu => ?_⟩
  have hw : 1 ≤ Real.logb 2 (d + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  set w := Real.logb 2 (d + 1)
  have h1 : (d + 1) ^ (p + 1) ≤ Real.exp (((p + 1 : ℕ) : ℝ) * w) := pow_le_exp_logb hd (p + 1)
  have h2 : u ^ q ≤ (q.factorial : ℝ) * Real.exp u := by
    have := Real.pow_div_factorial_le_exp u (by linarith) q
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hexp : Real.exp (((p + 1 : ℕ) : ℝ) * w) * Real.exp u * Real.exp (-b * (u + w)) ≤
      Real.exp ((p : ℝ) + 3) * Real.exp (-b) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    have hb1 : 0 ≤ b - (p : ℝ) - 1 := by linarith
    have hb2 : 0 ≤ b - 1 := by have := Nat.cast_nonneg (α := ℝ) p; linarith
    nlinarith [mul_le_mul_of_nonneg_left hw hb1, mul_le_mul_of_nonneg_left hu hb2]
  calc 2 * K₀ * (d + 1) ^ (p + 1) * u ^ q * Real.exp (-b * (u + w))
      ≤ 2 * K₀ * Real.exp (((p + 1 : ℕ) : ℝ) * w) * ((q.factorial : ℝ) * Real.exp u) *
          Real.exp (-b * (u + w)) := by
        gcongr
    _ = 2 * K₀ * (q.factorial : ℝ) *
          (Real.exp (((p + 1 : ℕ) : ℝ) * w) * Real.exp u * Real.exp (-b * (u + w))) := by ring
    _ ≤ 2 * K₀ * (q.factorial : ℝ) * (Real.exp ((p : ℝ) + 3) * Real.exp (-b)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * K₀ * (q.factorial : ℝ) * Real.exp ((p : ℝ) + 3) * Real.exp (-b) := by ring

omit [Fintype V] in
/-- **Edge volume of the touching set** on a graph of endpoint degree at most four:
`|edges touching S| ≤ 4 |S|`. -/
theorem card_edgesTouching_le [DecidableEq V] (G : Multigraph V E)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4) (S : Finset V) :
    (edgesTouching G (S : Set V)).card ≤ 4 * S.card := by
  classical
  have hsub : edgesTouching G (S : Set V) ⊆ S.biUnion fun x =>
      (Finset.univ.filter fun e => G.src e = x) ∪ (Finset.univ.filter fun e => G.tgt e = x) := by
    intro e he
    rcases (mem_edgesTouching G).mp he with h | h
    · exact Finset.mem_biUnion.mpr ⟨G.src e, h, Finset.mem_union_left _ (by simp)⟩
    · exact Finset.mem_biUnion.mpr ⟨G.tgt e, h, Finset.mem_union_right _ (by simp)⟩
  calc (edgesTouching G (S : Set V)).card
      ≤ (S.biUnion fun x => (Finset.univ.filter fun e => G.src e = x) ∪
          (Finset.univ.filter fun e => G.tgt e = x)).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ S, ((Finset.univ.filter fun e => G.src e = x) ∪
          (Finset.univ.filter fun e => G.tgt e = x)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, 4 := Finset.sum_le_sum fun x _ => (Finset.card_union_le _ _).trans (hdeg x)
    _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The touching edges of a set of `n`-element vertex count are at most `4n`, for a set given as
`Set V` of finite cardinality. -/
theorem card_edgesTouching_le_ncard [DecidableEq V] (G : Multigraph V E)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4) (S : Set V) :
    (edgesTouching G S).card ≤ 4 * S.ncard := by
  classical
  set F := Finset.univ.filter fun x => x ∈ S
  have hF : S = (F : Set V) := by ext x; simp [F]
  rw [hF, Set.ncard_coe_finset]
  exact card_edgesTouching_le G hdeg F

/-- The touching edges of a domain on KP's free square: `≤ 64 (d+1)²`. -/
theorem card_edgesTouching_densityDomain_squareFree_le {L : ℕ} (hL : 1 < L)
    (ρ : Fin L × Fin L → ℤ) (j : Fin L × Fin L) :
    ((edgesTouching (squareFree L) ((squareFree L).densityDomain ρ j)).card : ℝ) ≤
      64 * (((squareFree L).densityDiameter ρ : ℝ) + 1) ^ 2 := by
  have h := card_edgesTouching_le_ncard (squareFree L)
    (SpinWaves.squareFreeBipartiteDegreeFour L hL).endpointDegree_le_four
    ((squareFree L).densityDomain ρ j)
  have h2 := ncard_densityDomain_squareFree_le L ρ j
  have : (edgesTouching (squareFree L) ((squareFree L).densityDomain ρ j)).card ≤
      64 * ((squareFree L).densityDiameter ρ + 1) ^ 2 := by omega
  exact_mod_cast this

/-- The touching edges of a domain on KP's even periodic square: `≤ 64 (d+1)²`. -/
theorem card_edgesTouching_densityDomain_squarePeriodic_le {L : ℕ} (hL : 1 < L) (hEven : Even L)
    (ρ : Fin L × Fin L → ℤ) (j : Fin L × Fin L) :
    ((edgesTouching (squarePeriodic L) ((squarePeriodic L).densityDomain ρ j)).card : ℝ) ≤
      64 * (((squarePeriodic L).densityDiameter ρ : ℝ) + 1) ^ 2 := by
  have h := card_edgesTouching_le_ncard (squarePeriodic L)
    (SpinWaves.squarePeriodicBipartiteDegreeFour L hEven hL).endpointDegree_le_four
    ((squarePeriodic L).densityDomain ρ j)
  have h2 := ncard_densityDomain_squarePeriodic_le L ρ j
  have : (edgesTouching (squarePeriodic L) ((squarePeriodic L).densityDomain ρ j)).card ≤
      64 * ((squarePeriodic L).densityDiameter ρ + 1) ^ 2 := by omega
  exact_mod_cast this

end FroehlichSpencer.BKT.Generic

end
