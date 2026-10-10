/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Components
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Scalar estimates used in KP Lemma 4.6
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

universe u v

/--
This single
numerical lemma supplies both the direct large-domain exclusion and the exclusion through one
inductively bounded lower-scale component.
-/
theorem lemma46_t22b_scale_gt_nine {m dρ dσ : ℕ} (hm : 1 ≤ m)
    (hρ : m ≤ 10 * dρ) (hσ : m ≤ 10 * dσ) :
    9 * (m : ℝ) < (2 ^ 16 : ℝ) * (↑(min dρ dσ) : ℝ) ^ (7 / 4 : ℝ) := by
  let x : ℝ := m
  let y : ℝ := dρ
  let z : ℝ := dσ
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hm
  have hxy : x / 10 ≤ y := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10)).2
    dsimp [x, y]
    exact_mod_cast (by simpa [Nat.mul_comm] using hρ)
  have hxz : x / 10 ≤ z := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10)).2
    dsimp [x, z]
    exact_mod_cast (by simpa [Nat.mul_comm] using hσ)
  have hxmin : x / 10 ≤ min y z := le_min hxy hxz
  have hxpow : x ≤ x ^ (7 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) ≤ 7 / 4)
    simpa [Real.rpow_one, x] using h
  have h10 : (10 : ℝ) ^ (7 / 4 : ℝ) < 100 := by
    calc
      (10 : ℝ) ^ (7 / 4 : ℝ) < (10 : ℝ) ^ (2 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        norm_num
      _ = 100 := by norm_num [Real.rpow_natCast]
  have hrecip : (1 : ℝ) / 100 < 1 / ((10 : ℝ) ^ (7 / 4 : ℝ)) := by
    apply one_div_lt_one_div_of_lt
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 10) _)
    exact h10
  have hxpow0 : 0 < x ^ (7 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hcoeff : x ^ (7 / 4 : ℝ) / 100 < (x / 10) ^ (7 / 4 : ℝ) := by
    rw [Real.div_rpow (le_of_lt (by positivity : (0 : ℝ) < x)) (by norm_num : (0 : ℝ) ≤ 10)]
    calc
      x ^ (7 / 4 : ℝ) / 100 = x ^ (7 / 4 : ℝ) * (1 / 100) := by ring
      _ < x ^ (7 / 4 : ℝ) * (1 / (10 ^ (7 / 4 : ℝ))) :=
        mul_lt_mul_of_pos_left hrecip hxpow0
      _ = x ^ (7 / 4 : ℝ) / 10 ^ (7 / 4 : ℝ) := by ring
  have hminPow : (x / 10) ^ (7 / 4 : ℝ) ≤ (min y z) ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hxmin (by norm_num)
  have hMpow : 9 * x < (2 ^ 16 : ℝ) * (x ^ (7 / 4 : ℝ) / 100) := by
    have hfactor : (9 : ℝ) < (2 ^ 16 : ℝ) / 100 := by norm_num
    nlinarith only [hx, hxpow]
  have hrealMin : (min y z) = (↑(min dρ dσ) : ℝ) := by
    simp [y, z, Nat.cast_min]
  have hfinal : 9 * x < (2 ^ 16 : ℝ) * (↑(min dρ dσ) : ℝ) ^ (7 / 4 : ℝ) := by
    rw [← hrealMin]
    calc
      9 * x < (2 ^ 16 : ℝ) * (x ^ (7 / 4 : ℝ) / 100) := hMpow
      _ < (2 ^ 16 : ℝ) * (x / 10) ^ (7 / 4 : ℝ) := by
        exact mul_lt_mul_of_pos_left hcoeff (by norm_num)
      _ ≤ (2 ^ 16 : ℝ) * (min y z) ^ (7 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hminPow (by norm_num)
  simpa [x] using hfinal

/-- A slightly smaller density cutoff still gives the strict `9m` T2.2(b) gap with KP's
constants. It provides room for the edge at an attachment to a lower-scale component. -/
theorem lemma46_t22b_scale_gt_nine_of_twelve {m dρ dσ : ℕ} (hm : 1 ≤ m)
    (hρ : m ≤ 12 * dρ) (hσ : m ≤ 12 * dσ) :
    9 * (m : ℝ) < (2 ^ 16 : ℝ) * (↑(min dρ dσ) : ℝ) ^ (7 / 4 : ℝ) := by
  let x : ℝ := m
  let y : ℝ := dρ
  let z : ℝ := dσ
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hm
  have hxy : x / 12 ≤ y := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).2
    dsimp [x, y]
    exact_mod_cast (by simpa [Nat.mul_comm] using hρ)
  have hxz : x / 12 ≤ z := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).2
    dsimp [x, z]
    exact_mod_cast (by simpa [Nat.mul_comm] using hσ)
  have hxmin : x / 12 ≤ min y z := le_min hxy hxz
  have hxpow : x ≤ x ^ (7 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) ≤ 7 / 4)
    simpa [Real.rpow_one, x] using h
  have h12 : (12 : ℝ) ^ (7 / 4 : ℝ) < 144 := by
    calc
      (12 : ℝ) ^ (7 / 4 : ℝ) < (12 : ℝ) ^ (2 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        norm_num
      _ = 144 := by norm_num [Real.rpow_natCast]
  have hrecip : (1 : ℝ) / 144 < 1 / ((12 : ℝ) ^ (7 / 4 : ℝ)) := by
    apply one_div_lt_one_div_of_lt
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 12) _)
    exact h12
  have hxpow0 : 0 < x ^ (7 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hcoeff : x ^ (7 / 4 : ℝ) / 144 < (x / 12) ^ (7 / 4 : ℝ) := by
    rw [Real.div_rpow (le_of_lt (by positivity : (0 : ℝ) < x))
      (by norm_num : (0 : ℝ) ≤ 12)]
    calc
      x ^ (7 / 4 : ℝ) / 144 = x ^ (7 / 4 : ℝ) * (1 / 144) := by ring
      _ < x ^ (7 / 4 : ℝ) * (1 / (12 ^ (7 / 4 : ℝ))) :=
        mul_lt_mul_of_pos_left hrecip hxpow0
      _ = x ^ (7 / 4 : ℝ) / 12 ^ (7 / 4 : ℝ) := by ring
  have hminPow : (x / 12) ^ (7 / 4 : ℝ) ≤ (min y z) ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hxmin (by norm_num)
  have hMpow : 9 * x < (2 ^ 16 : ℝ) * (x ^ (7 / 4 : ℝ) / 144) := by
    have hfactor : (9 : ℝ) < (2 ^ 16 : ℝ) / 144 := by norm_num
    nlinarith only [hx, hxpow]
  have hrealMin : (min y z) = (↑(min dρ dσ) : ℝ) := by
    simp [y, z, Nat.cast_min]
  have hfinal : 9 * x < (2 ^ 16 : ℝ) * (↑(min dρ dσ) : ℝ) ^ (7 / 4 : ℝ) := by
    rw [← hrealMin]
    calc
      9 * x < (2 ^ 16 : ℝ) * (x ^ (7 / 4 : ℝ) / 144) := hMpow
      _ < (2 ^ 16 : ℝ) * (x / 12) ^ (7 / 4 : ℝ) :=
        mul_lt_mul_of_pos_left hcoeff (by norm_num)
      _ ≤ (2 ^ 16 : ℝ) * (min y z) ^ (7 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hminPow (by norm_num)
  simpa [x] using hfinal

/-- At the maximal scale `m` in a finite sub-ensemble, two distinct densities with diameter at
least `m/10` cannot have adjacent enlarged domains. This is the large-scale exclusion used in
the KP Lemma 4.6 induction. -/
theorem lemma46_large_domains_not_adjacent {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
    {N₀ : Finset (V → ℤ)} {ρstar ρ σ : V → ℤ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V) {m : ℕ}
    (hm : 1 ≤ m) (hρmem : ρ ∈ N₀) (hσmem : σ ∈ N₀) (hne : ρ ≠ σ)
    (hρneutral : ∑ x, ρ x = 0) (hσneutral : ∑ x, σ x = 0)
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hσcenter : G.IsDensityCenter σ (centerOf σ))
    (hρmax : G.densityDiameter ρ ≤ m) (hσmax : G.densityDiameter σ ≤ m)
    (hρlarge : m ≤ 10 * G.densityDiameter ρ)
    (hσlarge : m ≤ 10 * G.densityDiameter σ) :
    ∀ x ∈ G.densityDomainPlus ρ (centerOf ρ),
      ∀ y ∈ G.densityDomainPlus σ (centerOf σ), ¬ G.toSimpleGraph.Adj x y := by
  intro x hx y hy hxy
  have hscale := lemma46_t22b_scale_gt_nine hm hρlarge hσlarge
  have hupperNat : 4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1 ≤ 9 * m := by
    have hm' : 1 ≤ m := hm
    omega
  have hupper : (↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1) : ℝ) ≤
      9 * (m : ℝ) := by exact_mod_cast hupperNat
  have hscale' : (↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1) : ℝ) <
      (2 ^ 16 : ℝ) * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^
        (7 / 4 : ℝ) := hupper.trans_lt hscale
  exact densityDomainPlus_no_adj_of_scale (hsep := hsep) (hG := hG)
    (centerρ := centerOf ρ) (centerσ := centerOf σ) (x := x) (y := y)
    hρmem hσmem hne hρneutral hσneutral hρcenter hσcenter hx hy hxy hscale'

/-- The same no-adjacency conclusion at the `m/12` cutoff, retaining enough scale gap to absorb
one edge in the component-merging transition. -/
theorem lemma46_large_domains_not_adjacent_of_twelve {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
    {N₀ : Finset (V → ℤ)} {ρstar ρ σ : V → ℤ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V) {m : ℕ}
    (hm : 1 ≤ m) (hρmem : ρ ∈ N₀) (hσmem : σ ∈ N₀) (hne : ρ ≠ σ)
    (hρneutral : ∑ x, ρ x = 0) (hσneutral : ∑ x, σ x = 0)
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hσcenter : G.IsDensityCenter σ (centerOf σ))
    (hρmax : G.densityDiameter ρ ≤ m) (hσmax : G.densityDiameter σ ≤ m)
    (hρlarge : m ≤ 12 * G.densityDiameter ρ)
    (hσlarge : m ≤ 12 * G.densityDiameter σ) :
    ∀ x ∈ G.densityDomainPlus ρ (centerOf ρ),
      ∀ y ∈ G.densityDomainPlus σ (centerOf σ), ¬ G.toSimpleGraph.Adj x y := by
  intro x hx y hy hxy
  have hscale := lemma46_t22b_scale_gt_nine_of_twelve hm hρlarge hσlarge
  have hupperNat : 4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1 ≤ 9 * m := by
    have hm' : 1 ≤ m := hm
    omega
  have hupper : (↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1) : ℝ) ≤
      9 * (m : ℝ) := by exact_mod_cast hupperNat
  have hscale' : (↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1) : ℝ) <
      (2 ^ 16 : ℝ) * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^
        (7 / 4 : ℝ) := hupper.trans_lt hscale
  exact densityDomainPlus_no_adj_of_scale (hsep := hsep) (hG := hG)
    (centerρ := centerOf ρ) (centerσ := centerOf σ) (x := x) (y := y)
    hρmem hσmem hne hρneutral hσneutral hρcenter hσcenter hx hy hxy hscale'

/-- The density-scale conversion in KP Lemma 4.6(1): if component diameters are at most five
 times their selected density diameters, then T2.2(b)'s `M min(dρ,dσ)^α` bound implies the
component-scale bound with the source loss `25`, for `0 ≤ α < 2`. -/
theorem lemma46_pair_scale_bound {dE dF dρ dσ : ℕ} {M α supportDist rhs : ℝ}
    (hE : dE ≤ 5 * dρ) (hF : dF ≤ 5 * dσ)
    (hM : 0 ≤ M) (hα : 0 ≤ α) (hα2 : α < 2)
    (hsep : M * (↑(min dρ dσ) : ℝ) ^ α ≤ supportDist)
    (hgeom : supportDist ≤ rhs) :
    (M / 25) * (↑(min dE dF) : ℝ) ^ α ≤ rhs := by
  have hE' : (dE : ℝ) ≤ 5 * dρ := by exact_mod_cast hE
  have hF' : (dF : ℝ) ≤ 5 * dσ := by exact_mod_cast hF
  let a : ℝ := min (dE : ℝ) dF
  let b : ℝ := min (dρ : ℝ) dσ
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hab : a ≤ 5 * b := by
    dsimp [a, b]
    by_cases h : dρ ≤ dσ
    · have hc : (dρ : ℝ) ≤ dσ := by exact_mod_cast h
      rw [min_eq_left hc]
      exact (min_le_left _ _).trans hE'
    · have hc : (dσ : ℝ) ≤ dρ := by exact_mod_cast (le_of_not_ge h)
      rw [min_eq_right hc]
      exact (min_le_right _ _).trans hF'
  have hpow : a ^ α ≤ (5 * b) ^ α := Real.rpow_le_rpow ha0 hab hα
  have hmul : (5 * b) ^ α = 5 ^ α * b ^ α :=
    Real.mul_rpow (by norm_num) hb0
  have h5 : (5 : ℝ) ^ α < 25 := by
    calc
      (5 : ℝ) ^ α < (5 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hα2
      _ = 25 := by norm_num [Real.rpow_natCast]
  have hbpow : 0 ≤ b ^ α := Real.rpow_nonneg hb0 α
  have h5b : 5 ^ α * b ^ α ≤ 25 * b ^ α :=
    mul_le_mul_of_nonneg_right h5.le hbpow
  have h25 : a ^ α ≤ 25 * b ^ α := by
    rw [hmul] at hpow
    exact hpow.trans h5b
  have hscale : (M / 25) * a ^ α ≤ M * b ^ α := by
    calc
      (M / 25) * a ^ α ≤ (M / 25) * (25 * b ^ α) :=
        mul_le_mul_of_nonneg_left h25 (div_nonneg hM (by norm_num))
      _ = M * b ^ α := by ring
  calc
    (M / 25) * (↑(min dE dF) : ℝ) ^ α = (M / 25) * a ^ α := by
      simp [a, Nat.cast_min]
    _ ≤ M * b ^ α := hscale
    _ = M * (↑(min dρ dσ) : ℝ) ^ α := by simp [b, Nat.cast_min]
    _ ≤ supportDist := hsep
    _ ≤ rhs := hgeom

/-- KP Lemma 4.6(1), after the finite-scale induction has selected a maximal density in each
component. The theorem converts T2.2(b) support separation to the source component-distance
bound, using `d(E) ≤ 5 d(ρ_E)`. -/
theorem lemma46_component_separation_bound {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {ρstar ρ σ : V → ℤ}
    {M α : ℝ} (hsep : KPTheorem22bSeparation G N₀ ρstar M α)
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (c c' : DensityPlusComponent G N₀ centerOf) (hne : ρ ≠ σ)
    (hρmem : ρ ∈ N₀) (hσmem : σ ∈ N₀)
    (hρcomponent : ρ ∈ densitiesContainedInComponent G N₀ centerOf c)
    (hσcomponent : σ ∈ densitiesContainedInComponent G N₀ centerOf c')
    (hρneutral : ∑ x, ρ x = 0) (hσneutral : ∑ x, σ x = 0)
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hσcenter : G.IsDensityCenter σ (centerOf σ))
    (hρsupport : ∃ x, ρ x ≠ 0) (hσsupport : ∃ y, σ y ≠ 0)
    (hE : densityPlusComponentDiameter G N₀ centerOf c ≤ 5 * G.densityDiameter ρ)
    (hF : densityPlusComponentDiameter G N₀ centerOf c' ≤ 5 * G.densityDiameter σ)
    (hM : 0 ≤ M) (hα : 0 ≤ α) (hα2 : α < 2) :
    (M / 25) *
        (↑(min (densityPlusComponentDiameter G N₀ centerOf c)
          (densityPlusComponentDiameter G N₀ centerOf c')) : ℝ) ^ α ≤
      (↑(densityPlusComponentDistance G N₀ centerOf c c' +
        densityPlusComponentDiameter G N₀ centerOf c +
        densityPlusComponentDiameter G N₀ centerOf c') : ℝ) := by
  have hsep' := hsep.neutral_pair ρ hρmem σ hσmem hne
  have hgeom := densitySupportDistance_le_componentDistance_add G hG N₀ centerOf c c'
    hρcomponent hσcomponent hρneutral hσneutral hρcenter hσcenter hρsupport hσsupport
  have hgeom' : (↑(densitySupportDistance G ρ σ) : ℝ) ≤
      (↑(densityPlusComponentDistance G N₀ centerOf c c' +
        densityPlusComponentDiameter G N₀ centerOf c +
        densityPlusComponentDiameter G N₀ centerOf c') : ℝ) := by
    exact_mod_cast hgeom
  exact lemma46_pair_scale_bound hE hF hM hα hα2 hsep' hgeom'

/-- The root-distance scale arithmetic of KP Lemma 4.6(2), with `M₀=2^16`, `α=7/4`,
`d(E)≥4`, and `d(E)≤5d(ρ_E)`. This is the numerical inequality used after applying
T2.2(b) and the triangle bound from the component to the charged support. -/
theorem lemma46_root_scale_bound {dE dρ : ℕ} (hdE : 4 ≤ dE)
    (hscale : dE ≤ 5 * dρ) :
    ((2 ^ 16 : ℝ) / 128) * (dE : ℝ) ^ (7 / 4 : ℝ) + dE ≤
      (2 ^ 16 : ℝ) * (dρ : ℝ) ^ (7 / 4 : ℝ) := by
  let d : ℝ := dE
  let q : ℝ := dρ
  have hd0 : 0 < d := by dsimp [d]; exact_mod_cast (by omega : 0 < dE)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hscale' : d ≤ 5 * q := by
    dsimp [d, q]
    exact_mod_cast hscale
  have hdiv : d / 5 ≤ q := (div_le_iff₀ (by norm_num)).2 (by nlinarith only [hscale'])
  have hpowDiv : (d / 5) ^ (7 / 4 : ℝ) = d ^ (7 / 4 : ℝ) / 5 ^ (7 / 4 : ℝ) :=
    Real.div_rpow (le_of_lt hd0) (by norm_num : 0 ≤ (5 : ℝ)) _
  have h5 : (5 : ℝ) ^ (7 / 4 : ℝ) < 25 := by
    calc
      (5 : ℝ) ^ (7 / 4 : ℝ) < (5 : ℝ) ^ (2 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        norm_num
      _ = 25 := by norm_num [Real.rpow_natCast]
  have hrecip : (1 : ℝ) / 25 ≤ 1 / ((5 : ℝ) ^ (7 / 4 : ℝ)) := by
    apply one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by norm_num : 0 < (5 : ℝ)) _)
    exact le_of_lt h5
  have hdPow0 : 0 ≤ d ^ (7 / 4 : ℝ) := Real.rpow_nonneg (le_of_lt hd0) _
  have hquarter : d ^ (7 / 4 : ℝ) / 25 ≤ (d / 5) ^ (7 / 4 : ℝ) := by
    rw [hpowDiv]
    calc
      d ^ (7 / 4 : ℝ) / 25 = d ^ (7 / 4 : ℝ) * (1 / 25) := by ring
      _ ≤ d ^ (7 / 4 : ℝ) * (1 / (5 ^ (7 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hrecip hdPow0
      _ = d ^ (7 / 4 : ℝ) / 5 ^ (7 / 4 : ℝ) := by ring
  have hmonotone : (d / 5) ^ (7 / 4 : ℝ) ≤ q ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hdiv (by norm_num)
  have hqBound : d ^ (7 / 4 : ℝ) / 25 ≤ q ^ (7 / 4 : ℝ) := hquarter.trans hmonotone
  have hdge1 : 1 ≤ d := by dsimp [d]; exact_mod_cast (by omega : 1 ≤ dE)
  have hdPowLe : d ≤ d ^ (7 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hdge1 (by norm_num : (1 : ℝ) ≤ 7 / 4)
    simpa [Real.rpow_one, d] using h
  have hconst : (2 ^ 16 : ℝ) * (1 / 25 - 1 / 128) ≥ 1 := by norm_num
  have hdge : d ≤ (2 ^ 16 : ℝ) * (1 / 25 - 1 / 128) * d ^ (7 / 4 : ℝ) := by
    calc
      d ≤ d ^ (7 / 4 : ℝ) := hdPowLe
      _ ≤ (2 ^ 16 : ℝ) * (1 / 25 - 1 / 128) * d ^ (7 / 4 : ℝ) := by
        have hp := mul_le_mul_of_nonneg_right hconst
          (le_of_lt (Real.rpow_pos_of_pos hd0 (7 / 4 : ℝ)))
        simpa using hp
  have hgap : ((2 ^ 16 : ℝ) / 128) * d ^ (7 / 4 : ℝ) + d ≤
      (2 ^ 16 : ℝ) / 25 * d ^ (7 / 4 : ℝ) := by
    have h := hdge
    rw [show (2 ^ 16 : ℝ) * (1 / 25 - 1 / 128) =
        (2 ^ 16 : ℝ) / 25 - (2 ^ 16 : ℝ) / 128 by ring] at h
    linarith only [hdge]
  have hmul : (2 ^ 16 : ℝ) / 25 * d ^ (7 / 4 : ℝ) ≤
      (2 ^ 16 : ℝ) * q ^ (7 / 4 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hqBound (by norm_num : 0 ≤ (2 ^ 16 : ℝ))
    calc
      (2 ^ 16 : ℝ) / 25 * d ^ (7 / 4 : ℝ) =
          (2 ^ 16 : ℝ) * (d ^ (7 / 4 : ℝ) / 25) := by ring
      _ ≤ (2 ^ 16 : ℝ) * q ^ (7 / 4 : ℝ) := this
  change ((2 ^ 16 : ℝ) / 128) * d ^ (7 / 4 : ℝ) + d ≤
    (2 ^ 16 : ℝ) * q ^ (7 / 4 : ℝ)
  exact hgap.trans hmul

/-- KP Lemma 4.6(2), after the finite-scale induction has selected the maximal density in the
component and proved `d(E) ≤ 5 d(ρ_E)`. The component-to-root distance is measured from the
component vertex set to the support of the distinguished charged density. -/
theorem lemma46_component_root_separation_bound {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
    {N₀ : Finset (V → ℤ)} {ρstar ρ : V → ℤ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf)
    (hρmem : ρ ∈ N₀) (hne : ρ ≠ ρstar)
    (hρcomponent : ρ ∈ densitiesContainedInComponent G N₀ centerOf c)
    (hρneutral : ∑ x, ρ x = 0)
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hρsupport : ∃ x, ρ x ≠ 0) (hrootSupport : ∃ y, ρstar y ≠ 0)
    (hdE : 4 ≤ densityPlusComponentDiameter G N₀ centerOf c)
    (hE : densityPlusComponentDiameter G N₀ centerOf c ≤ 5 * G.densityDiameter ρ) :
    ((2 ^ 16 : ℝ) / 128) *
        (↑(densityPlusComponentDiameter G N₀ centerOf c) : ℝ) ^ (7 / 4 : ℝ) ≤
      (↑(densityPlusComponentRootDistance G N₀ centerOf c ρstar) : ℝ) := by
  have hsep' := hsep.root_pair ρ hρmem hne
  have hgeom := densitySupportDistance_le_componentRootDistance_add G hG N₀ centerOf c
    hρcomponent hρneutral hρcenter hρsupport hrootSupport
  have hgeom' : (↑(densitySupportDistance G ρ ρstar) : ℝ) ≤
      (↑(densityPlusComponentRootDistance G N₀ centerOf c ρstar) : ℝ) +
        densityPlusComponentDiameter G N₀ centerOf c := by
    exact_mod_cast hgeom
  have hscale := lemma46_root_scale_bound hdE hE
  linarith only [hsep', hgeom', hscale]

end FroehlichSpencer.BKT.SpinWaves

end
