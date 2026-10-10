/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Prop47Statements
public import FroehlichSpencer.BKT.SpinWaves.Prop47Geometry
import FroehlichSpencer.BKT.SpinWaves.ComponentCubeSum
import FroehlichSpencer.BKT.SpinWaves.LatticePacking
import FroehlichSpencer.BKT.SpinWaves.SquareGeometry
import FroehlichSpencer.BKT.Charges.DensityBall
import FroehlichSpencer.BKT.Charges.SeparatedPatch

/-!
# KP Proposition 4.7 from Lemma 4.6

For a separated square `s ∈ 𝒮_k^sep(ϱ*)` put `n = 2^k`, `S = 2^{k-1}`, `r = ⌈2^{k-3}⌉ = 2^{k-3}`,
let `ψ` be the ramp `clamp((S + 1 - dist(·, s))/(S + 1 - r), 0, 1)`, and let `ψ̃` be `ψ` flattened on
the components of `⋃_{ϱ' ∈ 𝒩₀(ϱ*)} D⁺(ϱ')` (`FlattenedWave.lean`).

The wave is
`a = q / (4096 β) · ψ̃`, where `q = ∑_{j ∈ s} ϱ*(j) ≠ 0` is the patch charge (

This is
's sign-corrected optimal multiple `ε_q γ` with `C_* = 4096`, and it serves every `k ≥ 1`
('s small-scale taper is the same ramp).

* Clauses (1)–(3): the ramp vanishes beyond `S` and is `1` within `r`; flattening keeps both
  because a component meeting `dist ≤ S + 1` has diameter `≤ n/200 < S - r` (L4.6(2) and
  `dist(E, ϱ*) ≤ S + 1 + 2(n - 1)`, the repaired  bound), and every `D⁺(ϱ')` lies in one
  component.
* Pairing: components avoid `supp ϱ*` (L4.6(2)), the ramp is `1` on `s` and `0` on the rest of the
  support (separation `R_k > 32 n`), so `⟨ψ̃, ϱ*⟩ = q`.
* Energy: `energy_flatten_ramp_le` with `|{dist ≤ S+1}| ≤ 25 n²` (ball count), `S + 1 - r ≥ n/4`,
  `|∂^ext E| ≤ 64 d(E)` (L4.6(3)) and `∑_{relevant E} d(E)³ ≤ n²/50`
  (`sum_cube_le_of_scale_separation`, from L4.6(1)–(2) and the lattice packing count) gives
  `energy(ψ̃) ≤ 1600 + 16384/50 < 4096`.

Hence
  `E_β(a, ϱ*) = q²/(4096 β) - (β/2) (q/(4096 β))² energy(ψ̃) ≥ q²/(8192 β) ≥ 1/(8192 β)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SpinWaves.P47

open Reduction

/-! ## Scalar algebra -/

section Algebra

variable {V : Type} {E : Type} [Fintype E]

/-- The energy is quadratic: `energy(c f) = c² energy(f)`. -/
theorem energy_const_mul (G : Multigraph V E) (c : ℝ) (f : V → ℝ) :
    G.energy (fun j => c * f j) = c ^ 2 * G.energy f := by
  unfold Multigraph.energy Multigraph.grad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The pairing is linear in the wave. -/
theorem pairing_const_mul [Fintype V] (c : ℝ) (f : V → ℝ) (ϱ : V → ℤ) :
    Multigraph.pairing (fun j => c * f j) (fun j => (ϱ j : ℝ)) =
      c * Multigraph.pairing f (fun j => (ϱ j : ℝ)) := by
  unfold Multigraph.pairing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The P4.7 energy gain for the optimal multiple of a profile with `⟨ψ, ϱ⟩ = q` and
`energy(ψ) ≤ 4096` ( with `C_* = 4096`). -/
theorem energyFunctional_optimal_ge [Fintype V] (G : Multigraph V E) {β : ℝ} (hβ : 0 < β) {ψ : V → ℝ}
    {ϱ : V → ℤ} {q : ℤ} (hq : q ≠ 0)
    (hpair : Multigraph.pairing ψ (fun j => (ϱ j : ℝ)) = q) (henergy : G.energy ψ ≤ 4096) :
    1 / 8192 / β ≤ energyFunctional G β (fun j => (q : ℝ) / (β * 4096) * ψ j) ϱ := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
    refine (one_le_sq_iff_one_le_abs _).mpr ?_
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hq
  unfold energyFunctional
  rw [pairing_const_mul, hpair, energy_const_mul]
  have hE0 : 0 ≤ G.energy ψ := Multigraph.energy_nonneg G ψ
  have key : (q : ℝ) / (β * 4096) * q - β / 2 * (((q : ℝ) / (β * 4096)) ^ 2 * G.energy ψ) ≥
      (q : ℝ) ^ 2 / (8192 * β) := by
    have h1 : β / 2 * (((q : ℝ) / (β * 4096)) ^ 2 * G.energy ψ) ≤
        β / 2 * (((q : ℝ) / (β * 4096)) ^ 2 * 4096) := by
      gcongr
    have h2 : (q : ℝ) / (β * 4096) * q - β / 2 * (((q : ℝ) / (β * 4096)) ^ 2 * 4096) =
        (q : ℝ) ^ 2 / (8192 * β) := by
      field_simp
      ring
    linarith only [h1, h2]
  have h3 : 1 / 8192 / β ≤ (q : ℝ) ^ 2 / (8192 * β) := by
    rw [div_div, div_le_div_iff_of_pos_right (by positivity)]
    exact hq1
  linarith only [key, h3]

end Algebra

/-! ## The profile -/

section Profile

variable {V : Type} {E : Type} [Fintype V] [DecidableEq V]
  (G : Multigraph V E) (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)

/-- The P4.7 profile `ψ̃` for a square `s` at scale `k`: the ramp from `r = 2^{k-3}` to
`S = 2^{k-1}` in the distance to `s`, flattened on the components. -/
def squareWaveProfile (s : Finset V) (k : ℕ) : V → ℝ :=
  flatten G N₁ centerOf (fun j => ramp (2 ^ (k - 3)) (2 ^ (k - 1)) (setDist G s j))
    (componentRep G N₁ centerOf (setDist G s) (2 ^ (k - 3)) (2 ^ (k - 1)))

theorem plateau_le_support (k : ℕ) : 2 ^ (k - 3) ≤ 2 ^ (k - 1) :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A component meeting the plateau but also `dist ≥ S + 1` would have diameter at least
`S + 1 - r`; this is excluded by the small-component bound `hsmall`. -/
theorem squareWaveProfile_support (hG : G.toSimpleGraph.Connected) {s : Finset V}
    (hs : s.Nonempty) (k : ℕ)
    (hsmall : ∀ c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)),
      densityPlusComponentDiameter G N₁ centerOf c + 2 ^ (k - 3) < 2 ^ (k - 1) + 1)
    {j : V} (hj : squareWaveProfile G N₁ centerOf s k j ≠ 0) :
    setDist G s j ≤ 2 ^ (k - 1) := by
  classical
  have hrS := plateau_le_support k
  unfold squareWaveProfile at hj
  by_cases hjU : j ∈ densityPlusUnion G N₁ centerOf
  · set c := componentOf G N₁ centerOf j hjU
    have hjc := mem_componentVertices_componentOf G N₁ centerOf j hjU
    rw [flatten_of_mem_component G N₁ centerOf _ _ hjc] at hj
    by_cases h₁ : ∃ x ∈ densityPlusComponentVertices G N₁ centerOf c,
        setDist G s x ≤ 2 ^ (k - 3)
    · -- the component meets the plateau, so it is relevant and small
      obtain ⟨x, hx, hxr⟩ := h₁
      have hrel : c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)) := by
        unfold relevantComponents
        exact Finset.mem_filter.mpr ⟨mem_componentFinset G N₁ centerOf c, x, hx, by omega⟩
      have hd := hsmall c hrel
      have hdist := dist_le_densityPlusComponentDiameter G N₁ centerOf c hjc hx
      have hlip := setDist_le_add G hG hs j x
      omega
    · by_cases h₂ : ∃ x ∈ densityPlusComponentVertices G N₁ centerOf c,
          2 ^ (k - 1) + 1 ≤ setDist G s x
      · exact absurd (ramp_eq_zero hrS (componentRep_zero G N₁ centerOf _ _ _ c h₁ h₂)) hj
      · push Not at h₂
        exact Nat.lt_succ_iff.mp (h₂ j hjc)
  · rw [flatten_of_not_mem G N₁ centerOf _ _ hjU] at hj
    by_contra h
    exact hj (ramp_eq_zero hrS (by omega))

/-- The profile is `1` on the plateau `dist(·, s) ≤ 2^{k-3}`. -/
theorem squareWaveProfile_plateau {s : Finset V} (k : ℕ) {j : V}
    (hj : setDist G s j ≤ 2 ^ (k - 3)) : squareWaveProfile G N₁ centerOf s k j = 1 := by
  classical
  have hrS := plateau_le_support k
  unfold squareWaveProfile
  by_cases hjU : j ∈ densityPlusUnion G N₁ centerOf
  · have hjc := mem_componentVertices_componentOf G N₁ centerOf j hjU
    rw [flatten_of_mem_component G N₁ centerOf _ _ hjc]
    exact ramp_eq_one hrS (componentRep_plateau G N₁ centerOf _ _ _ _ ⟨j, hjc, hj⟩)
  · rw [flatten_of_not_mem G N₁ centerOf _ _ hjU]
    exact ramp_eq_one hrS hj

/-- The profile is constant on each `D⁺(ϱ')`, `ϱ' ∈ 𝒩₀(ϱ*)`. -/
theorem squareWaveProfile_const_densityDomainPlus (hG : G.toSimpleGraph.Connected)
    {s : Finset V} (k : ℕ) {ϱ : V → ℤ} (hϱ : ϱ ∈ N₁) (hneutral : ∑ x, ϱ x = 0)
    (hcenter : G.IsDensityCenter ϱ (centerOf ϱ)) :
    ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ (centerOf ϱ),
      squareWaveProfile G N₁ centerOf s k j = c := by
  classical
  have hcD := G.mem_densityDomainPlus_of_center hG hneutral hcenter hcenter.1
  have hcU : centerOf ϱ ∈ densityPlusUnion G N₁ centerOf :=
    (mem_densityPlusUnion G N₁ centerOf _).2 ⟨ϱ, hϱ, hcD⟩
  have hsub := densityDomainPlus_subset_component G N₁ centerOf hG hϱ hneutral hcenter hcD
    (mem_componentVertices_componentOf G N₁ centerOf _ hcU)
  exact ⟨_, fun j hj => flatten_of_mem_component G N₁ centerOf _ _ (hsub hj)⟩

/-- The pairing of the profile with `ϱ*` is the patch charge, when the components avoid the
support and the rest of the support lies beyond `S + 1`. -/
theorem pairing_squareWaveProfile {s : Finset V} (k : ℕ) {ϱ : V → ℤ}
    (hoff : ∀ j, ϱ j ≠ 0 → j ∉ densityPlusUnion G N₁ centerOf)
    (hfar : ∀ j, ϱ j ≠ 0 → j ∉ s → 2 ^ (k - 1) + 1 ≤ setDist G s j) :
    Multigraph.pairing (squareWaveProfile G N₁ centerOf s k) (fun j => (ϱ j : ℝ)) =
      ((∑ j ∈ s, ϱ j : ℤ) : ℝ) := by
  classical
  have hrS := plateau_le_support k
  have hterm : ∀ j, squareWaveProfile G N₁ centerOf s k j * (ϱ j : ℝ) =
      if j ∈ s then (ϱ j : ℝ) else 0 := by
    intro j
    by_cases hj0 : ϱ j = 0
    · simp [hj0]
    · have hjU := hoff j hj0
      unfold squareWaveProfile
      rw [flatten_of_not_mem G N₁ centerOf _ _ hjU]
      by_cases hjs : j ∈ s
      · rw [ramp_eq_one hrS (by rw [setDist_eq_zero_of_mem G hjs]; exact Nat.zero_le _),
          one_mul, ite_eq_left hjs]
      · rw [ramp_eq_zero hrS (hfar j hj0 hjs), zero_mul, ite_eq_right hjs]
  unfold Multigraph.pairing
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  push_cast
  rfl

/-- The energy of the profile from the four scalar inputs: the near-set count, the ramp width,
L4.6(3) and the cube sum over relevant components. -/
theorem energy_squareWaveProfile_le [Fintype E] (hG : G.toSimpleGraph.Connected)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4)
    {s : Finset V} (hs : s.Nonempty) (k : ℕ) (n : ℝ) (hn : 0 < n)
    (hA : ((Finset.univ.filter fun j => setDist G s j ≤ 2 ^ (k - 1) + 1).card : ℝ) ≤ 25 * n ^ 2)
    (hwidth : n ≤ 4 * ((2 ^ (k - 1) + 1 - 2 ^ (k - 3) : ℕ) : ℝ))
    (hbdry : ∀ c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)),
      ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) ≤
        64 * densityPlusComponentDiameter G N₁ centerOf c)
    (hdiam : ∀ c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)),
      1 ≤ densityPlusComponentDiameter G N₁ centerOf c)
    (hcube : ∑ c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)),
      (densityPlusComponentDiameter G N₁ centerOf c : ℝ) ^ 3 ≤ n ^ 2 / 50) :
    G.energy (squareWaveProfile G N₁ centerOf s k) ≤ 4096 := by
  have hrS := plateau_le_support k
  have h := energy_flatten_ramp_le G N₁ centerOf hG hdeg hs hrS
  set δ : ℝ := ((2 ^ (k - 1) + 1 - 2 ^ (k - 3) : ℕ) : ℝ) with hδ
  have hδpos : 0 < δ := by linarith only [hn, hwidth]
  have hδ2 : n ^ 2 ≤ 16 * δ ^ 2 := by nlinarith only [hn, hwidth]
  have hfirst : 4 * ((Finset.univ.filter fun j => setDist G s j ≤ 2 ^ (k - 1) + 1).card : ℝ) /
      δ ^ 2 ≤ 1600 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hA, hδ2]
  have hterm : ∀ c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)),
      4 * ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) *
        ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 / δ ^ 2 ≤
      16384 / n ^ 2 * (densityPlusComponentDiameter G N₁ centerOf c : ℝ) ^ 3 := by
    intro c hc
    have hd1' : (1 : ℝ) ≤ (densityPlusComponentDiameter G N₁ centerOf c : ℝ) := by
      exact_mod_cast hdiam c hc
    set d : ℝ := (densityPlusComponentDiameter G N₁ centerOf c : ℝ)
    have hd1 : (1 : ℝ) ≤ d := hd1'
    have hb := hbdry c hc
    have hb0 : (0 : ℝ) ≤ (densityPlusExternalBoundary G N₁ centerOf c).card := Nat.cast_nonneg _
    have hnum : 4 * ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) * (d + 1) ^ 2 ≤
        1024 * d ^ 3 := by
      have h1 : (d + 1) ^ 2 ≤ 4 * d ^ 2 := by nlinarith only [hd1]
      calc 4 * ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) * (d + 1) ^ 2
          ≤ 4 * (64 * d) * (4 * d ^ 2) := by gcongr
        _ = 1024 * d ^ 3 := by ring
    rw [div_le_iff₀ (by positivity)]
    have hn2 : 0 < n ^ 2 := by positivity
    calc 4 * ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) * (d + 1) ^ 2
        ≤ 1024 * d ^ 3 := hnum
      _ ≤ 16384 / n ^ 2 * d ^ 3 * δ ^ 2 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hn2]
        have : 0 ≤ d ^ 3 := by positivity
        nlinarith only [hδ2, this]
  have hsecond := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsecond
  have hthird : 16384 / n ^ 2 * ∑ c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)),
      (densityPlusComponentDiameter G N₁ centerOf c : ℝ) ^ 3 ≤ 16384 / 50 := by
    calc _ ≤ 16384 / n ^ 2 * (n ^ 2 / 50) := by gcongr
      _ = 16384 / 50 := by field_simp
  unfold squareWaveProfile
  linarith only [h, hfirst, hsecond, hthird]

end Profile

/-! ## Proposition 4.7 on one domain -/

/-- KP Proposition 4.7 on one square domain from Lemma 4.6 on that domain, with `D₃ = 1/8192`. -/
theorem p47Step_of_l46Step (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L) {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (hdeg : ∀ j, (Finset.univ.filter fun e => Λ.src e = j).card +
      (Finset.univ.filter fun e => Λ.tgt e = j).card ≤ 4)
    (h46 : L46Step boundary Λ) : P47Step boundary Λ (1 / 8192) := by
  classical
  intro centerOf hcenter β hβ N hens hNa hNb hNc ϱstar hϱstar k C s hs
  obtain ⟨hϱN, hneutral⟩ := mem_neutralPart.mp hϱstar
  set N₁ := Λ.comparableDensities (neutralPart N) ϱstar with hN₁
  set n : ℕ := 2 ^ k.val with hn
  set S : ℕ := 2 ^ (k.val - 1) with hS
  set r : ℕ := 2 ^ (k.val - 3) with hr
  have hk := k.property
  have hnpos : 0 < n := Nat.two_pow_pos _
  have hSn : 2 * S = n := by
    rw [hS, hn, ← pow_succ']
    congr 1
    omega
  -- the patch and the square geometry
  obtain ⟨z, hz⟩ := separatedSquare_patch_nonempty boundary L ϱstar k C s hs
  obtain ⟨hzs, hzsupp⟩ := Finset.mem_inter.mp hz
  have hz0 : ϱstar z ≠ 0 := (Finset.mem_filter.mp hzsupp).2
  have hsne : s.Nonempty := ⟨z, hzs⟩
  have hq : ∑ j ∈ s, ϱstar j ≠ 0 := patchCharge_ne_zero boundary hL hNc hϱN hneutral hs
  have hsdiam : ∀ x ∈ s, ∀ y ∈ s, Λ.toSimpleGraph.dist x y ≤ 2 * (n - 1) := by
    intro x hx y hy
    rw [← hdist]
    exact latticeDistance_le_of_mem_separatedSquare boundary hL hs hx hy
  -- members of `𝒩₀(ϱ*)`
  have hN₁mem : ∀ ϱ ∈ N₁, ϱ ≠ 0 ∧ ∑ x, ϱ x = 0 ∧ Λ.IsDensityCenter ϱ (centerOf ϱ) := by
    intro ϱ hϱ
    have hϱ0 := (Λ.mem_comparableDensities.mp hϱ).1
    obtain ⟨hϱN', hϱn⟩ := mem_neutralPart.mp hϱ0
    have hne := hens.1 ϱ hϱN'
    exact ⟨hne, hϱn, hcenter ϱ hne⟩
  have hdiam1 := one_le_componentDiameter Λ N₁ centerOf hΛ hN₁mem
  have hL46 := h46 centerOf hcenter N hens hNa hNb hNc ϱstar hϱstar
  have hM128 : (chargeCoverScale : ℝ) / 128 = 512 := by norm_num [chargeCoverScale]
  have hM25 : (chargeCoverScale : ℝ) / 25 = 2 ^ 16 / 25 := by norm_num [chargeCoverScale]
  have hα : chargeCoverExponent = (7 / 4 : ℝ) := rfl
  -- distance from a point near `s` to the patch point `z`
  have hnear : ∀ p, setDist Λ s p ≤ S + 1 → Λ.toSimpleGraph.dist p z ≤ S + 1 + 2 * (n - 1) := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := exists_setDist_eq Λ hsne p
    have h1 := hΛ.dist_triangle (u := p) (v := y) (w := z)
    have h2 := hsdiam y hy z hzs
    omega
  -- relevant components are small (L4.6(2) with the repaired  bound)
  have hroot : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      (2 ^ 16 / 128 : ℝ) * (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ (7 / 4 : ℝ) ≤
        5 / 2 * (n : ℝ) + densityPlusComponentDiameter Λ N₁ centerOf c := by
    intro c hc
    obtain ⟨-, p, hp, hpS⟩ := Finset.mem_filter.mp hc
    have h2 := (hL46 c).2.1
    have hle := componentRootDistance_le Λ N₁ centerOf c hp hz0
    have hpz := hnear p hpS
    have hrd : (densityPlusComponentRootDistance Λ N₁ centerOf c ϱstar : ℝ) ≤ 5 / 2 * n := by
      have : densityPlusComponentRootDistance Λ N₁ centerOf c ϱstar ≤ S + 1 + 2 * (n - 1) :=
        hle.trans hpz
      have h' : S + 1 + 2 * (n - 1) ≤ 5 * S := by omega
      have : (densityPlusComponentRootDistance Λ N₁ centerOf c ϱstar : ℝ) ≤ 5 * S := by
        exact_mod_cast this.trans h'
      have hSR : (2 * S : ℝ) = n := by exact_mod_cast hSn
      linarith only [this, hSR]
    rw [hM128, hα] at h2
    have hd0 : (0 : ℝ) ≤ densityPlusComponentDiameter Λ N₁ centerOf c := Nat.cast_nonneg _
    have : (2 ^ 16 / 128 : ℝ) = 512 := by norm_num
    rw [this]
    linarith only [h2, hrd]
  have hsmall200 : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      200 * densityPlusComponentDiameter Λ N₁ centerOf c ≤ n := by
    intro c hc
    have h := hroot c hc
    have hd1 : (1 : ℝ) ≤ densityPlusComponentDiameter Λ N₁ centerOf c := by
      exact_mod_cast hdiam1 c
    have hself := Real.self_le_rpow_of_one_le hd1 (by norm_num : (1 : ℝ) ≤ 7 / 4)
    have : (200 * densityPlusComponentDiameter Λ N₁ centerOf c : ℕ) ≤ (n : ℝ) := by
      push_cast
      nlinarith only [h, hself]
    exact_mod_cast this
  have hsmall : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      densityPlusComponentDiameter Λ N₁ centerOf c + r < S + 1 := by
    intro c hc
    have h200 := hsmall200 c hc
    have hd1 := hdiam1 c
    -- `n ≥ 200`, so `k ≥ 8` and `r = n/8`, `S = n/2`
    have hk8 : 8 ≤ k.val := by
      by_contra hlt
      have : n ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h8r : 8 * r = n := by
      rw [hr, hn, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  -- components avoid the support of `ϱ*`
  have hoff : ∀ j, ϱstar j ≠ 0 → j ∉ densityPlusUnion Λ N₁ centerOf := by
    intro j hj hjU
    set c := componentOf Λ N₁ centerOf j hjU
    have hjc := mem_componentVertices_componentOf Λ N₁ centerOf j hjU
    have h2 := (hL46 c).2.1
    have hle := componentRootDistance_le Λ N₁ centerOf c hjc hj
    rw [SimpleGraph.dist_self, Nat.le_zero] at hle
    rw [hle, Nat.cast_zero] at h2
    have hd1 : (1 : ℝ) ≤ densityPlusComponentDiameter Λ N₁ centerOf c := by
      exact_mod_cast hdiam1 c
    have hpos : 0 < (chargeCoverScale : ℝ) / 128 *
        (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ chargeCoverExponent := by
      have : (0 : ℝ) < chargeCoverScale := by norm_num [chargeCoverScale]
      have : (0 : ℝ) < (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ chargeCoverExponent :=
        Real.rpow_pos_of_pos (by linarith only [hd1]) _
      positivity
    linarith only [h2, hpos]
  -- the rest of the support is far from `s`
  have hfar : ∀ j, ϱstar j ≠ 0 → j ∉ s → S + 1 ≤ setDist Λ s j := by
    intro j hj hjs
    obtain ⟨y, hy, hjy⟩ := exists_setDist_eq Λ hsne j
    have h := thirtyTwo_mul_lt_latticeDistance boundary hs hy hj hjs
    rw [hdist, SimpleGraph.dist_comm, ← hjy] at h
    omega
  -- the profile and the wave
  have hpair := pairing_squareWaveProfile Λ N₁ centerOf k.val hoff hfar
  -- the energy bound
  have hA : ((Finset.univ.filter fun j => setDist Λ s j ≤ S + 1).card : ℝ) ≤
      25 * (n : ℝ) ^ 2 := by
    have hsub : (Finset.univ.filter fun j => setDist Λ s j ≤ S + 1) ⊆
        Finset.univ.filter fun j => latticeDistance boundary L j z ≤ S + 1 + 2 * (n - 1) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [hdist]
      exact hnear j hj
    have hball := card_latticeDistance_le_le boundary L (S + 1 + 2 * (n - 1)) z
    have hcard := (Finset.card_le_card hsub).trans hball
    have hbound : (2 * (S + 1 + 2 * (n - 1)) + 1) ≤ 5 * n := by omega
    have : ((Finset.univ.filter fun j => setDist Λ s j ≤ S + 1).card : ℝ) ≤
        ((5 * n) ^ 2 : ℕ) := by
      exact_mod_cast hcard.trans (Nat.pow_le_pow_left hbound 2)
    push_cast at this
    linarith only [this]
  have hwidth : (n : ℝ) ≤ 4 * ((S + 1 - r : ℕ) : ℝ) := by
    have : n ≤ 4 * (S + 1 - r) := by
      rcases Nat.lt_or_ge k.val 3 with hk3 | hk3
      · have hr1 : r = 1 := by rw [hr, show k.val - 3 = 0 by omega, pow_zero]
        omega
      · have h8r : 8 * r = n := by
          rw [hr, hn, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
          congr 1
          omega
        omega
    exact_mod_cast this
  have hbdry : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      ((densityPlusExternalBoundary Λ N₁ centerOf c).card : ℝ) ≤
        64 * densityPlusComponentDiameter Λ N₁ centerOf c := by
    intro c _
    exact_mod_cast (hL46 c).2.2
  -- the cube sum, from L4.6(1)–(2) and the lattice packing count
  have hcube : ∑ c ∈ relevantComponents Λ N₁ centerOf s S,
      (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 / 50 := by
    have : Nonempty (Fin L × Fin L) := ⟨z⟩
    choose! pt hpt hptS using fun c (hc : c ∈ relevantComponents Λ N₁ centerOf s S) =>
      (Finset.mem_filter.mp hc).2
    refine sum_cube_le_of_scale_separation (relevantComponents Λ N₁ centerOf s S)
      (fun c => densityPlusComponentDiameter Λ N₁ centerOf c)
      (fun c c' => densityPlusComponentDistance Λ N₁ centerOf c c') (n : ℝ)
      (by exact_mod_cast hnpos) (3 * n) (by push_cast; linarith only) (fun c _ => hdiam1 c) hroot
      ?_ ?_
    · intro c _ c' _ hcc'
      have h1 := (hL46 c).1 c' hcc'
      rw [hM25, hα] at h1
      exact h1
    · intro J hJ m hm hJsep
      have hinj : Set.InjOn pt (J : Set (DensityPlusComponent Λ N₁ centerOf)) := by
        intro c hc c' hc' heq
        by_contra hne
        have h := hJsep c hc c' hc' hne
        have hle := densityPlusComponentDistance_le Λ N₁ centerOf c c' (hpt c (hJ hc))
          (hpt c' (hJ hc'))
        rw [heq, SimpleGraph.dist_self] at hle
        omega
      rw [← Finset.card_image_of_injOn hinj]
      refine card_le_of_pairwise_latticeDistance_ge boundary hL z (3 * n) m hm (J.image pt) ?_ ?_
      · intro p hp
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
        rw [hdist]
        have := hnear (pt c) (hptS c (hJ hc))
        omega
      · intro p hp p' hp' hpp'
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hp'
        have hcc' : c ≠ c' := fun h => hpp' (h ▸ rfl)
        rw [hdist]
        exact (hJsep c hc c' hc' hcc').trans
          (densityPlusComponentDistance_le Λ N₁ centerOf c c' (hpt c (hJ hc)) (hpt c' (hJ hc')))
  have henergy := energy_squareWaveProfile_le Λ N₁ centerOf hΛ hdeg hsne k.val (n : ℝ)
    (by exact_mod_cast hnpos) hA hwidth hbdry (fun c _ => hdiam1 c) hcube
  -- the four clauses
  refine ⟨fun j => ((∑ j ∈ s, ϱstar j : ℤ) : ℝ) / (β * 4096) *
    squareWaveProfile Λ N₁ centerOf s k.val j, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hψj : squareWaveProfile Λ N₁ centerOf s k.val j ≠ 0 := fun h => hj (by simp [h])
    have := squareWaveProfile_support Λ N₁ centerOf hΛ hsne k.val hsmall hψj
    exact (setDist_le_iff Λ hsne j _).mp this
  · refine ⟨((∑ j ∈ s, ϱstar j : ℤ) : ℝ) / (β * 4096) * 1, fun j hj => ?_⟩
    rw [ceil_two_zpow_sub_three] at hj
    show _ * squareWaveProfile Λ N₁ centerOf s k.val j = _
    rw [squareWaveProfile_plateau Λ N₁ centerOf k.val ((setDist_le_iff Λ hsne j _).mpr hj)]
  · intro ϱ' hϱ'
    obtain ⟨-, hn', hc'⟩ := hN₁mem ϱ' hϱ'
    obtain ⟨c, hc⟩ := squareWaveProfile_const_densityDomainPlus Λ N₁ centerOf hΛ k.val hϱ' hn' hc'
    exact ⟨_, fun j hj => by
      show _ * squareWaveProfile Λ N₁ centerOf s k.val j = _
      rw [hc j hj]⟩
  · exact energyFunctional_optimal_ge Λ hβ hq hpair henergy

/-- **KP Proposition 4.7 from KP Lemma 4.6** on every square domain, with `D₃ = 1/8192`. The
endpoint-degree bound comes from the square bipartition structures (`SquareGeometry.lean`). -/
theorem p47_of_l46 : l46Statement → p47Statement := by
  intro h46
  refine ⟨1 / 8192, by norm_num, fun L hL => ⟨?_, fun hEven => ?_⟩⟩
  · exact p47Step_of_l46Step .free hL (squareFree L) (squareFree_connected L hL) (fun _ _ => rfl)
      (squareFreeBipartiteDegreeFour L hL).endpointDegree_le_four (h46 L hL).1
  · exact p47Step_of_l46Step .periodic hL (squarePeriodic L) (squarePeriodic_connected L hL)
      (fun _ _ => rfl) (squarePeriodicBipartiteDegreeFour L hEven hL).endpointDegree_le_four
      ((h46 L hL).2 hEven)

end FroehlichSpencer.BKT.SpinWaves.P47

end
