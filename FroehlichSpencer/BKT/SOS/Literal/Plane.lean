/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Theorem73

/-!
# FS81 Theorem 7.3 for an arbitrary finite region of the plane (the finite comb construction)

FS81 state (7.17)–(7.18) for a finite region `A ⊂ ℤ²` and points `0, x ∈ A`, in the state built
from the zero-mass field of the whole plane (FS81). Here the plane field is
approximated by the zero-exterior field on boxes `Ω ⊇ A`: the box of side `L + 1` with the plane
recentred at its middle (`centeredSite`, `centeredRegion`).

`literal_theorem73_plane`: there are `β₀ ∈ (0, 1]` and `β' → 0` such that for `0 < β ≤ β₀`,
**every finite `A ⊂ ℤ²`** and all `u, v ∈ A`, for every box `Ω_L ⊇ A` with `L ≥ L_A`
(`L_A` depending only on the size of `A`), (7.17) for `|ε| ≤ β/2` and (7.18) hold in the literal
state with FS81's `log(1 + |x|)`, `|x| = ‖u − v‖_∞`, uniformly in `L`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open Filter Topology
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth)
open FroehlichSpencer.BKT.SOS.Roughening

/-- The centred placement of a plane site in the box of side `L + 1`. -/
def centeredSite (L : ℕ) (z : ℤ × ℤ) : Site (L + 1) :=
  (Fin.ofNat (L + 1) (z.1 + ((L + 1) / 2 : ℕ)).toNat,
    Fin.ofNat (L + 1) (z.2 + ((L + 1) / 2 : ℕ)).toNat)

/-- The centred copy of a plane region. -/
def centeredRegion (L : ℕ) (A : Finset (ℤ × ℤ)) : Finset (Site (L + 1)) :=
  A.image (centeredSite L)

/-- The `ℓ^∞` distance of plane sites. -/
def planeLinf (u v : ℤ × ℤ) : ℕ := max (u.1 - v.1).natAbs (u.2 - v.2).natAbs

/-- The size of a plane region: the largest coordinate. -/
def planeRadius (A : Finset (ℤ × ℤ)) : ℕ := A.sup fun z => max z.1.natAbs z.2.natAbs

theorem coord_le_planeRadius {A : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ A) :
    z.1.natAbs ≤ planeRadius A ∧ z.2.natAbs ≤ planeRadius A := by
  have h : max z.1.natAbs z.2.natAbs ≤ planeRadius A :=
    Finset.le_sup (f := fun z : ℤ × ℤ => max z.1.natAbs z.2.natAbs) hz
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

/-- In a large box the centred placement is the translation by `(L + 1)/2`. -/
theorem centeredSite_val {L R : ℕ} (hL : 2 * R + 1 ≤ L) {z : ℤ × ℤ} (h1 : z.1.natAbs ≤ R)
    (h2 : z.2.natAbs ≤ R) :
    ((centeredSite L z).1.val : ℤ) = z.1 + ((L + 1) / 2 : ℕ) ∧
      ((centeredSite L z).2.val : ℤ) = z.2 + ((L + 1) / 2 : ℕ) := by
  have hc : R ≤ (L + 1) / 2 := by omega
  have hc' : (L + 1) / 2 + R < L + 1 := by omega
  constructor
  · simp only [centeredSite, Fin.val_ofNat]
    have h0 : 0 ≤ z.1 + ((L + 1) / 2 : ℕ) := by omega
    have hlt : (z.1 + ((L + 1) / 2 : ℕ)).toNat < L + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg h0]
  · simp only [centeredSite, Fin.val_ofNat]
    have h0 : 0 ≤ z.2 + ((L + 1) / 2 : ℕ) := by omega
    have hlt : (z.2 + ((L + 1) / 2 : ℕ)).toNat < L + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg h0]

theorem linfDist_centeredSite {L R : ℕ} (hL : 2 * R + 1 ≤ L) {u v : ℤ × ℤ}
    (hu1 : u.1.natAbs ≤ R) (hu2 : u.2.natAbs ≤ R) (hv1 : v.1.natAbs ≤ R) (hv2 : v.2.natAbs ≤ R) :
    linfDist (centeredSite L u) (centeredSite L v) = planeLinf u v := by
  obtain ⟨hu1', hu2'⟩ := centeredSite_val hL hu1 hu2
  obtain ⟨hv1', hv2'⟩ := centeredSite_val hL hv1 hv2
  unfold linfDist planeLinf
  rw [hu1', hu2', hv1', hv2']
  congr 1 <;> congr 1 <;> ring

theorem planeLinf_le_two_mul {R : ℕ} {u v : ℤ × ℤ} (hu1 : u.1.natAbs ≤ R)
    (hu2 : u.2.natAbs ≤ R) (hv1 : v.1.natAbs ≤ R) (hv2 : v.2.natAbs ≤ R) :
    planeLinf u v ≤ 2 * R := by
  unfold planeLinf
  refine max_le ?_ ?_ <;> omega

theorem two_mul_le_depth_centeredSite {L R : ℕ} (hL : 6 * R + 1 ≤ L) {u : ℤ × ℤ}
    (hu1 : u.1.natAbs ≤ R) (hu2 : u.2.natAbs ≤ R) :
    2 * R ≤ siteBoundaryDepth (centeredSite L u) := by
  obtain ⟨hx, hy⟩ := centeredSite_val (by omega : 2 * R + 1 ≤ L) hu1 hu2
  set x := (centeredSite L u).1.val
  set y := (centeredSite L u).2.val
  set c := (L + 1) / 2
  have hc : 3 * R + 1 ≤ c := by omega
  have hc2 : c ≤ (L + 1) / 2 := le_rfl
  have hxlo : 2 * R + 1 ≤ x := by omega
  have hxhi : x + 2 * R + 1 ≤ L + 1 := by omega
  have hylo : 2 * R + 1 ≤ y := by omega
  have hyhi : y + 2 * R + 1 ≤ L + 1 := by omega
  unfold siteBoundaryDepth
  refine le_min (by omega) (le_min (by omega) (le_min (by omega) (by omega)))

theorem planeLinf_le_depth {L R : ℕ} (hL : 6 * R + 1 ≤ L) {u v : ℤ × ℤ}
    (hu1 : u.1.natAbs ≤ R) (hu2 : u.2.natAbs ≤ R) (hv1 : v.1.natAbs ≤ R) (hv2 : v.2.natAbs ≤ R) :
    planeLinf u v ≤ siteBoundaryDepth (centeredSite L u) :=
  (planeLinf_le_two_mul hu1 hu2 hv1 hv2).trans (two_mul_le_depth_centeredSite hL hu1 hu2)

/-- **FS81 Theorem 7.3 for an arbitrary finite region of the plane**, in the literal state on
every large box around it. -/
theorem literal_theorem73_plane :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), 0 < β₀ ∧ β₀ ≤ 1 ∧ Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β, 0 < β → β ≤ β₀ → 0 < β' β ∧ ∀ (A : Finset (ℤ × ℤ)) (u v : ℤ × ℤ), u ∈ A → v ∈ A →
        ∃ L_A : ℕ, ∀ L, L_A ≤ L →
          (∀ ε : ℝ, |ε| ≤ β / 2 →
            ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + (planeLinf u v : ℝ)))) ≤
              literalMomentExt (L + 1) β (centeredRegion L A) (centeredSite L u)
                (centeredSite L v) ε) ∧
          Real.log (1 + (planeLinf u v : ℝ)) / β' β ≤
            literalVariance (L + 1) β (centeredRegion L A) (centeredSite L u)
              (centeredSite L v) := by
  obtain ⟨β₀, β', L₀, hβ₀, hβ₀1, -, hlim, h⟩ := literal_theorem73_deep
  refine ⟨β₀, β', hβ₀, hβ₀1, hlim, fun β hβ hββ₀ => ⟨(h β hβ hββ₀).1, fun A u v hu hv => ?_⟩⟩
  set R := planeRadius A
  refine ⟨max L₀ (6 * R + 1), fun L hL => ?_⟩
  obtain ⟨hu1, hu2⟩ := coord_le_planeRadius hu
  obtain ⟨hv1, hv2⟩ := coord_le_planeRadius hv
  have hL6 : 6 * R + 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlinf := linfDist_centeredSite (by omega : 2 * R + 1 ≤ L) hu1 hu2 hv1 hv2
  have h' := (h β hβ hββ₀).2 (L + 1) (by have := le_max_left L₀ (6 * R + 1); omega)
    (centeredRegion L A) (centeredSite L u) (centeredSite L v) (Finset.mem_image_of_mem _ hu)
    (Finset.mem_image_of_mem _ hv) (hlinf ▸ planeLinf_le_depth hL6 hu1 hu2 hv1 hv2)
  rw [hlinf] at h'
  exact h'

end FroehlichSpencer.BKT.SOS.Literal

end
