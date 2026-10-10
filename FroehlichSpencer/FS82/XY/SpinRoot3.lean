/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.SpinOrder3
public import FroehlichSpencer.FS82.XY.EndpointResidual

/-!
# the finite-volume form of (4.40) for the Villain `XY` model, `D = 3`

`fs82_xy3_spinCorrelation_root`: there are `β₀` and `C` such that for every `β ≥ β₀`, every box
with three equal sides, and all sites `x, y` of it,

`exp(−C/β) ≤ ⟨cos(θ_x − θ_y)⟩_B(β)`,

The constants do not depend on `x`, `y` or the
box.

This is FS82 (4.40) in finite volume; the limit `Λ ↗ ℤ³` is not taken here.

On a cube of side `N` one takes `m = N`.

A cube of side `0` has no dual link,
and for `N ≥ 1`, `a ≥ 3`, `(N + 1)³ e^{−aN} ≤ 8 e^{−a}`.

So on every cube that term is at most
`320π² e^{−a(β)}`, and `e^{−a(β)} ≤ (400/3)/β`.

Hence the root holds on all cubes, with no lower
bound on the side; `fs82_xy3_spinCorrelation_root_centredCubes` states it on the centred cubes
`[−N, N]³` for `N ≥ N₀`, and `N₀ = 0` works.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.XY.Renormalization3

variable {B : Dual3Box}

/-! ## The long-current term on cubes -/

/-- A box with all sides zero has no dual link. -/
theorem dual3Links_isEmpty_of_sides_zero (hB : ∀ k, B k = 0) : IsEmpty (Dual3Links B) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ linkDirection e := by
    by_cases h : linkDirection e = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun h' => h h'.symm⟩
  obtain ⟨v, _⟩ := linkCoord_isLeft_of_ne_direction e hi
  have hv : v.val < B i := v.isLt
  have h0 := hB i
  omega

theorem cube_mul_exp_le {a : ℝ} (ha : 3 ≤ a) {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) + 1) ^ 3 * Real.exp (-(a * (N : ℝ))) ≤ 8 * Real.exp (-a) := by
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : ((N : ℝ) + 1) ^ 3 ≤ 8 * (N : ℝ) ^ 3 := by
    have h2 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    calc ((N : ℝ) + 1) ^ 3 ≤ (2 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
      _ = 8 * (N : ℝ) ^ 3 := by ring
  have h2 : (N : ℝ) ≤ Real.exp ((N : ℝ) - 1) := by
    have := Real.add_one_le_exp ((N : ℝ) - 1)
    linarith
  have h3 : (N : ℝ) ^ 3 ≤ Real.exp (a * ((N : ℝ) - 1)) := by
    calc (N : ℝ) ^ 3 ≤ Real.exp ((N : ℝ) - 1) ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
      _ = Real.exp (3 * ((N : ℝ) - 1)) := by
          rw [← Real.exp_nat_mul]
          norm_num
      _ ≤ Real.exp (a * ((N : ℝ) - 1)) := Real.exp_le_exp.mpr (by nlinarith)
  have hexp0 : 0 ≤ Real.exp (-(a * (N : ℝ))) := (Real.exp_pos _).le
  calc ((N : ℝ) + 1) ^ 3 * Real.exp (-(a * (N : ℝ)))
      ≤ 8 * (N : ℝ) ^ 3 * Real.exp (-(a * (N : ℝ))) := mul_le_mul_of_nonneg_right h1 hexp0
    _ ≤ 8 * Real.exp (a * ((N : ℝ) - 1)) * Real.exp (-(a * (N : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ hexp0
        linarith
    _ = 8 * Real.exp (-a) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The long-current term of (4.38) on a cube, uniformly in the side.** -/
theorem xy3_cubeLongTerm_le {a : ℝ} (ha : 3 ≤ a) (N : ℕ) (hB : ∀ k, B k = N) :
    5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) * Real.exp (-(a * (N : ℝ))) ≤
      320 * Real.pi ^ 2 * Real.exp (-a) := by
  have hpi : 0 ≤ 5 * Real.pi ^ 2 := by positivity
  by_cases hN : N = 0
  · have hempty : IsEmpty (Dual3Links B) :=
      dual3Links_isEmpty_of_sides_zero fun k => (hB k).trans hN
    have hcard : Fintype.card (Dual3Links B) = 0 := Fintype.card_eq_zero
    rw [hcard]
    have : 0 ≤ 320 * Real.pi ^ 2 * Real.exp (-a) := by positivity
    simpa using this
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hcard : (Fintype.card (Dual3Links B) : ℝ) ≤ 8 * ((N : ℝ) + 1) ^ 3 := by
      have h := card_dual3Links_le (B := B) N fun k => (hB k).le
      exact_mod_cast h
    have hcube := cube_mul_exp_le ha hN1
    have hexp0 : 0 ≤ Real.exp (-(a * (N : ℝ))) := (Real.exp_pos _).le
    calc 5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) * Real.exp (-(a * (N : ℝ)))
        ≤ 5 * Real.pi ^ 2 * (8 * ((N : ℝ) + 1) ^ 3) * Real.exp (-(a * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hpi) hexp0
      _ = 40 * Real.pi ^ 2 * (((N : ℝ) + 1) ^ 3 * Real.exp (-(a * (N : ℝ)))) := by ring
      _ ≤ 40 * Real.pi ^ 2 * (8 * Real.exp (-a)) :=
          mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = 320 * Real.pi ^ 2 * Real.exp (-a) := by ring

/-! ## The constants -/

/-- The threshold `β₀` of the finite-volume root. -/
def xy3RootBetaThreshold : ℝ := 144

/-- The constant of the Jensen rate bound `d(β) ≤ K e^{51 − 3β/8}`. -/
noncomputable def xy3JensenRateConstant : ℝ :=
  81 * (1280 * (2 * Real.pi * 64) ^ 2 * polyTail11)

/-- The constant `C` of the finite-volume root. -/
noncomputable def xy3RootConstant : ℝ :=
  36 + 400 / 3 * (72 * xy3JensenRateConstant * Real.exp 1 + 320 * Real.pi ^ 2)

theorem xy3JensenRateConstant_nonneg : 0 ≤ xy3JensenRateConstant := by
  unfold xy3JensenRateConstant
  have hpoly : 0 ≤ polyTail11 := by
    unfold polyTail11
    exact tsum_nonneg fun L => by positivity
  positivity

theorem xy3RootConstant_pos : 0 < xy3RootConstant := by
  unfold xy3RootConstant
  have := xy3JensenRateConstant_nonneg
  positivity

/-- The activity factor `e^{−a(β)}` is at most `(400/3)/β`. -/
theorem exp_neg_xy3ActivityRate_le {β : ℝ} (hβ : 144 ≤ β) :
    Real.exp (-(xy3ActivityRate β)) ≤ 400 / 3 / β := by
  have hβ0 : 0 < β := by linarith
  set t := xy3ActivityRate β with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    unfold xy3ActivityRate
    linarith
  have h1 : Real.exp (-t) * (1 + t) ≤ 1 := by
    have h := Real.add_one_le_exp t
    have hpos := Real.exp_pos (-t)
    calc Real.exp (-t) * (1 + t) ≤ Real.exp (-t) * Real.exp t :=
          mul_le_mul_of_nonneg_left (by linarith) hpos.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h2 : β ≤ 400 / 3 * (1 + t) := by
    rw [ht]
    unfold xy3ActivityRate
    linarith
  rw [le_div_iff₀ hβ0]
  have hpos := Real.exp_pos (-t)
  calc Real.exp (-t) * β ≤ Real.exp (-t) * (400 / 3 * (1 + t)) :=
        mul_le_mul_of_nonneg_left h2 hpos.le
    _ = 400 / 3 * (Real.exp (-t) * (1 + t)) := by ring
    _ ≤ 400 / 3 * 1 := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 400 / 3 := by ring

/-! ## The root -/


theorem xy3_spinCorrelation_lower {β : ℝ} (hβ : xy3RootBetaThreshold ≤ β) {B : Dual3Box}
    (hCube : ∀ i j : Fin 3, B i = B j) (x y : XYSites B) :
    Real.exp (-(xy3RootConstant / β)) ≤ xyEndpointCosExpectation β x y := by
  unfold xy3RootBetaThreshold at hβ
  have hβ0 : 0 < β := by linarith
  have hβ136 : (136 : ℝ) ≤ β := by linarith
  set N := B 0 with hN
  have hB : ∀ k, B k = N := fun k => hCube k 0
  have hres := xyDual3EndpointResidualEnergy_le_uniform x y hCube
  have hmain := xy3_endpointExpectation_lower_of_residual_le hβ136 N (fun k => (hB k).ge) x y
    72 hres
  rw [xyEndpointCosExpectation_eq_re_characterExpectation β hβ0 x y]
  refine le_trans (Real.exp_le_exp.mpr ?_) hmain
  have ha3 : 3 ≤ xy3ActivityRate β := by
    unfold xy3ActivityRate
    linarith
  set e := Real.exp (-(xy3ActivityRate β)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hK := xy3JensenRateConstant_nonneg
  have hd : xy3JensenRate β ≤ xy3JensenRateConstant * Real.exp 1 * e := by
    have h := xy3JensenRate_le hβ136
    have hexp : Real.exp (51 - 3 * β / 8) = Real.exp 1 * e := by
      rw [he, ← Real.exp_add]
      congr 1
      unfold xy3ActivityRate
      ring
    rw [hexp] at h
    unfold xy3JensenRateConstant
    linarith
  have hlong := xy3_cubeLongTerm_le (B := B) ha3 N hB
  rw [← he] at hlong
  have hrate : e ≤ 400 / 3 / β := exp_neg_xy3ActivityRate_le hβ
  have hcoef : 0 ≤ 72 * xy3JensenRateConstant * Real.exp 1 + 320 * Real.pi ^ 2 := by positivity
  have hhalf : 1 / (2 * β) * 72 = 36 / β := by
    field_simp
    ring
  have htotal : (1 / (2 * β) + xy3JensenRate β) * 72 +
      5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) *
        Real.exp (-(xy3ActivityRate β * (N : ℝ))) ≤ xy3RootConstant / β := by
    calc (1 / (2 * β) + xy3JensenRate β) * 72 +
          5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) *
            Real.exp (-(xy3ActivityRate β * (N : ℝ)))
        = 36 / β + xy3JensenRate β * 72 +
            5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) *
              Real.exp (-(xy3ActivityRate β * (N : ℝ))) := by rw [add_mul, hhalf]
      _ ≤ 36 / β + xy3JensenRateConstant * Real.exp 1 * e * 72 + 320 * Real.pi ^ 2 * e := by
          have := mul_le_mul_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 72)
          linarith
      _ = 36 / β + (72 * xy3JensenRateConstant * Real.exp 1 + 320 * Real.pi ^ 2) * e := by ring
      _ ≤ 36 / β + (72 * xy3JensenRateConstant * Real.exp 1 + 320 * Real.pi ^ 2) *
            (400 / 3 / β) := by
          have := mul_le_mul_of_nonneg_left hrate hcoef
          linarith
      _ = xy3RootConstant / β := by
          unfold xy3RootConstant
          ring
  linarith

/-- **The finite-volume root of FS82 Section 4 at `D = 3`, (4.40).** There are `β₀` and `C`
such that for every `β ≥ β₀`, every box with three equal sides and all sites `x, y` of it, the
spin correlation of the Villain `XY` model with free boundary conditions satisfies
`exp(−C/β) ≤ ⟨cos(θ_x − θ_y)⟩`. -/
theorem fs82_xy3_spinCorrelation_root :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧ ∀ β : ℝ, β₀ ≤ β → ∀ B : Dual3Box,
      (∀ i j : Fin 3, B i = B j) → ∀ x y : XYSites B,
        Real.exp (-(C / β)) ≤ xyEndpointCosExpectation β x y :=
  ⟨xy3RootBetaThreshold, xy3RootConstant, by unfold xy3RootBetaThreshold; norm_num,
    xy3RootConstant_pos, fun _ hβ _ hCube x y => xy3_spinCorrelation_lower hβ hCube x y⟩

/-! ## Centred cubes -/

/-- The centred cube `[−N, N]³` as a box: `2N` unit intervals in each direction. -/
def xy3CentredCube (N : ℕ) : Dual3Box := fun _ => 2 * N

/-- **The finite-volume root on centred cubes.** There are `β₀` and `C` such that for every
`β ≥ β₀` there is `N₀` with `exp(−C/β) ≤ ⟨cos(θ_x − θ_y)⟩` on the centred cube `[−N, N]³` for
all `N ≥ N₀` and all sites `x, y` of it. The proof gives `N₀ = 0`. -/
theorem fs82_xy3_spinCorrelation_root_centredCubes :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧ ∀ β : ℝ, β₀ ≤ β → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x y : XYSites (xy3CentredCube N),
        Real.exp (-(C / β)) ≤ xyEndpointCosExpectation β x y :=
  ⟨xy3RootBetaThreshold, xy3RootConstant, by unfold xy3RootBetaThreshold; norm_num,
    xy3RootConstant_pos, fun _ hβ => ⟨0, fun _ _ x y =>
      xy3_spinCorrelation_lower hβ (fun _ _ => rfl) x y⟩⟩

end FroehlichSpencer.FS82.XY

end
