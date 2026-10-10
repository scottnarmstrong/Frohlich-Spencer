/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Exterior
public import FroehlichSpencer.Multiscale.Basic
import FroehlichSpencer.Infra.Green.Iteration
import FroehlichSpencer.Infra.Green.PathExpansion

/-!
On a finite domain the path-sum iteration of the first-exit
identity is replaced by a single application of the identity at every point together with a
weighted maximum.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

/--
With `F(p) = ‖G_A(p, y)‖ e^{μ |p − y|}` the first-exit identity at each `p ∈ A` gives
`F(p) ≤ K + θ max F`, hence `max F ≤ 2K` when `θ ≤ 1/2`; no path sum or vanishing remainder is
needed on a finite domain.
-/
theorem norm_finiteGreen_le_of_firstExit {ν : ℕ} {A : Finset (Site ν)} (v : Site ν → ℝ)
    (E ε : ℝ) (hε : ε ≠ 0) (Rg : Site ν → Finset (Site ν)) (hRp : ∀ p ∈ A, p ∈ Rg p)
    (hRA : ∀ p ∈ A, Rg p ⊆ A) {μ K θ : ℝ} (hμ : 0 ≤ μ) (hK : 0 ≤ K) (hθ : θ ≤ 1 / 2)
    (y : Site ν) (hy : y ∈ A)
    (hdirect : ∀ (p : Site ν) (hp : p ∈ A) (hy' : y ∈ Rg p),
      ‖finiteGreen ν (Rg p) v E ε hε ⟨p, hRp p hp⟩ ⟨y, hy'⟩‖ ≤
        K * Real.exp (-μ * siteDist ν p y))
    (hcross : ∀ (p : Site ν) (hp : p ∈ A), ∑ u ∈ (Rg p).attach, ∑ u' ∈ A \ Rg p,
      ‖finiteGreen ν (Rg p) v E ε hε ⟨p, hRp p hp⟩ u‖ * ‖hoppingKernel ν u u'‖ *
        Real.exp (μ * siteDist ν p u') ≤ θ)
    (x : Site ν) (hx : x ∈ A) :
    ‖finiteGreen ν A v E ε hε ⟨x, hx⟩ ⟨y, hy⟩‖ ≤ 2 * K * Real.exp (-μ * siteDist ν x y) := by
  classical
  set z : ℂ := (E : ℂ) + (ε : ℂ) * Complex.I with hz0
  have hz : z.im ≠ 0 := by simpa [hz0] using hε
  set a := hoppingKernel ν with ha
  set V : Site ν → ℝ := fun x => v x + 2 * (ν : ℝ) with hV
  have hsymm : ∀ x y, a y x = star (a x y) := hoppingKernel_symm ν
  have hunit : ∀ A : Finset (Site ν),
      IsUnit (Infra.restrictedOp a V A - z • (1 : Matrix A A ℂ)) := fun A =>
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (Infra.isHermitian_restrictedOp hsymm V A) z hz
  set F : Site ν → ℝ := fun w =>
    ‖Infra.resolventColumn a V A z y w‖ * Real.exp (μ * siteDist ν w y) with hF
  have hne : A.Nonempty := ⟨x, hx⟩
  set M := A.sup' hne F with hM
  have hFM : ∀ w ∈ A, F w ≤ M := fun w hw => Finset.le_sup' F hw
  have hF0 : ∀ w, 0 ≤ F w := fun w => by simp only [hF]; positivity
  have hM0 : 0 ≤ M := (hF0 x).trans (hFM x hx)
  have key : ∀ p ∈ A, F p ≤ K + θ * M := by
    intro p hp
    set B := Rg p with hBdef
    have hBA : B ⊆ A := hRA p hp
    have hpB : p ∈ B := hRp p hp
    have hcr : ∑ k ∈ B, ∑ k' ∈ A \ B, ‖Infra.resolventColumn a V B z k p‖ * ‖a k k'‖ *
        Real.exp (μ * siteDist ν p k') ≤ θ := by
      refine le_trans (le_of_eq ?_) (hcross p hp)
      rw [← Finset.sum_attach B]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
      rw [finiteGreen_eq_resolventColumn]
    set S := ∑ k ∈ B, ∑ k' ∈ A \ B, Infra.resolventColumn a V B z k p * a k k' *
        Infra.resolventColumn a V A z y k' with hS
    have hSb : ‖S‖ * Real.exp (μ * siteDist ν p y) ≤ θ * M := by
      have hterm : ∀ k ∈ B, ∀ k' ∈ A \ B,
          ‖Infra.resolventColumn a V B z k p * a k k' * Infra.resolventColumn a V A z y k'‖ *
            Real.exp (μ * siteDist ν p y) ≤
          ‖Infra.resolventColumn a V B z k p‖ * ‖a k k'‖ * Real.exp (μ * siteDist ν p k') * M := by
        intro k _ k' hk'
        have hk'A : k' ∈ A := (Finset.mem_sdiff.1 hk').1
        have h1 : Real.exp (μ * siteDist ν p y) ≤
            Real.exp (μ * siteDist ν p k') * Real.exp (μ * siteDist ν k' y) := by
          rw [← Real.exp_add, ← mul_add]
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (siteDist_triangle ν p y k') hμ)
        have h2 := hFM k' hk'A
        simp only [hF] at h2
        rw [norm_mul, norm_mul]
        calc ‖Infra.resolventColumn a V B z k p‖ * ‖a k k'‖ *
              ‖Infra.resolventColumn a V A z y k'‖ * Real.exp (μ * siteDist ν p y)
            ≤ ‖Infra.resolventColumn a V B z k p‖ * ‖a k k'‖ *
              ‖Infra.resolventColumn a V A z y k'‖ *
              (Real.exp (μ * siteDist ν p k') * Real.exp (μ * siteDist ν k' y)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ‖Infra.resolventColumn a V B z k p‖ * ‖a k k'‖ * Real.exp (μ * siteDist ν p k') *
              (‖Infra.resolventColumn a V A z y k'‖ * Real.exp (μ * siteDist ν k' y)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
      calc ‖S‖ * Real.exp (μ * siteDist ν p y)
          ≤ (∑ k ∈ B, ∑ k' ∈ A \ B,
              ‖Infra.resolventColumn a V B z k p * a k k' *
                Infra.resolventColumn a V A z y k'‖) * Real.exp (μ * siteDist ν p y) :=
            mul_le_mul_of_nonneg_right
              ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _))
              (Real.exp_pos _).le
        _ = ∑ k ∈ B, ∑ k' ∈ A \ B,
              ‖Infra.resolventColumn a V B z k p * a k k' *
                Infra.resolventColumn a V A z y k'‖ * Real.exp (μ * siteDist ν p y) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
        _ ≤ ∑ k ∈ B, ∑ k' ∈ A \ B, ‖Infra.resolventColumn a V B z k p‖ * ‖a k k'‖ *
              Real.exp (μ * siteDist ν p k') * M :=
            Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun k' hk' => hterm k hk k' hk'
        _ = (∑ k ∈ B, ∑ k' ∈ A \ B, ‖Infra.resolventColumn a V B z k p‖ * ‖a k k'‖ *
              Real.exp (μ * siteDist ν p k')) * M := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
        _ ≤ θ * M := mul_le_mul_of_nonneg_right hcr hM0
    by_cases hyB : y ∈ B
    · have hid := resolventColumn_eq_sub_sum_coupling_of_mem (a := a) hsymm V hBA hz hpB hyB
      have hd := hdirect p hp hyB
      rw [finiteGreen_eq_resolventColumn] at hd
      have hid' : Infra.resolventColumn a V A z y p =
          Infra.resolventColumn a V B z y p - S := hid
      have hn : ‖Infra.resolventColumn a V A z y p‖ ≤
          ‖Infra.resolventColumn a V B z y p‖ + ‖S‖ := by
        rw [hid']; exact norm_sub_le _ _
      have he : Real.exp (-μ * siteDist ν p y) * Real.exp (μ * siteDist ν p y) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 : ‖Infra.resolventColumn a V B z y p‖ * Real.exp (μ * siteDist ν p y) ≤ K := by
        calc _ ≤ K * Real.exp (-μ * siteDist ν p y) * Real.exp (μ * siteDist ν p y) :=
              mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
          _ = K := by rw [mul_assoc, he, mul_one]
      calc F p = ‖Infra.resolventColumn a V A z y p‖ * Real.exp (μ * siteDist ν p y) := rfl
        _ ≤ (‖Infra.resolventColumn a V B z y p‖ + ‖S‖) * Real.exp (μ * siteDist ν p y) :=
            mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
        _ ≤ K + θ * M := by rw [add_mul]; linarith
    · have hid := Infra.resolventColumn_eq_neg_sum_coupling (a := a) V hBA (hunit A) (hunit B)
        hpB hy hyB
      have hid' : Infra.resolventColumn a V A z y p = -S := hid
      have hn : ‖Infra.resolventColumn a V A z y p‖ = ‖S‖ := by rw [hid', norm_neg]
      calc F p = ‖Infra.resolventColumn a V A z y p‖ * Real.exp (μ * siteDist ν p y) := rfl
        _ = ‖S‖ * Real.exp (μ * siteDist ν p y) := by rw [hn]
        _ ≤ K + θ * M := by nlinarith
  have hMle : M ≤ K + θ * M := Finset.sup'_le _ _ fun p hp => key p hp
  have hM2 : M ≤ 2 * K := by nlinarith
  have hfx := hFM x hx
  simp only [hF] at hfx
  rw [finiteGreen_eq_resolventColumn]
  have hexp := Real.exp_pos (μ * siteDist ν x y)
  have he : Real.exp (-μ * siteDist ν x y) * Real.exp (μ * siteDist ν x y) = 1 := by
    rw [← Real.exp_add]; simp
  have : ‖Infra.resolventColumn a V A z y x‖ * Real.exp (μ * siteDist ν x y) ≤
      2 * K * Real.exp (-μ * siteDist ν x y) * Real.exp (μ * siteDist ν x y) := by
    rw [mul_assoc (2 * K), he, mul_one]; linarith
  exact le_of_mul_le_mul_right this hexp

end FroehlichSpencer.T12

end
