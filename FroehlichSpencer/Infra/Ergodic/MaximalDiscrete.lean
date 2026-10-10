/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Ergodic.Basic

/-!
# Discrete Hardy–Littlewood maximal inequality for cubes in `ℤ^ν`

For `φ ≥ 0` on `ℤ^ν`, a finite set `B` of centres and cubes of radius `≤ L₀`,
`t · #{x ∈ B | ∃ L ≤ L₀, avg_{x + cube L} φ > t} ≤ 3^ν ∑_{B + cube L₀} φ`, by a finite Vitali
covering argument.

This is the combinatorial core of the Wiener maximal inequality used for the
ergodic theorem behind the integrated density of states of Fröhlich–Spencer (1983),
Fröhlich–Spencer (1983).
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

private theorem sub_mem_cube_two_mul {r s : ℕ} {x y : Fin ν → ℤ} (hrs : s ≤ r)
    (h : ¬ y - x ∈ cube ν (2 * r)) :
    Disjoint ((cube ν r).image (x + ·)) ((cube ν s).image (y + ·)) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [Finset.mem_image] at hz hz'
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb, hab⟩ := hz'
  apply h
  rw [mem_cube] at ha hb ⊢
  intro i
  have h1 := ha i
  have h2 := hb i
  have h3 := congrFun hab i
  simp only [Pi.add_apply] at h3
  simp only [Pi.sub_apply]
  push_cast
  constructor <;> omega

/-- Finite Vitali selection by decreasing radius. -/
private theorem vitali_select (r : (Fin ν → ℤ) → ℕ) :
    ∀ (n : ℕ) (S : Finset (Fin ν → ℤ)), S.card = n →
      ∃ T ⊆ S, (∀ x ∈ T, ∀ y ∈ T, x ≠ y →
          Disjoint ((cube ν (r x)).image (x + ·)) ((cube ν (r y)).image (y + ·))) ∧
        ∀ x' ∈ S, ∃ x ∈ T, r x' ≤ r x ∧ x' - x ∈ cube ν (2 * r x) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨x₀, hx₀, hmax⟩ := S.exists_max_image r hne
    set S' := S.filter (fun x' => ¬ x' - x₀ ∈ cube ν (2 * r x₀)) with hS'
    have hx₀S' : x₀ ∉ S' := by
      intro h
      rw [hS', Finset.mem_filter] at h
      apply h.2
      rw [sub_self, mem_cube]
      intro i
      simp
    have hlt : S'.card < n := by
      rw [← hS]
      refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => hx₀S' (h hx₀)⟩
    obtain ⟨T', hT'S', hdisj, hcov⟩ := ih _ hlt S' rfl
    have hT'S : ∀ y ∈ T', y ∈ S ∧ ¬ y - x₀ ∈ cube ν (2 * r x₀) := fun y hy => by
      have := hT'S' hy
      rw [hS', Finset.mem_filter] at this
      exact this
    have hx₀T' : x₀ ∉ T' := fun h => hx₀S' (hT'S' h)
    refine ⟨insert x₀ T', ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hx₀
      · exact (hT'S y hy).1
    · intro x hx y hy hxy
      rcases Finset.mem_insert.1 hx with h1 | h1 <;> rcases Finset.mem_insert.1 hy with h2 | h2
      · exact absurd (h1.trans h2.symm) hxy
      · subst h1
        exact sub_mem_cube_two_mul (hmax y (hT'S y h2).1) (hT'S y h2).2
      · subst h2
        exact (sub_mem_cube_two_mul (hmax x (hT'S x h1).1) (hT'S x h1).2).symm
      · exact hdisj x h1 y h2 hxy
    · intro x' hx'
      by_cases h : x' - x₀ ∈ cube ν (2 * r x₀)
      · exact ⟨x₀, Finset.mem_insert_self _ _, hmax x' hx', h⟩
      · obtain ⟨x, hx, h1, h2⟩ := hcov x' (by rw [hS', Finset.mem_filter]; exact ⟨hx', h⟩)
        exact ⟨x, Finset.mem_insert_of_mem hx, h1, h2⟩

private theorem card_cube_two_mul_le (ν r : ℕ) :
    (cube ν (2 * r)).card ≤ 3 ^ ν * (cube ν r).card := by
  rw [card_cube, card_cube, ← mul_pow]
  exact Nat.pow_le_pow_left (by omega) ν

/-- Discrete maximal inequality: the number of centres `x ∈ B` with a cube average of `φ` above `t`
is at most `3^ν / t` times the mass of `φ` on `B + cube ν L₀`. -/
theorem mul_card_maximal_le {φ : (Fin ν → ℤ) → ℝ} (hφ : ∀ x, 0 ≤ φ x)
    (B : Finset (Fin ν → ℤ)) (L₀ : ℕ) {t : ℝ} (ht : 0 < t) :
    t * #{x ∈ B | ∃ L ≤ L₀, t < ((cube ν L).card : ℝ)⁻¹ * ∑ y ∈ cube ν L, φ (x + y)} ≤
      3 ^ ν * ∑ y ∈ B + cube ν L₀, φ y := by
  classical
  set Bad := B.filter (fun x => ∃ L ≤ L₀,
    t < ((cube ν L).card : ℝ)⁻¹ * ∑ y ∈ cube ν L, φ (x + y)) with hBad
  have hex : ∀ x, ∃ L : ℕ, x ∈ Bad → L ≤ L₀ ∧
      t * ((cube ν L).card : ℝ) < ∑ y ∈ cube ν L, φ (x + y) := by
    intro x
    by_cases hx : x ∈ Bad
    · rw [hBad, Finset.mem_filter] at hx
      obtain ⟨L, hL, h⟩ := hx.2
      refine ⟨L, fun _ => ⟨hL, ?_⟩⟩
      have hc : (0 : ℝ) < (cube ν L).card := by exact_mod_cast card_cube_pos ν L
      rwa [inv_mul_eq_div, lt_div_iff₀ hc] at h
    · exact ⟨0, fun h => absurd h hx⟩
  choose r hr using hex
  obtain ⟨T, hTB, hdisj, hcov⟩ := vitali_select r _ Bad rfl
  -- counting
  have hcount : (Bad.card : ℝ) ≤ 3 ^ ν * ∑ x ∈ T, ((cube ν (r x)).card : ℝ) := by
    have h1 : Bad ⊆ T.biUnion (fun x => (cube ν (2 * r x)).image (x + ·)) := by
      intro x' hx'
      obtain ⟨x, hx, -, h⟩ := hcov x' hx'
      rw [Finset.mem_biUnion]
      exact ⟨x, hx, Finset.mem_image.2 ⟨x' - x, h, by simp⟩⟩
    have h2 : Bad.card ≤ ∑ x ∈ T, 3 ^ ν * (cube ν (r x)).card :=
      calc Bad.card ≤ _ := Finset.card_le_card h1
        _ ≤ ∑ x ∈ T, ((cube ν (2 * r x)).image (x + ·)).card := Finset.card_biUnion_le
        _ ≤ _ := Finset.sum_le_sum fun x _ =>
          (Finset.card_image_le).trans (card_cube_two_mul_le ν (r x))
    have h3 : (Bad.card : ℝ) ≤ ∑ x ∈ T, (3 : ℝ) ^ ν * ((cube ν (r x)).card : ℝ) := by
      exact_mod_cast h2
    rwa [← Finset.mul_sum] at h3
  -- mass
  have hmass : t * ∑ x ∈ T, ((cube ν (r x)).card : ℝ) ≤ ∑ y ∈ B + cube ν L₀, φ y := by
    have hpd : (T : Set (Fin ν → ℤ)).PairwiseDisjoint
        (fun x => (cube ν (r x)).image (x + ·)) := fun x hx y hy hxy => hdisj x hx y hy hxy
    have hsub : T.biUnion (fun x => (cube ν (r x)).image (x + ·)) ⊆ B + cube ν L₀ := by
      intro z hz
      rw [Finset.mem_biUnion] at hz
      obtain ⟨x, hx, hz⟩ := hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hz
      have hxB : x ∈ Bad := hTB hx
      have hxB' : x ∈ B := (Finset.mem_filter.1 hxB).1
      exact Finset.add_mem_add hxB' (cube_mono (hr x hxB).1 ha)
    calc t * ∑ x ∈ T, ((cube ν (r x)).card : ℝ)
        = ∑ x ∈ T, t * ((cube ν (r x)).card : ℝ) := Finset.mul_sum _ _ _
      _ ≤ ∑ x ∈ T, ∑ y ∈ cube ν (r x), φ (x + y) :=
          Finset.sum_le_sum fun x hx => (hr x (hTB hx)).2.le
      _ = ∑ x ∈ T, ∑ z ∈ (cube ν (r x)).image (x + ·), φ z := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
      _ = ∑ z ∈ T.biUnion (fun x => (cube ν (r x)).image (x + ·)), φ z :=
          (Finset.sum_biUnion hpd).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hφ z
  calc t * (Bad.card : ℝ) ≤ t * (3 ^ ν * ∑ x ∈ T, ((cube ν (r x)).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hcount ht.le
    _ = 3 ^ ν * (t * ∑ x ∈ T, ((cube ν (r x)).card : ℝ)) := by ring
    _ ≤ 3 ^ ν * ∑ y ∈ B + cube ν L₀, φ y :=
        mul_le_mul_of_nonneg_left hmass (by positivity)

end FroehlichSpencer.Infra
