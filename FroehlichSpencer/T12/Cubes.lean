/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Multiscale.Basic

/-!
# Cubes, minimum covers and cover volume (Section 4)

Internal lemmas.
-/

@[expose] public section

namespace FroehlichSpencer.T12

/-- Spacing of `n`-cube centres: `2^(n-1)` for `n ≥ 1`, `1` for `n = 0`. -/
def cubeSpacing (n : ℕ) : ℤ := if n = 0 then 1 else 2 ^ (n - 1)
/-- Half side of an `n`-cube: `2^(n-1)` for `n ≥ 1`, `0` for `n = 0`. -/
def cubeHalfSide (n : ℕ) : ℤ := if n = 0 then 0 else 2 ^ (n - 1)

def dyCube {ν : ℕ} (n : ℕ) (k : Site ν) : Finset (Site ν) :=
  Fintype.piFinset fun i => Finset.Icc (cubeSpacing n * k i - cubeHalfSide n)
    (cubeSpacing n * k i + cubeHalfSide n)

def IsCubeCover {ν : ℕ} (n : ℕ) (D K : Finset (Site ν)) : Prop :=
  ∀ x ∈ D, ∃ k ∈ K, x ∈ dyCube n k

theorem cubeSpacing_pos (n : ℕ) : 0 < cubeSpacing n := by
  unfold cubeSpacing; split_ifs <;> positivity

theorem cubeHalfSide_nonneg (n : ℕ) : 0 ≤ cubeHalfSide n := by
  unfold cubeHalfSide; split_ifs <;> positivity

theorem cubeSpacing_le_add_one (n : ℕ) : cubeSpacing n ≤ cubeHalfSide n + 1 := by
  unfold cubeSpacing cubeHalfSide; split_ifs <;> simp

theorem mem_dyCube {ν : ℕ} {n : ℕ} {k x : Site ν} :
    x ∈ dyCube n k ↔ ∀ i, cubeSpacing n * k i - cubeHalfSide n ≤ x i ∧
      x i ≤ cubeSpacing n * k i + cubeHalfSide n := by
  simp [dyCube, Fintype.mem_piFinset]

theorem mem_dyCube_self {ν : ℕ} (n : ℕ) (x : Site ν) :
    x ∈ dyCube n (fun i => x i / cubeSpacing n) := by
  rw [mem_dyCube]
  intro i
  have hs := cubeSpacing_pos n
  have h1 := cubeSpacing_le_add_one n
  have h2 := cubeHalfSide_nonneg n
  have e := Int.mul_ediv_add_emod (x i) (cubeSpacing n)
  have h3 := Int.emod_nonneg (x i) hs.ne'
  have h4 := Int.emod_lt_of_pos (x i) hs
  constructor <;> linarith


theorem exists_isCubeCover {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) :
    ∃ m, ∃ K : Finset (Site ν), IsCubeCover n D K ∧ K.card = m := by
  classical
  refine ⟨(D.image fun x i => x i / cubeSpacing n).card, D.image fun x i => x i / cubeSpacing n,
    ?_, rfl⟩
  intro x hx
  exact ⟨fun i => x i / cubeSpacing n,
    (Finset.mem_image_of_mem (fun x i => x i / cubeSpacing n) hx :), mem_dyCube_self n x⟩


noncomputable def coverNumber {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) : ℕ := by
  classical exact Nat.find (exists_isCubeCover n D)


theorem exists_minCover {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) :
    ∃ K : Finset (Site ν), IsCubeCover n D K ∧ K.card = coverNumber n D := by
  classical
  unfold coverNumber
  obtain ⟨K, hK, hc⟩ := Nat.find_spec (exists_isCubeCover n D)
  exact ⟨K, hK, hc⟩


noncomputable def minCover {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) : Finset (Site ν) :=
  Classical.choose (exists_minCover n D)

/-- The Euclidean diameter of a finite set (`0` if empty). -/
noncomputable def finDiam {ν : ℕ} (D : Finset (Site ν)) : ℝ :=
  ((D ×ˢ D).sup fun p => Real.toNNReal (Multiscale.siteDist ν p.1 p.2) : NNReal)


theorem exists_two_mul_finDiam_le {ν : ℕ} (D : Finset (Site ν)) :
    ∃ n : ℕ, 2 * finDiam D ≤ 2 ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * finDiam D) (by norm_num : (1 : ℝ) < 2)
  exact ⟨n, hn.le⟩


noncomputable def topScale {ν : ℕ} (D : Finset (Site ν)) : ℕ := by
  classical exact Nat.find (exists_two_mul_finDiam_le D)


noncomputable def coverVolume {ν : ℕ} (D : Finset (Site ν)) : ℕ :=
  ∑ n ∈ Finset.range (topScale D + 1), coverNumber n D


noncomputable def cubeDist {ν : ℕ} (n : ℕ) (k k' : Site ν) : ℝ :=
  ((dyCube n k ×ˢ dyCube n k').inf fun p => ENNReal.ofReal (Multiscale.siteDist ν p.1 p.2)).toReal


noncomputable def isolatedCount {ν : ℕ} (α M : ℝ) (n : ℕ) (D : Finset (Site ν)) : ℕ := by
  classical exact ((minCover n D).filter fun k =>
    ∀ k' ∈ minCover n D, k' ≠ k → M * 2 ^ (α * n) ≤ cubeDist n k k').card


noncomputable def isolatedVolume {ν : ℕ} (α M : ℝ) (D : Finset (Site ν)) : ℕ :=
  ∑ n ∈ Finset.Icc 1 (topScale D), isolatedCount α M n D


theorem minCover_isCubeCover {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) :
    IsCubeCover n D (minCover n D) :=
  (Classical.choose_spec (exists_minCover n D)).1


theorem card_minCover {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) :
    (minCover n D).card = coverNumber n D :=
  (Classical.choose_spec (exists_minCover n D)).2


theorem coverNumber_le {ν : ℕ} {n : ℕ} {D K : Finset (Site ν)} (hK : IsCubeCover n D K) :
    coverNumber n D ≤ K.card := by
  classical
  unfold coverNumber
  exact Nat.find_min' _ ⟨K, hK, rfl⟩


theorem coverNumber_le_card {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) :
    coverNumber n D ≤ D.card := by
  classical
  refine (coverNumber_le (K := D.image fun x i => x i / cubeSpacing n) ?_).trans
    Finset.card_image_le
  exact fun x hx => ⟨_, Finset.mem_image_of_mem _ hx, mem_dyCube_self n x⟩


theorem one_le_coverNumber {ν : ℕ} (n : ℕ) {D : Finset (Site ν)} (hD : D.Nonempty) :
    1 ≤ coverNumber n D := by
  obtain ⟨x, hx⟩ := hD
  rw [← card_minCover]
  obtain ⟨k, hk, -⟩ := minCover_isCubeCover n D x hx
  exact Finset.card_pos.mpr ⟨k, hk⟩


theorem dyCube_zero {ν : ℕ} (k : Site ν) : dyCube 0 k = {k} := by
  ext x
  simp only [mem_dyCube, cubeSpacing, cubeHalfSide, Finset.mem_singleton, funext_iff]
  simp only [ite_true, one_mul, sub_zero, add_zero]
  exact forall_congr' fun i => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩


theorem coverNumber_zero {ν : ℕ} (D : Finset (Site ν)) : coverNumber 0 D = D.card := by
  refine le_antisymm (coverNumber_le_card 0 D) ?_
  rw [← card_minCover]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨k, hk, hxk⟩ := minCover_isCubeCover 0 D x hx
  rw [dyCube_zero, Finset.mem_singleton] at hxk
  rwa [hxk]


theorem abs_sub_le_siteDist {ν : ℕ} (x y : Site ν) (i : Fin ν) :
    |((x i - y i : ℤ) : ℝ)| ≤ Multiscale.siteDist ν x y := by
  rw [Multiscale.siteDist_eq_norm]
  have := Infra.Lattice.abs_latticeCast_apply_le_norm (x - y) i
  have e : Infra.Lattice.latticeCast x - Infra.Lattice.latticeCast y =
      Infra.Lattice.latticeCast (x - y) := by
    ext j; simp [Infra.Lattice.latticeCast]
  rw [e]
  simpa using this


theorem siteDist_le_finDiam {ν : ℕ} {D : Finset (Site ν)} {x y : Site ν} (hx : x ∈ D)
    (hy : y ∈ D) : Multiscale.siteDist ν x y ≤ finDiam D := by
  have h : Real.toNNReal (Multiscale.siteDist ν x y) ≤
      (D ×ˢ D).sup fun p => Real.toNNReal (Multiscale.siteDist ν p.1 p.2) :=
    Finset.le_sup (f := fun p : Site ν × Site ν => Real.toNNReal (Multiscale.siteDist ν p.1 p.2))
      (b := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)
  unfold finDiam
  have h' := (NNReal.coe_le_coe.mpr h)
  rwa [Real.coe_toNNReal _ (Multiscale.siteDist_nonneg ν x y)] at h'


theorem exists_subset_dyCube {ν : ℕ} (D : Finset (Site ν)) {n : ℕ}
    (h : 2 * finDiam D ≤ 2 ^ n) : ∃ k, D ⊆ dyCube n k := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, Finset.empty_subset _⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨x0, hx0⟩ := hne
    refine ⟨x0, ?_⟩
    rw [dyCube_zero]
    intro y hy
    rw [Finset.mem_singleton]
    by_contra hne'
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ x0 i := by
      by_contra hcon; push Not at hcon; exact hne' (funext hcon)
    have h1 := abs_sub_le_siteDist y x0 i
    have h2 := siteDist_le_finDiam hy hx0
    have h3 : (1 : ℤ) ≤ |y i - x0 i| := Int.one_le_abs (sub_ne_zero.mpr hi)
    have h4 : (1 : ℝ) ≤ |((y i - x0 i : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast h3
    norm_num at h
    linarith
  · have hh : cubeHalfSide n = 2 ^ (n - 1) := by
      unfold cubeHalfSide; simp [hn.ne']
    have hs : cubeSpacing n = 2 ^ (n - 1) := by
      unfold cubeSpacing; simp [hn.ne']
    have hpos : (0 : ℤ) < 2 ^ (n - 1) := by positivity
    have hreal : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hd : finDiam D ≤ ((2 ^ (n - 1) : ℤ) : ℝ) := by
      push_cast; linarith
    have key : ∀ i : Fin ν, ∃ k : ℤ, ∀ x ∈ D,
        2 ^ (n - 1) * k - 2 ^ (n - 1) ≤ x i ∧ x i ≤ 2 ^ (n - 1) * k + 2 ^ (n - 1) := by
      intro i
      have hne2 : (D.image fun x => x i).Nonempty := hne.image _
      set a := (D.image fun x => x i).min' hne2 with ha
      have hamem : a ∈ D.image fun x => x i := Finset.min'_mem _ _
      obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp hamem
      have hlow : ∀ x ∈ D, a ≤ x i := fun x hx =>
        Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)
      have hup : ∀ x ∈ D, x i ≤ a + 2 ^ (n - 1) := by
        intro x hx
        have h1 := abs_sub_le_siteDist x y i
        have h2 := siteDist_le_finDiam hx hy
        have h3 : ((x i - y i : ℤ) : ℝ) ≤ ((2 ^ (n - 1) : ℤ) : ℝ) :=
          (le_abs_self _).trans (h1.trans (h2.trans hd))
        have h4 : x i - y i ≤ 2 ^ (n - 1) := by exact_mod_cast h3
        omega
      refine ⟨(a + 2 ^ (n - 1)) / 2 ^ (n - 1), fun x hx => ?_⟩
      have e := Int.mul_ediv_add_emod (a + 2 ^ (n - 1)) (2 ^ (n - 1))
      have h3 := Int.emod_nonneg (a + 2 ^ (n - 1)) hpos.ne'
      have h4 := Int.emod_lt_of_pos (a + 2 ^ (n - 1)) hpos
      have := hlow x hx
      have := hup x hx
      constructor <;> linarith
    choose k hk using key
    refine ⟨k, fun x hx => ?_⟩
    rw [mem_dyCube, hh, hs]
    exact fun i => hk i x hx


theorem coverNumber_topScale {ν : ℕ} {D : Finset (Site ν)} (hD : D.Nonempty) :
    coverNumber (topScale D) D = 1 := by
  classical
  have hspec : 2 * finDiam D ≤ 2 ^ topScale D := by
    unfold topScale; exact Nat.find_spec (exists_two_mul_finDiam_le D)
  obtain ⟨k, hk⟩ := exists_subset_dyCube D hspec
  refine le_antisymm ?_ (one_le_coverNumber _ hD)
  have := coverNumber_le (K := {k}) (fun x hx => ⟨k, Finset.mem_singleton_self k, hk hx⟩)
  simpa using this

end FroehlichSpencer.T12
