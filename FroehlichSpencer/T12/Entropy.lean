/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Cubes

/-!
# Entropy: the number of sets with a given cover volume (Section 4)

Internal lemma.

Proof: a set `D` is recovered from its chain of minimum covers `C_n(D)`, since `C_0(D) = D`.

Every cube of `C_n(D)` meets `D`, hence meets a cube of `C_{n+1}(D)`, so `C_n(D)` lies in a fixed
set of at most `7^ν |C_{n+1}(D)|` candidate centres.

Counting the possible chains level by level
gives at most `exp (7^ν V)` sets with a given top cube; with the `≤ 3^ν` top cubes containing `x`
and `n₀ < V` levels the total is at most `exp (Kν V)`, `Kν = 1 + 2ν + 7^ν`.
-/

@[expose] public section

namespace FroehlichSpencer.T12

/-- Candidate level-`n` centres whose cube meets the `(n+1)`-cube of centre `k`. -/
private def nbr {ν : ℕ} (n : ℕ) (k : Site ν) : Finset (Site ν) :=
  Fintype.piFinset fun i => Finset.Icc (cubeSpacing (n + 1) / cubeSpacing n * k i - 3)
    (cubeSpacing (n + 1) / cubeSpacing n * k i + 3)

/-- Candidate centres of the `n`-cubes containing `x`. -/
private def cen {ν : ℕ} (n : ℕ) (x : Site ν) : Finset (Site ν) :=
  Fintype.piFinset fun i => Finset.Icc (x i / cubeSpacing n - 1) (x i / cubeSpacing n + 1)

private theorem card_nbr {ν : ℕ} (n : ℕ) (k : Site ν) : (nbr n k).card = 7 ^ ν := by
  have h : ∀ i : Fin ν, (cubeSpacing (n + 1) / cubeSpacing n * k i + 3 + 1 -
      (cubeSpacing (n + 1) / cubeSpacing n * k i - 3)).toNat = 7 := fun i => by omega
  simp [nbr, Fintype.card_piFinset, h]

private theorem card_cen {ν : ℕ} (n : ℕ) (x : Site ν) : (cen n x).card = 3 ^ ν := by
  have h : ∀ i : Fin ν, (x i / cubeSpacing n + 1 + 1 - (x i / cubeSpacing n - 1)).toNat = 3 :=
    fun i => by omega
  simp [cen, Fintype.card_piFinset, h]

private theorem mem_nbr_of_mem_dyCube {ν n : ℕ} {k k' y : Site ν} (h1 : y ∈ dyCube n k')
    (h2 : y ∈ dyCube (n + 1) k) : k' ∈ nbr n k := by
  rw [mem_dyCube] at h1 h2
  simp only [nbr, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  obtain ⟨a1, a2⟩ := h1 i
  obtain ⟨b1, b2⟩ := h2 i
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cubeSpacing, cubeHalfSide] at a1 a2 b1 b2 ⊢
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ht : (0 : ℤ) < 2 ^ m := by positivity
    have e1 : cubeSpacing (m + 1) = 2 ^ m := by simp [cubeSpacing]
    have e2 : cubeHalfSide (m + 1) = 2 ^ m := by simp [cubeHalfSide]
    have e3 : cubeSpacing (m + 1 + 1) = 2 * 2 ^ m := by
      simp [cubeSpacing, pow_succ]; ring
    have e4 : cubeHalfSide (m + 1 + 1) = 2 * 2 ^ m := by
      simp [cubeHalfSide, pow_succ]; ring
    rw [e1, e2] at a1 a2
    rw [e3, e4] at b1 b2
    rw [e3, e1, Int.mul_ediv_cancel _ ht.ne']
    constructor
    · by_contra hc
      have : k' i ≤ 2 * k i - 4 := by omega
      nlinarith
    · by_contra hc
      have : 2 * k i + 4 ≤ k' i := by omega
      nlinarith

private theorem mem_cen_of_mem_dyCube {ν n : ℕ} {k x : Site ν} (h : x ∈ dyCube n k) :
    k ∈ cen n x := by
  rw [mem_dyCube] at h
  simp only [cen, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  obtain ⟨a1, a2⟩ := h i
  have hs := cubeSpacing_pos n
  have hh : cubeHalfSide n ≤ cubeSpacing n := by
    unfold cubeHalfSide cubeSpacing; split_ifs <;> simp
  have h0 := cubeHalfSide_nonneg n
  have e := Int.mul_ediv_add_emod (x i) (cubeSpacing n)
  have h3 := Int.emod_nonneg (x i) hs.ne'
  have h4 := Int.emod_lt_of_pos (x i) hs
  generalize x i / cubeSpacing n = q at *
  generalize x i % cubeSpacing n = r at *
  constructor
  · by_contra hc
    have : k i ≤ q - 2 := by omega
    nlinarith
  · by_contra hc
    have : q + 2 ≤ k i := by omega
    nlinarith

/-- Every cube of a minimum cover meets the set. -/
private theorem exists_mem_dyCube_of_mem_minCover {ν n : ℕ} {D : Finset (Site ν)}
    {k : Site ν} (hk : k ∈ minCover n D) : ∃ y ∈ D, y ∈ dyCube n k := by
  classical
  by_contra hc
  push Not at hc
  have hcov : IsCubeCover n D ((minCover n D).erase k) := by
    intro y hy
    obtain ⟨k₁, hk₁, hy₁⟩ := minCover_isCubeCover n D y hy
    refine ⟨k₁, Finset.mem_erase.mpr ⟨?_, hk₁⟩, hy₁⟩
    rintro rfl
    exact hc y hy hy₁
  have h1 := coverNumber_le hcov
  rw [Finset.card_erase_of_mem hk, card_minCover] at h1
  have : 0 < (minCover n D).card := Finset.card_pos.mpr ⟨k, hk⟩
  rw [card_minCover] at this
  omega

private theorem minCover_subset_biUnion_nbr {ν : ℕ} (n : ℕ) (D : Finset (Site ν)) :
    minCover n D ⊆ (minCover (n + 1) D).biUnion (nbr n) := by
  classical
  intro k' hk'
  obtain ⟨y, hy, hyk'⟩ := exists_mem_dyCube_of_mem_minCover hk'
  obtain ⟨k, hk, hyk⟩ := minCover_isCubeCover (n + 1) D y hy
  exact Finset.mem_biUnion.mpr ⟨k, hk, mem_nbr_of_mem_dyCube hyk' hyk⟩

private theorem minCover_zero {ν : ℕ} (D : Finset (Site ν)) : minCover 0 D = D := by
  have hc := card_minCover 0 D
  rw [coverNumber_zero] at hc
  have hsub : D ⊆ minCover 0 D := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := minCover_isCubeCover 0 D x hx
    rw [dyCube_zero, Finset.mem_singleton] at hxk
    rwa [hxk]
  exact (Finset.eq_of_subset_of_card_le hsub hc.le).symm

private theorem two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp m := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := pow_le_pow_left₀ (by norm_num) h m
    _ = Real.exp m := by rw [← Real.exp_nat_mul]; simp

/-- The chain-counting step: sets with a given level-`n` minimum cover `K` and given sum of the
lower cover numbers lie in a finite family of controlled size. -/
private theorem exists_finset_cover (ν : ℕ) (n : ℕ) : ∀ (K : Finset (Site ν)) (W : ℕ),
    ∃ F : Finset (Finset (Site ν)),
      {D : Finset (Site ν) | minCover n D = K ∧
        ∑ j ∈ Finset.range n, coverNumber j D = W} ⊆ ↑F ∧
        (F.card : ℝ) ≤ Real.exp (((7 ^ ν : ℕ) : ℝ) * W) *
          Real.exp (((7 ^ ν : ℕ) : ℝ) * K.card) := by
  classical
  induction n with
  | zero =>
    intro K W
    refine ⟨{K}, ?_, ?_⟩
    · intro D hD
      obtain ⟨h1, -⟩ := hD
      rw [minCover_zero] at h1
      simp [h1]
    · rw [← Real.exp_add]
      simp only [Finset.card_singleton, Nat.cast_one]
      exact Real.one_le_exp (by positivity)
  | succ n ih =>
    intro K W
    choose G hG using fun K' => ih K' (W - K'.card)
    set N : Finset (Site ν) := K.biUnion (nbr n) with hN
    set P : Finset (Finset (Site ν)) := N.powerset.filter fun K' => K'.card ≤ W with hP
    refine ⟨P.biUnion G, ?_, ?_⟩
    · rintro D ⟨h1, h2⟩
      rw [Finset.sum_range_succ, ← card_minCover] at h2
      have hmem : minCover n D ∈ P := by
        rw [hP, Finset.mem_filter, Finset.mem_powerset, hN, ← h1]
        exact ⟨minCover_subset_biUnion_nbr n D, by omega⟩
      rw [Finset.coe_biUnion]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hmem) ((hG _).1 ⟨rfl, by omega⟩)
    · have hNc : N.card ≤ K.card * 7 ^ ν := by
        calc N.card ≤ ∑ k ∈ K, (nbr n k).card := Finset.card_biUnion_le
          _ = K.card * 7 ^ ν := by simp [card_nbr]
      have hPc : (P.card : ℝ) ≤ Real.exp (((7 ^ ν : ℕ) : ℝ) * K.card) := by
        have h1 : P.card ≤ 2 ^ N.card := by
          calc P.card ≤ N.powerset.card := Finset.card_filter_le _ _
            _ = 2 ^ N.card := Finset.card_powerset N
        calc (P.card : ℝ) ≤ ((2 ^ N.card : ℕ) : ℝ) := by exact_mod_cast h1
          _ = (2 : ℝ) ^ N.card := by push_cast; rfl
          _ ≤ Real.exp N.card := two_pow_le_exp _
          _ ≤ _ := by
            apply Real.exp_le_exp.mpr
            have : (N.card : ℝ) ≤ (K.card * 7 ^ ν : ℕ) := by exact_mod_cast hNc
            push_cast at this ⊢
            linarith
      calc ((P.biUnion G).card : ℝ) ≤ ∑ K' ∈ P, ((G K').card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ K' ∈ P, Real.exp (((7 ^ ν : ℕ) : ℝ) * W) := by
            refine Finset.sum_le_sum fun K' hK' => ?_
            have hle : K'.card ≤ W := (Finset.mem_filter.mp hK').2
            refine ((hG K').2).trans (le_of_eq ?_)
            rw [← Real.exp_add]
            congr 1
            rw [Nat.cast_sub hle]
            ring
        _ = P.card * Real.exp (((7 ^ ν : ℕ) : ℝ) * W) := by simp
        _ ≤ Real.exp (((7 ^ ν : ℕ) : ℝ) * K.card) * Real.exp (((7 ^ ν : ℕ) : ℝ) * W) :=
            mul_le_mul_of_nonneg_right hPc (Real.exp_pos _).le
        _ = _ := mul_comm _ _

private theorem mem_family {ν : ℕ} {x : Site ν} {V : ℕ} {D : Finset (Site ν)}
    (hx : x ∈ D) (hV : coverVolume D = V) :
    ∃ n₀ k₀, n₀ < V ∧ k₀ ∈ cen n₀ x ∧ minCover n₀ D = {k₀} ∧
      ∑ j ∈ Finset.range n₀, coverNumber j D = V - 1 := by
  have hne : D.Nonempty := ⟨x, hx⟩
  have h1 : (minCover (topScale D) D).card = 1 := by
    rw [card_minCover]; exact coverNumber_topScale hne
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp h1
  have hsum : ∑ j ∈ Finset.range (topScale D + 1), coverNumber j D = V := hV
  have hlow : topScale D + 1 ≤ V := by
    rw [← hsum]
    calc topScale D + 1 = ∑ j ∈ Finset.range (topScale D + 1), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => one_le_coverNumber j hne
  have hcov := minCover_isCubeCover (topScale D) D x hx
  rw [hk₀] at hcov
  obtain ⟨k, hk, hxk⟩ := hcov
  rw [Finset.mem_singleton] at hk
  subst hk
  refine ⟨topScale D, k, by omega, mem_cen_of_mem_dyCube hxk, hk₀, ?_⟩
  rw [Finset.sum_range_succ, coverNumber_topScale hne] at hsum
  omega


theorem exists_ncard_coverVolume_le (ν : ℕ) :
    ∃ Kν : ℝ, ∀ (x : Site ν) (V : ℕ),
      {D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.Finite ∧
        (({D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.ncard : ℕ) : ℝ) ≤
          Real.exp (Kν * V) := by
  classical
  choose Fm hFm using exists_finset_cover ν
  refine ⟨1 + 2 * ν + ((7 ^ ν : ℕ) : ℝ), fun x V => ?_⟩
  set F : Finset (Finset (Site ν)) := (Finset.range V).biUnion fun n =>
    (cen n x).biUnion fun k => Fm n {k} (V - 1) with hF
  have hsub : {D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V} ⊆ ↑F := by
    rintro D ⟨hx, hV⟩
    obtain ⟨n₀, k₀, hn, hk, h1, h2⟩ := mem_family hx hV
    rw [hF, Finset.coe_biUnion]
    refine Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hn)) ?_
    rw [Finset.coe_biUnion]
    exact Set.mem_biUnion (Finset.mem_coe.mpr hk) ((hFm n₀ {k₀} (V - 1)).1 ⟨h1, h2⟩)
  have hfin : {D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.Finite :=
    F.finite_toSet.subset hsub
  refine ⟨hfin, ?_⟩
  have hcard : ((({D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.ncard : ℕ)) : ℝ) ≤
      F.card := by
    have := Set.ncard_le_ncard hsub F.finite_toSet
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  refine hcard.trans ?_
  rcases Nat.eq_zero_or_pos V with rfl | hV
  · simp [hF]
  set c : ℝ := ((7 ^ ν : ℕ) : ℝ) with hc
  have hterm : ∀ n ∈ Finset.range V, ∀ k : Site ν,
      ((Fm n {k} (V - 1)).card : ℝ) ≤ Real.exp (c * V) := by
    intro n hn k
    have hV1 : 1 ≤ V := by have := Finset.mem_range.mp hn; omega
    refine ((hFm n {k} (V - 1)).2).trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hV1]
    simp
    ring
  have h3 : ((3 ^ ν : ℕ) : ℝ) ≤ Real.exp (2 * ν * V) := by
    have h : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    calc ((3 ^ ν : ℕ) : ℝ) = (3 : ℝ) ^ ν := by push_cast; rfl
      _ ≤ Real.exp 2 ^ ν := pow_le_pow_left₀ (by norm_num) h ν
      _ = Real.exp (2 * ν) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (2 * ν * V) := by
        apply Real.exp_le_exp.mpr
        have : (1 : ℝ) ≤ V := by exact_mod_cast hV
        have : (0 : ℝ) ≤ ν := by positivity
        nlinarith
  calc (F.card : ℝ) ≤ ∑ n ∈ Finset.range V, (((cen n x).biUnion fun k => Fm n {k} (V - 1)).card
        : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ n ∈ Finset.range V, (((3 ^ ν : ℕ) : ℝ) * Real.exp (c * V)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have h1 : (((cen n x).biUnion fun k => Fm n {k} (V - 1)).card : ℝ) ≤
            ∑ k ∈ cen n x, ((Fm n {k} (V - 1)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        refine h1.trans ?_
        calc ∑ k ∈ cen n x, ((Fm n {k} (V - 1)).card : ℝ)
            ≤ ∑ k ∈ cen n x, Real.exp (c * V) :=
              Finset.sum_le_sum fun k _ => hterm n hn k
          _ = _ := by rw [Finset.sum_const, card_cen]; simp
    _ = V * (((3 ^ ν : ℕ) : ℝ) * Real.exp (c * V)) := by simp
    _ ≤ Real.exp V * (Real.exp (2 * ν * V) * Real.exp (c * V)) := by
        have hV' : (V : ℝ) ≤ Real.exp V := by linarith [Real.add_one_le_exp (V : ℝ)]
        have := Real.exp_pos (c * V)
        have := Real.exp_pos (2 * ν * V)
        have h4 : ((3 ^ ν : ℕ) : ℝ) * Real.exp (c * V) ≤ Real.exp (2 * ν * V) * Real.exp (c * V) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        exact mul_le_mul hV' h4 (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((1 + 2 * ν + c) * V) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := le_refl _

end FroehlichSpencer.T12
