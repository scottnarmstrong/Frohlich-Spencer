/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Cubes
import Mathlib.Data.Sym.Card

/-!
# Subordinate covers (Section 4)

Internal lemma.
-/

@[expose] public section

namespace FroehlichSpencer.T12

section Occupancy

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

private theorem card_occupancy_le (ch : ι → Finset β) (b m : ℕ) (hb : ∀ c, (ch c).card ≤ b) :
    ((Fintype.piFinset fun c => (ch c).powerset).filter
      (fun ψ => (∀ c, 1 ≤ (ψ c).card) ∧ ∑ c, (ψ c).card = m)).card ≤ (2 * b) ^ m := by
  classical
  set Ψ := (Fintype.piFinset fun c => (ch c).powerset).filter
      (fun ψ => (∀ c, 1 ≤ (ψ c).card) ∧ ∑ c, (ψ c).card = m) with hΨ
  let f : (ι → Finset β) → Multiset ι :=
    fun ψ => ∑ c, ((ψ c).card - 1) • ({c} : Multiset ι)
  have hcount : ∀ ψ c, (f ψ).count c = (ψ c).card - 1 := by
    intro ψ c
    simp [f, Multiset.count_sum', Multiset.count_singleton]
  have hfcard : ∀ ψ ∈ Ψ, Multiset.card (f ψ) = m - Fintype.card ι := by
    intro ψ hψ
    rw [hΨ, Finset.mem_filter] at hψ
    obtain ⟨-, h1, h2⟩ := hψ
    have hc : Multiset.card (f ψ) = ∑ c, ((ψ c).card - 1) := by
      simp [f, Multiset.card_sum]
    have hc1 : ∑ _c : ι, 1 = Fintype.card ι := by simp
    have : ∑ c, ((ψ c).card - 1) + Fintype.card ι = m := by
      rw [← h2, ← hc1, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => Nat.sub_add_cancel (h1 c)
    rw [hc]
    omega
  have himg : (Ψ.image f).card ≤ 2 ^ m := by
    by_cases hle : Fintype.card ι ≤ m
    swap
    · have : Ψ = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun ψ hψ => hle ?_
        rw [hΨ, Finset.mem_filter] at hψ
        calc Fintype.card ι = ∑ _c : ι, 1 := by simp
          _ ≤ ∑ c, (ψ c).card := Finset.sum_le_sum fun c _ => hψ.2.1 c
          _ = m := hψ.2.2
      simp [this]
    have hsub : Ψ.image f ⊆ (Finset.univ : Finset (Sym ι (m - Fintype.card ι))).image
        (fun s : Sym ι (m - Fintype.card ι) => s.1) := by
      intro M hM
      obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hM
      exact Finset.mem_image.mpr ⟨⟨f ψ, hfcard ψ hψ⟩, Finset.mem_univ _, rfl⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_univ, Sym.card_sym_eq_choose]
    refine (Nat.choose_le_two_pow _ _).trans ?_
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have hfib : ∀ M ∈ Ψ.image f, (Ψ.filter fun ψ => f ψ = M).card ≤ b ^ m := by
    intro M hM
    obtain ⟨ψ0, hψ0, rfl⟩ := Finset.mem_image.mp hM
    have hsub : Ψ.filter (fun ψ => f ψ = f ψ0) ⊆
        Fintype.piFinset fun c => (ch c).powersetCard (ψ0 c).card := by
      intro ψ hψ
      rw [Finset.mem_filter] at hψ
      have h1 := hψ.1
      rw [hΨ, Finset.mem_filter, Fintype.mem_piFinset] at h1
      rw [Fintype.mem_piFinset]
      intro c
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.mem_powerset.mp (h1.1 c), ?_⟩
      have := hcount ψ c
      rw [hψ.2, hcount ψ0 c] at this
      have a1 := h1.2.1 c
      have a2 : 1 ≤ (ψ0 c).card := by
        have := hψ0; rw [hΨ, Finset.mem_filter] at this; exact this.2.1 c
      omega
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset]
    simp only [Finset.card_powersetCard]
    calc ∏ c, ((ch c).card.choose (ψ0 c).card) ≤ ∏ c, b ^ (ψ0 c).card := by
          refine Finset.prod_le_prod (fun c _ => ?_)
          exact (Nat.choose_le_pow _ _).trans
            (Nat.pow_le_pow_left (hb c) _)
      _ = b ^ m := by
          rw [Finset.prod_pow_eq_pow_sum]
          have := hψ0; rw [hΨ, Finset.mem_filter] at this; rw [this.2.2]
  calc Ψ.card ≤ b ^ m * (Ψ.image f).card := Finset.card_le_mul_card_image Ψ _ hfib
    _ ≤ b ^ m * 2 ^ m := Nat.mul_le_mul_left _ himg
    _ = (2 * b) ^ m := by rw [mul_pow, mul_comm]

end Occupancy

section Children

/-- The `3 ^ ν` candidate centre indices of `(n-1)`-cubes inside the `n`-cube of index `k`. -/
private def children {ν : ℕ} (n : ℕ) (k : Site ν) : Finset (Site ν) :=
  Fintype.piFinset fun i => Finset.Icc ((if n = 1 then 1 else 2) * k i - 1)
    ((if n = 1 then 1 else 2) * k i + 1)

private theorem card_children {ν : ℕ} (n : ℕ) (k : Site ν) : (children n k).card = 3 ^ ν := by
  rw [children, Fintype.card_piFinset]
  have : ∀ i : Fin ν, (Finset.Icc ((if n = 1 then 1 else 2) * k i - 1)
      ((if n = 1 then 1 else 2) * k i + 1)).card = 3 := by
    intro i
    rw [Int.card_Icc]
    have : (if n = 1 then (1 : ℤ) else 2) * k i + 1 + 1 -
        ((if n = 1 then 1 else 2) * k i - 1) = 3 := by ring
    rw [this]; rfl
  rw [Finset.prod_congr rfl fun i _ => this i]
  simp

private theorem mem_children_of_subset {ν : ℕ} {n : ℕ} (hn : 1 ≤ n) {k k' : Site ν}
    (h : dyCube (n - 1) k' ⊆ dyCube n k) : k' ∈ children n k := by
  have hlow := fun i => (mem_dyCube.mp (h (show
    (fun j => cubeSpacing (n - 1) * k' j - cubeHalfSide (n - 1)) ∈ dyCube (n - 1) k' from
    mem_dyCube.mpr fun j => ⟨le_rfl, by linarith [cubeHalfSide_nonneg (n - 1)]⟩)) i).1
  have hup := fun i => (mem_dyCube.mp (h (show
    (fun j => cubeSpacing (n - 1) * k' j + cubeHalfSide (n - 1)) ∈ dyCube (n - 1) k' from
    mem_dyCube.mpr fun j => ⟨by linarith [cubeHalfSide_nonneg (n - 1)], le_rfl⟩)) i).2
  rw [children, Fintype.mem_piFinset]
  intro i
  have h1 := hlow i
  have h2 := hup i
  rw [Finset.mem_Icc]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1 h2
  rcases j with _ | j
  · have e1 : cubeSpacing 1 = 1 := by simp [cubeSpacing]
    have e2 : cubeHalfSide 1 = 1 := by simp [cubeHalfSide]
    have e3 : cubeSpacing 0 = 1 := by simp [cubeSpacing]
    have e4 : cubeHalfSide 0 = 0 := by simp [cubeHalfSide]
    rw [e1, e2, e3, e4] at h1 h2
    simp only [zero_add, ite_true]
    constructor <;> linarith
  · have ht : (0 : ℤ) < 2 ^ j := by positivity
    have e1 : cubeSpacing (j + 1 + 1) = 2 * 2 ^ j := by
      simp [cubeSpacing, pow_succ]; ring
    have e2 : cubeHalfSide (j + 1 + 1) = 2 * 2 ^ j := by
      simp [cubeHalfSide, pow_succ]; ring
    have e3 : cubeSpacing (j + 1) = 2 ^ j := by simp [cubeSpacing]
    have e4 : cubeHalfSide (j + 1) = 2 ^ j := by simp [cubeHalfSide]
    rw [e1, e2, e3, e4] at h1 h2
    have hne : j + 1 + 1 ≠ 1 := by omega
    simp only [hne, ite_false]
    have a1 : 0 ≤ 2 ^ j * (k' i - 2 * k i + 1) := by linarith
    have a2 : 0 ≤ 2 ^ j * (2 * k i + 1 - k' i) := by linarith
    have b1 := (mul_nonneg_iff_of_pos_left ht).mp a1
    have b2 := (mul_nonneg_iff_of_pos_left ht).mp a2
    constructor <;> linarith

end Children

/-- Essential witnesses: every cube of a minimum cover has a point of `D` covered by no other. -/
private theorem exists_essential {ν : ℕ} {n : ℕ} {D K : Finset (Site ν)} (hK : IsCubeCover n D K)
    (hKmin : K.card = coverNumber n D) {c : Site ν} (hc : c ∈ K) :
    ∃ x ∈ D, x ∈ dyCube n c ∧ ∀ c' ∈ K, x ∈ dyCube n c' → c' = c := by
  classical
  by_contra h
  push Not at h
  have hcov : IsCubeCover n D (K.erase c) := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hK x hx
    by_cases hkc : k = c
    · subst hkc
      obtain ⟨c', hc', hxc', hne⟩ := h x hx hxk
      exact ⟨c', Finset.mem_erase.mpr ⟨hne, hc'⟩, hxc'⟩
    · exact ⟨k, Finset.mem_erase.mpr ⟨hkc, hk⟩, hxk⟩
  have h1 := coverNumber_le hcov
  have h2 := Finset.card_erase_lt_of_mem hc
  omega

/-- The parent chosen for `k'`: some `k ∈ K` with `dyCube (n-1) k' ⊆ dyCube n k`, if any. -/
private noncomputable def parentOf {ν : ℕ} (n : ℕ) (K : Finset (Site ν)) (k' : Site ν) :
    Site ν := by
  classical exact if h : ∃ k ∈ K, dyCube (n - 1) k' ⊆ dyCube n k then h.choose else k'

private theorem parentOf_spec {ν : ℕ} {n : ℕ} {K : Finset (Site ν)} {k' : Site ν}
    (h : ∃ k ∈ K, dyCube (n - 1) k' ⊆ dyCube n k) :
    parentOf n K k' ∈ K ∧ dyCube (n - 1) k' ⊆ dyCube n (parentOf n K k') := by
  classical
  unfold parentOf
  simp only [h, ↓reduceDIte]
  exact h.choose_spec


theorem ncard_subordinateCovers_le {ν : ℕ} {n : ℕ} (hn : 1 ≤ n) {D K : Finset (Site ν)}
    (hK : IsCubeCover n D K) (hKmin : K.card = coverNumber n D) (m : ℕ) :
    {K' : Finset (Site ν) | IsCubeCover (n - 1) D K' ∧ K'.card = m ∧
        ∀ k' ∈ K', ∃ k ∈ K, dyCube (n - 1) k' ⊆ dyCube n k}.ncard ≤ (2 * 3 ^ ν) ^ m := by
  classical
  let ch : ↥K → Finset (Site ν) := fun c => children n c.1
  let Ψ := (Fintype.piFinset fun c : ↥K => (ch c).powerset).filter
      (fun ψ => (∀ c, 1 ≤ (ψ c).card) ∧ ∑ c, (ψ c).card = m)
  have hΨ : Ψ.card ≤ (2 * 3 ^ ν) ^ m :=
    card_occupancy_le ch (3 ^ ν) m fun c => (card_children n c.1).le
  let enc : Finset (Site ν) → ↥K → Finset (Site ν) :=
    fun K' c => K'.filter fun k' => parentOf n K k' = c.1
  have hmaps : ∀ K' ∈ {K' : Finset (Site ν) | IsCubeCover (n - 1) D K' ∧ K'.card = m ∧
        ∀ k' ∈ K', ∃ k ∈ K, dyCube (n - 1) k' ⊆ dyCube n k}, enc K' ∈ (Ψ : Set _) := by
    rintro K' ⟨hcov, hcard, hsub⟩
    have hpar := fun k' hk' => parentOf_spec (hsub k' hk')
    rw [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun c => ?_, fun c => ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro k' hk'
      rw [Finset.mem_filter] at hk'
      have := (hpar k' hk'.1).2
      rw [hk'.2] at this
      exact mem_children_of_subset hn this
    · obtain ⟨x, hxD, hxc, hxu⟩ := exists_essential hK hKmin c.2
      obtain ⟨k', hk', hxk'⟩ := hcov x hxD
      have hp := hpar k' hk'
      have : parentOf n K k' = c.1 := hxu _ hp.1 (hp.2 hxk')
      exact Finset.card_pos.mpr ⟨k', Finset.mem_filter.mpr ⟨hk', this⟩⟩
    · rw [← hcard, Finset.card_eq_sum_card_fiberwise (f := parentOf n K)
        (t := K) (fun k' hk' => (hpar k' hk').1)]
      exact (Finset.sum_coe_sort K fun c => (K'.filter fun k' => parentOf n K k' = c).card)
  refine (Set.ncard_le_ncard_of_injOn enc hmaps ?_ (Finset.finite_toSet Ψ)).trans ?_
  · rintro K' ⟨hcov, hcard, hsub⟩ K'' ⟨hcov', hcard', hsub'⟩ heq
    have key : ∀ (A : Finset (Site ν)), (∀ k' ∈ A, ∃ k ∈ K, dyCube (n - 1) k' ⊆ dyCube n k) →
        A = Finset.univ.biUnion (enc A) := by
      intro A hA
      ext k'
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, enc, Finset.mem_filter]
      constructor
      · intro hk'
        exact ⟨⟨_, (parentOf_spec (hA k' hk')).1⟩, hk', rfl⟩
      · rintro ⟨c, hk', -⟩; exact hk'
    rw [key K' hsub, key K'' hsub', heq]
  · rw [Set.ncard_coe_finset]; exact hΨ

end FroehlichSpencer.T12
