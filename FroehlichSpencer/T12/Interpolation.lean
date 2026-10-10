/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Cubes
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Scale recurrence and entropy interpolation (Section 4)

Internal lemmas.
-/

@[expose] public section

namespace FroehlichSpencer.T12

/-! ### Grouping argument -/

private theorem exists_matching {β : Type*} [DecidableEq β] (K : Finset β) (R : β → β → Prop) :
    ∃ P : Finset (β × β), (∀ p ∈ P, p.1 ∈ K ∧ p.2 ∈ K ∧ R p.1 p.2) ∧ 2 * P.card ≤ K.card ∧
      ∀ k ∈ K, (∃ k' ∈ K, k' ≠ k ∧ R k k') →
        ∃ p ∈ P, k = p.1 ∨ k = p.2 ∨ R k p.1 ∨ R k p.2 := by
  classical
  let Good : Finset (β × β) → Prop := fun P =>
    (∀ p ∈ P, p.1 ∈ K ∧ p.2 ∈ K ∧ R p.1 p.2) ∧
    (∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q) ∧ (∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q) ∧
    (∀ p ∈ P, ∀ q ∈ P, p.1 ≠ q.2)
  have hne : ((K ×ˢ K).powerset.filter Good).Nonempty :=
    ⟨∅, by simp [Good]⟩
  obtain ⟨P, hPmem, hPmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hPmem
  obtain ⟨h1, h2, h3, h4⟩ := hPmem.2
  refine ⟨P, h1, ?_, ?_⟩
  · have hi1 : (P.image Prod.fst).card = P.card :=
      Finset.card_image_of_injOn fun p hp q hq h => h2 p hp q hq h
    have hi2 : (P.image Prod.snd).card = P.card :=
      Finset.card_image_of_injOn fun p hp q hq h => h3 p hp q hq h
    have hd : Disjoint (P.image Prod.fst) (P.image Prod.snd) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp hx'
      exact h4 p hp q hq hq'.symm
    have hsub : P.image Prod.fst ∪ P.image Prod.snd ⊆ K := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx; exact (h1 p hp).1
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx; exact (h1 p hp).2.1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, hi1, hi2] at this
    omega
  · intro k hk ⟨k', hk', hkk', hR⟩
    by_contra hcon
    push Not at hcon
    have hk1 : ∀ p ∈ P, k ≠ p.1 ∧ k ≠ p.2 := fun p hp =>
      ⟨(hcon p hp).1, (hcon p hp).2.1⟩
    have hk2 : ∀ p ∈ P, k' ≠ p.1 ∧ k' ≠ p.2 := by
      intro p hp
      constructor
      · rintro rfl; exact (hcon p hp).2.2.1 hR
      · rintro rfl; exact (hcon p hp).2.2.2 hR
    have hgood : Good (insert (k, k') P) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact ⟨hk, hk', hR⟩
        · exact h1 p hp
      · intro p hp q hq h
        rcases Finset.mem_insert.mp hp with rfl | hp <;>
          rcases Finset.mem_insert.mp hq with rfl | hq
        · rfl
        · exact absurd h (hk1 q hq).1
        · exact absurd h.symm (hk1 p hp).1
        · exact h2 p hp q hq h
      · intro p hp q hq h
        rcases Finset.mem_insert.mp hp with rfl | hp <;>
          rcases Finset.mem_insert.mp hq with rfl | hq
        · rfl
        · exact absurd h (hk2 q hq).2
        · exact absurd h.symm (hk2 p hp).2
        · exact h3 p hp q hq h
      · intro p hp q hq h
        rcases Finset.mem_insert.mp hp with rfl | hp <;>
          rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hkk'.symm h
        · exact (hk1 q hq).2 h
        · exact (hk2 p hp).1 h.symm
        · exact h4 p hp q hq h
    have hmem : insert (k, k') P ∈ (K ×ˢ K).powerset.filter Good := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, hgood⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Finset.mem_product.mpr ⟨hk, hk'⟩
      · exact hPmem.1 hp
    have hnot : (k, k') ∉ P := fun h => (hk1 _ h).1 rfl
    have := hPmax _ hmem
    rw [Finset.card_insert_of_notMem hnot] at this
    omega

/-! ### Cube geometry -/

private theorem two_mul_cubeHalfSide_le (m : ℕ) : 2 * cubeHalfSide m ≤ 2 ^ m := by
  unfold cubeHalfSide
  split_ifs with h
  · simp
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp [pow_succ, mul_comm]

private theorem siteDist_le_of_mem_dyCube {ν : ℕ} {m : ℕ} {k x y : Site ν}
    (hx : x ∈ dyCube m k) (hy : y ∈ dyCube m k) :
    Multiscale.siteDist ν x y ≤ Real.sqrt ν * 2 ^ m := by
  rw [mem_dyCube] at hx hy
  have hcoord : ∀ i, (((x i - y i : ℤ) : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := by
    intro i
    have h1 := hx i
    have h2 := hy i
    have h3 := two_mul_cubeHalfSide_le m
    have h4 : |x i - y i| ≤ 2 ^ m := by
      rw [abs_le]; constructor <;> linarith only [h3, h1.1, h1.2, h2.1, h2.2]
    have h5 : |((x i - y i : ℤ) : ℝ)| ≤ (2 : ℝ) ^ m := by
      rw [← Int.cast_abs]; exact_mod_cast h4
    have h6 := neg_abs_le ((x i - y i : ℤ) : ℝ)
    have h7 := le_abs_self ((x i - y i : ℤ) : ℝ)
    exact sq_le_sq' (by linarith only [h5, h6]) (by linarith only [h5, h7])
  have hsq : Multiscale.siteDist ν x y ^ 2 ≤ (Real.sqrt ν * 2 ^ m) ^ 2 := by
    rw [Multiscale.siteDist_eq_norm, Infra.Lattice.norm_sq_latticeCast_sub, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg ν)]
    calc _ ≤ ∑ _i : Fin ν, ((2 : ℝ) ^ m) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := by simp
  exact (sq_le_sq₀ (Multiscale.siteDist_nonneg ν x y) (by positivity)).mp hsq

private theorem finDiam_le {ν : ℕ} {S : Finset (Site ν)} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x ∈ S, ∀ y ∈ S, Multiscale.siteDist ν x y ≤ B) : finDiam S ≤ B := by
  unfold finDiam
  have : ((S ×ˢ S).sup fun p => Real.toNNReal (Multiscale.siteDist ν p.1 p.2) : NNReal) ≤
      B.toNNReal := by
    refine Finset.sup_le fun p hp => ?_
    rw [Finset.mem_product] at hp
    exact Real.toNNReal_le_toNNReal (h _ hp.1 _ hp.2)
  have h' := NNReal.coe_le_coe.mpr this
  rwa [Real.coe_toNNReal _ hB] at h'

private theorem exists_dyCube_of_diam_le {ν : ℕ} {S : Finset (Site ν)} {B : ℝ} {n : ℕ}
    (hB : 0 ≤ B) (h : ∀ x ∈ S, ∀ y ∈ S, Multiscale.siteDist ν x y ≤ B) (hn : 2 * B ≤ 2 ^ n) :
    ∃ c, S ⊆ dyCube n c :=
  exists_subset_dyCube S (by linarith only [hn, finDiam_le hB h])

private theorem center_mem_dyCube {ν : ℕ} (n : ℕ) (k : Site ν) :
    (fun i => cubeSpacing n * k i) ∈ dyCube n k := by
  rw [mem_dyCube]
  intro i
  have := cubeHalfSide_nonneg n
  constructor <;> linarith only [this]

private theorem exists_pts_of_cubeDist_lt {ν : ℕ} {n : ℕ} {k k' : Site ν} {r : ℝ}
    (h : cubeDist n k k' < r) :
    ∃ p ∈ dyCube n k, ∃ q ∈ dyCube n k', Multiscale.siteDist ν p q < r := by
  by_contra hcon
  push Not at hcon
  unfold cubeDist at h
  have hne : (dyCube n k ×ˢ dyCube n k').Nonempty :=
    ⟨(_, _), Finset.mem_product.mpr ⟨center_mem_dyCube n k, center_mem_dyCube n k'⟩⟩
  have hle : ENNReal.ofReal r ≤ (dyCube n k ×ˢ dyCube n k').inf fun p =>
      ENNReal.ofReal (Multiscale.siteDist ν p.1 p.2) := by
    refine Finset.le_inf fun p hp => ?_
    rw [Finset.mem_product] at hp
    exact ENNReal.ofReal_le_ofReal (hcon _ hp.1 _ hp.2)
  obtain ⟨p0, hp0⟩ := hne
  have hlt : ((dyCube n k ×ˢ dyCube n k').inf fun p =>
      ENNReal.ofReal (Multiscale.siteDist ν p.1 p.2)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Finset.inf_le hp0)
  have := (ENNReal.ofReal_le_iff_le_toReal hlt).mp hle
  linarith only [h, this]


/-! ### The scale recurrence -/

/--
(Meaningful for `n ≥ C`; for smaller `n` the natural floor returns `0`.)
-/
noncomputable def recScale (ν : ℕ) (α M : ℝ) (n : ℕ) : ℕ :=
  ⌊((n : ℝ) - (1 + Real.logb 2 (3 * M + 4 * Real.sqrt ν))) / α⌋₊

private theorem near_of_rel {ν : ℕ} {m : ℕ} {k k' : Site ν} {r : ℝ} {x z : Site ν}
    (hx : x ∈ dyCube m k) (hz : z ∈ dyCube m k')
    (h : ∃ p ∈ dyCube m k, ∃ q ∈ dyCube m k', Multiscale.siteDist ν p q < r) :
    Multiscale.siteDist ν x z ≤ r + 2 * (Real.sqrt ν * 2 ^ m) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := h
  have h1 := siteDist_le_of_mem_dyCube hx hp
  have h2 := siteDist_le_of_mem_dyCube hq hz
  have h3 := Multiscale.siteDist_triangle ν x z p
  have h4 := Multiscale.siteDist_triangle ν p z q
  have h5 := Multiscale.siteDist_comm ν z p
  have h6 := Multiscale.siteDist_comm ν z q
  have h7 := Multiscale.siteDist_comm ν x p
  have h8 := Multiscale.siteDist_comm ν q z
  linarith only [hpq, h1, h2, h3, h4]


theorem coverNumber_le_recurrence {ν : ℕ} {α M : ℝ} (hα : 1 ≤ α) (hM : 0 < M) {n : ℕ}
    (hn : 1 + Real.logb 2 (3 * M + 4 * Real.sqrt ν) ≤ n) (D : Finset (Site ν)) :
    (coverNumber n D : ℝ) ≤
      (1 / 2) * coverNumber (recScale ν α M n) D + isolatedCount α M (recScale ν α M n) D := by
  classical
  set m := recScale ν α M n with hmdef
  set T : ℝ := 3 * M + 4 * Real.sqrt ν with hT
  have hsq0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  have hTpos : 0 < T := by rw [hT]; positivity
  have hα0 : 0 < α := by linarith only [hα]
  have hm : α * m ≤ n - (1 + Real.logb 2 T) := by
    have h0 : 0 ≤ ((n : ℝ) - (1 + Real.logb 2 T)) / α := div_nonneg (by linarith only [hn]) hα0.le
    have := Nat.floor_le h0
    rw [le_div_iff₀ hα0] at this
    rw [hmdef, recScale]
    linarith only [this]
  set A : ℝ := (2 : ℝ) ^ (α * (m : ℝ)) with hA
  have hApos : 0 < A := by positivity
  have h2n : 2 * (T * A) ≤ (2 : ℝ) ^ n := by
    have h1 : (2 : ℝ) ^ (1 + Real.logb 2 T + α * m) ≤ (2 : ℝ) ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hm])
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_logb (by norm_num) (by norm_num) hTpos, Real.rpow_natCast] at h1
    linarith only [h1]
  have h2m : (2 : ℝ) ^ m ≤ A := by
    have : (2 : ℝ) ^ (m : ℝ) ≤ (2 : ℝ) ^ (α * m) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith only [hα, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    rwa [Real.rpow_natCast] at this
  set K := minCover m D with hK
  set r : ℝ := M * A with hr
  have hrpos : 0 < r := by positivity
  set s : ℝ := Real.sqrt ν * 2 ^ m with hs
  have hs0 : 0 ≤ s := by positivity
  have hsA : s ≤ Real.sqrt ν * A := mul_le_mul_of_nonneg_left h2m hsq0
  have h3rs : 3 * r + 4 * s ≤ T * A := by
    have : 4 * s ≤ 4 * (Real.sqrt ν * A) := by linarith only [hsA]
    rw [hr, hT]; nlinarith only [this]
  have hsB : s ≤ T * A := by
    have : Real.sqrt ν * A ≤ T * A := by
      apply mul_le_mul_of_nonneg_right _ hApos.le
      rw [hT]; linarith only [hM, hTpos]
    linarith only [h3rs, this]
  have hBnn : 0 ≤ T * A := by positivity
  let Rm : Site ν → Site ν → Prop := fun k k' =>
    ∃ p ∈ dyCube m k, ∃ q ∈ dyCube m k', Multiscale.siteDist ν p q < r
  obtain ⟨P, hPK, hPcard, hPcov⟩ := exists_matching K Rm
  set I := K.filter (fun k => ∀ k' ∈ K, k' ≠ k → M * 2 ^ (α * (m : ℝ)) ≤ cubeDist m k k') with hI
  have hIcard : I.card = isolatedCount α M m D := by
    unfold isolatedCount; rfl
  let S : Site ν × Site ν → Finset (Site ν) := fun p =>
    (K.filter fun k => k = p.1 ∨ k = p.2 ∨ Rm k p.1 ∨ Rm k p.2).biUnion (dyCube m)
  have hPdiam : ∀ p ∈ P, ∃ c, S p ⊆ dyCube n c := by
    intro p hp
    obtain ⟨hp1, hp2, hR⟩ := hPK p hp
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := hR
    have hnear : ∀ x ∈ S p, Multiscale.siteDist ν x pa ≤ r + 2 * s ∨
        Multiscale.siteDist ν x pb ≤ r + 2 * s := by
      intro x hx
      obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
      rw [Finset.mem_filter] at hk
      rcases hk.2 with h | h | h | h
      · left; subst h
        have := siteDist_le_of_mem_dyCube hxk hpa; linarith only [hrpos, hs0, this]
      · right; subst h
        have := siteDist_le_of_mem_dyCube hxk hpb; linarith only [hrpos, hs0, this]
      · left; exact near_of_rel hxk hpa h
      · right; exact near_of_rel hxk hpb h
    refine exists_dyCube_of_diam_le hBnn ?_ h2n
    intro x hx y hy
    have hxy := Multiscale.siteDist_triangle ν x y pa
    have hxy' := Multiscale.siteDist_triangle ν x y pb
    have c1 := Multiscale.siteDist_comm ν y pa
    have c2 := Multiscale.siteDist_comm ν y pb
    have c3 := Multiscale.siteDist_triangle ν x pb pa
    have c4 := Multiscale.siteDist_triangle ν x pa pb
    have c5 := Multiscale.siteDist_comm ν pb pa
    have c6 := Multiscale.siteDist_triangle ν pa y pb
    have c7 := Multiscale.siteDist_triangle ν pb y pa
    have c8 := Multiscale.siteDist_comm ν pa y
    rcases hnear x hx with hx1 | hx1 <;> rcases hnear y hy with hy1 | hy1 <;>
      linarith only [h3rs, hab, hxy, c5, c6, c7, c8, hx1, hy1, hxy', c2, c3]
  have hIdiam : ∀ k ∈ I, ∃ c, dyCube m k ⊆ dyCube n c := by
    intro k _
    exact exists_dyCube_of_diam_le hBnn (fun x hx y hy => (siteDist_le_of_mem_dyCube hx hy).trans
      hsB) h2n
  choose! cP hcP using hPdiam
  choose! cI hcI using hIdiam
  have hcover : IsCubeCover n D (P.image cP ∪ I.image cI) := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := minCover_isCubeCover m D x hx
    by_cases hiso : k ∈ I
    · exact ⟨cI k, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hiso), hcI k hiso hxk⟩
    · have hk' : ¬ ∀ k' ∈ K, k' ≠ k → M * 2 ^ (α * (m : ℝ)) ≤ cubeDist m k k' := by
        intro h; exact hiso (Finset.mem_filter.mpr ⟨hk, h⟩)
      push Not at hk'
      obtain ⟨k', hk'K, hne, hlt⟩ := hk'
      have hRk : Rm k k' := exists_pts_of_cubeDist_lt hlt
      obtain ⟨p, hp, hpk⟩ := hPcov k hk ⟨k', hk'K, hne, hRk⟩
      refine ⟨cP p, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp), hcP p hp ?_⟩
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hpk⟩, hxk⟩
  have h1 := coverNumber_le hcover
  have h2 : (P.image cP ∪ I.image cI).card ≤ P.card + I.card :=
    (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
  have h3 : 2 * P.card ≤ coverNumber m D := by rw [← card_minCover]; exact hPcard
  rw [← hIcard]
  have : (coverNumber n D : ℝ) ≤ P.card + I.card := by exact_mod_cast h1.trans h2
  have h3' : (2 : ℝ) * P.card ≤ coverNumber m D := by exact_mod_cast h3
  linarith only [this, h3']

/-! ### Iterating the recurrence -/

/-- The `j`-th level set: points of `[ns, ∞)` all of whose first `j` iterates stay `≥ ns`
and whose `j`-th iterate is `m`. -/
private def Lev (g : ℕ → ℕ) (ns j m : ℕ) : Set ℕ :=
  {n | (∀ i < j, ns ≤ g^[i] n) ∧ g^[j] n = m}

private theorem mem_Lev_succ {g : ℕ → ℕ} {ns j m n : ℕ} :
    n ∈ Lev g ns (j + 1) m ↔ ns ≤ n ∧ g n ∈ Lev g ns j m := by
  simp only [Lev, Set.mem_ofPred_eq, Function.iterate_succ_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0 (Nat.succ_pos _), fun i hi => h1 (i + 1) (by omega), h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i hi => ?_, h3⟩
    rcases i with _ | i
    · exact h1
    · rw [Function.iterate_succ_apply]; exact h2 i (by omega)

private theorem iterate_le_self {g : ℕ → ℕ} (hgle : ∀ n, g n ≤ n) (j n : ℕ) : g^[j] n ≤ n := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply']; exact (hgle _).trans ih

private theorem iterate_add_le {g : ℕ → ℕ} {ns : ℕ} (hgdec : ∀ n, ns ≤ n → g n < n) (j n : ℕ)
    (h : ∀ i < j, ns ≤ g^[i] n) : g^[j] n + j ≤ n := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ih fun i hi => h i (by omega)
    have h2 := hgdec _ (h j (by omega))
    rw [Function.iterate_succ_apply']
    omega

private theorem unroll {g : ℕ → ℕ} {ns : ℕ} {v w : ℕ → ℝ}
    (hrec : ∀ n, ns ≤ n → v n ≤ 1 / 2 * v (g n) + w (g n)) (j n : ℕ)
    (h : ∀ i < j, ns ≤ g^[i] n) :
    v n ≤ (1 / 2) ^ j * v (g^[j] n) + ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i * w (g^[i + 1] n) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ih fun i hi => h i (by omega)
    have h2 := hrec _ (h j (by omega))
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    have h3 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
    have := mul_le_mul_of_nonneg_left h2 h3
    rw [pow_succ]
    nlinarith only [h1, this]

private theorem exists_stop {g : ℕ → ℕ} {ns : ℕ} (hgdec : ∀ n, ns ≤ n → g n < n) (n : ℕ) :
    ∃ q, g^[q] n < ns := by
  by_contra hcon
  push Not at hcon
  have := iterate_add_le hgdec (n + 1) n fun i _ => hcon i
  omega

/-- Pointwise unrolled bound: for `ns ≤ n ≤ N`, `v n` is bounded by the level-wise sum. -/
private theorem pointwise_bound {g : ℕ → ℕ} {ns : ℕ} {v w : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n) (hw : ∀ n, 0 ≤ w n) (hv0 : ∀ n, v n ≤ v 0)
    (hgdec : ∀ n, ns ≤ n → g n < n) (hg1 : ∀ n, ns ≤ n → 1 ≤ g n)
    (hrec : ∀ n, ns ≤ n → v n ≤ 1 / 2 * v (g n) + w (g n)) {n N : ℕ} (hn : ns ≤ n) (hnN : n ≤ N) :
    v n ≤ ∑ i ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ i *
      (if ∀ i' < i + 1, ns ≤ g^[i'] n then
        ((if 1 ≤ g^[i + 1] n then w (g^[i + 1] n) else 0) +
          1 / 2 * (if g^[i + 1] n < ns then v 0 else 0)) else 0) := by
  classical
  have hex := exists_stop hgdec n
  set q := Nat.find hex with hq
  have hqspec : g^[q] n < ns := Nat.find_spec hex
  have hqmin : ∀ i < q, ns ≤ g^[i] n := fun i hi => not_lt.mp (Nat.find_min hex hi)
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0] at hqspec; simp at hqspec; omega
  clear_value q
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
  have hqle : q' + 1 ≤ N + 1 := by
    by_contra hcon
    have := iterate_add_le hgdec (n + 1) n fun i hi => hqmin i (by omega)
    omega
  have hU := unroll hrec (q' + 1) n hqmin
  have hU2 : v n ≤ (1 / 2) ^ (q' + 1) * v 0 +
      ∑ i ∈ Finset.range (q' + 1), (1 / 2 : ℝ) ^ i * w (g^[i + 1] n) := by
    have := mul_le_mul_of_nonneg_left (hv0 (g^[q' + 1] n))
      (by positivity : (0 : ℝ) ≤ (1 / 2) ^ (q' + 1))
    linarith only [hU, this]
  refine hU2.trans ?_
  have hterm : ∀ i, 0 ≤ (1 / 2 : ℝ) ^ i *
      (if ∀ i' < i + 1, ns ≤ g^[i'] n then
        ((if 1 ≤ g^[i + 1] n then w (g^[i + 1] n) else 0) +
          1 / 2 * (if g^[i + 1] n < ns then v 0 else 0)) else 0) := by
    intro i
    have := hv 0
    have := hw (g^[i + 1] n)
    split_ifs <;> positivity
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr hqle) fun i _ _ => hterm i)
  have hcongr : ∀ i ∈ Finset.range (q' + 1), (1 / 2 : ℝ) ^ i *
      (if ∀ i' < i + 1, ns ≤ g^[i'] n then
        ((if 1 ≤ g^[i + 1] n then w (g^[i + 1] n) else 0) +
          1 / 2 * (if g^[i + 1] n < ns then v 0 else 0)) else 0) =
      (1 / 2 : ℝ) ^ i * w (g^[i + 1] n) +
        (1 / 2) ^ i * (1 / 2 * (if g^[i + 1] n < ns then v 0 else 0)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ∀ i' < i + 1, ns ≤ g^[i'] n := fun i' hi' => hqmin i' (by omega)
    have h2 : 1 ≤ g^[i + 1] n := by
      rw [Function.iterate_succ_apply']; exact hg1 _ (hqmin i (by omega))
    simp only [eq_true h1, eq_true h2, ↓reduceIte]; ring
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib]
  have hsingle : (1 / 2 : ℝ) ^ (q' + 1) * v 0 ≤
      ∑ i ∈ Finset.range (q' + 1), (1 / 2 : ℝ) ^ i *
        (1 / 2 * (if g^[i + 1] n < ns then v 0 else 0)) := by
    have h := Finset.single_le_sum (f := fun i => (1 / 2 : ℝ) ^ i *
        (1 / 2 * (if g^[i + 1] n < ns then v 0 else 0)))
      (fun i _ => by have := hv 0; split_ifs <;> positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_self q'))
    simp only [hqspec, ↓reduceIte] at h
    rw [pow_succ]
    linarith only [h]
  linarith only [hsingle]

/-- Fibre counting: the level-`i + 1` contribution of a nonnegative function. -/
private theorem level_sum_le {g : ℕ → ℕ} {ns : ℕ} {L : ℕ → ℝ} {f : ℕ → ℝ}
    (hf : ∀ m, 0 ≤ f m) (hgle : ∀ n, g n ≤ n)
    (hfib : ∀ j m, ∃ a len : ℕ, Lev g ns (j + 1) m ⊆ Set.Ico a (a + len) ∧ (len : ℝ) ≤ L j)
    (i N : ℕ) :
    ∑ n ∈ Finset.Icc ns N, (if ∀ i' < i + 1, ns ≤ g^[i'] n then f (g^[i + 1] n) else 0) ≤
      L i * ∑ m ∈ Finset.range (N + 1), f m := by
  classical
  have hL : 0 ≤ L i := by
    obtain ⟨a, len, -, h⟩ := hfib i 0
    exact (Nat.cast_nonneg len).trans h
  rw [← Finset.sum_filter]
  rw [Finset.sum_comp (fun b => f b) (g^[i + 1])]
  rw [Finset.mul_sum]
  have hsub : ((Finset.Icc ns N).filter fun n => ∀ i' < i + 1, ns ≤ g^[i'] n).image
      (g^[i + 1]) ⊆ Finset.range (N + 1) := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    have := iterate_le_self hgle (i + 1) n
    omega
  refine (Finset.sum_le_sum fun b _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    fun b _ _ => mul_nonneg hL (hf b))
  obtain ⟨a, len, hsubset, hlen⟩ := hfib i b
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hf b)
  have hc : (((Finset.Icc ns N).filter fun n => ∀ i' < i + 1, ns ≤ g^[i'] n).filter
      (fun n => g^[i + 1] n = b)).card ≤ len := by
    have : ((Finset.Icc ns N).filter fun n => ∀ i' < i + 1, ns ≤ g^[i'] n).filter
        (fun n => g^[i + 1] n = b) ⊆ Finset.Ico a (a + len) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_filter] at hn
      have : n ∈ Lev g ns (i + 1) b := ⟨hn.1.2, hn.2⟩
      simpa using hsubset this
    simpa using Finset.card_le_card this
  exact (Nat.cast_le.mpr hc).trans hlen

private theorem sum_le_of_recurrence (g : ℕ → ℕ) (ns : ℕ) (v w : ℕ → ℝ) (L : ℕ → ℝ) (Λ : ℝ)
    (hv : ∀ n, 0 ≤ v n) (hw : ∀ n, 0 ≤ w n) (hv0 : ∀ n, v n ≤ v 0)
    (hgle : ∀ n, g n ≤ n) (hgdec : ∀ n, ns ≤ n → g n < n) (hg1 : ∀ n, ns ≤ n → 1 ≤ g n)
    (hrec : ∀ n, ns ≤ n → v n ≤ 1 / 2 * v (g n) + w (g n))
    (hfib : ∀ j m, ∃ a len : ℕ, Lev g ns (j + 1) m ⊆ Set.Ico a (a + len) ∧ (len : ℝ) ≤ L j)
    (hΛ : ∀ J, ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * L j ≤ Λ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), v n ≤
      ns * (1 + Λ / 2) * v 0 + Λ * ∑ m ∈ Finset.Icc 1 N, w m := by
  classical
  have hΛ0 : 0 ≤ Λ := by simpa using hΛ 0
  set f : ℕ → ℝ := fun m => (if 1 ≤ m then w m else 0) + 1 / 2 * (if m < ns then v 0 else 0)
    with hfdef
  have hf : ∀ m, 0 ≤ f m := by
    intro m
    have := hv 0
    have := hw m
    simp only [hfdef]
    split_ifs <;> positivity
  have hF : ∑ m ∈ Finset.range (N + 1), f m ≤
      ∑ m ∈ Finset.Icc 1 N, w m + 1 / 2 * (ns * v 0) := by
    simp only [hfdef]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : ∑ m ∈ Finset.range (N + 1), (if 1 ≤ m then w m else 0) =
        ∑ m ∈ Finset.Icc 1 N, w m := by
      rw [← Finset.sum_filter]
      congr 1
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    have e2 : ∑ m ∈ Finset.range (N + 1), (if m < ns then v 0 else 0) ≤ ns * v 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (hv 0)
      have : ((Finset.range (N + 1)).filter fun m => m < ns).card ≤ (Finset.range ns).card :=
        Finset.card_le_card fun m hm => by
          simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; exact hm.2
      simpa using this
    rw [e1]
    linarith only [e2]
  have hF0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), f m := Finset.sum_nonneg fun m _ => hf m
  have hmid : ∑ n ∈ Finset.Icc ns N, v n ≤ Λ * ∑ m ∈ Finset.range (N + 1), f m := by
    calc ∑ n ∈ Finset.Icc ns N, v n
        ≤ ∑ n ∈ Finset.Icc ns N, ∑ i ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ i *
          (if ∀ i' < i + 1, ns ≤ g^[i'] n then f (g^[i + 1] n) else 0) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_Icc] at hn
          refine (pointwise_bound hv hw hv0 hgdec hg1 hrec hn.1 hn.2).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
      _ = ∑ i ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ i * ∑ n ∈ Finset.Icc ns N,
          (if ∀ i' < i + 1, ns ≤ g^[i'] n then f (g^[i + 1] n) else 0) := by
          rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ i *
          (L i * ∑ m ∈ Finset.range (N + 1), f m) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (level_sum_le hf hgle hfib i N) (by positivity)
      _ = (∑ i ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ i * L i) *
          ∑ m ∈ Finset.range (N + 1), f m := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hΛ _) hF0
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) (fun n => n < ns) v
  have hlow : ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n < ns), v n ≤ ns * v 0 := by
    calc _ ≤ ∑ _n ∈ (Finset.range (N + 1)).filter (fun n => n < ns), v 0 :=
          Finset.sum_le_sum fun n _ => hv0 n
      _ ≤ ns * v 0 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (hv 0)
          have : ((Finset.range (N + 1)).filter fun m => m < ns).card ≤ (Finset.range ns).card :=
            Finset.card_le_card fun m hm => by
              simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; exact hm.2
          simpa using this
  have hhigh : (Finset.range (N + 1)).filter (fun n => ¬ n < ns) = Finset.Icc ns N := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [hhigh] at hsplit
  have h1 := mul_le_mul_of_nonneg_left hF hΛ0
  nlinarith only [hmid, hsplit, hlow, h1]

/-! ### Fibres of the recurrence scale -/

private theorem preimage_step {α C : ℝ} {ns : ℕ} (hα : 1 ≤ α) (hC : 0 < C) (hns : C ≤ ns)
    {a len : ℕ} {S : Set ℕ} (hS : S ⊆ Set.Ico a (a + len)) :
    ∃ a' len' : ℕ, {n : ℕ | ns ≤ n ∧ ⌊((n : ℝ) - C) / α⌋₊ ∈ S} ⊆ Set.Ico a' (a' + len') ∧
      (len' : ℝ) ≤ α * len + 1 ∧ (α = 1 → len' ≤ len) := by
  have hα0 : 0 < α := by linarith only [hα]
  set p := ⌈α * a + C⌉₊ with hp
  set q := ⌈α * ((a : ℝ) + len) + C⌉₊ with hq
  have hpq : p ≤ q := by
    apply Nat.ceil_le_ceil
    have : (0 : ℝ) ≤ len := Nat.cast_nonneg len
    nlinarith only [hα0]
  refine ⟨p, q - p, ?_, ?_, ?_⟩
  · intro n ⟨hn, hmem⟩
    have hnC : C ≤ n := hns.trans (by exact_mod_cast hn)
    have hx : 0 ≤ ((n : ℝ) - C) / α := div_nonneg (by linarith only [hnC]) hα0.le
    have h := hS hmem
    rw [Set.mem_Ico] at h
    have h1 : (a : ℝ) ≤ ((n : ℝ) - C) / α := (Nat.le_floor_iff hx).mp h.1
    have h2 : ((n : ℝ) - C) / α < (a : ℝ) + len := by
      have := (Nat.floor_lt hx).mp (by exact_mod_cast h.2)
      simpa using this
    rw [le_div_iff₀ hα0] at h1
    rw [div_lt_iff₀ hα0] at h2
    rw [Set.mem_Ico]
    refine ⟨Nat.ceil_le.mpr (by linarith only [h1]), ?_⟩
    have : n < q := Nat.lt_ceil.mpr (by linarith only [h2])
    omega
  · have h1 : (q : ℝ) < α * ((a : ℝ) + len) + C + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : α * a + C ≤ p := Nat.le_ceil _
    rw [Nat.cast_sub hpq]
    nlinarith only [h1, h2]
  · intro h1
    subst h1
    have e : (1 : ℝ) * ((a : ℝ) + len) + C = C + ((a + len : ℕ) : ℝ) := by push_cast; ring
    have e' : (1 : ℝ) * (a : ℝ) + C = C + (a : ℕ) := by ring
    rw [hq, hp, e, e', Nat.ceil_add_natCast hC.le, Nat.ceil_add_natCast hC.le]
    omega

private theorem lev_bound {α C : ℝ} {ns : ℕ} (hα : 1 ≤ α) (hC : 0 < C) (hns : C ≤ ns)
    (j m : ℕ) :
    ∃ a len : ℕ, Lev (fun n : ℕ => ⌊((n : ℝ) - C) / α⌋₊) ns j m ⊆ Set.Ico a (a + len) ∧
      (len : ℝ) ≤ (j + 1) * α ^ j ∧ (α = 1 → len ≤ 1) := by
  induction j with
  | zero =>
    refine ⟨m, 1, ?_, by simp, fun _ => le_rfl⟩
    intro n hn
    simp only [Lev, Set.mem_ofPred_eq, Function.iterate_zero, id] at hn
    simp [hn.2]
  | succ j ih =>
    obtain ⟨a, len, hsub, hlen, h1⟩ := ih
    obtain ⟨a', len', hsub', hlen', h1'⟩ := preimage_step hα hC hns hsub
    refine ⟨a', len', ?_, ?_, fun h => (h1' h).trans (h1 h)⟩
    · intro n hn
      rw [mem_Lev_succ] at hn
      exact hsub' hn
    · have hpow : (1 : ℝ) ≤ α ^ (j + 1) := one_le_pow₀ hα
      have : α * len ≤ α * ((j + 1) * α ^ j) :=
        mul_le_mul_of_nonneg_left hlen (by linarith only [hα])
      push_cast
      rw [pow_succ]
      rw [pow_succ] at hpow
      nlinarith only [hlen', hpow, this]

/-- The threshold scale `n*`: beyond it the recurrence applies and `g(n) ≥ 1`. -/
private noncomputable def thr (ν : ℕ) (M : ℝ) : ℕ :=
  ⌈1 + Real.logb 2 (3 * M + 4 * Real.sqrt ν)⌉₊ + 2

private theorem recConst_pos {ν : ℕ} {M : ℝ} (hM : 2 ≤ M) :
    0 < 1 + Real.logb 2 (3 * M + 4 * Real.sqrt ν) := by
  have : 0 < Real.logb 2 (3 * M + 4 * Real.sqrt ν) :=
    Real.logb_pos (by norm_num) (by nlinarith only [hM, Real.sqrt_nonneg (ν : ℝ)])
  linarith only [this]

private theorem fib_general {ν : ℕ} {α M : ℝ} (hα : 1 ≤ α) (hM : 2 ≤ M) (j m : ℕ) :
    ∃ a len : ℕ, Lev (recScale ν α M) (thr ν M) (j + 1) m ⊆ Set.Ico a (a + len) ∧
      (len : ℝ) ≤ (j + 2) * α ^ (j + 1) ∧ (α = 1 → len ≤ 1) := by
  have hC := recConst_pos (ν := ν) hM
  have hns : 1 + Real.logb 2 (3 * M + 4 * Real.sqrt ν) ≤ (thr ν M : ℝ) := by
    unfold thr
    push_cast
    linarith only [Nat.le_ceil (1 + Real.logb 2 (3 * M + 4 * Real.sqrt ν))]
  obtain ⟨a, len, h1, h2, h3⟩ := lev_bound hα hC hns (j + 1) m
  exact ⟨a, len, h1, by push_cast at h2; linarith only [h2], h3⟩

private theorem isolatedCount_mono {ν : ℕ} {α M M' : ℝ} (h : M ≤ M') (n : ℕ)
    (D : Finset (Site ν)) : isolatedCount α M' n D ≤ isolatedCount α M n D := by
  classical
  unfold isolatedCount
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, fun k' hk' hne => ?_⟩
  have h1 := hk.2 k' hk' hne
  have h0 : (0 : ℝ) ≤ 2 ^ (α * n) := by positivity
  nlinarith only [h, h1, h0]

private theorem isolatedVolume_mono {ν : ℕ} {α M M' : ℝ} (h : M ≤ M') (D : Finset (Site ν)) :
    isolatedVolume α M' D ≤ isolatedVolume α M D :=
  Finset.sum_le_sum fun n _ => isolatedCount_mono h n D

private theorem interp_core {ν : ℕ} {α M : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 2) (hM : 2 ≤ M)
    {L : ℕ → ℝ} {Λ : ℝ}
    (hfib : ∀ j m, ∃ a len : ℕ, Lev (recScale ν α M) (thr ν M) (j + 1) m ⊆
      Set.Ico a (a + len) ∧ (len : ℝ) ≤ L j)
    (hΛ : ∀ J, ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * L j ≤ Λ) (D : Finset (Site ν)) :
    (coverVolume D : ℝ) ≤
      thr ν M * (1 + Λ / 2) * coverNumber 0 D + Λ * isolatedVolume α M D := by
  have hC := recConst_pos (ν := ν) hM
  set C := 1 + Real.logb 2 (3 * M + 4 * Real.sqrt ν) with hCdef
  have hα0 : 0 < α := by linarith only [hα1]
  have hnsC : C + 2 ≤ (thr ν M : ℝ) := by
    unfold thr
    push_cast
    linarith only [Nat.le_ceil C]
  have hrecC : ∀ n : ℕ, thr ν M ≤ n → C + 2 ≤ (n : ℝ) :=
    fun n hn => hnsC.trans (by exact_mod_cast hn)
  have key := sum_le_of_recurrence (recScale ν α M) (thr ν M)
    (fun n => (coverNumber n D : ℝ)) (fun n => (isolatedCount α M n D : ℝ)) L Λ
    (fun n => Nat.cast_nonneg _) (fun n => Nat.cast_nonneg _)
    (fun n => by exact_mod_cast (coverNumber_le_card n D).trans (coverNumber_zero D).ge)
    (fun n => by
      unfold recScale
      refine Nat.floor_le_of_le ?_
      rw [div_le_iff₀ hα0]
      nlinarith only [hα1, hC, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (fun n hn => by
      have h2 := hrecC n hn
      unfold recScale
      have hx : 0 ≤ ((n : ℝ) - C) / α := div_nonneg (by linarith only [h2]) hα0.le
      refine (Nat.floor_lt hx).mpr ?_
      rw [div_lt_iff₀ hα0]
      nlinarith only [hα1, hC, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (fun n hn => by
      have h2 := hrecC n hn
      unfold recScale
      refine Nat.le_floor ?_
      rw [Nat.cast_one, le_div_iff₀ hα0]
      linarith only [hα2, h2])
    (fun n hn =>
      coverNumber_le_recurrence hα1 (by linarith only [hM]) (by linarith only [hrecC n hn]) D)
    hfib hΛ (topScale D)
  simpa [coverVolume, isolatedVolume, Nat.cast_sum] using key

private theorem hasSum_bound {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, ((j : ℝ) + 2) * ρ ^ j ≤ ρ / (1 - ρ) ^ 2 + 2 * (1 - ρ)⁻¹ := by
  have hA := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := ρ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have hB := (hasSum_geometric_of_lt_one h0 h1).mul_left 2
  have hS : HasSum (fun j : ℕ => ((j : ℝ) + 2) * ρ ^ j)
      (ρ / (1 - ρ) ^ 2 + 2 * (1 - ρ)⁻¹) := by
    convert hA.add hB using 1
    ext j
    ring
  exact sum_le_hasSum _ (fun j _ => by positivity) hS

/--
Strengthening: `M ≥ 2` is not assumed (reduced to `max M 2` by monotonicity of `V'` in `M`);
the hypothesis `0 < M` is not used.
-/
theorem exists_coverVolume_le (ν : ℕ) {α M : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 2) :
    ∃ K₀ K' : ℝ, ∀ D : Finset (Site ν),
      (coverVolume D : ℝ) ≤ K₀ * coverNumber 0 D + K' * isolatedVolume α M D := by
  set M' := max M 2 with hM'
  have hM2 : 2 ≤ M' := le_max_right _ _
  have hMM : M ≤ M' := le_max_left _ _
  set ρ := α / 2 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith only [hα1]
  have hρ1 : ρ < 1 := by rw [hρ]; linarith only [hα2]
  set Λ : ℝ := α * (ρ / (1 - ρ) ^ 2 + 2 * (1 - ρ)⁻¹) with hΛdef
  have hΛ : ∀ J, ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * (((j : ℝ) + 2) * α ^ (j + 1)) ≤ Λ := by
    intro J
    have h := hasSum_bound hρ0 hρ1 J
    have h2 : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * (((j : ℝ) + 2) * α ^ (j + 1)) =
        α * ∑ j ∈ Finset.range J, ((j : ℝ) + 2) * ρ ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hρ]; ring
    rw [h2, hΛdef]
    exact mul_le_mul_of_nonneg_left h (by linarith only [hρ, hρ0])
  have hΛ0 : 0 ≤ Λ := by simpa using hΛ 0
  refine ⟨thr ν M' * (1 + Λ / 2), Λ, fun D => ?_⟩
  have h1 := interp_core (ν := ν) hα1 hα2 hM2 (L := fun j => ((j : ℝ) + 2) * α ^ (j + 1))
    (Λ := Λ) (fun j m => by
      obtain ⟨a, len, h1, h2, -⟩ := fib_general (ν := ν) hα1 hM2 j m
      exact ⟨a, len, h1, h2⟩) hΛ D
  have h2 : (isolatedVolume α M' D : ℝ) ≤ isolatedVolume α M D := by
    exact_mod_cast isolatedVolume_mono hMM D
  nlinarith only [h1, mul_le_mul_of_nonneg_left h2 hΛ0]

/--
As above `M ≥ 2`
is not assumed and `0 < M` is not used.
-/
theorem exists_coverVolume_le_of_alpha_one (ν : ℕ) (M : ℝ) :
    ∃ K₀ : ℝ, ∀ D : Finset (Site ν),
      (coverVolume D : ℝ) ≤ K₀ * coverNumber 0 D + 2 * isolatedVolume 1 M D := by
  set M' := max M 2 with hM'
  have hM2 : 2 ≤ M' := le_max_right _ _
  have hMM : M ≤ M' := le_max_left _ _
  refine ⟨thr ν M' * (1 + 2 / 2), fun D => ?_⟩
  have h1 := interp_core (ν := ν) (α := 1) le_rfl one_lt_two hM2 (L := fun _ => 1) (Λ := 2)
    (fun j m => by
      obtain ⟨a, len, h1, -, h3⟩ := fib_general (ν := ν) (α := 1) le_rfl hM2 j m
      exact ⟨a, len, h1, by exact_mod_cast h3 rfl⟩)
    (fun J => by simpa using sum_geometric_two_le J) D
  have h2 : (isolatedVolume 1 M' D : ℝ) ≤ isolatedVolume 1 M D := by
    exact_mod_cast isolatedVolume_mono hMM D
  nlinarith only [h1, h2]

end FroehlichSpencer.T12
