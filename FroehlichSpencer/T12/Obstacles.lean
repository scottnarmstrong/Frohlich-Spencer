/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Events

/-!
# Appendix D geometry: obstacles, admissibility, obstacle filling

Pure
geometry over an abstract obstacle family `G`.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


def vertexBoundary {ν : ℕ} (A : Set (Site ν)) : Set (Site ν) :=
  {a | a ∈ A ∧ ∃ b, siteDist ν a b = 1 ∧ b ∉ A}

/-- The nearest-neighbour component of `x` in `U`: chain steps of Euclidean length `< 5/4`, i.e.
nearest-neighbour edges (distinct lattice sites are at distance `1` or `≥ √2 > 5/4`). -/
def nnComponent {ν : ℕ} (U : Set (Site ν)) (x : Site ν) : Set (Site ν) :=
  chainCluster (siteDist ν) U (5 / 4) x

/-- The closed neighbourhood `C^[R] = {x | ∃ c ∈ C, |x − c| ≤ R}` of a set. -/
def nbhd {ν : ℕ} (C : Set (Site ν)) (R : ℝ) : Set (Site ν) := {x | ∃ c ∈ C, siteDist ν x c ≤ R}


structure ObstacleFamily {ν : ℕ} (K₀ : ℝ) (G : ℕ → Set (Set (Site ν))) : Prop where
  nonempty : ∀ j, ∀ C ∈ G j, C.Nonempty
  finite : ∀ j, ∀ C ∈ G j, C.Finite
  diam_le : ∀ j, ∀ C ∈ G j, DiamLE (siteDist ν) C (scaleD K₀ j)
  sep_same : ∀ j, ∀ C ∈ G j, ∀ C' ∈ G j, C ≠ C' → ∀ x ∈ C, ∀ y ∈ C',
    2 * scaleD K₀ (j + 1) ≤ siteDist ν x y
  sep_lower : ∀ i j, i < j → ∀ C ∈ G i, ∀ C' ∈ G j, ∀ x ∈ C, ∀ y ∈ C',
    2 * scaleD K₀ (i + 1) ≤ siteDist ν x y

/--
the deterministic induction’s "`k`-admissible" is `n = k + 1`; "`(k−1)`-admissible" is `n = k`
(vacuous at `k = 0`).
-/
def Admissible {ν : ℕ} (K₀ : ℝ) (G : ℕ → Set (Set (Site ν))) (n : ℕ) (A : Set (Site ν)) : Prop :=
  ∀ j < n, ∀ C ∈ G j, Disjoint (vertexBoundary A) (nbhd C (4 * scaleD K₀ j))


def obstacleUnion {ν : ℕ} (K₀ : ℝ) (G : ℕ → Set (Set (Site ν))) (n : ℕ) : Set (Site ν) :=
  ⋃ j ∈ Finset.range n, ⋃ C ∈ G j, nbhd C (4 * scaleD K₀ j + 2)


def obstacleFill {ν : ℕ} (K₀ : ℝ) (G : ℕ → Set (Set (Site ν))) (n : ℕ) (D₁ : Set (Site ν)) :
    Set (Site ν) :=
  D₁ ∪ ⋃ a ∈ vertexBoundary D₁ ∩ obstacleUnion K₀ G n, nnComponent (obstacleUnion K₀ G n) a


def ScaleConditions (K₀ : ℝ) : Prop :=
  6 < scaleD K₀ 0 ∧ 28 < scaleD K₀ 1 ∧
  1 < 2 * scaleD K₀ 1 - 8 * scaleD K₀ 0 - 4 ∧
  (∀ r, 10 * scaleD K₀ r + 3 < 2 * scaleD K₀ (r + 2) - 8 * scaleD K₀ (r + 1) - 4) ∧
  (∀ r, 30 * scaleD K₀ r + 7 < scaleD K₀ (r + 1)) ∧
  (∀ k, 9 * scaleD K₀ k < scaleD K₀ (k + 1) / 5) ∧
  (∀ k, 10 * scaleD K₀ k + 3 ≤ scaleD K₀ (k + 1) / 4) ∧
  (∀ k, 10 * scaleD K₀ k + 7 < scaleD K₀ (k + 2) / 4) ∧
  (∀ i, 4 * scaleD K₀ i + 3 < 2 * scaleD K₀ (i + 1))

private theorem exp_ten_ge : (1024 : ℝ) ≤ Real.exp 10 := by
  have h : Real.exp 10 = Real.exp 1 ^ 10 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [h]
  calc (1024 : ℝ) = 2 ^ 10 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 10

private theorem scaleD_ratio {K₀ : ℝ} (hK : 40 ≤ K₀) (k : ℕ) :
    1024 * scaleD K₀ k ≤ scaleD K₀ (k + 1) := by
  have hp : (1 : ℝ) ≤ (5 / 4) ^ k := one_le_pow₀ (by norm_num)
  have h40 : 40 ≤ K₀ * (5 / 4) ^ k := by nlinarith
  have hb : (1024 : ℝ) ≤ Real.exp (K₀ * (5 / 4) ^ k / 4) :=
    exp_ten_ge.trans (Real.exp_le_exp.2 (by linarith))
  have e : scaleD K₀ (k + 1) = scaleD K₀ k * Real.exp (K₀ * (5 / 4) ^ k / 4) := by
    unfold scaleD
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e]
  have := scaleD_pos K₀ k
  nlinarith


theorem exists_scaleConditions : ∃ K : ℝ, ∀ K₀, K ≤ K₀ → ScaleConditions K₀ := by
  refine ⟨40, fun K₀ hK => ?_⟩
  have hr := scaleD_ratio hK
  have hge : ∀ k, 1 ≤ scaleD K₀ k := fun k => one_le_scaleD (by linarith) k
  have h0 : 1024 ≤ scaleD K₀ 0 := by
    rw [scaleD_zero]
    exact exp_ten_ge.trans (Real.exp_le_exp.2 (by linarith))
  have h1 := hr 0
  refine ⟨by linarith, by linarith [hge 0], by linarith [hge 0], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    have a := hr r
    have b := hr (r + 1)
    have c : 1024 * scaleD K₀ (r + 1) ≤ scaleD K₀ (r + 2) := b
    linarith [hge r]
  · intro r
    linarith [hr r, hge r]
  · intro k
    linarith [hr k, hge k]
  · intro k
    linarith [hr k, hge k]
  · intro k
    have b := hr (k + 1)
    have c : 1024 * scaleD K₀ (k + 1) ≤ scaleD K₀ (k + 2) := b
    linarith [hr k, hge k]
  · intro i
    linarith [hr i, hge i]


theorem obstacleFamily_gentleClasses {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν))
    (S₀ : Set (Site ν)) (v : Site ν → ℝ) : ObstacleFamily P.K₀ (gentleClasses P blk S₀ v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro j C ⟨⟨x, hx, rfl⟩, -⟩
    exact ⟨x, mem_chainCluster_self hx⟩
  · rintro j C ⟨-, hg⟩
    exact hg.fst
  · rintro j C ⟨-, hg⟩
    exact hg.snd.1
  · rintro j C ⟨hC, -⟩ C' ⟨⟨x₁, hx₁, rfl⟩, -⟩ hne x hx y hy
    have hyS := chainCluster_subset x₁ hy
    have hyC : y ∉ C := by
      intro hyC
      obtain ⟨x₀, -, rfl⟩ := hC
      apply hne
      rw [← chainCluster_eq_of_mem (siteDist_comm ν) hyC,
        chainCluster_eq_of_mem (siteDist_comm ν) hy]
    rw [← scaleR_eq_scaleD_succ]
    exact two_mul_scaleR_le_siteDist P hC hx hyS hyC
  · rintro i j hij C ⟨hC, hg⟩ C' ⟨⟨x₁, hx₁, rfl⟩, -⟩ x hx y hy
    have hyj : y ∈ singularSetsGen P blk S₀ v j := chainCluster_subset x₁ hy
    have hyi1 := singularSetsGen_antitone P blk S₀ v hij hyj
    rw [singularSetsGen_succ] at hyi1
    have hyC : y ∉ C := fun h => hyi1.2 ⟨C, ⟨hC, hg⟩, h⟩
    rw [← scaleR_eq_scaleD_succ]
    exact two_mul_scaleR_le_siteDist P hC hx hyi1.1 hyC

private theorem mem_obstacleUnion_iff {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n : ℕ}
    {x : Site ν} :
    x ∈ obstacleUnion K₀ G n ↔
      ∃ j, j < n ∧ ∃ C ∈ G j, x ∈ nbhd C (4 * scaleD K₀ j + 2) := by
  simp [obstacleUnion]

private theorem mem_obstacleUnion_succ_iff {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {r : ℕ}
    {x : Site ν} :
    x ∈ obstacleUnion K₀ G (r + 1) ↔
      x ∈ obstacleUnion K₀ G r ∨ ∃ C ∈ G r, x ∈ nbhd C (4 * scaleD K₀ r + 2) := by
  rw [mem_obstacleUnion_iff, mem_obstacleUnion_iff]
  constructor
  · rintro ⟨j, hj, C, hC, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · exact Or.inl ⟨j, h, C, hC, hx⟩
    · exact Or.inr ⟨C, hC, hx⟩
  · rintro (⟨j, hj, C, hC, hx⟩ | ⟨C, hC, hx⟩)
    · exact ⟨j, Nat.lt_succ_of_lt hj, C, hC, hx⟩
    · exact ⟨r, Nat.lt_succ_self r, C, hC, hx⟩

private theorem not_mem_obstacleUnion_zero {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))}
    {x : Site ν} : x ∉ obstacleUnion K₀ G 0 := by
  simp [obstacleUnion]

private theorem siteDist_le_three {ν : ℕ} (a b c d : Site ν) :
    siteDist ν a d ≤ siteDist ν a b + siteDist ν b c + siteDist ν c d := by
  have h1 := siteDist_triangle ν a d b
  have h2 := siteDist_triangle ν b d c
  linarith

private theorem sep_nbhd {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))}
    (hG : ObstacleFamily K₀ G) {r : ℕ} {C C' : Set (Site ν)} (hC : C ∈ G r) (hC' : C' ∈ G r)
    (hne : C ≠ C') {x y : Site ν} (hx : x ∈ nbhd C (4 * scaleD K₀ r + 2))
    (hy : y ∈ nbhd C' (4 * scaleD K₀ r + 2)) :
    2 * scaleD K₀ (r + 1) - 8 * scaleD K₀ r - 4 ≤ siteDist ν x y := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨c', hc', hyc⟩ := hy
  have h := hG.sep_same r C hC C' hC' hne c hc c' hc'
  have h1 := siteDist_le_three c x y c'
  have h2 := siteDist_comm ν c x
  linarith

private theorem diam_nbhd {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))}
    (hG : ObstacleFamily K₀ G) {r : ℕ} {C : Set (Site ν)} (hC : C ∈ G r) {x y : Site ν}
    (hx : x ∈ nbhd C (4 * scaleD K₀ r + 2)) (hy : y ∈ nbhd C (4 * scaleD K₀ r + 2)) :
    siteDist ν x y ≤ 9 * scaleD K₀ r + 4 := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨c', hc', hyc⟩ := hy
  have h := hG.diam_le r C hC c hc c' hc'
  have h1 := siteDist_le_three x c c' y
  have h2 := siteDist_comm ν c' y
  linarith


private theorem chain_core {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))}
    (hG : ObstacleFamily K₀ G) (r : ℕ) (e : ℝ) (he : 0 ≤ e)
    (IH : ∀ x y z, y ∈ nnComponent (obstacleUnion K₀ G r) x →
      z ∈ nnComponent (obstacleUnion K₀ G r) x → siteDist ν y z < e)
    (hsep : e + 3 ≤ 2 * scaleD K₀ (r + 1) - 8 * scaleD K₀ r - 4)
    {C₀ : Set (Site ν)} (hC₀ : C₀ ∈ G r) {p y : Site ν}
    (hp : p ∈ nbhd C₀ (4 * scaleD K₀ r + 2))
    (hy : y ∈ nnComponent (obstacleUnion K₀ G (r + 1)) p) :
    y ∈ nbhd C₀ (4 * scaleD K₀ r + 2) ∨
      (y ∈ obstacleUnion K₀ G r ∧
        ∃ w ∈ nnComponent (obstacleUnion K₀ G r) y, ∃ t ∈ nbhd C₀ (4 * scaleD K₀ r + 2),
          siteDist ν w t < 5 / 4) := by
  obtain ⟨hpU, hch⟩ := hy
  induction hch with
  | refl => exact Or.inl hp
  | tail hab hbc ih =>
    rename_i b c
    obtain ⟨hbU, hcU, hbc⟩ := hbc
    by_cases hcT : c ∈ nbhd C₀ (4 * scaleD K₀ r + 2)
    · exact Or.inl hcT
    right
    have hcd : siteDist ν c b < 5 / 4 := by rw [siteDist_comm]; exact hbc
    rcases mem_obstacleUnion_succ_iff.1 hcU with hcr | ⟨C', hC', hcC'⟩
    · rcases ih with hb | ⟨hbr, w, hw, t, ht, hwt⟩
      · exact ⟨hcr, c, mem_chainCluster_self hcr, b, hb, hcd⟩
      · have hcb : c ∈ nnComponent (obstacleUnion K₀ G r) b :=
          mem_chainCluster_of_lt (mem_chainCluster_self hbr) hcr hbc
        have heq : nnComponent (obstacleUnion K₀ G r) c = nnComponent (obstacleUnion K₀ G r) b :=
          chainCluster_eq_of_mem (siteDist_comm ν) hcb
        exact ⟨hcr, w, by rw [heq]; exact hw, t, ht, hwt⟩
    · exfalso
      have hne : C₀ ≠ C' := by
        rintro rfl
        exact hcT hcC'
      rcases ih with hb | ⟨hbr, w, hw, t, ht, hwt⟩
      · have := sep_nbhd hG hC₀ hC' hne hb hcC'
        linarith
      · have h1 := sep_nbhd hG hC₀ hC' hne ht hcC'
        have h2 := siteDist_le_three t w b c
        have h3 := IH b b w (mem_chainCluster_self hbr) hw
        have h4 := siteDist_comm ν t w
        have h5 := siteDist_comm ν w b
        linarith


private theorem diam_step {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))}
    (hG : ObstacleFamily K₀ G) (r : ℕ) (e : ℝ) (he : 0 ≤ e)
    (IH : ∀ x y z, y ∈ nnComponent (obstacleUnion K₀ G r) x →
      z ∈ nnComponent (obstacleUnion K₀ G r) x → siteDist ν y z < e)
    (hsep : e + 3 ≤ 2 * scaleD K₀ (r + 1) - 8 * scaleD K₀ r - 4)
    (he10 : e ≤ 10 * scaleD K₀ r) (hd4 : 4 < scaleD K₀ r)
    (hd : (∃ u, u ∈ obstacleUnion K₀ G r) → 2 * e + 7 < scaleD K₀ r)
    {x y z : Site ν} (hy : y ∈ nnComponent (obstacleUnion K₀ G (r + 1)) x)
    (hz : z ∈ nnComponent (obstacleUnion K₀ G (r + 1)) x) :
    siteDist ν y z < 10 * scaleD K₀ r := by
  have hxU : x ∈ obstacleUnion K₀ G (r + 1) := hy.1
  by_cases hex : ∃ q ∈ nnComponent (obstacleUnion K₀ G (r + 1)) x, ∃ C₀ ∈ G r,
      q ∈ nbhd C₀ (4 * scaleD K₀ r + 2)
  · obtain ⟨q, hq, C₀, hC₀, hqT⟩ := hex
    have hcq : nnComponent (obstacleUnion K₀ G (r + 1)) q =
        nnComponent (obstacleUnion K₀ G (r + 1)) x :=
      chainCluster_eq_of_mem (siteDist_comm ν) hq
    have key : ∀ w ∈ nnComponent (obstacleUnion K₀ G (r + 1)) x,
        ∃ t ∈ nbhd C₀ (4 * scaleD K₀ r + 2), siteDist ν w t ≤ e + 5 / 4 ∧
          (w ∉ nbhd C₀ (4 * scaleD K₀ r + 2) → ∃ u, u ∈ obstacleUnion K₀ G r) := by
      intro w hw
      rw [← hcq] at hw
      rcases chain_core hG r e he IH hsep hC₀ hqT hw with hT | ⟨hwr, w', hw', t, ht, hwt⟩
      · exact ⟨w, hT, by rw [siteDist_self]; linarith, fun h => absurd hT h⟩
      · refine ⟨t, ht, ?_, fun _ => ⟨w, hwr⟩⟩
        have h1 := IH w w w' (mem_chainCluster_self hwr) hw'
        have h2 := siteDist_triangle ν w t w'
        have h3 := siteDist_comm ν w w'
        linarith
    obtain ⟨ty, hty, hyd, hy2⟩ := key y hy
    obtain ⟨tz, htz, hzd, hz2⟩ := key z hz
    by_cases hyT : y ∈ nbhd C₀ (4 * scaleD K₀ r + 2)
    · by_cases hzT : z ∈ nbhd C₀ (4 * scaleD K₀ r + 2)
      · have := diam_nbhd hG hC₀ hyT hzT
        linarith
      · have hd' := hd (hz2 hzT)
        have h1 := diam_nbhd hG hC₀ hty htz
        have h2 := siteDist_le_three y ty tz z
        have h3 := siteDist_comm ν tz z
        linarith
    · have hd' := hd (hy2 hyT)
      have h1 := diam_nbhd hG hC₀ hty htz
      have h2 := siteDist_le_three y ty tz z
      have h3 := siteDist_comm ν tz z
      linarith
  · have hsub : nnComponent (obstacleUnion K₀ G (r + 1)) x ⊆
        nnComponent (obstacleUnion K₀ G r) x := by
      have hin : ∀ w ∈ nnComponent (obstacleUnion K₀ G (r + 1)) x,
          w ∈ obstacleUnion K₀ G r := by
        intro w hw
        rcases mem_obstacleUnion_succ_iff.1 (chainCluster_subset x hw) with h | ⟨C₀, hC₀, h⟩
        · exact h
        · exact absurd ⟨w, hw, C₀, hC₀, h⟩ hex
      rintro w ⟨hx, hw⟩
      have hxr := hin x (mem_chainCluster_self hxU)
      induction hw with
      | refl => exact mem_chainCluster_self hxr
      | tail hab hbc ih =>
        rename_i b c
        exact mem_chainCluster_of_lt ih (hin c ⟨hx, hab.tail hbc⟩) hbc.2.2
    have := IH x y z (hsub hy) (hsub hz)
    linarith

private theorem diam_aux {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) :
    ∀ x y z : Site ν, y ∈ nnComponent (obstacleUnion K₀ G (k + 1)) x →
      z ∈ nnComponent (obstacleUnion K₀ G (k + 1)) x → siteDist ν y z < 10 * scaleD K₀ k := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hK
  induction k with
  | zero =>
    intro x y z hy hz
    have hd0 := scaleD_pos K₀ 0
    refine diam_step hG 0 0 le_rfl (fun x y z hy _ => absurd hy.1 not_mem_obstacleUnion_zero)
      ?_ (by linarith) (by linarith) (fun ⟨u, hu⟩ => absurd hu not_mem_obstacleUnion_zero) hy hz
    have := h5 0
    linarith
  | succ k ih =>
    intro x y z hy hz
    have hd0 := scaleD_pos K₀ k
    have a3 : 10 * scaleD K₀ k + 3 <
        2 * scaleD K₀ (k + 1 + 1) - 8 * scaleD K₀ (k + 1) - 4 := h3 k
    have a4 := h4 k
    exact diam_step hG (k + 1) (10 * scaleD K₀ k) (by linarith) ih (by linarith) (by linarith)
      (by linarith) (fun _ => by linarith) hy hz


theorem diam_nnComponent_obstacleUnion_lt {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {x y z : Site ν}
    (hy : y ∈ nnComponent (obstacleUnion K₀ G (k + 1)) x)
    (hz : z ∈ nnComponent (obstacleUnion K₀ G (k + 1)) x) :
    siteDist ν y z < 10 * scaleD K₀ k :=
  diam_aux hK hG k x y z hy hz


theorem obstacleFill_spec {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {D₁ D₂ : Set (Site ν)}
    (hD₁ : D₁.Finite) (h12 : D₁ ⊆ D₂)
    (hsep : ∀ x ∈ D₁, ∀ y, y ∉ D₂ → 10 * scaleD K₀ k ≤ siteDist ν x y) :
    (obstacleFill K₀ G (k + 1) D₁).Finite ∧ D₁ ⊆ obstacleFill K₀ G (k + 1) D₁ ∧
      obstacleFill K₀ G (k + 1) D₁ ⊆ D₂ ∧
      Admissible K₀ G (k + 1) (obstacleFill K₀ G (k + 1) D₁) := by
  have hball : ∀ a ∈ obstacleUnion K₀ G (k + 1),
      ∀ y ∈ nnComponent (obstacleUnion K₀ G (k + 1)) a, siteDist ν a y < 10 * scaleD K₀ k :=
    fun a ha y hy =>
      diam_nnComponent_obstacleUnion_lt hK hG k (mem_chainCluster_self ha) hy
  refine ⟨?_, Set.subset_union_left, ?_, ?_⟩
  · refine hD₁.union (Set.Finite.biUnion (hD₁.subset fun a ha => ha.1.1) fun a ha => ?_)
    exact (finite_setOf_siteDist_le ν a (10 * scaleD K₀ k)).subset
      fun y hy => (hball a ha.2 y hy).le
  · intro y hy
    rcases hy with hy | hy
    · exact h12 hy
    · obtain ⟨a, ha, hy⟩ := Set.mem_iUnion₂.1 hy
      by_contra hyD
      have := hsep a ha.1.1 y hyD
      linarith [hball a ha.2 y hy]
  · intro j hj C hC
    rw [Set.disjoint_left]
    rintro a ⟨haA, b, hab, hbA⟩ ⟨c, hc, hac⟩
    have haU : a ∈ obstacleUnion K₀ G (k + 1) :=
      mem_obstacleUnion_iff.2 ⟨j, hj, C, hC, c, hc, by linarith⟩
    have hbc := siteDist_triangle ν b c a
    have hba := siteDist_comm ν a b
    have hbU : b ∈ obstacleUnion K₀ G (k + 1) :=
      mem_obstacleUnion_iff.2 ⟨j, hj, C, hC, c, hc, by linarith⟩
    obtain ⟨a', ha', haa'⟩ : ∃ a' ∈ vertexBoundary D₁ ∩ obstacleUnion K₀ G (k + 1),
        a ∈ nnComponent (obstacleUnion K₀ G (k + 1)) a' := by
      rcases haA with haD | haB
      · exact ⟨a, ⟨⟨haD, b, hab, fun h => hbA (Or.inl h)⟩, haU⟩, mem_chainCluster_self haU⟩
      · obtain ⟨a', ha', haa'⟩ := Set.mem_iUnion₂.1 haB
        exact ⟨a', ha', haa'⟩
    refine hbA (Or.inr (Set.mem_iUnion₂.2 ⟨a', ha', ?_⟩))
    exact mem_chainCluster_of_lt haa' hbU (by rw [hab]; norm_num)

end FroehlichSpencer.T12

end
