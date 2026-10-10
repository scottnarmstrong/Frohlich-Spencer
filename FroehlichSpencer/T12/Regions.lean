/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Obstacles

/-!
# Appendix D geometry: regions around a gentle component and radial cuts
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

/-! ### Lattice arithmetic -/

private theorem siteDist_eq_sqrt {ν : ℕ} (x y : Site ν) :
    siteDist ν x y = Real.sqrt (∑ i, ((x i : ℝ) - (y i : ℝ)) ^ 2) := by
  unfold siteDist latticeLength
  simp [Pi.sub_apply]

private theorem coord_le_siteDist {ν : ℕ} (x y : Site ν) (i : Fin ν) :
    |(x i : ℝ) - (y i : ℝ)| ≤ siteDist ν x y := by
  rw [siteDist_eq_sqrt]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => ((x j : ℝ) - (y j : ℝ)) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private theorem siteDist_le_sqrt_mul {ν : ℕ} (x y : Site ν) {h : ℝ} (h0 : 0 ≤ h)
    (hxy : ∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ h) :
    siteDist ν x y ≤ Real.sqrt ν * h := by
  rw [siteDist_eq_sqrt]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  calc ∑ i, ((x i : ℝ) - (y i : ℝ)) ^ 2 ≤ ∑ _i : Fin ν, h ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          have := abs_le.1 (hxy i)
          nlinarith only [this.1, this.2]
    _ = (Real.sqrt ν * h) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg ν)]
        simp

private theorem siteDist_three {ν : ℕ} (a b c d : Site ν) :
    siteDist ν a d ≤ siteDist ν a b + siteDist ν b c + siteDist ν c d := by
  have h1 := siteDist_triangle ν a d b
  have h2 := siteDist_triangle ν b d c
  linarith only [h1, h2]

/-- If distinct sites are at distance `< 5/4`, the distance is `1`. -/
private theorem siteDist_eq_one_of_lt {ν : ℕ} {u w : Site ν} (hne : u ≠ w)
    (h : siteDist ν u w < 5 / 4) : siteDist ν u w = 1 := by
  have hsq : siteDist ν u w ^ 2 = ((∑ i, (u i - w i) ^ 2 : ℤ) : ℝ) := by
    rw [siteDist_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    push_cast
    rfl
  have h0 : siteDist ν u w ≠ 0 := by
    intro h0
    apply hne
    have := (Infra.Lattice.norm_latticeCast_sub_eq_zero_iff u w).1
      (by rw [← siteDist_eq_norm]; exact h0)
    exact this
  have hpos : 0 < siteDist ν u w := lt_of_le_of_ne (siteDist_nonneg ν u w) (Ne.symm h0)
  have hN0 : (0 : ℤ) < ∑ i, (u i - w i) ^ 2 := by
    have : (0 : ℝ) < ((∑ i, (u i - w i) ^ 2 : ℤ) : ℝ) := by rw [← hsq]; positivity
    exact_mod_cast this
  have hN1 : (∑ i, (u i - w i) ^ 2 : ℤ) < 2 := by
    have : ((∑ i, (u i - w i) ^ 2 : ℤ) : ℝ) < 2 := by
      rw [← hsq]; nlinarith only [h, hpos]
    exact_mod_cast this
  have hN : (∑ i, (u i - w i) ^ 2 : ℤ) = 1 := by omega
  rw [hN] at hsq
  have : siteDist ν u w ^ 2 = 1 := by rw [hsq]; norm_num
  nlinarith only [hpos, this]

/-! ### Chain clusters and boxes -/

/-- A nearest-neighbour cluster in `S` lifts to `S'` as soon as it lies in `S'`. -/
private theorem chainCluster_subset_of_subset {ν : ℕ} {S S' : Set (Site ν)} {a : Site ν}
    (ha : a ∈ S') (hsub : ∀ b ∈ nnComponent S a, b ∈ S') :
    nnComponent S a ⊆ nnComponent S' a := by
  rintro y ⟨haS, hy⟩
  induction hy with
  | refl => exact mem_chainCluster_self ha
  | tail hab hbc ih =>
    rename_i b c
    exact mem_chainCluster_of_lt ih (hsub c ⟨haS, hab.tail hbc⟩) hbc.2.2

private theorem nnComponent_symm {ν : ℕ} {U : Set (Site ν)} {x y : Site ν}
    (h : y ∈ nnComponent U x) : x ∈ nnComponent U y :=
  (mem_chainCluster_comm (siteDist_comm ν)).1 h

private theorem nnComponent_trans {ν : ℕ} {U : Set (Site ν)} {x y z : Site ν}
    (h : y ∈ nnComponent U x) (h' : z ∈ nnComponent U y) : z ∈ nnComponent U x := by
  have e : nnComponent U y = nnComponent U x :=
    chainCluster_eq_of_mem (siteDist_comm ν) h
  rw [← e]
  exact h'

/-- The integer box `{z | |z − c|_∞ ≤ h}`. -/
private def Box {ν : ℕ} (c : Site ν) (h : ℕ) : Set (Site ν) :=
  {z | ∀ i, c i - (h : ℤ) ≤ z i ∧ z i ≤ c i + (h : ℤ)}

private theorem box_coord {ν : ℕ} {c z : Site ν} {h : ℕ} (hz : z ∈ Box c h) (i : Fin ν) :
    |(z i : ℝ) - (c i : ℝ)| ≤ h := by
  have h1 := (hz i).1
  have h2 := (hz i).2
  rw [abs_le]
  constructor
  · have : (c i : ℝ) - h ≤ z i := by exact_mod_cast h1
    linarith only [this]
  · have : (z i : ℝ) ≤ c i + h := by exact_mod_cast h2
    linarith only [this]

private theorem mem_box_of_dist {ν : ℕ} {c z : Site ν} {h : ℕ} (hd : siteDist ν z c ≤ h) :
    z ∈ Box c h := by
  intro i
  have := abs_le.1 ((coord_le_siteDist z c i).trans hd)
  constructor
  · have : (c i : ℝ) - h ≤ z i := by linarith only [this.1]
    exact_mod_cast this
  · have : (z i : ℝ) ≤ c i + h := by linarith only [this.2]
    exact_mod_cast this

private theorem siteDist_box_le {ν : ℕ} {c x y : Site ν} {h : ℕ} (hx : x ∈ Box c h)
    (hy : y ∈ Box c h) : siteDist ν x y ≤ Real.sqrt ν * (2 * h) := by
  apply siteDist_le_sqrt_mul x y (by positivity)
  intro i
  have a := abs_le.1 (box_coord hx i)
  have b := abs_le.1 (box_coord hy i)
  rw [abs_le]
  constructor <;> linarith only [a.1, a.2, b.1, b.2]

private theorem siteDist_box_centre_le {ν : ℕ} {c x : Site ν} {h : ℕ} (hx : x ∈ Box c h) :
    siteDist ν c x ≤ Real.sqrt ν * h := by
  apply siteDist_le_sqrt_mul c x (by positivity)
  intro i
  rw [abs_sub_comm]
  exact box_coord hx i

private theorem box_finite {ν : ℕ} (c : Site ν) (h : ℕ) : (Box c h).Finite :=
  (finite_setOf_siteDist_le ν c (Real.sqrt ν * h)).subset fun _ hx => siteDist_box_centre_le hx

private theorem centre_mem_box {ν : ℕ} (c : Site ν) (h : ℕ) : c ∈ Box c h := by
  intro i
  constructor <;> omega

/-- One step towards the centre inside a box. -/
private theorem box_step {ν : ℕ} {c z : Site ν} {h : ℕ} (hz : z ∈ Box c h) (hne : z ≠ c) :
    ∃ z' ∈ Box c h, siteDist ν z' z = 1 ∧
      ∑ i, (z' i - c i).natAbs + 1 = ∑ i, (z i - c i).natAbs := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have key : ∀ δ : ℤ, (δ = 1 ∨ δ = -1) → (z i - δ - c i).natAbs + 1 = (z i - c i).natAbs →
      ∃ z' ∈ Box c h, siteDist ν z' z = 1 ∧
        ∑ j, (z' j - c j).natAbs + 1 = ∑ j, (z j - c j).natAbs := by
    intro δ hδ hlt
    refine ⟨Function.update z i (z i - δ), ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst hj
        have := hz j
        simp only [Function.update_self]
        omega
      · simp only [Function.update_of_ne hj]
        exact hz j
    · rw [siteDist_eq_norm]
      apply (Infra.Lattice.norm_latticeCast_sub_eq_one_iff _ _).2
      refine ⟨i, ?_, fun j hj => ?_⟩
      · simp only [Function.update_self]
        omega
      · simp [Function.update_of_ne hj]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase (Finset.univ) (fun j => (z j - c j).natAbs) (Finset.mem_univ i)]
      have : ∑ j ∈ Finset.univ.erase i, (Function.update z i (z i - δ) j - c j).natAbs =
          ∑ j ∈ Finset.univ.erase i, (z j - c j).natAbs :=
        Finset.sum_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [this]
      simp only [Function.update_self]
      omega
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact key (-1) (Or.inr rfl) (by omega)
  · exact key 1 (Or.inl rfl) (by omega)

private theorem box_reach {ν : ℕ} (c : Site ν) (h : ℕ) :
    ∀ n : ℕ, ∀ z ∈ Box c h, ∑ i, (z i - c i).natAbs ≤ n → z ∈ nnComponent (Box c h) c := by
  intro n
  induction n with
  | zero =>
    intro z hz hn
    have : z = c := by
      funext i
      have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hn)) i (Finset.mem_univ i)
      omega
    subst this
    exact mem_chainCluster_self hz
  | succ n ih =>
    intro z hz hn
    by_cases hzc : z = c
    · subst hzc
      exact mem_chainCluster_self hz
    · obtain ⟨z', hz', hd, hm⟩ := box_step hz hzc
      have := ih z' hz' (by omega)
      exact mem_chainCluster_of_lt this hz (by rw [hd]; norm_num)

private theorem box_connected {ν : ℕ} (c : Site ν) (h : ℕ) {z : Site ν} (hz : z ∈ Box c h) :
    z ∈ nnComponent (Box c h) c :=
  box_reach c h _ z hz le_rfl

private theorem box_mono {ν : ℕ} {c : Site ν} {h h' : ℕ} (hh : h ≤ h') : Box c h ⊆ Box c h' := by
  intro z hz i
  have := hz i
  have : (h : ℤ) ≤ h' := by exact_mod_cast hh
  constructor <;> omega

/-- The obstacle fill of a connected set around one of its points is connected. -/
private theorem fill_connected {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} (n : ℕ)
    {D₁ : Set (Site ν)} {c : Site ν} (hc : c ∈ D₁) (hconn : ∀ z ∈ D₁, z ∈ nnComponent D₁ c) :
    ∀ x ∈ obstacleFill K₀ G n D₁, x ∈ nnComponent (obstacleFill K₀ G n D₁) c := by
  have hsub : D₁ ⊆ obstacleFill K₀ G n D₁ := Set.subset_union_left
  have hD : ∀ z ∈ D₁, z ∈ nnComponent (obstacleFill K₀ G n D₁) c := fun z hz =>
    chainCluster_subset_of_subset (hsub hc)
      (fun b hb => hsub (chainCluster_subset c hb)) (hconn z hz)
  intro x hx
  rcases hx with hx | hx
  · exact hD x hx
  · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 hx
    have haR : a ∈ obstacleFill K₀ G n D₁ := hsub ha.1.1
    have h1 : x ∈ nnComponent (obstacleFill K₀ G n D₁) a :=
      chainCluster_subset_of_subset haR (fun b hb => Or.inr (Set.mem_iUnion₂.2 ⟨a, ha, hb⟩)) hxa
    exact nnComponent_trans (hD a ha.1.1) h1

private theorem connected_of_centre {ν : ℕ} {R : Set (Site ν)} {c : Site ν}
    (h : ∀ x ∈ R, x ∈ nnComponent R c) : ∀ x ∈ R, ∀ y ∈ R, y ∈ nnComponent R x :=
  fun x hx y hy => nnComponent_trans (nnComponent_symm (h x hx)) (h y hy)


/--
(`R ∩ (S_k ∖ C) = ∅` follows from
`R ⊆ C^[d_{k+1}]` and A(k)(b).) Strengthening: none of the conclusions is dropped; the extra
hypothesis `0 < ν` is necessary (for `ν = 0` the lattice is a point and no pair of points is at
distance `≥ d_{k+1}/5`), matching the standing assumption `ν ≥ 1`.
-/
theorem exists_regionAround {ν : ℕ} (hν : 0 < ν) {K₀ : ℝ} (hK : ScaleConditions K₀)
    (hKν : ∀ k, 80 * Real.sqrt ν * (scaleD K₀ k + 1) ≤ scaleD K₀ (k + 1))
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {C : Set (Site ν)}
    (hC : C ∈ G k) :
    ∃ R : Set (Site ν), R.Finite ∧ (∀ x ∈ R, ∀ y ∈ R, y ∈ nnComponent R x) ∧
      Admissible K₀ G (k + 1) R ∧ nbhd C (4 * scaleD K₀ k + 2) ⊆ R ∧
      R ⊆ nbhd C (scaleD K₀ (k + 1)) ∧
      (∃ x ∈ R, ∃ y ∈ R, scaleD K₀ (k + 1) / 5 ≤ siteDist ν x y) ∧
      DiamLE (siteDist ν) R (3 * scaleD K₀ (k + 1) / 2) ∧
      Disjoint (vertexBoundary R) (nbhd C (4 * scaleD K₀ k)) := by
  obtain ⟨c, hc⟩ := hG.nonempty k C hC
  have hs1 : 1 ≤ Real.sqrt ν := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hν)
  set s := Real.sqrt ν with hs
  have hdk := scaleD_pos K₀ k
  set dk := scaleD K₀ k with hdkdef
  set D := scaleD K₀ (k + 1) with hDdef
  have hD : 80 * s * (dk + 1) ≤ D := hKν k
  set A : ℝ := D / (8 * s) with hA
  have hDA : D = 8 * s * A := by rw [hA]; field_simp
  have hA10 : 10 * (dk + 1) ≤ A := by
    have : 8 * s * (10 * (dk + 1)) ≤ 8 * s * A := by rw [← hDA]; nlinarith only [hD]
    exact le_of_mul_le_mul_left this (by positivity)
  have hA0 : 0 ≤ A := by nlinarith only [hdk, hA10]
  set h₁ : ℕ := ⌊A⌋₊ with hh₁
  set h₂ : ℕ := ⌊2 * A⌋₊ with hh₂
  have e1 : (h₁ : ℝ) ≤ A := Nat.floor_le hA0
  have e2 : A - 1 < h₁ := Nat.sub_one_lt_floor A
  have e3 : (h₂ : ℝ) ≤ 2 * A := Nat.floor_le (by linarith only [e1])
  have e4 : 2 * A - 1 < h₂ := Nat.sub_one_lt_floor (2 * A)
  have h12 : h₁ ≤ h₂ := Nat.floor_le_floor (by linarith only [e3])
  have hQ12 : Box c h₁ ⊆ Box c h₂ := box_mono h12
  -- the buffer `C^[4 d_k + 2] ⊆ Q₁`
  have hCQ : nbhd C (4 * dk + 2) ⊆ Box c h₁ := by
    rintro z ⟨c', hc', hz⟩
    apply mem_box_of_dist
    have h1 := hG.diam_le k C hC c' hc' c hc
    have h2 := siteDist_triangle ν z c c'
    linarith only [hA10, e2, hz, h1, h2]
  have hQfin : (Box c h₁).Finite := box_finite c h₁
  have hsep : ∀ x ∈ Box c h₁, ∀ y, y ∉ Box c h₂ → 10 * dk ≤ siteDist ν x y := by
    intro x hx y hy
    obtain ⟨i, hi⟩ : ∃ i, ¬(c i - (h₂ : ℤ) ≤ y i ∧ y i ≤ c i + (h₂ : ℤ)) := by
      by_contra hcon
      push Not at hcon
      exact hy fun i => by have := hcon i; omega
    have hxi := hx i
    have hcoord := coord_le_siteDist x y i
    have key : (h₂ : ℝ) + 1 - h₁ ≤ |(x i : ℝ) - y i| := by
      rcases not_and_or.1 hi with h | h
      · have h' : y i < c i - (h₂ : ℤ) := by omega
        have : (y i : ℝ) + 1 ≤ c i - h₂ := by exact_mod_cast (by omega : y i + 1 ≤ c i - (h₂ : ℤ))
        have : (c i : ℝ) - h₁ ≤ x i := by exact_mod_cast hxi.1
        rw [abs_of_pos (by linarith)]
        linarith
      · have h' : c i + (h₂ : ℤ) < y i := by omega
        have : (c i : ℝ) + h₂ + 1 ≤ y i := by
          exact_mod_cast (by omega : c i + (h₂ : ℤ) + 1 ≤ y i)
        have : (x i : ℝ) ≤ c i + h₁ := by exact_mod_cast hxi.2
        rw [abs_of_neg (by linarith)]
        linarith
    linarith only [hA10, e1, e4, hcoord, key]
  obtain ⟨hRfin, hQR, hRQ, hRadm⟩ := obstacleFill_spec hK hG k hQfin hQ12 hsep
  set R := obstacleFill K₀ G (k + 1) (Box c h₁) with hR
  have hRconn : ∀ x ∈ R, x ∈ nnComponent R c :=
    fill_connected (k + 1) (centre_mem_box c h₁) (fun z hz => box_connected c h₁ hz)
  refine ⟨R, hRfin, connected_of_centre hRconn, hRadm, hCQ.trans hQR, ?_, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨c, hc, ?_⟩
    have := siteDist_box_centre_le (hRQ hz)
    rw [siteDist_comm]
    nlinarith only [hs1, hDA, e3, this]
  · let x : Site ν := fun i => c i - (h₁ : ℤ)
    let y : Site ν := fun i => c i + (h₁ : ℤ)
    have hx : x ∈ Box c h₁ := fun i => by simp only [x]; constructor <;> omega
    have hy : y ∈ Box c h₁ := fun i => by simp only [y]; constructor <;> omega
    refine ⟨x, hQR hx, y, hQR hy, ?_⟩
    have hxy : siteDist ν x y = s * (2 * h₁) := by
      rw [siteDist_eq_sqrt]
      have : ∀ i : Fin ν, ((x i : ℝ) - (y i : ℝ)) ^ 2 = (2 * h₁) ^ 2 := by
        intro i; simp only [x, y]; push_cast; ring
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (Nat.cast_nonneg ν), Real.sqrt_sq (by positivity)]
    rw [hxy]
    have : s * (A - 1) ≤ s * h₁ := mul_le_mul_of_nonneg_left e2.le (by linarith only [hs1])
    nlinarith only [hdk, hDA, hA10, e2, this]
  · intro a ha b hb
    have := siteDist_box_le (hRQ ha) (hRQ hb)
    have h2 : s * (2 * h₂) ≤ s * (2 * (2 * A)) :=
      mul_le_mul_of_nonneg_left (by linarith only [e3]) (by linarith only [hs1])
    nlinarith only [hs1, hDA, this, h2]
  · rw [Set.disjoint_left]
    rintro a ⟨haR, b, hab, hbR⟩ ⟨c', hc', had⟩
    apply hbR
    apply hQR
    apply hCQ
    refine ⟨c', hc', ?_⟩
    have := siteDist_triangle ν b c' a
    rw [siteDist_comm ν b a] at this
    linarith only [hab, had, this]


private noncomputable def bandW (K₀ : ℝ) : ℕ → ℝ
  | 0 => 2
  | k + 1 => 10 * scaleD K₀ k + 2

private theorem bandW_props {K₀ : ℝ} (hK : ScaleConditions K₀) (k : ℕ) :
    2 ≤ bandW K₀ k ∧ 3 * bandW K₀ k < scaleD K₀ k := by
  obtain ⟨h0, -, -, -, h5, -⟩ := hK
  cases k with
  | zero => exact ⟨le_rfl, by simp only [bandW]; linarith only [h0]⟩
  | succ k =>
    have := h5 k
    have := scaleD_pos K₀ k
    exact ⟨by simp only [bandW]; linarith only [this], by simp only [bandW]; linarith⟩

/-- A point far from `C` is far from every point near `C`. -/
private theorem far_dist {ν : ℕ} {C : Set (Site ν)} {z u : Site ν} {r s : ℝ}
    (hz : ∀ c ∈ C, r < siteDist ν z c) (hu : ∃ c ∈ C, siteDist ν u c ≤ s) :
    r - s < siteDist ν z u := by
  obtain ⟨c, hc, hd⟩ := hu
  have := siteDist_triangle ν z c u
  have := siteDist_comm ν c u
  have := hz c hc
  linarith

private theorem not_near_far {ν : ℕ} {C : Set (Site ν)} {z : Site ν} {r : ℝ}
    (h : z ∉ nbhd C r) : ∀ c ∈ C, r < siteDist ν z c := by
  intro c hc
  by_contra hle
  exact h ⟨c, hc, not_lt.1 hle⟩

private theorem nbhd_mono {ν : ℕ} {C : Set (Site ν)} {r r' : ℝ} (h : r ≤ r') :
    nbhd C r ⊆ nbhd C r' := fun _ ⟨c, hc, hd⟩ => ⟨c, hc, hd.trans h⟩

private theorem mem_nbhd_self {ν : ℕ} {C : Set (Site ν)} {r : ℝ} (hr : 0 ≤ r) {c : Site ν}
    (hc : c ∈ C) : c ∈ nbhd C r := ⟨c, hc, by rw [siteDist_self]; exact hr⟩

private theorem nbhd_finite {ν : ℕ} {C : Set (Site ν)} (hC : C.Finite) (r : ℝ) :
    (nbhd C r).Finite :=
  (hC.biUnion fun c _ => finite_setOf_siteDist_le ν c r).subset fun x ⟨c, hc, hd⟩ =>
    Set.mem_iUnion₂.2 ⟨c, hc, by rw [Set.mem_ofPred_eq, siteDist_comm]; exact hd⟩

/-- The two radial bands: either both `x, y` are far from `C` (low band), or each is near `C` or
beyond `4 d` (high band). -/
private theorem band_choice {ν : ℕ} {C : Set (Site ν)} {x y : Site ν} {d W : ℝ} (hW : 2 ≤ W)
    (hd : 3 * W < d) (hxy : ¬(x ∈ nbhd C (4 * d) ∧ y ∈ nbhd C (4 * d))) :
    ((∀ c ∈ C, d + W < siteDist ν x c) ∧ (∀ c ∈ C, d + W < siteDist ν y c)) ∨
      ((x ∈ nbhd C (2 * d - W - 1) ∨ ∀ c ∈ C, 4 * d < siteDist ν x c) ∧
        (y ∈ nbhd C (2 * d - W - 1) ∨ ∀ c ∈ C, 4 * d < siteDist ν y c)) := by
  have hm : nbhd C (2 * d - W - 1) ⊆ nbhd C (4 * d) := nbhd_mono (by linarith only [hW, hd])
  by_cases hx : x ∈ nbhd C (2 * d - W - 1) <;> by_cases hy : y ∈ nbhd C (2 * d - W - 1)
  · exact absurd ⟨hm hx, hm hy⟩ hxy
  · right
    refine ⟨Or.inl hx, Or.inr (not_near_far fun h => hxy ⟨hm hx, h⟩)⟩
  · right
    refine ⟨Or.inr (not_near_far fun h => hxy ⟨h, hm hy⟩), Or.inl hy⟩
  · left
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := not_near_far hx c hc
      linarith only [hW, hd, this]
    · have := not_near_far hy c hc
      linarith only [hW, hd, this]


private theorem mem_obstacleUnion_of {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n j : ℕ}
    (hj : j < n) {C' : Set (Site ν)} (hC' : C' ∈ G j) {x : Site ν}
    (hx : x ∈ nbhd C' (4 * scaleD K₀ j + 2)) : x ∈ obstacleUnion K₀ G n :=
  Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hj, Set.mem_iUnion₂.2 ⟨C', hC', hx⟩⟩

/-- Obstacle components are filled whole: a `U`-neighbour of a filled `U`-point is filled. -/
private theorem fill_sym {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n : ℕ}
    {D₁ : Set (Site ν)} {a b : Site ν} (hab : siteDist ν a b = 1)
    (ha : a ∈ obstacleUnion K₀ G n) (hb : b ∈ obstacleUnion K₀ G n)
    (hbB : b ∈ obstacleFill K₀ G n D₁) : a ∈ obstacleFill K₀ G n D₁ := by
  have hba : siteDist ν b a < 5 / 4 := by rw [siteDist_comm, hab]; norm_num
  rcases hbB with hbD | hbc
  · by_cases haD : a ∈ D₁
    · exact Or.inl haD
    · refine Or.inr (Set.mem_iUnion₂.2 ⟨b, ⟨⟨hbD, a, by rw [siteDist_comm]; exact hab, haD⟩, hb⟩,
        mem_chainCluster_of_lt (mem_chainCluster_self hb) ha hba⟩)
  · obtain ⟨a', ha', hba'⟩ := Set.mem_iUnion₂.1 hbc
    exact Or.inr (Set.mem_iUnion₂.2 ⟨a', ha', mem_chainCluster_of_lt hba' ha hba⟩)


private theorem bandFill {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {C : Set (Site ν)}
    (hC : C ∈ G k) (t : ℝ) :
    ∃ B : Set (Site ν), nbhd C t ⊆ B ∧ B ⊆ nbhd C (t + bandW K₀ k - 1) ∧
      Admissible K₀ G k B ∧
      ∀ j < k, ∀ C' ∈ G j, ∀ a b : Site ν, siteDist ν a b = 1 →
        a ∈ nbhd C' (4 * scaleD K₀ j) → b ∈ B → a ∈ B := by
  cases k with
  | zero =>
    refine ⟨nbhd C t, subset_rfl, nbhd_mono (by simp only [bandW]; linarith only []),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k =>
    have hW : bandW K₀ (k + 1) = 10 * scaleD K₀ k + 2 := rfl
    have hdk := scaleD_pos K₀ k
    have hfin : (nbhd C t).Finite := nbhd_finite (hG.finite _ C hC) t
    have hsep : ∀ x ∈ nbhd C t, ∀ y, y ∉ nbhd C (t + bandW K₀ (k + 1) - 1) →
        10 * scaleD K₀ k ≤ siteDist ν x y := by
      intro x ⟨c, hc, hxc⟩ y hy
      have h1 := not_near_far hy c hc
      have h2 := siteDist_triangle ν y c x
      have h3 := siteDist_comm ν x y
      have h4 := siteDist_comm ν x c
      linarith only [hW, hxc, h1, h2, h3]
    obtain ⟨-, h1, h2, h3⟩ := obstacleFill_spec hK hG k hfin
      (nbhd_mono (by simp only [bandW]; linarith only [hdk]) : nbhd C t ⊆
        nbhd C (t + bandW K₀ (k + 1) - 1)) hsep
    refine ⟨obstacleFill K₀ G (k + 1) (nbhd C t), h1, h2, h3, ?_⟩
    intro j hj C' hC' a b hab ha hb
    have hU : ∀ z, z ∈ nbhd C' (4 * scaleD K₀ j + 1) → z ∈ obstacleUnion K₀ G (k + 1) :=
      fun z hz => mem_obstacleUnion_of hj hC' (nbhd_mono (by linarith only []) hz)
    refine fill_sym hab (hU a (nbhd_mono (by linarith only []) ha)) (hU b ?_) hb
    obtain ⟨c, hc, hac⟩ := ha
    refine ⟨c, hc, ?_⟩
    have := siteDist_triangle ν b c a
    rw [siteDist_comm ν b a] at this
    linarith only [hab, hac, this]

/-- A nearest-neighbour edge leaves `B` inside a connected `R`. -/
private theorem exists_edge {ν : ℕ} {R B : Set (Site ν)} {p q : Site ν}
    (hconn : ∀ x ∈ R, ∀ y ∈ R, y ∈ nnComponent R x) (hBR : B ⊆ R) (hp : p ∈ B) (hq : q ∈ R)
    (hqB : q ∉ B) : ∃ u ∈ B, ∃ w ∈ R, w ∉ B ∧ siteDist ν u w < 5 / 4 := by
  obtain ⟨-, hch⟩ := hconn p (hBR hp) q hq
  have key : ∀ y, Relation.ReflTransGen (chainStep (siteDist ν) R (5 / 4)) p y → y ∈ B ∨
      ∃ u ∈ B, ∃ w ∈ R, w ∉ B ∧ siteDist ν u w < 5 / 4 := by
    intro y hy
    induction hy with
    | refl => exact Or.inl hp
    | tail hab hbc ih =>
      rename_i b c
      rcases ih with hb | found
      · by_cases hcB : c ∈ B
        · exact Or.inl hcB
        · exact Or.inr ⟨b, hb, c, hbc.2.1, hcB, hbc.2.2⟩
      · exact Or.inr found
  rcases key q hch with h | h
  · exact absurd h hqB
  · exact h


private theorem cut_core {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {C : Set (Site ν)}
    (hC : C ∈ G k) {R : Set (Site ν)}
    (hRconn : ∀ x ∈ R, ∀ y ∈ R, y ∈ nnComponent R x) (hRadm : Admissible K₀ G (k + 1) R)
    (hCR : nbhd C (4 * scaleD K₀ k) ⊆ R) {x y : Site ν} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : scaleD K₀ (k + 1) / 5 ≤ siteDist ν x y) {t : ℝ} (ht0 : 0 ≤ t)
    (htW : t + bandW K₀ k ≤ 3 * scaleD K₀ k) :
    ∃ B : Set (Site ν), nbhd C t ⊆ B ∧ B ⊆ nbhd C (t + bandW K₀ k - 1) ∧ C ⊆ B ∧
      B ⊆ nbhd C (4 * scaleD K₀ k) ∧ Admissible K₀ G k B ∧ Admissible K₀ G k (R \ B) ∧
      DiamLE (siteDist ν) B (7 * scaleD K₀ k) ∧
      (∃ w ∈ R \ B, ∃ c ∈ C, siteDist ν w c ≤ 3 * scaleD K₀ k) := by
  obtain ⟨hW2, hW3⟩ := bandW_props hK k
  have hdk := scaleD_pos K₀ k
  have h6 := hK.2.2.2.2.2.1 k
  obtain ⟨B, hB1, hB2, hBadm, hBsym⟩ := bandFill hK hG k hC t
  have hBN : B ⊆ nbhd C (3 * scaleD K₀ k - 1) :=
    hB2.trans (nbhd_mono (by linarith only [htW]))
  have hBR : B ⊆ R := (hBN.trans (nbhd_mono (by linarith only [hdk]))).trans hCR
  have hdiam : DiamLE (siteDist ν) B (7 * scaleD K₀ k) := by
    intro a ha b hb
    obtain ⟨ca, hca, hda⟩ := hBN ha
    obtain ⟨cb, hcb, hdb⟩ := hBN hb
    have h1 := hG.diam_le k C hC ca hca cb hcb
    have h2 := siteDist_three a ca cb b
    have h3 := siteDist_comm ν cb b
    linarith only [hda, hdb, h1, h2, h3]
  obtain ⟨c₀, hc₀⟩ := hG.nonempty k C hC
  have hc₀B : c₀ ∈ B := hB1 (mem_nbhd_self ht0 hc₀)
  have hnot : ¬(x ∈ B ∧ y ∈ B) := fun ⟨h1, h2⟩ => by
    have := hdiam x h1 y h2
    linarith only [hxy, hdk, h6, this]
  obtain ⟨q, hqR, hqB⟩ : ∃ q ∈ R, q ∉ B := by
    by_cases hxB : x ∈ B
    · exact ⟨y, hy, fun h => hnot ⟨hxB, h⟩⟩
    · exact ⟨x, hx, hxB⟩
  obtain ⟨u, hu, w, hwR, hwB, hlt⟩ := exists_edge hRconn hBR hc₀B hqR hqB
  have hu1 : siteDist ν u w = 1 :=
    siteDist_eq_one_of_lt (fun h => hwB (h ▸ hu)) hlt
  refine ⟨B, hB1, hB2, fun c hc => hB1 (mem_nbhd_self ht0 hc),
    hBN.trans (nbhd_mono (by linarith only [hdk])), hBadm, ?_, hdiam, ?_⟩
  · intro j hj C' hC'
    rw [Set.disjoint_left]
    rintro a ⟨⟨haR, haB⟩, b, hab, hb⟩ hac
    by_cases hbR : b ∈ R
    · have hbB : b ∈ B := by
        by_contra hbB
        exact hb ⟨hbR, hbB⟩
      exact haB (hBsym j hj C' hC' a b hab hac hbB)
    · exact Set.disjoint_left.1 (hRadm j (Nat.lt_succ_of_lt hj) C' hC') ⟨haR, b, hab, hbR⟩ hac
  · obtain ⟨cu, hcu, hdu⟩ := hBN hu
    refine ⟨w, ⟨hwR, hwB⟩, cu, hcu, ?_⟩
    have := siteDist_triangle ν w cu u
    have := siteDist_comm ν u w
    linarith


theorem exists_radialCut {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {C : Set (Site ν)}
    (hC : C ∈ G k) {R : Set (Site ν)}
    (hRconn : ∀ x ∈ R, ∀ y ∈ R, y ∈ nnComponent R x) (hRadm : Admissible K₀ G (k + 1) R)
    (hCR : nbhd C (4 * scaleD K₀ k) ⊆ R) {x y : Site ν} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : scaleD K₀ (k + 1) / 5 ≤ siteDist ν x y) :
    ∃ B : Set (Site ν), C ⊆ B ∧ B ⊆ nbhd C (4 * scaleD K₀ k) ∧
      B ⊆ nbhd C (3 * scaleD K₀ k - 1) ∧ Admissible K₀ G k B ∧
      Admissible K₀ G k (R \ B) ∧ DiamLE (siteDist ν) B (7 * scaleD K₀ k) ∧
      (∃ w ∈ R \ B, ∃ c ∈ C, siteDist ν w c ≤ 3 * scaleD K₀ k) ∧
      ∀ u ∈ B, ∀ w ∈ R \ B, siteDist ν u w = 1 →
        scaleD K₀ k ≤ siteDist ν x u ∧ scaleD K₀ k ≤ siteDist ν y u ∧
          scaleD K₀ k ≤ siteDist ν x w ∧ scaleD K₀ k ≤ siteDist ν y w := by
  obtain ⟨hW2, hW3⟩ := bandW_props hK k
  have hdk := scaleD_pos K₀ k
  have h6 := hK.2.2.2.2.2.1 k
  set d := scaleD K₀ k with hd
  set W := bandW K₀ k with hW
  have hnear : ¬(x ∈ nbhd C (4 * d) ∧ y ∈ nbhd C (4 * d)) := by
    rintro ⟨⟨cx, hcx, hdx⟩, ⟨cy, hcy, hdy⟩⟩
    have h1 := hG.diam_le k C hC cx hcx cy hcy
    have h2 := siteDist_three x cx cy y
    have h3 := siteDist_comm ν cy y
    linarith only [hxy, h6, hdx, hdy, h1, h2, h3]
  -- given `u ∈ B`, `w ∈ R \ B` adjacent: both lie in `C^[3 d]`
  rcases band_choice hW2 hW3 hnear with ⟨hxF, hyF⟩ | ⟨hxH, hyH⟩
  · obtain ⟨B, hB1, hB2, hCB, hB4, hBadm, hQadm, hdiam, hw⟩ :=
      cut_core hK hG k hC hRconn hRadm hCR hx hy hxy (t := 0) le_rfl (by linarith only [hW2, hW3])
    refine ⟨B, hCB, hB4, hB2.trans (nbhd_mono (by linarith only [hW2, hW3])), hBadm, hQadm, hdiam,
      hw, ?_⟩
    intro u hu w hwB huw
    obtain ⟨cu, hcu, hdu⟩ := hB2 hu
    have hwu : siteDist ν w cu ≤ W := by
      have := siteDist_triangle ν w cu u
      have := siteDist_comm ν u w
      linarith
    have key : ∀ z, (∀ c ∈ C, d + W < siteDist ν z c) →
        d ≤ siteDist ν z u ∧ d ≤ siteDist ν z w := fun z hz => by
      have a := far_dist hz ⟨cu, hcu, hdu⟩
      have b := far_dist hz ⟨cu, hcu, hwu⟩
      constructor <;> linarith only [a, b]
    obtain ⟨a1, a2⟩ := key x hxF
    obtain ⟨b1, b2⟩ := key y hyF
    exact ⟨a1, b1, a2, b2⟩
  · obtain ⟨B, hB1, hB2, hCB, hB4, hBadm, hQadm, hdiam, hw⟩ :=
      cut_core hK hG k hC hRconn hRadm hCR hx hy hxy (t := 3 * d - W)
        (by linarith only [hW2, hW3]) (by linarith only [])
    refine ⟨B, hCB, hB4, hB2.trans (nbhd_mono (by linarith only [])), hBadm, hQadm, hdiam, hw, ?_⟩
    intro u hu w hwB huw
    have hwN : w ∉ nbhd C (3 * d - W) := fun h => hwB.2 (hB1 h)
    have hwF := not_near_far hwN
    obtain ⟨cu, hcu, hdu⟩ := hB2 hu
    rw [← hW] at hdu
    have hwu : siteDist ν w cu ≤ 3 * d := by
      have := siteDist_triangle ν w cu u
      have := siteDist_comm ν u w
      have : 3 * d - W + W - 1 ≤ 3 * d - 1 := by linarith only []
      linarith
    have huF : ∀ c ∈ C, 3 * d - W - 1 < siteDist ν u c := by
      intro c hc
      have := hwF c hc
      have := siteDist_triangle ν w c u
      have := siteDist_comm ν u w
      linarith
    have key : ∀ z, (z ∈ nbhd C (2 * d - W - 1) ∨ ∀ c ∈ C, 4 * d < siteDist ν z c) →
        d ≤ siteDist ν z u ∧ d ≤ siteDist ν z w := by
      intro z hz
      rcases hz with ⟨cz, hcz, hdz⟩ | hz
      · have h1 := huF cz hcz
        have h2 := hwF cz hcz
        have h3 := siteDist_triangle ν u cz z
        have h4 := siteDist_triangle ν w cz z
        have h5 := siteDist_comm ν z u
        have h6 := siteDist_comm ν z w
        constructor <;> linarith only [hdz, h1, h3, h5, h2, h4, h6]
      · have a := far_dist (u := u) hz ⟨cu, hcu, (by linarith only [hdu] : siteDist ν u cu ≤ 3 * d)⟩
        have b := far_dist (u := w) hz ⟨cu, hcu, hwu⟩
        constructor <;> linarith only [a, b]
    obtain ⟨a1, a2⟩ := key x hxH
    obtain ⟨b1, b2⟩ := key y hyH
    exact ⟨a1, b1, a2, b2⟩

/--
For any `(k+1)`-admissible `R` (no containment
`C^[4 d_k] ⊆ R`, connectivity or `x, y` needed: the band is taken at `t = 0`), there is `B` with
`C ⊆ B ⊆ C^[d_k / 3]`, `B` and `R ∖ B` both `(k−1)`-admissible, and `diam B ≤ 2 d_k`.
-/
theorem exists_lowCut {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {C : Set (Site ν)}
    (hC : C ∈ G k) {R : Set (Site ν)} (hRadm : Admissible K₀ G (k + 1) R) :
    ∃ B : Set (Site ν), C ⊆ B ∧ B ⊆ nbhd C (scaleD K₀ k / 3) ∧ Admissible K₀ G k B ∧
      Admissible K₀ G k (R \ B) ∧ DiamLE (siteDist ν) B (2 * scaleD K₀ k) := by
  obtain ⟨hW2, hW3⟩ := bandW_props hK k
  have hdk := scaleD_pos K₀ k
  obtain ⟨B, hB1, hB2, hBadm, hBsym⟩ := bandFill hK hG k hC 0
  have hBN : B ⊆ nbhd C (scaleD K₀ k / 3) :=
    hB2.trans (nbhd_mono (by linarith only [hW3]))
  refine ⟨B, fun c hc => hB1 (mem_nbhd_self le_rfl hc), hBN, hBadm, ?_, ?_⟩
  · intro j hj C' hC'
    rw [Set.disjoint_left]
    rintro a ⟨⟨haR, haB⟩, b, hab, hb⟩ hac
    by_cases hbR : b ∈ R
    · have hbB : b ∈ B := by
        by_contra hbB
        exact hb ⟨hbR, hbB⟩
      exact haB (hBsym j hj C' hC' a b hab hac hbB)
    · exact Set.disjoint_left.1 (hRadm j (Nat.lt_succ_of_lt hj) C' hC') ⟨haR, b, hab, hbR⟩ hac
  · intro a ha b hb
    obtain ⟨ca, hca, hda⟩ := hBN ha
    obtain ⟨cb, hcb, hdb⟩ := hBN hb
    have h1 := hG.diam_le k C hC ca hca cb hcb
    have h2 := siteDist_three a ca cb b
    have h3 := siteDist_comm ν cb b
    linarith only [hdk, hda, hdb, h1, h2, h3]

end FroehlichSpencer.T12

end
