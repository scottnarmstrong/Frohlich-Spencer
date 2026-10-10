/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerAssembly

/-!
* `card_le_of_separated`: finitely many objects whose chosen sites lie in an `ℓ∞`-box of
  half-width `ℓ` and are pairwise farther than `s` apart number at most `(4ℓ/s + 2)²`
  (cells of side `s/2`).
* `card_near_square_le`: densities pairwise farther than `s` apart that come within `R` of one
  scale-`i` free square number at most `(4(2^i + R)/s + 2)²`.
* `card_neighbors_le`: the densities of such a family within `2s` of one of them number at most
  `324 · A_i` when `2^i ≤ 2s`.
* `sum_cover_le`: if each scale-`i` square meets at most `m` of the parts of a decomposition of a
  support, the parts' cover numbers sum to at most `m · A_i`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

theorem abs_fst_le_siteDist (x y : Site L) :
    |(x.1.val : ℝ) - y.1.val| ≤ euclideanSiteDistance x y := by
  unfold euclideanSiteDistance
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((x.2.val : ℝ) - y.2.val)])

theorem abs_snd_le_siteDist (x y : Site L) :
    |(x.2.val : ℝ) - y.2.val| ≤ euclideanSiteDistance x y := by
  unfold euclideanSiteDistance
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((x.1.val : ℝ) - y.1.val)])

/-- Two sites of one scale-`i` free square differ by less than `2^i` in each coordinate. -/
theorem abs_sub_lt_of_mem_kpSquare {i : ℕ} {a x y : Site L} (hx : x ∈ kpSquare .free L i a)
    (hy : y ∈ kpSquare .free L i a) :
    |(x.1.val : ℝ) - y.1.val| < 2 ^ i ∧ |(x.2.val : ℝ) - y.2.val| < 2 ^ i := by
  have hside : ((squareSide i : ℕ) : ℝ) = 2 ^ i := by simp [squareSide]
  unfold kpSquare at hx hy
  by_cases hbig : squareSide i > L
  · have hL : (L : ℝ) < 2 ^ i := by rw [← hside]; exact_mod_cast hbig
    have h1 : (x.1.val : ℝ) < L := by exact_mod_cast x.1.isLt
    have h2 : (y.1.val : ℝ) < L := by exact_mod_cast y.1.isLt
    have h3 : (x.2.val : ℝ) < L := by exact_mod_cast x.2.isLt
    have h4 : (y.2.val : ℝ) < L := by exact_mod_cast y.2.isLt
    have h5 : (0 : ℝ) ≤ x.1.val := Nat.cast_nonneg _
    have h6 : (0 : ℝ) ≤ y.1.val := Nat.cast_nonneg _
    have h7 : (0 : ℝ) ≤ x.2.val := Nat.cast_nonneg _
    have h8 : (0 : ℝ) ≤ y.2.val := Nat.cast_nonneg _
    constructor <;> rw [abs_lt] <;> constructor <;> linarith
  · simp only [hbig, ite_false, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
    have c1 : (a.1.val : ℝ) ≤ x.1.val := by exact_mod_cast hx1
    have c2 : (x.1.val : ℝ) < a.1.val + 2 ^ i := by rw [← hside]; exact_mod_cast hx2
    have c3 : (a.2.val : ℝ) ≤ x.2.val := by exact_mod_cast hx3
    have c4 : (x.2.val : ℝ) < a.2.val + 2 ^ i := by rw [← hside]; exact_mod_cast hx4
    have d1 : (a.1.val : ℝ) ≤ y.1.val := by exact_mod_cast hy1
    have d2 : (y.1.val : ℝ) < a.1.val + 2 ^ i := by rw [← hside]; exact_mod_cast hy2
    have d3 : (a.2.val : ℝ) ≤ y.2.val := by exact_mod_cast hy3
    have d4 : (y.2.val : ℝ) < a.2.val + 2 ^ i := by rw [← hside]; exact_mod_cast hy4
    constructor <;> rw [abs_lt] <;> constructor <;> linarith

/-- **Cell packing.** Objects with chosen sites in an `ℓ∞`-box of half-width `ℓ`, pairwise farther
than `s`, number at most `(4ℓ/s + 2)²`. -/
theorem card_le_of_separated {ι : Type*} {T : Finset ι} (y : ι → Site L) {s ℓ : ℝ} (hs : 0 < s)
    (c : ℝ × ℝ)
    (hbox : ∀ t ∈ T, |((y t).1.val : ℝ) - c.1| ≤ ℓ ∧ |((y t).2.val : ℝ) - c.2| ≤ ℓ)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → s < euclideanSiteDistance (y t) (y t')) :
    (T.card : ℝ) ≤ (4 * ℓ / s + 2) ^ 2 := by
  classical
  rcases T.eq_empty_or_nonempty with hT | ⟨t₀, ht₀⟩
  · simp [hT]
    positivity
  have hℓ : 0 ≤ ℓ := (abs_nonneg _).trans (hbox t₀ ht₀).1
  set m := s / 2 with hm
  have hm0 : 0 < m := by positivity
  let g : ι → ℤ × ℤ := fun t =>
    (⌊(((y t).1.val : ℝ) - c.1) / m⌋, ⌊(((y t).2.val : ℝ) - c.2) / m⌋)
  let I : Finset ℤ := Finset.Icc ⌊-ℓ / m⌋ ⌊ℓ / m⌋
  have hmaps : ∀ t ∈ T, g t ∈ I ×ˢ I := by
    intro t ht
    obtain ⟨h1, h2⟩ := hbox t ht
    rw [abs_le] at h1 h2
    simp only [Finset.mem_product, I, Finset.mem_Icc, g]
    refine ⟨⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩⟩
    · exact div_le_div_of_nonneg_right h1.1 hm0.le
    · exact div_le_div_of_nonneg_right h1.2 hm0.le
    · exact div_le_div_of_nonneg_right h2.1 hm0.le
    · exact div_le_div_of_nonneg_right h2.2 hm0.le
  have hinj : Set.InjOn g T := by
    intro t ht t' ht' hgt
    by_contra hne
    have hsep' := hsep t ht t' ht' hne
    have hx := Int.abs_sub_lt_one_of_floor_eq_floor (congrArg Prod.fst hgt)
    have hy := Int.abs_sub_lt_one_of_floor_eq_floor (congrArg Prod.snd hgt)
    rw [← sub_div, abs_div, abs_of_pos hm0, div_lt_one hm0] at hx hy
    have ex : (((y t).1.val : ℝ) - c.1) - (((y t').1.val : ℝ) - c.1) =
        (y t).1.val - (y t').1.val := by ring
    have ey : (((y t).2.val : ℝ) - c.2) - (((y t').2.val : ℝ) - c.2) =
        (y t).2.val - (y t').2.val := by ring
    rw [ex] at hx
    rw [ey] at hy
    have hx2 : (((y t).1.val : ℝ) - (y t').1.val) ^ 2 < m ^ 2 := by
      have := abs_lt.mp hx
      nlinarith
    have hy2 : (((y t).2.val : ℝ) - (y t').2.val) ^ 2 < m ^ 2 := by
      have := abs_lt.mp hy
      nlinarith
    have hd : euclideanSiteDistance (y t) (y t') < s := by
      unfold euclideanSiteDistance
      rw [Real.sqrt_lt' hs, hm] at *
      nlinarith
    linarith
  have hcard : T.card ≤ (I ×ˢ I).card := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Finset.card_product] at hcard
  have hle : ⌊-ℓ / m⌋ ≤ ⌊ℓ / m⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hm0.le)
  have hIcard : ((I.card : ℕ) : ℝ) = ((⌊ℓ / m⌋ + 1 - ⌊-ℓ / m⌋ : ℤ) : ℝ) := by
    simp only [I, Int.card_Icc]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have hI : ((I.card : ℕ) : ℝ) ≤ 4 * ℓ / s + 2 := by
    rw [hIcard]
    push_cast
    have h1 := Int.floor_le (ℓ / m)
    have h2 := Int.lt_floor_add_one (-ℓ / m)
    have h3 : ℓ / m = 2 * ℓ / s := by rw [hm]; field_simp
    have h4 : -ℓ / m = -(2 * ℓ / s) := by rw [neg_div, h3]
    have h5 : 4 * ℓ / s = 2 * (2 * ℓ / s) := by ring
    linarith
  calc (T.card : ℝ) ≤ ((I.card * I.card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((I.card : ℕ) : ℝ) ^ 2 := by push_cast; ring
    _ ≤ (4 * ℓ / s + 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hI 2

/-- The set distance of nonempty sets is attained. -/
theorem exists_setDist_eq {S T : Finset (Site L)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ∃ x ∈ S, ∃ y ∈ T, euclideanSetDistance S T = euclideanSiteDistance x y := by
  classical
  have hprod : (S.product T).Nonempty := by
    obtain ⟨x, hx⟩ := hS
    obtain ⟨y, hy⟩ := hT
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  have hmem := Finset.min'_mem ((S.product T).image fun p : Site L × Site L =>
    euclideanSiteDistance p.1 p.2) (Finset.image_nonempty.mpr hprod)
  obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp hmem
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  refine ⟨p.1, hp1, p.2, hp2, ?_⟩
  rw [euclideanSetDistance, dite_eq_left hprod]
  exact hpeq.symm

/-- A minimum cover exists. -/
theorem exists_minCover (j : ℕ) (ρ : ChargeDensity L) :
    ∃ C, IsSquareCover .free L j ρ C ∧ C.card = squareCoverNumber .free L j ρ := by
  classical
  have hmem := Finset.min'_mem ((squareCoverCandidates .free L j ρ).image Finset.card)
    (Finset.image_nonempty.mpr (squareCoverCandidates_nonempty .free L j ρ))
  obtain ⟨C, hC, hcard⟩ := Finset.mem_image.mp hmem
  exact ⟨C, (mem_squareCoverCandidates_iff .free L j ρ C).mp hC, hcard⟩

/-- A family of densities pairwise farther than `s`. -/
def IsSeparatedFamily (s : ℝ) (𝒜 : Finset (ChargeDensity L)) : Prop :=
  ∀ b ∈ 𝒜, ∀ b' ∈ 𝒜, b ≠ b' → s < euclideanSetDistance (chargeSupport b) (chargeSupport b')

/-- **Densities near a square.** -/
theorem card_near_square_le {𝒜 : Finset (ChargeDensity L)} {s : ℝ} (hs : 0 < s)
    (hsep : IsSeparatedFamily s 𝒜) {i : ℕ} {Q : Finset (Site L)}
    (hQ : Q ∈ kpSquares .free L i) {R : ℝ} :
    ((𝒜.filter fun b => ∃ y ∈ chargeSupport b, ∃ q ∈ Q, euclideanSiteDistance y q ≤ R).card : ℝ)
      ≤ (4 * ((2 : ℝ) ^ i + R) / s + 2) ^ 2 := by
  classical
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hQ
  set P : ChargeDensity L → Prop :=
    fun b => ∃ y ∈ chargeSupport b, ∃ q ∈ kpSquare .free L i a, euclideanSiteDistance y q ≤ R
  let y : ChargeDensity L → Site L := fun b => if h : P b then h.choose else a
  have hy : ∀ b, P b → y b ∈ chargeSupport b ∧
      ∃ q ∈ kpSquare .free L i a, euclideanSiteDistance (y b) q ≤ R := by
    intro b hb
    simp only [y, dite_eq_left hb]
    exact hb.choose_spec
  refine card_le_of_separated y hs ((a.1.val : ℝ), (a.2.val : ℝ)) (fun b hb => ?_)
    (fun b hb b' hb' hne => ?_)
  · obtain ⟨-, q, hq, hdq⟩ := hy b (Finset.mem_filter.mp hb).2
    have ha := anchor_mem_kpSquare .free L i a
    obtain ⟨h1, h2⟩ := abs_sub_lt_of_mem_kpSquare hq ha
    have e1 := abs_fst_le_siteDist (y b) q
    have e2 := abs_snd_le_siteDist (y b) q
    have t1 := abs_sub_le ((y b).1.val : ℝ) (q.1.val : ℝ) (a.1.val : ℝ)
    have t2 := abs_sub_le ((y b).2.val : ℝ) (q.2.val : ℝ) (a.2.val : ℝ)
    constructor <;> simp only <;> linarith
  · have h1 := (hy b (Finset.mem_filter.mp hb).2).1
    have h2 := (hy b' (Finset.mem_filter.mp hb').2).1
    exact (hsep b (Finset.mem_filter.mp hb).1 b' (Finset.mem_filter.mp hb').1 hne).trans_le
      (setDist_le_siteDist h1 h2)

/-- The square bound `(4(2^i + R)/s + 2)² ≤ (4(2s + R)/s + 2)²` for `2^i ≤ 2s`. -/
theorem near_bound_le {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) {i : ℕ} (hi : (2 : ℝ) ^ i ≤ 2 * s) :
    (4 * ((2 : ℝ) ^ i + R) / s + 2) ^ 2 ≤ (4 * (2 * s + R) / s + 2) ^ 2 := by
  apply pow_le_pow_left₀ (by positivity)
  have : 4 * ((2 : ℝ) ^ i + R) / s ≤ 4 * (2 * s + R) / s :=
    div_le_div_of_nonneg_right (by linarith) hs.le
  linarith

/-- **Neighbours.** In a separated family of nonzero densities, the members within `2s` of one
member `b` number at most `324 · A_i(b)` when `2^i ≤ 2s`. -/
theorem card_neighbors_le {𝒜 : Finset (ChargeDensity L)} {s : ℝ} (hs : 0 < s)
    (hsep : IsSeparatedFamily s 𝒜) (h𝒜 : ∀ b ∈ 𝒜, b ≠ 0) {b : ChargeDensity L} (hb : b ≠ 0)
    {i : ℕ} (hi : (2 : ℝ) ^ i ≤ 2 * s) :
    ((𝒜.filter fun b' => b' ≠ b ∧
        euclideanSetDistance (chargeSupport b) (chargeSupport b') ≤ 2 * s).card : ℝ) ≤
      324 * squareCoverNumber .free L i b := by
  classical
  obtain ⟨C, hC, hCcard⟩ := exists_minCover i b
  have hsub : (𝒜.filter fun b' => b' ≠ b ∧
      euclideanSetDistance (chargeSupport b) (chargeSupport b') ≤ 2 * s) ⊆
      C.biUnion fun Q => 𝒜.filter fun b' =>
        ∃ y ∈ chargeSupport b', ∃ q ∈ Q, euclideanSiteDistance y q ≤ 2 * s := by
    intro b' hb'
    obtain ⟨hb'𝒜, -, hd⟩ := Finset.mem_filter.mp hb'
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_setDist_eq (chargeSupport_nonempty_of_ne_zero b hb)
      (chargeSupport_nonempty_of_ne_zero b' (h𝒜 b' hb'𝒜))
    obtain ⟨Q, hQ, hxQ⟩ := hC.2 x hx
    refine Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_filter.mpr ⟨hb'𝒜, y, hy, x, hxQ, ?_⟩⟩
    rw [siteDist_comm, ← hxy]
    exact hd
  have hQ : ∀ Q ∈ C, ((𝒜.filter fun b' =>
      ∃ y ∈ chargeSupport b', ∃ q ∈ Q, euclideanSiteDistance y q ≤ 2 * s).card : ℝ) ≤ 324 := by
    intro Q hQC
    refine (card_near_square_le hs hsep (hC.1 hQC)).trans ((near_bound_le hs (by linarith) hi).trans
      (le_of_eq ?_))
    field_simp
    norm_num
  calc ((𝒜.filter fun b' => b' ≠ b ∧
        euclideanSetDistance (chargeSupport b) (chargeSupport b') ≤ 2 * s).card : ℝ)
      ≤ ((C.biUnion fun Q => 𝒜.filter fun b' =>
        ∃ y ∈ chargeSupport b', ∃ q ∈ Q, euclideanSiteDistance y q ≤ 2 * s).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ Q ∈ C, ((𝒜.filter fun b' =>
        ∃ y ∈ chargeSupport b', ∃ q ∈ Q, euclideanSiteDistance y q ≤ 2 * s).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _Q ∈ C, (324 : ℝ) := Finset.sum_le_sum hQ
    _ = 324 * squareCoverNumber .free L i b := by
        rw [Finset.sum_const, nsmul_eq_mul, hCcard, mul_comm]

/-- **Cover sums over a decomposition.** If the support of `a` is the union of the supports of the
parts `b ∈ P`, and each scale-`i` square meets at most `m` parts, then `∑_b A_i(b) ≤ m A_i(a)`. -/
theorem sum_cover_le {P : Finset (ChargeDensity L)} {a : ChargeDensity L}
    (hsupp : chargeSupport a = P.biUnion chargeSupport) {i m : ℕ}
    (hm : ∀ Q ∈ kpSquares .free L i, (P.filter fun b => (Q ∩ chargeSupport b).Nonempty).card ≤ m) :
    ∑ b ∈ P, squareCoverNumber .free L i b ≤ m * squareCoverNumber .free L i a := by
  classical
  obtain ⟨C, hC, hCcard⟩ := exists_minCover i a
  have hcov : ∀ b ∈ P, squareCoverNumber .free L i b ≤
      (C.filter fun Q => (Q ∩ chargeSupport b).Nonempty).card := by
    intro b hb
    refine squareCoverNumber_le .free L i b _ ⟨fun Q hQ => hC.1 (Finset.mem_filter.mp hQ).1,
      fun x hx => ?_⟩
    have hxa : x ∈ chargeSupport a := hsupp ▸ Finset.mem_biUnion.mpr ⟨b, hb, hx⟩
    obtain ⟨Q, hQ, hxQ⟩ := hC.2 x hxa
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, x, Finset.mem_inter.mpr ⟨hxQ, hx⟩⟩, hxQ⟩
  calc ∑ b ∈ P, squareCoverNumber .free L i b
      ≤ ∑ b ∈ P, (C.filter fun Q => (Q ∩ chargeSupport b).Nonempty).card :=
        Finset.sum_le_sum hcov
    _ = ∑ Q ∈ C, (P.filter fun b => (Q ∩ chargeSupport b).Nonempty).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _Q ∈ C, m := Finset.sum_le_sum fun Q hQ => hm Q (hC.1 hQ)
    _ = m * squareCoverNumber .free L i a := by
        rw [Finset.sum_const, smul_eq_mul, hCcard, mul_comm]

/-- Squares of side `2^i ≤ 2s` meet at most `100` members of a separated family. -/
theorem card_meet_le_100 {𝒜 : Finset (ChargeDensity L)} {s : ℝ} (hs : 0 < s)
    (hsep : IsSeparatedFamily s 𝒜) {i : ℕ} (hi : (2 : ℝ) ^ i ≤ 2 * s) {Q : Finset (Site L)}
    (hQ : Q ∈ kpSquares .free L i) :
    (𝒜.filter fun b => (Q ∩ chargeSupport b).Nonempty).card ≤ 100 := by
  classical
  have hsub : (𝒜.filter fun b => (Q ∩ chargeSupport b).Nonempty) ⊆
      𝒜.filter fun b => ∃ y ∈ chargeSupport b, ∃ q ∈ Q, euclideanSiteDistance y q ≤ 0 := by
    intro b hb
    obtain ⟨hb𝒜, x, hx⟩ := Finset.mem_filter.mp hb
    obtain ⟨hxQ, hxb⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_filter.mpr ⟨hb𝒜, x, hxb, x, hxQ, by rw [siteDist_self]⟩
  have h := (card_near_square_le (R := 0) hs hsep hQ).trans (near_bound_le hs le_rfl hi)
  have h100 : (4 * (2 * s + 0) / s + 2) ^ 2 = (100 : ℝ) := by
    field_simp
    ring
  have : ((𝒜.filter fun b => (Q ∩ chargeSupport b).Nonempty).card : ℝ) ≤ 100 :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (h.trans h100.le)
  exact_mod_cast this

/-- Squares of side `2^i` with `2^{i+1} ≤ s` meet at most one member of a separated family. -/
theorem card_meet_le_one {𝒜 : Finset (ChargeDensity L)} {s : ℝ}
    (hsep : IsSeparatedFamily s 𝒜) {i : ℕ} (hi : 2 * (2 : ℝ) ^ i ≤ s) {Q : Finset (Site L)}
    (hQ : Q ∈ kpSquares .free L i) :
    (𝒜.filter fun b => (Q ∩ chargeSupport b).Nonempty).card ≤ 1 := by
  classical
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hQ
  rw [Finset.card_le_one]
  intro b hb b' hb'
  by_contra hne
  obtain ⟨hb𝒜, x, hx⟩ := Finset.mem_filter.mp hb
  obtain ⟨hb'𝒜, x', hx'⟩ := Finset.mem_filter.mp hb'
  obtain ⟨hxQ, hxb⟩ := Finset.mem_inter.mp hx
  obtain ⟨hx'Q, hx'b⟩ := Finset.mem_inter.mp hx'
  have hd := (hsep b hb𝒜 b' hb'𝒜 hne).trans_le (setDist_le_siteDist hxb hx'b)
  obtain ⟨h1, h2⟩ := abs_sub_lt_of_mem_kpSquare hxQ hx'Q
  have hpos : (0 : ℝ) < 2 ^ i := by positivity
  have hd2 : euclideanSiteDistance x x' < s := by
    unfold euclideanSiteDistance
    rw [Real.sqrt_lt' (by linarith)]
    have e1 : ((x.1.val : ℝ) - x'.1.val) ^ 2 < (2 ^ i) ^ 2 := by
      have := abs_lt.mp h1
      nlinarith
    have e2 : ((x.2.val : ℝ) - x'.2.val) ^ 2 < (2 ^ i) ^ 2 := by
      have := abs_lt.mp h2
      nlinarith
    nlinarith
  linarith

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
