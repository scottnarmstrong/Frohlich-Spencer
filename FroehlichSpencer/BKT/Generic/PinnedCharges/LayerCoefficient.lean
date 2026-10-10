/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerPacking

/-!
Along a selection run from a comb start, every density carries a keep count `κ` with
`3|K(ρ)| ≤ 12^{‖ρ‖₁} 3^{κ(ρ)}` (leaves: `3 K_q ≤ 12^q`; merges multiply; a keep adds one).

The
keep count is controlled by a potential: during one base scale, with the actives at its start as
atoms, `κ(a) + Φ(a) ≤ ∑_{b ⊆ a} (κ(b) + Φ₀(b))` where `Φ` counts actives within `2s`; a keep
trades one unit of `Φ` for one of `κ`, and merges and drops never raise `Φ`.

Packing
(`LayerPacking`) turns the atom sums into cover numbers, which gives at the end of each scale
`κ ≤ C₀ ∑_{i < j} A_i + C₁ A_j` (`atomBound`), and for  densities
`κ ≤ (C₀ + C₁) ∑_{i ≤ n_Λ} A_i`.

`combCoefficientBound`: `CombCoefficientBound (log 12) ((C₀ + C₁) log 3)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The constant of the top-scale term. -/
def coefC₁ : ℕ := 32400

/-- The constant of the lower-scale terms: `C₀ = 100 (C₁ + 324)`. -/
def coefC₀ : ℕ := 3272400

/-- The integer mass `‖ρ‖₁`. -/
def nrm (ρ : ChargeDensity L) : ℕ := ∑ x, (ρ x).natAbs

/-- The keep budget of a density at the start of scale index `j`. -/
def atomBound (j : ℕ) (b : ChargeDensity L) : ℕ :=
  if j = 0 then 0 else
    coefC₀ * ∑ i ∈ Finset.range (j - 1), squareCoverNumber .free L i b +
      coefC₁ * squareCoverNumber .free L (j - 1) b

/-- The number of members of `𝒜` within `2s` of `a`. -/
def nbr (s : ℝ) (𝒜 : Finset (ChargeDensity L)) (a : ChargeDensity L) : ℕ :=
  (𝒜.filter fun σ => σ ≠ a ∧
    euclideanSetDistance (chargeSupport a) (chargeSupport σ) ≤ 2 * s).card

/-- Keep counts and the current scale's atoms. -/
structure CoeffData (L : ℕ) where
  κ : ChargeDensity L → ℕ
  κ₀ : ChargeDensity L → ℕ
  A₀ : Finset (ChargeDensity L)
  At : ChargeDensity L → Finset (ChargeDensity L)

/-- The coefficient invariant. -/
def CoeffInv (S : SelConfig L) (D : CoeffData L) : Prop :=
  (∀ ρ ∈ S.A ∪ S.F, 3 * |S.K ρ| ≤ (12 : ℝ) ^ nrm ρ * 3 ^ D.κ ρ) ∧
  (∀ ρ ∈ S.F, D.κ ρ ≤ (coefC₀ + coefC₁) *
    ∑ i ∈ Finset.range (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1),
      squareCoverNumber .free L i ρ) ∧
  (∀ b ∈ D.A₀, b ≠ 0) ∧ IsSeparatedFamily S.scale D.A₀ ∧
  (∀ b ∈ D.A₀, D.κ₀ b ≤ atomBound S.j b) ∧
  (∀ a ∈ S.A, D.At a ⊆ D.A₀ ∧ chargeSupport a = (D.At a).biUnion chargeSupport) ∧
  (∀ a ∈ S.A, ∀ a' ∈ S.A, a ≠ a' → Disjoint (D.At a) (D.At a')) ∧
  (∀ a ∈ S.A, D.κ a + nbr S.scale S.A a ≤ ∑ b ∈ D.At a, (D.κ₀ b + nbr S.scale D.A₀ b))

/-! ### Elementary facts -/

theorem natAbs_add_of_zero {u v : ℤ} (h : u = 0 ∨ v = 0) :
    (u + v).natAbs = u.natAbs + v.natAbs := by
  rcases h with rfl | rfl <;> simp

theorem natAbs_sub_of_zero {u v : ℤ} (h : u = 0 ∨ v = 0) :
    (u - v).natAbs = u.natAbs + v.natAbs := by
  rcases h with rfl | rfl <;> simp

theorem zero_or_zero_of_disjoint {a c : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport c)) (x : Site L) : a x = 0 ∨ c x = 0 := by
  by_contra h
  push Not at h
  have ha : x ∈ chargeSupport a := by simp [chargeSupport, h.1]
  have hc : x ∈ chargeSupport c := by simp [chargeSupport, h.2]
  exact Finset.disjoint_left.mp hdisj ha hc

theorem nrm_add {a c : ChargeDensity L} (hdisj : Disjoint (chargeSupport a) (chargeSupport c)) :
    nrm (a + c) = nrm a + nrm c := by
  unfold nrm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => natAbs_add_of_zero (zero_or_zero_of_disjoint hdisj x)

theorem nrm_sub {a c : ChargeDensity L} (hdisj : Disjoint (chargeSupport a) (chargeSupport c)) :
    nrm (a - c) = nrm a + nrm c := by
  unfold nrm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => natAbs_sub_of_zero (zero_or_zero_of_disjoint hdisj x)

theorem nbr_mono {s : ℝ} {𝒜 ℬ : Finset (ChargeDensity L)} (h : 𝒜 ⊆ ℬ) (a : ChargeDensity L) :
    nbr s 𝒜 a ≤ nbr s ℬ a :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Removing a neighbour lowers the count. -/
theorem nbr_erase_lt {s : ℝ} {𝒜 : Finset (ChargeDensity L)} {a c : ChargeDensity L}
    (hc : c ∈ 𝒜) (hne : c ≠ a)
    (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s) :
    nbr s (𝒜.erase c) a < nbr s 𝒜 a := by
  unfold nbr
  rw [Finset.filter_erase]
  exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨hc, hne, hD⟩)

/-! ### Keeps -/

/-- **Keep step.** Keeping `a` and dropping its neighbour `c` adds one to `κ(a)`. -/
theorem coeffInv_keep {S : SelConfig L} {D : CoeffData L}
    (hv : S.Valid (chargeCoverScale : ℝ) chargeCoverExponent) (h : CoeffInv S D)
    {a c : ChargeDensity L} (ha : a ∈ S.A) (hc : c ∈ S.A) (hne : a ≠ c)
    (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale) :
    CoeffInv ⟨S.j, S.A.erase c, S.F, pairRewriteFirstCoefficient S.K a⟩
      ⟨Function.update D.κ a (D.κ a + 1), D.κ₀, D.A₀, D.At⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have haF : a ∉ S.F := fun h' => Finset.disjoint_left.mp hv.disjoint ha h'
  have hsub : ∀ {ρ}, ρ ∈ S.A.erase c ∪ S.F → ρ ∈ S.A ∪ S.F := fun hρ =>
    Finset.union_subset_union (Finset.erase_subset _ _) subset_rfl hρ
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_, h3, h4, h5, fun x hx => h6 x (Finset.mem_of_mem_erase hx),
    fun x hx y hy hxy => h7 x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy,
    fun x hx => ?_⟩
  · by_cases hρa : ρ = a
    · subst hρa
      have hb := h1 ρ (hsub hρ)
      simp only [pairRewriteFirstCoefficient, ite_true, Function.update_self, pow_succ, abs_mul]
      have : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
      rw [this]
      nlinarith
    · simp only [pairRewriteFirstCoefficient, hρa, ite_false, Function.update_of_ne hρa]
      exact h1 ρ (hsub hρ)
  · have hρa : ρ ≠ a := fun e => haF (e ▸ hρ)
    simp only [Function.update_of_ne hρa]
    exact h2 ρ hρ
  · have hxA := Finset.mem_of_mem_erase hx
    have hb := h8 x hxA
    by_cases hxa : x = a
    · subst hxa
      simp only [Function.update_self]
      have hlt := nbr_erase_lt (s := S.scale) hc (Ne.symm hne) hD
      change D.κ x + 1 + nbr S.scale (S.A.erase c) x ≤
        ∑ b ∈ D.At x, (D.κ₀ b + nbr S.scale D.A₀ b)
      omega
    · simp only [Function.update_of_ne hxa]
      have := nbr_mono (s := S.scale) (Finset.erase_subset c S.A) x
      change D.κ x + nbr S.scale (S.A.erase c) x ≤
        ∑ b ∈ D.At x, (D.κ₀ b + nbr S.scale D.A₀ b)
      omega

/-! ### Merges -/

theorem near_union {a c σ : ChargeDensity L} (ha : (chargeSupport a).Nonempty)
    (hσ : (chargeSupport σ).Nonempty) {r : ℝ}
    (h : euclideanSetDistance (chargeSupport a ∪ chargeSupport c) (chargeSupport σ) ≤ r) :
    euclideanSetDistance (chargeSupport a) (chargeSupport σ) ≤ r ∨
      euclideanSetDistance (chargeSupport c) (chargeSupport σ) ≤ r :=
  min_le_iff.mp ((min_le_setDist_union ha hσ).trans h)

theorem nbr_insert_le_of_near {s : ℝ} {A R : Finset (ChargeDensity L)} {τ a' d : ChargeDensity L}
    (hR : R ⊆ A) (hd : d ∈ A) (hdR : d ∉ R) (hda' : d ≠ a')
    (hdnear : euclideanSetDistance (chargeSupport a') (chargeSupport d) ≤ 2 * s) :
    nbr s (insert τ R) a' ≤ nbr s A a' := by
  classical
  unfold nbr
  calc ((insert τ R).filter fun σ => σ ≠ a' ∧
        euclideanSetDistance (chargeSupport a') (chargeSupport σ) ≤ 2 * s).card
      ≤ (insert τ (R.filter fun σ => σ ≠ a' ∧
        euclideanSetDistance (chargeSupport a') (chargeSupport σ) ≤ 2 * s)).card := by
        refine Finset.card_le_card fun σ hσ => ?_
        obtain ⟨hσ1, hσ2⟩ := Finset.mem_filter.mp hσ
        rcases Finset.mem_insert.mp hσ1 with rfl | hσR
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hσR, hσ2⟩)
    _ ≤ (R.filter fun σ => σ ≠ a' ∧
        euclideanSetDistance (chargeSupport a') (chargeSupport σ) ≤ 2 * s).card + 1 :=
        Finset.card_insert_le _ _
    _ = (insert d (R.filter fun σ => σ ≠ a' ∧
        euclideanSetDistance (chargeSupport a') (chargeSupport σ) ≤ 2 * s)).card :=
        (Finset.card_insert_of_notMem fun h => hdR (Finset.mem_filter.mp h).1).symm
    _ ≤ (A.filter fun σ => σ ≠ a' ∧
        euclideanSetDistance (chargeSupport a') (chargeSupport σ) ≤ 2 * s).card :=
        Finset.card_le_card (Finset.insert_subset (Finset.mem_filter.mpr ⟨hd, hda', hdnear⟩)
          (Finset.filter_subset_filter _ hR))

theorem nbr_insert_le_of_far {s : ℝ} {A R : Finset (ChargeDensity L)} {τ a' : ChargeDensity L}
    (hR : R ⊆ A)
    (hfar : ¬ euclideanSetDistance (chargeSupport a') (chargeSupport τ) ≤ 2 * s) :
    nbr s (insert τ R) a' ≤ nbr s A a' := by
  classical
  unfold nbr
  refine Finset.card_le_card fun σ hσ => ?_
  obtain ⟨hσ1, hσ2⟩ := Finset.mem_filter.mp hσ
  rcases Finset.mem_insert.mp hσ1 with rfl | hσR
  · exact absurd hσ2.2 hfar
  · exact Finset.mem_filter.mpr ⟨hR hσR, hσ2⟩

/-- **Merge step.** Replacing `a, c` by `τ` (support `supp a ∪ supp c`, mass `‖a‖ + ‖c‖`) with
`K(τ) = 3K(a)K(c)` adds the keep counts and the atom sets. -/
theorem coeffInv_merge {S : SelConfig L} {D : CoeffData L}
    (hv : S.Valid (chargeCoverScale : ℝ) chargeCoverExponent) (h : CoeffInv S D)
    {a c τ : ChargeDensity L} (ha : a ∈ S.A) (hc : c ∈ S.A) (hne : a ≠ c)
    (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale)
    (hsupp : chargeSupport τ = chargeSupport a ∪ chargeSupport c)
    (hnrm : nrm τ = nrm a + nrm c) (hnew : τ ∉ (S.A.erase a).erase c ∪ S.F) :
    CoeffInv ⟨S.j, insert τ ((S.A.erase a).erase c), S.F,
        fun ρ => if ρ = τ then 3 * S.K a * S.K c else S.K ρ⟩
      ⟨Function.update D.κ τ (D.κ a + D.κ c), D.κ₀, D.A₀,
        Function.update D.At τ (D.At a ∪ D.At c)⟩ := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  set R := (S.A.erase a).erase c with hRdef
  have hRA : R ⊆ S.A := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hold : ∀ {σ}, σ ∈ R → σ ∈ S.A ∧ σ ≠ a ∧ σ ≠ c := by
    intro σ hσ
    obtain ⟨hσc, hσ'⟩ := Finset.mem_erase.mp hσ
    obtain ⟨hσa, hσA⟩ := Finset.mem_erase.mp hσ'
    exact ⟨hσA, hσa, hσc⟩
  have hτR : τ ∉ R := fun h' => hnew (Finset.mem_union_left _ h')
  have hτF : τ ∉ S.F := fun h' => hnew (Finset.mem_union_right _ h')
  have hU : ∀ {ρ}, ρ ∈ insert τ R ∪ S.F → ρ ≠ τ → ρ ∈ S.A ∪ S.F := by
    intro ρ hρ hρτ
    rcases Finset.mem_union.mp hρ with hρ | hρ
    · rcases Finset.mem_insert.mp hρ with rfl | hρ
      · exact absurd rfl hρτ
      · exact Finset.mem_union_left _ (hRA hρ)
    · exact Finset.mem_union_right _ hρ
  have hne0 : ∀ {σ}, σ ∈ S.A → (chargeSupport σ).Nonempty := fun hσ =>
    chargeSupport_nonempty_of_ne_zero _ (hv.ne_zero (Finset.mem_union_left _ hσ))
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_, h3, h4, h5, fun x hx => ?_, fun x hx y hy hxy => ?_,
    fun x hx => ?_⟩
  · by_cases hρτ : ρ = τ
    · subst hρτ
      simp only [ite_true, Function.update_self]
      rw [hnrm, pow_add, pow_add]
      have ha1 := h1 a (Finset.mem_union_left _ ha)
      have hc1 := h1 c (Finset.mem_union_left _ hc)
      have e : 3 * |3 * S.K a * S.K c| = (3 * |S.K a|) * (3 * |S.K c|) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        ring
      rw [e]
      calc (3 * |S.K a|) * (3 * |S.K c|)
          ≤ ((12 : ℝ) ^ nrm a * 3 ^ D.κ a) * ((12 : ℝ) ^ nrm c * 3 ^ D.κ c) :=
            mul_le_mul ha1 hc1 (by positivity) (by positivity)
        _ = (12 : ℝ) ^ nrm a * 12 ^ nrm c * (3 ^ D.κ a * 3 ^ D.κ c) := by ring
    · simp only [hρτ, ite_false, Function.update_of_ne hρτ]
      exact h1 ρ (hU hρ hρτ)
  · have hρτ : ρ ≠ τ := fun e => hτF (e ▸ hρ)
    simp only [Function.update_of_ne hρτ]
    exact h2 ρ hρ
  · rcases Finset.mem_insert.mp hx with rfl | hxR
    · simp only [Function.update_self]
      refine ⟨Finset.union_subset (h6 a ha).1 (h6 c hc).1, ?_⟩
      rw [hsupp, Finset.union_biUnion, ← (h6 a ha).2, ← (h6 c hc).2]
    · have hxτ : x ≠ τ := fun e => hτR (e ▸ hxR)
      simp only [Function.update_of_ne hxτ]
      exact h6 x (hRA hxR)
  · rcases Finset.mem_insert.mp hx with rfl | hxR <;> rcases Finset.mem_insert.mp hy with rfl | hyR
    · exact absurd rfl hxy
    · obtain ⟨hyA, hya, hyc⟩ := hold hyR
      have hyτ : y ≠ x := fun e => hτR (e ▸ hyR)
      simp only [Function.update_self, Function.update_of_ne hyτ]
      exact Finset.disjoint_union_left.mpr ⟨h7 a ha y hyA (Ne.symm hya), h7 c hc y hyA (Ne.symm hyc)⟩
    · obtain ⟨hxA, hxa, hxc⟩ := hold hxR
      have hxτ : x ≠ y := fun e => hτR (e ▸ hxR)
      simp only [Function.update_self, Function.update_of_ne hxτ]
      exact Finset.disjoint_union_right.mpr ⟨h7 x hxA a ha hxa, h7 x hxA c hc hxc⟩
    · have hxτ : x ≠ τ := fun e => hτR (e ▸ hxR)
      have hyτ : y ≠ τ := fun e => hτR (e ▸ hyR)
      simp only [Function.update_of_ne hxτ, Function.update_of_ne hyτ]
      exact h7 x (hRA hxR) y (hRA hyR) hxy
  · rcases Finset.mem_insert.mp hx with rfl | hxR
    · -- the merged density
      simp only [Function.update_self]
      rw [Finset.sum_union (h7 a ha c hc hne)]
      have hca : c ∈ S.A.filter fun σ => σ ≠ a ∧
          euclideanSetDistance (chargeSupport a) (chargeSupport σ) ≤ 2 * S.scale :=
        Finset.mem_filter.mpr ⟨hc, Ne.symm hne, hD⟩
      have hac : a ∈ S.A.filter fun σ => σ ≠ c ∧
          euclideanSetDistance (chargeSupport c) (chargeSupport σ) ≤ 2 * S.scale :=
        Finset.mem_filter.mpr ⟨ha, hne, by rw [setDist_comm]; exact hD⟩
      have hsub : ((insert x R).filter fun σ => σ ≠ x ∧
          euclideanSetDistance (chargeSupport x) (chargeSupport σ) ≤ 2 * S.scale) ⊆
          ((S.A.filter fun σ => σ ≠ a ∧
            euclideanSetDistance (chargeSupport a) (chargeSupport σ) ≤ 2 * S.scale).erase c) ∪
          ((S.A.filter fun σ => σ ≠ c ∧
            euclideanSetDistance (chargeSupport c) (chargeSupport σ) ≤ 2 * S.scale).erase a) := by
        intro σ hσ
        obtain ⟨hσ1, hσx, hσd⟩ := Finset.mem_filter.mp hσ
        have hσR : σ ∈ R := by
          rcases Finset.mem_insert.mp hσ1 with rfl | h'
          · exact absurd rfl hσx
          · exact h'
        obtain ⟨hσA, hσa, hσc⟩ := hold hσR
        rw [hsupp] at hσd
        rcases near_union (hne0 ha) (hne0 hσA) hσd with hn | hn
        · exact Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hσc, Finset.mem_filter.mpr ⟨hσA, hσa, hn⟩⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨hσa, Finset.mem_filter.mpr ⟨hσA, hσc, hn⟩⟩)
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_erase_of_mem hca, Finset.card_erase_of_mem hac] at hcard
      have hpa : 1 ≤ nbr S.scale S.A a := Finset.card_pos.mpr ⟨c, hca⟩
      have hpc : 1 ≤ nbr S.scale S.A c := Finset.card_pos.mpr ⟨a, hac⟩
      have ha8 := h8 a ha
      have hc8 := h8 c hc
      change D.κ a + D.κ c + nbr S.scale (insert x R) x ≤
        ∑ b ∈ D.At a, (D.κ₀ b + nbr S.scale D.A₀ b) + ∑ b ∈ D.At c, (D.κ₀ b + nbr S.scale D.A₀ b)
      unfold nbr at ha8 hc8 hpa hpc ⊢
      omega
    · -- an old density
      obtain ⟨hxA, hxa, hxc⟩ := hold hxR
      have hxτ : x ≠ τ := fun e => hτR (e ▸ hxR)
      simp only [Function.update_of_ne hxτ]
      have hle : nbr S.scale (insert τ R) x ≤ nbr S.scale S.A x := by
        by_cases hnear : euclideanSetDistance (chargeSupport x) (chargeSupport τ) ≤ 2 * S.scale
        · have hn' : euclideanSetDistance (chargeSupport a ∪ chargeSupport c) (chargeSupport x) ≤
              2 * S.scale := by rw [setDist_comm, ← hsupp]; exact hnear
          rcases near_union (hne0 ha) (hne0 hxA) hn' with hn | hn
          · exact nbr_insert_le_of_near hRA ha (fun h' => (hold h').2.1 rfl) (Ne.symm hxa)
              (by rw [setDist_comm]; exact hn)
          · exact nbr_insert_le_of_near hRA hc (fun h' => (hold h').2.2 rfl) (Ne.symm hxc)
              (by rw [setDist_comm]; exact hn)
        · exact nbr_insert_le_of_far hRA hnear
      have hx8 := h8 x hxA
      change D.κ x + nbr S.scale (insert τ R) x ≤ ∑ b ∈ D.At x, (D.κ₀ b + nbr S.scale D.A₀ b)
      omega

/-! ### End of a scale -/

theorem two_pow_pred_le (j : ℕ) : (2 : ℝ) ^ (j - 1) ≤ 2 * ((2 : ℝ) ^ j / 2) := by
  rw [mul_div_cancel₀ _ (two_ne_zero)]
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)

theorem two_mul_two_pow_le {i j : ℕ} (hi : i < j - 1) : 2 * (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j / 2 := by
  have hj : j = (j - 1 - 1) + 2 := by omega
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), hj, pow_add]
  have : (2 : ℝ) ^ i ≤ 2 ^ (j - 1 - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) i]

/-- **End-of-scale bound.** At the end of base index `j`, every active has
`κ ≤ C₀ ∑_{i<j} A_i + C₁ A_j`. -/
theorem coeffInv_eos {S : SelConfig L} {D : CoeffData L} (h : CoeffInv S D)
    {a : ChargeDensity L} (ha : a ∈ S.A) : D.κ a ≤ atomBound (S.j + 1) a := by
  classical
  obtain ⟨-, -, h3, h4, h5, h6, -, h8⟩ := h
  obtain ⟨hAt, hsupp⟩ := h6 a ha
  have hs := S.scale_pos
  have hsepAt : IsSeparatedFamily S.scale (D.At a) :=
    fun b hb b' hb' hne => h4 b (hAt hb) b' (hAt hb') hne
  have hi₀ : (2 : ℝ) ^ (S.j - 1) ≤ 2 * S.scale := two_pow_pred_le S.j
  -- neighbour sums
  have hnb : ∀ b ∈ D.At a, nbr S.scale D.A₀ b ≤ 324 * squareCoverNumber .free L (S.j - 1) b := by
    intro b hb
    have := card_neighbors_le (𝒜 := D.A₀) hs h4 h3 (h3 b (hAt hb)) hi₀
    unfold nbr
    exact_mod_cast this
  have htop : ∑ b ∈ D.At a, squareCoverNumber .free L (S.j - 1) b ≤
      100 * squareCoverNumber .free L (S.j - 1) a :=
    sum_cover_le hsupp fun Q hQ => card_meet_le_100 hs hsepAt hi₀ hQ
  have hsum := h8 a ha
  rw [Finset.sum_add_distrib] at hsum
  have hnbsum : ∑ b ∈ D.At a, nbr S.scale D.A₀ b ≤
      324 * ∑ b ∈ D.At a, squareCoverNumber .free L (S.j - 1) b := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hnb
  have hκ₀ : ∑ b ∈ D.At a, D.κ₀ b ≤ ∑ b ∈ D.At a, atomBound S.j b :=
    Finset.sum_le_sum fun b hb => h5 b (hAt hb)
  by_cases hj : S.j = 0
  · have hz : ∑ b ∈ D.At a, atomBound S.j b = 0 := by simp [atomBound, hj]
    have hab : atomBound (S.j + 1) a = coefC₁ * squareCoverNumber .free L (S.j - 1) a := by
      simp [atomBound, hj]
    rw [hab]
    unfold coefC₁
    omega
  · -- lower scales are additive, the top scale loses a factor 100
    have hlow : ∀ i ∈ Finset.range (S.j - 1),
        ∑ b ∈ D.At a, squareCoverNumber .free L i b ≤ squareCoverNumber .free L i a := by
      intro i hi
      have := sum_cover_le (m := 1) hsupp fun Q hQ =>
        card_meet_le_one hsepAt (two_mul_two_pow_le (Finset.mem_range.mp hi)) hQ
      simpa using this
    have hab : ∑ b ∈ D.At a, atomBound S.j b ≤
        coefC₀ * ∑ i ∈ Finset.range (S.j - 1), squareCoverNumber .free L i a +
          coefC₁ * (100 * squareCoverNumber .free L (S.j - 1) a) := by
      simp only [atomBound, hj, ite_false]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (Finset.sum_le_sum hlow))
        (Nat.mul_le_mul_left _ htop)
    have hsplit : ∑ i ∈ Finset.range S.j, squareCoverNumber .free L i a =
        ∑ i ∈ Finset.range (S.j - 1), squareCoverNumber .free L i a +
          squareCoverNumber .free L (S.j - 1) a := by
      conv_lhs => rw [show S.j = S.j - 1 + 1 by omega]
      rw [Finset.sum_range_succ]
    have hab' : atomBound (S.j + 1) a = coefC₀ * ∑ i ∈ Finset.range S.j,
        squareCoverNumber .free L i a + coefC₁ * squareCoverNumber .free L S.j a := by
      simp [atomBound]
    rw [hab', hsplit]
    unfold coefC₀ coefC₁ at hab ⊢
    nlinarith

/-! ### Freezing, the start, and reachability -/

/-- A density active at base index `j` has `j ≤ n_Λ`. -/
theorem le_cutoff_of_active {S : SelConfig L}
    (hv : S.Valid (chargeCoverScale : ℝ) chargeCoverExponent) {ρ : ChargeDensity L}
    (hρ : ρ ∈ S.A) :
    S.j ≤ boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ := by
  have hlt := SelectionState.lt_mul_rpow one_lt_chargeCoverScale one_le_chargeCoverExponent
    S.scale_pos hv hρ
  set X := (chargeCoverScale : ℝ) * boundaryAdjustedSize ρ ^ chargeCoverExponent
  have hX : 0 < X := S.scale_pos.trans hlt
  have hlog : (S.j : ℝ) - 1 < Real.logb 2 X := by
    have h1 : Real.logb 2 S.scale = (S.j : ℝ) - 1 := by
      unfold SelConfig.scale
      rw [Real.logb_div (by positivity) (by norm_num), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      ring
    rw [← h1]
    exact Real.logb_lt_logb (by norm_num) S.scale_pos hlt
  have hceil := Nat.le_ceil (Real.logb 2 X)
  unfold boundaryChargeCutoff
  have : (S.j : ℝ) < (⌈Real.logb 2 X⌉₊ : ℝ) + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

theorem atomBound_le_sum (j : ℕ) (ρ : ChargeDensity L) {n : ℕ} (hjn : j ≤ n) :
    atomBound (j + 1) ρ ≤ (coefC₀ + coefC₁) *
      ∑ i ∈ Finset.range (n + 1), squareCoverNumber .free L i ρ := by
  have hab : atomBound (j + 1) ρ = coefC₀ * ∑ i ∈ Finset.range j,
      squareCoverNumber .free L i ρ + coefC₁ * squareCoverNumber .free L j ρ := by
    simp [atomBound]
  have h1 : ∑ i ∈ Finset.range j, squareCoverNumber .free L i ρ ≤
      ∑ i ∈ Finset.range (n + 1), squareCoverNumber .free L i ρ :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (show j ≤ n + 1 by omega))
  have h2 : squareCoverNumber .free L j ρ ≤
      ∑ i ∈ Finset.range (n + 1), squareCoverNumber .free L i ρ :=
    Finset.single_le_sum (f := fun i => squareCoverNumber .free L i ρ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (show j < n + 1 by omega))
  rw [hab, add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)

/-- **Freezing step.** The remaining actives become the next scale's atoms. -/
theorem coeffInv_freeze {S : SelConfig L} {D : CoeffData L}
    (hv : S.Valid (chargeCoverScale : ℝ) chargeCoverExponent) (h : CoeffInv S D)
    {J : Finset (ChargeDensity L)}
    (hJ : IsMaximalFreezeSet (chargeCoverScale : ℝ) chargeCoverExponent S.A J)
    (hfar : ∀ ρ ∈ S.A, ∀ σ ∈ S.A, ρ ≠ σ →
      2 * S.scale < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ)) :
    CoeffInv ⟨S.j + 1, S.A \ J, S.F ∪ J, S.K⟩ ⟨D.κ, D.κ, S.A \ J, fun a => {a}⟩ := by
  classical
  have heos := fun {a} (ha : a ∈ S.A) => coeffInv_eos h ha
  obtain ⟨h1, h2, -, -, -, -, -, -⟩ := h
  have hU := sdiff_union_union_eq (F := S.F) hJ.1.1
  have hscale : (⟨S.j + 1, S.A \ J, S.F ∪ J, S.K⟩ : SelConfig L).scale = 2 * S.scale := by
    unfold SelConfig.scale
    rw [pow_succ]
    ring
  refine ⟨fun ρ hρ => h1 ρ (hU ▸ hρ), fun ρ hρ => ?_, fun b hb => ?_, fun b hb b' hb' hne => ?_,
    fun b hb => heos (Finset.mem_sdiff.mp hb).1, fun a ha => ⟨?_, ?_⟩, fun a _ a' _ hne => ?_,
    fun a _ => ?_⟩
  · rcases Finset.mem_union.mp hρ with hρ | hρ
    · exact h2 ρ hρ
    · have hρA := hJ.1.1 hρ
      exact (heos hρA).trans (atomBound_le_sum _ _ (le_cutoff_of_active hv hρA))
  · exact hv.ne_zero (Finset.mem_union_left _ (Finset.mem_sdiff.mp hb).1)
  · rw [hscale]
    exact hfar b (Finset.mem_sdiff.mp hb).1 b' (Finset.mem_sdiff.mp hb').1 hne
  · exact Finset.singleton_subset_iff.mpr ha
  · exact (Finset.singleton_biUnion).symm
  · exact Finset.disjoint_singleton.mpr hne
  · simp

theorem nrm_siteCharge (f : Site L → ℕ) (x : Site L) : nrm (siteCharge f x) = f x := by
  unfold nrm
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [siteCharge_apply, hy]) (by simp)]
  simp [siteCharge_apply]

/-- **The start.** -/
theorem coeffInv_start {N : ℕ} {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) :
    CoeffInv (SelConfig.start (singleSiteEnsemble f) (combActivity N))
      ⟨0, 0, singleSiteEnsemble f, fun a => {a}⟩ := by
  classical
  have hv := SelConfig.start_valid one_lt_chargeCoverScale one_le_chargeCoverExponent
    (singleSiteEnsemble_pinned hf) (singleSiteEnsemble_card_support hf) (combActivity N)
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => by simp [SelConfig.start] at hρ,
    (singleSiteEnsemble_pinned hf).1, hv.separated, fun b _ => by simp [atomBound],
    fun a ha => ⟨Finset.singleton_subset_iff.mpr ha, Finset.singleton_biUnion.symm⟩,
    fun a _ a' _ hne => Finset.disjoint_singleton.mpr hne, fun a _ => by simp [SelConfig.start]⟩
  have hρE : ρ ∈ singleSiteEnsemble f := by simpa [SelConfig.start] using hρ
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hρE
  have hZ : 0 ≤ combNorm N := by
    rw [combNorm_eq]
    have := pow_le_one₀ (n := N) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    linarith
  have hC0 : 0 ≤ combCoeff N (f x) := by unfold combCoeff; positivity
  simp only [SelConfig.start, Pi.zero_apply, pow_zero, mul_one]
  rw [combActivity_siteCharge, nrm_siteCharge, abs_of_nonneg hC0]
  have hq := hf x
  have h1 := combCoeff_le N (f x)
  have h2 : (6 : ℝ) * 2 ^ f x ≤ 12 ^ f x := by
    have : (12 : ℝ) ^ f x = 6 ^ f x * 2 ^ f x := by rw [← mul_pow]; norm_num
    rw [this]
    have : (6 : ℝ) ≤ 6 ^ f x := le_self_pow₀ (by norm_num) (by omega)
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (f x)]
  rw [pow_succ] at h1
  linarith

theorem coeffInv_of_reach {N : ℕ} {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) {T : SelConfig L}
    (hr : SelReach (chargeCoverScale : ℝ) chargeCoverExponent
      (SelConfig.start (singleSiteEnsemble f) (combActivity N)) T) :
    T.Valid (chargeCoverScale : ℝ) chargeCoverExponent ∧ ∃ D : CoeffData L, CoeffInv T D := by
  classical
  induction hr with
  | refl =>
    exact ⟨SelConfig.start_valid one_lt_chargeCoverScale one_le_chargeCoverExponent
      (singleSiteEnsemble_pinned hf) (singleSiteEnsemble_card_support hf) (combActivity N),
      _, coeffInv_start hf⟩
  | tail _ hstep ih =>
    obtain ⟨hv, D, hD⟩ := ih
    refine ⟨hstep.valid one_lt_chargeCoverScale one_le_chargeCoverExponent hv, ?_⟩
    have hmerged : ∀ {S : SelConfig L} {a c τ : ChargeDensity L},
        S.Valid (chargeCoverScale : ℝ) chargeCoverExponent → a ∈ S.A → c ∈ S.A → a ≠ c →
        chargeSupport τ = chargeSupport a ∪ chargeSupport c →
        τ ∉ (S.A.erase a).erase c ∪ S.F := by
      intro S a c τ hv ha hc hne hsupp hτ
      have hτU : τ ∈ S.A ∪ S.F := by
        rcases Finset.mem_union.mp hτ with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h'))
        · exact Finset.mem_union_right _ h'
      have hτa : τ ≠ a := by
        rintro rfl
        rcases Finset.mem_union.mp hτ with h' | h'
        · exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase h')).1 rfl
        · exact Finset.disjoint_left.mp hv.disjoint ha h'
      have hd := hv.disjoint_support hτU (Finset.mem_union_left _ ha) hτa
      obtain ⟨x, hx⟩ := chargeSupport_nonempty_of_ne_zero a (hv.ne_zero (Finset.mem_union_left _ ha))
      have hxτ : x ∈ chargeSupport τ := hsupp ▸ Finset.mem_union_left _ hx
      exact Finset.disjoint_left.mp hd hxτ hx
    cases hstep with
    | keepLeft ha hc hne hD' => exact ⟨_, coeffInv_keep hv hD ha hc hne hD'⟩
    | keepRight ha hc hne hD' =>
      exact ⟨_, coeffInv_keep hv hD hc ha (Ne.symm hne) (by rw [setDist_comm]; exact hD')⟩
    | @mergeSub a c ha hc hne hD' =>
      have hdisj := hv.disjoint_support (Finset.mem_union_left _ ha) (Finset.mem_union_left _ hc) hne
      have hsupp : chargeSupport (a - c) = chargeSupport a ∪ chargeSupport c := by
        have := chargeSupport_add_smul hdisj (Or.inr rfl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1)
        rwa [neg_one_smul, ← sub_eq_add_neg] at this
      exact ⟨_, coeffInv_merge hv hD ha hc hne hD' hsupp (nrm_sub hdisj)
        (hmerged hv ha hc hne hsupp)⟩
    | @mergeAdd a c ha hc hne hD' =>
      have hdisj := hv.disjoint_support (Finset.mem_union_left _ ha) (Finset.mem_union_left _ hc) hne
      have hsupp : chargeSupport (a + c) = chargeSupport a ∪ chargeSupport c :=
        chargeSupport_add hdisj
      exact ⟨_, coeffInv_merge hv hD ha hc hne hD' hsupp (nrm_add hdisj)
        (hmerged hv ha hc hne hsupp)⟩
    | freeze hfar hJ => exact ⟨_, coeffInv_freeze hv hD hJ hfar⟩

/-! ### The coefficient bound -/

theorem cast_natAbs_eq_abs (k : ℤ) : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- **The coefficient bound on comb terminals.** -/
theorem combCoefficientBound :
    CombCoefficientBound (Real.log 12) (((coefC₀ + coefC₁ : ℕ) : ℝ) * Real.log 3) := by
  intro L N T hT ρ hρ
  obtain ⟨-, f, hf, hreach⟩ := hT
  obtain ⟨-, D, h1, h2, -⟩ := coeffInv_of_reach (fun x => (hf x).1) hreach
  have hb := h1 ρ (Finset.mem_union_right _ hρ)
  have hκ := h2 ρ hρ
  set A := ∑ i ∈ Finset.range
    (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1),
    squareCoverNumber .free L i ρ with hAdef
  have hcs : layerCoverSum (neutralizeAtWiredRoot ρ) = (A : ℝ) := by
    unfold layerCoverSum layerCutoff
    rw [siteRestrict_neutralize, hAdef]
    push_cast
    rfl
  have hn : ∑ x, |(ρ x : ℝ)| = (nrm ρ : ℝ) := by
    unfold nrm
    push_cast
    exact Finset.sum_congr rfl fun x _ => (cast_natAbs_eq_abs (ρ x)).symm
  rw [hn, hcs]
  have e12 : Real.exp (Real.log 12 * (nrm ρ : ℝ)) = (12 : ℝ) ^ nrm ρ := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have e3 : Real.exp (((coefC₀ + coefC₁ : ℕ) : ℝ) * Real.log 3 * (A : ℝ)) =
      (3 : ℝ) ^ ((coefC₀ + coefC₁) * A) := by
    rw [show ((coefC₀ + coefC₁ : ℕ) : ℝ) * Real.log 3 * (A : ℝ) =
      (((coefC₀ + coefC₁) * A : ℕ) : ℝ) * Real.log 3 by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, e12, e3]
  calc |T.K ρ| ≤ 3 * |T.K ρ| := by linarith [abs_nonneg (T.K ρ)]
    _ ≤ (12 : ℝ) ^ nrm ρ * 3 ^ D.κ ρ := hb
    _ ≤ (12 : ℝ) ^ nrm ρ * 3 ^ ((coefC₀ + coefC₁) * A) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hκ) (by positivity)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
