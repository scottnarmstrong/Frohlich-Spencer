/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGGeometry

/-!
At base scale `s`, merging two active densities `a, c` at distance `s < D ≤ 2s` (FS81 (2.13), branch
`a ± c`) preserves boundary isolation and `2s`-connectivity, provided both operands are
boundary-isolated, `2s`-connected and satisfy the scale witness `d(·) < s ⇒ s < M d_Λ(·)^α`.

This is the cut-to-history step of Appendix D.

A constituent separated from its complement by
`2M d^α` cannot be split between two operands merged at the current scale (`not_meets_both`), so
the first crossing of its cut is a merge of a whole operand, and that operand's witness bounds the
crossing distance by `2M δ^α` (`isolated_add_of_subset`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

open FroehlichSpencer.BKT

variable {L : ℕ}

/-- The Appendix D isolation clause for a single density (`HasBoundaryIsolation` is this clause for
every member of an ensemble). -/
def IsIsolated (M α : ℝ) (ρ : ChargeDensity L) : Prop :=
  ∀ ρ₁, IsConstituent ρ ρ₁ →
    2 * M * chargeEuclideanDiameter ρ₁ ^ α ≤
      euclideanSetDistance (chargeSupport ρ₁) (chargeSupport (fun x => ρ x - ρ₁ x)) →
    totalCharge ρ₁ ≠ 0 ∧
      euclideanSetDistance (chargeSupport ρ₁) (chargeSupport (fun x => ρ x - ρ₁ x)) ≤
        2 * M * chargeBoundaryDistance ρ₁ ^ α

theorem hasBoundaryIsolation_iff {M α : ℝ} {N : Finset (ChargeDensity L)} :
    HasBoundaryIsolation M α N ↔ ∀ ρ ∈ N, IsIsolated M α ρ :=
  Iff.rfl

/-- Every proper cut of the support is crossed at distance at most `r`. -/
def IsScaleConnected (r : ℝ) (ρ : ChargeDensity L) : Prop :=
  ∀ S ⊆ chargeSupport ρ, S.Nonempty → (chargeSupport ρ \ S).Nonempty →
    euclideanSetDistance S (chargeSupport ρ \ S) ≤ r

/-- The scale witness: a density of diameter below `s` has `s < M d_Λ^α`. -/
def HasScaleWitness (M α s : ℝ) (ρ : ChargeDensity L) : Prop :=
  chargeEuclideanDiameter ρ < s → s < M * boundaryAdjustedSize ρ ^ α

theorem IsScaleConnected.mono {r r' : ℝ} {ρ : ChargeDensity L} (h : IsScaleConnected r ρ)
    (hr : r ≤ r') : IsScaleConnected r' ρ := fun S hS h₁ h₂ => (h S hS h₁ h₂).trans hr

/-! ### Supports, constituents, signs -/

theorem setDist_empty_right (s : Finset (Site L)) : euclideanSetDistance s ∅ = 0 := by
  simp [euclideanSetDistance]

/-- The complement of a constituent has the complementary support. -/
theorem chargeSupport_sub_constituent {ρ ρ₁ : ChargeDensity L} (h : IsConstituent ρ ρ₁) :
    chargeSupport (fun x => ρ x - ρ₁ x) = chargeSupport ρ \ chargeSupport ρ₁ := by
  ext x
  by_cases hx : x ∈ chargeSupport ρ₁
  · have hagree := h.2.2 x hx
    simp [chargeSupport, hagree]
  · have hz : ρ₁ x = 0 := by simpa [chargeSupport] using hx
    simp [chargeSupport, hz]

/-- A constituent is determined by its support. -/
theorem constituent_eq_of_support {ρ ρ₁ σ : ChargeDensity L} (h : IsConstituent ρ ρ₁)
    (hsupp : chargeSupport ρ₁ = chargeSupport σ) (hagree : ∀ x ∈ chargeSupport σ, ρ x = σ x) :
    ρ₁ = σ := by
  funext x
  by_cases hx : x ∈ chargeSupport σ
  · rw [← hagree x hx, h.2.2 x (hsupp ▸ hx)]
  · have h1 : ρ₁ x = 0 := by
      have : x ∉ chargeSupport ρ₁ := hsupp ▸ hx
      simpa [chargeSupport] using this
    have h2 : σ x = 0 := by simpa [chargeSupport] using hx
    rw [h1, h2]

theorem chargeSupport_add {a c : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport c)) :
    chargeSupport (a + c) = chargeSupport a ∪ chargeSupport c := by
  simpa using chargeSupport_add_smul (ε := 1) hdisj (Or.inl rfl)

theorem add_apply_of_mem_left {a c : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport c)) {x : Site L}
    (hx : x ∈ chargeSupport a) : (a + c) x = a x := by
  simpa using add_smul_eq_left (ε := 1) hdisj hx

theorem chargeSupport_neg (c : ChargeDensity L) : chargeSupport (-c) = chargeSupport c := by
  ext x
  simp [chargeSupport]

theorem totalCharge_neg (c : ChargeDensity L) : totalCharge (-c) = -totalCharge c := by
  simp [totalCharge]

theorem boundaryAdjustedSize_neg (c : ChargeDensity L) :
    boundaryAdjustedSize (-c) = boundaryAdjustedSize c := by
  simp [boundaryAdjustedSize, totalCharge_neg, chargeEuclideanDiameter, chargeBoundaryDistance,
    chargeSupport_neg]

theorem isConstituent_neg {c ρ₁ : ChargeDensity L} (h : IsConstituent (-c) ρ₁) :
    IsConstituent c (-ρ₁) := by
  refine ⟨neg_ne_zero.mpr h.1, ?_, fun x hx => ?_⟩
  · rw [chargeSupport_neg, ← chargeSupport_neg c]
    exact h.2.1
  · rw [chargeSupport_neg] at hx
    have := h.2.2 x hx
    simp only [Pi.neg_apply] at this ⊢
    omega

theorem IsIsolated.neg {M α : ℝ} {c : ChargeDensity L} (h : IsIsolated M α c) :
    IsIsolated M α (-c) := by
  intro ρ₁ hρ₁ hH
  have hc := isConstituent_neg hρ₁
  have hT : chargeSupport (fun x => (-c) x - ρ₁ x) = chargeSupport (fun x => c x - (-ρ₁) x) := by
    rw [chargeSupport_sub_constituent hρ₁, chargeSupport_sub_constituent hc, chargeSupport_neg,
      chargeSupport_neg]
  rw [hT] at hH ⊢
  have key := h (-ρ₁) hc (by simpa [chargeEuclideanDiameter, chargeSupport_neg] using hH)
  refine ⟨fun h0 => key.1 (by rw [totalCharge_neg, h0, neg_zero]), ?_⟩
  simpa [chargeBoundaryDistance, chargeSupport_neg] using key.2

theorem IsScaleConnected.neg {r : ℝ} {c : ChargeDensity L} (h : IsScaleConnected r c) :
    IsScaleConnected r (-c) := by
  simpa [IsScaleConnected, chargeSupport_neg] using h

theorem HasScaleWitness.neg {M α s : ℝ} {c : ChargeDensity L} (h : HasScaleWitness M α s c) :
    HasScaleWitness M α s (-c) := by
  simpa [HasScaleWitness, chargeEuclideanDiameter, boundaryAdjustedSize_neg, chargeSupport_neg]
    using h

theorem sign_smul_eq {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (c : ChargeDensity L) :
    ε • c = c ∨ ε • c = -c := by
  rcases hε with rfl | rfl
  · exact Or.inl (one_smul ℤ c)
  · exact Or.inr (neg_one_smul ℤ c)

/-! ### Diameters against powers -/

theorem le_rpow_self {d α : ℝ} (hd : 1 ≤ d) (hα : 1 ≤ α) : d ≤ d ^ α := by
  calc d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
    _ ≤ d ^ α := Real.rpow_le_rpow_of_exponent_le hd hα

/-- `2M d^α ≤ 2s` with `M > 1` forces `d < s`, since lattice diameters are `0` or `≥ 1`. -/
theorem diam_lt_of_two_mul_rpow_le {M α s : ℝ} {σ : Finset (Site L)} (hM : 1 < M)
    (hα : 1 ≤ α) (hs : 0 < s) (h : 2 * M * euclideanSetDiameter σ ^ α ≤ 2 * s) :
    euclideanSetDiameter σ < s := by
  rcases diam_eq_zero_or_one_le σ with h0 | h1
  · rw [h0]
    exact hs
  · have := le_rpow_self h1 hα
    nlinarith

/-- `2M d^α ≤ 2s` with `M ≥ 1` is impossible once `d > s > 0`. -/
theorem not_two_mul_rpow_le {M α s : ℝ} {σ : Finset (Site L)} (hM : 1 ≤ M) (hα : 1 ≤ α)
    (hs : 0 < s) (hd : s < euclideanSetDiameter σ) :
    ¬ 2 * M * euclideanSetDiameter σ ^ α ≤ 2 * s := by
  intro h
  rcases diam_eq_zero_or_one_le σ with h0 | h1
  · rw [h0] at hd
    linarith
  · have := le_rpow_self h1 hα
    nlinarith

/-! ### The merge lemma -/

/-- A cut of a `2s`-connected operand `a ⊆ U` by `S` is crossed within `2s` in `U`. -/
theorem cross_le_of_cut {s : ℝ} {a : ChargeDensity L} {S U : Finset (Site L)}
    (hca : IsScaleConnected (2 * s) a) (haU : chargeSupport a ⊆ U)
    (hSa : (S ∩ chargeSupport a).Nonempty) (hTa : (chargeSupport a \ S).Nonempty) :
    euclideanSetDistance S (U \ S) ≤ 2 * s := by
  have hsd : chargeSupport a \ (S ∩ chargeSupport a) = chargeSupport a \ S := by
    ext x
    simp
  have hcut := hca _ Finset.inter_subset_right hSa (hsd ▸ hTa)
  rw [hsd] at hcut
  refine (setDist_le_of_subset Finset.inter_subset_left ?_ hSa hTa).trans hcut
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  exact ⟨haU hx.1, hx.2⟩

/-- **Cut-to-history, split case.** A constituent of `a + c` meeting both operands is never
separated from its complement by `2M d^α`. -/
theorem not_meets_both {M α s : ℝ} (hM : 1 ≤ M) (hα : 1 ≤ α) (hs : 0 < s)
    {a c ρ₁ : ChargeDensity L} (hdisj : Disjoint (chargeSupport a) (chargeSupport c))
    (hD : s < euclideanSetDistance (chargeSupport a) (chargeSupport c))
    (hca : IsScaleConnected (2 * s) a) (hcc : IsScaleConnected (2 * s) c)
    (hρ₁ : IsConstituent (a + c) ρ₁)
    (hSa : (chargeSupport ρ₁ ∩ chargeSupport a).Nonempty)
    (hSc : (chargeSupport ρ₁ ∩ chargeSupport c).Nonempty) :
    ¬ 2 * M * chargeEuclideanDiameter ρ₁ ^ α ≤
      euclideanSetDistance (chargeSupport ρ₁) (chargeSupport (fun x => (a + c) x - ρ₁ x)) := by
  intro hH
  set S := chargeSupport ρ₁
  have hτ := chargeSupport_add hdisj
  rw [chargeSupport_sub_constituent hρ₁, hτ] at hH
  have hdS : s < euclideanSetDiameter S :=
    hD.trans_le ((setDist_le_of_subset Finset.inter_subset_right Finset.inter_subset_right
      hSa hSc).trans (setDist_le_diam Finset.inter_subset_left Finset.inter_subset_left hSa hSc))
  have hcross : euclideanSetDistance S ((chargeSupport a ∪ chargeSupport c) \ S) ≤ 2 * s := by
    by_cases hTa : (chargeSupport a \ S).Nonempty
    · exact cross_le_of_cut hca Finset.subset_union_left hSa hTa
    by_cases hTc : (chargeSupport c \ S).Nonempty
    · exact cross_le_of_cut hcc Finset.subset_union_right hSc hTc
    have hempty : (chargeSupport a ∪ chargeSupport c) \ S = ∅ := by
      rw [Finset.union_sdiff_distrib, Finset.not_nonempty_iff_eq_empty.mp hTa,
        Finset.not_nonempty_iff_eq_empty.mp hTc, Finset.union_empty]
    rw [hempty, setDist_empty_right]
    linarith
  exact not_two_mul_rpow_le hM hα hs hdS (hH.trans hcross)

/-- **Cut-to-history, one-sided case.** A constituent of `a + c` inside `supp a` is isolated: if it
cuts `a`, by the isolation of `a`; if it is all of `a`, the crossing is the merge itself, bounded
by the witness of `a`. -/
theorem isolated_add_of_subset {M α s : ℝ} (hM : 1 < M) (hα : 1 ≤ α) (hs : 0 < s)
    {a c ρ₁ : ChargeDensity L} (hdisj : Disjoint (chargeSupport a) (chargeSupport c))
    (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s)
    (hia : IsIsolated M α a) (hwa : HasScaleWitness M α s a)
    (hρ₁ : IsConstituent (a + c) ρ₁) (hSa : chargeSupport ρ₁ ⊆ chargeSupport a)
    (hH : 2 * M * chargeEuclideanDiameter ρ₁ ^ α ≤
      euclideanSetDistance (chargeSupport ρ₁) (chargeSupport (fun x => (a + c) x - ρ₁ x))) :
    totalCharge ρ₁ ≠ 0 ∧
      euclideanSetDistance (chargeSupport ρ₁) (chargeSupport (fun x => (a + c) x - ρ₁ x)) ≤
        2 * M * chargeBoundaryDistance ρ₁ ^ α := by
  set S := chargeSupport ρ₁ with hSdef
  have hSne : S.Nonempty := chargeSupport_nonempty_of_ne_zero ρ₁ hρ₁.1
  have hτ := chargeSupport_add hdisj
  rw [chargeSupport_sub_constituent hρ₁, hτ] at hH ⊢
  have hρa : IsConstituent a ρ₁ :=
    ⟨hρ₁.1, hSa, fun x hx => by rw [← hρ₁.2.2 x hx, add_apply_of_mem_left hdisj (hSa hx)]⟩
  by_cases hcut : (chargeSupport a \ S).Nonempty
  · have hmono : euclideanSetDistance S ((chargeSupport a ∪ chargeSupport c) \ S) ≤
        euclideanSetDistance S (chargeSupport a \ S) :=
      setDist_le_of_subset subset_rfl (Finset.sdiff_subset_sdiff Finset.subset_union_left subset_rfl)
        hSne hcut
    have key := hia ρ₁ hρa (by rw [chargeSupport_sub_constituent hρa]; exact hH.trans hmono)
    rw [chargeSupport_sub_constituent hρa] at key
    exact ⟨key.1, hmono.trans key.2⟩
  · -- the constituent is the whole operand `a`
    have hSeq : S = chargeSupport a :=
      Finset.Subset.antisymm hSa (Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp hcut))
    have hρeq : ρ₁ = a :=
      constituent_eq_of_support hρ₁ hSeq fun x hx => add_apply_of_mem_left hdisj hx
    subst hρeq
    have hTc : (chargeSupport ρ₁ ∪ chargeSupport c) \ chargeSupport ρ₁ = chargeSupport c := by
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint]
      exact hdisj.symm
    rw [← hSdef, hSeq, hTc] at hH ⊢
    have hH2 := hH.trans hD
    have hd := diam_lt_of_two_mul_rpow_le hM hα hs hH2
    have hw := hwa hd
    have hdpow : M * chargeEuclideanDiameter ρ₁ ^ α ≤ s := by linarith
    by_cases hq : totalCharge ρ₁ = 0
    · rw [boundaryAdjustedSize_of_neutral ρ₁ hq] at hw
      linarith
    rw [boundaryAdjustedSize_of_charged ρ₁ hq] at hw
    refine ⟨hq, ?_⟩
    rcases le_total (chargeBoundaryDistance ρ₁) (chargeEuclideanDiameter ρ₁) with hle | hle
    · rw [max_eq_right hle] at hw
      linarith
    · rw [max_eq_left hle] at hw
      linarith

/-- **Merge lemma.** Merging two isolated, `2s`-connected, witnessed operands at distance in
`(s, 2s]` gives an isolated density. -/
theorem isIsolated_add {M α s : ℝ} (hM : 1 < M) (hα : 1 ≤ α) (hs : 0 < s)
    {a c : ChargeDensity L} (hdisj : Disjoint (chargeSupport a) (chargeSupport c))
    (hD₁ : s < euclideanSetDistance (chargeSupport a) (chargeSupport c))
    (hD₂ : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s)
    (hia : IsIsolated M α a) (hic : IsIsolated M α c)
    (hca : IsScaleConnected (2 * s) a) (hcc : IsScaleConnected (2 * s) c)
    (hwa : HasScaleWitness M α s a) (hwc : HasScaleWitness M α s c) :
    IsIsolated M α (a + c) := by
  intro ρ₁ hρ₁ hH
  have hSne := chargeSupport_nonempty_of_ne_zero ρ₁ hρ₁.1
  have hSτ : chargeSupport ρ₁ ⊆ chargeSupport a ∪ chargeSupport c :=
    chargeSupport_add hdisj ▸ hρ₁.2.1
  by_cases hSa : (chargeSupport ρ₁ ∩ chargeSupport a).Nonempty <;>
    by_cases hSc : (chargeSupport ρ₁ ∩ chargeSupport c).Nonempty
  · exact absurd hH (not_meets_both hM.le hα hs hdisj hD₁ hca hcc hρ₁ hSa hSc)
  · refine isolated_add_of_subset hM hα hs hdisj hD₂ hia hwa hρ₁ ?_ hH
    intro x hx
    rcases Finset.mem_union.mp (hSτ hx) with h | h
    · exact h
    · exact absurd ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩ hSc
  · rw [add_comm a c] at hρ₁ hH ⊢
    refine isolated_add_of_subset hM hα hs hdisj.symm (by rwa [setDist_comm]) hic hwc hρ₁ ?_ hH
    intro x hx
    rcases Finset.mem_union.mp (hSτ hx) with h | h
    · exact absurd ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩ hSa
    · exact h
  · exfalso
    obtain ⟨x, hx⟩ := hSne
    rcases Finset.mem_union.mp (hSτ hx) with h | h
    · exact hSa ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩
    · exact hSc ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩

/-- Merging two `2s`-connected operands at distance `≤ 2s` gives a `2s`-connected density. -/
theorem isScaleConnected_add {s : ℝ} {a c : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport c))
    (ha : (chargeSupport a).Nonempty) (hc : (chargeSupport c).Nonempty)
    (hD₂ : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s)
    (hca : IsScaleConnected (2 * s) a) (hcc : IsScaleConnected (2 * s) c) :
    IsScaleConnected (2 * s) (a + c) := by
  intro S hS hSne hTne
  rw [chargeSupport_add hdisj] at hS hTne ⊢
  by_cases hA : (S ∩ chargeSupport a).Nonempty ∧ (chargeSupport a \ S).Nonempty
  · exact cross_le_of_cut hca Finset.subset_union_left hA.1 hA.2
  by_cases hC : (S ∩ chargeSupport c).Nonempty ∧ (chargeSupport c \ S).Nonempty
  · exact cross_le_of_cut hcc Finset.subset_union_right hC.1 hC.2
  -- neither operand is cut: each lies wholly in `S` or wholly outside it
  have side : ∀ b : Finset (Site L), ¬ ((S ∩ b).Nonempty ∧ (b \ S).Nonempty) →
      b ⊆ S ∨ Disjoint b S := by
    intro b hb
    by_cases h₁ : (S ∩ b).Nonempty
    · left
      have : ¬ (b \ S).Nonempty := fun h => hb ⟨h₁, h⟩
      exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp this)
    · right
      rw [Finset.disjoint_left]
      intro x hxb hxS
      exact h₁ ⟨x, Finset.mem_inter.mpr ⟨hxS, hxb⟩⟩
  have out : ∀ b : Finset (Site L), b ⊆ chargeSupport a ∪ chargeSupport c → Disjoint b S →
      b ⊆ (chargeSupport a ∪ chargeSupport c) \ S := fun b hb hbS x hx =>
    Finset.mem_sdiff.mpr ⟨hb hx, Finset.disjoint_left.mp hbS hx⟩
  rcases side _ hA with hAS | hAS <;> rcases side _ hC with hCS | hCS
  · exfalso
    obtain ⟨x, hx⟩ := hTne
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.mp hx.1 with h | h
    · exact hx.2 (hAS h)
    · exact hx.2 (hCS h)
  · exact (setDist_le_of_subset hAS (out _ Finset.subset_union_right hCS) ha hc).trans hD₂
  · refine (setDist_le_of_subset hCS (out _ Finset.subset_union_left hAS) hc ha).trans ?_
    rwa [setDist_comm]
  · exfalso
    obtain ⟨x, hx⟩ := hSne
    rcases Finset.mem_union.mp (hS hx) with h | h
    · exact Finset.disjoint_left.mp hAS h hx
    · exact Finset.disjoint_left.mp hCS h hx

/-- The merged density has diameter at least the merge distance. -/
theorem setDist_le_diam_add {a c : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport c))
    (ha : (chargeSupport a).Nonempty) (hc : (chargeSupport c).Nonempty) :
    euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ chargeEuclideanDiameter (a + c) := by
  unfold chargeEuclideanDiameter
  rw [chargeSupport_add hdisj]
  exact setDist_le_diam Finset.subset_union_left Finset.subset_union_right ha hc

/-- The merged density satisfies the witness vacuously. -/
theorem hasScaleWitness_add {M α s : ℝ} {a c : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport c))
    (ha : (chargeSupport a).Nonempty) (hc : (chargeSupport c).Nonempty)
    (hD₁ : s < euclideanSetDistance (chargeSupport a) (chargeSupport c)) :
    HasScaleWitness M α s (a + c) := fun hd =>
  absurd (hD₁.trans_le (setDist_le_diam_add hdisj ha hc)) (lt_asymm hd)

/-- **Merge lemma, signed form** (`τ = a + ε c`, FS81 (2.13) branches `a ± c`). -/
theorem merge_signed {M α s : ℝ} (hM : 1 < M) (hα : 1 ≤ α) (hs : 0 < s)
    {a c : ChargeDensity L} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (ha : a ≠ 0) (hc : c ≠ 0)
    (hdisj : Disjoint (chargeSupport a) (chargeSupport c))
    (hD₁ : s < euclideanSetDistance (chargeSupport a) (chargeSupport c))
    (hD₂ : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s)
    (hia : IsIsolated M α a) (hic : IsIsolated M α c)
    (hca : IsScaleConnected (2 * s) a) (hcc : IsScaleConnected (2 * s) c)
    (hwa : HasScaleWitness M α s a) (hwc : HasScaleWitness M α s c) :
    IsIsolated M α (a + ε • c) ∧ IsScaleConnected (2 * s) (a + ε • c) ∧
      HasScaleWitness M α s (a + ε • c) ∧
      chargeSupport (a + ε • c) = chargeSupport a ∪ chargeSupport c ∧
      s < chargeEuclideanDiameter (a + ε • c) := by
  have hane := chargeSupport_nonempty_of_ne_zero a ha
  have hcne := chargeSupport_nonempty_of_ne_zero c hc
  have hsupp := chargeSupport_add_smul hdisj hε
  rcases sign_smul_eq hε c with h | h <;> rw [h] at hsupp ⊢
  · exact ⟨isIsolated_add hM hα hs hdisj hD₁ hD₂ hia hic hca hcc hwa hwc,
      isScaleConnected_add hdisj hane hcne hD₂ hca hcc,
      hasScaleWitness_add hdisj hane hcne hD₁, hsupp,
      hD₁.trans_le (setDist_le_diam_add hdisj hane hcne)⟩
  · rw [← chargeSupport_neg c] at hdisj hD₁ hD₂ hcne
    exact ⟨isIsolated_add hM hα hs hdisj hD₁ hD₂ hia hic.neg hca hcc.neg hwa hwc.neg,
      isScaleConnected_add hdisj hane hcne hD₂ hca hcc.neg,
      hasScaleWitness_add hdisj hane hcne hD₁, hsupp,
      hD₁.trans_le (setDist_le_diam_add hdisj hane hcne)⟩

end FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

end
