/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ScaleGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scale-atom families and the first-crossing argument for KP Theorem 2.2(c)

Along the scale process every factor `f`
carries the supports of its ancestors at each earlier scale.

These form a laminar family of
subsets of `supp f`, indexed by levels `0, …, T`; level `s` corresponds to KP's scale `s − 1`
(threshold `levelThreshold s`).

A `ScaleAtomFamily` records exactly the properties used in the
first-crossing argument:

* level `0` consists of the singletons of `supp f`, level `T` is `{supp f}`, and each level
  partitions `supp f` and refines the next;
* below the top, distinct atoms of one level `s` are more than `2^{s−1}` apart (the active
  separation of the scale process);
* the children of an atom at level `s + 1` are connected by conflict edges of length `≤ 2^s`
  (the merge history of KP Lemma 4.3);
* below the top, an atom on which `f` is neutral has `2^{s−1} < M d^α` (KP Claim 4.4).

`ScaleAtomFamily.split_charged` is : for a neutral `f`, a split `f = f₁ + f₂` with
`dist(f₁, f₂) ≥ 2M [min(d(f₁), d(f₂))]^α` has both pieces non-neutral.

`ScaleAtomFamily.ofSingleton`
and `ScaleAtomFamily.merge` build the families along the process.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open Finset

/-- The separation threshold of level `s`, i.e. of KP scale `s − 1`: `0` at level `0` (scale
`−1`, where separation means disjointness), `2^{s−1}` otherwise. -/
def levelThreshold : ℕ → ℕ
  | 0 => 0
  | s + 1 => 2 ^ s

theorem levelThreshold_succ (s : ℕ) : levelThreshold (s + 1) = 2 ^ s := rfl

theorem levelThreshold_mono {s t : ℕ} (hst : s ≤ t) : levelThreshold s ≤ levelThreshold t := by
  rcases s with _ | s
  · exact Nat.zero_le _
  · rcases t with _ | t
    · omega
    · rw [levelThreshold_succ, levelThreshold_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Distance between sets is antitone in both arguments (for nonempty subsets). -/
theorem squareDistance_le_of_subset (boundary : SquareBoundary) (L : ℕ)
    {X Y S T : Finset (Fin L × Fin L)} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXS : X ⊆ S) (hYT : Y ⊆ T) :
    squareDistance boundary L S T ≤ squareDistance boundary L X Y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_squareDistance_eq boundary L X Y hX hY
  rw [hxy]
  exact squareDistance_le_latticeDistance_of_mem boundary L S T x y (hXS hx) (hYT hy)

/-- A laminar family of ancestor supports of `f` at levels `0, …, T` (level `s` ↔ KP scale
`s − 1`), with the separation, connectivity and Claim 4.4 properties of the scale process. -/
structure ScaleAtomFamily (boundary : SquareBoundary) (L : ℕ) (f : ChargeDensity L) (T : ℕ) where
  /-- The atoms at each level. -/
  atoms : ℕ → Finset (Finset (Fin L × Fin L))
  base : atoms 0 = (chargeSupport f).image fun x => {x}
  top : atoms T = {chargeSupport f}
  nonempty : ∀ s ≤ T, ∀ X ∈ atoms s, X.Nonempty
  subset : ∀ s ≤ T, ∀ X ∈ atoms s, X ⊆ chargeSupport f
  cover : ∀ s ≤ T, ∀ x ∈ chargeSupport f, ∃ X ∈ atoms s, x ∈ X
  disjoint : ∀ s ≤ T, ∀ X ∈ atoms s, ∀ Y ∈ atoms s, X ≠ Y → Disjoint X Y
  refine : ∀ s < T, ∀ X ∈ atoms s, ∃ Y ∈ atoms (s + 1), X ⊆ Y
  separated : ∀ s < T, ∀ X ∈ atoms s, ∀ Y ∈ atoms s, X ≠ Y →
    levelThreshold s < squareDistance boundary L X Y
  connected : ∀ s < T, ∀ X ∈ atoms (s + 1), ∀ U ⊆ (atoms s).filter (· ⊆ X), U.Nonempty →
    U ≠ (atoms s).filter (· ⊆ X) →
    ∃ u ∈ U, ∃ v ∈ (atoms s).filter (· ⊆ X), v ∉ U ∧ squareDistance boundary L u v ≤ 2 ^ s
  neutral : ∀ s < T, ∀ X ∈ atoms s, ∑ x ∈ X, f x = 0 →
    (levelThreshold s : ℝ) <
      (chargeCoverScale : ℝ) * (squareDiameter boundary L X : ℝ) ^ chargeCoverExponent

namespace ScaleAtomFamily

variable {boundary : SquareBoundary} {L : ℕ} {f : ChargeDensity L} {T : ℕ}

/-- The children of an atom at level `s + 1` cover it. -/
theorem mem_child (F : ScaleAtomFamily boundary L f T) {s : ℕ} (hs : s < T)
    {X : Finset (Fin L × Fin L)} (hX : X ∈ F.atoms (s + 1)) {x : Fin L × Fin L} (hx : x ∈ X) :
    ∃ Y ∈ F.atoms s, Y ⊆ X ∧ x ∈ Y := by
  obtain ⟨Y, hY, hxY⟩ := F.cover s hs.le x (F.subset (s + 1) hs X hX hx)
  obtain ⟨Z, hZ, hYZ⟩ := F.refine s hs Y hY
  refine ⟨Y, hY, ?_, hxY⟩
  by_cases hZX : Z = X
  · exact hZX ▸ hYZ
  · exact absurd (F.disjoint (s + 1) hs Z hZ X hX hZX) (Finset.not_disjoint_iff.mpr
      ⟨x, hYZ hxY, hx⟩)

end ScaleAtomFamily

/-- `M d^α` exceeds `d` for `d ≥ 1`. -/
theorem lt_chargeCoverScale_mul_rpow {d : ℝ} (hd : 1 ≤ d) :
    d < (chargeCoverScale : ℝ) * d ^ chargeCoverExponent := by
  have hα : (1 : ℝ) ≤ chargeCoverExponent := by unfold chargeCoverExponent; norm_num
  have h1 : d ≤ d ^ chargeCoverExponent := by
    simpa using Real.rpow_le_rpow_of_exponent_le hd hα
  have hM : (2 : ℝ) ≤ (chargeCoverScale : ℝ) := by unfold chargeCoverScale; norm_num
  have hpos : 0 < d ^ chargeCoverExponent := by positivity
  nlinarith

/-- The one-sided half of : if `f = f₁ + f₂` with disjoint supports and
`dist(f₁, f₂) ≥ 2M d(f₁)^α`, then `f₁` is non-neutral. -/
theorem ScaleAtomFamily.smaller_piece_charged {boundary : SquareBoundary} {L : ℕ}
    (hL : 1 < L) {f : ChargeDensity L} {T : ℕ} (F : ScaleAtomFamily boundary L f T)
    (f₁ f₂ : ChargeDensity L) (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0)
    (hdisj : Disjoint (chargeSupport f₁) (chargeSupport f₂)) (hsum : f = f₁ + f₂)
    (hsep : 2 * (chargeCoverScale : ℝ) * (chargeDiameter boundary L f₁ : ℝ) ^ chargeCoverExponent ≤
      densityDistance boundary L f₁ f₂) :
    ∑ x, f₁ x ≠ 0 := by
  classical
  set S₁ := chargeSupport f₁ with hS₁
  set S₂ := chargeSupport f₂ with hS₂
  have hS₁ne : S₁.Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, f₁ x ≠ 0 := by
      by_contra h
      push Not at h
      exact h₁ (funext h)
    exact ⟨x, by simp [S₁, chargeSupport, hx]⟩
  have hS₂ne : S₂.Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, f₂ x ≠ 0 := by
      by_contra h
      push Not at h
      exact h₂ (funext h)
    exact ⟨x, by simp [S₂, chargeSupport, hx]⟩
  -- `f` agrees with `f₁` on `S₁` and with `f₂` on `S₂`.
  have hf₁ : ∀ x ∈ S₁, f x = f₁ x := by
    intro x hx
    have hx2 : x ∉ S₂ := Finset.disjoint_left.mp hdisj hx
    have : f₂ x = 0 := by simpa [S₂, chargeSupport] using hx2
    rw [hsum, Pi.add_apply, this, add_zero]
  have hsupp : chargeSupport f = S₁ ∪ S₂ := by
    ext x
    simp only [chargeSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      S₁, S₂, hsum, Pi.add_apply]
    constructor
    · intro hx
      by_contra hcon
      push Not at hcon
      exact hx (by rw [hcon.1, hcon.2]; rfl)
    · rintro (hx | hx)
      · have : f₂ x = 0 := by
          by_contra h0
          exact Finset.disjoint_left.mp hdisj
            (by simp [S₁, chargeSupport, hx] : x ∈ S₁) (by simp [S₂, chargeSupport, h0])
        rw [this, add_zero]
        exact hx
      · have : f₁ x = 0 := by
          by_contra h0
          exact Finset.disjoint_left.mp hdisj
            (by simp [S₁, chargeSupport, h0] : x ∈ S₁) (by simp [S₂, chargeSupport, hx])
        rw [this, zero_add]
        exact hx
  have hsumS₁ : ∑ x, f₁ x = ∑ x ∈ S₁, f₁ x := by
    rw [← Finset.sum_subset (Finset.subset_univ S₁)]
    intro x _ hx
    simpa [S₁, chargeSupport] using hx
  rw [hsumS₁]
  -- Small piece: a single site.
  by_cases hd0 : chargeDiameter boundary L f₁ = 0
  · obtain ⟨x, hx⟩ := hS₁ne
    have hsing : S₁ = {x} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        by_contra hyx
        have h1 := one_le_latticeDistance_of_ne boundary hL hyx
        have h2 := latticeDistance_le_squareDiameter_of_mem boundary L S₁ y x hy hx
        have : chargeDiameter boundary L f₁ = squareDiameter boundary L S₁ := rfl
        omega
      · rintro rfl
        exact hx
    rw [hsing, Finset.sum_singleton]
    simpa [S₁, chargeSupport] using hx
  have hd1 : 1 ≤ chargeDiameter boundary L f₁ := Nat.one_le_iff_ne_zero.mpr hd0
  -- One-sided atoms.
  let OneSided : Finset (Fin L × Fin L) → Prop := fun X => X ⊆ S₁ ∨ X ⊆ S₂
  have hex : ∃ s, s ≤ T ∧ ∃ X ∈ F.atoms s, ¬ OneSided X := by
    refine ⟨T, le_rfl, chargeSupport f, by rw [F.top]; exact Finset.mem_singleton_self _, ?_⟩
    rintro (h | h)
    · obtain ⟨y, hy⟩ := hS₂ne
      exact Finset.disjoint_left.mp hdisj (h (hsupp ▸ Finset.mem_union_right S₁ hy)) hy
    · obtain ⟨y, hy⟩ := hS₁ne
      exact Finset.disjoint_left.mp hdisj hy (h (hsupp ▸ Finset.mem_union_left S₂ hy))
  classical
  let s₀ := Nat.find hex
  have hs₀ : s₀ ≤ T ∧ ∃ X ∈ F.atoms s₀, ¬ OneSided X := Nat.find_spec hex
  have hmin : ∀ s < s₀, s ≤ T → ∀ X ∈ F.atoms s, OneSided X := by
    intro s hs hsT X hX
    by_contra hcon
    exact Nat.find_min hex hs ⟨hsT, X, hX, hcon⟩
  have hs₀pos : s₀ ≠ 0 := by
    intro h0
    obtain ⟨X, hX, hX2⟩ := hs₀.2
    rw [h0, F.base] at hX
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hX
    rw [hsupp] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hX2 (Or.inl (Finset.singleton_subset_iff.mpr hx))
    · exact hX2 (Or.inr (Finset.singleton_subset_iff.mpr hx))
  obtain ⟨s, hs⟩ : ∃ s, s₀ = s + 1 := Nat.exists_eq_succ_of_ne_zero hs₀pos
  have hsT : s < T := by omega
  have hside : ∀ X ∈ F.atoms s, OneSided X := hmin s (by omega) hsT.le
  obtain ⟨X, hX, hX2⟩ := hs₀.2
  rw [hs] at hX
  -- The children of the two-sided atom.
  set Ch := (F.atoms s).filter (· ⊆ X) with hCh
  set U := Ch.filter (· ⊆ S₁) with hU
  have hXsub : X ⊆ S₁ ∪ S₂ := hsupp ▸ F.subset (s + 1) hsT X hX
  have hX1 : ∃ x ∈ X, x ∈ S₁ := by
    by_contra h
    push Not at h
    exact hX2 (Or.inr fun x hx => by
      rcases Finset.mem_union.mp (hXsub hx) with h' | h'
      · exact absurd h' (h x hx)
      · exact h')
  have hX2' : ∃ x ∈ X, x ∈ S₂ := by
    by_contra h
    push Not at h
    exact hX2 (Or.inl fun x hx => by
      rcases Finset.mem_union.mp (hXsub hx) with h' | h'
      · exact h'
      · exact absurd h' (h x hx))
  have hUne : U.Nonempty := by
    obtain ⟨x, hxX, hx1⟩ := hX1
    obtain ⟨Y, hY, hYX, hxY⟩ := F.mem_child hsT hX hxX
    refine ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hY, hYX⟩, ?_⟩⟩
    rcases hside Y hY with h | h
    · exact h
    · exact absurd (h hxY) (Finset.disjoint_left.mp hdisj hx1)
  have hUne' : U ≠ Ch := by
    obtain ⟨x, hxX, hx2⟩ := hX2'
    obtain ⟨Y, hY, hYX, hxY⟩ := F.mem_child hsT hX hxX
    intro hUC
    have hYCh : Y ∈ Ch := Finset.mem_filter.mpr ⟨hY, hYX⟩
    rw [← hUC] at hYCh
    have hY1 : Y ⊆ S₁ := (Finset.mem_filter.mp hYCh).2
    exact Finset.disjoint_left.mp hdisj (hY1 hxY) hx2
  obtain ⟨u, huU, v, hvCh, hvU, huv⟩ :=
    F.connected s hsT X hX U (Finset.filter_subset _ _) hUne hUne'
  have hu1 : u ⊆ S₁ := (Finset.mem_filter.mp huU).2
  have huA : u ∈ F.atoms s := (Finset.mem_filter.mp (Finset.mem_filter.mp huU).1).1
  have hvA : v ∈ F.atoms s := (Finset.mem_filter.mp hvCh).1
  have hv2 : v ⊆ S₂ := by
    rcases hside v hvA with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨hvCh, h⟩) hvU
    · exact h
  have hdist : densityDistance boundary L f₁ f₂ ≤ 2 ^ s :=
    (squareDistance_le_of_subset boundary L (F.nonempty s hsT.le u huA)
      (F.nonempty s hsT.le v hvA) hu1 hv2).trans huv
  -- The separation bound puts the crossing at a high scale.
  set d₁ : ℝ := (chargeDiameter boundary L f₁ : ℝ) with hd₁
  have hd₁1 : (1 : ℝ) ≤ d₁ := by rw [hd₁]; exact_mod_cast hd1
  have hlt := lt_chargeCoverScale_mul_rpow hd₁1
  have hMd : (2 : ℝ) * ((chargeCoverScale : ℝ) * d₁ ^ chargeCoverExponent) ≤ 2 ^ s := by
    have h := hsep.trans (by exact_mod_cast hdist : (densityDistance boundary L f₁ f₂ : ℝ) ≤
      ((2 ^ s : ℕ) : ℝ))
    rw [Nat.cast_pow, Nat.cast_ofNat] at h
    linarith
  have hspos : s ≠ 0 := by
    rintro rfl
    have : (1 : ℝ) < (chargeCoverScale : ℝ) * d₁ ^ chargeCoverExponent := by linarith
    norm_num at hMd
    linarith
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := Nat.exists_eq_succ_of_ne_zero hspos
  have hMd' : (chargeCoverScale : ℝ) * d₁ ^ chargeCoverExponent ≤ 2 ^ t := by
    rw [pow_succ] at hMd
    linarith
  have hthr : levelThreshold (t + 1) = 2 ^ t := levelThreshold_succ t
  -- Side-one atoms at level `t + 1`: there is exactly one, equal to `S₁`.
  have hatom1 : ∃ Y ∈ F.atoms (t + 1), Y ⊆ S₁ ∧ ∀ x ∈ S₁, x ∈ Y := by
    obtain ⟨x₀, hx₀⟩ := hS₁ne
    have hx₀f : x₀ ∈ chargeSupport f := hsupp ▸ Finset.mem_union_left S₂ hx₀
    obtain ⟨Y, hY, hx₀Y⟩ := F.cover (t + 1) hsT.le x₀ hx₀f
    have hY1 : Y ⊆ S₁ := by
      rcases hside Y hY with h | h
      · exact h
      · exact absurd (h hx₀Y) (Finset.disjoint_left.mp hdisj hx₀)
    refine ⟨Y, hY, hY1, fun x hx => ?_⟩
    have hxf : x ∈ chargeSupport f := hsupp ▸ Finset.mem_union_left S₂ hx
    obtain ⟨Y', hY', hxY'⟩ := F.cover (t + 1) hsT.le x hxf
    have hY'1 : Y' ⊆ S₁ := by
      rcases hside Y' hY' with h | h
      · exact h
      · exact absurd (h hxY') (Finset.disjoint_left.mp hdisj hx)
    by_contra hxY
    have hne : Y ≠ Y' := fun h => hxY (h ▸ hxY')
    have hsepY := F.separated (t + 1) hsT Y hY Y' hY' hne
    have hdiam := squareDistance_le_squareDiameter_of_subset boundary L
      (F.nonempty (t + 1) hsT.le Y hY) (F.nonempty (t + 1) hsT.le Y' hY') hY1 hY'1
    rw [hthr] at hsepY
    have : (2 : ℝ) ^ t < d₁ := by
      rw [hd₁]
      have h' : 2 ^ t < chargeDiameter boundary L f₁ := lt_of_lt_of_le hsepY hdiam
      exact_mod_cast h'
    linarith
  obtain ⟨Y, hY, hY1, hYcov⟩ := hatom1
  have hYeq : Y = S₁ := Finset.Subset.antisymm hY1 hYcov
  intro hzero
  have hneutralY : ∑ x ∈ Y, f x = 0 := by
    rw [hYeq, Finset.sum_congr rfl hf₁]
    exact hzero
  have hlarge := F.neutral (t + 1) hsT Y hY hneutralY
  rw [hthr, hYeq] at hlarge
  have : (squareDiameter boundary L S₁ : ℝ) = d₁ := rfl
  rw [this] at hlarge
  push_cast at hlarge
  linarith

/-- ** (KP Theorem 2.2(c))** for a factor carrying a scale-atom family: if `f` is neutral and
`f = f₁ + f₂` with disjoint supports and `dist(f₁, f₂) ≥ 2M [min(d(f₁), d(f₂))]^α`, then `f₁` and
`f₂` are non-neutral. -/
theorem ScaleAtomFamily.split_charged {boundary : SquareBoundary} {L : ℕ} (hL : 1 < L)
    {f : ChargeDensity L} {T : ℕ} (F : ScaleAtomFamily boundary L f T) (hf : ∑ x, f x = 0)
    (f₁ f₂ : ChargeDensity L) (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0)
    (hdisj : Disjoint (Function.support f₁) (Function.support f₂)) (hsum : f = f₁ + f₂)
    (hsep : 2 * (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L f₁) (chargeDiameter boundary L f₂) : ℕ) : ℝ) ^
          chargeCoverExponent ≤ densityDistance boundary L f₁ f₂) :
    ∑ x, f₁ x ≠ 0 ∧ ∑ x, f₂ x ≠ 0 := by
  classical
  have hdisj' : Disjoint (chargeSupport f₁) (chargeSupport f₂) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact Set.disjoint_left.mp hdisj (by simpa [chargeSupport] using hx1)
      (by simpa [chargeSupport] using hx2)
  have hcharge : ∑ x, f₁ x + ∑ x, f₂ x = 0 := by
    rw [← Finset.sum_add_distrib]
    simpa [hsum] using hf
  rcases le_total (chargeDiameter boundary L f₁) (chargeDiameter boundary L f₂) with hd | hd
  · rw [min_eq_left hd] at hsep
    have h := F.smaller_piece_charged hL f₁ f₂ h₁ h₂ hdisj' hsum hsep
    exact ⟨h, fun h' => h (by linarith)⟩
  · rw [min_eq_right hd] at hsep
    have hcomm : densityDistance boundary L f₁ f₂ = densityDistance boundary L f₂ f₁ :=
      squareDistance_symm boundary L _ _
    rw [hcomm] at hsep
    have h := F.smaller_piece_charged hL f₂ f₁ h₂ h₁ hdisj'.symm (by rw [hsum, add_comm]) hsep
    exact ⟨fun h' => h (by linarith), h⟩

/-! ### Building scale-atom families along the process -/

/-- An initial point charge carries the trivial family with top level `0`. -/
theorem ScaleAtomFamily.nonempty_of_support_eq_singleton {boundary : SquareBoundary} {L : ℕ}
    {f : ChargeDensity L} {x : Fin L × Fin L} (hf : chargeSupport f = {x}) :
    Nonempty (ScaleAtomFamily boundary L f 0) := by
  refine ⟨{
    atoms := fun _ => {{x}}
    base := by rw [hf, Finset.image_singleton]
    top := by rw [hf]
    nonempty := fun _ _ X hX => by
      rw [Finset.mem_singleton.mp hX]
      exact Finset.singleton_nonempty x
    subset := fun _ _ X hX => by rw [Finset.mem_singleton.mp hX, hf]
    cover := fun _ _ y hy => ⟨{x}, Finset.mem_singleton_self _, by rw [hf] at hy; exact hy⟩
    disjoint := fun _ _ X hX Y hY hXY => by
      rw [Finset.mem_singleton.mp hX, Finset.mem_singleton.mp hY] at hXY
      exact absurd rfl hXY
    refine := fun s hs => absurd hs (Nat.not_lt_zero s)
    separated := fun s hs => absurd hs (Nat.not_lt_zero s)
    connected := fun s hs => absurd hs (Nat.not_lt_zero s)
    neutral := fun s hs => absurd hs (Nat.not_lt_zero s) }⟩

/-- **The merge step.** An output `a` of KP Lemma 4.3 at scale `j` (level `j + 1`), whose active
parents `P` carry families with top level `j`, are `(j−1)`-separated, are connected by conflict
edges of length `≤ 2^j`, satisfy Claim 4.4 at level `j`, and agree with `a` up to sign on their
supports, carries a family with top level `j + 1`. -/
theorem ScaleAtomFamily.merge {boundary : SquareBoundary} {L : ℕ} (j : ℕ)
    (a : ChargeDensity L) (P : ChargeEnsemble L) (hP : P.Nonempty)
    (hfam : ∀ b ∈ P, Nonempty (ScaleAtomFamily boundary L b j))
    (hPdisj : ∀ b ∈ P, ∀ b' ∈ P, b ≠ b' → Disjoint (chargeSupport b) (chargeSupport b'))
    (hPne : ∀ b ∈ P, (chargeSupport b).Nonempty)
    (hsupp : chargeSupport a = P.biUnion chargeSupport)
    (hsign : ∀ b ∈ P, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ chargeSupport b, a x = σ * b x)
    (hsep : ∀ b ∈ P, ∀ b' ∈ P, b ≠ b' → levelThreshold j < densityDistance boundary L b b')
    (hconn : ∀ U ⊆ P, U.Nonempty → U ≠ P →
      ∃ b ∈ U, ∃ b' ∈ P, b' ∉ U ∧ densityDistance boundary L b b' ≤ 2 ^ j)
    (hneutral : ∀ b ∈ P, ∑ x, b x = 0 →
      (levelThreshold j : ℝ) <
        (chargeCoverScale : ℝ) * (chargeDiameter boundary L b : ℝ) ^ chargeCoverExponent) :
    Nonempty (ScaleAtomFamily boundary L a (j + 1)) := by
  classical
  let Fb : (b : P) → ScaleAtomFamily boundary L b.1 j := fun b => Classical.choice (hfam b.1 b.2)
  let atoms : ℕ → Finset (Finset (Fin L × Fin L)) := fun s =>
    if s ≤ j then P.attach.biUnion fun b => (Fb b).atoms s else {chargeSupport a}
  have hlow : ∀ s ≤ j, ∀ X, X ∈ atoms s ↔ ∃ b : P, X ∈ (Fb b).atoms s := by
    intro s hs X
    simp only [atoms, hs, ↓reduceIte, Finset.mem_biUnion, Finset.mem_attach, true_and]
  have htopA : atoms (j + 1) = {chargeSupport a} := by
    have h : ¬ j + 1 ≤ j := by omega
    simp only [atoms, h, ↓reduceIte]
  have hsubb : ∀ b : P, chargeSupport b.1 ⊆ chargeSupport a := fun b x hx => by
    rw [hsupp]; exact Finset.mem_biUnion.mpr ⟨b.1, b.2, hx⟩
  -- Atoms below the top live inside one parent support.
  have hin : ∀ s ≤ j, ∀ (b : P), ∀ X ∈ (Fb b).atoms s, X ⊆ chargeSupport b.1 ∧ X.Nonempty :=
    fun s hs b X hX => ⟨(Fb b).subset s hs X hX, (Fb b).nonempty s hs X hX⟩
  have huniq' : ∀ s ≤ j, ∀ t ≤ j, ∀ (b b' : P), ∀ X ∈ (Fb b).atoms s, ∀ Y ∈ (Fb b').atoms t,
      ¬ Disjoint X Y → b = b' := by
    intro s hs t ht b b' X hX Y hY hXY
    by_contra hne
    have hne' : b.1 ≠ b'.1 := fun h => hne (Subtype.ext h)
    exact hXY (Finset.disjoint_of_subset_left (hin s hs b X hX).1
      (Finset.disjoint_of_subset_right (hin t ht b' Y hY).1 (hPdisj b.1 b.2 b'.1 b'.2 hne')))
  have huniq : ∀ s ≤ j, ∀ (b b' : P), ∀ X ∈ (Fb b).atoms s, ∀ Y ∈ (Fb b').atoms s,
      ¬ Disjoint X Y → b = b' := fun s hs => huniq' s hs s hs
  have hparTop : ∀ b : P, (Fb b).atoms j = {chargeSupport b.1} := fun b => (Fb b).top
  refine ⟨{
    atoms := atoms
    base := ?_
    top := htopA
    nonempty := ?_
    subset := ?_
    cover := ?_
    disjoint := ?_
    refine := ?_
    separated := ?_
    connected := ?_
    neutral := ?_ }⟩
  · -- base
    ext X
    rw [hlow 0 (Nat.zero_le _)]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨b, hX⟩
      rw [(Fb b).base] at hX
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hX
      exact ⟨x, hsubb b hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hsupp] at hx
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
      refine ⟨⟨b, hb⟩, ?_⟩
      rw [(Fb ⟨b, hb⟩).base]
      exact Finset.mem_image.mpr ⟨x, hxb, rfl⟩
  · -- nonempty
    intro s hs X hX
    by_cases hsj : s ≤ j
    · obtain ⟨b, hb⟩ := (hlow s hsj X).mp hX
      exact (hin s hsj b X hb).2
    · have : s = j + 1 := by omega
      subst this
      rw [htopA, Finset.mem_singleton] at hX
      subst hX
      obtain ⟨b, hb⟩ := hP
      obtain ⟨x, hx⟩ := hPne b hb
      exact ⟨x, hsubb ⟨b, hb⟩ hx⟩
  · -- subset
    intro s hs X hX
    by_cases hsj : s ≤ j
    · obtain ⟨b, hb⟩ := (hlow s hsj X).mp hX
      exact (hin s hsj b X hb).1.trans (hsubb b)
    · have : s = j + 1 := by omega
      subst this
      rw [htopA, Finset.mem_singleton] at hX
      exact hX ▸ subset_refl _
  · -- cover
    intro s hs x hx
    by_cases hsj : s ≤ j
    · have hx' := hx
      rw [hsupp] at hx'
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx'
      obtain ⟨X, hX, hxX⟩ := (Fb ⟨b, hb⟩).cover s hsj x hxb
      exact ⟨X, (hlow s hsj X).mpr ⟨⟨b, hb⟩, hX⟩, hxX⟩
    · have : s = j + 1 := by omega
      subst this
      exact ⟨chargeSupport a, by rw [htopA]; exact Finset.mem_singleton_self _, hx⟩
  · -- disjoint
    intro s hs X hX Y hY hXY
    by_cases hsj : s ≤ j
    · obtain ⟨b, hb⟩ := (hlow s hsj X).mp hX
      obtain ⟨b', hb'⟩ := (hlow s hsj Y).mp hY
      by_contra hcon
      have hbb := huniq s hsj b b' X hb Y hb' hcon
      subst hbb
      exact hcon ((Fb b).disjoint s hsj X hb Y hb' hXY)
    · have : s = j + 1 := by omega
      subst this
      rw [htopA, Finset.mem_singleton] at hX hY
      exact absurd (hX.trans hY.symm) hXY
  · -- refine
    intro s hs X hX
    have hsj : s ≤ j := by omega
    obtain ⟨b, hb⟩ := (hlow s hsj X).mp hX
    by_cases hlt : s < j
    · obtain ⟨Y, hY, hXY⟩ := (Fb b).refine s hlt X hb
      exact ⟨Y, (hlow (s + 1) hlt Y).mpr ⟨b, hY⟩, hXY⟩
    · have : s = j := by omega
      subst this
      refine ⟨chargeSupport a, by rw [htopA]; exact Finset.mem_singleton_self _, ?_⟩
      exact (hin s hsj b X hb).1.trans (hsubb b)
  · -- separated
    intro s hs X hX Y hY hXY
    have hsj : s ≤ j := by omega
    obtain ⟨b, hb⟩ := (hlow s hsj X).mp hX
    obtain ⟨b', hb'⟩ := (hlow s hsj Y).mp hY
    by_cases hbb : b = b'
    · subst hbb
      by_cases hlt : s < j
      · exact (Fb b).separated s hlt X hb Y hb' hXY
      · have : s = j := by omega
        subst this
        rw [hparTop b, Finset.mem_singleton] at hb hb'
        exact absurd (hb.trans hb'.symm) hXY
    · have hne : b.1 ≠ b'.1 := fun h => hbb (Subtype.ext h)
      have h1 := hsep b.1 b.2 b'.1 b'.2 hne
      have h2 := squareDistance_le_of_subset boundary L (hin s hsj b X hb).2
        (hin s hsj b' Y hb').2 (hin s hsj b X hb).1 (hin s hsj b' Y hb').1
      have h3 := levelThreshold_mono hsj
      unfold densityDistance at h1
      omega
  · -- connected
    intro s hs X hX U hU hUne hUne'
    have hsj : s ≤ j := by omega
    by_cases hlt : s + 1 ≤ j
    · obtain ⟨b, hb⟩ := (hlow (s + 1) hlt X).mp hX
      have hfilt : (atoms s).filter (· ⊆ X) = ((Fb b).atoms s).filter (· ⊆ X) := by
        ext Y
        simp only [Finset.mem_filter]
        rw [hlow s hsj Y]
        constructor
        · rintro ⟨⟨b', hb'⟩, hYX⟩
          have hYne := (hin s hsj b' Y hb').2
          have hbb : b' = b := huniq' s hsj (s + 1) hlt b' b Y hb' X hb (by
            rw [Finset.not_disjoint_iff]
            obtain ⟨y, hy⟩ := hYne
            exact ⟨y, hy, hYX hy⟩)
          subst hbb
          exact ⟨hb', hYX⟩
        · rintro ⟨hY, hYX⟩
          exact ⟨⟨b, hY⟩, hYX⟩
      rw [hfilt] at hU hUne' ⊢
      exact (Fb b).connected s (by omega) X hb U hU hUne hUne'
    · have hsj' : s = j := by omega
      subst hsj'
      rw [htopA, Finset.mem_singleton] at hX
      subst hX
      have hchild : (atoms s).filter (· ⊆ chargeSupport a) = P.image chargeSupport := by
        ext Y
        simp only [Finset.mem_filter, Finset.mem_image]
        rw [hlow s le_rfl Y]
        constructor
        · rintro ⟨⟨b, hb⟩, -⟩
          rw [hparTop b, Finset.mem_singleton] at hb
          exact ⟨b.1, b.2, hb.symm⟩
        · rintro ⟨b, hb, rfl⟩
          refine ⟨⟨⟨b, hb⟩, ?_⟩, hsubb ⟨b, hb⟩⟩
          rw [hparTop ⟨b, hb⟩]
          exact Finset.mem_singleton_self _
      rw [hchild] at hU hUne' ⊢
      set U' := P.filter fun b => chargeSupport b ∈ U with hU'
      have hU'ne : U'.Nonempty := by
        obtain ⟨Z, hZ⟩ := hUne
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hU hZ)
        exact ⟨b, Finset.mem_filter.mpr ⟨hb, hZ⟩⟩
      have hU'ne' : U' ≠ P := by
        intro hEq
        apply hUne'
        apply Finset.Subset.antisymm hU
        intro Z hZ
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hZ
        rw [← hEq] at hb
        exact (Finset.mem_filter.mp hb).2
      obtain ⟨b, hbU, b', hb'P, hb'U, hdist⟩ :=
        hconn U' (Finset.filter_subset _ _) hU'ne hU'ne'
      refine ⟨chargeSupport b, (Finset.mem_filter.mp hbU).2, chargeSupport b',
        Finset.mem_image_of_mem _ hb'P, ?_, hdist⟩
      intro hmem
      exact hb'U (Finset.mem_filter.mpr ⟨hb'P, hmem⟩)
  · -- neutral
    intro s hs X hX hzero
    have hsj : s ≤ j := by omega
    obtain ⟨b, hb⟩ := (hlow s hsj X).mp hX
    obtain ⟨σ, hσ, hσx⟩ := hsign b.1 b.2
    have hXb := (hin s hsj b X hb).1
    have hzero' : ∑ x ∈ X, b.1 x = 0 := by
      have : ∑ x ∈ X, a x = σ * ∑ x ∈ X, b.1 x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x hx => hσx x (hXb hx)
      rw [this] at hzero
      rcases hσ with rfl | rfl
      · simpa using hzero
      · simpa using hzero
    by_cases hlt : s < j
    · exact (Fb b).neutral s hlt X hb hzero'
    · have : s = j := by omega
      subst this
      rw [hparTop b, Finset.mem_singleton] at hb
      subst hb
      have hfull : ∑ x, b.1 x = 0 := by
        rw [← hzero']
        refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
        simpa [chargeSupport] using hx
      exact hneutral b.1 b.2 hfull

end FroehlichSpencer.BKT

end
