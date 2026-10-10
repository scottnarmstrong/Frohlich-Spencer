/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawAmplitude
public import FroehlichSpencer.FS82.Wilson.AreaLawRootCount
public import FroehlichSpencer.FS82.Wilson.AreaLawTail
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Connected source activity bound

The positive source-component sum is grouped by its exact finite plaquette
support. The support is rooted at a source link, has size at least the
rectangle area, and has at most `400^k` possibilities per root.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

private theorem dualGaussianSupportSubset_tsum_le {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (supports : Finset (Finset (PrimalPlaquettes B))) :
    (∑' m : {m : PrimalPlaquettes B → ℤ //
      plaquetteFieldSupport m ∈ supports}, dualGaussianProduct β m.1) ≤
      ∑ S ∈ supports, nonzeroGaussianActivity β ^ S.card := by
  classical
  let A := {S : Finset (PrimalPlaquettes B) // S ∈ supports}
  let Fiber (s : A) := {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m = s.1}
  let Y := Σ s : A, Fiber s
  let w : Y → ℝ := fun y => dualGaussianProduct β y.2.1
  let e : {m : PrimalPlaquettes B → ℤ //
      plaquetteFieldSupport m ∈ supports} → Y := fun m =>
    ⟨⟨plaquetteFieldSupport m.1, m.2⟩, ⟨m.1, rfl⟩⟩
  have hinj : Function.Injective e := by
    intro m n h
    apply Subtype.ext
    exact congrArg (fun y : Y => y.2.1) h
  have hwNonneg (y : Y) : 0 ≤ w y := dualGaussianProduct_nonneg β y.2.1
  have hfiber (s : A) : Summable (fun m : Fiber s => w ⟨s, m⟩) := by
    have hgauss := dualGaussianProduct_summable (B := B) β hβ
    exact hgauss.comp_injective (by
      intro m n h
      exact Subtype.ext h)
  have houter : Summable (fun s : A => ∑' m : Fiber s, w ⟨s, m⟩) := by
    exact Summable.of_finite
  have hY : Summable w :=
    (summable_sigma_of_nonneg hwNonneg).2 ⟨hfiber, houter⟩
  have hsubsum :
      (∑' m : {m : PrimalPlaquettes B → ℤ //
        plaquetteFieldSupport m ∈ supports}, dualGaussianProduct β m.1) ≤
        ∑' y : Y, w y := by
    have hfun :
        (fun m : {m : PrimalPlaquettes B → ℤ //
          plaquetteFieldSupport m ∈ supports} => dualGaussianProduct β m.1) =
          w ∘ e := by
      funext m
      rfl
    rw [hfun]
    exact tsum_comp_le_tsum_of_inj hY hwNonneg hinj
  have hdecomp : (∑' y : Y, w y) =
      ∑' s : A, ∑' m : Fiber s, w ⟨s, m⟩ := hY.tsum_sigma
  calc
    _ ≤ ∑' y : Y, w y := hsubsum
    _ = ∑ S ∈ supports, nonzeroGaussianActivity β ^ S.card := by
      calc
        _ = ∑' s : A, ∑' m : Fiber s, w ⟨s, m⟩ := hdecomp
        _ = ∑ s : A, ∑' m : Fiber s, w ⟨s, m⟩ := by
          let inst : Fintype A := Fintype.ofFinite A
          rw [tsum_fintype]
          refine Finset.sum_congr ?_ ?_
          · ext s
            simp
          · intro s hs
            rfl
        _ = ∑ s : A, nonzeroGaussianActivity β ^ s.1.card := by
          apply Finset.sum_congr rfl
          intro s hs
          have hfiberValue :
              (∑' m : Fiber s, w ⟨s, m⟩) =
                nonzeroGaussianActivity β ^ s.1.card := by
            simpa [w, Fiber] using
              dualGaussianProduct_exactSupport_tsum β hβ s.1
          exact hfiberValue
        _ = ∑ S ∈ supports, nonzeroGaussianActivity β ^ S.card := by
          simpa [A] using
            (Finset.sum_coe_sort supports
              (fun S : Finset (PrimalPlaquettes B) =>
                nonzeroGaussianActivity β ^ S.card))

private theorem geometricTail_sum_le {A N : ℕ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range (N + 1), if A ≤ k then r ^ k else 0) ≤
      areaActivityTail r A := by
  classical
  let f : ℕ → ℝ := fun k => if A ≤ k then r ^ k else 0
  have hgeom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr0 hr1
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun k => by
      by_cases hk : A ≤ k
      · simpa [f, hk] using (pow_nonneg hr0 k)
      · simp [f, hk]) (fun k => by
      by_cases hk : A ≤ k
      · simp [f, hk]
      · simpa [f, hk] using (pow_nonneg hr0 k)) hgeom
  have htailEq : (∑' k : ℕ, f k) = areaActivityTail r A := by
    let e : ℕ ≃ {k : ℕ // A ≤ k} := {
      toFun := fun n => ⟨A + n, by omega⟩
      invFun := fun k => k.1 - A
      left_inv := by intro n; simp
      right_inv := by
        intro k
        apply Subtype.ext
        exact Nat.add_sub_of_le k.2 }
    calc
      (∑' k : ℕ, f k) = ∑' k : {k : ℕ // A ≤ k}, r ^ k.1 := by
        calc
          _ = ∑' k : ℕ, ({k : ℕ | A ≤ k}.indicator (fun k => r ^ k)) k := by
            apply tsum_congr
            intro k
            by_cases hk : A ≤ k <;> simp [Set.indicator, hk, f]
          _ = _ := (tsum_subtype {k : ℕ | A ≤ k} (fun k => r ^ k)).symm
      _ = ∑' n : ℕ, r ^ (A + n) := by
        symm
        exact e.tsum_eq (fun k : {k : ℕ // A ≤ k} => r ^ k.1)
      _ = areaActivityTail r A := rfl
  calc
    (∑ k ∈ Finset.range (N + 1), f k) ≤ ∑' k : ℕ, f k :=
      hf.sum_le_tsum (Finset.range (N + 1)) (fun k hk => by
        dsimp [f]
        split_ifs <;> positivity)
    _ = areaActivityTail r A := htailEq

/-- Sum of residual Gaussian activities over all connected source-rooted
supports of size at least the rectangle area. -/
theorem rectangleConnectedSourceActivity_le_tail {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (hA : 1 ≤ L * T)
    (β : ℝ) (hβ : 0 < β) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ Real.exp (-7))
    (hrEq : r = 400 * nonzeroGaussianActivity β) :
    (∑' m : {m : PrimalPlaquettes B → ℤ //
      (∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
        plaquetteFieldSupport m ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteFieldSupport m).card) ∧
      L * T ≤ (plaquetteFieldSupport m).card}, dualGaussianProduct β m.1) ≤
      24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T) := by
  classical
  let roots := rectangleSourceRootPlaquettes L T hL hT
  let supports : Finset (Finset (PrimalPlaquettes B)) :=
    Finset.univ.filter fun S =>
      (L * T) ≤ S.card ∧
        ∃ p ∈ roots, S ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p S.card
  have hallowed (m : {m : PrimalPlaquettes B → ℤ //
      (∃ p ∈ roots,
        plaquetteFieldSupport m ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteFieldSupport m).card) ∧
      L * T ≤ (plaquetteFieldSupport m).card}) :
      plaquetteFieldSupport m.1 ∈ supports := by
    simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m.2.2, m.2.1⟩
  have hsumSupport := dualGaussianSupportSubset_tsum_le β hβ supports
  have hsumCluster :
      (∑' m : {m : PrimalPlaquettes B → ℤ //
        (∃ p ∈ roots,
          plaquetteFieldSupport m ∈
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
              (plaquetteFieldSupport m).card) ∧
        L * T ≤ (plaquetteFieldSupport m).card},
        dualGaussianProduct β m.1) ≤
      ∑' m : {m : PrimalPlaquettes B → ℤ //
        plaquetteFieldSupport m ∈ supports}, dualGaussianProduct β m.1 := by
    have hsummable := dualGaussianProduct_summable (B := B) β hβ
    let target : Type := {m : PrimalPlaquettes B → ℤ //
      plaquetteFieldSupport m ∈ supports}
    let forget : target → (PrimalPlaquettes B → ℤ) := fun m => m.1
    have hforget : Function.Injective forget := by
      intro m n h
      exact Subtype.ext h
    have hsummableTarget : Summable (fun m : target =>
        dualGaussianProduct β m.1) := by
      change Summable (dualGaussianProduct β ∘ forget)
      exact hsummable.comp_injective hforget
    let i : {m : PrimalPlaquettes B → ℤ //
        (∃ p ∈ roots,
          plaquetteFieldSupport m ∈
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
              (plaquetteFieldSupport m).card) ∧
        L * T ≤ (plaquetteFieldSupport m).card} →
        {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m ∈ supports} :=
      fun m => ⟨m.1, hallowed m⟩
    have hi : Function.Injective i := by
      intro m n h
      apply Subtype.ext
      exact congrArg
        (fun z : {m : PrimalPlaquettes B → ℤ //
          plaquetteFieldSupport m ∈ supports} => z.1) h
    have hfun :
        (fun m : {m : PrimalPlaquettes B → ℤ //
          (∃ p ∈ roots,
            plaquetteFieldSupport m ∈
              FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
                (plaquetteFieldSupport m).card) ∧
          L * T ≤ (plaquetteFieldSupport m).card} =>
            dualGaussianProduct β m.1) =
          (fun m => dualGaussianProduct β m.1) ∘ i := by
      funext m
      rfl
    rw [hfun]
    exact tsum_comp_le_tsum_of_inj hsummableTarget
      (fun m : target => dualGaussianProduct_nonneg β m.1) hi
  have hmax (S : Finset (PrimalPlaquettes B)) :
      S.card ≤ Fintype.card (PrimalPlaquettes B) := by
    exact Finset.card_le_card (Finset.subset_univ S)
  let K := Finset.range (Fintype.card (PrimalPlaquettes B) + 1)
  let f : Finset (PrimalPlaquettes B) → ℝ :=
    fun S => nonzeroGaussianActivity β ^ S.card
  have hsumFib := Finset.sum_fiberwise_of_maps_to
    (s := supports) (t := K) (g := fun S => S.card) (f := f)
    (by
      intro S hS
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hmax S)))
  have hsumBounds :
      (∑ k ∈ K, ∑ S ∈ supports with S.card = k, f S) ≤
        ∑ k ∈ K, if L * T ≤ k then
          24 * ((L * T : ℕ) : ℝ) * r ^ k else 0 := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkA : L * T ≤ k
    · have hlevelSubset :
        supports.filter (fun S => S.card = k) ⊆
          (roots.biUnion fun p =>
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p k) := by
        intro S hS
        have hS' := Finset.mem_filter.mp hS
        have hmem := Finset.mem_filter.mp hS'.1
        obtain ⟨p, hp, hanimal⟩ := hmem.2.2
        have hsize : S.card = k := hS'.2
        refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
        simpa [hsize] using hanimal
      have hcount :
          (supports.filter (fun S => S.card = k)).card ≤
            24 * (L * T) * 400 ^ k := by
        exact (Finset.card_le_card hlevelSubset).trans
          (card_rectangleSourceAnimalSupports_le hL hT k (by omega))
      have hconst :
          (∑ S ∈ supports with S.card = k, f S) =
            ((supports.filter (fun S => S.card = k)).card : ℝ) *
              nonzeroGaussianActivity β ^ k := by
        calc
          (∑ S ∈ supports with S.card = k, f S) =
              ∑ S ∈ supports.filter (fun S => S.card = k),
                nonzeroGaussianActivity β ^ k := by
                  apply Finset.sum_congr rfl
                  intro S hS
                  have hsize' := (Finset.mem_filter.mp hS).2
                  simp [f, hsize']
          _ = ((supports.filter (fun S => S.card = k)).card : ℝ) *
                nonzeroGaussianActivity β ^ k := by
                  simp [Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      have hcountR :
          ((supports.filter (fun S => S.card = k)).card : ℝ) ≤
            24 * (L * T : ℕ) * (400 : ℝ) ^ k := by exact_mod_cast hcount
      have htau : 0 ≤ nonzeroGaussianActivity β := by
        unfold nonzeroGaussianActivity
        exact tsum_nonneg fun z => by
          split_ifs <;> positivity
      have hpow : 0 ≤ nonzeroGaussianActivity β ^ k := pow_nonneg htau _
      simp only [ite_eq_left hkA]
      calc
        ((supports.filter (fun S => S.card = k)).card : ℝ) *
            nonzeroGaussianActivity β ^ k ≤
          (24 * (L * T : ℕ) * (400 : ℝ) ^ k) *
            nonzeroGaussianActivity β ^ k :=
              mul_le_mul_of_nonneg_right hcountR hpow
        _ = 24 * ((L * T : ℕ) : ℝ) * r ^ k := by
              rw [hrEq]
              rw [mul_pow]
              ring
    · have hempty : supports.filter (fun S => S.card = k) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (by
          intro S hS
          simp only [supports, Finset.mem_filter, Finset.mem_univ,
            true_and] at hS
          intro heq
          exact hkA (by omega))
      have hzero : (∑ S ∈ supports with S.card = k, f S) = 0 := by
        simp [hempty]
      rw [hzero]
      simp only [ite_eq_right hkA]
      norm_num
  have htauGeometric :
      (∑ S ∈ supports, f S) ≤
        24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T) := by
    rw [← hsumFib]
    calc
      _ ≤ ∑ k ∈ K,
          if L * T ≤ k then 24 * ((L * T : ℕ) : ℝ) * r ^ k else 0 := hsumBounds
      _ = 24 * ((L * T : ℕ) : ℝ) *
            (∑ k ∈ K, if L * T ≤ k then r ^ k else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              split_ifs <;> ring
      _ ≤ 24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact geometricTail_sum_le hr0 (lt_of_le_of_lt hr1
                (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)))
  exact hsumCluster.trans (hsumSupport.trans htauGeometric)

end FroehlichSpencer.FS82.Wilson

end
