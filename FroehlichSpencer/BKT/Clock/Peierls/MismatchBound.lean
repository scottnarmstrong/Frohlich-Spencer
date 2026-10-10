/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ActiveContour
public import FroehlichSpencer.BKT.Clock.Peierls.ClockReduction
public import FroehlichSpencer.BKT.Clock.Peierls.ContourRemoval
public import FroehlichSpencer.BKT.Clock.Peierls.FiniteUnionBound
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # A uniform Peierls bound for finite clock boxes -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.Infra

/-- The endpoint mismatch event in a finite free clock box is small whenever the Peierls
activity, multiplied by the degree-six animal growth, is at most 1/100. -/
theorem clockMismatchRatio_le_quarter_of_small_activity
    (n L R : ℕ) (hn : 2 ≤ n) (hRL : R ≤ L) (_hR : 1 ≤ R)
    (β : ℝ) (hβ : 0 ≤ β)
    (hq : 36 * (n : ℝ) * Real.exp (-(β * clockEnergyGap n)) ≤ 1 / 100) :
    let a : RotatorSpinSite L := clockBoxOrigin L
    let b : RotatorSpinSite L := (⟨R, by omega⟩, ⟨0, by omega⟩)
    clockMismatchWeight n L β a b / clockBoxPartitionSum n L β ≤ 1 / 4 := by
  classical
  let thisNeZero : NeZero n := ⟨by omega⟩
  let a : RotatorSpinSite L := clockBoxOrigin L
  let b : RotatorSpinSite L := (⟨R, by omega⟩, ⟨0, by omega⟩)
  let E := Lattice2D.SquareFreeEdge (L + 1)
  let G := clockPeierlsAdjacencyGraph (L + 1)
  let J := {j : ℕ // j ∈ Finset.Icc 1 R}
  let thisJ : Fintype J := Fintype.ofFinset (Finset.Icc 1 R) (fun _ => Iff.rfl)
  let K := Fintype.card E
  let A : Finset (RotatorSpinSite L → Fin n) :=
    Finset.univ.filter fun σ => σ a ≠ σ b
  let pIndex : J → Fin R := fun j =>
    ⟨j.val - 1, by
      have hj := Finset.mem_Icc.mp j.property
      omega⟩
  let Z := clockBoxPartitionSum n L β
  let activity := (n : ℝ) * Real.exp (-(β * clockEnergyGap n))
  let q := 36 * activity
  let Index := (J × Fin K) × Finset E
  let thisIndex : Fintype Index := inferInstance
  let events : Index → Finset (RotatorSpinSite L → Fin n) := fun ix =>
    if clockPeierlsMinContourSize R L ix.1.1.val ≤ ix.1.2.val + 1 ∧
        ix.2 ∈ animals G (clockPeierlsPathEdge hRL (pIndex ix.1.1))
          (ix.1.2.val + 1) then
      clockContourEvent n L ix.2
    else ∅
  have hZ : 0 < Z := by
    exact clockBoxPartitionSum_pos n L (by omega) β
  have hZnonneg : 0 ≤ Z := hZ.le
  have hactivity : 0 ≤ activity := by
    dsimp [activity]
    positivity
  have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
  have hAweight : clockMismatchWeight n L β a b =
      ∑ σ ∈ A, clockBoxWeight n L β σ := by
    unfold clockMismatchWeight
    rw [Finset.sum_filter]
  have hcover : ∀ σ ∈ A, ∃ ix : Index, σ ∈ events ix := by
    intro σ hσA
    have hneq : σ a ≠ σ b := (Finset.mem_filter.mp hσA).2
    have htotal : clockPeierlsPathFlux (clockConfigurationField σ)
        (clockPeierlsPathEdge hRL) ≠ 0 := by
      rw [clockPeierlsPathFlux_eq_horizontalSegmentSum hRL,
        clockConfigurationSegmentSum_eq_endpoints σ 0 0 R (by omega) (by omega)]
      apply sub_ne_zero.mpr
      intro hEq
      apply hneq
      exact (ZMod.finEquiv n).injective (by
        simpa [clockConfigurationZMod, a, b, clockBoxOrigin] using hEq)
    obtain ⟨c, hcflux, i, hiroot⟩ := exists_componentFlux_ne_zero_of_pathFlux_ne_zero
      G (clockConfigurationField σ) (clockPeierlsPathEdge hRL) htotal
    let S := clockPeierlsComponentSupport G (clockConfigurationField σ) c
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨clockPeierlsPathEdge hRL i, hiroot⟩
    have hScard : S.card ≤ K := by
      dsimp [K, E]
      exact Finset.card_le_univ S
    let knat := S.card - 1
    have hknat : knat + 1 = S.card := by dsimp [knat]; omega
    have hklt : knat < K := by omega
    let j : J := ⟨i.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    let k : Fin K := ⟨knat, hklt⟩
    have hactive : clockPeierlsMinContourSize R L j.val ≤ k.val + 1 := by
      have hsize := clockPeierlsComponent_minContourSize_le
        (R := R) (M := L) (n := n) hRL σ i c hcflux hiroot
      simpa [j, k, knat, hknat] using hsize
    have hroot : clockPeierlsPathEdge hRL (pIndex j) ∈ S := by
      simpa [j, pIndex, S] using hiroot
    have hSanim : S ∈ animals G (clockPeierlsPathEdge hRL (pIndex j)) (k.val + 1) := by
      have hanim := clockPeierlsComponentSupport_mem_animals
        (clockPeierlsAdjacencyGraph (L + 1)) (clockConfigurationField σ) c hroot
      simpa [S, k, hknat] using hanim
    have hSbad : ∀ e ∈ S, clockConfigurationField σ e ≠ 0 := by
      intro e he
      exact (mem_clockPeierlsComponentSupport_iff G (clockConfigurationField σ) c e).mp he |>.1
    have hSsat := clockPeierlsComponentSupport_squareSaturated σ c
    have hevent : σ ∈ clockContourEvent n L S := by
      unfold clockContourEvent
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hSbad, by simpa [S] using hSsat⟩
    refine ⟨((j, k), S), ?_⟩
    simpa [events, hactive, hSanim] using hevent
  have hWnonneg : ∀ σ : RotatorSpinSite L → Fin n, 0 ≤ clockBoxWeight n L β σ :=
    fun σ => (clockBoxWeight_pos n L β σ).le
  have hunion := weightedFinset_union_bound A events (clockBoxWeight n L β)
    hcover hWnonneg
  have hsum_animals (j : J) (k : Fin K) :
      (∑ S : Finset E, ∑ σ ∈ events ((j, k), S), clockBoxWeight n L β σ) ≤
        (if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
          q ^ (k.val + 1) * Z else 0) := by
    let T := animals G (clockPeierlsPathEdge hRL (pIndex j)) (k.val + 1)
    let active := clockPeierlsMinContourSize R L j.val ≤ k.val + 1
    let B := activity ^ (k.val + 1) * Z
    have hpoint (S : Finset E) :
        (∑ σ ∈ events ((j, k), S), clockBoxWeight n L β σ) ≤
          if active ∧ S ∈ T then B else 0 := by
      by_cases hcond : active ∧ S ∈ T
      · have hcard : S.card = k.val + 1 :=
          ((FroehlichSpencer.Infra.mem_animals G).mp hcond.2).2.1
        let thisEvent : Fintype {σ // σ ∈ clockContourEvent n L S} :=
          Fintype.ofFinset (clockContourEvent n L S) (fun _ => Iff.rfl)
        have hfix := clockContourEvent_weight_le n L hn β hβ S hcard
        have hfix' : (∑ σ ∈ clockContourEvent n L S, clockBoxWeight n L β σ) ≤
            activity ^ (k.val + 1) * Z := by
          calc
            _ = ∑ σ ∈ (clockContourEvent n L S).attach,
                  clockBoxWeight n L β σ.1 :=
              (Finset.sum_attach (clockContourEvent n L S) (clockBoxWeight n L β)).symm
            _ ≤ _ := by simpa [activity, Z] using hfix
        simpa [events, T, active, B, hcond] using hfix'
      · simp [events, T, active, hcond]
    have hsumPoint :
        (∑ S : Finset E, ∑ σ ∈ events ((j, k), S), clockBoxWeight n L β σ) ≤
          ∑ S : Finset E, if active ∧ S ∈ T then B else 0 := by
      apply Finset.sum_le_sum
      intro S _
      exact hpoint S
    have hanimBoundNat : T.card ≤ 6 ^ (2 * k.val) := by
      dsimp [T]
      have hbound := clockPeierlsAdjacencyGraph_card_animals_le (L + 1)
        (clockPeierlsPathEdge hRL (pIndex j)) (k.val + 1)
      simpa using hbound
    have hanimBound : (T.card : ℝ) ≤ (36 : ℝ) ^ k.val := by
      calc
        (T.card : ℝ) ≤ ((6 : ℕ) ^ (2 * k.val) : ℕ) := by exact_mod_cast hanimBoundNat
        _ = (36 : ℝ) ^ k.val := by
          push_cast
          rw [pow_mul]
          norm_num
    have hfactor : (36 : ℝ) ^ k.val * activity ^ (k.val + 1) ≤ q ^ (k.val + 1) := by
      have hpow : (36 : ℝ) ^ k.val * activity ^ k.val =
          ((36 : ℝ) * activity) ^ k.val := by rw [← mul_pow]
      have hle : activity ≤ (36 : ℝ) * activity := by nlinarith [hactivity]
      calc
        (36 : ℝ) ^ k.val * activity ^ (k.val + 1) =
            activity * ((36 : ℝ) ^ k.val * activity ^ k.val) := by rw [pow_succ]; ring
        _ = activity * ((36 : ℝ) * activity) ^ k.val := by rw [hpow]
        _ ≤ ((36 : ℝ) * activity) * ((36 : ℝ) * activity) ^ k.val :=
          mul_le_mul_of_nonneg_right hle
            (pow_nonneg (mul_nonneg (by norm_num) hactivity) _)
        _ = q ^ (k.val + 1) := by dsimp [q]; rw [pow_succ]; ring
    have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
    by_cases hactive : active
    · have hrhs : (∑ S : Finset E, if active ∧ S ∈ T then B else 0) =
          (T.card : ℝ) * B := by
        calc
          _ = ∑ S ∈ (Finset.univ : Finset (Finset E)),
                if S ∈ T then B else 0 := by simp [hactive]
          _ = ∑ S ∈ Finset.univ ∩ T, B :=
            Finset.sum_ite_mem Finset.univ T (fun _ => B)
          _ = (T.card : ℝ) * B := by simp [nsmul_eq_mul]
      calc
        _ ≤ ∑ S : Finset E, if active ∧ S ∈ T then B else 0 := hsumPoint
        _ = (T.card : ℝ) * B := hrhs
        _ ≤ (36 : ℝ) ^ k.val * activity ^ (k.val + 1) * Z := by
          dsimp [B]
          have hcardweight : (T.card : ℝ) * activity ^ (k.val + 1) ≤
              (36 : ℝ) ^ k.val * activity ^ (k.val + 1) :=
            mul_le_mul_of_nonneg_right hanimBound (pow_nonneg hactivity _)
          calc
            (T.card : ℝ) * (activity ^ (k.val + 1) * Z) =
                ((T.card : ℝ) * activity ^ (k.val + 1)) * Z := by ring
            _ ≤ ((36 : ℝ) ^ k.val * activity ^ (k.val + 1)) * Z :=
              mul_le_mul_of_nonneg_right hcardweight hZnonneg
            _ = (36 : ℝ) ^ k.val * activity ^ (k.val + 1) * Z := by ring
        _ ≤ q ^ (k.val + 1) * Z := mul_le_mul_of_nonneg_right hfactor hZnonneg
        _ = if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
              q ^ (k.val + 1) * Z else 0 := by simp [active, hactive]
    · have hrhs : (∑ S : Finset E, if active ∧ S ∈ T then B else 0) = 0 := by
        simp [hactive]
      calc
        _ ≤ ∑ S : Finset E, if active ∧ S ∈ T then B else 0 := hsumPoint
        _ = 0 := hrhs
        _ = if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
              q ^ (k.val + 1) * Z else 0 := by simp [active, hactive]
  have hunionBound : (∑ ix : Index, ∑ σ ∈ events ix, clockBoxWeight n L β σ) ≤
      ∑ j : J, ∑ k : Fin K,
        if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
          q ^ (k.val + 1) * Z else 0 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    exact hsum_animals j k
  have hseries : (∑ j : J, ∑ k : Fin K,
      if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
        q ^ (k.val + 1) else 0) ≤ 1 / 4 := by
    have hJsum : (∑ j : J, ∑ k : Fin K,
        if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
          q ^ (k.val + 1) else 0) =
      ∑ j ∈ Finset.Icc 1 R, ∑ k : Fin K,
        if clockPeierlsMinContourSize R L j ≤ k.val + 1 then
          q ^ (k.val + 1) else 0 := by
      symm
      exact Finset.sum_subtype (Finset.Icc 1 R) (fun _ => Iff.rfl)
        (fun j => ∑ k : Fin K,
          if clockPeierlsMinContourSize R L j ≤ k.val + 1 then q ^ (k.val + 1) else 0)
    rw [hJsum]
    have hKsum (j : ℕ) :
        (∑ k : Fin K, if clockPeierlsMinContourSize R L j ≤ k.val + 1 then
          q ^ (k.val + 1) else 0) =
        ∑ k ∈ Finset.range K,
          if clockPeierlsMinContourSize R L j ≤ k + 1 then q ^ (k + 1) else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun k =>
        if clockPeierlsMinContourSize R L j ≤ k + 1 then q ^ (k + 1) else 0) K]
    simp_rw [hKsum]
    have hqsmall : q ≤ 1 / 100 := by
      dsimp [q, activity]
      nlinarith [hq]
    exact clockPeierlsContourSeries_partial_le_quarter R L K hRL q hqnonneg hqsmall
  have haggregate :
      (∑ ix : Index, ∑ σ ∈ events ix, clockBoxWeight n L β σ) ≤ Z / 4 := by
    calc
      _ ≤ ∑ j : J, ∑ k : Fin K,
            if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
              q ^ (k.val + 1) * Z else 0 := hunionBound
      _ = (∑ j : J, ∑ k : Fin K,
            if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
              q ^ (k.val + 1) else 0) * Z := by
        have hterm (j : J) (k : Fin K) :
            (if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
                q ^ (k.val + 1) * Z else 0) =
              (if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
                q ^ (k.val + 1) else 0) * Z := by
          by_cases h : clockPeierlsMinContourSize R L j.val ≤ k.val + 1 <;> simp [h]
        simp_rw [hterm]
        let f : J → Fin K → ℝ := fun j k =>
          if clockPeierlsMinContourSize R L j.val ≤ k.val + 1 then
            q ^ (k.val + 1) else 0
        change (∑ j : J, ∑ k : Fin K, f j k * Z) =
          (∑ j : J, ∑ k : Fin K, f j k) * Z
        calc
          _ = ∑ j : J, (∑ k : Fin K, f j k) * Z := by
            apply Finset.sum_congr rfl
            intro j _
            exact (map_sum (AddMonoidHom.mulRight Z) (fun k : Fin K => f j k)
              Finset.univ).symm
          _ = _ := (map_sum (AddMonoidHom.mulRight Z)
              (fun j : J => ∑ k : Fin K, f j k) Finset.univ).symm
      _ ≤ (1 / 4) * Z := mul_le_mul_of_nonneg_right hseries hZnonneg
      _ = Z / 4 := by ring
  have hmisbound : clockMismatchWeight n L β a b ≤ Z / 4 := by
    rw [hAweight]
    exact hunion.trans haggregate
  change clockMismatchWeight n L β a b / Z ≤ 1 / 4
  exact (div_le_iff₀ hZ).2 (by nlinarith)

end FroehlichSpencer.BKT.Clock.Peierls

end
