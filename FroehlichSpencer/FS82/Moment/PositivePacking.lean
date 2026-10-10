module

public import FroehlichSpencer.FS82.Moment.Packing
import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Moment.Packing

/-- At every positive integer length, the side-six box cardinality bound divides
by the support size with the same constant 5184. -/
theorem card_le_5184_mul_length_cube_positive
    {I α : Type*} [DecidableEq α]
    (T : Finset I) (S : I → Finset α) (B : Finset α) (L : ℕ)
    (hL : 1 ≤ L)
    (hdisj : (↑T : Set I).PairwiseDisjoint S)
    (hsub : ∀ i ∈ T, S i ⊆ B)
    (hsize : ∀ i ∈ T, (S i).card = L)
    (hbox : B.card ≤ 4 * (6 * L)^4) :
    T.card ≤ 5184 * L^3 := by
  have hmul := FroehlichSpencer.FS82.Moment.Packing.card_mul_le_of_disjoint_supports T S B L hdisj hsub hsize
  have hgeom : 4 * (6 * L)^4 = 5184 * L^4 := by ring
  have hnat : T.card * L ≤ 5184 * L^4 := by
    calc
      T.card * L ≤ B.card := hmul
      _ ≤ 4 * (6 * L)^4 := hbox
      _ = 5184 * L^4 := hgeom
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hL)
  have hcast : (T.card : ℝ) * (L : ℝ) ≤ 5184 * (L : ℝ)^4 := by
    exact_mod_cast hnat
  have hreal : (T.card : ℝ) ≤ 5184 * (L : ℝ)^3 := by
    calc
      (T.card : ℝ) = ((T.card : ℝ) * (L : ℝ)) / (L : ℝ) := by
        field_simp [ne_of_gt hLpos]
      _ ≤ (5184 * (L : ℝ)^4) / (L : ℝ) :=
        div_le_div_of_nonneg_right hcast (le_of_lt hLpos)
      _ = 5184 * (L : ℝ)^3 := by
        field_simp [ne_of_gt hLpos]
  exact_mod_cast hreal

/-- The finite family side-six packing inequality needs only positive support
length. -/
theorem finite_current_packing_l2_side_six_positive
    {I P α : Type*} [DecidableEq I] [DecidableEq α] [Fintype P] [DecidableEq P]
    (T : Finset I) (K : Finset ℕ)
    (support : I → Finset α) (box : P → ℕ → Finset α)
    (plaquette : I → P) (length : I → ℕ)
    (error : I → ℝ) (field : P → ℝ) (activity : ℕ → ℝ) (cpack : ℝ)
    (hlength_mem : ∀ i ∈ T, length i ∈ K)
    (hlength_large : ∀ L ∈ K, 1 ≤ L)
    (hdisj : (↑T : Set I).PairwiseDisjoint support)
    (hsize : ∀ i ∈ T, (support i).card = length i)
    (hlocal : ∀ i ∈ T, support i ⊆ box (plaquette i) (length i))
    (hbox : ∀ p L, (box p L).card ≤ 4 * (6 * L)^4)
    (herror : ∀ i ∈ T, error i ≤ activity (length i) * (field (plaquette i))^2)
    (hactivity : ∀ L ∈ K, 0 ≤ activity L)
    (hbudget : (∑ L ∈ K, 5184 * (L : ℝ)^3 * activity L) ≤ cpack) :
    (∑ i ∈ T, error i) ≤ cpack * (∑ p, (field p)^2) := by
  classical
  let key : I → P × ℕ := fun i => (plaquette i, length i)
  let keys : Finset (P × ℕ) := Finset.univ ×ˢ K
  have hkeys : ∀ i ∈ T, key i ∈ keys := by
    intro i hi
    simp only [keys, Finset.mem_product, Finset.mem_univ, true_and]
    exact hlength_mem i hi
  have hsplit := Finset.sum_fiberwise_of_maps_to hkeys error
  rw [← hsplit]
  rw [Finset.sum_product]
  calc
    (∑ p, ∑ L ∈ K, ∑ i ∈ T with key i = (p, L), error i)
        ≤ ∑ p, ∑ L ∈ K, (5184 * (L : ℝ)^3 * activity L) * (field p)^2 := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro L hL
          let U : Finset I := T.filter (fun i => key i = (p, L))
          have hdisjU : (↑U : Set I).PairwiseDisjoint support := by
            intro i hi j hj hij
            exact hdisj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
          have hsubU : ∀ i ∈ U, support i ⊆ box p L := by
            intro i hi
            obtain ⟨hiT, hiKey⟩ := Finset.mem_filter.mp hi
            have hpEq : plaquette i = p := congrArg Prod.fst hiKey
            have hLEq : length i = L := congrArg Prod.snd hiKey
            simpa [hpEq, hLEq] using hlocal i hiT
          have hsizeU : ∀ i ∈ U, (support i).card = L := by
            intro i hi
            obtain ⟨hiT, hiKey⟩ := Finset.mem_filter.mp hi
            have hLEq : length i = L := congrArg Prod.snd hiKey
            simpa [hLEq] using hsize i hiT
          have hUCard : U.card ≤ 5184 * L^3 :=
            card_le_5184_mul_length_cube_positive U support (box p L) L
              (hlength_large L hL) hdisjU hsubU hsizeU (hbox p L)
          have hsum : (∑ i ∈ U, error i) ≤
              (5184 * (L : ℝ)^3) * activity L * (field p)^2 := by
            calc
              (∑ i ∈ U, error i) ≤ ∑ i ∈ U, activity L * (field p)^2 := by
                apply Finset.sum_le_sum
                intro i hi
                obtain ⟨hiT, hiKey⟩ := Finset.mem_filter.mp hi
                have hpEq : plaquette i = p := congrArg Prod.fst hiKey
                have hLEq : length i = L := congrArg Prod.snd hiKey
                simpa [hpEq, hLEq] using herror i hiT
              _ = (U.card : ℝ) * (activity L * (field p)^2) := by simp
              _ ≤ (5184 * (L : ℝ)^3) * activity L * (field p)^2 := by
                have hUCardR : (U.card : ℝ) ≤ 5184 * (L : ℝ)^3 := by exact_mod_cast hUCard
                calc
                  (U.card : ℝ) * (activity L * (field p)^2)
                      ≤ (5184 * (L : ℝ)^3) * (activity L * (field p)^2) :=
                        mul_le_mul_of_nonneg_right hUCardR
                          (mul_nonneg (hactivity L hL) (sq_nonneg (field p)))
                  _ = (5184 * (L : ℝ)^3) * activity L * (field p)^2 := by ring_nf
          simpa [U, key, mul_assoc] using hsum
    _ ≤ cpack * (∑ p, (field p)^2) := by
          exact (FroehlichSpencer.FS82.Moment.Packing.sum_l2_with_length_budget K field
            (fun L => 5184 * (L : ℝ)^3 * activity L) cpack hbudget)

/-- The positive-length side-six buckets retain exactly the same source
activity constant, with the geometric multiplier `5184/64 = 81` absorbed in
the final coefficient. -/
theorem side_six_activity_budget_le_81_cpack
    (a C : ℝ) (ha : 0 < a) (K : Finset ℕ) :
    (∑ L ∈ K, 5184 * (L : ℝ)^3 * FroehlichSpencer.FS82.Moment.Packing.currentActivity a C L) ≤
      81 * FroehlichSpencer.FS82.Moment.Packing.cpack a C := by
  have hbase := FroehlichSpencer.FS82.Moment.Packing.activity_budget_le_cpack a C ha K
  have hfactor : (∑ L ∈ K, 5184 * (L : ℝ)^3 *
      FroehlichSpencer.FS82.Moment.Packing.currentActivity a C L) =
      81 * (∑ L ∈ K, 64 * (L : ℝ)^3 *
        FroehlichSpencer.FS82.Moment.Packing.currentActivity a C L) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    ring
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hbase (by norm_num)

/-- The source activity tail is already below one half at any positive integer
length when the corrected rate is at least one. -/
theorem activity_z_le_half_positive (a x L z : ℝ)
    (ha : 1 ≤ a) (hx : 0 ≤ x) (hL : 1 ≤ L)
    (hz : z ≤ Real.exp (-(a * (x + L)))) : z ≤ 1 / 2 := by
  have hsum : 1 ≤ x + L := by linarith
  have hprod : 1 ≤ a * (x + L) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (le_trans (by norm_num : (0 : ℝ) ≤ 1) hsum)]
  have harg : -(a * (x + L)) ≤ -1 := by linarith
  have hExp : Real.exp (-(a * (x + L))) ≤ Real.exp (-1) := (Real.exp_le_exp).2 harg
  have hExp1 : 2 ≤ Real.exp (1 : ℝ) := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hfrac : (1 : ℝ) / Real.exp 1 ≤ 1 / 2 :=
    (div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)).2 (by linarith)
  have hnegexp : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa [one_div] using hfrac
  calc
    z ≤ Real.exp (-(a * (x + L))) := hz
    _ ≤ Real.exp (-1) := hExp
    _ ≤ 1 / 2 := hnegexp

/-- Per-current Jensen control with the corrected exponential tail, valid from
length one onward. -/
theorem jensen_per_current_activity_error_positive
    (a C x M z theta : ℝ) (L : ℕ)
    (ha : 0 < a) (ha1 : 1 ≤ a) (hC : 0 ≤ C) (hx : 0 ≤ x) (hM : 0 ≤ M)
    (hz0 : 0 ≤ z)
    (hz : z ≤ Real.exp (-(a * (x + (L : ℝ)))))
    (hL : 1 ≤ L)
    (htheta : |theta| ≤ C * M * x * (L : ℝ)^4) :
    FroehlichSpencer.FS82.Moment.Packing.jensenGamma z * theta^2 ≤ FroehlichSpencer.FS82.Moment.Packing.currentActivity a C L * M^2 := by
  have hsmall : z ≤ 1 / 2 :=
    activity_z_le_half_positive a x (L : ℝ) z ha1 hx (by exact_mod_cast hL) hz
  have hgamma : FroehlichSpencer.FS82.Moment.Packing.jensenGamma z ≤ 5 * z :=
    FroehlichSpencer.FS82.Moment.Packing.jensenGamma_le_five_mul z hz0 hsmall
  exact FroehlichSpencer.FS82.Moment.Packing.per_current_activity_error a C x (L : ℝ) M z
    (FroehlichSpencer.FS82.Moment.Packing.jensenGamma z) theta ha hC hx hM hz hgamma htheta

end FroehlichSpencer.FS82.Moment.Packing
