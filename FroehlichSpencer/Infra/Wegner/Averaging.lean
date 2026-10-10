/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Wegner.OneSite
public import FroehlichSpencer.Infra.Spectral.Interlacing
public import FroehlichSpencer.Infra.Spectral.Regularity

/-!
# Wegner-type spectral averaging for `A + diagonal (v|_Λ)`

Wegner's estimate (Fröhlich–Spencer (1983), Lemma 2.4 via Appendix C, (C.1)–(C.4),
Fröhlich–Spencer (1983)) for an arbitrary Hermitian matrix `A` on a finite set `Λ`
plus the random diagonal potential `v|_Λ`, `v ∼ productMeasure μ`, with `μ` having a density
bounded by `ρ`: the expected number of eigenvalues in a window of length `ℓ` is at most
`ρ ℓ |Λ|`, and so the probability of an eigenvalue in a window of length `2κ` is at most
`2 κ ρ |Λ|`.
-/

@[expose] public section

open Matrix Finset MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.Infra

/-- Counting eigenvalues in a half-open window (helper; any finite index type). -/
theorem eigenvalueCount_add_card_Ioc {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {a b : ℝ} (hab : a ≤ b) :
    eigenvalueCount hH a + #{i | hH.eigenvalues i ∈ Set.Ioc a b} = eigenvalueCount hH b := by
  rw [eigenvalueCount, eigenvalueCount, ← card_union_of_disjoint]
  · congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and, Set.mem_Ioc]
    constructor
    · rintro (h | h)
      · exact h.trans hab
      · exact h.2
    · intro h
      by_cases hi : hH.eigenvalues i ≤ a
      · exact Or.inl hi
      · exact Or.inr ⟨not_le.mp hi, h⟩
  · rw [disjoint_filter]
    intro i _ h h'
    exact absurd h h'.1.not_ge

section Averaging

variable {ι : Type*} [DecidableEq ι] {Λ : Finset ι} {A : Matrix Λ Λ ℂ}

/-- The eigenvalue count at `E` of `A + diagonal (v|_Λ)`. -/
private noncomputable def cnt (hA : A.IsHermitian) (E : ℝ) (v : ι → ℝ) : ℕ :=
  eigenvalueCount (isHermitian_add_diagonal hA fun x : Λ => v x) E

/-- Partial shift of the configuration by `s` on `S`. -/
private def shiftOn (S : Finset ι) (s : ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun y => if y ∈ S then v y + s else v y

private theorem cnt_congr (hA : A.IsHermitian) (E : ℝ) {v w : ι → ℝ}
    (h : (fun x : Λ => v x) = fun x : Λ => w x) : cnt hA E v = cnt hA E w := by
  have key : ∀ f f' : Λ → ℝ, f = f' → eigenvalueCount (isHermitian_add_diagonal hA f) E =
      eigenvalueCount (isHermitian_add_diagonal hA f') E := fun f f' h => by subst h; rfl
  exact key _ _ h

private theorem measurable_cnt (hA : A.IsHermitian) (E : ℝ) : Measurable (cnt hA E) :=
  measurable_eigenvalueCount (measurable_add_diagonal_comp A (Subtype.val : Λ → ι))
    (fun v => isHermitian_add_diagonal hA fun x : Λ => v x) E

private theorem measurable_shiftOn (S : Finset ι) (s : ℝ) : Measurable (shiftOn S s) :=
  measurable_pi_iff.2 fun i => by
    by_cases hi : i ∈ S
    · simp only [shiftOn, hi, ite_true]
      exact (measurable_pi_apply i : Measurable fun v : ι → ℝ => v i).add_const s
    · simp only [shiftOn, hi, ite_false]
      exact measurable_pi_apply i

private theorem measurable_natSub_cast {α : Type*} [MeasurableSpace α] {f g : α → ℕ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => ((f a - g a : ℕ) : ℝ≥0∞) :=
  ((measurable_from_prod_countable_right (f := fun p : ℕ × ℕ => ((p.1 - p.2 : ℕ) : ℝ≥0∞))
    (fun _ => measurable_of_countable _)).comp (hf.prodMk hg) :)

private theorem shiftOn_empty (s : ℝ) (v : ι → ℝ) : shiftOn ∅ s v = v := by
  funext y; simp [shiftOn]

private theorem shiftOn_insert {x : ι} {S : Finset ι} (s : ℝ) (v : ι → ℝ) :
    shiftOn (insert x S) s v = Function.update (shiftOn S s v) x (v x + s) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [shiftOn]
  · simp [shiftOn, hy]

private theorem shiftOn_update {x : ι} {S : Finset ι} (hx : x ∉ S) (s : ℝ) (v : ι → ℝ) (t : ℝ) :
    shiftOn S s (Function.update v x t) = Function.update (shiftOn S s v) x t := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [shiftOn, hx]
  · simp [shiftOn, hy]

private theorem cnt_update_eq (hA : A.IsHermitian) (E : ℝ) {x : ι} (hx : x ∈ Λ) (w : ι → ℝ)
    (r : ℝ) : cnt hA E (Function.update w x r) =
      eigenvalueCount (isHermitian_add_diagonal hA
        (Function.update (fun y : Λ => w y) ⟨x, hx⟩ r)) E := by
  have key : ∀ f f' : Λ → ℝ, f = f' → eigenvalueCount (isHermitian_add_diagonal hA f) E =
      eigenvalueCount (isHermitian_add_diagonal hA f') E := fun f f' h => by subst h; rfl
  refine key _ _ (funext fun y => ?_)
  by_cases h : y = ⟨x, hx⟩
  · subst h; simp
  · have h' : y.1 ≠ x := fun e => h (Subtype.ext e)
    simp [Function.update_of_ne h, Function.update_of_ne h']

private theorem cnt_update_pair (hA : A.IsHermitian) (E : ℝ) (x : ι) (w : ι → ℝ) {s t : ℝ}
    (hst : s ≤ t) :
    cnt hA E (Function.update w x t) ≤ cnt hA E (Function.update w x s) ∧
      cnt hA E (Function.update w x s) ≤ cnt hA E (Function.update w x t) + 1 := by
  by_cases hx : x ∈ Λ
  · rw [cnt_update_eq hA E hx, cnt_update_eq hA E hx]
    exact eigenvalueCount_update_le A (fun y : Λ => w y) ⟨x, hx⟩ hst _ _ E
  · have : cnt hA E (Function.update w x t) = cnt hA E (Function.update w x s) :=
      cnt_congr hA E (funext fun y => by
        have h' : y.1 ≠ x := fun e => hx (e ▸ y.2)
        simp [Function.update_of_ne h'])
    omega

private theorem cnt_update_anti (hA : A.IsHermitian) (E : ℝ) (x : ι) (w : ι → ℝ) :
    Antitone fun t => cnt hA E (Function.update w x t) :=
  fun _ _ hst => (cnt_update_pair hA E x w hst).1

private theorem cnt_update_jump (hA : A.IsHermitian) (E : ℝ) (x : ι) (w : ι → ℝ) (t t' : ℝ) :
    cnt hA E (Function.update w x t) ≤ cnt hA E (Function.update w x t') + 1 := by
  rcases le_total t t' with h | h
  · exact (cnt_update_pair hA E x w h).2
  · have := (cnt_update_pair hA E x w h).1
    omega

private theorem cnt_shiftOn (hA : A.IsHermitian) (E s : ℝ) (v : ι → ℝ) :
    cnt hA E (shiftOn Λ s v) = cnt hA (E - s) v := by
  have heq : A + diagonal (fun x : Λ => ((shiftOn Λ s v x : ℝ) : ℂ)) =
      (A + diagonal (fun x : Λ => ((v x : ℝ) : ℂ))) + s • (1 : Matrix Λ Λ ℂ) := by
    rw [add_assoc]
    congr 1
    ext i j
    by_cases h : i = j
    · subst h
      simp [shiftOn]
    · simp [h]
  have hHt : ((A + diagonal (fun x : Λ => ((v x : ℝ) : ℂ))) +
      s • (1 : Matrix Λ Λ ℂ)).IsHermitian := heq ▸ isHermitian_add_diagonal hA _
  unfold cnt
  rw [eigenvalueCount_congr (isHermitian_add_diagonal hA _) hHt heq E]
  exact eigenvalueCount_add_smul_one (isHermitian_add_diagonal hA fun x : Λ => v x) s hHt E

private theorem lintegral_cnt_sub_shiftOn_le (hA : A.IsHermitian) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    (E s : ℝ) (S : Finset ι) :
    ∫⁻ v, ((cnt hA E v - cnt hA E (shiftOn S s v) : ℕ) : ℝ≥0∞) ∂productMeasure μ ≤
      ρ * ENNReal.ofReal s * S.card := by
  induction S using Finset.induction_on with
  | empty => simp [shiftOn_empty]
  | @insert x S hx ih =>
    have hm1 : Measurable fun v : ι → ℝ => ((cnt hA E v - cnt hA E (shiftOn S s v) : ℕ) : ℝ≥0∞) :=
      measurable_natSub_cast (measurable_cnt hA E)
        ((measurable_cnt hA E).comp (measurable_shiftOn S s))
    have hone := lintegral_natSub_update_add_le (ι := ι) μ hμ hg
      (F := fun v => cnt hA E (shiftOn S s v))
      ((measurable_cnt hA E).comp (measurable_shiftOn S s)) x
      (fun v => by
        simp only [shiftOn_update hx]
        exact cnt_update_anti hA E x _)
      (fun v t t' => by
        simp only [shiftOn_update hx]
        exact cnt_update_jump hA E x _ t t') s
    simp only [shiftOn_update hx, ← shiftOn_insert] at hone
    calc ∫⁻ v, ((cnt hA E v - cnt hA E (shiftOn (insert x S) s v) : ℕ) : ℝ≥0∞)
            ∂productMeasure μ
        ≤ ∫⁻ v, (((cnt hA E v - cnt hA E (shiftOn S s v) : ℕ) : ℝ≥0∞) +
            ((cnt hA E (shiftOn S s v) - cnt hA E (shiftOn (insert x S) s v) : ℕ) : ℝ≥0∞))
            ∂productMeasure μ := by
          refine lintegral_mono fun v => ?_
          have := tsub_le_tsub_add_tsub (a := cnt hA E v) (b := cnt hA E (shiftOn S s v))
            (c := cnt hA E (shiftOn (insert x S) s v))
          rw [← Nat.cast_add]
          exact Nat.cast_le.2 this
      _ = ∫⁻ v, ((cnt hA E v - cnt hA E (shiftOn S s v) : ℕ) : ℝ≥0∞) ∂productMeasure μ +
          ∫⁻ v, ((cnt hA E (shiftOn S s v) - cnt hA E (shiftOn (insert x S) s v) : ℕ) : ℝ≥0∞)
            ∂productMeasure μ := lintegral_add_left hm1 _
      _ ≤ ρ * ENNReal.ofReal s * S.card + ρ * ENNReal.ofReal s := add_le_add ih hone
      _ = ρ * ENNReal.ofReal s * (insert x S).card := by
          rw [card_insert_of_notMem hx]; push_cast; ring

/-- **Wegner-type averaged counting bound**, general window `(a, b]`. -/
theorem lintegral_eigenvalueCount_add_diagonal_sub_le (hA : A.IsHermitian) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    (a b : ℝ) :
    ∫⁻ v : ι → ℝ, ((eigenvalueCount (isHermitian_add_diagonal hA fun x : Λ => v x) b -
        eigenvalueCount (isHermitian_add_diagonal hA fun x : Λ => v x) a : ℕ) : ℝ≥0∞)
        ∂productMeasure μ ≤ ρ * ENNReal.ofReal (b - a) * Λ.card := by
  have h := lintegral_cnt_sub_shiftOn_le hA μ hμ hg b (b - a) Λ
  simp only [cnt_shiftOn, sub_sub_cancel] at h
  exact h

private theorem measurableSet_exists_mem_Ioc (hA : A.IsHermitian) (a b : ℝ) :
    MeasurableSet {v : ι → ℝ |
      ∃ i, (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i ∈ Set.Ioc a b} := by
  have : {v : ι → ℝ | ∃ i, (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i ∈
      Set.Ioc a b} = ⋃ i, (fun v : ι → ℝ =>
        (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i) ⁻¹' Set.Ioc a b := by
    ext v; simp
  rw [this]
  exact MeasurableSet.iUnion fun i =>
    measurable_eigenvalues (measurable_add_diagonal_comp A (Subtype.val : Λ → ι))
      (fun v => isHermitian_add_diagonal hA fun x : Λ => v x) i measurableSet_Ioc

private theorem measure_exists_mem_Ioc_le (hA : A.IsHermitian) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    (a b : ℝ) :
    productMeasure μ {v : ι → ℝ |
        ∃ i, (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i ∈ Set.Ioc a b} ≤
      ρ * ENNReal.ofReal (b - a) * Λ.card := by
  refine le_trans ?_ (lintegral_eigenvalueCount_add_diagonal_sub_le hA μ hμ hg a b)
  rw [← lintegral_indicator_one (measurableSet_exists_mem_Ioc hA a b)]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ {v : ι → ℝ |
      ∃ i, (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i ∈ Set.Ioc a b}
  · rw [Set.indicator_of_mem hv]
    obtain ⟨i, hi⟩ := hv
    have hab : a ≤ b := hi.1.le.trans hi.2
    have h := eigenvalueCount_add_card_Ioc (isHermitian_add_diagonal hA fun x : Λ => v x) hab
    have hpos : 0 < #{j | (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues j ∈
        Set.Ioc a b} := card_pos.mpr ⟨i, by simpa using hi⟩
    have : 1 ≤ eigenvalueCount (isHermitian_add_diagonal hA fun x : Λ => v x) b -
        eigenvalueCount (isHermitian_add_diagonal hA fun x : Λ => v x) a := by omega
    show (1 : ℝ≥0∞) ≤ _
    exact_mod_cast this
  · rw [Set.indicator_of_notMem hv]
    exact zero_le


theorem lintegral_eigenvalueCount_window_le (hA : A.IsHermitian) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    (E κ : ℝ) :
    ∫⁻ v : ι → ℝ, ((eigenvalueCount (isHermitian_add_diagonal hA fun x : Λ => v x) (E + κ) -
        eigenvalueCount (isHermitian_add_diagonal hA fun x : Λ => v x) (E - κ) : ℕ) : ℝ≥0∞)
        ∂productMeasure μ ≤ ρ * ENNReal.ofReal (2 * κ) * Λ.card := by
  have h := lintegral_eigenvalueCount_add_diagonal_sub_le hA μ hμ hg (E - κ) (E + κ)
  have e : E + κ - (E - κ) = 2 * κ := by ring
  rwa [e] at h

/-- Probability of an eigenvalue in the half-open window `(E - κ, E + κ]`. -/
theorem productMeasure_exists_eigenvalues_mem_Ioc_le (hA : A.IsHermitian) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    (E κ : ℝ) :
    productMeasure μ {v : ι → ℝ |
        ∃ i, (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i ∈
          Set.Ioc (E - κ) (E + κ)} ≤
      ρ * ENNReal.ofReal (2 * κ) * Λ.card := by
  have h := measure_exists_mem_Ioc_le hA μ hμ hg (E - κ) (E + κ)
  have e : E + κ - (E - κ) = 2 * κ := by ring
  rwa [e] at h

/-- Open window: `dist(spec H(v), E) < κ`. -/
theorem productMeasure_exists_abs_eigenvalues_sub_lt_le (hA : A.IsHermitian) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    (E κ : ℝ) :
    productMeasure μ {v : ι → ℝ |
        ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| < κ} ≤
      ρ * ENNReal.ofReal (2 * κ) * Λ.card := by
  refine le_trans (measure_mono ?_)
    (productMeasure_exists_eigenvalues_mem_Ioc_le hA μ hμ hg E κ)
  rintro v ⟨i, hi⟩
  rw [abs_lt] at hi
  exact ⟨i, by linarith only [hi.1], by linarith only [hi.2]⟩

private theorem exists_mul_ofReal_card_le {ρ : ℝ≥0∞} (hρ : ρ ≠ ⊤) (c : ℕ) {ε : NNReal}
    (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ρ * ENNReal.ofReal δ * c ≤ ε := by
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  set r : ℝ := ρ.toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hpos : 0 < r * c + 1 := by positivity
  refine ⟨(ε : ℝ) / (r * c + 1), by positivity, ?_⟩
  have hρ' : ρ = ENNReal.ofReal r := (ENNReal.ofReal_toReal hρ).symm
  calc ρ * ENNReal.ofReal ((ε : ℝ) / (r * c + 1)) * c
      = ENNReal.ofReal (r * ((ε : ℝ) / (r * c + 1)) * c) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ← hρ']
    _ ≤ ENNReal.ofReal (ε : ℝ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : r * ((ε : ℝ) / (r * c + 1)) * c = ε * (r * c / (r * c + 1)) := by
          field_simp
        rw [e]
        have : r * c / (r * c + 1) ≤ 1 := (div_le_one hpos).2 (by linarith only)
        exact (mul_le_mul_of_nonneg_left this hε'.le).trans_eq (mul_one _)
    _ = ε := ENNReal.ofReal_coe_nnreal

/-- Closed window (FS83 (C.1): `dist(spec H(v), E) ≤ κ`); needs `ρ ≠ ⊤` for the limit `ε → 0`. -/
theorem productMeasure_exists_abs_eigenvalues_sub_le_le (hA : A.IsHermitian) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ) (hρ : ρ ≠ ⊤)
    (E κ : ℝ) :
    productMeasure μ {v : ι → ℝ |
        ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ} ≤
      ρ * ENNReal.ofReal (2 * κ) * Λ.card := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ, hsmall⟩ := exists_mul_ofReal_card_le hρ Λ.card hε
  calc productMeasure μ {v : ι → ℝ |
        ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ}
      ≤ ρ * ENNReal.ofReal ((E + κ) - (E - κ - δ)) * Λ.card := by
        refine le_trans (measure_mono ?_)
          (measure_exists_mem_Ioc_le hA μ hμ hg (E - κ - δ) (E + κ))
        rintro v ⟨i, hi⟩
        rw [abs_le] at hi
        exact ⟨i, by linarith only [hi.1, hδ], by linarith only [hi.2]⟩
    _ ≤ ρ * (ENNReal.ofReal (2 * κ) + ENNReal.ofReal δ) * Λ.card := by
        gcongr
        have e : (E + κ) - (E - κ - δ) = 2 * κ + δ := by ring
        rw [e]
        exact ENNReal.ofReal_add_le
    _ = ρ * ENNReal.ofReal (2 * κ) * Λ.card + ρ * ENNReal.ofReal δ * Λ.card := by ring
    _ ≤ _ := add_le_add_right hsmall _

end Averaging

end FroehlichSpencer.Infra
