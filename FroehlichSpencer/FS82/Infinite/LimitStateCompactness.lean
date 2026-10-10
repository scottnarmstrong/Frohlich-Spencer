module

public import FroehlichSpencer.FS82.Infinite.CubeExhaustion
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

open Set Filter Topology

set_option linter.style.haveILetI false

namespace FroehlichSpencer.FS82.Infinite

universe u

/-- A cylinder is a finite plaquette set and an integer assignment on it. -/
abbrev CylinderIndex (α : Type u) := Σ P : Finset α, P → ℤ

noncomputable def cylinderProbVector {α : Type u} [DecidableEq α]
    (laws : ℕ → (P : Finset α) → PMF (P → ℤ)) (n : ℕ) :
    CylinderIndex α → Set.Icc (0 : ℝ) 1 := fun i => by
  let r := ((laws n i.1) i.2).toReal
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (ENNReal.toReal_le_toReal ((laws n i.1).apply_ne_top i.2) ENNReal.one_ne_top).2
      ((laws n i.1).coe_le_one i.2)
  exact ⟨r, hr0, hr1⟩

def cylinderLimitValue {α : Type u} (v : CylinderIndex α → Set.Icc (0 : ℝ) 1)
    (i : CylinderIndex α) : ℝ := (v i).val

 theorem cylinderLimitValue_nonneg {α : Type u} (v : CylinderIndex α → Set.Icc (0 : ℝ) 1)
    (i : CylinderIndex α) : 0 ≤ cylinderLimitValue v i := (v i).property.1

theorem cylinderLimitValue_le_one {α : Type u} (v : CylinderIndex α → Set.Icc (0 : ℝ) 1)
    (i : CylinderIndex α) : cylinderLimitValue v i ≤ 1 := (v i).property.2

/-- Countably many cylinder probabilities have a pointwise convergent
subsequence. Uniform tightness ensures that each limiting cylinder still has
mass one. -/
theorem exists_subseq_cylinderPMF
    {α : Type u} [Countable α] [DecidableEq α]
    (laws : ℕ → (P : Finset α) → PMF (P → ℤ))
    (htight : ∀ (P : Finset α) (ε : ℝ), 0 < ε →
      ∃ s : Finset (P → ℤ), ∀ n,
        1 - ε ≤ ∑ x ∈ s, ((laws n P) x).toReal) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∃ limits : CylinderIndex α → Set.Icc (0 : ℝ) 1,
        Tendsto (fun k => cylinderProbVector laws (s k)) atTop (𝓝 limits) ∧
        ∀ P : Finset α, ∃ ν : PMF (P → ℤ),
          (∀ x, ν x = ENNReal.ofReal (cylinderLimitValue limits ⟨P, x⟩)) := by
  classical
  let I := CylinderIndex α
  have hcount : Countable I := by infer_instance
  letI : Countable I := hcount
  let X : I → Type := fun _ => Set.Icc (0 : ℝ) 1
  let K : Set (∀ i : I, X i) := Set.univ
  have hcompact : IsCompact K := isCompact_univ
  letI : FirstCountableTopology (∀ i : I, X i) :=
    TopologicalSpace.instFirstCountableTopologyForallOfCountable
  have hseq : IsSeqCompact K := hcompact.isSeqCompact
  let f : ℕ → ∀ i : I, X i := fun n => cylinderProbVector laws n
  have hmem : ∀ n, f n ∈ K := fun _ => Set.mem_univ _
  obtain ⟨v, hv, s, hs, hconv⟩ := hseq hmem
  refine ⟨s, hs, v, ?_, ?_⟩
  · exact hconv
  · intro P
    let r : (P → ℤ) → ℝ := fun x => cylinderLimitValue v ⟨P, x⟩
    let q : (P → ℤ) → ENNReal := fun x => ENNReal.ofReal (r x)
    have hpoint (x : P → ℤ) :
        Tendsto (fun k => ((laws (s k) P) x).toReal) atTop (𝓝 (r x)) := by
      have hpi := (tendsto_pi_nhds.mp hconv) (show I from ⟨P, x⟩)
      have hval := continuous_subtype_val.continuousAt.tendsto.comp hpi
      change Tendsto (fun k => ((laws (s k) P) x).toReal) atTop
        (𝓝 ((v ⟨P, x⟩).val)) at hval
      exact hval
    have hr_nonneg (x : P → ℤ) : 0 ≤ r x := cylinderLimitValue_nonneg v ⟨P, x⟩
    have hr_le (x : P → ℤ) : r x ≤ 1 := cylinderLimitValue_le_one v ⟨P, x⟩
    have hsum_le (s₀ : Finset (P → ℤ)) : ∑ x ∈ s₀, q x ≤ 1 := by
      have hconvsum : Tendsto (fun k => ∑ x ∈ s₀, ((laws (s k) P) x).toReal)
          atTop (𝓝 (∑ x ∈ s₀, r x)) := by
        apply tendsto_finsetSum
        intro x hx
        exact hpoint x
      have hbound : ∀ k, ∑ x ∈ s₀, ((laws (s k) P) x).toReal ≤ 1 := by
        intro k
        have hsum : ∑ x ∈ s₀, (laws (s k) P) x ≤ 1 := by
          calc
            _ ≤ ∑' x, (laws (s k) P) x := ENNReal.sum_le_tsum s₀
            _ = 1 := PMF.tsum_coe _
        have hsumtop : (∑ x ∈ s₀, (laws (s k) P) x) ≠ ⊤ := by
          have ht : ∑ x ∈ s₀, (laws (s k) P) x ≤ 1 := hsum
          exact ne_of_lt (lt_of_le_of_lt ht ENNReal.one_lt_top)
        rw [← ENNReal.toReal_sum (fun x hx => (laws (s k) P).apply_ne_top x)]
        exact (ENNReal.toReal_le_toReal hsumtop ENNReal.one_ne_top).2 hsum
      have hlim : (∑ x ∈ s₀, r x) ≤ 1 :=
        le_of_tendsto_of_tendsto' hconvsum tendsto_const_nhds hbound
      have hsum_ofReal : ∑ x ∈ s₀, q x = ENNReal.ofReal (∑ x ∈ s₀, r x) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun x hx => hr_nonneg x)]
      rw [hsum_ofReal]
      simpa using ENNReal.ofReal_le_ofReal hlim
    have hqsum_le : ∑' x, q x ≤ 1 := by
      rw [ENNReal.tsum_eq_iSup_sum]
      apply iSup_le
      intro s₀
      exact hsum_le s₀
    have hqsum_toReal : (∑' x, q x).toReal = ∑' x, r x := by
      rw [ENNReal.tsum_toReal_eq (fun x => by simp [q])]
      congr 1
      funext x
      simp [q, r, hr_nonneg x]
    have hqsum_ne_top : (∑' x, q x) ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hqsum_le ENNReal.one_lt_top)
    have hqsum_real_le : (∑' x, r x) ≤ 1 := by
      rw [← hqsum_toReal]
      have h := (ENNReal.toReal_le_toReal hqsum_ne_top ENNReal.one_ne_top).2 hqsum_le
      simpa [hqsum_toReal] using h
    have hqsum_real_ge : 1 ≤ (∑' x, q x).toReal := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨s₀, hs₀⟩ := htight P (ε/2) (by linarith)
      have hconvsum : Tendsto (fun k => ∑ x ∈ s₀, ((laws (s k) P) x).toReal)
          atTop (𝓝 (∑ x ∈ s₀, r x)) := by
        apply tendsto_finsetSum
        intro x hx
        exact hpoint x
      have hlow : 1 - ε/2 ≤ ∑ x ∈ s₀, r x := by
        apply le_of_tendsto_of_tendsto' tendsto_const_nhds hconvsum
        intro k
        exact hs₀ (s k)
      have hsum_ofReal : ∑ x ∈ s₀, q x = ENNReal.ofReal (∑ x ∈ s₀, r x) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun x hx => hr_nonneg x)]
      have hlower : ENNReal.ofReal (1 - ε/2) ≤ ∑ x ∈ s₀, q x := by
        rw [hsum_ofReal]
        exact ENNReal.ofReal_le_ofReal hlow
      have hbelow : ENNReal.ofReal (1 - ε/2) ≤ ∑' x, q x :=
        le_trans hlower (ENNReal.sum_le_tsum s₀)
      have hrealbelow := (ENNReal.ofReal_le_iff_le_toReal hqsum_ne_top).1 hbelow
      linarith
    have hqsum_real_eq : (∑' x, r x) = 1 := le_antisymm hqsum_real_le (by
      rw [← hqsum_toReal]
      exact hqsum_real_ge)
    have hqsum_real_eq_one : (∑' x, q x).toReal = 1 := by
      rw [hqsum_toReal]
      exact hqsum_real_eq
    have hqsum_eq : ∑' x, q x = 1 :=
      (ENNReal.toReal_eq_toReal_iff' hqsum_ne_top ENNReal.one_ne_top).1 hqsum_real_eq_one
    refine ⟨⟨q, ?_⟩, ?_⟩
    · rw [ENNReal.summable.hasSum_iff]
      exact hqsum_eq
    · intro x
      rfl

end FroehlichSpencer.FS82.Infinite
