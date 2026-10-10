module

public import FroehlichSpencer.FS82.Infinite.LimitStateLaw
public import FroehlichSpencer.FS82.Infinite.LimitStateCompactness

@[expose] public section

open Filter Topology

namespace FroehlichSpencer.FS82.Infinite

theorem pmf_map_apply_toReal {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β] [DecidableEq β]
    (p : PMF α) (f : α → β) (y : β) :
    ((p.map f) y).toReal = ∑' x, if y = f x then (p x).toReal else 0 := by
  classical
  rw [PMF.map_apply]
  rw [ENNReal.tsum_toReal_eq]
  · congr 1
    funext x
    split_ifs <;> simp
  · intro x
    split_ifs <;> simp [p.apply_ne_top]

private theorem pmf_toReal_tsum {α : Type*} [Countable α] (p : PMF α) :
    ∑' x, (p x).toReal = 1 := by
  have h := ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x)
  rw [p.tsum_coe] at h
  simpa using h.symm

private theorem pmf_toReal_summable {α : Type*} [Countable α] (p : PMF α) :
    Summable (fun x => (p x).toReal) := by
  apply ENNReal.summable_toReal
  rw [p.tsum_coe]
  exact ENNReal.one_ne_top

/-- Pointwise convergence of probability masses, together with finite-set
tightness, is preserved by a map of countable discrete spaces. -/
theorem pmf_map_apply_tendsto_of_tight
    {α β : Type*} [Countable α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable β] [DecidableEq β]
    [MeasurableSpace β] [MeasurableSingletonClass β] (pn : ℕ → PMF α) (p : PMF α) (f : α → β) (y : β)
    (hpoint : ∀ x, Tendsto (fun n => (pn n x).toReal) atTop
      (𝓝 ((p x).toReal)))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ S : Finset α, ∀ n,
      1 - ε ≤ ∑ x ∈ S, (pn n x).toReal) :
    Tendsto (fun n => ((pn n).map f y).toReal) atTop
      (𝓝 ((p.map f y).toReal)) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  let ε := δ / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨S, hS⟩ := htight ε hε
  have hfinite : Tendsto (fun n => ∑ x ∈ S, (pn n x).toReal) atTop
      (𝓝 (∑ x ∈ S, (p x).toReal)) := by
    apply tendsto_finsetSum
    intro x hx
    exact hpoint x
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hfinite ε hε
  have hlimitMass : 1 - ε ≤ ∑ x ∈ S, (p x).toReal :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hfinite (fun n => hS n)
  have hpTailEq := (pmf_toReal_summable p).sum_add_tsum_subtype_compl S
  rw [pmf_toReal_tsum p] at hpTailEq
  have hpTail : ∑' x : {x // x ∉ S}, (p x.1).toReal ≤ ε := by linarith
  have hpnTail (n : ℕ) :
      ∑' x : {x // x ∉ S}, (pn n x.1).toReal ≤ ε := by
    have hdecomp := (pmf_toReal_summable (pn n)).sum_add_tsum_subtype_compl S
    rw [pmf_toReal_tsum (pn n)] at hdecomp
    linarith [hS n]
  let w (n : ℕ) (x : α) : ℝ := if y = f x then (pn n x).toReal else 0
  let wlim (x : α) : ℝ := if y = f x then (p x).toReal else 0
  have hw_nonneg (n : ℕ) (x : α) : 0 ≤ w n x := by
    simp only [w]
    split_ifs <;> positivity
  have hw_le (n : ℕ) (x : α) : w n x ≤ (pn n x).toReal := by
    simp only [w]
    split_ifs <;> simp [ENNReal.toReal_nonneg]
  have hwlim_nonneg (x : α) : 0 ≤ wlim x := by
    simp only [wlim]
    split_ifs <;> positivity
  have hwlim_le (x : α) : wlim x ≤ (p x).toReal := by
    simp only [wlim]
    split_ifs <;> simp [ENNReal.toReal_nonneg]
  have hmapSummable (n : ℕ) : Summable (w n) :=
    Summable.of_nonneg_of_le (fun x => hw_nonneg n x) (fun x => hw_le n x)
      (pmf_toReal_summable (pn n))
  have hlimSummable : Summable wlim :=
    Summable.of_nonneg_of_le hwlim_nonneg hwlim_le (pmf_toReal_summable p)
  have hpartial : Tendsto (fun n => ∑ x ∈ S, w n x) atTop
      (𝓝 (∑ x ∈ S, wlim x)) := by
    apply tendsto_finsetSum
    intro x hx
    by_cases hy : y = f x
    · simpa [w, wlim, hy] using hpoint x
    · simp [w, wlim, hy]
  obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.mp hpartial ε hε
  have hfiberTail (n : ℕ) :
      ∑' x : {x // x ∉ S}, w n x.1 ≤ ε := by
    have hsubW := (hmapSummable n).subtype (fun x => x ∉ S)
    have hsubP := (pmf_toReal_summable (pn n)).subtype (fun x => x ∉ S)
    have hle := Summable.tsum_le_tsum
      (fun x : {x // x ∉ S} => hw_le n x.1) hsubW hsubP
    exact hle.trans (hpnTail n)
  have hfiberTailLim :
      ∑' x : {x // x ∉ S}, wlim x.1 ≤ ε := by
    have hsubW := hlimSummable.subtype (fun x => x ∉ S)
    have hsubP := (pmf_toReal_summable p).subtype (fun x => x ∉ S)
    have hle := Summable.tsum_le_tsum
      (fun x : {x // x ∉ S} => hwlim_le x.1) hsubW hsubP
    exact hle.trans hpTail
  have hdecomp (n : ℕ) :
      ((pn n).map f y).toReal = (∑ x ∈ S, w n x) +
        ∑' x : {x // x ∉ S}, w n x.1 := by
    rw [pmf_map_apply_toReal]
    have h := (hmapSummable n).sum_add_tsum_subtype_compl S
    simpa [w] using h.symm
  have hdecompLim :
      ((p.map f y).toReal) = (∑ x ∈ S, wlim x) +
        ∑' x : {x // x ∉ S}, wlim x.1 := by
    rw [pmf_map_apply_toReal]
    have h := hlimSummable.sum_add_tsum_subtype_compl S
    simpa [wlim] using h.symm
  have htailNNonneg (n : ℕ) : 0 ≤ ∑' x : {x // x ∉ S}, w n x.1 :=
    tsum_nonneg (fun x => hw_nonneg n x.1)
  have htailLimNonneg : 0 ≤ ∑' x : {x // x ∉ S}, wlim x.1 :=
    tsum_nonneg (fun x => hwlim_nonneg x.1)
  refine ⟨max n₀ n₁, fun n hn => ?_⟩
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : n₁ ≤ n := le_trans (le_max_right _ _) hn
  rw [Real.dist_eq, hdecomp n, hdecompLim]
  calc
    |(∑ x ∈ S, w n x) + ∑' x : {x // x ∉ S}, w n x.1 -
        ((∑ x ∈ S, wlim x) + ∑' x : {x // x ∉ S}, wlim x.1)|
      ≤ |(∑ x ∈ S, w n x) - ∑ x ∈ S, wlim x| +
        |(∑' x : {x // x ∉ S}, w n x.1) -
          ∑' x : {x // x ∉ S}, wlim x.1| := by
            rw [show (∑ x ∈ S, w n x) + (∑' x : {x // x ∉ S}, w n x.1) -
                ((∑ x ∈ S, wlim x) + (∑' x : {x // x ∉ S}, wlim x.1)) =
                ((∑ x ∈ S, w n x) - ∑ x ∈ S, wlim x) +
                ((∑' x : {x // x ∉ S}, w n x.1) -
                  ∑' x : {x // x ∉ S}, wlim x.1) by ring]
            exact abs_add_le _ _
    _ ≤ ε + ε := by
      have hfiniteClose : |(∑ x ∈ S, w n x) - ∑ x ∈ S, wlim x| < ε := by
        simpa [Real.dist_eq] using hn₁ n hn1
      have htailClose : |(∑' x : {x // x ∉ S}, w n x.1) -
          ∑' x : {x // x ∉ S}, wlim x.1| ≤ ε := by
        rw [abs_le]
        constructor <;> linarith [hfiberTail n, hfiberTailLim,
          htailNNonneg n, htailLimNonneg]
      exact add_le_add (le_of_lt hfiniteClose) htailClose
    _ < δ := by dsimp [ε]; linarith

/-- A subsequential thermodynamic-limit state in the local integer curvature
coordinates. -/
structure CubeCurvatureLimitState (β : ℝ) (hβ : 0 < β) where
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  law : (P : Finset GlobalIntegerPlaquette) → PMF (P → ℤ)
  pointwise : ∀ P x, Tendsto
    (fun k => (cubeCurvaturePMFTotal (subsequence k) β hβ P x).toReal) atTop
    (𝓝 ((law P x).toReal))
  consistent : ∀ (P₀ P₁ : Finset GlobalIntegerPlaquette) (hP : P₀ ⊆ P₁),
    PMF.map (restrictCurvature hP) (law P₁) = law P₀

/-- The cube curvature laws have a common pointwise-convergent subsequence.
The limiting cylinder PMFs are consistent under restriction. -/
theorem exists_cubeCurvatureLimitState (β : ℝ) (hβ : 0 < β) :
    Nonempty (CubeCurvatureLimitState β hβ) := by
  classical
  let laws : ℕ → (P : Finset GlobalIntegerPlaquette) → PMF (P → ℤ) :=
    fun N P => cubeCurvaturePMFTotal N β hβ P
  have htight : ∀ (P : Finset GlobalIntegerPlaquette) (ε : ℝ), 0 < ε →
      ∃ S : Finset (P → ℤ), ∀ N,
        1 - ε ≤ ∑ x ∈ S, ((laws N P) x).toReal := by
    intro P ε hε
    exact cubeCurvaturePMFTotal_uniform_tight β hβ P ε hε
  obtain ⟨s, hs, limits, hconv, hpmf⟩ :=
    exists_subseq_cylinderPMF laws htight
  let ν : (P : Finset GlobalIntegerPlaquette) → PMF (P → ℤ) :=
    fun P => Classical.choose (hpmf P)
  have hν (P : Finset GlobalIntegerPlaquette) (x : P → ℤ) :
      ν P x = ENNReal.ofReal (cylinderLimitValue limits ⟨P, x⟩) :=
    Classical.choose_spec (hpmf P) x
  have hpoint (P : Finset GlobalIntegerPlaquette) (x : P → ℤ) :
      Tendsto (fun k => ((laws (s k) P) x).toReal) atTop (𝓝 ((ν P x).toReal)) := by
    have hpi := (tendsto_pi_nhds.mp hconv)
      (show CylinderIndex GlobalIntegerPlaquette from ⟨P, x⟩)
    have hval := continuous_subtype_val.continuousAt.tendsto.comp hpi
    change Tendsto (fun k => ((laws (s k) P) x).toReal) atTop
      (𝓝 (cylinderLimitValue limits ⟨P, x⟩)) at hval
    rw [hν]
    rw [ENNReal.toReal_ofReal (cylinderLimitValue_nonneg limits ⟨P, x⟩)]
    exact hval
  have hconsistent (P₀ P₁ : Finset GlobalIntegerPlaquette)
      (hP : P₀ ⊆ P₁) :
      PMF.map (restrictCurvature hP) (ν P₁) = ν P₀ := by
    ext y
    have hmapPoint :
        Tendsto (fun k =>
          ((cubeCurvaturePMFTotal (s k) β hβ P₁).map (restrictCurvature hP) y).toReal)
          atTop (𝓝 ((PMF.map (restrictCurvature hP) (ν P₁) y).toReal)) := by
      apply pmf_map_apply_tendsto_of_tight
      · intro x
        exact hpoint P₁ x
      · intro ε hε
        obtain ⟨S, hS⟩ := cubeCurvaturePMFTotal_uniform_tight β hβ P₁ ε hε
        exact ⟨S, fun k => hS (s k)⟩
    have hsmallPoint :
        Tendsto (fun k => (cubeCurvaturePMFTotal (s k) β hβ P₀ y).toReal)
          atTop (𝓝 ((ν P₀ y).toReal)) := hpoint P₀ y
    obtain ⟨N₀, hN₀⟩ :=
      cubeCurvaturePMFTotal_eventually_consistent β hβ P₀ P₁ hP
    have hsLower (k : ℕ) : k ≤ s k := by
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih =>
          have hlt : s k < s (Nat.succ k) := hs (Nat.lt_succ_self k)
          exact le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt hlt)
    have hevent : ∀ᶠ k in atTop,
        ((cubeCurvaturePMFTotal (s k) β hβ P₁).map (restrictCurvature hP) y).toReal =
          (cubeCurvaturePMFTotal (s k) β hβ P₀ y).toReal := by
      filter_upwards [eventually_atTop.2 ⟨N₀, fun k hk => hk⟩] with k hk
      rw [hN₀ (s k) (le_trans hk (hsLower k))]
    have heventRev : ∀ᶠ k in atTop,
        (cubeCurvaturePMFTotal (s k) β hβ P₀ y).toReal =
          ((cubeCurvaturePMFTotal (s k) β hβ P₁).map (restrictCurvature hP) y).toReal := by
      filter_upwards [hevent] with k hk
      exact hk.symm
    have hmapAsSmall :
        Tendsto (fun k => (cubeCurvaturePMFTotal (s k) β hβ P₀ y).toReal)
          atTop (𝓝 ((PMF.map (restrictCurvature hP) (ν P₁) y).toReal)) :=
      Tendsto.congr' hevent hmapPoint
    have hreal := tendsto_nhds_unique hmapAsSmall hsmallPoint
    have hmass : PMF.map (restrictCurvature hP) (ν P₁) y = ν P₀ y := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
      exact hreal
    exact hmass
  exact ⟨⟨s, hs, ν, hpoint, hconsistent⟩⟩

end FroehlichSpencer.FS82.Infinite

