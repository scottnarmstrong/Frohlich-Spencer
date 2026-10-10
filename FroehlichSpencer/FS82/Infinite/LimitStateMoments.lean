module

public import FroehlichSpencer.FS82.Infinite.LimitStateLimit

@[expose] public section

open Filter Topology MeasureTheory

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

private theorem pmf_real_mass_tsum {α : Type*} [Countable α] (p : PMF α) :
    ∑' x, (p x).toReal = 1 := by
  have h := ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x)
  rw [p.tsum_coe] at h
  simpa using h.symm

private theorem pmf_real_mass_summable {α : Type*} [Countable α] (p : PMF α) :
    Summable (fun x => (p x).toReal) := by
  apply ENNReal.summable_toReal
  rw [p.tsum_coe]
  exact ENNReal.one_ne_top

private theorem young_linear_sq {d x : ℝ} (hd : 0 < d) :
    x ≤ d * x ^ 2 + 1 / (4 * d) := by
  have hs : 0 ≤ (2 * d * x - 1) ^ 2 := sq_nonneg _
  have hmul : (4 * d) * x ≤ 4 * d * d * x ^ 2 + 1 := by nlinarith [hs]
  have hmul' : (4 * d) * x ≤ (4 * d) * (d * x ^ 2 + 1 / (4 * d)) := by
    calc
      _ ≤ 4 * d * d * x ^ 2 + 1 := hmul
      _ = _ := by field_simp [hd.ne']
  exact le_of_mul_le_mul_left hmul' (by positivity)

/-- Second moment bounds pass to a pointwise limit of PMFs by finite
truncation. -/
theorem pmf_secondMoment_bound_of_pointwise
    {α : Type*} [Countable α] [DecidableEq α]
    (pn : ℕ → PMF α) (p : PMF α) (f : α → ℝ) (C : ℝ)
    (hpoint : ∀ x, Tendsto (fun n => (pn n x).toReal) atTop
      (𝓝 ((p x).toReal)))
    (hsq : ∀ n, Summable (fun x => (pn n x).toReal * (f x) ^ 2))
    (hsqBound : ∀ n, ∑' x, (pn n x).toReal * (f x) ^ 2 ≤ C) :
    Summable (fun x => (p x).toReal * (f x) ^ 2) ∧
      ∑' x, (p x).toReal * (f x) ^ 2 ≤ C := by
  classical
  have hfinite (S : Finset α) :
      ∑ x ∈ S, (p x).toReal * (f x) ^ 2 ≤ C := by
    have hconv : Tendsto
        (fun n => ∑ x ∈ S, (pn n x).toReal * (f x) ^ 2) atTop
        (𝓝 (∑ x ∈ S, (p x).toReal * (f x) ^ 2)) := by
      apply tendsto_finsetSum
      intro x hx
      exact (hpoint x).mul_const ((f x) ^ 2)
    have hbound : ∀ n, ∑ x ∈ S, (pn n x).toReal * (f x) ^ 2 ≤ C := by
      intro n
      exact ((hsq n).sum_le_tsum S (fun x hx => by positivity)).trans (hsqBound n)
    exact le_of_tendsto_of_tendsto' hconv tendsto_const_nhds hbound
  have hsummable : Summable (fun x => (p x).toReal * (f x) ^ 2) :=
    summable_of_sum_le (fun x => by positivity) hfinite
  exact ⟨hsummable, hsummable.tsum_le_of_sum_le hfinite⟩

/-- A second moment bound gives a uniform-integrability tail estimate:
the expectation of f above R is at most C divided by R. -/
theorem pmf_weighted_tsum_largeTail_le
    {α : Type*} [Countable α] (p : PMF α) (f : α → ℝ) (C R : ℝ)
    (hnonneg : ∀ x, 0 ≤ f x) (hR : 0 < R)
    (hsq : Summable (fun x => (p x).toReal * (f x) ^ 2))
    (hsqBound : ∑' x, (p x).toReal * (f x) ^ 2 ≤ C) :
    ∑' x, (p x).toReal * (if R ≤ f x then f x else 0) ≤ C / R := by
  classical
  let g : α → ℝ := fun x => (p x).toReal * (if R ≤ f x then f x else 0)
  let q : α → ℝ := fun x => (p x).toReal * (f x) ^ 2
  have hpointwise (x : α) : g x ≤ q x / R := by
    by_cases h : R ≤ f x
    · have hmul : R * f x ≤ (f x) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right h (hnonneg x)]
      have hmass : 0 ≤ (p x).toReal := ENNReal.toReal_nonneg
      simp [g, q, h]
      apply (le_div_iff₀ hR).2
      have hmul' := mul_le_mul_of_nonneg_left hmul hmass
      nlinarith [hmul']
    · simp [g, q, h]
      positivity
  have hdom : Summable (fun x => q x / R) := by
    simpa [q, div_eq_mul_inv] using hsq.mul_right R⁻¹
  have hg0 (x : α) : 0 ≤ g x := by
    dsimp [g]
    have hp : 0 ≤ (p x).toReal := ENNReal.toReal_nonneg
    split_ifs with h
    · exact mul_nonneg hp (hnonneg x)
    · simp
  have hgsum : Summable g := Summable.of_nonneg_of_le hg0 hpointwise hdom
  have hle := Summable.tsum_le_tsum hpointwise hgsum hdom
  calc
    ∑' x, (p x).toReal * (if R ≤ f x then f x else 0) = ∑' x, g x := by rfl
    _ ≤ ∑' x, q x / R := hle
    _ = (∑' x, q x) / R := by rw [tsum_div_const]
    _ ≤ C / R := div_le_div_of_nonneg_right hsqBound hR.le


/-- Under pointwise convergence and tightness, a uniformly bounded second
moment makes expectations of every nonnegative observable converge. -/
theorem pmf_weighted_tsum_tendsto_of_tight_secondMoment
    {α : Type*} [Countable α] [DecidableEq α]
    (pn : ℕ → PMF α) (p : PMF α) (f : α → ℝ) (C : ℝ)
    (hpoint : ∀ x, Tendsto (fun n => (pn n x).toReal) atTop
      (𝓝 ((p x).toReal)))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ S : Finset α, ∀ n,
      1 - ε ≤ ∑ x ∈ S, (pn n x).toReal)
    (hnonneg : ∀ x, 0 ≤ f x)
    (hsq : ∀ n, Summable (fun x => (pn n x).toReal * (f x) ^ 2))
    (hsqBound : ∀ n, ∑' x, (pn n x).toReal * (f x) ^ 2 ≤ C) :
    Tendsto (fun n => ∑' x, (pn n x).toReal * f x) atTop
      (𝓝 (∑' x, (p x).toReal * f x)) := by
  classical
  have hlimSq := pmf_secondMoment_bound_of_pointwise pn p f C hpoint hsq hsqBound
  have hmassSummable (n : ℕ) := pmf_real_mass_summable (pn n)
  have hmassLimSummable := pmf_real_mass_summable p
  have hYoung (x : α) : f x ≤ 1 + (f x) ^ 2 := by
    nlinarith [sq_nonneg (f x - 1 / 2)]
  have hweightSummable (n : ℕ) :
      Summable (fun x => (pn n x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (hnonneg x))
    · intro x
      have hm := ENNReal.toReal_nonneg (a := pn n x)
      have hh := mul_le_mul_of_nonneg_left (hYoung x) hm
      simpa [mul_add] using hh
    · exact (hmassSummable n).add (hsq n)
  have hweightLimSummable : Summable (fun x => (p x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (hnonneg x))
    · intro x
      have hm := ENNReal.toReal_nonneg (a := p x)
      have hh := mul_le_mul_of_nonneg_left (hYoung x) hm
      simpa [mul_add] using hh
    · exact hmassLimSummable.add hlimSq.1
  have hCnonneg : 0 ≤ C := by
    have h : 0 ≤ ∑' x : α, (pn 0 x).toReal * (f x) ^ 2 :=
      tsum_nonneg (fun x => mul_nonneg ENNReal.toReal_nonneg
        (sq_nonneg (f x)))
    exact le_trans h (hsqBound 0)
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  let d := δ / (8 * (C + 1))
  let ε := d * δ / 8
  have hd : 0 < d := by dsimp [d]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨S, hS⟩ := htight ε hε
  have hmassConv : Tendsto (fun n => ∑ x ∈ S, (pn n x).toReal) atTop
      (𝓝 (∑ x ∈ S, (p x).toReal)) := by
    apply tendsto_finsetSum
    intro x hx
    exact hpoint x
  have hlimitMass : 1 - ε ≤ ∑ x ∈ S, (p x).toReal :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hmassConv (fun n => hS n)
  have hpMassTailEq := hmassLimSummable.sum_add_tsum_subtype_compl S
  rw [pmf_real_mass_tsum p] at hpMassTailEq
  have hpMassTail : ∑' x : {x // x ∉ S}, (p x.1).toReal ≤ ε := by
    linarith
  have hpnMassTail (n : ℕ) :
      ∑' x : {x // x ∉ S}, (pn n x.1).toReal ≤ ε := by
    have hdecomp := (hmassSummable n).sum_add_tsum_subtype_compl S
    rw [pmf_real_mass_tsum (pn n)] at hdecomp
    linarith [hS n]
  have hpartial : Tendsto
      (fun n => ∑ x ∈ S, (pn n x).toReal * f x) atTop
      (𝓝 (∑ x ∈ S, (p x).toReal * f x)) := by
    apply tendsto_finsetSum
    intro x hx
    exact (hpoint x).mul_const (f x)
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hpartial (δ / 2) (by linarith)
  have htailBound (n : ℕ) :
      ∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1 ≤
        d * C + (1 / (4 * d)) * ε := by
    let q : α → ℝ := fun x => (pn n x).toReal * f x ^ 2
    let m : α → ℝ := fun x => (pn n x).toReal
    let u : α → ℝ := fun x => (pn n x).toReal * f x
    have hqSub := (hsq n).subtype (fun x => x ∉ S)
    have hmSub := (hmassSummable n).subtype (fun x => x ∉ S)
    have huSub := (hweightSummable n).subtype (fun x => x ∉ S)
    have hdom1 := hqSub.mul_left d
    have hdom2 := hmSub.mul_left (1 / (4 * d))
    have hdom := hdom1.add hdom2
    have hpointwise (x : {x // x ∉ S}) :
        u x.1 ≤ d * q x.1 + (1 / (4 * d)) * m x.1 := by
      have hy := young_linear_sq (d := d) (x := f x.1) hd
      have hm0 : 0 ≤ m x.1 := by dsimp [m]; positivity
      have hh := mul_le_mul_of_nonneg_left (hy) hm0
      dsimp [u, q, m]
      nlinarith
    have hcmp := Summable.tsum_le_tsum hpointwise huSub hdom
    have hdomTsum :
        (∑' x : {x // x ∉ S}, (d * q x.1 +
          (1 / (4 * d)) * m x.1)) =
        (d * (∑' x : {x // x ∉ S}, q x.1) +
          (1 / (4 * d)) * (∑' x : {x // x ∉ S}, m x.1)) := by
      calc
        _ = (∑' x : {x // x ∉ S}, d * q x.1) +
            (∑' x : {x // x ∉ S}, (1 / (4 * d)) * m x.1) := by
              simpa [q, m] using (hdom1.tsum_add hdom2)
        _ = _ := by rw [tsum_mul_left, tsum_mul_left]
    have hqTail : ∑' x : {x // x ∉ S}, q x.1 ≤ C := by
      have hle := Summable.tsum_subtype_le
        (fun x => (pn n x).toReal * f x ^ 2) {x | x ∉ S}
        (fun x => by positivity) (hsq n)
      exact hle.trans (hsqBound n)
    calc
      ∑' x : {x // x ∉ S}, u x.1 ≤
          (∑' x : {x // x ∉ S}, (d * q x.1 +
            (1 / (4 * d)) * m x.1)) := hcmp
      _ = (d * (∑' x : {x // x ∉ S}, q x.1) +
          (1 / (4 * d)) * (∑' x : {x // x ∉ S}, m x.1)) := hdomTsum
      _ ≤ d * C + (1 / (4 * d)) * ε := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hqTail hd.le)
          (mul_le_mul_of_nonneg_left (hpnMassTail n) (by positivity))
  have htailBoundLim :
      ∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1 ≤
        d * C + (1 / (4 * d)) * ε := by
    let q : α → ℝ := fun x => (p x).toReal * f x ^ 2
    let m : α → ℝ := fun x => (p x).toReal
    let u : α → ℝ := fun x => (p x).toReal * f x
    have hqSub := (hlimSq.1).subtype (fun x => x ∉ S)
    have hmSub := hmassLimSummable.subtype (fun x => x ∉ S)
    have huSub := hweightLimSummable.subtype (fun x => x ∉ S)
    have hdom1 := hqSub.mul_left d
    have hdom2 := hmSub.mul_left (1 / (4 * d))
    have hdom := hdom1.add hdom2
    have hpointwise (x : {x // x ∉ S}) :
        u x.1 ≤ d * q x.1 + (1 / (4 * d)) * m x.1 := by
      have hy := young_linear_sq (d := d) (x := f x.1) hd
      have hm0 : 0 ≤ m x.1 := by dsimp [m]; positivity
      have hh := mul_le_mul_of_nonneg_left (hy) hm0
      dsimp [u, q, m]
      nlinarith
    have hcmp := Summable.tsum_le_tsum hpointwise huSub hdom
    have hdomTsum :
        (∑' x : {x // x ∉ S}, (d * q x.1 +
          (1 / (4 * d)) * m x.1)) =
        (d * (∑' x : {x // x ∉ S}, q x.1) +
          (1 / (4 * d)) * (∑' x : {x // x ∉ S}, m x.1)) := by
      calc
        _ = (∑' x : {x // x ∉ S}, d * q x.1) +
            (∑' x : {x // x ∉ S}, (1 / (4 * d)) * m x.1) := by
              simpa [q, m] using (hdom1.tsum_add hdom2)
        _ = _ := by rw [tsum_mul_left, tsum_mul_left]
    have hqTail : ∑' x : {x // x ∉ S}, q x.1 ≤ C := by
      have hle := Summable.tsum_subtype_le
        (fun x => (p x).toReal * f x ^ 2) {x | x ∉ S}
        (fun x => by positivity) hlimSq.1
      exact hle.trans hlimSq.2
    calc
      ∑' x : {x // x ∉ S}, u x.1 ≤
          (∑' x : {x // x ∉ S}, (d * q x.1 +
            (1 / (4 * d)) * m x.1)) := hcmp
      _ = (d * (∑' x : {x // x ∉ S}, q x.1) +
          (1 / (4 * d)) * (∑' x : {x // x ∉ S}, m x.1)) := hdomTsum
      _ ≤ d * C + (1 / (4 * d)) * ε := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hqTail hd.le)
          (mul_le_mul_of_nonneg_left hpMassTail (by positivity))
  have hweightDecomp (n : ℕ) :
      ∑' x, (pn n x).toReal * f x =
        (∑ x ∈ S, (pn n x).toReal * f x) +
          ∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1 :=
    (hweightSummable n).sum_add_tsum_subtype_compl S |>.symm
  have hweightDecompLim :
      ∑' x, (p x).toReal * f x =
        (∑ x ∈ S, (p x).toReal * f x) +
          ∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1 :=
    hweightLimSummable.sum_add_tsum_subtype_compl S |>.symm
  have hdC : d * C < δ / 8 := by
    change (δ / (8 * (C + 1))) * C < δ / 8
    have hden : 0 < 8 * (C + 1) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    field_simp
    nlinarith [hCnonneg]
  have hkε : (1 / (4 * d)) * ε = δ / 32 := by
    dsimp [ε]
    field_simp [hd.ne']
    ring
  have hA : d * C + (1 / (4 * d)) * ε < δ / 4 := by
    rw [hkε]
    linarith
  have htailClose (n : ℕ) :
      |(∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1) -
        ∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1| ≤
          d * C + (1 / (4 * d)) * ε := by
    have htailNNonneg :
        0 ≤ ∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1 :=
      tsum_nonneg (fun x => mul_nonneg ENNReal.toReal_nonneg (hnonneg x.1))
    have htailLNonneg :
        0 ≤ ∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1 :=
      tsum_nonneg (fun x => mul_nonneg ENNReal.toReal_nonneg (hnonneg x.1))
    rw [abs_le]
    constructor <;> linarith [htailBound n, htailBoundLim,
      htailNNonneg, htailLNonneg]
  refine ⟨n₀, fun n hn => ?_⟩
  have hpartClose : |(∑ x ∈ S, (pn n x).toReal * f x) -
      ∑ x ∈ S, (p x).toReal * f x| < δ / 2 := by
    simpa [Real.dist_eq] using hn₀ n hn
  rw [Real.dist_eq, hweightDecomp n, hweightDecompLim]
  calc
    |(∑ x ∈ S, (pn n x).toReal * f x) +
        ∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1 -
        ((∑ x ∈ S, (p x).toReal * f x) +
          ∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1)|
      ≤ |(∑ x ∈ S, (pn n x).toReal * f x) -
          ∑ x ∈ S, (p x).toReal * f x| +
        |(∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1) -
          ∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1| := by
            rw [show (∑ x ∈ S, (pn n x).toReal * f x) +
                (∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1) -
                ((∑ x ∈ S, (p x).toReal * f x) +
                  (∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1)) =
                ((∑ x ∈ S, (pn n x).toReal * f x) -
                  ∑ x ∈ S, (p x).toReal * f x) +
                ((∑' x : {x // x ∉ S}, (pn n x.1).toReal * f x.1) -
                  ∑' x : {x // x ∉ S}, (p x.1).toReal * f x.1) by ring]
            exact abs_add_le _ _
    _ < δ / 2 + (d * C + (1 / (4 * d)) * ε) := by
      exact add_lt_add_of_lt_of_le hpartClose (htailClose n)
    _ < δ := by linarith [hA]


/-- Jensen's inequality for a nonempty finite index set gives an exponential
of a finite sum below the sum of the exponentials with cardinality-scaled
arguments. -/
theorem finite_exp_sum_le_sum_exp_scaled {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → ℝ) :
    Real.exp (∑ i, y i) ≤ ∑ i, Real.exp ((Fintype.card ι : ℝ) * y i) := by
  let m : ℝ := Fintype.card ι
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hweights : ∑ i : ι, m⁻¹ = 1 := by
    simp [m, hm.ne']
  have hj : Real.exp (∑ i : ι, m⁻¹ * (m * y i)) ≤
      ∑ i : ι, m⁻¹ * Real.exp (m * y i) := by
    simpa only [smul_eq_mul] using
      convexOn_exp.map_sum_le (t := Finset.univ)
        (p := fun i : ι => m * y i) (w := fun _ : ι => m⁻¹)
        (by intro i hi; positivity) hweights
        (by intro i hi; exact Set.mem_univ _)
  have hleft : (∑ i : ι, m⁻¹ * (m * y i)) = ∑ i, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hm.ne']
  have hright : (∑ i : ι, m⁻¹ * Real.exp (m * y i)) ≤
      ∑ i, Real.exp (m * y i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hm1 : 1 ≤ m := by
      dsimp [m]
      exact_mod_cast (Nat.succ_le_iff.mpr
        (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)))
    have hmle : m⁻¹ ≤ 1 := (inv_le_one₀ hm).2 hm1
    calc
      m⁻¹ * Real.exp (m * y i) ≤ 1 * Real.exp (m * y i) :=
        mul_le_mul_of_nonneg_right hmle (Real.exp_pos _).le
      _ = Real.exp (m * y i) := by ring
  rw [hleft] at hj
  exact hj.trans hright

/-- A finite linear combination of local curvatures has an exponential moment
uniformly bounded in the cube size. The bound follows from the one-coordinate
Gaussian estimates by finite Jensen. -/
theorem cubeCurvaturePMFTotal_exp_linear_bound
    (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (P : Finset GlobalIntegerPlaquette) (c : P → ℝ) (t : ℝ) :
    MeasureTheory.Integrable
        (fun x : P → ℤ => Real.exp (t * ∑ p : P, c p * (x p : ℝ)))
        (cubeCurvaturePMFTotal N β hβ P).toMeasure ∧
      ∫ x, Real.exp (t * ∑ p : P, c p * (x p : ℝ)) ∂
          (cubeCurvaturePMFTotal N β hβ P).toMeasure ≤
        1 + ∑ p : P,
          Real.exp (((t * (Fintype.card P : ℝ) * c p) ^ 2 * β) / 2) := by
  classical
  let ν := (cubeCurvaturePMFTotal N β hβ P).toMeasure
  let F : (P → ℤ) → ℝ := fun x => Real.exp (t * ∑ p : P, c p * (x p : ℝ))
  by_cases hP : Nonempty P
  · let m : ℝ := Fintype.card P
    have hm : 0 < m := by
      dsimp [m]
      exact_mod_cast (Fintype.card_pos_iff.mpr hP)
    let G : (P → ℤ) → ℝ := fun x =>
      ∑ p : P, Real.exp ((t * m * c p) * (x p : ℝ))
    have hpoint (x : P → ℤ) : F x ≤ G x := by
      dsimp [F, G]
      have h := finite_exp_sum_le_sum_exp_scaled
        (fun p : P => t * c p * (x p : ℝ))
      have heq : (∑ p : P, t * c p * (x p : ℝ)) =
          t * ∑ p : P, c p * (x p : ℝ) := by
        calc
          _ = ∑ p : P, t * (c p * (x p : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ = _ := (Finset.mul_sum ..).symm
      rw [heq] at h
      have harg (p : P) : m * (t * c p * (x p : ℝ)) =
          (t * m * c p) * (x p : ℝ) := by ring
      have hcard : (Fintype.card P : ℝ) = m := rfl
      rw [hcard] at h
      simp_rw [harg] at h
      exact h
    have hterm (p : P) :
        MeasureTheory.Integrable
          (fun x : P → ℤ => Real.exp ((t * m * c p) * (x p : ℝ))) ν := by
      dsimp [ν]
      exact cubeCurvaturePMFTotal_coordinate_exp_integrable
        N β (t * m * c p) hβ P p
    have hG : MeasureTheory.Integrable G ν := by
      dsimp [G]
      exact MeasureTheory.integrable_finsetSum Finset.univ
        (fun p hp => hterm p)
    have hF : MeasureTheory.Integrable F ν := by
      apply hG.mono'
      · change MeasureTheory.AEStronglyMeasurable F ν
        fun_prop
      · filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hpoint x
    have hsumInt :
        ∫ x, G x ∂ν = ∑ p : P,
          ∫ x, Real.exp ((t * m * c p) * (x p : ℝ)) ∂ν := by
      dsimp [G]
      exact MeasureTheory.integral_finsetSum Finset.univ (fun p hp => hterm p)
    have hsumBound :
        ∑ p : P, ∫ x, Real.exp ((t * m * c p) * (x p : ℝ)) ∂ν ≤
          ∑ p : P, Real.exp (((t * m * c p) ^ 2 * β) / 2) := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp [ν]
      convert cubeCurvaturePMFTotal_coordinate_exp_le N β (t * m * c p)
        hβ P p using 1
    have hbound : ∫ x, F x ∂ν ≤
        ∑ p : P, Real.exp (((t * m * c p) ^ 2 * β) / 2) := by
      calc
        ∫ x, F x ∂ν ≤ ∫ x, G x ∂ν :=
          MeasureTheory.integral_mono hF hG hpoint
        _ ≤ ∑ p : P, Real.exp (((t * m * c p) ^ 2 * β) / 2) := by
          rw [hsumInt]
          exact hsumBound
    refine ⟨?_, ?_⟩
    · simpa [ν, F] using hF
    · have hsum0 : 0 ≤ ∑ p : P,
          Real.exp (((t * m * c p) ^ 2 * β) / 2) :=
        Finset.sum_nonneg (fun p hp => (Real.exp_pos _).le)
      simpa [ν, F, m] using hbound.trans
        (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  · have hPempty : IsEmpty P := not_nonempty_iff.mp hP
    have hone : F = fun _ => (1 : ℝ) := by
      funext x
      have hsum : (∑ p : P, c p * (x p : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        exact (hPempty.false p).elim
      simp [F]
    change MeasureTheory.Integrable F ν ∧ ∫ x, F x ∂ν ≤
      1 + ∑ p : P, Real.exp (((t * (Fintype.card P : ℝ) * c p) ^ 2 * β) / 2)
    constructor
    · rw [hone]
      exact MeasureTheory.integrable_const 1
    · rw [hone]
      have hmass : ∫ x : P → ℤ, (1 : ℝ) ∂ν = 1 := by simp [ν]
      rw [hmass]
      have hsum0 : 0 ≤ ∑ p : P,
          Real.exp (((t * (Fintype.card P : ℝ) * c p) ^ 2 * β) / 2) :=
        Finset.sum_nonneg (fun p hp => (Real.exp_pos _).le)
      linarith

/-- Integrability under a countable PMF implies summability of its weighted
absolute values. -/
theorem pmf_summable_norm_of_integrable {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] {p : PMF α} {f : α → ℝ}
    (hint : MeasureTheory.Integrable f p.toMeasure) :
    Summable (fun x => (p x).toReal * ‖f x‖) := by
  rw [pmf_toMeasure_eq_sum_dirac] at hint
  have hiff := MeasureTheory.integrable_sum_dirac_iff
    (f := f) (x := fun x : α => x) (c := p) (fun x => p.apply_ne_top x)
  exact hiff.mp hint

/-- The finite local exponential observable has a uniformly bounded second
moment. -/
theorem cubeCurvaturePMFTotal_exp_linear_secondMoment
    (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (P : Finset GlobalIntegerPlaquette) (c : P → ℝ) (t : ℝ) :
    Summable (fun x : P → ℤ =>
      (cubeCurvaturePMFTotal N β hβ P x).toReal *
        (Real.exp (t * ∑ p : P, c p * (x p : ℝ))) ^ 2) ∧
      ∑' x : P → ℤ,
        (cubeCurvaturePMFTotal N β hβ P x).toReal *
          (Real.exp (t * ∑ p : P, c p * (x p : ℝ))) ^ 2 ≤
        1 + ∑ p : P,
          Real.exp (((2 * t * (Fintype.card P : ℝ) * c p) ^ 2 * β) / 2) := by
  classical
  let p := cubeCurvaturePMFTotal N β hβ P
  let F : (P → ℤ) → ℝ := fun x => Real.exp (t * ∑ q : P, c q * (x q : ℝ))
  let F2 : (P → ℤ) → ℝ := fun x => Real.exp ((2 * t) * ∑ q : P, c q * (x q : ℝ))
  have hF2 := cubeCurvaturePMFTotal_exp_linear_bound N β hβ P c (2 * t)
  have hnorm := pmf_summable_norm_of_integrable (p := p) (f := F2) (by
    simpa [p, F2] using hF2.1)
  have hsquare (x : P → ℤ) : F x ^ 2 = F2 x := by
    dsimp [F, F2]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hterm (x : P → ℤ) : (p x).toReal * F x ^ 2 =
      (p x).toReal * ‖F2 x‖ := by
    rw [hsquare, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsummable : Summable (fun x : P → ℤ => (p x).toReal * F x ^ 2) := by
    refine hnorm.congr ?_
    intro x
    exact (hterm x).symm
  have hsum : ∫ x, F2 x ∂p.toMeasure =
      ∑' x : P → ℤ, (p x).toReal * F2 x := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum p F2 (by
      simpa [p, F2] using hF2.1)
  have hbound : ∫ x, F2 x ∂p.toMeasure ≤
      1 + ∑ q : P,
        Real.exp (((2 * t * (Fintype.card P : ℝ) * c q) ^ 2 * β) / 2) := by
    simpa [p, F2] using hF2.2
  refine ⟨?_, ?_⟩
  · simpa [p, F] using hsummable
  · calc
      ∑' x : P → ℤ, (p x).toReal * F x ^ 2 = ∫ x, F2 x ∂p.toMeasure := by
        rw [hsum]
        apply tsum_congr
        intro x
        rw [hsquare]
      _ ≤ 1 + ∑ q : P,
          Real.exp (((2 * t * (Fintype.card P : ℝ) * c q) ^ 2 * β) / 2) := hbound

/-- Exponential moments of every finite weighted local-curvature observable
converge along the common subsequence defining a cylinder limit state. -/
theorem cubeCurvatureLimitState_expLinear_integral_tendsto
    (β : ℝ) (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (P : Finset GlobalIntegerPlaquette) (c : P → ℝ) (t : ℝ) :
    Tendsto
      (fun k => ∫ x, Real.exp (t * ∑ q : P, c q * (x q : ℝ)) ∂
        (cubeCurvaturePMFTotal (L.subsequence k) β hβ P).toMeasure)
      atTop
      (𝓝 (∫ x, Real.exp (t * ∑ q : P, c q * (x q : ℝ)) ∂
        (L.law P).toMeasure)) := by
  classical
  let pn : ℕ → PMF (P → ℤ) := fun k =>
    cubeCurvaturePMFTotal (L.subsequence k) β hβ P
  let p : PMF (P → ℤ) := L.law P
  let f : (P → ℤ) → ℝ := fun x => Real.exp (t * ∑ q : P, c q * (x q : ℝ))
  have hpoint : ∀ x, Tendsto (fun k => (pn k x).toReal) atTop (𝓝 ((p x).toReal)) := by
    intro x
    exact L.pointwise P x
  have htight : ∀ ε : ℝ, 0 < ε → ∃ S : Finset (P → ℤ), ∀ k,
      1 - ε ≤ ∑ x ∈ S, (pn k x).toReal := by
    intro ε hε
    obtain ⟨S, hS⟩ := cubeCurvaturePMFTotal_uniform_tight β hβ P ε hε
    exact ⟨S, fun k => hS (L.subsequence k)⟩
  have hnonneg (x : P → ℤ) : 0 ≤ f x := (Real.exp_pos _).le
  let C : ℝ := 1 + ∑ q : P,
    Real.exp (((2 * t * (Fintype.card P : ℝ) * c q) ^ 2 * β) / 2)
  have hsq : ∀ k, Summable (fun x => (pn k x).toReal * (f x) ^ 2) := by
    intro k
    exact (cubeCurvaturePMFTotal_exp_linear_secondMoment
      (L.subsequence k) β hβ P c t).1
  have hsqBound : ∀ k, ∑' x, (pn k x).toReal * (f x) ^ 2 ≤ C := by
    intro k
    exact cubeCurvaturePMFTotal_exp_linear_secondMoment
      (L.subsequence k) β hβ P c t |>.2
  have hsumTendsto := pmf_weighted_tsum_tendsto_of_tight_secondMoment
    pn p f C hpoint htight hnonneg hsq hsqBound
  have hlimSq := pmf_secondMoment_bound_of_pointwise pn p f C hpoint hsq hsqBound
  have hmass := pmf_real_mass_summable p
  have hYoung (x : P → ℤ) : f x ≤ 1 + f x ^ 2 := by
    nlinarith [sq_nonneg (f x - 1 / 2)]
  have hweight : Summable (fun x => (p x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (hnonneg x))
    · intro x
      have hm := ENNReal.toReal_nonneg (a := p x)
      have hh := mul_le_mul_of_nonneg_left (hYoung x) hm
      simpa [mul_add] using hh
    · exact hmass.add hlimSq.1
  have hlimIntegrable : MeasureTheory.Integrable f p.toMeasure :=
    pmf_integrable_of_summable_norm (by
      refine hweight.congr ?_
      intro x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
  have hseqIntegrable (k : ℕ) : MeasureTheory.Integrable f (pn k).toMeasure := by
    simpa [pn, f] using
      (cubeCurvaturePMFTotal_exp_linear_bound (L.subsequence k) β hβ P c t).1
  have hseqEq (k : ℕ) :
      ∫ x, f x ∂(pn k).toMeasure = ∑' x, (pn k x).toReal * f x := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn k) f (hseqIntegrable k)
  have hlimEq : ∫ x, f x ∂p.toMeasure = ∑' x, (p x).toReal * f x := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum p f hlimIntegrable
  have hsumIntegral := hsumTendsto.congr'
    (Filter.Eventually.of_forall fun k => (hseqEq k).symm)
  rw [← hlimEq] at hsumIntegral
  simpa [pn, p, f] using hsumIntegral


/-- The finite set of global plaquettes in a compact plaquette field's
support. -/
noncomputable def fillingPlaquetteEmbedding (σ : GlobalPlaquetteField) :
    {c : LatticeCell 4 // c ∈ (σ : RealLatticeChain 4).support} ↪
      GlobalIntegerPlaquette where
  toFun c := ⟨c.1, σ.2 c.1 c.2⟩
  inj' := by
    intro a b h
    cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        have hab : a = b := congrArg Subtype.val h
        cases hab
        rfl

noncomputable def fillingCurvatureIndexSet (σ : GlobalPlaquetteField) :
    Finset GlobalIntegerPlaquette :=
  ((σ : RealLatticeChain 4).support.attach).map (fillingPlaquetteEmbedding σ)

/-- Coefficients of a compact plaquette filling, read on its local integer
curvature coordinates. -/
noncomputable def fillingPlaquetteCoeff (σ : GlobalPlaquetteField)
    (p : fillingCurvatureIndexSet σ) : ℝ :=
  (σ : RealLatticeChain 4) p.1.1


end FroehlichSpencer.FS82.Infinite

end
