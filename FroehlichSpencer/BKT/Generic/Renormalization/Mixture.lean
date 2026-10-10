/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Theorem22

/-!
# KP Theorem 2.2 with a general site mixture (generic core)

KP Theorem 2.2 (pp. 9–10, (2.6)–(2.7); `Reduction.T22Step`, proved by
`Charges.t22Statement_of_repairedBasicLemma`) writes each site weight
`λ_j(φ) = 1 + 2 ∑_q λ̂_j(q) cos(qφ)` as the convex mixture
`∑_q ζ(q) (1 + z_j(q) cos(qφ))`, `z_j(q) = 2 λ̂_j(q) / ζ(q)`, with KP's Gaussian mixture weights
`ζ(q) ∝ e^{-q²}` (`Charges.siteModeWeight`), and then runs the scale process of KP §4.2.

The
activity bound (2.7) therefore carries the entropy factor `e^{ϱ(j)²}` at every site.

A Gaussian reference law absorbs that factor through the quadratic energy gain `‖ϱ‖²/(16β)`.

This module proves KP Theorem 2.2 for **every** positive site mixture `ζ_j(q)` (`T22MixStep`,
`t22MixStep_holds`), with the activity bound
`|K(ϱ)| ≤ e^{200 A(ϱ)} ∏_{j ∈ supp ϱ} Z_j(|ϱ(j)|)`, `Z_j(q) = 2|λ̂_j(q)| / ζ_j(q)` (`mixtureLeaf`).

It reuses the scale process unchanged.

`exists_scaleIteration` and the `ScaleInvariant`
API are generic in the leaf weight `Z`, and `Charges.basicLemmaStepStatement` supplies KP Lemma
4.3.

Only the initial mixture (`mixture_prod_eq`, `mixture_initial_invariant`) and the terminal
bound (`mixture_terminal_properties`) are restated for a general leaf weight.

KP's choice
`ζ = siteModeWeight` is the special case.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open Finset

variable {L : ℕ}

/-- The leaf weight of a positive site mixture: `Z_j(q) = 2|λ̂_j(q)| / ζ_j(q)` on the modes
`1 ≤ q ≤ N_j`, and `0` otherwise. -/
def mixtureLeaf {L : ℕ} (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (j : Fin L × Fin L) (q : ℕ) : ℝ :=
  if h : q ∈ Finset.Icc 1 (Nq j) then 2 * |lamHat j q| / ζ j ⟨q, h⟩ else 0

/-- KP Theorem 2.2 (2.6)–(2.7) with a general positive site mixture. -/
def T22MixStep (boundary : SquareBoundary) (L : ℕ) (D₂ : ℝ) : Prop :=
  ∀ (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ),
    (∀ j, 0 < Nq j) → (∀ j q, Nq j < q → lamHat j q = 0) →
    (∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ)) →
    (∀ j q, 0 < ζ j q) → (∀ j, ∑ q, ζ j q = 1) →
    ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
      (K : Fin n → (Fin L × Fin L → ℤ) → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
      (∀ ψ : Fin L × Fin L → ℝ,
        ∏ j, lam j (ψ j) = ∑ i, c i * ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, ψ j * ϱ j))) ∧
      ∀ i, AtMostOneNonNeutral (N i) ∧ IsScaleSeparated boundary L (N i) ∧
        NeutralSplitsAreCharged boundary L (N i) ∧
        ∀ ϱ ∈ N i, ∑ j, ϱ j = 0 →
          |K i ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
            ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs

/-- A positive mixture has a nonnegative leaf weight. -/
theorem mixtureLeaf_nonneg {Nq : Fin L × Fin L → ℕ} (lamHat : Fin L × Fin L → ℕ → ℝ)
    {ζ : ∀ j, SiteMode (Nq j) → ℝ} (hζ : ∀ j q, 0 < ζ j q) (x : Fin L × Fin L) (q : ℕ) :
    0 ≤ mixtureLeaf Nq lamHat ζ x q := by
  unfold mixtureLeaf
  split_ifs with h
  · exact div_nonneg (by positivity) (hζ x _).le
  · exact le_rfl

/-! ## The site mixture -/

/-- The coefficient `z_j(q) = 2 λ̂_j(q) / ζ_j(q)` of one mode. -/
def mixtureCoeff {Nq : Fin L × Fin L → ℕ} (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (j : Fin L × Fin L) (q : SiteMode (Nq j)) : ℝ :=
  2 * lamHat j q.1 / ζ j q

/-- The product weight `∏_j ζ_j(q_j)` of a frequency vector. -/
def mixtureWeight {Nq : Fin L × Fin L → ℕ} (ζ : ∀ j, SiteMode (Nq j) → ℝ)
    (q : SiteFrequencyVector Nq) : ℝ :=
  ∏ j, ζ j (q j)

/-- One site: `∑_q ζ(q) (1 + z(q) cos(qφ)) = λ(φ)`. -/
theorem mixture_site_eq {Nq : Fin L × Fin L → ℕ} (lamHat : Fin L × Fin L → ℕ → ℝ)
    {ζ : ∀ j, SiteMode (Nq j) → ℝ} (hζ : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1)
    (lam : Fin L × Fin L → ℝ → ℝ)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (j : Fin L × Fin L) (φ : ℝ) :
    ∑ q : SiteMode (Nq j), ζ j q * (1 + mixtureCoeff lamHat ζ j q * Real.cos (q.1 * φ)) =
      lam j φ := by
  have hterm : ∀ q : SiteMode (Nq j),
      ζ j q * (1 + mixtureCoeff lamHat ζ j q * Real.cos (q.1 * φ)) =
        ζ j q + 2 * (lamHat j q.1 * Real.cos (q.1 * φ)) := by
    intro q
    unfold mixtureCoeff
    field_simp [(hζ j q).ne']
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hζsum j, hlam j φ, ← Finset.mul_sum]
  congr 2
  rw [Finset.univ_eq_attach (Finset.Icc 1 (Nq j))]
  exact Finset.sum_attach (Finset.Icc 1 (Nq j)) fun q => lamHat j q * Real.cos (q * φ)

/-- The product mixture over frequency vectors. -/
theorem mixture_prod_eq {Nq : Fin L × Fin L → ℕ} (lamHat : Fin L × Fin L → ℕ → ℝ)
    {ζ : ∀ j, SiteMode (Nq j) → ℝ} (hζ : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1)
    (lam : Fin L × Fin L → ℝ → ℝ)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (ψ : Fin L × Fin L → ℝ) :
    ∏ j, lam j (ψ j) =
      ∑ q : SiteFrequencyVector Nq, mixtureWeight ζ q *
        ∏ j, (1 + mixtureCoeff lamHat ζ j (q j) * Real.cos ((q j).1 * ψ j)) := by
  classical
  calc ∏ j, lam j (ψ j) = ∏ j, ∑ q : SiteMode (Nq j),
        ζ j q * (1 + mixtureCoeff lamHat ζ j q * Real.cos (q.1 * ψ j)) :=
        Finset.prod_congr rfl fun j _ => (mixture_site_eq lamHat hζ hζsum lam hlam j (ψ j)).symm
    _ = ∑ q : SiteFrequencyVector Nq, ∏ j,
        ζ j (q j) * (1 + mixtureCoeff lamHat ζ j (q j) * Real.cos ((q j).1 * ψ j)) :=
        Fintype.prod_sum _
    _ = _ := Finset.sum_congr rfl fun q _ => by
        unfold mixtureWeight
        rw [Finset.prod_mul_distrib]

/-- The product weights are positive and sum to one. -/
theorem mixtureWeight_positive_sum {Nq : Fin L × Fin L → ℕ} {ζ : ∀ j, SiteMode (Nq j) → ℝ}
    (hζ : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) :
    (∀ q : SiteFrequencyVector Nq, 0 < mixtureWeight ζ q) ∧
      ∑ q : SiteFrequencyVector Nq, mixtureWeight ζ q = 1 := by
  classical
  refine ⟨fun q => Finset.prod_pos fun j _ => hζ j (q j), ?_⟩
  unfold mixtureWeight
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun j _ => hζsum j

/-! ## The point-charge state -/

/-- The coefficient function on charge densities encoding the selected modes. -/
def mixtureChargeCoefficient {Nq : Fin L × Fin L → ℕ} (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (q : SiteFrequencyVector Nq) : ChargeDensity L → ℝ :=
  fun ρ => ∑ j, if ρ = pointCharge j ((q j).1 : ℤ) then mixtureCoeff lamHat ζ j (q j) else 0

theorem mixtureChargeCoefficient_at_site {Nq : Fin L × Fin L → ℕ}
    (lamHat : Fin L × Fin L → ℕ → ℝ) (ζ : ∀ j, SiteMode (Nq j) → ℝ)
    (q : SiteFrequencyVector Nq) (j : Fin L × Fin L) :
    mixtureChargeCoefficient lamHat ζ q (pointCharge j ((q j).1 : ℤ)) =
      mixtureCoeff lamHat ζ j (q j) := by
  classical
  have hqnonzero (i : Fin L × Fin L) : ((q i).1 : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp (q i).2).1)
  have hinj := pointCharge_siteMap_injective (fun i => ((q i).1 : ℤ)) hqnonzero
  unfold mixtureChargeCoefficient
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have heq : pointCharge j ((q j).1 : ℤ) ≠ pointCharge i ((q i).1 : ℤ) :=
      fun heq => hij (hinj heq.symm)
    simp [heq]
  · simp

/-- The point-charge product is the product of the sitewise factors. -/
theorem mixtureChargeProduct_eq {Nq : Fin L × Fin L → ℕ} (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (ψ : Fin L × Fin L → ℝ) (q : SiteFrequencyVector Nq) :
    chargeFactorProduct (siteFrequencyChargeFamily Nq q) (mixtureChargeCoefficient lamHat ζ q)
        ψ = ∏ j, (1 + mixtureCoeff lamHat ζ j (q j) * Real.cos ((q j).1 * ψ j)) := by
  classical
  have hqnonzero (j : Fin L × Fin L) : ((q j).1 : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp (q j).2).1)
  have hinj := pointCharge_siteMap_injective (fun j => ((q j).1 : ℤ)) hqnonzero
  unfold chargeFactorProduct siteFrequencyChargeFamily
  rw [Finset.prod_image hinj.injOn]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [chargeFactor, mixtureChargeCoefficient_at_site, chargePhase_pointCharge]
  push_cast
  ring_nf

/-- The point charges `q_j δ_j` with coefficients `z_j(q_j)` satisfy the scale-`0` invariants
with the mixture leaf weight (KP p. 21: `Q_{-1} = {q_j δ_j}`, `G_{-1} = ∅`). -/
theorem mixture_initial_invariant (boundary : SquareBoundary) (hL : 1 < L)
    {Nq : Fin L × Fin L → ℕ} (lamHat : Fin L × Fin L → ℕ → ℝ) {ζ : ∀ j, SiteMode (Nq j) → ℝ}
    (hζ : ∀ j q, 0 < ζ j q) (q : SiteFrequencyVector Nq) :
    ScaleInvariant boundary L (mixtureLeaf Nq lamHat ζ) 0
      ⟨siteFrequencyChargeFamily Nq q, ∅, mixtureChargeCoefficient lamHat ζ q⟩ := by
  classical
  have hq : ∀ x, ((q x).1 : ℤ) ≠ 0 := fun x => by
    have := (Finset.mem_Icc.mp (q x).2).1
    omega
  have hmem : ∀ ρ, ρ ∈ siteFrequencyChargeFamily Nq q ↔ ∃ x, pointCharge x ((q x).1 : ℤ) = ρ :=
    fun ρ => by simp [siteFrequencyChargeFamily]
  refine
    { ensemble := siteFrequencyChargeFamily_isEnsemble Nq q
      protected_subset := Finset.empty_subset _
      protected_neutral := fun g hg => absurd hg (Finset.notMem_empty g)
      active_separated := ?_
      protected_separated := fun g hg => absurd hg (Finset.notMem_empty g)
      protected_active := fun g hg => absurd hg (Finset.notMem_empty g)
      active_claim44 := ?_
      active_coeff := ?_
      protected_coeff := fun g hg => absurd hg (Finset.notMem_empty g)
      active_atoms := ?_
      protected_atoms := fun g hg => absurd hg (Finset.notMem_empty g) }
  · rw [Finset.sdiff_empty]
    refine ⟨siteFrequencyChargeFamily_isEnsemble Nq q, fun ρ hρ σ hσ hne => ?_⟩
    obtain ⟨x, rfl⟩ := (hmem ρ).mp hρ
    obtain ⟨y, rfl⟩ := (hmem σ).mp hσ
    have hxy : x ≠ y := fun h => hne (by rw [h])
    show 0 < densityDistance boundary L _ _
    unfold densityDistance
    rw [chargeSupport_pointCharge x (hq x), chargeSupport_pointCharge y (hq y)]
    obtain ⟨a, ha, b, hb, hab⟩ := exists_squareDistance_eq boundary L {x} {y}
      (Finset.singleton_nonempty x) (Finset.singleton_nonempty y)
    rw [Finset.mem_singleton] at ha hb
    subst ha hb
    rw [hab]
    exact one_le_latticeDistance_of_ne boundary hL hxy
  · intro a ha hzero
    rw [Finset.sdiff_empty] at ha
    obtain ⟨x, rfl⟩ := (hmem a).mp ha
    rw [sum_pointCharge] at hzero
    exact absurd hzero (hq x)
  · intro a ha
    rw [Finset.sdiff_empty] at ha
    obtain ⟨x, rfl⟩ := (hmem a).mp ha
    show |mixtureChargeCoefficient lamHat ζ q (pointCharge x ((q x).1 : ℤ))| ≤ _
    rw [mixtureChargeCoefficient_at_site]
    simp only [scaleCost, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero,
      Real.exp_zero, one_mul]
    unfold leafProduct
    rw [chargeSupport_pointCharge x (hq x), Finset.prod_singleton]
    simp only [pointCharge, ↓reduceIte, Int.natAbs_natCast]
    unfold mixtureLeaf mixtureCoeff
    rw [dite_eq_left (q x).2, abs_div, abs_mul, abs_of_pos (hζ x _), abs_two]
  · intro a ha
    rw [Finset.sdiff_empty] at ha
    obtain ⟨x, rfl⟩ := (hmem a).mp ha
    exact ScaleAtomFamily.nonempty_of_support_eq_singleton (chargeSupport_pointCharge x (hq x))

/-! ## Terminal branches -/

/-- **Properties (a)–(d) of KP Theorem 2.2** for a terminal branch, for any nonnegative leaf
weight `Z`. -/
theorem mixture_terminal_properties {boundary : SquareBoundary} (hL : 1 < L)
    {Z : (Fin L × Fin L) → ℕ → ℝ} (hZ : ∀ x q, 0 ≤ Z x q) {m : ℕ} {s : ScaleState L}
    (hs : ScaleInvariant boundary L Z m s)
    (hm₁ : ((2 * L : ℕ) : ℝ) ≤ levelThreshold m)
    (hm₂ : (chargeCoverScale : ℝ) * ((2 * L : ℕ) : ℝ) ^ chargeCoverExponent ≤ levelThreshold m) :
    AtMostOneNonNeutral s.Q ∧ IsScaleSeparated boundary L s.Q ∧
      NeutralSplitsAreCharged boundary L s.Q ∧
      ∀ ϱ ∈ s.Q, ∑ j, ϱ j = 0 →
        |s.K ϱ| ≤ Real.exp (200 * chargeCoverCost boundary L ϱ) *
          ∏ j ∈ chargeSupport ϱ, Z j (ϱ j).natAbs := by
  classical
  have hcomm : ∀ ρ σ : ChargeDensity L,
      densityDistance boundary L ρ σ = densityDistance boundary L σ ρ :=
    fun ρ σ => squareDistance_symm boundary L _ _
  have hact : ∀ ρ ∈ s.Q, ∑ j, ρ j ≠ 0 → ρ ∈ s.Q \ s.G := fun ρ hρ hne =>
    Finset.mem_sdiff.mpr ⟨hρ, fun hG => hne (hs.protected_neutral ρ hG)⟩
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- (a)
    intro ρ₁ h₁ ρ₂ h₂ hc₁ hc₂
    exact hs.active_subsingleton hL hm₁ ρ₁ (hact ρ₁ h₁ hc₁) ρ₂ (hact ρ₂ h₂ hc₂)
  · -- (b), general clause
    intro ρ₁ h₁ ρ₂ h₂ hne
    by_cases hG₁ : ρ₁ ∈ s.G <;> by_cases hG₂ : ρ₂ ∈ s.G
    · exact hs.protected_separated ρ₁ hG₁ ρ₂ hG₂ hne
    · exact (chargeCoverScale_mul_rpow_le (min_le_left _ _)).trans
        (hs.protected_active ρ₁ hG₁ ρ₂ (Finset.mem_sdiff.mpr ⟨h₂, hG₂⟩))
    · rw [hcomm]
      exact (chargeCoverScale_mul_rpow_le (min_le_right _ _)).trans
        (hs.protected_active ρ₂ hG₂ ρ₁ (Finset.mem_sdiff.mpr ⟨h₁, hG₁⟩))
    · exact absurd (hs.active_subsingleton hL hm₁ ρ₁ (Finset.mem_sdiff.mpr ⟨h₁, hG₁⟩) ρ₂
        (Finset.mem_sdiff.mpr ⟨h₂, hG₂⟩)) hne
  · -- (b), the charged density
    intro ρc hc hcne ρ hρ hne
    have hρG : ρ ∈ s.G := by
      by_contra hG
      exact hne (hs.active_subsingleton hL hm₁ ρ (Finset.mem_sdiff.mpr ⟨hρ, hG⟩) ρc
        (hact ρc hc hcne))
    exact hs.protected_active ρ hρG ρc (hact ρc hc hcne)
  · -- (c)
    intro ρ hρ hzero ρ₁ ρ₂ h₁ h₂ hdisj hsum hsep
    obtain ⟨T, ⟨F⟩⟩ := hs.protected_atoms ρ (hs.mem_protected_of_neutral hL hm₂ hρ hzero)
    exact F.split_charged hL hzero ρ₁ ρ₂ h₁ h₂ hdisj hsum hsep
  · -- (d)
    intro ρ hρ hzero
    have hG := hs.mem_protected_of_neutral hL hm₂ hρ hzero
    have hd1 := one_le_chargeDiameter_of_neutral boundary hL ρ
      (hs.ensemble.1 ρ hρ) hzero
    have hcost := scaleCost_protectionCutoff_le boundary L ρ hd1
    show |s.K ρ| ≤ _ * leafProduct Z ρ
    refine (hs.protected_coeff ρ hG).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (StepData.leafProduct_nonneg hZ ρ))
    have : (scaleCost boundary L ρ (protectionCutoff boundary L ρ + 2) : ℝ) ≤
        2 * (chargeCoverCost boundary L ρ : ℝ) := by exact_mod_cast hcost
    linarith

/-! ## KP Theorem 2.2 with a general mixture -/

/-- **KP Theorem 2.2 with a general site mixture on one square domain** (`D₂ = 200`), given KP
Lemma 4.3 there. -/
theorem t22MixStep_of_basicLemmaStep (boundary : SquareBoundary) (hL : 1 < L)
    (hstep : BasicLemmaStepStatement boundary L) : T22MixStep boundary L 200 := by
  classical
  intro lam Nq lamHat ζ hNq _ hlam hζ hζsum
  obtain ⟨m, hm₁, hm₂⟩ := exists_terminalLevel L
  have hZ := mixtureLeaf_nonneg lamHat hζ
  choose n c s hc hcsum hid hs using fun q : SiteFrequencyVector Nq =>
    exists_scaleIteration hL hstep hZ (mixture_initial_invariant boundary hL lamHat hζ q) m
  obtain ⟨hξpos, hξsum⟩ := mixtureWeight_positive_sum (Nq := Nq) hζ hζsum
  let ι := Σ q : SiteFrequencyVector Nq, Fin (n q)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let st : Fin (Fintype.card ι) → ScaleState L := fun k => s (e.symm k).1 (e.symm k).2
  let w : Fin (Fintype.card ι) → ℝ := fun k =>
    mixtureWeight ζ (e.symm k).1 * c (e.symm k).1 (e.symm k).2
  have hsumι : ∀ g : ι → ℝ, ∑ k, g (e.symm k) = ∑ q, ∑ i, g ⟨q, i⟩ := fun g => by
    rw [Equiv.sum_comp e.symm g, Fintype.sum_sigma]
  refine ⟨Fintype.card ι, fun k => (st k).Q, w, fun k => (st k).K, fun k => (hs _ _).ensemble,
    fun k => mul_pos (hξpos _) (hc _ _), ?_, fun ψ => ?_, fun k => ?_⟩
  · show ∑ k, w k = 1
    have := hsumι fun p => mixtureWeight ζ p.1 * c p.1 p.2
    simp only [w]
    rw [this]
    simp_rw [← Finset.mul_sum, hcsum, mul_one]
    exact hξsum
  · rw [mixture_prod_eq lamHat hζ hζsum lam hlam ψ]
    have hk := hsumι fun p => mixtureWeight ζ p.1 * c p.1 p.2 *
      chargeFactorProduct (s p.1 p.2).Q (s p.1 p.2).K ψ
    have hgoal : ∑ k, w k * ∏ ϱ ∈ (st k).Q, (1 + (st k).K ϱ * Real.cos (∑ j, ψ j * ϱ j)) =
        ∑ k, mixtureWeight ζ (e.symm k).1 * c (e.symm k).1 (e.symm k).2 *
          chargeFactorProduct (s (e.symm k).1 (e.symm k).2).Q (s (e.symm k).1 (e.symm k).2).K ψ :=
      rfl
    rw [hgoal, hk]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mixtureChargeProduct_eq lamHat ζ ψ q, hid q ψ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · exact mixture_terminal_properties hL hZ (hs _ _) hm₁ hm₂

/-- **KP Theorem 2.2 with a general site mixture** on the free square and on the even periodic
square (`D₂ = 200`), from the closed KP Lemma 4.3 (`Charges.basicLemmaStepStatement`). -/
theorem t22MixStep_holds (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (hdom : boundary = .free ∨ Even L) : T22MixStep boundary L 200 :=
  t22MixStep_of_basicLemmaStep boundary hL (basicLemmaStepStatement boundary hL hdom)

end FroehlichSpencer.BKT.Generic

end
