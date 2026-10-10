/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ScaleProcess
public import FroehlichSpencer.BKT.Charges.BasicLemmaStep
public import FroehlichSpencer.BKT.Reduction.T16AssemblyStatements

/-!
# KP Theorem 2.2: the convex expansion into mostly neutral ensembles

`t22Statement_of_basicLemmaStep` proves the exact proposition
`Reduction.t22Statement` with `D₂ = 200`, given KP Lemma 4.3 in the form
`BasicLemmaStepStatement` on every square domain.

`BasicLemmaStep.lean` now proves that gateway
from the expansion, its signed lineage certificate, and the finite-square count.

1. **Site-weight mixture ((4.14)–(4.16)).** Each weight `λ_j` is a convex mixture of
   `1 + z_j(q) cos(q ψ_j)`; the product is a mixture over frequency vectors `q⃗` of products over
   the point-charge ensemble `{q_j δ_j}` (`Charges/SiteWeightMixture.lean`).
2. **Scale process (** From the point charges (`initial_invariant`), apply
   `exists_scaleStep` up to a terminal level `m` with `2^{m−1} ≥ max(2L, M(2L)^α)`
   (`exists_scaleIteration`).
3. **Terminal branches.** The active set is empty or one non-neutral factor; every neutral
   factor is protected.

Then (a) and (b) are the protection invariants, (c) is the first-crossing
   lemma `ScaleAtomFamily.split_charged`, and (d) is the protected coefficient bound with
   `∑_{i ≤ n+1} A_{i−1} ≤ 2 A(ϱ)` and `2 C(N) ≤ 1` (
4. **Assembly (** The nested finite mixtures are flattened to one `Fin n`-indexed family
   retaining duplicate ensembles with their own coefficients.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open Finset

/-! ### Composition of finite convex families -/

/-- Flatten a two-level finite family into one `Fin N`-indexed family. -/
theorem exists_convex_compose {α : Type*} {n : ℕ} (c : Fin n → ℝ) (m : Fin n → ℕ)
    (d : ∀ i, Fin (m i) → ℝ) (x : ∀ i, Fin (m i) → α) :
    ∃ (N : ℕ) (e : Fin N → ℝ) (y : Fin N → α),
      (∀ k, ∃ i j, e k = c i * d i j ∧ y k = x i j) ∧
      ∀ g : α → ℝ, ∑ k, e k * g (y k) = ∑ i, c i * ∑ j, d i j * g (x i j) := by
  refine ⟨∑ i, m i, fun k => c (finSigmaFinEquiv.symm k).1 * d _ (finSigmaFinEquiv.symm k).2,
    fun k => x _ (finSigmaFinEquiv.symm k).2, fun k => ⟨_, _, rfl, rfl⟩, fun g => ?_⟩
  let F : ((i : Fin n) × Fin (m i)) → ℝ := fun p => c p.1 * d p.1 p.2 * g (x p.1 p.2)
  have hF : ∀ k : Fin (∑ i, m i),
      c (finSigmaFinEquiv.symm k).1 * d _ (finSigmaFinEquiv.symm k).2 *
        g (x _ (finSigmaFinEquiv.symm k).2) = F (finSigmaFinEquiv.symm k) := fun _ => rfl
  simp_rw [hF]
  rw [Equiv.sum_comp finSigmaFinEquiv.symm F, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [F]; ring

/-- **The iterated scale process**: a state with the scale-`0` invariants is, identically in `ψ`,
a positive convex combination of states with the scale-`m` invariants. -/
theorem exists_scaleIteration {boundary : SquareBoundary} {L : ℕ} (hL : 1 < L)
    (hstep : BasicLemmaStepStatement boundary L) {Z : (Fin L × Fin L) → ℕ → ℝ}
    (hZ : ∀ x q, 0 ≤ Z x q) {s₀ : ScaleState L} (hs₀ : ScaleInvariant boundary L Z 0 s₀)
    (m : ℕ) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (s : Fin n → ScaleState L),
      (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
      (∀ ψ, chargeFactorProduct s₀.Q s₀.K ψ = ∑ i, c i * chargeFactorProduct (s i).Q (s i).K ψ) ∧
      ∀ i, ScaleInvariant boundary L Z m (s i) := by
  induction m with
  | zero =>
    exact ⟨1, fun _ => 1, fun _ => s₀, fun _ => one_pos, by simp, fun ψ => by simp,
      fun _ => hs₀⟩
  | succ m ih =>
    obtain ⟨n, c, s, hc, hcsum, hid, hs⟩ := ih
    choose m' d s' hd hdsum hdid hds' using fun i => exists_scaleStep hL hstep hZ (hs i)
    obtain ⟨N, e, y, hrep, hsum⟩ := exists_convex_compose c m' d s'
    refine ⟨N, e, y, fun k => ?_, ?_, fun ψ => ?_, fun k => ?_⟩
    · obtain ⟨i, j, he, -⟩ := hrep k
      rw [he]
      exact mul_pos (hc i) (hd i j)
    · have h := hsum fun _ => 1
      simp only [mul_one] at h
      rw [h]
      simp [hdsum, hcsum]
    · rw [hid ψ, hsum fun t => chargeFactorProduct t.Q t.K ψ]
      exact Finset.sum_congr rfl fun i _ => by rw [hdid i ψ]
    · obtain ⟨i, j, -, hy⟩ := hrep k
      rw [hy]
      exact hds' i j

/-! ### The initial point-charge state -/

theorem chargeSupport_pointCharge {L : ℕ} (x : Fin L × Fin L) {q : ℤ} (hq : q ≠ 0) :
    chargeSupport (pointCharge x q) = {x} := by
  ext y
  by_cases hy : y = x <;> simp [chargeSupport, pointCharge, hy, hq]

theorem sum_pointCharge {L : ℕ} (x : Fin L × Fin L) (q : ℤ) : ∑ y, pointCharge x q y = q := by
  simp [pointCharge]

/-- The site leaf weight `Z(j, q) = e^{q²} |λ̂_j(q)|` of (2.7). -/
def siteLeafWeight {L : ℕ} (hat : (Fin L × Fin L) → ℕ → ℝ) (x : Fin L × Fin L) (q : ℕ) : ℝ :=
  Real.exp ((q : ℝ) ^ 2) * |hat x q|

theorem siteLeafWeight_nonneg {L : ℕ} (hat : (Fin L × Fin L) → ℕ → ℝ) (x : Fin L × Fin L)
    (q : ℕ) : 0 ≤ siteLeafWeight hat x q :=
  mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

/-- The point charges `q_j δ_j` with coefficients `z_j(q_j)` satisfy the scale-`0` invariants
(KP p. 21: `Q_{-1} = {q_j δ_j}`, `G_{-1} = ∅`). -/
theorem initial_invariant (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (N : (Fin L × Fin L) → ℕ) (hat : (Fin L × Fin L) → ℕ → ℝ) (q : SiteFrequencyVector N) :
    ScaleInvariant boundary L (siteLeafWeight hat) 0
      ⟨siteFrequencyChargeFamily N q, ∅, siteFrequencyChargeCoefficient N hat q⟩ := by
  classical
  have hq : ∀ x, ((q x).1 : ℤ) ≠ 0 := fun x => by
    have := (Finset.mem_Icc.mp (q x).2).1
    omega
  have hmem : ∀ ρ, ρ ∈ siteFrequencyChargeFamily N q ↔ ∃ x, pointCharge x ((q x).1 : ℤ) = ρ :=
    fun ρ => by simp [siteFrequencyChargeFamily]
  refine
    { ensemble := siteFrequencyChargeFamily_isEnsemble N q
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
    refine ⟨siteFrequencyChargeFamily_isEnsemble N q, fun ρ hρ σ hσ hne => ?_⟩
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
    show |siteFrequencyChargeCoefficient N hat q (pointCharge x ((q x).1 : ℤ))| ≤ _
    rw [siteFrequencyChargeCoefficient_at_site]
    simp only [scaleCost, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero,
      Real.exp_zero, one_mul]
    unfold leafProduct
    rw [chargeSupport_pointCharge x (hq x), Finset.prod_singleton]
    simp only [pointCharge, ↓reduceIte, Int.natAbs_natCast]
    exact abs_siteModeCoefficient_le (N x) (hat x) (q x)
  · intro a ha
    rw [Finset.sdiff_empty] at ha
    obtain ⟨x, rfl⟩ := (hmem a).mp ha
    exact ScaleAtomFamily.nonempty_of_support_eq_singleton (chargeSupport_pointCharge x (hq x))

/-! ### Terminal branches -/

/-- A terminal level: `2^{m−1} ≥ max(2L, M (2L)^α)`. -/
theorem exists_terminalLevel (L : ℕ) :
    ∃ m : ℕ, ((2 * L : ℕ) : ℝ) ≤ levelThreshold m ∧
      (chargeCoverScale : ℝ) * ((2 * L : ℕ) : ℝ) ^ chargeCoverExponent ≤ levelThreshold m := by
  set B₁ : ℝ := ((2 * L : ℕ) : ℝ)
  set B₂ : ℝ := (chargeCoverScale : ℝ) * ((2 * L : ℕ) : ℝ) ^ chargeCoverExponent
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max B₁ B₂) one_lt_two
  have h2 : ((levelThreshold (m + 1) : ℕ) : ℝ) = (2 : ℝ) ^ m := by
    rw [levelThreshold_succ]
    push_cast
    rfl
  exact ⟨m + 1, by rw [h2]; linarith [le_max_left B₁ B₂], by rw [h2]; linarith [le_max_right B₁ B₂]⟩

section Terminal

variable {boundary : SquareBoundary} {L : ℕ} {Z : (Fin L × Fin L) → ℕ → ℝ} {m : ℕ}
  {s : ScaleState L}

/-- At a terminal level the active set has at most one member. -/
theorem ScaleInvariant.active_subsingleton (hs : ScaleInvariant boundary L Z m s) (hL : 1 < L)
    (hm : ((2 * L : ℕ) : ℝ) ≤ levelThreshold m) :
    ∀ a ∈ s.Q \ s.G, ∀ a' ∈ s.Q \ s.G, a = a' := by
  intro a ha a' ha'
  by_contra hne
  have h1 := hs.active_separated.2 a ha a' ha' hne
  rw [← levelThreshold_eq_separationThreshold] at h1
  have h2 := squareDistance_le_two_mul boundary hL (chargeSupport a) (chargeSupport a')
  have h3 : levelThreshold m < 2 * L := lt_of_lt_of_le h1 h2
  have h4 : ((2 * L : ℕ) : ℝ) ≤ (levelThreshold m : ℝ) := hm
  have h5 : (levelThreshold m : ℝ) < ((2 * L : ℕ) : ℝ) := by exact_mod_cast h3
  linarith

/-- At a terminal level no active factor is neutral (Claim 4.4 with `M d^α ≤ M (2L)^α`). -/
theorem ScaleInvariant.active_charged (hs : ScaleInvariant boundary L Z m s) (hL : 1 < L)
    (hm : (chargeCoverScale : ℝ) * ((2 * L : ℕ) : ℝ) ^ chargeCoverExponent ≤ levelThreshold m) :
    ∀ a ∈ s.Q \ s.G, ∑ x, a x ≠ 0 := by
  intro a ha hzero
  have h1 := hs.active_claim44 a ha hzero
  have h2 := chargeCoverScale_mul_rpow_le (squareDiameter_le_two_mul boundary hL (chargeSupport a))
  have : chargeDiameter boundary L a = squareDiameter boundary L (chargeSupport a) := rfl
  rw [← this] at h2
  linarith

theorem ScaleInvariant.mem_protected_of_neutral (hs : ScaleInvariant boundary L Z m s)
    (hL : 1 < L)
    (hm : (chargeCoverScale : ℝ) * ((2 * L : ℕ) : ℝ) ^ chargeCoverExponent ≤ levelThreshold m)
    {ρ : ChargeDensity L} (hρ : ρ ∈ s.Q) (hzero : ∑ x, ρ x = 0) : ρ ∈ s.G := by
  by_contra hG
  exact hs.active_charged hL hm ρ (Finset.mem_sdiff.mpr ⟨hρ, hG⟩) hzero

end Terminal

/-- `A_k = |𝒮_k|` at every natural scale (`|𝒮_0| = |supp|`). -/
theorem chargeA_ofNat_eq (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) (i : ℕ) :
    chargeA boundary L ρ (.ofNat i) = squareCoverNumber boundary L i ρ := by
  rcases i with _ | i
  · rw [chargeA_zero_eq_supportCard, squareCoverNumber_zero]
  · rfl

/-- `∑_{i ≤ n+1} A_{i−1}(ϱ) = |supp ϱ| + A(ϱ) ≤ 2 A(ϱ)` ( (4)). -/
theorem scaleCost_protectionCutoff_le (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L)
    (hd : 1 ≤ chargeDiameter boundary L ρ) :
    scaleCost boundary L ρ (protectionCutoff boundary L ρ + 2) ≤
      2 * chargeCoverCost boundary L ρ := by
  have hd0 : chargeDiameter boundary L ρ ≠ 0 := by omega
  have hcost : chargeCoverCost boundary L ρ =
      ∑ k ∈ range (protectionCutoff boundary L ρ + 1), squareCoverNumber boundary L k ρ := by
    simp only [chargeCoverCost, hd0, ↓reduceDIte]
    rfl
  have hsplit : scaleCost boundary L ρ (protectionCutoff boundary L ρ + 2) =
      (chargeSupport ρ).card + chargeCoverCost boundary L ρ := by
    unfold scaleCost
    rw [Finset.sum_range_succ', hcost, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => chargeA_ofNat_eq boundary L ρ i
  have hsupp : (chargeSupport ρ).card ≤ chargeCoverCost boundary L ρ := by
    rw [hcost, ← squareCoverNumber_zero boundary L ρ]
    exact Finset.single_le_sum (f := fun k => squareCoverNumber boundary L k ρ)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  omega

/-- The leaf product with the site weights of (2.7). -/
theorem leafProduct_siteLeafWeight {L : ℕ} (hat : (Fin L × Fin L) → ℕ → ℝ)
    (ρ : ChargeDensity L) :
    leafProduct (siteLeafWeight hat) ρ =
      ∏ j ∈ chargeSupport ρ, Real.exp ((ρ j : ℝ) ^ 2) * |hat j (ρ j).natAbs| := by
  unfold leafProduct siteLeafWeight
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : ((ρ j).natAbs : ℝ) = |(ρ j : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [h, sq_abs]

/-- **Properties (a)–(d) of KP Theorem 2.2** for a terminal branch. -/
theorem terminal_t22Properties {boundary : SquareBoundary} {L : ℕ} (hL : 1 < L)
    {hat : (Fin L × Fin L) → ℕ → ℝ} {m : ℕ} {s : ScaleState L}
    (hs : ScaleInvariant boundary L (siteLeafWeight hat) m s)
    (hm₁ : ((2 * L : ℕ) : ℝ) ≤ levelThreshold m)
    (hm₂ : (chargeCoverScale : ℝ) * ((2 * L : ℕ) : ℝ) ^ chargeCoverExponent ≤ levelThreshold m) :
    AtMostOneNonNeutral s.Q ∧ IsScaleSeparated boundary L s.Q ∧
      NeutralSplitsAreCharged boundary L s.Q ∧
      ∀ ϱ ∈ s.Q, ∑ j, ϱ j = 0 →
        |s.K ϱ| ≤ Real.exp (200 * chargeCoverCost boundary L ϱ) *
          ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |hat j (ϱ j).natAbs| := by
  classical
  have hcomm : ∀ ρ σ : ChargeDensity L,
      densityDistance boundary L ρ σ = densityDistance boundary L σ ρ :=
    fun ρ σ => squareDistance_symm boundary L _ _
  -- Non-neutral members are active.
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
    rw [← leafProduct_siteLeafWeight]
    refine (hs.protected_coeff ρ hG).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (StepData.leafProduct_nonneg
        (siteLeafWeight_nonneg hat) ρ))
    have : (scaleCost boundary L ρ (protectionCutoff boundary L ρ + 2) : ℝ) ≤
        2 * (chargeCoverCost boundary L ρ : ℝ) := by exact_mod_cast hcost
    linarith

/-! ### KP Theorem 2.2 -/

/-- **KP Theorem 2.2 on one square domain** (`D₂ = 200`), given KP Lemma 4.3 there. -/
theorem t22Step_of_basicLemmaStep (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (hstep : BasicLemmaStepStatement boundary L) : Reduction.T22Step boundary L 200 := by
  classical
  intro lam Nq lamHat hNq _ hlam
  obtain ⟨m, hm₁, hm₂⟩ := exists_terminalLevel L
  have hZ := siteLeafWeight_nonneg lamHat
  choose n c s hc hcsum hid hs using fun q : SiteFrequencyVector Nq =>
    exists_scaleIteration hL hstep hZ (initial_invariant boundary hL Nq lamHat q) m
  obtain ⟨hξpos, hξsum⟩ := siteFrequencyWeight_positive_sum Nq hNq
  let ι := Σ q : SiteFrequencyVector Nq, Fin (n q)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let st : Fin (Fintype.card ι) → ScaleState L := fun k => s (e.symm k).1 (e.symm k).2
  let w : Fin (Fintype.card ι) → ℝ := fun k =>
    siteFrequencyWeight Nq (e.symm k).1 * c (e.symm k).1 (e.symm k).2
  have hsumι : ∀ g : ι → ℝ, ∑ k, g (e.symm k) = ∑ q, ∑ i, g ⟨q, i⟩ := fun g => by
    rw [Equiv.sum_comp e.symm g, Fintype.sum_sigma]
  refine ⟨Fintype.card ι, fun k => (st k).Q, w, fun k => (st k).K, fun k => (hs _ _).ensemble,
    fun k => mul_pos (hξpos _) (hc _ _), ?_, fun ψ => ?_, fun k => ?_⟩
  · show ∑ k, w k = 1
    have := hsumι fun p => siteFrequencyWeight Nq p.1 * c p.1 p.2
    simp only [w]
    rw [this]
    simp_rw [← Finset.mul_sum, hcsum, mul_one]
    exact hξsum
  · have hmix := siteFrequency_mixture_eq Nq hNq lamHat lam hlam ψ
    rw [hmix]
    have hk := hsumι fun p => siteFrequencyWeight Nq p.1 * c p.1 p.2 *
      chargeFactorProduct (s p.1 p.2).Q (s p.1 p.2).K ψ
    have hgoal : ∑ k, w k * ∏ ϱ ∈ (st k).Q, (1 + (st k).K ϱ * Real.cos (∑ j, ψ j * ϱ j)) =
        ∑ k, siteFrequencyWeight Nq (e.symm k).1 * c (e.symm k).1 (e.symm k).2 *
          chargeFactorProduct (s (e.symm k).1 (e.symm k).2).Q (s (e.symm k).1 (e.symm k).2).K ψ :=
      rfl
    rw [hgoal, hk]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← siteFrequencyChargeProduct_eq Nq lamHat ψ q, hid q ψ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · exact terminal_t22Properties hL (hs _ _) hm₁ hm₂

/-- **KP Theorem 2.2** (`Reduction.t22Statement`, `D₂ = 200`), given KP Lemma 4.3 in the form
`BasicLemmaStepStatement` on every square domain. -/
theorem t22Statement_of_basicLemmaStep
    (hstep : ∀ L : ℕ, 1 < L →
      BasicLemmaStepStatement .free L ∧ (Even L → BasicLemmaStepStatement .periodic L)) :
    Reduction.t22Statement :=
  ⟨200, by norm_num, fun L hL =>
    ⟨t22Step_of_basicLemmaStep .free hL (hstep L hL).1,
      fun hEven => t22Step_of_basicLemmaStep .periodic hL ((hstep L hL).2 hEven)⟩⟩

/-- **KP Theorem 2.2** from the closed repaired KP Lemma 4.3 interface. -/
theorem t22Statement_of_repairedBasicLemma : Reduction.t22Statement :=
  t22Statement_of_basicLemmaStep fun _L hL =>
    ⟨basicLemmaStepStatement .free hL (Or.inl rfl),
      fun hEven => basicLemmaStepStatement .periodic hL (Or.inr hEven)⟩

/-- Theorem 2.2 from explicit lineage and neighbourhood-count hypotheses. -/
theorem t22Statement_of_lineageFormula (hlin : basicLemmaLineageFormulaStatement)
    (hcount : basicLemmaNeighborhoodCountStatement) : Reduction.t22Statement :=
  t22Statement_of_basicLemmaStep fun _ hL =>
    ⟨basicLemmaStepStatement_of_lineageFormula hlin hcount .free hL (Or.inl rfl),
      fun hEven => basicLemmaStepStatement_of_lineageFormula hlin hcount .periodic hL (Or.inr hEven)⟩

end FroehlichSpencer.BKT

end
