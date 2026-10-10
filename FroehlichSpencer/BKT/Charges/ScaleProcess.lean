/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ScaleAtoms
public import FroehlichSpencer.BKT.Charges.ScaleOverlap
public import FroehlichSpencer.BKT.Charges.BasicLemmaIdentity

/-!
A branch of the process is a
`ScaleState`: the current ensemble `Q_k`, the protected neutral factors `G_k ⊆ Q_k`, and the
coefficients `K`.

One step at scale `k` applies KP Lemma 4.3 to the active ensemble
`Q_{k-1} ∖ G_{k-1}` (through the interface `BasicLemmaStepStatement`), adjoins the protected
factors unchanged, and protects every new neutral output `ϱ` with `M d(ϱ)^α ≤ 2^k`.

This protection rule is the eligibility condition of KP Claim 4.4.

It differs from KP's greedy
pass ((4.17)–(4.18)), which may protect earlier; Theorem 2.2 is an existence statement, and the
rule keeps every invariant used by – while making Claim 4.4 hold by construction.

`ScaleInvariant` collects the invariants carried from scale to scale:

* the ensemble, protected-neutral and active-separation invariants ( (i)–(iii));
* Claim 4.4 for the active factors;
* the telescoped coefficient bound of  (with the overlap lemma , stored as a
  current-state bound: active factors carry `exp(100 ∑_{i<k} A_{i-1})`, protected factors
  `exp(100 ∑_{i ≤ n(ϱ)+1} A_{i-1})`;
* a `ScaleAtomFamily` for every factor, for property (c) (
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open Finset

/-! ### The Lemma 4.3 interface -/

/-- An output factor `a` (coefficient `Ka`) of one application of KP Lemma 4.3 at scale `k` to
`E` (coefficients `K`), with its active parents `P ⊆ E` (repaired L4.3: certified merge history
leaves, sign, conflict connectivity and the refined bound (4.11) with `C₁ = 100`). -/
structure IsScaleStepFactor (boundary : SquareBoundary) (L : ℕ) (k : ℕ) (E : ChargeEnsemble L)
    (K : ChargeDensity L → ℝ) (a : ChargeDensity L) (Ka : ℝ) (P : ChargeEnsemble L) : Prop where
  parents_subset : P ⊆ E
  parents_nonempty : P.Nonempty
  support_eq : chargeSupport a = P.biUnion chargeSupport
  sign : ∀ b ∈ P, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ chargeSupport b, a x = σ * b x
  connected : ∀ U ⊆ P, U.Nonempty → U ≠ P →
    ∃ b ∈ U, ∃ b' ∈ P, b' ∉ U ∧ densityDistance boundary L b b' ≤ 2 ^ k
  coefficient : |Ka| ≤
    Real.exp (100 * (chargeA boundary L a (basicLemmaPreviousScale k) : ℝ)) * ∏ b ∈ P, |K b|

/-- KP Lemma 4.3 (repaired, – as consumed by the scale process: for every `k` and every
`(k−1)`-separated ensemble `E` with coefficients `K`, a finite convex expansion (4.10) into
`k`-separated ensembles whose output factors satisfy `IsScaleStepFactor`. -/
def BasicLemmaStepStatement (boundary : SquareBoundary) (L : ℕ) : Prop :=
  ∀ (k : ℕ) (E : ChargeEnsemble L), IsChargeScaleEnsemble boundary E (basicLemmaPreviousScale k) →
    ∀ K : ChargeDensity L → ℝ, ∃ (n : ℕ) (F : Fin n → ChargeEnsemble L)
      (K' : Fin n → ChargeDensity L → ℝ) (c : Fin n → ℝ),
      (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
      (∀ ψ, chargeFactorProduct E K ψ = ∑ i, c i * chargeFactorProduct (F i) (K' i) ψ) ∧
      ∀ i, IsChargeScaleEnsemble boundary (F i) (.ofNat k) ∧
        ∃ par : ChargeDensity L → ChargeEnsemble L,
          (∀ a ∈ F i, ∀ a' ∈ F i, a ≠ a' → Disjoint (par a) (par a')) ∧
          ∀ a ∈ F i, IsScaleStepFactor boundary L k E K a (K' i a) (par a)

/-! ### States and invariants -/

/-- A branch of the scale process: the ensemble `Q`, the protected factors `G` and the
coefficients `K`. -/
structure ScaleState (L : ℕ) where
  /-- The current ensemble `Q_k`. -/
  Q : ChargeEnsemble L
  /-- The protected neutral factors `G_k`. -/
  G : ChargeEnsemble L
  /-- The coefficients `K(ϱ)`. -/
  K : ChargeDensity L → ℝ

/-- `∑_{i<m} A_{i-1}(ϱ)`, i.e. `A_{-1} + A_0 + ⋯ + A_{m-2}`. -/
def scaleCost (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) (m : ℕ) : ℕ :=
  ∑ i ∈ range m, chargeA boundary L ρ (basicLemmaPreviousScale i)

/-- KP's cutoff `n(ϱ) = ⌈log₂(M d(ϱ)^α)⌉` (2.3). -/
def protectionCutoff (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) : ℕ :=
  Nat.ceil (Real.logb 2 ((chargeCoverScale : ℝ) *
    (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent))

/-- The leaf product `∏_{j ∈ supp ϱ} Z(j, |ϱ(j)|)`. -/
def leafProduct {L : ℕ} (Z : (Fin L × Fin L) → ℕ → ℝ) (ρ : ChargeDensity L) : ℝ :=
  ∏ x ∈ chargeSupport ρ, Z x (ρ x).natAbs

/-- The invariants of the scale process after scale `k − 1` (state index `k`). -/
structure ScaleInvariant (boundary : SquareBoundary) (L : ℕ) (Z : (Fin L × Fin L) → ℕ → ℝ)
    (k : ℕ) (s : ScaleState L) : Prop where
  ensemble : IsBKTEnsemble s.Q
  protected_subset : s.G ⊆ s.Q
  protected_neutral : ∀ g ∈ s.G, ∑ x, g x = 0
  active_separated : IsChargeScaleEnsemble boundary (s.Q \ s.G) (basicLemmaPreviousScale k)
  protected_separated : ∀ g₁ ∈ s.G, ∀ g₂ ∈ s.G, g₁ ≠ g₂ →
    (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L g₁) (chargeDiameter boundary L g₂) : ℕ) : ℝ) ^
          chargeCoverExponent ≤ densityDistance boundary L g₁ g₂
  protected_active : ∀ g ∈ s.G, ∀ a ∈ s.Q \ s.G,
    (chargeCoverScale : ℝ) * (chargeDiameter boundary L g : ℝ) ^ chargeCoverExponent ≤
      densityDistance boundary L g a
  active_claim44 : ∀ a ∈ s.Q \ s.G, ∑ x, a x = 0 →
    (levelThreshold k : ℝ) <
      (chargeCoverScale : ℝ) * (chargeDiameter boundary L a : ℝ) ^ chargeCoverExponent
  active_coeff : ∀ a ∈ s.Q \ s.G,
    |s.K a| ≤ Real.exp (100 * (scaleCost boundary L a k : ℝ)) * leafProduct Z a
  protected_coeff : ∀ g ∈ s.G,
    |s.K g| ≤ Real.exp (100 * (scaleCost boundary L g (protectionCutoff boundary L g + 2) : ℝ)) *
      leafProduct Z g
  active_atoms : ∀ a ∈ s.Q \ s.G, Nonempty (ScaleAtomFamily boundary L a k)
  protected_atoms : ∀ g ∈ s.G, ∃ T, Nonempty (ScaleAtomFamily boundary L g T)

theorem levelThreshold_eq_separationThreshold (k : ℕ) :
    levelThreshold k = ChargeScale.separationThreshold (basicLemmaPreviousScale k) := by
  cases k <;> rfl

theorem IsChargeScaleEnsemble.subset {L : ℕ} {boundary : SquareBoundary} {E E' : ChargeEnsemble L}
    {s : ChargeScale} (hE : IsChargeScaleEnsemble boundary E s) (hsub : E' ⊆ E) :
    IsChargeScaleEnsemble boundary E' s :=
  ⟨IsBKTEnsemble_mono hE.1 hsub, fun ρ hρ σ hσ hne => hE.2 ρ (hsub hρ) σ (hsub hσ) hne⟩

theorem chargeSupport_nonempty {L : ℕ} {ρ : ChargeDensity L} (hρ : ρ ≠ 0) :
    (chargeSupport ρ).Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x, ρ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hρ (funext h)
  exact ⟨x, by simp [chargeSupport, hx]⟩

theorem disjoint_chargeSupport_of_isBKTEnsemble {L : ℕ} {E : ChargeEnsemble L}
    (hE : IsBKTEnsemble E) {ρ σ : ChargeDensity L} (hρ : ρ ∈ E) (hσ : σ ∈ E) (hne : ρ ≠ σ) :
    Disjoint (chargeSupport ρ) (chargeSupport σ) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact Set.disjoint_left.mp (hE.2 ρ hρ σ hσ hne) (by simpa [chargeSupport] using hx)
    (by simpa [chargeSupport] using hx')

/-- `M m^α ≤ M d^α` for natural `m ≤ d`. -/
theorem chargeCoverScale_mul_rpow_le {m d : ℕ} (h : m ≤ d) :
    (chargeCoverScale : ℝ) * (m : ℝ) ^ chargeCoverExponent ≤
      (chargeCoverScale : ℝ) * (d : ℝ) ^ chargeCoverExponent := by
  have hα : (0 : ℝ) ≤ chargeCoverExponent := by unfold chargeCoverExponent; norm_num
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) hα)
    (by positivity)

/-- A density distance is at least the minimum over the parents of the second argument. -/
theorem le_densityDistance_of_parents {L : ℕ} (boundary : SquareBoundary)
    {g a : ChargeDensity L} {P : ChargeEnsemble L} (c : ℝ) (hg : (chargeSupport g).Nonempty)
    (ha : chargeSupport a = P.biUnion chargeSupport) (hP : P.Nonempty)
    (hPne : ∀ b ∈ P, (chargeSupport b).Nonempty)
    (hc : ∀ b ∈ P, c ≤ densityDistance boundary L g b) :
    c ≤ densityDistance boundary L g a := by
  have hane : (chargeSupport a).Nonempty := by
    obtain ⟨b, hb⟩ := hP
    obtain ⟨x, hx⟩ := hPne b hb
    exact ⟨x, ha ▸ Finset.mem_biUnion.mpr ⟨b, hb, hx⟩⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_squareDistance_eq boundary L _ _ hg hane
  rw [ha] at hy
  obtain ⟨b, hb, hyb⟩ := Finset.mem_biUnion.mp hy
  have h1 := squareDistance_le_latticeDistance_of_mem boundary L (chargeSupport g)
    (chargeSupport b) x y hx hyb
  have h2 : densityDistance boundary L g a = latticeDistance boundary L x y := hxy
  have h3 : (densityDistance boundary L g b : ℝ) ≤ densityDistance boundary L g a := by
    rw [h2]
    exact_mod_cast h1
  exact (hc b hb).trans h3

/-- The protection rule at scale `k`: new neutral outputs with `M d(ϱ)^α ≤ 2^k` (the eligibility
condition of KP Claim 4.4). -/
def protectionSelect (boundary : SquareBoundary) (L k : ℕ) (F : ChargeEnsemble L) :
    ChargeEnsemble L :=
  F.filter fun a => ∑ x, a x = 0 ∧
    (chargeCoverScale : ℝ) * (chargeDiameter boundary L a : ℝ) ^ chargeCoverExponent ≤ 2 ^ k

theorem mem_protectionSelect {boundary : SquareBoundary} {L k : ℕ} {F : ChargeEnsemble L}
    {a : ChargeDensity L} :
    a ∈ protectionSelect boundary L k F ↔ a ∈ F ∧ ∑ x, a x = 0 ∧
      (chargeCoverScale : ℝ) * (chargeDiameter boundary L a : ℝ) ^ chargeCoverExponent ≤
        2 ^ k := by
  unfold protectionSelect
  rw [Finset.mem_filter]

/-- The state after applying one Lemma 4.3 branch `(F, K')` at scale `k`. -/
def stepState (boundary : SquareBoundary) (L k : ℕ) (s : ScaleState L) (F : ChargeEnsemble L)
    (K' : ChargeDensity L → ℝ) : ScaleState L where
  Q := s.G ∪ F
  G := s.G ∪ protectionSelect boundary L k F
  K := fun a => if a ∈ s.G then s.K a else K' a

section Step

variable {boundary : SquareBoundary} {L : ℕ} {Z : (Fin L × Fin L) → ℕ → ℝ}

/-- The output facts shared by the step lemmas. -/
structure StepData (boundary : SquareBoundary) (L k : ℕ) (Z : (Fin L × Fin L) → ℕ → ℝ)
    (s : ScaleState L) (F : ChargeEnsemble L) (K' : ChargeDensity L → ℝ)
    (par : ChargeDensity L → ChargeEnsemble L) : Prop where
  inv : ScaleInvariant boundary L Z k s
  scale : IsChargeScaleEnsemble boundary F (.ofNat k)
  factor : ∀ a ∈ F, IsScaleStepFactor boundary L k (s.Q \ s.G) s.K a (K' a) (par a)

namespace StepData

variable {k : ℕ} {s : ScaleState L} {F : ChargeEnsemble L} {K' : ChargeDensity L → ℝ}
  {par : ChargeDensity L → ChargeEnsemble L}

theorem output_ne_zero (D : StepData boundary L k Z s F K' par) {a : ChargeDensity L}
    (ha : a ∈ F) : a ≠ 0 := D.scale.1.1 a ha

theorem parent_mem (D : StepData boundary L k Z s F K' par) {a b : ChargeDensity L}
    (ha : a ∈ F) (hb : b ∈ par a) : b ∈ s.Q \ s.G := (D.factor a ha).parents_subset hb

theorem parent_ne_zero (D : StepData boundary L k Z s F K' par) {a b : ChargeDensity L}
    (ha : a ∈ F) (hb : b ∈ par a) : b ≠ 0 :=
  D.inv.ensemble.1 b (Finset.mem_sdiff.mp (D.parent_mem ha hb)).1

theorem parent_support_nonempty (D : StepData boundary L k Z s F K' par) {a b : ChargeDensity L}
    (ha : a ∈ F) (hb : b ∈ par a) : (chargeSupport b).Nonempty :=
  chargeSupport_nonempty (D.parent_ne_zero ha hb)

/-- Outputs are disjoint from protected factors. -/
theorem disjoint_protected (D : StepData boundary L k Z s F K' par) {a g : ChargeDensity L}
    (ha : a ∈ F) (hg : g ∈ s.G) : Disjoint (chargeSupport g) (chargeSupport a) := by
  rw [(D.factor a ha).support_eq, Finset.disjoint_biUnion_right]
  intro b hb
  have hbQ := D.parent_mem ha hb
  have hne : g ≠ b := fun h => (Finset.mem_sdiff.mp hbQ).2 (h ▸ hg)
  exact disjoint_chargeSupport_of_isBKTEnsemble D.inv.ensemble (D.inv.protected_subset hg)
    (Finset.mem_sdiff.mp hbQ).1 hne

theorem not_mem_protected (D : StepData boundary L k Z s F K' par) {a : ChargeDensity L}
    (ha : a ∈ F) : a ∉ s.G := by
  intro hg
  have h := D.disjoint_protected ha hg
  obtain ⟨x, hx⟩ := chargeSupport_nonempty (D.output_ne_zero ha)
  exact Finset.disjoint_left.mp h hx hx

/-- Protected factors stay `M d(g)^α` away from every new output ( (iii)). -/
theorem protected_far (D : StepData boundary L k Z s F K' par) {a g : ChargeDensity L}
    (ha : a ∈ F) (hg : g ∈ s.G) :
    (chargeCoverScale : ℝ) * (chargeDiameter boundary L g : ℝ) ^ chargeCoverExponent ≤
      densityDistance boundary L g a :=
  le_densityDistance_of_parents boundary _
    (chargeSupport_nonempty (D.inv.ensemble.1 g (D.inv.protected_subset hg)))
    (D.factor a ha).support_eq (D.factor a ha).parents_nonempty
    (fun _ hb => D.parent_support_nonempty ha hb)
    (fun b hb => D.inv.protected_active g hg b (D.parent_mem ha hb))

/-- Distinct outputs are more than `2^k` apart. -/
theorem output_far (D : StepData boundary L k Z s F K' par) {a a' : ChargeDensity L}
    (ha : a ∈ F) (ha' : a' ∈ F) (hne : a ≠ a') :
    ((2 : ℝ) ^ k) < densityDistance boundary L a a' := by
  have h := D.scale.2 a ha a' ha' hne
  have : ((2 ^ k : ℕ) : ℝ) < densityDistance boundary L a a' := by exact_mod_cast h
  simpa using this

/-- The leaf product of an output is the product of its parents' leaf products. -/
theorem leafProduct_eq (D : StepData boundary L k Z s F K' par) {a : ChargeDensity L}
    (ha : a ∈ F) : leafProduct Z a = ∏ b ∈ par a, leafProduct Z b := by
  classical
  have hf := D.factor a ha
  unfold leafProduct
  rw [hf.support_eq, Finset.prod_biUnion]
  · refine Finset.prod_congr rfl fun b hb => Finset.prod_congr rfl fun x hx => ?_
    obtain ⟨σ, hσ, hσx⟩ := hf.sign b hb
    rw [hσx x hx]
    rcases hσ with rfl | rfl <;> simp
  · intro b hb b' hb' hne
    exact disjoint_chargeSupport_of_isBKTEnsemble D.inv.ensemble
      (Finset.mem_sdiff.mp (D.parent_mem ha hb)).1 (Finset.mem_sdiff.mp (D.parent_mem ha hb')).1
      hne

theorem leafProduct_nonneg (hZ : ∀ x q, 0 ≤ Z x q) (ρ : ChargeDensity L) :
    0 ≤ leafProduct Z ρ :=
  Finset.prod_nonneg fun x _ => hZ x _

/--  summed over the scales below `k`: the parents' costs add up to at most the output's. -/
theorem sum_scaleCost_le (D : StepData boundary L k Z s F K' par) (hL : 1 < L)
    {a : ChargeDensity L} (ha : a ∈ F) :
    ∑ b ∈ par a, scaleCost boundary L b k ≤ scaleCost boundary L a k := by
  classical
  unfold scaleCost
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i < k := Finset.mem_range.mp hi
  have hsep : IsChargeScaleEnsemble boundary (par a) (.ofNat i) := by
    refine (D.inv.active_separated.subset (D.factor a ha).parents_subset).mono ?_
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    show 2 ^ i ≤ 2 ^ m
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sum_chargeA_le_of_scaleSeparated boundary hL i (par a) hsep a fun b hb x hx => by
    rw [(D.factor a ha).support_eq]
    exact Finset.mem_biUnion.mpr ⟨b, hb, hx⟩

/-- The telescoped coefficient bound for a new output ( (3), one scale). -/
theorem output_coeff (D : StepData boundary L k Z s F K' par) (hL : 1 < L)
    (hZ : ∀ x q, 0 ≤ Z x q) {a : ChargeDensity L} (ha : a ∈ F) :
    |K' a| ≤ Real.exp (100 * (scaleCost boundary L a (k + 1) : ℝ)) * leafProduct Z a := by
  classical
  have hf := D.factor a ha
  set A : ℝ := (chargeA boundary L a (basicLemmaPreviousScale k) : ℝ)
  have hprod : ∏ b ∈ par a, |s.K b| ≤
      Real.exp (100 * ((∑ b ∈ par a, scaleCost boundary L b k : ℕ) : ℝ)) * leafProduct Z a := by
    calc ∏ b ∈ par a, |s.K b|
        ≤ ∏ b ∈ par a, (Real.exp (100 * (scaleCost boundary L b k : ℝ)) * leafProduct Z b) :=
          Finset.prod_le_prod₀ (fun b _ => abs_nonneg _)
            (fun b hb => D.inv.active_coeff b (D.parent_mem ha hb))
      _ = Real.exp (100 * ((∑ b ∈ par a, scaleCost boundary L b k : ℕ) : ℝ)) *
            ∏ b ∈ par a, leafProduct Z b := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum]
          congr 2
          push_cast
          rw [Finset.mul_sum]
      _ = _ := by rw [D.leafProduct_eq ha]
  have hcost : ((∑ b ∈ par a, scaleCost boundary L b k : ℕ) : ℝ) ≤ scaleCost boundary L a k := by
    exact_mod_cast D.sum_scaleCost_le hL ha
  have hsucc : (scaleCost boundary L a (k + 1) : ℝ) = scaleCost boundary L a k + A := by
    unfold scaleCost
    rw [Finset.sum_range_succ]
    push_cast
    rfl
  have hleaf := leafProduct_nonneg hZ a
  calc |K' a| ≤ Real.exp (100 * A) * ∏ b ∈ par a, |s.K b| := hf.coefficient
    _ ≤ Real.exp (100 * A) * (Real.exp (100 * ((∑ b ∈ par a, scaleCost boundary L b k : ℕ) : ℝ)) *
          leafProduct Z a) := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ ≤ Real.exp (100 * A) * (Real.exp (100 * (scaleCost boundary L a k : ℝ)) * leafProduct Z a) := by
        gcongr
    _ = Real.exp (100 * (scaleCost boundary L a (k + 1) : ℝ)) * leafProduct Z a := by
        rw [hsucc, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- Every output carries a scale-atom family with top level `k + 1` ( bookkeeping). -/
theorem output_atoms (D : StepData boundary L k Z s F K' par) {a : ChargeDensity L}
    (ha : a ∈ F) : Nonempty (ScaleAtomFamily boundary L a (k + 1)) := by
  have hf := D.factor a ha
  refine ScaleAtomFamily.merge k a (par a) hf.parents_nonempty
    (fun b hb => D.inv.active_atoms b (D.parent_mem ha hb)) ?_
    (fun b hb => D.parent_support_nonempty ha hb) hf.support_eq hf.sign ?_ hf.connected
    (fun b hb hb0 => D.inv.active_claim44 b (D.parent_mem ha hb) hb0)
  · intro b hb b' hb' hne
    exact disjoint_chargeSupport_of_isBKTEnsemble D.inv.ensemble
      (Finset.mem_sdiff.mp (D.parent_mem ha hb)).1 (Finset.mem_sdiff.mp (D.parent_mem ha hb')).1
      hne
  · intro b hb b' hb' hne
    rw [levelThreshold_eq_separationThreshold]
    exact D.inv.active_separated.2 b (D.parent_mem ha hb) b' (D.parent_mem ha hb') hne

/-- A newly protected factor at scale `k ≥ 1` has `2^{k−1} ≤ M d^α`: a single active parent
would itself be eligible (Claim 4.4), two parents are `2^{k−1}` apart inside `supp ϱ`
( (2)). -/
theorem selected_large (D : StepData boundary L k Z s F K' par) (hL : 1 < L)
    {a : ChargeDensity L} (ha : a ∈ F) (hneutral : ∑ x, a x = 0) (hk : 1 ≤ k) :
    (2 : ℝ) ^ (k - 1) ≤
      (chargeCoverScale : ℝ) * (chargeDiameter boundary L a : ℝ) ^ chargeCoverExponent := by
  classical
  have hf := D.factor a ha
  have hthr : (levelThreshold k : ℝ) = 2 ^ (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [levelThreshold_succ]
    push_cast
    simp
  have hd1 : 1 ≤ chargeDiameter boundary L a :=
    one_le_chargeDiameter_of_neutral boundary hL a (D.output_ne_zero ha) hneutral
  have hlt := lt_chargeCoverScale_mul_rpow (d := (chargeDiameter boundary L a : ℝ))
    (by exact_mod_cast hd1)
  by_cases htwo : ∃ b ∈ par a, ∃ b' ∈ par a, b ≠ b'
  · obtain ⟨b, hb, b', hb', hne⟩ := htwo
    have hsep := D.inv.active_separated.2 b (D.parent_mem ha hb) b' (D.parent_mem ha hb') hne
    rw [← levelThreshold_eq_separationThreshold] at hsep
    have hsub : ∀ c ∈ par a, chargeSupport c ⊆ chargeSupport a := fun c hc x hx => by
      rw [hf.support_eq]; exact Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
    have hdist := squareDistance_le_squareDiameter_of_subset boundary L
      (D.parent_support_nonempty ha hb) (D.parent_support_nonempty ha hb') (hsub b hb) (hsub b' hb')
    have h1 : (levelThreshold k : ℝ) < chargeDiameter boundary L a := by
      have : levelThreshold k < chargeDiameter boundary L a := lt_of_lt_of_le hsep hdist
      exact_mod_cast this
    rw [hthr] at h1
    linarith
  · push Not at htwo
    obtain ⟨b, hb⟩ := hf.parents_nonempty
    have hsingle : par a = {b} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hb, fun c hc => htwo c hc b hb⟩
    have hsupp : chargeSupport a = chargeSupport b := by rw [hf.support_eq, hsingle]; simp
    obtain ⟨σ, hσ, hσx⟩ := hf.sign b hb
    have hbneutral : ∑ x, b x = 0 := by
      have hsa : ∑ x, a x = ∑ x ∈ chargeSupport a, a x :=
        (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => by
          simpa [chargeSupport] using hx).symm
      have hsb : ∑ x, b x = ∑ x ∈ chargeSupport b, b x :=
        (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => by
          simpa [chargeSupport] using hx).symm
      rw [hsa, hsupp, Finset.sum_congr rfl hσx, ← Finset.mul_sum, ← hsb] at hneutral
      rcases hσ with rfl | rfl
      · simpa using hneutral
      · simpa using hneutral
    have hdiam : chargeDiameter boundary L b = chargeDiameter boundary L a := by
      unfold chargeDiameter; rw [hsupp]
    have h44 := D.inv.active_claim44 b (D.parent_mem ha hb) hbneutral
    rw [hdiam, hthr] at h44
    exact h44.le

end StepData

namespace StepData

variable {k : ℕ} {s : ScaleState L} {F : ChargeEnsemble L} {K' : ChargeDensity L → ℝ}
  {par : ChargeDensity L → ChargeEnsemble L}

theorem cutoff_ge (D : StepData boundary L k Z s F K' par) (hL : 1 < L) {a : ChargeDensity L}
    (ha : a ∈ F) (hneutral : ∑ x, a x = 0) : k + 1 ≤ protectionCutoff boundary L a + 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  have hlarge := D.selected_large hL ha hneutral hk
  set y := (chargeCoverScale : ℝ) * (chargeDiameter boundary L a : ℝ) ^ chargeCoverExponent
  have hy : 0 < y := lt_of_lt_of_le (by positivity) hlarge
  have hlog : ((k - 1 : ℕ) : ℝ) ≤ Real.logb 2 y := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hy]
    rw [Real.rpow_natCast]
    exact hlarge
  have hceil : Real.logb 2 y ≤ (protectionCutoff boundary L a : ℝ) := Nat.le_ceil _
  have : ((k - 1 : ℕ) : ℝ) ≤ (protectionCutoff boundary L a : ℝ) := hlog.trans hceil
  have : k - 1 ≤ protectionCutoff boundary L a := by exact_mod_cast this
  omega

/-- **One scale of the process preserves the invariants** (KP Claim 4.4). -/
theorem invariant (D : StepData boundary L k Z s F K' par) (hL : 1 < L)
    (hZ : ∀ x q, 0 ≤ Z x q) : ScaleInvariant boundary L Z (k + 1) (stepState boundary L k s F K') := by
  classical
  have hsel : ∀ {a}, a ∈ protectionSelect boundary L k F → a ∈ F := fun h =>
    (mem_protectionSelect.mp h).1
  have hactive : ∀ {a}, a ∈ (s.G ∪ F) \ (s.G ∪ protectionSelect boundary L k F) →
      a ∈ F ∧ a ∉ protectionSelect boundary L k F := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp ha
    rcases Finset.mem_union.mp h1 with hG | hF
    · exact absurd (Finset.mem_union_left _ hG) h2
    · exact ⟨hF, fun h => h2 (Finset.mem_union_right _ h)⟩
  have hK : ∀ a ∈ F, (stepState boundary L k s F K').K a = K' a := fun a ha => by
    simp [stepState, D.not_mem_protected ha]
  have hKG : ∀ g ∈ s.G, (stepState boundary L k s F K').K g = s.K g := fun g hg => by
    simp [stepState, hg]
  have hmin : ∀ g₁ g₂ : ChargeDensity L,
      (chargeCoverScale : ℝ) *
          ((min (chargeDiameter boundary L g₁) (chargeDiameter boundary L g₂) : ℕ) : ℝ) ^
            chargeCoverExponent ≤
        (chargeCoverScale : ℝ) * (chargeDiameter boundary L g₁ : ℝ) ^ chargeCoverExponent :=
    fun g₁ g₂ => chargeCoverScale_mul_rpow_le (min_le_left _ _)
  have hmin' : ∀ g₁ g₂ : ChargeDensity L,
      (chargeCoverScale : ℝ) *
          ((min (chargeDiameter boundary L g₁) (chargeDiameter boundary L g₂) : ℕ) : ℝ) ^
            chargeCoverExponent ≤
        (chargeCoverScale : ℝ) * (chargeDiameter boundary L g₂ : ℝ) ^ chargeCoverExponent :=
    fun g₁ g₂ => chargeCoverScale_mul_rpow_le (min_le_right _ _)
  have hcomm : ∀ ρ σ : ChargeDensity L,
      densityDistance boundary L ρ σ = densityDistance boundary L σ ρ :=
    fun ρ σ => squareDistance_symm boundary L _ _
  refine
    { ensemble := ?_
      protected_subset := ?_
      protected_neutral := ?_
      active_separated := ?_
      protected_separated := ?_
      protected_active := ?_
      active_claim44 := ?_
      active_coeff := ?_
      protected_coeff := ?_
      active_atoms := ?_
      protected_atoms := ?_ }
  · -- ensemble
    refine ⟨fun ρ hρ => ?_, fun ρ hρ σ hσ hne => ?_⟩
    · rcases Finset.mem_union.mp hρ with h | h
      · exact D.inv.ensemble.1 ρ (D.inv.protected_subset h)
      · exact D.output_ne_zero h
    · have key : Disjoint (chargeSupport ρ) (chargeSupport σ) := by
        rcases Finset.mem_union.mp hρ with h1 | h1 <;> rcases Finset.mem_union.mp hσ with h2 | h2
        · exact disjoint_chargeSupport_of_isBKTEnsemble D.inv.ensemble
            (D.inv.protected_subset h1) (D.inv.protected_subset h2) hne
        · exact D.disjoint_protected h2 h1
        · exact (D.disjoint_protected h1 h2).symm
        · exact disjoint_chargeSupport_of_isBKTEnsemble D.scale.1 h1 h2 hne
      rw [Set.disjoint_left]
      intro x hx hx'
      exact Finset.disjoint_left.mp key (by simpa [chargeSupport] using hx)
        (by simpa [chargeSupport] using hx')
  · -- protected ⊆ ensemble
    exact Finset.union_subset_union (subset_refl _) (Finset.filter_subset _ _)
  · -- protected factors are neutral
    intro g hg
    rcases Finset.mem_union.mp hg with h | h
    · exact D.inv.protected_neutral g h
    · exact (mem_protectionSelect.mp h).2.1
  · -- active separation
    exact D.scale.subset fun a ha => (hactive ha).1
  · -- protected pairs (4.17)
    intro g₁ hg₁ g₂ hg₂ hne
    rcases Finset.mem_union.mp hg₁ with h1 | h1 <;> rcases Finset.mem_union.mp hg₂ with h2 | h2
    · exact D.inv.protected_separated g₁ h1 g₂ h2 hne
    · exact (hmin g₁ g₂).trans (D.protected_far (hsel h2) h1)
    · rw [hcomm]
      exact (hmin' g₁ g₂).trans (D.protected_far (hsel h1) h2)
    · have hfar := D.output_far (hsel h1) (hsel h2) hne
      exact ((hmin g₁ g₂).trans (mem_protectionSelect.mp h1).2.2).trans hfar.le
  · -- protected vs active (4.18)
    intro g hg a ha
    obtain ⟨haF, hasel⟩ := hactive ha
    rcases Finset.mem_union.mp hg with h | h
    · exact D.protected_far haF h
    · have hne : g ≠ a := fun he => hasel (he ▸ h)
      exact (mem_protectionSelect.mp h).2.2.trans (D.output_far (hsel h) haF hne).le
  · -- Claim 4.4
    intro a ha hneutral
    obtain ⟨haF, hasel⟩ := hactive ha
    rw [levelThreshold_succ]
    push_cast
    by_contra hcon
    push Not at hcon
    exact hasel (mem_protectionSelect.mpr ⟨haF, hneutral, hcon⟩)
  · -- active coefficients
    intro a ha
    rw [hK a (hactive ha).1]
    exact D.output_coeff hL hZ (hactive ha).1
  · -- protected coefficients
    intro g hg
    rcases Finset.mem_union.mp hg with h | h
    · rw [hKG g h]
      exact D.inv.protected_coeff g h
    · have hgF := hsel h
      rw [hK g hgF]
      refine (D.output_coeff hL hZ hgF).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (leafProduct_nonneg hZ g)
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      have hle := D.cutoff_ge hL hgF (mem_protectionSelect.mp h).2.1
      unfold scaleCost
      exact_mod_cast Finset.sum_le_sum_of_subset (Finset.range_mono hle)
  · -- active atoms
    intro a ha
    exact D.output_atoms (hactive ha).1
  · -- protected atoms
    intro g hg
    rcases Finset.mem_union.mp hg with h | h
    · exact D.inv.protected_atoms g h
    · exact ⟨k + 1, D.output_atoms (hsel h)⟩

end StepData

/-- The product over a state splits into protected and active factors. -/
theorem chargeFactorProduct_protected_mul_active {L : ℕ} (s : ScaleState L) (hG : s.G ⊆ s.Q)
    (ψ : (Fin L × Fin L) → ℝ) :
    chargeFactorProduct s.Q s.K ψ =
      chargeFactorProduct s.G s.K ψ * chargeFactorProduct (s.Q \ s.G) s.K ψ := by
  classical
  unfold chargeFactorProduct
  rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hG]

/-- **One scale of the process** (: a state with the scale-`k` invariants is a positive
convex combination, identically in `ψ`, of states with the scale-`(k+1)` invariants. -/
theorem exists_scaleStep {boundary : SquareBoundary} {L : ℕ} (hL : 1 < L)
    (hstep : BasicLemmaStepStatement boundary L) {Z : (Fin L × Fin L) → ℕ → ℝ}
    (hZ : ∀ x q, 0 ≤ Z x q) {k : ℕ} {s : ScaleState L} (hs : ScaleInvariant boundary L Z k s) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (s' : Fin n → ScaleState L),
      (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
      (∀ ψ, chargeFactorProduct s.Q s.K ψ = ∑ i, c i * chargeFactorProduct (s' i).Q (s' i).K ψ) ∧
      ∀ i, ScaleInvariant boundary L Z (k + 1) (s' i) := by
  classical
  obtain ⟨n, F, K', c, hc, hcsum, hid, hF⟩ :=
    hstep k (s.Q \ s.G) hs.active_separated s.K
  choose hFscale par _ hfac using hF
  have D : ∀ i, StepData boundary L k Z s (F i) (K' i) (par i) := fun i =>
    ⟨hs, hFscale i, hfac i⟩
  refine ⟨n, c, fun i => stepState boundary L k s (F i) (K' i), hc, hcsum, fun ψ => ?_,
    fun i => (D i).invariant hL hZ⟩
  rw [chargeFactorProduct_protected_mul_active s hs.protected_subset ψ, hid ψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdisj : Disjoint s.G (F i) := by
    rw [Finset.disjoint_left]
    intro a hG hF
    exact (D i).not_mem_protected hF hG
  show _ = c i * ∏ ρ ∈ s.G ∪ F i, chargeFactor (stepState boundary L k s (F i) (K' i)).K ψ ρ
  rw [Finset.prod_union hdisj]
  unfold chargeFactorProduct
  have h1 : ∏ ρ ∈ s.G, chargeFactor s.K ψ ρ =
      ∏ ρ ∈ s.G, chargeFactor (stepState boundary L k s (F i) (K' i)).K ψ ρ :=
    Finset.prod_congr rfl fun ρ hρ => by simp [chargeFactor, stepState, hρ]
  have h2 : ∏ ρ ∈ F i, chargeFactor (K' i) ψ ρ =
      ∏ ρ ∈ F i, chargeFactor (stepState boundary L k s (F i) (K' i)).K ψ ρ :=
    Finset.prod_congr rfl fun ρ hρ => by
      simp [chargeFactor, stepState, (D i).not_mem_protected hρ]
  rw [h1, h2]
  ring

end Step

end FroehlichSpencer.BKT

end
