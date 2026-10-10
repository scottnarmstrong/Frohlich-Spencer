/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGExpansion

/-!
A configuration `⟨j, A, F, K⟩` is a base scale `s = 2^j/2`, actives `A`,  densities `F` and the
current coefficient function `K`.

`SelStep` is one branch of FS81's (2.13) rewrite of an active pair
at distance `≤ 2s` (keep `a`, keep `c`, merge `a − c`, merge `a + c`, with the source coefficient
updates), or a freezing stage.

`SelReach` is its reflexive-transitive closure.

* `SelStep.selectionState`: every step preserves the selection invariants of `SelectionG`.
* `exists_runExpansion`: every configuration satisfying the invariants expands, as a finite convex
  combination uniformly in `ψ`, into terminal configurations (`A = ∅`) **reachable from it**.
* `SelReach.geometry`: a terminal configuration reachable from a single-site start has the full
  Appendix D geometry.

Recording reachability lets later statements (the coefficient bound, the terminal waves) quantify
over exactly the ensembles the expansion produces.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- A selection configuration. -/
structure SelConfig (L : ℕ) where
  /-- The scale index: the base scale is `2^j/2`. -/
  j : ℕ
  /-- The active densities. -/
  A : Finset (ChargeDensity L)
  /--
The densities.
-/
  F : Finset (ChargeDensity L)
  /-- The current coefficient function. -/
  K : ChargeDensity L → ℝ

/-- The base scale `2^j/2`. -/
def SelConfig.scale (S : SelConfig L) : ℝ := (2 : ℝ) ^ S.j / 2

theorem SelConfig.scale_pos (S : SelConfig L) : 0 < S.scale := by
  unfold SelConfig.scale
  positivity

/-- One step of the selection: a branch of the (2.13) pair rewrite, or a freezing stage. -/
inductive SelStep (M α : ℝ) : SelConfig L → SelConfig L → Prop
  | keepLeft {S : SelConfig L} {a c : ChargeDensity L} (ha : a ∈ S.A) (hc : c ∈ S.A) (hne : a ≠ c)
      (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale) :
      SelStep M α S ⟨S.j, S.A.erase c, S.F, pairRewriteFirstCoefficient S.K a⟩
  | keepRight {S : SelConfig L} {a c : ChargeDensity L} (ha : a ∈ S.A) (hc : c ∈ S.A)
      (hne : a ≠ c)
      (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale) :
      SelStep M α S ⟨S.j, S.A.erase a, S.F, pairRewriteSecondCoefficient S.K c⟩
  | mergeSub {S : SelConfig L} {a c : ChargeDensity L} (ha : a ∈ S.A) (hc : c ∈ S.A)
      (hne : a ≠ c)
      (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale) :
      SelStep M α S ⟨S.j, insert (a - c) ((S.A.erase a).erase c), S.F,
        pairRewriteDifferenceCoefficient S.K a c⟩
  | mergeAdd {S : SelConfig L} {a c : ChargeDensity L} (ha : a ∈ S.A) (hc : c ∈ S.A)
      (hne : a ≠ c)
      (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale) :
      SelStep M α S ⟨S.j, insert (a + c) ((S.A.erase a).erase c), S.F,
        pairRewriteSumCoefficient S.K a c⟩
  | freeze {S : SelConfig L} {J : Finset (ChargeDensity L)}
      (hfar : ∀ ρ ∈ S.A, ∀ σ ∈ S.A, ρ ≠ σ →
        2 * S.scale < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ))
      (hJ : IsMaximalFreezeSet M α S.A J) :
      SelStep M α S ⟨S.j + 1, S.A \ J, S.F ∪ J, S.K⟩

/-- Reachability under selection steps. -/
abbrev SelReach (M α : ℝ) : SelConfig L → SelConfig L → Prop :=
  Relation.ReflTransGen (SelStep M α)

/-- The selection invariants of a configuration. -/
def SelConfig.Valid (M α : ℝ) (S : SelConfig L) : Prop :=
  SelectionState M α S.scale S.A S.F

variable {M α : ℝ}

theorem SelStep.valid (hM : 1 < M) (hα : 1 ≤ α) {S T : SelConfig L} (h : SelStep M α S T)
    (hS : S.Valid M α) : T.Valid M α := by
  cases h with
  | keepLeft ha hc hne hD => exact hS.erase _
  | keepRight ha hc hne hD => exact hS.erase _
  | mergeSub ha hc hne hD =>
    have hm := hS.merge hM hα S.scale_pos ha hc hne hD (ε := -1) (Or.inr rfl)
    rw [neg_one_smul, ← sub_eq_add_neg] at hm
    exact hm
  | mergeAdd ha hc hne hD =>
    have hm := hS.merge hM hα S.scale_pos ha hc hne hD (ε := 1) (Or.inl rfl)
    rw [one_smul] at hm
    exact hm
  | freeze hfar hJ =>
    have h := hS.freeze (by linarith) (by linarith) S.scale_pos.le hfar hJ
    unfold SelConfig.Valid SelConfig.scale
    convert h using 2
    simp only [SelConfig.scale, pow_succ]
    ring

theorem SelReach.valid (hM : 1 < M) (hα : 1 ≤ α) {S T : SelConfig L} (h : SelReach M α S T)
    (hS : S.Valid M α) : T.Valid M α := by
  induction h with
  | refl => exact hS
  | tail _ hstep ih => exact hstep.valid hM hα ih

/-- The single-site start at base `1/2`. -/
def SelConfig.start (E : Finset (ChargeDensity L)) (K : ChargeDensity L → ℝ) : SelConfig L :=
  ⟨0, E, ∅, K⟩

theorem SelConfig.start_valid (hM : 1 < M) (hα : 1 ≤ α) {E : Finset (ChargeDensity L)}
    (hE : IsPinnedChargeEnsemble E) (hsingle : ∀ ρ ∈ E, (chargeSupport ρ).card = 1)
    (K : ChargeDensity L → ℝ) : (SelConfig.start E K).Valid M α := by
  have h := SelectionState.initial (M := M) (α := α) hM hα hE hsingle
  unfold SelConfig.Valid SelConfig.scale SelConfig.start
  convert h using 2
  norm_num

/-- **Terminal geometry.** A terminal configuration reachable from a valid one has the full
Appendix D geometry. -/
theorem SelReach.geometry (hM : 1 < M) (hα : 1 ≤ α) {S T : SelConfig L} (h : SelReach M α S T)
    (hS : S.Valid M α) (hT : T.A = ∅) : AppendixDChargeGeometry M α T.F := by
  have hv := h.valid hM hα hS
  unfold SelConfig.Valid at hv
  rw [hT] at hv
  exact hv.geometry

/-! ### The run expansion -/

/-- A finite convex expansion of a configuration's charge-factor product into terminal
configurations reachable from it. -/
def IsRunExpansion (M α : ℝ) (S : SelConfig L) (B : List (ℝ × SelConfig L)) : Prop :=
  (∀ b ∈ B, 0 < b.1 ∧ b.2.A = ∅ ∧ SelReach M α S b.2) ∧ (B.map fun b => b.1).sum = 1 ∧
    ∀ ψ, chargeFactorProduct (S.A ∪ S.F) S.K ψ =
      (B.map fun b => b.1 * chargeFactorProduct b.2.F b.2.K ψ).sum

/-- Rescale the weights of a run family. -/
def scaleRun (w : ℝ) (B : List (ℝ × SelConfig L)) : List (ℝ × SelConfig L) :=
  B.map fun b => (w * b.1, b.2)

theorem sum_scaleRun_weight (w : ℝ) (B : List (ℝ × SelConfig L)) :
    ((scaleRun w B).map fun b => b.1).sum = w * (B.map fun b => b.1).sum := by
  simp only [scaleRun, List.map_map]
  rw [← List.sum_map_mul_left]
  rfl

theorem sum_scaleRun_prod (w : ℝ) (B : List (ℝ × SelConfig L)) (ψ : Site L → ℝ) :
    ((scaleRun w B).map fun b => b.1 * chargeFactorProduct b.2.F b.2.K ψ).sum =
      w * (B.map fun b => b.1 * chargeFactorProduct b.2.F b.2.K ψ).sum := by
  simp only [scaleRun, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b _
  simp [mul_assoc]

theorem IsRunExpansion.of_step {S T : SelConfig L} (hst : SelStep M α S T)
    (hprod : ∀ ψ, chargeFactorProduct (S.A ∪ S.F) S.K ψ = chargeFactorProduct (T.A ∪ T.F) T.K ψ)
    {B : List (ℝ × SelConfig L)} (hB : IsRunExpansion M α T B) : IsRunExpansion M α S B :=
  ⟨fun b hb => ⟨(hB.1 b hb).1, (hB.1 b hb).2.1, Relation.ReflTransGen.head hst (hB.1 b hb).2.2⟩,
    hB.2.1, fun ψ => (hprod ψ).trans (hB.2.2 ψ)⟩

theorem IsRunExpansion.combine {S S₁ S₂ S₃ S₄ : SelConfig L}
    (h₁s : SelStep M α S S₁) (h₂s : SelStep M α S S₂) (h₃s : SelStep M α S S₃)
    (h₄s : SelStep M α S S₄) {B₁ B₂ B₃ B₄ : List (ℝ × SelConfig L)}
    (h₁ : IsRunExpansion M α S₁ B₁) (h₂ : IsRunExpansion M α S₂ B₂)
    (h₃ : IsRunExpansion M α S₃ B₃) (h₄ : IsRunExpansion M α S₄ B₄)
    (hid : ∀ ψ, chargeFactorProduct (S.A ∪ S.F) S.K ψ =
      (1 / 3 : ℝ) * chargeFactorProduct (S₁.A ∪ S₁.F) S₁.K ψ +
        (1 / 3 : ℝ) * chargeFactorProduct (S₂.A ∪ S₂.F) S₂.K ψ +
        (1 / 6 : ℝ) * chargeFactorProduct (S₃.A ∪ S₃.F) S₃.K ψ +
        (1 / 6 : ℝ) * chargeFactorProduct (S₄.A ∪ S₄.F) S₄.K ψ) :
    IsRunExpansion M α S
      (scaleRun (1 / 3) B₁ ++ scaleRun (1 / 3) B₂ ++ scaleRun (1 / 6) B₃ ++ scaleRun (1 / 6) B₄) := by
  refine ⟨fun b hb => ?_, ?_, fun ψ => ?_⟩
  · have mem : ∀ {w : ℝ} {T : SelConfig L} {B : List (ℝ × SelConfig L)}, 0 < w →
        SelStep M α S T → IsRunExpansion M α T B → b ∈ scaleRun w B →
        0 < b.1 ∧ b.2.A = ∅ ∧ SelReach M α S b.2 := by
      intro w T B hw hst hB hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      obtain ⟨h1, h2, h3⟩ := hB.1 b' hb'
      exact ⟨mul_pos hw h1, h2, Relation.ReflTransGen.head hst h3⟩
    simp only [List.mem_append] at hb
    rcases hb with ((hb | hb) | hb) | hb
    · exact mem (by norm_num) h₁s h₁ hb
    · exact mem (by norm_num) h₂s h₂ hb
    · exact mem (by norm_num) h₃s h₃ hb
    · exact mem (by norm_num) h₄s h₄ hb
  · simp only [List.map_append, List.sum_append, sum_scaleRun_weight, h₁.2.1, h₂.2.1, h₃.2.1,
      h₄.2.1]
    norm_num
  · simp only [List.map_append, List.sum_append, sum_scaleRun_prod, ← h₁.2.2, ← h₂.2.2, ← h₃.2.2,
      ← h₄.2.2]
    exact hid ψ

/-- One four-branch pair step. -/
theorem runPairStep (hM : 1 < M) (hα : 1 ≤ α) {S : SelConfig L} (h : S.Valid M α)
    {a c : ChargeDensity L} (ha : a ∈ S.A) (hc : c ∈ S.A) (hne : a ≠ c)
    (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale)
    (IH : ∀ T : SelConfig L, T.j = S.j → T.F = S.F → T.A.card < S.A.card → T.Valid M α →
      ∃ B, IsRunExpansion M α T B) :
    ∃ B, IsRunExpansion M α S B := by
  classical
  have haF : a ∉ S.F := fun h' => Finset.disjoint_left.mp h.disjoint ha h'
  have hcF : c ∉ S.F := fun h' => Finset.disjoint_left.mp h.disjoint hc h'
  have hcard3 : ∀ τ, (insert τ ((S.A.erase a).erase c)).card < S.A.card := by
    intro τ
    have hc' : c ∈ S.A.erase a := Finset.mem_erase.mpr ⟨Ne.symm hne, hc⟩
    have := Finset.card_insert_le τ ((S.A.erase a).erase c)
    have e1 := Finset.card_erase_of_mem hc'
    have e2 := Finset.card_erase_of_mem ha
    have hpos : 0 < (S.A.erase a).card := Finset.card_pos.mpr ⟨c, hc'⟩
    omega
  have s₁ := SelStep.keepLeft (M := M) (α := α) ha hc hne hD
  have s₂ := SelStep.keepRight (M := M) (α := α) ha hc hne hD
  have s₃ := SelStep.mergeSub (M := M) (α := α) ha hc hne hD
  have s₄ := SelStep.mergeAdd (M := M) (α := α) ha hc hne hD
  obtain ⟨B₁, h₁⟩ := IH ⟨S.j, S.A.erase c, S.F, pairRewriteFirstCoefficient S.K a⟩ rfl rfl
    (Finset.card_erase_lt_of_mem hc) (s₁.valid hM hα h)
  obtain ⟨B₂, h₂⟩ := IH ⟨S.j, S.A.erase a, S.F, pairRewriteSecondCoefficient S.K c⟩ rfl rfl
    (Finset.card_erase_lt_of_mem ha) (s₂.valid hM hα h)
  obtain ⟨B₃, h₃⟩ := IH ⟨S.j, insert (a - c) ((S.A.erase a).erase c), S.F,
    pairRewriteDifferenceCoefficient S.K a c⟩ rfl rfl (hcard3 _) (s₃.valid hM hα h)
  obtain ⟨B₄, h₄⟩ := IH ⟨S.j, insert (a + c) ((S.A.erase a).erase c), S.F,
    pairRewriteSumCoefficient S.K a c⟩ rfl rfl (hcard3 _) (s₄.valid hM hα h)
  refine ⟨_, IsRunExpansion.combine s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ fun ψ => ?_⟩
  have hU : a ∈ S.A ∪ S.F := Finset.mem_union_left _ ha
  have hid := chargeFactorProduct_pairBranches_identity (S.A ∪ S.F)
    (isBKTEnsemble_of_pinned h.pinned) S.K ψ a c hU (Finset.mem_union_left _ hc) hne
  simp only at hid
  rw [hid, erase_erase_union haF hcF]
  have e₁ : insert a ((S.A.erase a).erase c ∪ S.F) = S.A.erase c ∪ S.F := by
    rw [← Finset.insert_union, Finset.erase_right_comm,
      Finset.insert_erase (Finset.mem_erase.mpr ⟨hne, ha⟩)]
  have e₂ : insert c ((S.A.erase a).erase c ∪ S.F) = S.A.erase a ∪ S.F := by
    rw [← Finset.insert_union, Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hne, hc⟩)]
  rw [e₁, e₂, ← Finset.insert_union, ← Finset.insert_union]

theorem exists_runExpansion_aux (hM : 1 < M) (hα : 1 ≤ α) :
    ∀ (n k : ℕ) (S : SelConfig L), S.A.card = n → 2 * L - S.j = k → S.Valid M α →
      ∃ B, IsRunExpansion M α S B := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro S hn hk h
  by_cases hA : S.A = ∅
  · refine ⟨[(1, S)], ?_, by simp, fun ψ => ?_⟩
    · intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact ⟨one_pos, hA, Relation.ReflTransGen.refl⟩
    · simp [hA]
  by_cases hpair : ∃ a ∈ S.A, ∃ c ∈ S.A, a ≠ c ∧
      euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * S.scale
  · obtain ⟨a, ha, c, hc, hne, hD⟩ := hpair
    exact runPairStep hM hα h ha hc hne hD fun T _ _ hlt hT =>
      ihn _ (hn ▸ hlt) _ T rfl rfl hT
  · push Not at hpair
    have hfar : ∀ ρ ∈ S.A, ∀ σ ∈ S.A, ρ ≠ σ →
        2 * S.scale < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ) :=
      fun ρ hρ σ hσ hne => hpair ρ hρ σ hσ hne
    obtain ⟨J, hJ⟩ := exists_maximalFreezeSet M α S.A
    have hst := SelStep.freeze (M := M) (α := α) hfar hJ
    have hT := hst.valid hM hα h
    have hU := sdiff_union_union_eq (F := S.F) hJ.1.1
    have hprod : ∀ ψ, chargeFactorProduct (S.A ∪ S.F) S.K ψ =
        chargeFactorProduct ((S.A \ J) ∪ (S.F ∪ J)) S.K ψ := fun ψ => by rw [hU]
    by_cases hJne : J.Nonempty
    · have hlt : (S.A \ J).card < S.A.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hJ.1.1 hJne)
      obtain ⟨B, hB⟩ := ihn _ (hn ▸ hlt) _ _ rfl rfl hT
      exact ⟨B, hB.of_step hst hprod⟩
    · have hJe : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJne
      obtain ⟨ρ, hρ⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      have hσ : ∃ σ ∈ S.A, σ ≠ ρ := by
        by_contra hno
        push Not at hno
        refine hJ.2 ρ (by simpa [hJe] using hρ) ?_
        rw [hJe]
        refine ⟨by simpa using hρ, fun ρ' hρ' σ hσ => ?_, fun x hx y hy hxy => ?_⟩
        · obtain ⟨hσA, hσn⟩ := Finset.mem_sdiff.mp hσ
          exact absurd (hno σ hσA) (by simpa using hσn)
        · simp only [insert_empty_eq, Finset.mem_singleton] at hx hy
          exact absurd (hx.trans hy.symm) hxy
      obtain ⟨σ, hσA, hσρ⟩ := hσ
      have hρne := chargeSupport_nonempty_of_ne_zero ρ
        (h.ne_zero (Finset.mem_union_left _ hρ))
      have hσne := chargeSupport_nonempty_of_ne_zero σ
        (h.ne_zero (Finset.mem_union_left _ hσA))
      obtain ⟨x, hx⟩ := hρne
      obtain ⟨y, hy⟩ := hσne
      have hbox : (2 : ℝ) ^ S.j < 2 * L := by
        have h1 := hfar ρ hρ σ hσA (Ne.symm hσρ)
        have h2 := (setDist_le_siteDist hx hy).trans (euclideanSiteDistance_le x y)
        unfold SelConfig.scale at h1
        linarith
      have hjL : S.j < 2 * L := by
        have h2 : 2 ^ S.j < 2 * L := by exact_mod_cast hbox
        exact (Nat.lt_two_pow_self).trans h2
      have hcard : (S.A \ J).card = n := by rw [hJe, Finset.sdiff_empty]; exact hn
      obtain ⟨B, hB⟩ := ihk (2 * L - (S.j + 1)) (by omega) _ hcard rfl hT
      exact ⟨B, hB.of_step hst hprod⟩

/-- **The run expansion.** Every valid configuration expands, as a finite convex combination
uniformly in `ψ`, into terminal configurations reachable from it. -/
theorem exists_runExpansion (hM : 1 < M) (hα : 1 ≤ α) {S : SelConfig L} (h : S.Valid M α) :
    ∃ B, IsRunExpansion M α S B :=
  exists_runExpansion_aux hM hα _ _ S rfl rfl h

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
