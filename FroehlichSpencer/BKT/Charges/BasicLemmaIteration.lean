/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.BasicLemmaAncestryCertificates
public import FroehlichSpencer.BKT.Charges.CompatibilityParentTransitivity

/-! # Finite termination of the pair rewrite

This module iterates the exact four-branch cosine identity by induction on
the number of factors. It proves a finite convex expansion with terminal
strictly separated ensembles, records that every terminal ensemble is
parented by the original input, and carries a binary merge-history tree for
each terminal factor. The source-graph connectedness and quantitative
coefficient estimates are separate refinements. -/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.BKT

/-- One weighted factorization appearing in a finite Basic Lemma expansion. -/
structure ChargeProductTerm (L : ℕ) where
  ensemble : ChargeEnsemble L
  coefficient : ChargeDensity L → ℝ
  weight : ℝ

/-- The sum of the convex weights in a finite list of factorization terms. -/
def chargeProductTermWeightSum {L : ℕ} (T : List (ChargeProductTerm L)) : ℝ :=
  (T.map ChargeProductTerm.weight).sum

/-- The weighted sum of factorized products represented by a term list. -/
noncomputable def chargeProductTermExpressionSum {L : ℕ}
    (T : List (ChargeProductTerm L)) (ψ : (Fin L × Fin L) → ℝ) : ℝ :=
  (T.map fun t => t.weight * chargeFactorProduct t.ensemble t.coefficient ψ).sum

/-- Scale every branch weight by a fixed nonnegative convex weight. -/
def scaleChargeProductTerms {L : ℕ} (c : ℝ)
    (T : List (ChargeProductTerm L)) : List (ChargeProductTerm L) :=
  T.map fun t => { t with weight := c * t.weight }

/-- A finite convex expansion whose terms are terminal `k`-ensembles. -/
structure IsChargeProductExpansion {L : ℕ} (boundary : SquareBoundary) (k : ℕ)
    (E : ChargeEnsemble L) (K : ChargeDensity L → ℝ)
    (T : List (ChargeProductTerm L)) : Prop where
  nonempty : T ≠ []
  terminal : ∀ t ∈ T, IsChargeScaleEnsemble boundary t.ensemble (.ofNat k)
  positive : ∀ t ∈ T, 0 < t.weight
  normalized : chargeProductTermWeightSum T = 1
  identity : ∀ ψ, chargeFactorProduct E K ψ = chargeProductTermExpressionSum T ψ
  parented : ∀ t ∈ T, IsParentEnsemble E t.ensemble
  coefficientLineage : ∀ t ∈ T,
    ∃ family : CertifiedChargeHistoryFamily boundary k E t.ensemble,
      ∀ ρ (hρ : ρ ∈ t.ensemble),
        t.coefficient ρ = (family.history ρ hρ).history.lineageValue K

theorem IsChargeProductExpansion.ancestry {L : ℕ} {boundary : SquareBoundary}
    {k : ℕ} {E : ChargeEnsemble L} {K : ChargeDensity L → ℝ}
    {T : List (ChargeProductTerm L)} (hT : IsChargeProductExpansion boundary k E K T)
    (t : ChargeProductTerm L) (ht : t ∈ T) :
    Nonempty (CertifiedChargeHistoryFamily boundary k E t.ensemble) := by
  obtain ⟨family, _⟩ := hT.coefficientLineage t ht
  exact ⟨family⟩

private noncomputable def pairBranchHistoryFamily {L : ℕ}
    (boundary : SquareBoundary) (k : ℕ) (E R : ChargeEnsemble L)
    (hR : R ⊆ E) (ρ σ selected : ChargeDensity L)
    (cert : CertifiedChargeMergeHistory boundary k E selected)
    (hpair : cert.history.allLeaves = {ρ, σ})
    (hRnot : ∀ a ∈ R, a ≠ ρ ∧ a ≠ σ) :
    CertifiedChargeHistoryFamily boundary k E (insert selected R) := by
  classical
  let chooseHistory : ∀ a, a ∈ insert selected R →
      CertifiedChargeMergeHistory boundary k E a := fun a ha => by
    by_cases hselected : a = selected
    · subst a
      exact cert
    · have hrest : a ∈ R := (Finset.mem_insert.mp ha).resolve_left hselected
      exact ⟨.leaf a (hR hrest), .leaf a (hR hrest)⟩
  refine { history := chooseHistory, disjoint := ?_ }
  intro a ha b hb hab
  have hresA : (chooseHistory a ha).history.allLeaves =
      if a = selected then {ρ, σ} else {a} := by
    by_cases hselected : a = selected
    · subst a
      simp [chooseHistory, hpair]
    · have hrest : a ∈ R := (Finset.mem_insert.mp ha).resolve_left hselected
      simp [chooseHistory, hselected, ChargeMergeHistory.allLeaves]
  have hresB : (chooseHistory b hb).history.allLeaves =
      if b = selected then {ρ, σ} else {b} := by
    by_cases hselected : b = selected
    · subst b
      simp [chooseHistory, hpair]
    · have hrest : b ∈ R := (Finset.mem_insert.mp hb).resolve_left hselected
      simp [chooseHistory, hselected, ChargeMergeHistory.allLeaves]
  by_cases hselectedA : a = selected
  · by_cases hselectedB : b = selected
    · exact (hab (hselectedA.trans hselectedB.symm)).elim
    · have hbR : b ∈ R := (Finset.mem_insert.mp hb).resolve_left hselectedB
      rw [hresA, hresB]
      simp [hselectedA, hselectedB]
      exact hRnot b hbR
  · have haR : a ∈ R := (Finset.mem_insert.mp ha).resolve_left hselectedA
    by_cases hselectedB : b = selected
    · rw [hresA, hresB]
      simp [hselectedA, hselectedB]
      exact hRnot a haR
    · have hbR : b ∈ R := (Finset.mem_insert.mp hb).resolve_left hselectedB
      rw [hresA, hresB]
      simp [hselectedA, hselectedB]
      exact hab

private theorem pairBranchHistoryFamily_lineageValue {L : ℕ}
    (boundary : SquareBoundary) (k : ℕ) (E R : ChargeEnsemble L)
    (hR : R ⊆ E) (ρ σ selected : ChargeDensity L)
    (cert : CertifiedChargeMergeHistory boundary k E selected)
    (hpair : cert.history.allLeaves = {ρ, σ})
    (hRnot : ∀ a ∈ R, a ≠ ρ ∧ a ≠ σ)
    (K Kbranch : ChargeDensity L → ℝ)
    (hselected : Kbranch selected = cert.history.lineageValue K)
    (hrest : ∀ a ∈ R, Kbranch a = K a) :
    ∀ a (ha : a ∈ insert selected R),
      Kbranch a =
        (pairBranchHistoryFamily boundary k E R hR ρ σ selected cert hpair hRnot
          |>.history a ha).history.lineageValue K := by
  intro a ha
  by_cases hsel : a = selected
  · subst a
    simpa [pairBranchHistoryFamily] using hselected
  · have haR : a ∈ R := (Finset.mem_insert.mp ha).resolve_left hsel
    simpa [pairBranchHistoryFamily, hsel, ChargeMergeHistory.lineageValue] using
      hrest a haR

private theorem composeChargeCoefficientLineage {L : ℕ}
    {boundary : SquareBoundary} {k : ℕ} {E F G : ChargeEnsemble L}
    (source : CertifiedChargeHistoryFamily boundary k F G)
    (replace : CertifiedChargeHistoryFamily boundary k E F)
    (K Kbranch Kout : ChargeDensity L → ℝ)
    (ρ : ChargeDensity L) (hρ : ρ ∈ G)
    (hcoef : Kout ρ = (source.history ρ hρ).history.lineageValue Kbranch)
    (hbranch : ∀ a (ha : a ∈ (source.history ρ hρ).history.leaves),
      Kbranch a = (replace.history a
        ((source.history ρ hρ).history.allLeaves_subset
          ((source.history ρ hρ).history.leaves_subset_allLeaves ha))).history.lineageValue K) :
    Kout ρ =
      ((CertifiedChargeHistoryFamily.compose source replace).history ρ hρ).history.lineageValue K := by
  have hsub := (source.history ρ hρ).history.lineageValue_substitute_eq
    (fun a ha => replace.history a ha) K Kbranch hbranch
  exact hcoef.trans hsub.symm
/-- View the `i`th branch of a list as an element of the finite type whose
cardinality is the list length. -/
def chargeProductTermAt {L : ℕ} (T : List (ChargeProductTerm L))
    (i : Fin T.length) : ChargeProductTerm L := T.get i

/-- The list weight sum is the corresponding sum over `Fin T.length`. -/
theorem chargeProductTermWeightSum_eq_fin {L : ℕ}
    (T : List (ChargeProductTerm L)) :
    chargeProductTermWeightSum T =
      ∑ i : Fin T.length, (chargeProductTermAt T i).weight := by
  unfold chargeProductTermWeightSum chargeProductTermAt
  rw [← List.ofFn_getElem_eq_map T ChargeProductTerm.weight]
  rw [List.sum_ofFn]
  simp only [List.get_eq_getElem]

/-- The list expression sum is the corresponding sum over `Fin T.length`. -/
theorem chargeProductTermExpressionSum_eq_fin {L : ℕ}
    (T : List (ChargeProductTerm L)) (ψ : (Fin L × Fin L) → ℝ) :
    chargeProductTermExpressionSum T ψ =
      ∑ i : Fin T.length,
        (chargeProductTermAt T i).weight *
          chargeFactorProduct (chargeProductTermAt T i).ensemble
            (chargeProductTermAt T i).coefficient ψ := by
  unfold chargeProductTermExpressionSum chargeProductTermAt
  let f : ChargeProductTerm L → ℝ := fun t =>
    t.weight * chargeFactorProduct t.ensemble t.coefficient ψ
  change (T.map f).sum = ∑ i : Fin T.length, f (T.get i)
  rw [← List.ofFn_getElem_eq_map T f]
  rw [List.sum_ofFn]
  simp only [List.get_eq_getElem]

private theorem chargeProductTermWeightSum_append {L : ℕ}
    (T U : List (ChargeProductTerm L)) :
    chargeProductTermWeightSum (T ++ U) =
      chargeProductTermWeightSum T + chargeProductTermWeightSum U := by
  simp [chargeProductTermWeightSum, List.map_append]

private theorem chargeProductTermExpressionSum_append {L : ℕ}
    (T U : List (ChargeProductTerm L)) (ψ : (Fin L × Fin L) → ℝ) :
    chargeProductTermExpressionSum (T ++ U) ψ =
      chargeProductTermExpressionSum T ψ + chargeProductTermExpressionSum U ψ := by
  simp [chargeProductTermExpressionSum, List.map_append]

private theorem chargeProductTermWeightSum_scale {L : ℕ} (c : ℝ)
    (T : List (ChargeProductTerm L)) :
    chargeProductTermWeightSum (scaleChargeProductTerms c T) =
      c * chargeProductTermWeightSum T := by
  induction T with
  | nil => simp [chargeProductTermWeightSum, scaleChargeProductTerms]
  | cons t T ih =>
      change c * t.weight + chargeProductTermWeightSum
          (scaleChargeProductTerms c T) =
        c * (t.weight + chargeProductTermWeightSum T)
      rw [ih]
      ring

private theorem chargeProductTermExpressionSum_scale {L : ℕ} (c : ℝ)
    (T : List (ChargeProductTerm L)) (ψ : (Fin L × Fin L) → ℝ) :
    chargeProductTermExpressionSum (scaleChargeProductTerms c T) ψ =
      c * chargeProductTermExpressionSum T ψ := by
  induction T with
  | nil => simp [chargeProductTermExpressionSum, scaleChargeProductTerms]
  | cons t T ih =>
      change c * t.weight * chargeFactorProduct t.ensemble t.coefficient ψ +
          chargeProductTermExpressionSum (scaleChargeProductTerms c T) ψ =
        c * (t.weight * chargeFactorProduct t.ensemble t.coefficient ψ +
          chargeProductTermExpressionSum T ψ)
      rw [ih]
      ring

private theorem terminal_of_mem_scaled {L : ℕ} (boundary : SquareBoundary) (k : ℕ)
    (T : List (ChargeProductTerm L)) (c : ℝ)
    (hT : ∀ t ∈ T, IsChargeScaleEnsemble boundary t.ensemble (.ofNat k)) :
    ∀ t ∈ scaleChargeProductTerms c T,
      IsChargeScaleEnsemble boundary t.ensemble (.ofNat k) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  simpa [scaleChargeProductTerms] using hT u hu

private theorem positive_of_mem_scaled {L : ℕ} (T : List (ChargeProductTerm L))
    (c : ℝ) (hc : 0 < c)
    (hT : ∀ t ∈ T, 0 < t.weight) :
    ∀ t ∈ scaleChargeProductTerms c T, 0 < t.weight := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  simpa [scaleChargeProductTerms] using mul_pos hc (hT u hu)

/-- Every valid ensemble has a finite exact convex expansion into strict
`k`-ensembles. At each induction step one conflicting pair is replaced by the
four branches of (4.12); each branch has one fewer factor. -/
theorem exists_chargeProductExpansion {L : ℕ} (boundary : SquareBoundary)
    (k : ℕ) (E : ChargeEnsemble L) (hE : IsBKTEnsemble E)
    (K : ChargeDensity L → ℝ) :
    ∃ T : List (ChargeProductTerm L), IsChargeProductExpansion boundary k E K T := by
  classical
  let P : ℕ → Prop := fun n => ∀ E : ChargeEnsemble L,
    ∀ hE : IsBKTEnsemble E, ∀ K : ChargeDensity L → ℝ, E.card = n →
      ∃ T : List (ChargeProductTerm L), IsChargeProductExpansion boundary k E K T
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro E hE K hcard
        rcases chargeEnsemble_conflict_or_kSeparated boundary k E hE with hterm | hconf
        · refine ⟨[{ ensemble := E, coefficient := K, weight := 1 }], ?_⟩
          refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro t ht
            simp only [List.mem_singleton] at ht
            subst t
            exact hterm
          · intro t ht
            simp only [List.mem_singleton] at ht
            subst t
            norm_num
          · simp [chargeProductTermWeightSum]
          · intro ψ
            simp [chargeProductTermExpressionSum, chargeFactorProduct]
          · intro t ht
            simp only [List.mem_singleton] at ht
            subst t
            exact IsParentEnsemble_refl E hE
          · intro t ht
            simp only [List.mem_singleton] at ht
            subst t
            refine ⟨?_, ?_⟩
            · refine { history := ?_, disjoint := ?_ }
              · intro ρ hρ
                exact ⟨.leaf ρ hρ, .leaf ρ hρ⟩
              · intro ρ hρ σ hσ hne
                apply Finset.disjoint_left.mpr
                intro τ hτρ hτσ
                simp only [ChargeMergeHistory.allLeaves,
                  Finset.mem_singleton] at hτρ hτσ
                exact hne (hτρ.symm.trans hτσ)
            · intro ρ hρ
              rfl
        · obtain ⟨ρ, hρ, σ, hσ, hne, hdist⟩ := hconf
          let R : ChargeEnsemble L := E.erase ρ |>.erase σ
          have hσerase : σ ∈ E.erase ρ := Finset.mem_erase.mpr ⟨hne.symm, hσ⟩
          have hEcard2 : 2 ≤ E.card := by
            have hpos : 0 < (E.erase ρ).card :=
              Finset.card_pos.mpr ⟨σ, hσerase⟩
            rw [Finset.card_erase_of_mem hρ] at hpos
            omega
          obtain ⟨hEρ, hEσ, hEminus, hEplus⟩ :=
            pairRewriteBranches_are_parentedEnsembles E hE ρ σ hρ hσ hne
          have hcards := pairRewriteBranches_card E hE ρ σ hρ hσ hne
          dsimp [R] at hcards
          have hRsubset : R ⊆ E := by
            intro a ha
            dsimp [R] at ha
            exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)
          have hRnot : ∀ a ∈ R, a ≠ ρ ∧ a ≠ σ := by
            intro a ha
            dsimp [R] at ha
            rcases Finset.mem_erase.mp ha with ⟨haσ, ha⟩
            rcases Finset.mem_erase.mp ha with ⟨haρ, haE⟩
            exact ⟨haρ, haσ⟩
          have hρσdisj : Disjoint ({ρ} : Finset (ChargeDensity L)) {σ} := by
            apply Finset.disjoint_left.mpr
            intro a ha hb
            simp only [Finset.mem_singleton] at ha hb
            subst a
            subst σ
            exact hne rfl
          let firstPair : CertifiedChargeMergeHistory boundary k E ρ :=
            ⟨.keepLeft (.leaf ρ hρ) (.leaf σ hσ) hdist,
              .keepLeft hdist (.leaf ρ hρ) (.leaf σ hσ) hρσdisj⟩
          let secondPair : CertifiedChargeMergeHistory boundary k E σ :=
            ⟨.keepRight (.leaf ρ hρ) (.leaf σ hσ) hdist,
              .keepRight hdist (.leaf ρ hρ) (.leaf σ hσ) hρσdisj⟩
          let minusPair : CertifiedChargeMergeHistory boundary k E (ρ - σ) :=
            ⟨.sub (.leaf ρ hρ) (.leaf σ hσ) hdist,
              .sub hdist (.leaf ρ hρ) (.leaf σ hσ) hρσdisj⟩
          let plusPair : CertifiedChargeMergeHistory boundary k E (ρ + σ) :=
            ⟨.add (.leaf ρ hρ) (.leaf σ hσ) hdist,
              .add hdist (.leaf ρ hρ) (.leaf σ hσ) hρσdisj⟩
          have hfirstPair : firstPair.history.allLeaves = {ρ, σ} := by
            change ({ρ} : Finset (ChargeDensity L)) ∪ {σ} = {ρ, σ}
            simp
          have hsecondPair : secondPair.history.allLeaves = {ρ, σ} := by
            change ({ρ} : Finset (ChargeDensity L)) ∪ {σ} = {ρ, σ}
            simp
          have hminusPair : minusPair.history.allLeaves = {ρ, σ} := by
            change ({ρ} : Finset (ChargeDensity L)) ∪ {σ} = {ρ, σ}
            simp
          have hplusPair : plusPair.history.allLeaves = {ρ, σ} := by
            change ({ρ} : Finset (ChargeDensity L)) ∪ {σ} = {ρ, σ}
            simp
          have hminusNot : ρ - σ ∉ R := by
            exact mergedCharge_not_mem_pairRest E ρ σ (ρ - σ) hE hρ
              (functionSupport_sub_of_disjoint ρ σ (hE.2 ρ hρ σ hσ hne))
          have hplusNot : ρ + σ ∉ R := by
            exact mergedCharge_not_mem_pairRest E ρ σ (ρ + σ) hE hρ
              (functionSupport_add_of_disjoint ρ σ (hE.2 ρ hρ σ hσ hne))
          let familyFirst := pairBranchHistoryFamily boundary k E R hRsubset
            ρ σ ρ firstPair hfirstPair hRnot
          let familySecond := pairBranchHistoryFamily boundary k E R hRsubset
            ρ σ σ secondPair hsecondPair hRnot
          let familyDifference := pairBranchHistoryFamily boundary k E R hRsubset
            ρ σ (ρ - σ) minusPair hminusPair hRnot
          let familySum := pairBranchHistoryFamily boundary k E R hRsubset
            ρ σ (ρ + σ) plusPair hplusPair hRnot
          have hlt : E.card - 1 < n := by rw [hcard]; omega
          obtain ⟨Tρ, hTρ⟩ := ih (E.card - 1) hlt
            (insert ρ R) hEρ.1 (pairRewriteFirstCoefficient K ρ) hcards.1
          obtain ⟨Tσ, hTσ⟩ := ih (E.card - 1) hlt
            (insert σ R) hEσ.1 (pairRewriteSecondCoefficient K σ) hcards.2.1
          obtain ⟨Tminus, hTminus⟩ := ih (E.card - 1) hlt
            (insert (ρ - σ) R) hEminus.1
            (pairRewriteDifferenceCoefficient K ρ σ) hcards.2.2.1
          obtain ⟨Tplus, hTplus⟩ := ih (E.card - 1) hlt
            (insert (ρ + σ) R) hEplus.1
            (pairRewriteSumCoefficient K ρ σ) hcards.2.2.2
          let Tρ' := scaleChargeProductTerms (1 / 3 : ℝ) Tρ
          let Tσ' := scaleChargeProductTerms (1 / 3 : ℝ) Tσ
          let Tminus' := scaleChargeProductTerms (1 / 6 : ℝ) Tminus
          let Tplus' := scaleChargeProductTerms (1 / 6 : ℝ) Tplus
          let T := Tρ' ++ (Tσ' ++ (Tminus' ++ Tplus'))
          have hnonemptyρ : Tρ' ≠ [] := by
            change List.map
              (fun t => { t with weight := (1 / 3 : ℝ) * t.weight }) Tρ ≠ []
            intro hnil
            exact hTρ.nonempty (List.map_eq_nil_iff.mp hnil)
          have hnonemptyT : T ≠ [] := by
            simp [T, hnonemptyρ]
          have hterminalT : ∀ t ∈ T,
              IsChargeScaleEnsemble boundary t.ensemble (.ofNat k) := by
            intro t ht
            change t ∈ Tρ' ++ (Tσ' ++ (Tminus' ++ Tplus')) at ht
            rw [List.mem_append] at ht
            rcases ht with hρ' | hrest
            · exact terminal_of_mem_scaled boundary k Tρ (1 / 3 : ℝ)
                hTρ.terminal t hρ'
            · rw [List.mem_append] at hrest
              rcases hrest with hσ' | hrest
              · exact terminal_of_mem_scaled boundary k Tσ (1 / 3 : ℝ)
                  hTσ.terminal t hσ'
              · rw [List.mem_append] at hrest
                rcases hrest with hminus' | hplus'
                · exact terminal_of_mem_scaled boundary k Tminus (1 / 6 : ℝ)
                    hTminus.terminal t hminus'
                · exact terminal_of_mem_scaled boundary k Tplus (1 / 6 : ℝ)
                    hTplus.terminal t hplus'
          have hpositiveT : ∀ t ∈ T, 0 < t.weight := by
            intro t ht
            change t ∈ Tρ' ++ (Tσ' ++ (Tminus' ++ Tplus')) at ht
            rw [List.mem_append] at ht
            rcases ht with hρ' | hrest
            · exact positive_of_mem_scaled Tρ (1 / 3 : ℝ) (by norm_num)
                hTρ.positive t hρ'
            · rw [List.mem_append] at hrest
              rcases hrest with hσ' | hrest
              · exact positive_of_mem_scaled Tσ (1 / 3 : ℝ) (by norm_num)
                  hTσ.positive t hσ'
              · rw [List.mem_append] at hrest
                rcases hrest with hminus' | hplus'
                · exact positive_of_mem_scaled Tminus (1 / 6 : ℝ) (by norm_num)
                    hTminus.positive t hminus'
                · exact positive_of_mem_scaled Tplus (1 / 6 : ℝ) (by norm_num)
                    hTplus.positive t hplus'
          have hparentedT : ∀ t ∈ T, IsParentEnsemble E t.ensemble := by
            intro t ht
            change t ∈ Tρ' ++ (Tσ' ++ (Tminus' ++ Tplus')) at ht
            rw [List.mem_append] at ht
            rcases ht with hρ' | hrest
            · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hρ'
              exact IsParentEnsemble_trans hE hEρ.1 hEρ.2
                (hTρ.parented u hu)
            · rw [List.mem_append] at hrest
              rcases hrest with hσ' | hrest
              · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hσ'
                exact IsParentEnsemble_trans hE hEσ.1 hEσ.2
                  (hTσ.parented u hu)
              · rw [List.mem_append] at hrest
                rcases hrest with hminus' | hplus'
                · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hminus'
                  exact IsParentEnsemble_trans hE hEminus.1 hEminus.2
                    (hTminus.parented u hu)
                · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hplus'
                  exact IsParentEnsemble_trans hE hEplus.1 hEplus.2
                    (hTplus.parented u hu)
          have hfirstBranchValue : ∀ a (ha : a ∈ insert ρ R),
              pairRewriteFirstCoefficient K ρ a =
                (familyFirst.history a ha).history.lineageValue K := by
            have hselected : pairRewriteFirstCoefficient K ρ ρ =
                firstPair.history.lineageValue K := by
              simp [pairRewriteFirstCoefficient, firstPair,
                ChargeMergeHistory.lineageValue]
            have hrest : ∀ a ∈ R, pairRewriteFirstCoefficient K ρ a = K a := by
              intro a ha
              simp [pairRewriteFirstCoefficient, (hRnot a ha).1]
            simpa [familyFirst] using pairBranchHistoryFamily_lineageValue
              boundary k E R hRsubset ρ σ ρ firstPair hfirstPair hRnot K
              (pairRewriteFirstCoefficient K ρ) hselected hrest
          have hsecondBranchValue : ∀ a (ha : a ∈ insert σ R),
              pairRewriteSecondCoefficient K σ a =
                (familySecond.history a ha).history.lineageValue K := by
            have hselected : pairRewriteSecondCoefficient K σ σ =
                secondPair.history.lineageValue K := by
              simp [pairRewriteSecondCoefficient, secondPair,
                ChargeMergeHistory.lineageValue]
            have hrest : ∀ a ∈ R, pairRewriteSecondCoefficient K σ a = K a := by
              intro a ha
              simp [pairRewriteSecondCoefficient, (hRnot a ha).2]
            simpa [familySecond] using pairBranchHistoryFamily_lineageValue
              boundary k E R hRsubset ρ σ σ secondPair hsecondPair hRnot K
              (pairRewriteSecondCoefficient K σ) hselected hrest
          have hdifferenceBranchValue : ∀ a (ha : a ∈ insert (ρ - σ) R),
              pairRewriteDifferenceCoefficient K ρ σ a =
                (familyDifference.history a ha).history.lineageValue K := by
            have hselected : pairRewriteDifferenceCoefficient K ρ σ (ρ - σ) =
                minusPair.history.lineageValue K := by
              simp [pairRewriteDifferenceCoefficient, minusPair,
                ChargeMergeHistory.lineageValue]
            have hrest : ∀ a ∈ R,
                pairRewriteDifferenceCoefficient K ρ σ a = K a := by
              intro a ha
              have hne' : a ≠ ρ - σ := by
                intro heq
                exact hminusNot (heq ▸ ha)
              simp [pairRewriteDifferenceCoefficient, hne']
            simpa [familyDifference] using pairBranchHistoryFamily_lineageValue
              boundary k E R hRsubset ρ σ (ρ - σ) minusPair hminusPair hRnot K
              (pairRewriteDifferenceCoefficient K ρ σ) hselected hrest
          have hsumBranchValue : ∀ a (ha : a ∈ insert (ρ + σ) R),
              pairRewriteSumCoefficient K ρ σ a =
                (familySum.history a ha).history.lineageValue K := by
            have hselected : pairRewriteSumCoefficient K ρ σ (ρ + σ) =
                plusPair.history.lineageValue K := by
              simp [pairRewriteSumCoefficient, plusPair,
                ChargeMergeHistory.lineageValue]
            have hrest : ∀ a ∈ R,
                pairRewriteSumCoefficient K ρ σ a = K a := by
              intro a ha
              have hne' : a ≠ ρ + σ := by
                intro heq
                exact hplusNot (heq ▸ ha)
              simp [pairRewriteSumCoefficient, hne']
            simpa [familySum] using pairBranchHistoryFamily_lineageValue
              boundary k E R hRsubset ρ σ (ρ + σ) plusPair hplusPair hRnot K
              (pairRewriteSumCoefficient K ρ σ) hselected hrest
          have hcoefficientLineageT : ∀ t ∈ T,
              ∃ family : CertifiedChargeHistoryFamily boundary k E t.ensemble,
                ∀ q (hq : q ∈ t.ensemble),
                  t.coefficient q = (family.history q hq).history.lineageValue K := by
            intro t ht
            change t ∈ Tρ' ++ (Tσ' ++ (Tminus' ++ Tplus')) at ht
            rw [List.mem_append] at ht
            rcases ht with hρ' | hrest
            · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hρ'
              obtain ⟨source, hsourceCoeff⟩ := hTρ.coefficientLineage u hu
              refine ⟨CertifiedChargeHistoryFamily.compose source familyFirst, ?_⟩
              intro q hq
              have hbranch : ∀ a (ha : a ∈ (source.history q hq).history.leaves),
                  pairRewriteFirstCoefficient K ρ a =
                    (familyFirst.history a
                      ((source.history q hq).history.allLeaves_subset
                        ((source.history q hq).history.leaves_subset_allLeaves ha))).history.lineageValue K := by
                intro a ha
                have haF : a ∈ insert ρ R :=
                  (source.history q hq).history.allLeaves_subset
                    ((source.history q hq).history.leaves_subset_allLeaves ha)
                exact hfirstBranchValue a haF
              exact composeChargeCoefficientLineage source familyFirst K
                (pairRewriteFirstCoefficient K ρ) u.coefficient q hq
                (hsourceCoeff q hq) hbranch
            · rw [List.mem_append] at hrest
              rcases hrest with hσ' | hrest
              · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hσ'
                obtain ⟨source, hsourceCoeff⟩ := hTσ.coefficientLineage u hu
                refine ⟨CertifiedChargeHistoryFamily.compose source familySecond, ?_⟩
                intro q hq
                have hbranch : ∀ a (ha : a ∈ (source.history q hq).history.leaves),
                    pairRewriteSecondCoefficient K σ a =
                      (familySecond.history a
                        ((source.history q hq).history.allLeaves_subset
                          ((source.history q hq).history.leaves_subset_allLeaves ha))).history.lineageValue K := by
                  intro a ha
                  have haF : a ∈ insert σ R :=
                    (source.history q hq).history.allLeaves_subset
                      ((source.history q hq).history.leaves_subset_allLeaves ha)
                  exact hsecondBranchValue a haF
                exact composeChargeCoefficientLineage source familySecond K
                  (pairRewriteSecondCoefficient K σ) u.coefficient q hq
                  (hsourceCoeff q hq) hbranch
              · rw [List.mem_append] at hrest
                rcases hrest with hminus' | hplus'
                · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hminus'
                  obtain ⟨source, hsourceCoeff⟩ := hTminus.coefficientLineage u hu
                  refine ⟨CertifiedChargeHistoryFamily.compose source familyDifference, ?_⟩
                  intro q hq
                  have hbranch : ∀ a (ha : a ∈ (source.history q hq).history.leaves),
                      pairRewriteDifferenceCoefficient K ρ σ a =
                        (familyDifference.history a
                          ((source.history q hq).history.allLeaves_subset
                            ((source.history q hq).history.leaves_subset_allLeaves ha))).history.lineageValue K := by
                    intro a ha
                    have haF : a ∈ insert (ρ - σ) R :=
                      (source.history q hq).history.allLeaves_subset
                        ((source.history q hq).history.leaves_subset_allLeaves ha)
                    exact hdifferenceBranchValue a haF
                  exact composeChargeCoefficientLineage source familyDifference K
                    (pairRewriteDifferenceCoefficient K ρ σ) u.coefficient q hq
                    (hsourceCoeff q hq) hbranch
                · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hplus'
                  obtain ⟨source, hsourceCoeff⟩ := hTplus.coefficientLineage u hu
                  refine ⟨CertifiedChargeHistoryFamily.compose source familySum, ?_⟩
                  intro q hq
                  have hbranch : ∀ a (ha : a ∈ (source.history q hq).history.leaves),
                      pairRewriteSumCoefficient K ρ σ a =
                        (familySum.history a
                          ((source.history q hq).history.allLeaves_subset
                            ((source.history q hq).history.leaves_subset_allLeaves ha))).history.lineageValue K := by
                    intro a ha
                    have haF : a ∈ insert (ρ + σ) R :=
                      (source.history q hq).history.allLeaves_subset
                        ((source.history q hq).history.leaves_subset_allLeaves ha)
                    exact hsumBranchValue a haF
                  exact composeChargeCoefficientLineage source familySum K
                    (pairRewriteSumCoefficient K ρ σ) u.coefficient q hq
                    (hsourceCoeff q hq) hbranch
          have hnormalizedT : chargeProductTermWeightSum T = 1 := by
            simp only [T, Tρ', Tσ', Tminus', Tplus',
              chargeProductTermWeightSum_append]
            rw [chargeProductTermWeightSum_scale, chargeProductTermWeightSum_scale,
              chargeProductTermWeightSum_scale, chargeProductTermWeightSum_scale]
            rw [hTρ.normalized, hTσ.normalized, hTminus.normalized, hTplus.normalized]
            norm_num
          have hidentityT : ∀ ψ,
              chargeFactorProduct E K ψ = chargeProductTermExpressionSum T ψ := by
            intro ψ
            have hstep := chargeFactorProduct_pairBranches_identity E hE K ψ
              ρ σ hρ hσ hne
            calc
              chargeFactorProduct E K ψ =
                  (1 / 3 : ℝ) * chargeFactorProduct (insert ρ R)
                    (pairRewriteFirstCoefficient K ρ) ψ +
                  (1 / 3 : ℝ) * chargeFactorProduct (insert σ R)
                    (pairRewriteSecondCoefficient K σ) ψ +
                  (1 / 6 : ℝ) * chargeFactorProduct (insert (ρ - σ) R)
                    (pairRewriteDifferenceCoefficient K ρ σ) ψ +
                  (1 / 6 : ℝ) * chargeFactorProduct (insert (ρ + σ) R)
                    (pairRewriteSumCoefficient K ρ σ) ψ := by
                      simpa [R] using hstep
              _ = (1 / 3 : ℝ) * chargeProductTermExpressionSum Tρ ψ +
                    (1 / 3 : ℝ) * chargeProductTermExpressionSum Tσ ψ +
                    (1 / 6 : ℝ) * chargeProductTermExpressionSum Tminus ψ +
                    (1 / 6 : ℝ) * chargeProductTermExpressionSum Tplus ψ := by
                  rw [hTρ.identity ψ, hTσ.identity ψ,
                    hTminus.identity ψ, hTplus.identity ψ]
              _ = chargeProductTermExpressionSum T ψ := by
                  simp [T, Tρ', Tσ', Tminus', Tplus',
                    chargeProductTermExpressionSum_append,
                    chargeProductTermExpressionSum_scale]
                  ring
          exact ⟨T, ⟨hnonemptyT, hterminalT, hpositiveT,
            hnormalizedT, hidentityT, hparentedT,
            hcoefficientLineageT⟩⟩
  exact hP E.card E hE K rfl

/-- The recursive list expansion is also an explicitly indexed finite family
over `Fin n`, matching the finite-family interface of KP's statement. -/
theorem exists_chargeProductExpansion_fin {L : ℕ} (boundary : SquareBoundary)
    (k : ℕ) (E : ChargeEnsemble L) (hE : IsBKTEnsemble E)
    (K : ChargeDensity L → ℝ) :
    ∃ n : ℕ, ∃ F : Fin n → ChargeEnsemble L,
      ∃ K' : Fin n → ChargeDensity L → ℝ, ∃ c : Fin n → ℝ,
        (0 < n) ∧
        (∀ i, IsChargeScaleEnsemble boundary (F i) (.ofNat k)) ∧
        (∀ i, 0 < c i) ∧
        (∑ i, c i) = 1 ∧
        (∀ i, IsParentEnsemble E (F i)) ∧
        (∀ i ρ, ρ ∈ F i →
          Nonempty (ChargeMergeHistory boundary k E ρ)) ∧
        (∀ ψ, chargeFactorProduct E K ψ =
          ∑ i, c i * chargeFactorProduct (F i) (K' i) ψ) := by
  classical
  obtain ⟨T, hT⟩ := exists_chargeProductExpansion boundary k E hE K
  refine ⟨T.length, (fun i => (chargeProductTermAt T i).ensemble),
    (fun i => (chargeProductTermAt T i).coefficient),
    (fun i => (chargeProductTermAt T i).weight),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.length_pos_of_ne_nil hT.nonempty
  · intro i
    exact hT.terminal (chargeProductTermAt T i) (List.get_mem T i)
  · intro i
    exact hT.positive (chargeProductTermAt T i) (List.get_mem T i)
  · rw [← chargeProductTermWeightSum_eq_fin]
    exact hT.normalized
  · intro i
    exact hT.parented (chargeProductTermAt T i) (List.get_mem T i)
  · intro i ρ hρ
    obtain ⟨histories⟩ := hT.ancestry
      (chargeProductTermAt T i) (List.get_mem T i)
    exact ⟨(histories.history ρ hρ).history⟩
  · intro ψ
    calc
      chargeFactorProduct E K ψ = chargeProductTermExpressionSum T ψ := hT.identity ψ
      _ = ∑ i : Fin T.length,
            (chargeProductTermAt T i).weight *
              chargeFactorProduct (chargeProductTermAt T i).ensemble
                (chargeProductTermAt T i).coefficient ψ :=
          chargeProductTermExpressionSum_eq_fin T ψ

/-- Every terminal factor's original-source leaves form a connected set in the
input conflict graph. -/
theorem IsChargeProductExpansion.factor_sourceConflictConnected {L : ℕ}
    {boundary : SquareBoundary} {k : ℕ} {E : ChargeEnsemble L}
    {K : ChargeDensity L → ℝ} {T : List (ChargeProductTerm L)}
    (hT : IsChargeProductExpansion boundary k E K T)
    (hE : IsBKTEnsemble E) (t : ChargeProductTerm L) (ht : t ∈ T)
    (ρ : ChargeDensity L) (hρ : ρ ∈ t.ensemble) :
    ∃ c : CertifiedChargeMergeHistory boundary k E ρ,
      ∀ a ∈ c.history.allLeaves, ∀ b ∈ c.history.allLeaves,
        SourceConflictPath boundary L k a b := by
  obtain ⟨family⟩ := hT.ancestry t ht
  let c := family.history ρ hρ
  exact ⟨c, c.history.good_sourceConnected c.good hE⟩

end FroehlichSpencer.BKT

end
