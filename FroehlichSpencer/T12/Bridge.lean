/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.InductionDefs
public import FroehlichSpencer.T12.Base

/-!
# Domain bridge, base pair and mass bookkeeping
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

/-- induced-graph vertex boundary of `B` in `Λ`: points of `B` with a nearest neighbour in
`Λ ∖ B`. -/
def relVertexBoundary {ν : ℕ} (Λ B : Set (Site ν)) : Set (Site ν) :=
  {b | b ∈ B ∧ ∃ c, siteDist ν b c = 1 ∧ c ∈ Λ ∧ c ∉ B}

/-- admissibility relative to the induced graph on `Λ` (levels `j < n`). -/
def RelAdmissible {ν : ℕ} (K₀ : ℝ) (G : ℕ → Set (Set (Site ν))) (n : ℕ) (Λ B : Set (Site ν)) :
    Prop :=
  ∀ j < n, ∀ C ∈ G j, Disjoint (relVertexBoundary Λ B) (nbhd C (4 * scaleD K₀ j))

/-- requested finite-volume T2.1 at level `k` (rate `M`) on a class `𝒟` of induced domains
`B ⊆ Λ`. -/
def ProbT21On {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ) (M : ℝ)
    (𝒟 : Set (Finset (Site ν))) : Prop :=
  ∀ B ∈ 𝒟, B ⊆ Λ → RelAdmissible P.K₀ (restrictedClasses P Λ v) (k + 1) (Λ : Set (Site ν)) B →
    (∀ x ∈ B, x ∉ singularSetsIn P Λ v (k + 1)) →
    ∀ (ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ B}), scaleD P.K₀ (k + 1) / 5 ≤ siteDist ν x y →
      ‖finiteGreen ν B v P.E ε hε x y‖ ≤ Real.exp (-M * siteDist ν x y)


theorem relVertexBoundary_inter_subset {ν : ℕ} (Λ A : Set (Site ν)) :
    relVertexBoundary Λ (A ∩ Λ) ⊆ vertexBoundary A := by
  rintro b ⟨hb, c, hc, hcΛ, hcB⟩
  exact ⟨hb.1, c, hc, fun hcA => hcB ⟨hcA, hcΛ⟩⟩


theorem relAdmissible_inter {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n : ℕ}
    {Λ A : Set (Site ν)} (h : Admissible K₀ G n A) : RelAdmissible K₀ G n Λ (A ∩ Λ) :=
  fun j hj C hC => (h j hj C hC).mono_left (relVertexBoundary_inter_subset Λ A)

/--
The converse fails: a relatively admissible `B ⊆ Λ` need not be such a trace (e.g.
-/
theorem probT21On_traces_of_jPred {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ)
    (k : ℕ) (M : ℝ) (h : JPred P Λ v (k + 1) M) :
    ProbT21On P Λ v k M {B | ∃ A : Finset (Site ν),
      Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) (A : Set (Site ν)) ∧ B = A ∩ Λ} := by
  rintro B ⟨A, hA, rfl⟩ _ _ hsing _ hε x y hxy
  exact h A hA hsing _ hε x y hxy


theorem jPred_zero {ν : ℕ} (P : Params) (hN : 2 * (ν : ℝ) + 1 ≤ P.Nthr) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    JPred P Λ v 0 (Real.log (P.Nthr / (2 * ν)) - C₀ * scaleD P.K₀ 0 ^ (-(1 / 4 : ℝ))) :=
  fun _ _ hA _ hε x y _ =>
    (norm_finiteGreen_le_exp_base_restricted P hN hC₀ hA hε x y).2


theorem nPred_zero {ν : ℕ} (P : Params) (hN : 2 * (ν : ℝ) + 1 ≤ P.Nthr) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) : NPred P Λ v 0 (normBound P.K₀ 0) := by
  intro A _ hA ε hε x y
  rw [show normBound P.K₀ 0 = 1 by simp [normBound]]
  exact (norm_finiteGreen_le_exp_base_restricted P hN le_rfl hA hε x y).1


theorem jPred_mono {ν : ℕ} {P : Params} {Λ : Finset (Site ν)} {v : Site ν → ℝ} {k : ℕ}
    {m m' : ℝ} (hmm' : m' ≤ m) (h : JPred P Λ v k m) : JPred P Λ v k m' := by
  intro A hA hs ε hε x y hxy
  refine (h A hA hs ε hε x y hxy).trans (Real.exp_le_exp.2 ?_)
  nlinarith [siteDist_nonneg ν x y]


theorem massSeq_succ (K₀ mbase Cstep : ℝ) (k : ℕ) :
    massSeq K₀ mbase Cstep (k + 1) =
      massSeq K₀ mbase Cstep k - Cstep * scaleD K₀ k ^ (-(1 / 8 : ℝ)) := by
  unfold massSeq
  rw [Finset.sum_range_succ]
  ring


theorem massSeq_antitone (K₀ mbase : ℝ) {Cstep : ℝ} (hC : 0 ≤ Cstep) :
    Antitone (massSeq K₀ mbase Cstep) := by
  refine antitone_nat_of_succ_le fun k => ?_
  rw [massSeq_succ]
  have : 0 ≤ Cstep * scaleD K₀ k ^ (-(1 / 8 : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg (scaleD_pos K₀ k).le _)
  linarith

private theorem scaleD_rpow_neg_eighth (K₀ : ℝ) (i : ℕ) :
    scaleD K₀ i ^ (-(1 / 8 : ℝ)) = Real.exp (-(K₀ * (5 / 4 : ℝ) ^ i / 8)) := by
  unfold scaleD
  rw [← Real.exp_mul]
  congr 1
  ring

private theorem scaleD_rpow_succ_le {K₀ : ℝ} (hK : 32 * Real.log 2 ≤ K₀) (i : ℕ) :
    scaleD K₀ (i + 1) ^ (-(1 / 8 : ℝ)) ≤ scaleD K₀ i ^ (-(1 / 8 : ℝ)) / 2 := by
  rw [scaleD_rpow_neg_eighth, scaleD_rpow_neg_eighth]
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK0 : 0 ≤ K₀ := by linarith
  have h1 : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have h2 : Real.log 2 ≤ K₀ * (5 / 4 : ℝ) ^ i / 32 := by nlinarith
  have h3 : Real.exp (-(K₀ * (5 / 4 : ℝ) ^ (i + 1) / 8)) =
      Real.exp (-(K₀ * (5 / 4 : ℝ) ^ i / 8)) * Real.exp (-(K₀ * (5 / 4 : ℝ) ^ i / 32)) := by
    rw [← Real.exp_add, pow_succ]
    congr 1
    ring
  rw [h3]
  have h4 : Real.exp (-(K₀ * (5 / 4 : ℝ) ^ i / 32)) ≤ 1 / 2 := by
    calc _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h5 := Real.exp_pos (-(K₀ * (5 / 4 : ℝ) ^ i / 8))
  nlinarith


theorem sum_scaleD_rpow_le {K₀ : ℝ} (hK : 32 * Real.log 2 ≤ K₀) (k : ℕ) :
    ∑ i ∈ Finset.range k, scaleD K₀ i ^ (-(1 / 8 : ℝ)) ≤ 2 * scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) := by
  have hge : ∀ i, scaleD K₀ i ^ (-(1 / 8 : ℝ)) ≤ scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) * (1 / 2) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc _ ≤ scaleD K₀ i ^ (-(1 / 8 : ℝ)) / 2 := scaleD_rpow_succ_le hK i
        _ ≤ scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) * (1 / 2) ^ i / 2 := by linarith
        _ = _ := by rw [pow_succ]; ring
  calc _ ≤ ∑ i ∈ Finset.range k, scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) * (1 / 2) ^ i :=
        Finset.sum_le_sum fun i _ => hge i
    _ = scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) * ∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ i :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le k)
          (Real.rpow_nonneg (scaleD_pos K₀ 0).le _)
    _ = _ := by ring


theorem half_le_massSeq {K₀ mbase Cstep : ℝ} (hK : 32 * Real.log 2 ≤ K₀) (hC : 0 ≤ Cstep)
    (hsmall : 2 * Cstep * scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) ≤ mbase / 2) (k : ℕ) :
    mbase / 2 ≤ massSeq K₀ mbase Cstep k := by
  unfold massSeq
  have := mul_le_mul_of_nonneg_left (sum_scaleD_rpow_le hK k) hC
  linarith


theorem pow_mul_exp_le_entropy {M D m L : ℝ} (hM : 2 ≤ M) (hD : 0 < D) {n : ℕ}
    (hL : n * D / 2 ≤ L) :
    M ^ n * Real.exp (-(m * L)) ≤ (1 / 2) ^ n * Real.exp (-((m - 8 * Real.log M / D) * L)) := by
  have hM0 : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hn : (n : ℝ) ≤ 2 * L / D := by
    rw [le_div_iff₀ hD]; linarith
  have hX : (2 * M) ^ n ≤ Real.exp (8 * Real.log M / D * L) := by
    have h1 : (2 * M) ^ n ≤ (M ^ 2) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) n
    have h2 : (M ^ 2) ^ n = Real.exp (n * (2 * Real.log M)) := by
      rw [Real.exp_nat_mul, show 2 * Real.log M = Real.log M * 2 by ring,
        Real.exp_mul, Real.exp_log hM0]
      norm_cast
    rw [h2] at h1
    refine h1.trans (Real.exp_le_exp.2 ?_)
    have : (n : ℝ) * (2 * Real.log M) ≤ 2 * L / D * (2 * Real.log M) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    refine this.trans ?_
    have h3 : 0 ≤ Real.log M / D * L := by
      have : 0 ≤ L := le_trans (by positivity) hL
      positivity
    have : 2 * L / D * (2 * Real.log M) = 4 * (Real.log M / D * L) := by ring
    have : 8 * Real.log M / D * L = 8 * (Real.log M / D * L) := by ring
    nlinarith
  have hE : Real.exp (-((m - 8 * Real.log M / D) * L)) =
      Real.exp (-(m * L)) * Real.exp (8 * Real.log M / D * L) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hE]
  have hpos := Real.exp_pos (-(m * L))
  have h2n : (1 / 2 : ℝ) ^ n * (2 * M) ^ n = M ^ n := by
    rw [← mul_pow, show (1 / 2 : ℝ) * (2 * M) = M by ring]
  calc M ^ n * Real.exp (-(m * L)) = (1 / 2) ^ n * (2 * M) ^ n * Real.exp (-(m * L)) := by
        rw [h2n]
    _ ≤ (1 / 2) ^ n * (Real.exp (8 * Real.log M / D * L)) * Real.exp (-(m * L)) := by
        gcongr
    _ = _ := by ring

end FroehlichSpencer.T12

end
