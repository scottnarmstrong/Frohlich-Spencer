/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Assembly
public import FroehlichSpencer.BKT.Generic.Marked.Waves
import Mathlib.Tactic

/-!
# The composite wave of a marked clock term

This is the marked analogue of KP P2.4 for the clock cost, with uniform amplitude (FS81 §7.1, the
marked lower bound `L_q(β, n) ≥ K_q n − Lβ` of T7.2 in KP's geometry). The composite
`ρ = (ξ/n)ϱ₀ + ϱ^𝒩` of a marked term is real. Its proxy `p` is a neutral member of the extended KP
ensemble. Every nonzero value of `ρ`, and every patch charge over the separated squares of `p`,
has absolute value at least `η`.

The wave uses amplitude `λ` throughout: the sign wave of the linear-mass colour class of `ρ`
(each edge gradient at most `2`), plus the signed P4.7 profiles of the separated squares (each
gradient at most `28`). With `28λ ≤ n` the clock cost stays in its quadratic range
`c(u) ≤ βu²/n²`, so `8192βλ ≤ ηn²` gives the gain.

* `realSign`, `exists_linearMassColor_real`.
* **`exists_clockCompositeWave`**: the P2.4 support and constancy clauses for `p`, and
  `E_c(a, ρ) ≥ (λ/4) ∑_j |ρ_j| + (λη/2) ∑_k |𝒮_k^sep(p)|`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open SpinWaves SpinWaves.P47 Reduction
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked

/-! ### Real signs and the linear-mass colour class -/

/-- The sign of a real number, `0` at `0`. -/
def realSign (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then -1 else 0

theorem realSign_mul_self (t : ℝ) : realSign t * t = |t| := by
  unfold realSign
  split_ifs with h1 h2
  · rw [one_mul, abs_of_pos h1]
  · rw [abs_of_neg h2]; ring
  · have : t = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
    simp [this]

theorem abs_realSign_le_one (t : ℝ) : |realSign t| ≤ 1 := by
  unfold realSign
  split_ifs <;> simp

/-- One colour class carries at least half of the linear mass of a real density. -/
theorem exists_linearMassColor_real {V : Type*} [Fintype V] (color : V → Bool) (ρ : V → ℝ) :
    ∃ b : Bool, (1 / 2 : ℝ) * ∑ j, |ρ j| ≤
      ∑ j, if color j = b then |ρ j| else 0 := by
  have hsplit : ∑ j, |ρ j| = (∑ j, if color j = true then |ρ j| else 0) +
      ∑ j, if color j = false then |ρ j| else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases color j <;> simp
  by_cases h : (1 / 2 : ℝ) * ∑ j, |ρ j| ≤ ∑ j, if color j = true then |ρ j| else 0
  · exact ⟨true, h⟩
  · exact ⟨false, by linarith⟩

/-! ### The clock composite wave -/

section Composite

variable (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]

/-- **The composite wave for the clock cost** (the marked analogue of KP P2.4 with the compact
cost, uniform amplitude). Let `p` be a neutral member of a KP ensemble `N` with (a)–(c), and `ρ`
a real neutral density with the support of `p`, whose nonzero values and whose patch charges over
the separated squares of `p` have absolute value at least `η`. With amplitude `λ` on the sign
wave of the linear-mass colour class of `ρ` and on the signed P4.7 profiles of the separated
squares, and `28 λ ≤ n`, `8192 β λ ≤ η n²` (so that the clock cost stays in its quadratic range
`c(u) ≤ β u²/n²`),
`E_c(a, ρ) ≥ (λ/4) ∑_j |ρ_j| + (λη/2) ∑_k |𝒮_k^sep(p)|`, and `a` satisfies the support and
constancy clauses of P2.4 for `p` in `N`. -/
theorem exists_clockCompositeWave (hL : 1 < L) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    (N : Finset (Fin L × Fin L → ℤ)) (hens : IsChargeEnsemble N) (hNa : AtMostOneNonNeutral N)
    (hNb : IsScaleSeparated boundary L N) (hNc : NeutralSplitsAreCharged boundary L N)
    (p : Fin L × Fin L → ℤ) (hp : p ∈ neutralPart N) (ρ : Fin L × Fin L → ℝ)
    (hρsupp : ∀ j, ρ j ≠ 0 ↔ p j ≠ 0) {η : ℝ} (hη : 0 < η)
    (hsite : ∀ j, ρ j ≠ 0 → η ≤ |ρ j|)
    (hgap : ∀ (k : {k : ℕ // 1 ≤ k}) (s : Finset (Fin L × Fin L)),
      s ∈ separatedSquares boundary L p k (sharedMinimumSquareCover boundary L p (by omega) k) →
        η ≤ |∑ j ∈ s, ρ j|)
    {β n lam : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hlam : 0 ≤ lam) (hlamn : 28 * lam ≤ n)
    (hcost : 8192 * β * lam ≤ η * n ^ 2) :
    ∃ a : Fin L × Fin L → ℝ,
      (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) p,
        ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), a j = c) ∧
      Function.support a ⊆ Λ.densityDomain p (centerOf p) ∧
      lam / 4 * ∑ j, |ρ j| + lam * η / 2 *
          (separatedSquareTotal boundary L
            (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) p : ℝ) ≤
        translationEnergy (clockShiftCost β n) (gradLinear Λ) a ρ := by
  classical
  have hL0 : 0 < L := by omega
  have hdeg := B.endpointDegree_le_four
  obtain ⟨hpN, hpn⟩ := mem_neutralPart.mp hp
  have hp0 : p ≠ 0 := hens.1 p hpN
  have hc := hcenter p hp0
  set N₁ := Λ.comparableDensities (neutralPart N) p with hN₁
  have hsep := initialWaveSeparation_of_scaleSeparated boundary Λ hdist hΛ hens hNb centerOf
    hcenter hp
  -- the separated squares, scale `k + 1` for `k < L`
  set sep : ℕ → Finset (Finset (Fin L × Fin L)) := fun k =>
    separatedSquares boundary L p ⟨k + 1, by omega⟩
      (sharedMinimumSquareCover boundary L p hL0 ⟨k + 1, by omega⟩) with hsepdef
  set T : Finset (Σ _ : ℕ, Finset (Fin L × Fin L)) := (Finset.range L).sigma sep with hT
  have hsepmem : ∀ t ∈ T, t.2 ∈ separatedSquares boundary L p ⟨t.1 + 1, by omega⟩
      (sharedMinimumSquareCover boundary L p hL0 ⟨t.1 + 1, by omega⟩) :=
    fun t ht => (Finset.mem_sigma.mp ht).2
  set ψ : (Σ _ : ℕ, Finset (Fin L × Fin L)) → Fin L × Fin L → ℝ :=
    fun t => squareWaveProfile Λ N₁ centerOf t.2 (t.1 + 1) with hψ
  have hF := fun t (ht : t ∈ T) => squareProfile_facts boundary hL Λ hΛ hdist hdeg h46 centerOf
    hcenter N hens hNa hNb hNc p hp ⟨t.1 + 1, by omega⟩
    (sharedMinimumSquareCover boundary L p hL0 ⟨t.1 + 1, by omega⟩) t.2 (hsepmem t ht)
  have hsne : ∀ t ∈ T, t.2.Nonempty := by
    intro t ht
    obtain ⟨z, hz⟩ := separatedSquare_patch_nonempty boundary L p _ _ t.2 (hsepmem t ht)
    exact ⟨z, (Finset.mem_inter.mp hz).1⟩
  have hw : ∀ t ∈ T, IsSquareWave Λ t.2 (t.1 + 1) (ψ t) := by
    intro t ht
    refine ⟨fun j hj => (setDist_le_iff Λ (hsne t ht) j _).mp ((hF t ht).1 j hj),
      ⟨1, fun j hj => (hF t ht).2.1 j ((setDist_le_iff Λ (hsne t ht) j _).mpr hj)⟩⟩
  have hnearD : ∀ t ∈ T, ∀ j y, y ∈ t.2 → Λ.toSimpleGraph.dist j y ≤ 2 ^ t.1 + 1 →
      j ∈ Λ.densityDomain p (centerOf p) := by
    intro t ht j y hy hjy
    exact mem_densityDomain_of_near_separatedSquare boundary hL Λ hdist hΛ hc
      (by omega) (hsepmem t ht) hy (by simpa using hjy)
  have hbasefar : ∀ t ∈ T, ∀ x, p x ≠ 0 → x ∉ t.2 → ∀ y ∈ t.2,
      2 ^ (t.1 + 1 - 1) + 1 < Λ.toSimpleGraph.dist x y := by
    intro t ht x hx hxs y hy
    have h : 32 * 2 ^ (t.1 + 1) < latticeDistance boundary L y x :=
      thirtyTwo_mul_lt_latticeDistance boundary (hsepmem t ht) hy hx hxs
    rw [hdist, SimpleGraph.dist_comm] at h
    simp only [Nat.add_sub_cancel]
    have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
    omega
  have hpair : ∀ e, ∀ t ∈ T, ∀ t' ∈ T, t.1 < t'.1 →
      Λ.grad (ψ t) e = 0 ∨ Λ.grad (ψ t') e = 0 := by
    intro e t ht t' ht' hlt
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, hwx⟩ : ∃ x, (x = Λ.src e ∨ x = Λ.tgt e) ∧ ψ t x ≠ 0 := by
      rcases ne_zero_of_grad_ne_zero Λ (ψ t) e hcon.1 with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    obtain ⟨x', hx', hwx'⟩ : ∃ x', (x' = Λ.src e ∨ x' = Λ.tgt e) ∧ ψ t' x' ≠ 0 := by
      rcases ne_zero_of_grad_ne_zero Λ (ψ t') e hcon.2 with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    obtain ⟨y, hy, hxy⟩ := (hw t ht).supp x hwx
    obtain ⟨y', hy', hxy'⟩ := (hw t' ht').supp x' hwx'
    obtain ⟨hsrc, htgt⟩ := cross_scale_endpoints_near boundary hL Λ hdist hΛ p
      (by omega : 1 ≤ t.1 + 1) (by omega : t.1 + 1 < t'.1 + 1) (hsepmem t ht)
      (hsepmem t' ht') e hx hx' hy hxy hy' hxy'
    exact hcon.2 ((hw t' ht').grad_eq_zero Λ e hsrc htgt)
  have hsame : ∀ e, ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → t.1 = t'.1 →
      Λ.grad (ψ t) e = 0 ∨ Λ.grad (ψ t') e = 0 := by
    intro e t ht t' ht' htt' heq
    have hs2 : t.2 ≠ t'.2 := fun h => htt' (Sigma.ext heq (heq_of_eq h))
    refine IsSquareWave.grad_disjoint_of_far Λ hΛ (hw t ht) (hw t' ht') ?_ e
    intro y hy y' hy'
    have hsC : t'.2 ∈ (sharedMinimumSquareCover boundary L p hL0
        ⟨t.1 + 1, by omega⟩).val := by
      have := (Finset.mem_filter.mp (hsepmem t' ht')).1
      rwa [show (⟨t'.1 + 1, by omega⟩ : {k : ℕ // 1 ≤ k}) = ⟨t.1 + 1, by omega⟩ from
        Subtype.ext (by simp [heq])] at this
    have h32' : 32 * 2 ^ (t.1 + 1) < Λ.toSimpleGraph.dist y y' := by
      rw [← hdist]
      exact thirtyTwo_mul_lt_latticeDistance_of_mem_cover boundary (hsepmem t ht) hsC
        (Ne.symm hs2) hy hy'
    simp only [Nat.add_sub_cancel]
    rw [← heq]
    have : 2 ^ t.1 ≤ 2 ^ (t.1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
    omega
  have hoff : ∀ j, ρ j ≠ 0 → j ∉ densityPlusUnion Λ N₁ centerOf := by
    intro j hj hjU
    obtain ⟨ϱ', hϱ', hjD⟩ := (mem_densityPlusUnion Λ N₁ centerOf j).1 hjU
    obtain ⟨y, hy, hjy⟩ := (Λ.mem_densityDomainPlus).1 hjD
    have hfar := hsep ϱ' hϱ' y hy j ((hρsupp j).1 hj)
    rcases hjy with rfl | hadj
    · simp at hfar
    · have h1 : Λ.toSimpleGraph.dist y j = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      omega
  have hfarR : ∀ t ∈ T, ∀ j, ρ j ≠ 0 → j ∉ t.2 →
      2 ^ (t.1 + 1 - 1) + 1 ≤ setDist Λ t.2 j := by
    intro t ht j hj hjs
    obtain ⟨y, hy, hjy⟩ := exists_setDist_eq Λ (hsne t ht) j
    have h : 32 * 2 ^ (t.1 + 1) < latticeDistance boundary L y j :=
      thirtyTwo_mul_lt_latticeDistance boundary (hsepmem t ht) hy ((hρsupp j).1 hj) hjs
    rw [hdist, SimpleGraph.dist_comm, ← hjy] at h
    simp only [Nat.add_sub_cancel]
    have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
    omega
  have hpairR : ∀ t ∈ T, Multigraph.pairing (ψ t) ρ = ∑ j ∈ t.2, ρ j := fun t ht =>
    pairing_squareWaveProfile_real Λ N₁ centerOf (t.1 + 1) hoff (hfarR t ht)
  -- the base colour class and its sign wave
  obtain ⟨b, hb⟩ := exists_linearMassColor_real B.color ρ
  set u : Fin L × Fin L → ℝ := fun j => if B.color j = b then realSign (ρ j) else 0 with hu
  have hu_supp : ∀ j, u j ≠ 0 → ρ j ≠ 0 ∧ B.color j = b := by
    intro j hj
    simp only [hu] at hj
    split_ifs at hj with h
    · refine ⟨fun h0 => hj (by simp [h0, realSign]), h⟩
    · exact absurd rfl hj
  have hu_le : ∀ j, |u j| ≤ 1 := fun j => by
    simp only [hu]
    split_ifs
    · exact abs_realSign_le_one _
    · simp
  have hu_pair : ∑ j, u j * ρ j = ∑ j, if B.color j = b then |ρ j| else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu]
    split_ifs
    · exact realSign_mul_self _
    · simp
  -- the family
  set ι := {t // t ∈ T}
  set rs : ι → ℝ := fun t => realSign (∑ j ∈ t.val.2, ρ j) with hrs
  set g : Option ι → Fin L × Fin L → ℝ := fun o => Option.elim o (fun j => lam * u j)
    (fun t j => lam * rs t * ψ t.val j) with hg
  set a : Fin L × Fin L → ℝ := fun j => ∑ o, g o j with ha
  have hgrad_smul : ∀ (c : ℝ) (f : Fin L × Fin L → ℝ) e,
      Λ.grad (fun j => c * f j) e = c * Λ.grad f e := fun c f e => by
    unfold Multigraph.grad; ring
  have hdisj : ∀ o ∈ (Finset.univ : Finset (Option ι)), ∀ o' ∈ (Finset.univ : Finset (Option ι)),
      o ≠ o' → ∀ e, gradLinear Λ (g o) e = 0 ∨ gradLinear Λ (g o') e = 0 := by
    have hbase : ∀ (t : ι) e, Λ.grad u e = 0 ∨ Λ.grad (ψ t.val) e = 0 := fun t e =>
      IsSquareWave.grad_disjoint_base Λ hΛ (hw t.val t.property)
        (fun j hj => (hρsupp j).1 (hu_supp j hj).1) (hbasefar t.val t.property) e
    intro o _ o' _ hoo' e
    change Λ.grad (g o) e = 0 ∨ Λ.grad (g o') e = 0
    rcases o with _ | t <;> rcases o' with _ | t'
    · exact absurd rfl hoo'
    · simp only [hg, Option.elim, hgrad_smul]
      rcases hbase t' e with h | h
      · exact Or.inl (by rw [h, mul_zero])
      · exact Or.inr (by rw [h, mul_zero])
    · simp only [hg, Option.elim, hgrad_smul]
      rcases hbase t e with h | h
      · exact Or.inr (by rw [h, mul_zero])
      · exact Or.inl (by rw [h, mul_zero])
    · have hne : t.val ≠ t'.val := fun h => hoo' (congrArg some (Subtype.ext h))
      simp only [hg, Option.elim, hgrad_smul]
      have h : Λ.grad (ψ t.val) e = 0 ∨ Λ.grad (ψ t'.val) e = 0 := by
        rcases lt_trichotomy t.val.1 t'.val.1 with hlt | heq | hgt
        · exact hpair e t.val t.property t'.val t'.property hlt
        · exact hsame e t.val t.property t'.val t'.property hne heq
        · exact (hpair e t'.val t'.property t.val t.property hgt).symm
      rcases h with h | h
      · exact Or.inl (by rw [h, mul_zero])
      · exact Or.inr (by rw [h, mul_zero])
  have hc0 : clockShiftCost β n 0 = 0 := by simp [clockShiftCost]
  have hEsum := Generic.SpinWave.translationEnergy_sum_of_grad_disjoint Finset.univ
    (clockShiftCost β n) hc0
    (gradLinear Λ) g ρ hdisj
  -- the quadratic range of the clock cost
  have hquad : ∀ u : ℝ, |u| ≤ n → clockShiftCost β n u ≤ β / n ^ 2 * u ^ 2 :=
    fun u hu => clockShiftCost_le_quadratic β n u hβ hn hu
  have hcnn : ∀ u : ℝ, 0 ≤ clockShiftCost β n u := by
    intro u
    unfold clockShiftCost
    have := Real.one_le_cosh (u / n)
    nlinarith
  have hn2 : 0 < n ^ 2 := by positivity
  -- the base piece
  set Sb : ℝ := ∑ j, if B.color j = b then |ρ j| else 0 with hSb
  have hcardb : ((Finset.univ.filter fun j => u j ≠ 0).card : ℝ) * η ≤ Sb := by
    rw [hSb, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => u j ≠ 0)]
    have h1 : ((Finset.univ.filter fun j => u j ≠ 0).card : ℝ) * η ≤
        ∑ j ∈ Finset.univ.filter (fun j => u j ≠ 0), if B.color j = b then |ρ j| else 0 := by
      have hconst : ((Finset.univ.filter fun j => u j ≠ 0).card : ℝ) * η =
          ∑ _j ∈ Finset.univ.filter (fun j => u j ≠ 0), η := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨h1, h2⟩ := hu_supp j (Finset.mem_filter.1 hj).2
      simp only [h2, ↓reduceIte]
      exact hsite j h1
    have h2 : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬u j ≠ 0),
        if B.color j = b then |ρ j| else 0 :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> simp
    linarith
  have hEbase :
      lam / 2 * Sb ≤ translationEnergy (clockShiftCost β n) (gradLinear Λ) (g none) ρ := by
    have hge : ∀ e, |Λ.grad u e| ≤ 2 := fun e => by
      unfold Multigraph.grad
      have := abs_sub (u (Λ.src e)) (u (Λ.tgt e))
      linarith [hu_le (Λ.src e), hu_le (Λ.tgt e)]
    have hcost_e : ∀ e, clockShiftCost β n (gradLinear Λ (g none) e) ≤
        (if Λ.grad u e ≠ 0 then 4 * β / n ^ 2 * lam ^ 2 else 0) := by
      intro e
      change clockShiftCost β n (Λ.grad (fun j => lam * u j) e) ≤ _
      rw [hgrad_smul]
      split_ifs with h
      · have hlu : |lam * Λ.grad u e| ≤ n := by
          rw [abs_mul, abs_of_nonneg hlam]
          nlinarith [hge e, abs_nonneg (Λ.grad u e)]
        refine (hquad _ hlu).trans ?_
        have h4 : (lam * Λ.grad u e) ^ 2 ≤ 4 * lam ^ 2 := by
          rw [mul_pow]
          have : Λ.grad u e ^ 2 ≤ 4 := by
            have := hge e
            nlinarith [sq_abs (Λ.grad u e), abs_nonneg (Λ.grad u e)]
          nlinarith [sq_nonneg lam]
        calc β / n ^ 2 * (lam * Λ.grad u e) ^ 2 ≤ β / n ^ 2 * (4 * lam ^ 2) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = 4 * β / n ^ 2 * lam ^ 2 := by ring
      · push Not at h
        rw [h, mul_zero, hc0]
    have hcount := card_grad_ne_zero_le Λ hdeg u (Finset.univ.filter fun j => u j ≠ 0)
      (fun j hj => Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
    have hsumc : ∑ e, clockShiftCost β n (gradLinear Λ (g none) e) ≤
        4 * β / n ^ 2 * lam ^ 2 * (4 * Sb / η) := by
      refine (Finset.sum_le_sum fun e _ => hcost_e e).trans ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hc' : ((Finset.univ.filter fun e => Λ.grad u e ≠ 0).card : ℝ) ≤ 4 * Sb / η := by
        rw [le_div_iff₀ hη]
        have : ((Finset.univ.filter fun e => Λ.grad u e ≠ 0).card : ℝ) ≤
            4 * ((Finset.univ.filter fun j => u j ≠ 0).card : ℝ) := by exact_mod_cast hcount
        nlinarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hc' (by positivity)
    have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun j _ => by split_ifs <;> simp
    have hpair0 : ∑ j, g none j * ρ j = lam * Sb := by
      simp only [hg, Option.elim, mul_assoc, ← Finset.mul_sum]
      rw [hu_pair]
    unfold translationEnergy
    rw [hpair0]
    have hk : 4 * β / n ^ 2 * lam ^ 2 * (4 * Sb / η) ≤ lam / 2 * Sb := by
      rw [show 4 * β / n ^ 2 * lam ^ 2 * (4 * Sb / η) = (16 * β * lam) / (n ^ 2 * η) * (lam * Sb)
        by field_simp; ring]
      rw [show lam / 2 * Sb = (1 / 2) * (lam * Sb) by ring]
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hlam hSb0)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- the square pieces
  have hEsq : ∀ t : ι, lam * η / 2 ≤
      translationEnergy (clockShiftCost β n) (gradLinear Λ) (g (some t)) ρ := by
    intro t
    have hgap' := hgap ⟨t.val.1 + 1, by omega⟩ t.val.2 (hsepmem t.val t.property)
    have hgrad28 : ∀ e, |Λ.grad (ψ t.val) e| ≤ 28 := by
      intro e
      refine ((hF t.val t.property).2.2.2.2.2.2.1 e).trans ?_
      have := rpow_neg_gradExponent_le_one (by norm_num : (1 : ℝ) < 7 / 4) (t.val.1 + 1)
      unfold gradExponent at this
      have h' : (2 : ℝ) ^ (-(1 - 1 / (7 / 4 : ℝ)) * ((t.val.1 + 1 : ℕ) : ℝ)) ≤ 1 := by
        simpa [neg_mul] using this
      nlinarith
    have hrs1 : |rs t| ≤ 1 := abs_realSign_le_one _
    have hcost_e : ∀ e, clockShiftCost β n (gradLinear Λ (g (some t)) e) ≤
        β / n ^ 2 * lam ^ 2 * Λ.grad (ψ t.val) e ^ 2 := by
      intro e
      change clockShiftCost β n (Λ.grad (fun j => lam * rs t * ψ t.val j) e) ≤ _
      rw [hgrad_smul]
      have hlu : |lam * rs t * Λ.grad (ψ t.val) e| ≤ n := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlam]
        calc lam * |rs t| * |Λ.grad (ψ t.val) e| ≤ lam * 1 * 28 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hrs1 hlam) (hgrad28 e) (abs_nonneg _)
                (by positivity)
          _ ≤ n := by linarith
      refine (hquad _ hlu).trans ?_
      have : (lam * rs t * Λ.grad (ψ t.val) e) ^ 2 ≤ lam ^ 2 * Λ.grad (ψ t.val) e ^ 2 := by
        have h1 : rs t ^ 2 ≤ 1 := by nlinarith [sq_abs (rs t), abs_nonneg (rs t)]
        have h2 : 0 ≤ lam ^ 2 * Λ.grad (ψ t.val) e ^ 2 := by positivity
        calc (lam * rs t * Λ.grad (ψ t.val) e) ^ 2 =
              rs t ^ 2 * (lam ^ 2 * Λ.grad (ψ t.val) e ^ 2) :=
              by ring
          _ ≤ 1 * (lam ^ 2 * Λ.grad (ψ t.val) e ^ 2) := mul_le_mul_of_nonneg_right h1 h2
          _ = _ := one_mul _
      calc β / n ^ 2 * (lam * rs t * Λ.grad (ψ t.val) e) ^ 2 ≤
            β / n ^ 2 * (lam ^ 2 * Λ.grad (ψ t.val) e ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = β / n ^ 2 * lam ^ 2 * Λ.grad (ψ t.val) e ^ 2 := by ring
    have hsumc : ∑ e, clockShiftCost β n (gradLinear Λ (g (some t)) e) ≤
        β / n ^ 2 * lam ^ 2 * 4096 := by
      refine (Finset.sum_le_sum fun e _ => hcost_e e).trans ?_
      rw [← Finset.mul_sum]
      have hen := (hF t.val t.property).2.2.2.2.2.1
      unfold Multigraph.energy at hen
      exact mul_le_mul_of_nonneg_left hen (by positivity)
    have hpair1 : ∑ j, g (some t) j * ρ j = lam * |∑ j ∈ t.val.2, ρ j| := by
      have h1 : ∑ j, g (some t) j * ρ j = lam * rs t * Multigraph.pairing (ψ t.val) ρ := by
        simp only [hg, Option.elim, Multigraph.pairing, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h1, hpairR t.val t.property, mul_assoc, hrs, realSign_mul_self]
    unfold translationEnergy
    rw [hpair1]
    have hk : β / n ^ 2 * lam ^ 2 * 4096 ≤ lam * η / 2 := by
      rw [show β / n ^ 2 * lam ^ 2 * 4096 = (4096 * β * lam) / n ^ 2 * lam by field_simp]
      rw [show lam * η / 2 = η / 2 * lam by ring]
      refine mul_le_mul_of_nonneg_right ?_ hlam
      rw [div_le_iff₀ hn2]
      nlinarith
    have : lam * η ≤ lam * |∑ j ∈ t.val.2, ρ j| := mul_le_mul_of_nonneg_left hgap' hlam
    have hsumc' : ∑ e, clockShiftCost β n (gradLinear Λ (g (some t)) e) ≤ lam * η / 2 :=
      hsumc.trans hk
    linarith
  have hcard : (Fintype.card ι : ℝ) = (separatedSquareTotal boundary L
      (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) p : ℝ) := by
    rw [Fintype.card_coe, hT, Finset.card_sigma]
    rfl
  refine ⟨a, ?_, ?_, ?_⟩
  · -- clause (1): constant on every comparable `D⁺(ϱ')`
    intro ϱ' hϱ'
    have hcst : ∀ t : ι, ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), ψ t.val j = c :=
      fun t => (hF t.val t.property).2.2.1 ϱ' hϱ'
    choose cs hcs using hcst
    refine ⟨∑ t : ι, lam * rs t * cs t, fun j hj => ?_⟩
    have h0 : u j = 0 := by
      by_contra hne
      obtain ⟨y, hy, hjy⟩ := (Λ.mem_densityDomainPlus).1 hj
      have hfar := hsep ϱ' hϱ' y hy j ((hρsupp j).1 (hu_supp j hne).1)
      rcases hjy with rfl | hadj
      · simp at hfar
      · have h1 : Λ.toSimpleGraph.dist y j = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
        omega
    simp only [ha, hg, Fintype.sum_option, Option.elim, h0, mul_zero, zero_add]
    exact Finset.sum_congr rfl fun t _ => by rw [hcs t j hj]
  · -- clause (2): `supp a ⊆ D(p)`
    intro j hj
    have hj' : ∑ o, g o j ≠ 0 := hj
    obtain ⟨o, -, hoj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
    rcases o with _ | t
    · have hu0 : u j ≠ 0 := fun h => hoj (by simp [hg, h])
      exact Λ.mem_densityDomain_of_center hΛ hpn hc ((hρsupp j).1 (hu_supp j hu0).1)
    · have hψ0 : ψ t.val j ≠ 0 := fun h => hoj (by simp [hg, h])
      obtain ⟨y, hy, hjy⟩ := (hw t.val t.property).supp j hψ0
      exact hnearD t.val t.property j y hy (by simp only [Nat.add_sub_cancel] at hjy; omega)
  · -- the energy
    have hEa : translationEnergy (clockShiftCost β n) (gradLinear Λ) a ρ =
        ∑ o, translationEnergy (clockShiftCost β n) (gradLinear Λ) (g o) ρ := hEsum
    rw [hEa, Fintype.sum_option]
    have hsq : ∑ _t : ι, lam * η / 2 ≤
        ∑ t : ι, translationEnergy (clockShiftCost β n) (gradLinear Λ) (g (some t)) ρ :=
      Finset.sum_le_sum fun t _ => hEsq t
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsq
    have hb' : lam / 4 * ∑ j, |ρ j| ≤ lam / 2 * Sb := by
      have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ lam / 2)
      rw [hSb]
      linarith
    nlinarith

end Composite

end FroehlichSpencer.BKT.Clock.Compact

end
