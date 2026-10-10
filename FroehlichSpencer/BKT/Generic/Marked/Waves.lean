/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Energy
public import FroehlichSpencer.BKT.Generic.Renormalization.Waves
import Mathlib.Tactic

/-!
# The marked P2.4 assembly: composite waves and the extended ensemble

* **`exists_realCompositeWave`** (KP Proposition 2.4 for a real density).

Let `p` be a neutral
  member of a KP ensemble `N` with (a)–(c), and let `ρ` be a real neutral density with the support
  of `p` whose patch charges `∑_{j ∈ s} ρ j` over the separated squares `s` of `p` have size at
  least `η`.

Then one wave satisfies P2.4 (1)–(3) for `p` in `N`, and
  `E_β(a, ρ) ≥ β⁻¹ (‖ρ‖²/16 + (η²/8192) ∑_k |𝒮_k^sep(p)|)`.
  - The square pieces are those of `exists_fullGradedSpinWave` : the P4.7 profiles of
    the L4.6, paired with `ρ` by `pairing_squareWaveProfile_real`.
  - The base piece is the half-mass colour part of `ρ` (`marked_gaussian_energy_ge`).

When
    `d(p) = 1` it is taken at the centre (`exists_halfMass_color_center`).
* **`markedExtension_kp`**: the integer proxy `p = ϱ₀ + 2ϱ^𝒩 = 2(½ϱ₀ + ϱ^𝒩)` of a dipole
  composite (`markedProxy`) has the composite's support (`chargeSupport_markedProxy_dipole`).

The
  remainder of the cluster together with `p` (`markedExtension`) is a KP ensemble with (a)–(c):
  - (b) is the remainder's separation from the composite (`markedRemainder_separation_*`);
  - (c) for `p` is `dipoleComposite_charged_split` at `ξ = 1/2`.

**L4.6 and property (c).** The L4.6 is applied only to integer KP ensembles, here the
extended ensemble `rem(C) ∪ {p}`.

Its property (c) is genuine KP (c), so no claim about how L4.6
uses (c) is needed:
- a split that cuts the mark carries an odd charge;
- any other split carries twice a nonzero composite charge.

The real composite's charges enter only through its energy, via the patch charges of
`exists_realCompositeWave`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

open SpinWaves SpinWaves.P47 Reduction

/-! ### The real-density spin wave of a composite -/

section RealWave

variable {V : Type} {E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- With the cost `c(u) = βu²/2`, the translation energy of a real density is KP's (2.12). -/
theorem translationEnergy_gaussian_real (G : Multigraph V E) (β : ℝ) (a ρ : V → ℝ) :
    translationEnergy (fun u => β / 2 * u ^ 2) (gradLinear G) a ρ =
      gffTranslationEnergy G β a ρ := by
  classical
  unfold gffTranslationEnergy translationEnergy Multigraph.pairing Multigraph.energy
  rw [Finset.mul_sum]
  rfl

omit [Fintype E] [DecidableEq V] in
/-- A function supported on at most one point: `∑ f² = (∑ f)²`. -/
theorem sum_sq_eq_sq_sum_of_subsingleton_support (f : V → ℝ)
    (h : ∀ j j', f j ≠ 0 → f j' ≠ 0 → j = j') : ∑ j, f j ^ 2 = (∑ j, f j) ^ 2 := by
  classical
  by_cases hz : ∃ j₀, f j₀ ≠ 0
  · obtain ⟨j₀, hj₀⟩ := hz
    have h1 : ∑ j, f j = f j₀ := Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ _)
      fun j _ hj => by
        by_contra hne
        exact hj (h j j₀ hne hj₀)
    have h2 : ∑ j, f j ^ 2 = f j₀ ^ 2 := Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ _)
      fun j _ hj => by
        by_contra hne
        exact hj (h j j₀ (fun h0 => hne (by rw [h0]; ring)) hj₀)
    rw [h1, h2]
  · push Not at hz
    simp [hz]

omit [Fintype E] [DecidableEq V] in
/-- Two support points of a density are at most `d(ϱ)` apart. -/
theorem dist_le_densityDiameter' (G : Multigraph V E) {ϱ : V → ℤ} {x y : V} (hx : ϱ x ≠ 0)
    (hy : ϱ y ≠ 0) : G.toSimpleGraph.dist x y ≤ G.densityDiameter ϱ := by
  classical
  have hmem : (x, y) ∈ (Finset.univ.filter fun j => ϱ j ≠ 0) ×ˢ
      (Finset.univ.filter fun j => ϱ j ≠ 0) := by simp [hx, hy]
  unfold Multigraph.densityDiameter
  exact Finset.le_sup (f := fun p : V × V => G.toSimpleGraph.dist p.1 p.2) hmem

/-- The base colour of a real density supported on the support of a neutral integer density `p`:
a class carrying half of the squared mass, which is the class of the center when `d(p) = 1`. Then
the only charged site of that class is the center. -/
theorem exists_halfMass_color_center (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (B : SpinWaves.BipartiteDegreeFour G) {p : V → ℤ} (ρ : V → ℝ)
    (hρsupp : ∀ j, ρ j ≠ 0 → p j ≠ 0) (hρ : ∑ j, ρ j = 0) {c : V}
    (hc : G.IsDensityCenter p c) :
    ∃ b : Bool, (1 / 2 : ℝ) * ∑ j, ρ j ^ 2 ≤ ∑ j, colorPart B ρ b j ^ 2 ∧
      (G.densityDiameter p = 1 → ∀ j, p j ≠ 0 → B.color j = b → j = c) := by
  classical
  by_cases hd1 : G.densityDiameter p = 1
  · set b := B.color c with hbdef
    -- two charged sites of one class coincide
    have hone : ∀ j j', p j ≠ 0 → p j' ≠ 0 → B.color j = B.color j' → j = j' := by
      intro j j' hj hj' hcol
      by_contra hne
      have hle : G.toSimpleGraph.dist j j' ≤ 1 := by
        have := dist_le_densityDiameter' G hj hj'
        omega
      have hpos := hG.pos_dist_of_ne hne
      have h1 : G.toSimpleGraph.dist j j' = 1 := by omega
      have hadj := SpinWaves.adj_fromSimpleGraph G (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact SpinWaves.not_adj_same_color G B hadj _ hcol rfl
    have hcenter : ∀ j, p j ≠ 0 → B.color j = b → j = c := fun j hj hcol =>
      hone j c hj hc.1 hcol
    refine ⟨b, ?_, fun _ => hcenter⟩
    have hsplit : ∑ j, colorPart B ρ b j ^ 2 + ∑ j, colorPart B ρ (!b) j ^ 2 =
        ∑ j, ρ j ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold colorPart
      cases hcj : B.color j <;> cases b <;> simp
    have hsum : ∑ j, colorPart B ρ b j + ∑ j, colorPart B ρ (!b) j = 0 := by
      rw [← Finset.sum_add_distrib, ← hρ]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold colorPart
      cases hcj : B.color j <;> cases b <;> simp
    have hsub : ∀ b' : Bool, ∀ j j', colorPart B ρ b' j ≠ 0 → colorPart B ρ b' j' ≠ 0 →
        j = j' := by
      intro b' j j' hj hj'
      have k1 : B.color j = b' ∧ ρ j ≠ 0 := by
        unfold colorPart at hj
        split_ifs at hj with h
        · exact ⟨h, hj⟩
        · exact absurd rfl hj
      have k2 : B.color j' = b' ∧ ρ j' ≠ 0 := by
        unfold colorPart at hj'
        split_ifs at hj' with h
        · exact ⟨h, hj'⟩
        · exact absurd rfl hj'
      exact hone j j' (hρsupp j k1.2) (hρsupp j' k2.2) (k1.1.trans k2.1.symm)
    rw [← hsplit, sum_sq_eq_sq_sum_of_subsingleton_support _ (hsub b),
      sum_sq_eq_sq_sum_of_subsingleton_support _ (hsub (!b)),
      show ∑ j, colorPart B ρ (!b) j = -∑ j, colorPart B ρ b j by linarith]
    nlinarith [sq_nonneg (∑ j, colorPart B ρ b j)]
  · obtain ⟨b, hb⟩ := exists_halfMass_color B ρ
    exact ⟨b, hb, fun h => absurd h hd1⟩

end RealWave

/-! ### The composite wave on a square domain -/

section Composite

variable (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]

/-- **KP Proposition 2.4 for a real density** (the marked composite wave). Let `p` be a neutral
member of a KP ensemble `N` with properties (a)–(c) on a square domain, and let `ρ` be a real
neutral density with the same support as `p` whose patch charges `∑_{j ∈ s} ρ j` over the
separated squares `s` of `p` (shared minimum covers) have absolute value at least `η`. Then one
wave `a` satisfies P2.4 (1)–(3) for `p` in `N`, and
`E_β(a, ρ) ≥ β⁻¹ (‖ρ‖²/16 + (η²/8192) ∑_k |𝒮_k^sep(p)|)`.

The pieces are those of `exists_fullGradedSpinWave` for `p`, with the half-mass colour part of
`ρ` as base wave (`marked_gaussian_energy_ge`); the square profiles pair with `ρ` to its patch
charges (`pairing_squareWaveProfile_real`). -/
theorem exists_realCompositeWave (hL : 1 < L) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    (N : Finset (Fin L × Fin L → ℤ)) (hens : IsChargeEnsemble N) (hNa : AtMostOneNonNeutral N)
    (hNb : IsScaleSeparated boundary L N) (hNc : NeutralSplitsAreCharged boundary L N)
    (p : Fin L × Fin L → ℤ) (hp : p ∈ neutralPart N) (ρ : Fin L × Fin L → ℝ)
    (hρsupp : ∀ j, ρ j ≠ 0 ↔ p j ≠ 0) (hρ : ∑ j, ρ j = 0) {η : ℝ} (hη : 0 ≤ η)
    (hgap : ∀ (k : {k : ℕ // 1 ≤ k}) (s : Finset (Fin L × Fin L)),
      s ∈ separatedSquares boundary L p k (sharedMinimumSquareCover boundary L p (by omega) k) →
        η ≤ |∑ j ∈ s, ρ j|)
    {β : ℝ} (hβ : 0 < β) :
    ∃ a : Fin L × Fin L → ℝ,
      (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) p,
        ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), a j = c) ∧
      Function.support a ⊆ Λ.densityDomain p (centerOf p) ∧
      Function.support (Λ.laplacian a) ⊆ Λ.densityDomain p (centerOf p) ∧
      ((∑ j, ρ j ^ 2) / 16 + η ^ 2 / 8192 *
          (separatedSquareTotal boundary L
            (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) p : ℝ)) / β ≤
        gffTranslationEnergy Λ β a ρ := by
  classical
  have hL0 : 0 < L := by omega
  have hdeg := B.endpointDegree_le_four
  obtain ⟨hpN, hpn⟩ := mem_neutralPart.mp hp
  have hp0 : p ≠ 0 := hens.1 p hpN
  have hc := hcenter p hp0
  set N₁ := Λ.comparableDensities (neutralPart N) p with hN₁
  have hsep := initialWaveSeparation_of_scaleSeparated boundary Λ hdist hΛ hens hNb centerOf
    hcenter hp
  -- the base colour class
  obtain ⟨b, hb, hbc⟩ := exists_halfMass_color_center Λ hΛ B ρ (fun j hj => (hρsupp j).1 hj)
    hρ hc
  have hbase_supp : ∀ j, colorPart B ρ b j ≠ 0 → p j ≠ 0 ∧ B.color j = b := by
    intro j hj
    unfold colorPart at hj
    split_ifs at hj with h
    · exact ⟨(hρsupp j).1 hj, h⟩
    · exact absurd rfl hj
  -- the separated squares, scale `k + 1` for `k < L`
  set sep : ℕ → Finset (Finset (Fin L × Fin L)) := fun k =>
    separatedSquares boundary L p ⟨k + 1, by omega⟩
      (sharedMinimumSquareCover boundary L p hL0 ⟨k + 1, by omega⟩) with hsepdef
  set T : Finset (Σ _ : ℕ, Finset (Fin L × Fin L)) := (Finset.range L).sigma sep with hT
  have hsepmem : ∀ t ∈ T, t.2 ∈ separatedSquares boundary L p ⟨t.1 + 1, by omega⟩
      (sharedMinimumSquareCover boundary L p hL0 ⟨t.1 + 1, by omega⟩) :=
    fun t ht => (Finset.mem_sigma.mp ht).2
  -- the profile of a square
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
  -- the base/square far-support fact
  have hbasefar : ∀ t ∈ T, ∀ x, p x ≠ 0 → x ∉ t.2 → ∀ y ∈ t.2,
      2 ^ (t.1 + 1 - 1) + 1 < Λ.toSimpleGraph.dist x y := by
    intro t ht x hx hxs y hy
    have h : 32 * 2 ^ (t.1 + 1) < latticeDistance boundary L y x :=
      thirtyTwo_mul_lt_latticeDistance boundary (hsepmem t ht) hy hx hxs
    rw [hdist, SimpleGraph.dist_comm] at h
    simp only [Nat.add_sub_cancel]
    have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
    omega
  -- two squares
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
  -- the support of `ρ` avoids the comparable domains and lies far from each square
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
  -- the energy of the family
  let ι := {t // t ∈ T}
  have hE := marked_gaussian_energy_ge Λ B hβ ρ hb (ι := ι) (fun t => ψ t.val)
    (fun t => ∑ j ∈ t.val.2, ρ j) hη (fun t => hpairR t.val t.property)
    (fun t => hgap ⟨t.val.1 + 1, by omega⟩ t.val.2 (hsepmem t.val t.property))
    (fun t => (hF t.val t.property).2.2.2.2.2.1)
    (fun t t' htt' e => by
      have hne : t.val ≠ t'.val := fun h => htt' (Subtype.ext h)
      rcases lt_trichotomy t.val.1 t'.val.1 with hlt | heq | hgt
      · exact hpair e t.val t.property t'.val t'.property hlt
      · exact hsame e t.val t.property t'.val t'.property hne heq
      · exact (hpair e t'.val t'.property t.val t.property hgt).symm)
    (fun t e => IsSquareWave.grad_disjoint_base Λ hΛ (hw t.val t.property)
      (fun j hj => (hbase_supp j hj).1) (hbasefar t.val t.property) e)
  have hcard : (Fintype.card ι : ℝ) = (separatedSquareTotal boundary L
      (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) p : ℝ) := by
    rw [Fintype.card_coe, hT, Finset.card_sigma]
    rfl
  rw [hcard, translationEnergy_gaussian_real] at hE
  refine ⟨_, ?_, ?_, ?_, hE⟩
  · -- clause (1): constant on every comparable `D⁺(ϱ')`
    intro ϱ' hϱ'
    have hcst : ∀ t : ι, ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), ψ t.val j = c :=
      fun t => (hF t.val t.property).2.2.1 ϱ' hϱ'
    choose cs hcs using hcst
    refine ⟨∑ t : ι, (∑ j ∈ t.val.2, ρ j) / (β * 4096) * cs t, fun j hj => ?_⟩
    have h0 : colorPart B ρ b j = 0 := by
      by_contra hne
      obtain ⟨y, hy, hjy⟩ := (Λ.mem_densityDomainPlus).1 hj
      have hfar := hsep ϱ' hϱ' y hy j (hbase_supp j hne).1
      rcases hjy with rfl | hadj
      · simp at hfar
      · have h1 : Λ.toSimpleGraph.dist y j = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
        omega
    simp only [h0, mul_zero, zero_add]
    exact Finset.sum_congr rfl fun t _ => by rw [hcs t j hj]
  · -- clause (2): `supp a ⊆ D(p)`
    intro j hj
    have hj' : 1 / (4 * β) * colorPart B ρ b j + ∑ t : ι, (∑ i ∈ t.val.2, ρ i) / (β * 4096) *
        ψ t.val j ≠ 0 := hj
    by_cases h0 : colorPart B ρ b j = 0
    · rw [h0, mul_zero, zero_add] at hj'
      obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
      have hψ0 : ψ t.val j ≠ 0 := fun h => ht (by rw [h, mul_zero])
      obtain ⟨y, hy, hjy⟩ := (hw t.val t.property).supp j hψ0
      exact hnearD t.val t.property j y hy (by simp only [Nat.add_sub_cancel] at hjy; omega)
    · exact Λ.mem_densityDomain_of_center hΛ hpn hc (hbase_supp j h0).1
  · -- clause (3): `supp Δa ⊆ D(p)`
    intro j hj
    set g : Option ι → Fin L × Fin L → ℝ := fun o => Option.elim o
      (fun i => 1 / (4 * β) * colorPart B ρ b i)
      (fun t i => (∑ k ∈ t.val.2, ρ k) / (β * 4096) * ψ t.val i) with hg
    have hsum : (fun i => 1 / (4 * β) * colorPart B ρ b i + ∑ t : ι,
        (∑ k ∈ t.val.2, ρ k) / (β * 4096) * ψ t.val i) = fun i => ∑ o ∈ Finset.univ, g o i := by
      funext i
      rw [Fintype.sum_option]
      rfl
    have hj' : ∑ o ∈ Finset.univ, Λ.laplacian (g o) j ≠ 0 := by
      rw [← laplacian_finset_sum Λ Finset.univ g j, ← hsum]
      exact hj
    obtain ⟨o, -, hoj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
    rcases o with _ | t
    · -- the base piece: within distance one of a charged site of colour `b`
      have hd1 := Λ.one_le_densityDiameter_of_neutral hΛ p hp0 hpn
      obtain ⟨x, hx0, hjx⟩ : ∃ x, colorPart B ρ b x ≠ 0 ∧ Λ.toSimpleGraph.dist j x ≤ 1 := by
        rcases laplacian_ne_zero_has_neighbor Λ (g none) j hoj with h0 | ⟨k, hk, hadj⟩
        · refine ⟨j, fun h => h0 ?_, by simp⟩
          show 1 / (4 * β) * colorPart B ρ b j = 0
          rw [h, mul_zero]
        · refine ⟨k, fun h => hk ?_, ?_⟩
          · show 1 / (4 * β) * colorPart B ρ b k = 0
            rw [h, mul_zero]
          · exact (SimpleGraph.dist_eq_one_iff_adj.mpr (adj_toSimpleGraph Λ hadj)).le
      obtain ⟨hpx, hcx⟩ := hbase_supp x hx0
      have hxc := Λ.dist_le_densityDiameter_of_center p (centerOf p) hc x hpx
      have tri := hΛ.dist_triangle (u := j) (v := x) (w := centerOf p)
      show Λ.toSimpleGraph.dist j (centerOf p) < 2 * Λ.densityDiameter p
      by_cases hdeq : Λ.densityDiameter p = 1
      · have hxeq := hbc hdeq x hpx hcx
        rw [hxeq] at hjx
        omega
      · omega
    · rcases laplacian_ne_zero_has_neighbor Λ (g (some t)) j hoj with h0 | ⟨k, hk, hadj⟩
      · have hψ0 : ψ t.val j ≠ 0 := fun h => h0 (by
          show (∑ i ∈ t.val.2, ρ i) / (β * 4096) * ψ t.val j = 0
          rw [h, mul_zero])
        obtain ⟨y, hy, hjy⟩ := (hw t.val t.property).supp j hψ0
        exact hnearD t.val t.property j y hy (by simp only [Nat.add_sub_cancel] at hjy; omega)
      · have hψ0 : ψ t.val k ≠ 0 := fun h => hk (by
          show (∑ i ∈ t.val.2, ρ i) / (β * 4096) * ψ t.val k = 0
          rw [h, mul_zero])
        obtain ⟨y, hy, hky⟩ := (hw t.val t.property).supp k hψ0
        have hjk : Λ.toSimpleGraph.dist j k = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (adj_toSimpleGraph Λ hadj)
        have tri := hΛ.dist_triangle (u := j) (v := k) (w := y)
        exact hnearD t.val t.property j y hy (by simp only [Nat.add_sub_cancel] at hky; omega)

end Composite


/-! ### The integer proxy of a marked composite and the extended ensemble -/

section Proxy

open Classical

variable {boundary : SquareBoundary} {L : ℕ}

/-- The integer proxy `ϱ₀ + 2 ϱ^𝒩 = 2 (½ ϱ₀ + ϱ^𝒩)` of the marked composite `ξ ϱ₀ + ϱ^𝒩`. For the
dipole it has the support of the composite (`chargeSupport_markedProxy_dipole`) and KP's
property (c) (`markedComposite_charged_split` at `ξ = 1/2`), so it can stand for the composite in
a KP ensemble, whose geometry is support-based. -/
def markedProxy (ρ₀ : ChargeDensity L) (C T : Finset (ChargeDensity L)) : ChargeDensity L :=
  fun j => ρ₀ j + 2 * satellite L C T j

/-- The extended ensemble of a marked term: the remainder of the cluster `C` and the proxy of
the composite. -/
def markedExtension (ρ₀ : ChargeDensity L) (N C T : Finset (ChargeDensity L)) :
    Finset (ChargeDensity L) :=
  insert (markedProxy ρ₀ C T) (markedRemainder boundary L ρ₀ N C)

theorem markedProxy_cast (ρ₀ : ChargeDensity L) (C T : Finset (ChargeDensity L))
    (j : Fin L × Fin L) :
    (markedProxy ρ₀ C T j : ℝ) = 2 * markedDensity (1 / 2) ρ₀ (satellite L C T) j := by
  unfold markedProxy markedDensity
  push_cast
  ring

/-- The satellite of a neutral cluster is neutral. -/
theorem sum_satellite {C T : Finset (ChargeDensity L)} (hCn : ∀ m ∈ C, ∑ j, m j = 0)
    (hT : T ⊆ C) : ∑ j, satellite L C T j = 0 := by
  unfold satellite
  rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := C \ T),
    Finset.sum_eq_zero fun m hm => hCn m (hT hm),
    Finset.sum_eq_zero fun m hm => hCn m (Finset.mem_sdiff.1 hm).1, sub_zero]

theorem sum_markedProxy {ρ₀ : ChargeDensity L} (hmark : ∑ j, ρ₀ j = 0)
    {C T : Finset (ChargeDensity L)} (hCn : ∀ m ∈ C, ∑ j, m j = 0) (hT : T ⊆ C) :
    ∑ j, markedProxy ρ₀ C T j = 0 := by
  unfold markedProxy
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmark, sum_satellite hCn hT]
  ring

/-- The marked composite of the dipole and its proxy vanish at the same sites. -/
theorem markedProxy_ne_zero_iff_dipole {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℝ}
    (h0 : 0 < ξ) (h1 : ξ < 1) {C T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m')) (j : Fin L × Fin L) :
    markedDensity ξ (dipoleMark o x) (satellite L C T) j ≠ 0 ↔
      markedProxy (dipoleMark o x) C T j ≠ 0 := by
  rw [dipole_markedDensity_ne_zero_iff hox h0 h1 hT hdisj,
    ← dipole_markedDensity_ne_zero_iff hox (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hT hdisj j]
  have hc := markedProxy_cast (dipoleMark o x) C T j
  constructor
  · intro h hp
    rw [hp, Int.cast_zero] at hc
    exact h (by linarith)
  · intro h hm
    rw [hm, mul_zero] at hc
    exact h (by exact_mod_cast hc)

theorem chargeSupport_markedProxy_dipole {o x : Fin L × Fin L} (hox : o ≠ x)
    {C T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m')) :
    chargeSupport (markedProxy (dipoleMark o x) C T) = markedSupport L (dipoleMark o x) C := by
  ext j
  rw [mem_chargeSupport', ← markedProxy_ne_zero_iff_dipole hox (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hT hdisj j,
    dipole_markedDensity_ne_zero_iff hox (by norm_num) (by norm_num) hT hdisj]

/-- A nonzero member has adjacency scale at least one against a composite of diameter `≥ 1`. -/
theorem one_le_markScale (hL : 1 < L) {ρ₀ m : ChargeDensity L} {C : Finset (ChargeDensity L)}
    (hm : m ≠ 0) (hX : 1 ≤ squareDiameter boundary L (markedSupport L ρ₀ C)) :
    1 ≤ markScale boundary L ρ₀ m C := by
  unfold markScale
  split_ifs with h
  · exact_mod_cast hX.trans (le_max_right _ _)
  · push Not at h
    have hd := one_le_chargeDiameter_of_neutral boundary hL m hm h.1
    exact_mod_cast le_min hd hX

/-- A remainder member is disjoint from (indeed at distance `≥ M` from) the composite support. -/
theorem disjoint_markedSupport_of_mem_markedRemainder (hL : 1 < L) {ρ₀ m : ChargeDensity L}
    {N C : Finset (ChargeDensity L)} (hm0 : m ≠ 0)
    (hX : 1 ≤ squareDiameter boundary L (markedSupport L ρ₀ C))
    (hm : m ∈ markedRemainder boundary L ρ₀ N C) :
    Disjoint (chargeSupport m) (markedSupport L ρ₀ C) := by
  have hsep := markedRemainder_separation hm
  have hs1 := one_le_markScale (boundary := boundary) hL hm0 hX (ρ₀ := ρ₀)
  have hpow : (1 : ℝ) ≤ markScale boundary L ρ₀ m C ^ chargeCoverExponent :=
    Real.one_le_rpow hs1 (by norm_num [chargeCoverExponent])
  have hM : (1 : ℝ) ≤ chargeCoverScale := by norm_num [chargeCoverScale]
  rw [Finset.disjoint_left]
  intro j hj hjX
  have h0 := squareDistance_le_latticeDistance_of_mem boundary L _ _ j j hj hjX
  have hself : latticeDistance boundary L j j = 0 := by
    cases boundary <;> simp [latticeDistance]
  rw [hself] at h0
  have : (squareDistance boundary L (chargeSupport m) (markedSupport L ρ₀ C) : ℝ) = 0 := by
    exact_mod_cast Nat.le_zero.mp h0
  nlinarith

/-- **The extended ensemble is a KP ensemble.** For the dipole mark, a neutral cluster `C` of a
KP ensemble `N` with (a)–(c), and `T ⊆ C`, the remainder of `C` together with the integer proxy
`p` of the composite is a KP ensemble with (a)–(c); `p` is a neutral member, not in the
remainder, with support `supp ϱ₀ ∪ ⋃ C`. Property (c) for `p` is the charged-split lemma of the
composite at `ξ = 1/2`; (b) is the remainder's separation from the composite. -/
theorem markedExtension_kp (hL : 1 < L) {o x : Fin L × Fin L} (hox : o ≠ x)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N) (hNa : AtMostOneNonNeutral N)
    (hNb : IsScaleSeparated boundary L N) (hNc : NeutralSplitsAreCharged boundary L N)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) {T : Finset (ChargeDensity L)} (hT : T ⊆ C) :
    IsChargeEnsemble (markedExtension (boundary := boundary) (dipoleMark o x) N C T) ∧
      AtMostOneNonNeutral (markedExtension (boundary := boundary) (dipoleMark o x) N C T) ∧
      IsScaleSeparated boundary L (markedExtension (boundary := boundary) (dipoleMark o x) N C T) ∧
      NeutralSplitsAreCharged boundary L
        (markedExtension (boundary := boundary) (dipoleMark o x) N C T) ∧
      markedProxy (dipoleMark o x) C T ∈
        neutralPart (markedExtension (boundary := boundary) (dipoleMark o x) N C T) ∧
      markedProxy (dipoleMark o x) C T ∉ markedRemainder boundary L (dipoleMark o x) N C ∧
      chargeSupport (markedProxy (dipoleMark o x) C T) = markedSupport L (dipoleMark o x) C := by
  set ρ₀ := dipoleMark o x with hρ₀
  set p := markedProxy ρ₀ C T with hpdef
  set X := markedSupport L ρ₀ C with hX
  set R := markedRemainder boundary L ρ₀ N C with hR
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hRN : R ⊆ N := remainder_subset _ _
  have hdisjC : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m') :=
    fun m hm m' hm' hne => hens.2 m (hCN hm) m' (hCN hm') hne
  have hsuppP : chargeSupport p = X := chargeSupport_markedProxy_dipole hox hT hdisjC
  have hX1 : 1 ≤ squareDiameter boundary L X := one_le_squareDiameter_markedSupport_dipole hL hox C
  have hpn : ∑ j, p j = 0 := sum_markedProxy (sum_univ_dipoleMark o x) hCn hT
  have hp0 : p ≠ 0 := by
    intro h
    have ho : o ∈ X := chargeSupport_subset_markedSupport _ C
      (mem_chargeSupport'.2 (by simp [hρ₀, dipoleMark, hox]))
    rw [← hsuppP, h] at ho
    exact (mem_chargeSupport'.1 ho) rfl
  have hdP : chargeDiameter boundary L p = squareDiameter boundary L X := by
    unfold chargeDiameter
    rw [hsuppP]
  have hdisjR : ∀ m ∈ R, Disjoint (chargeSupport m) X := fun m hm =>
    disjoint_markedSupport_of_mem_markedRemainder hL (hens.1 m (hRN hm)) hX1 hm
  have hpR : p ∉ R := by
    intro hp
    have h := hdisjR p hp
    rw [hsuppP] at h
    obtain ⟨j, hj⟩ := chargeSupport_nonempty' hp0
    rw [hsuppP] at hj
    exact Finset.disjoint_left.1 h hj hj
  have hfun : ∀ m ∈ R, Disjoint (Function.support m) (Function.support p) := by
    intro m hm
    rw [Function.disjoint_support_iff]
    intro j hj
    have hj' : j ∈ chargeSupport m := mem_chargeSupport'.2 hj
    by_contra hpj
    have hjX : j ∈ X := by rw [← hsuppP]; exact mem_chargeSupport'.2 hpj
    exact Finset.disjoint_left.1 (hdisjR m hm) hj' hjX
  have hmemE : ∀ ϱ, ϱ ∈ markedExtension (boundary := boundary) ρ₀ N C T ↔ ϱ = p ∨ ϱ ∈ R :=
    fun ϱ => Finset.mem_insert
  -- the distance between `p` and a remainder member
  have hdistP : ∀ m, densityDistance boundary L p m =
      squareDistance boundary L (chargeSupport m) X := by
    intro m
    unfold densityDistance
    rw [hsuppP, squareDistance_comm]
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, hpR, hsuppP⟩
  · -- nonzero members
    intro ϱ hϱ
    rcases (hmemE ϱ).1 hϱ with rfl | hϱ
    · exact hp0
    · exact hens.1 ϱ (hRN hϱ)
  · -- disjoint supports
    intro ϱ₁ h₁ ϱ₂ h₂ hne
    rcases (hmemE ϱ₁).1 h₁ with rfl | h₁ <;> rcases (hmemE ϱ₂).1 h₂ with rfl | h₂
    · exact absurd rfl hne
    · exact (hfun ϱ₂ h₂).symm
    · exact hfun ϱ₁ h₁
    · exact hens.2 ϱ₁ (hRN h₁) ϱ₂ (hRN h₂) hne
  · -- (a)
    intro ϱ₁ h₁ ϱ₂ h₂ hq₁ hq₂
    rcases (hmemE ϱ₁).1 h₁ with rfl | h₁
    · exact absurd hpn hq₁
    rcases (hmemE ϱ₂).1 h₂ with rfl | h₂
    · exact absurd hpn hq₂
    exact hNa ϱ₁ (hRN h₁) ϱ₂ (hRN h₂) hq₁ hq₂
  · -- (b), first clause
    have hpm : ∀ m ∈ R, (chargeCoverScale : ℝ) *
        ((min (chargeDiameter boundary L p) (chargeDiameter boundary L m) : ℕ) : ℝ) ^
          chargeCoverExponent ≤ densityDistance boundary L p m := by
      intro m hm
      rw [hdistP, hdP, min_comm]
      exact markedRemainder_separation_min hm
    intro ϱ₁ h₁ ϱ₂ h₂ hne
    rcases (hmemE ϱ₁).1 h₁ with rfl | h₁ <;> rcases (hmemE ϱ₂).1 h₂ with rfl | h₂
    · exact absurd rfl hne
    · exact hpm ϱ₂ h₂
    · rw [min_comm]
      unfold densityDistance
      rw [squareDistance_comm]
      exact hpm ϱ₁ h₁
    · exact hNb.1 ϱ₁ (hRN h₁) ϱ₂ (hRN h₂) hne
  · -- (b), second clause
    intro ϱc hc hq ϱ hϱ hne
    rcases (hmemE ϱc).1 hc with rfl | hc
    · exact absurd hpn hq
    rcases (hmemE ϱ).1 hϱ with rfl | hϱ
    · have h := markedRemainder_separation_of_charged hc (Or.inl hq)
      rw [hdistP, hdP]
      refine le_trans ?_ h
      have hα : (0 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hα)
        (by norm_num [chargeCoverScale])
      exact_mod_cast le_max_right _ _
    · exact hNb.2 ϱc (hRN hc) hq ϱ (hRN hϱ) hne
  · -- (c)
    intro ϱ hϱ hq ϱ₁ ϱ₂ h₁ h₂ hdisj hsum hsep
    rcases (hmemE ϱ).1 hϱ with rfl | hϱ
    · -- the proxy: the charged-split lemma of the composite at `ξ = 1/2`
      have hval : ∀ j, ϱ₁ j ≠ 0 → ϱ₂ j = 0 := fun j hj => by
        by_contra h
        exact Set.disjoint_left.1 hdisj hj h
      have hval2 : ∀ j, ϱ₂ j ≠ 0 → ϱ₁ j = 0 := fun j hj => by
        by_contra h
        exact Set.disjoint_left.1 hdisj h hj
      have hpj : ∀ j, p j = ϱ₁ j + ϱ₂ j := fun j => by rw [hsum]; rfl
      set S := chargeSupport ϱ₁ with hS
      have hXS : X ∩ S = chargeSupport ϱ₁ := by
        ext j
        simp only [Finset.mem_inter, hS, mem_chargeSupport']
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          rw [← hsuppP, mem_chargeSupport', hpj, hval j h, add_zero]
          exact h
      have hXS' : X \ S = chargeSupport ϱ₂ := by
        ext j
        simp only [Finset.mem_sdiff, hS, mem_chargeSupport']
        constructor
        · rintro ⟨hjX, hj1⟩
          rw [← hsuppP, mem_chargeSupport', hpj] at hjX
          push Not at hj1
          rwa [hj1, zero_add] at hjX
        · intro h
          refine ⟨?_, fun h' => h' (hval2 j h)⟩
          rw [← hsuppP, mem_chargeSupport', hpj, hval2 j h, zero_add]
          exact h
      have hA : (X ∩ S).Nonempty := by rw [hXS]; exact chargeSupport_nonempty' h₁
      have hB : (X \ S).Nonempty := by rw [hXS']; exact chargeSupport_nonempty' h₂
      have hsep' : 2 * (chargeCoverScale : ℝ) *
          ((min (squareDiameter boundary L (X ∩ S)) (squareDiameter boundary L (X \ S)) : ℕ) :
            ℝ) ^ chargeCoverExponent ≤ squareDistance boundary L (X ∩ S) (X \ S) := by
        rw [hXS, hXS']
        exact hsep
      have hgap := dipoleComposite_charged_split hL hox (1 / 2) hens hNb hNc hC hCn hT S hA hB
        hsep'
      have hgap0 : 0 < dipoleGap (1 / 2 : ℝ) := dipoleGap_pos (by norm_num) (by norm_num)
      -- the charge of `ϱ₁` is twice the composite charge on `X ∩ S`
      have hQ : ((∑ j, ϱ₁ j : ℤ) : ℝ) =
          2 * setCharge (markedDensity (1 / 2) ρ₀ (satellite L C T)) (X ∩ S) := by
        have h1 : ∑ j, ϱ₁ j = ∑ j ∈ S, ϱ₁ j :=
          (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by
            by_contra h
            exact hj (mem_chargeSupport'.2 h)).symm
        have h2 : ∑ j ∈ S, ϱ₁ j = ∑ j ∈ X ∩ S, p j := by
          rw [hXS]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hpj, hval j (mem_chargeSupport'.1 hj), add_zero]
        rw [h1, h2, setCharge, Finset.mul_sum]
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        exact markedProxy_cast ρ₀ C T j
      have hne1 : ∑ j, ϱ₁ j ≠ 0 := by
        intro h0
        rw [h0, Int.cast_zero] at hQ
        have : setCharge (markedDensity (1 / 2) ρ₀ (satellite L C T)) (X ∩ S) = 0 := by linarith
        rw [this, abs_zero] at hgap
        linarith
      refine ⟨hne1, ?_⟩
      have htot : ∑ j, ϱ₁ j + ∑ j, ϱ₂ j = 0 := by
        rw [← Finset.sum_add_distrib, ← hpn]
        exact Finset.sum_congr rfl fun j _ => (hpj j).symm
      omega
    · exact hNc ϱ (hRN hϱ) hq ϱ₁ ϱ₂ h₁ h₂ hdisj hsum hsep
  · exact mem_neutralPart.2 ⟨Finset.mem_insert_self _ _, hpn⟩

end Proxy

end FroehlichSpencer.BKT.Generic.Marked
