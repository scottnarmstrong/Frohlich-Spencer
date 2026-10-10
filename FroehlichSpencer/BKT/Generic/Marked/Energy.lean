/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Expansion
public import FroehlichSpencer.BKT.Generic.SpinWave.Base
public import FroehlichSpencer.BKT.Generic.GaussianInstance
public import FroehlichSpencer.BKT.SpinWaves.Prop47
public import FroehlichSpencer.BKT.SpinWaves.Prop47Geometry
import Mathlib.Tactic

/-!
# The marked energy gain for the Gaussian cost

KP Lemma 4.5 and Proposition 4.7 (the energy clause (2.17) of KP P2.4) for a **marked** real
density, as FS81 §4–5 use them for Coulomb B (J pp. 562, 568–569: the gain for a marked
constituent is `c q_*² β` instead of `c β`).

* `gaussian_gain_of_pieces`: for pieces with pairwise disjoint gradients, `⟨ψ_t, ρ⟩ = q_t` and
  `‖∇ψ_t‖² ≤ K_t`, the amplitudes `q_t/(β K_t)` give `E_β ≥ ∑ q_t²/(2β K_t)` (spin-wave construction's
  `translationEnergy_sum_of_grad_disjoint` plus KP's one-piece optimization), for real `ρ`.
* `exists_halfMass_color`, `translationEnergy_colorPart_ge`: KP L4.5 for real densities,
  `E_β(ρ₁/(4β), ρ) ≥ ‖ρ‖²/(16β)` on a color class with half the mass.
* **`marked_gaussian_energy_ge`**: base wave plus square pieces with `|q_t| ≥ q_*` give
  `E_β ≥ β⁻¹(‖ρ‖²/16 + (q_*²/8192)·#pieces)`, KP's `D₃ = 1/8192` replaced by `q_*²/8192`.
* `pairing_squareWaveProfile_real`: KP's P4.7 profile pairs a real density to its patch charge.
* **`marked_patchCharge_ge`** (marked  and **`dipole_patchCharge_ge`**: the patch of every
  separated square of a neutral composite (separated squares of the integer support proxy
  `supportProxy`, as all KP geometry is support-based) carries charge `≥ η`; for Coulomb B,
  `η = min(ξ, 1 − ξ)`.

This supplies the hypothesis `|q_t| ≥ q_*` above.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

/-! ### The Gaussian translation energy of disjoint pieces -/

section Gain

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

omit [DecidableEq V] in
/-- The Gaussian translation energy of a multiple of one piece:
`E_β(λψ, ρ) = λ⟨ψ, ρ⟩ − (β/2) λ² ‖∇ψ‖²`. -/
theorem translationEnergy_gaussian_const_mul (G : Multigraph V E) (β c : ℝ) (ψ ρ : V → ℝ) :
    translationEnergy (fun u => β / 2 * u ^ 2) (gradLinear G) (fun j => c * ψ j) ρ =
      c * Multigraph.pairing ψ ρ - β / 2 * c ^ 2 * G.energy ψ := by
  unfold translationEnergy Multigraph.pairing Multigraph.energy
  have hg : ∀ e, (gradLinear G) (fun j => c * ψ j) e = c * G.grad ψ e := by
    intro e
    show G.grad (fun j => c * ψ j) e = c * G.grad ψ e
    unfold Multigraph.grad
    ring
  simp only [hg, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine Finset.sum_congr rfl fun e _ => ?_
    ring

omit [DecidableEq V] in
/-- **The Gaussian gain of disjoint pieces.** If the pieces `ψ_t` have pairwise disjoint gradient
supports, `⟨ψ_t, ρ⟩ = q_t` and `‖∇ψ_t‖² ≤ K_t`, the amplitudes `λ_t = q_t/(β K_t)` give
`E_β(∑ λ_t ψ_t, ρ) ≥ ∑ q_t² / (2 β K_t)`. This is KP's `energyFunctional_optimal_ge` summed over
disjoint pieces, for an arbitrary real density `ρ`. -/
theorem gaussian_gain_of_pieces (G : Multigraph V E) {β : ℝ} (hβ : 0 < β) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (ψ : ι → V → ℝ) (ρ : V → ℝ) (q K : ι → ℝ)
    (hK : ∀ t, 0 < K t) (hpair : ∀ t, Multigraph.pairing (ψ t) ρ = q t)
    (henergy : ∀ t, G.energy (ψ t) ≤ K t)
    (hdisj : ∀ t t', t ≠ t' → ∀ e, G.grad (ψ t) e = 0 ∨ G.grad (ψ t') e = 0) :
    ∑ t, q t ^ 2 / (2 * β * K t) ≤
      translationEnergy (fun u => β / 2 * u ^ 2) (gradLinear G)
        (fun j => ∑ t, q t / (β * K t) * ψ t j) ρ := by
  rw [SpinWave.translationEnergy_sum_of_grad_disjoint Finset.univ (fun u => β / 2 * u ^ 2)
    (by simp) (gradLinear G) (fun t j => q t / (β * K t) * ψ t j) ρ ?_]
  · refine Finset.sum_le_sum fun t _ => ?_
    rw [translationEnergy_gaussian_const_mul, hpair t]
    have hKt := hK t
    have hE := henergy t
    have hcoef : 0 ≤ β / 2 * (q t / (β * K t)) ^ 2 := by positivity
    have key : q t / (β * K t) * q t - β / 2 * (q t / (β * K t)) ^ 2 * K t =
        q t ^ 2 / (2 * β * K t) := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left hE hcoef]
  · intro t _ t' _ hne e
    have hg : ∀ (c : ℝ) (f : V → ℝ), (gradLinear G) (fun j => c * f j) e = c * G.grad f e := by
      intro c f
      show G.grad (fun j => c * f j) e = c * G.grad f e
      unfold Multigraph.grad
      ring
    rw [hg, hg]
    rcases hdisj t t' hne e with h | h
    · exact Or.inl (by rw [h, mul_zero])
    · exact Or.inr (by rw [h, mul_zero])

/-- The part of a real density on one color class. -/
def colorPart {G : Multigraph V E} (B : SpinWaves.BipartiteDegreeFour G) (ρ : V → ℝ)
    (b : Bool) : V → ℝ :=
  fun j => if B.color j = b then ρ j else 0

/-- One of the two color classes carries at least half of the squared mass of a real density
(the color choice of KP Lemma 4.5, for real densities). -/
theorem exists_halfMass_color {G : Multigraph V E} (B : SpinWaves.BipartiteDegreeFour G)
    (ρ : V → ℝ) :
    ∃ b : Bool, (1 / 2 : ℝ) * ∑ j, ρ j ^ 2 ≤ ∑ j, colorPart B ρ b j ^ 2 := by
  have hsplit : ∑ j, colorPart B ρ true j ^ 2 + ∑ j, colorPart B ρ false j ^ 2 =
      ∑ j, ρ j ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold colorPart
    cases B.color j <;> simp
  by_cases h : (1 / 2 : ℝ) * ∑ j, ρ j ^ 2 ≤ ∑ j, colorPart B ρ true j ^ 2
  · exact ⟨true, h⟩
  · exact ⟨false, by linarith⟩

/-- **KP Lemma 4.5 for real densities** (Gaussian cost): the base wave `ρ₁/(4β)`, `ρ₁` the part
of `ρ` on a class with half the mass, has `E_β ≥ ‖ρ‖²/(16β)`. -/
theorem translationEnergy_colorPart_ge (G : Multigraph V E) (B : SpinWaves.BipartiteDegreeFour G)
    {β : ℝ} (hβ : 0 < β) (ρ : V → ℝ) {b : Bool}
    (hb : (1 / 2 : ℝ) * ∑ j, ρ j ^ 2 ≤ ∑ j, colorPart B ρ b j ^ 2) :
    (∑ j, ρ j ^ 2) / (16 * β) ≤
      translationEnergy (fun u => β / 2 * u ^ 2) (gradLinear G)
        (fun j => 1 / (4 * β) * colorPart B ρ b j) ρ := by
  rw [translationEnergy_gaussian_const_mul]
  have hpair : Multigraph.pairing (colorPart B ρ b) ρ = ∑ j, colorPart B ρ b j ^ 2 := by
    unfold Multigraph.pairing colorPart
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hE : G.energy (colorPart B ρ b) ≤ 4 * ∑ j, colorPart B ρ b j ^ 2 :=
    SpinWaves.energy_le_four_sum_sq_of_one_color G B b _ fun j hj => by
      unfold colorPart at hj
      split_ifs at hj with h
      · exact h
      · exact absurd rfl hj
  rw [hpair]
  set m := ∑ j, colorPart B ρ b j ^ 2 with hm
  have hcoef : 0 ≤ β / 2 * (1 / (4 * β)) ^ 2 := by positivity
  have key : 1 / (4 * β) * m - β / 2 * (1 / (4 * β)) ^ 2 * (4 * m) = m / (8 * β) := by
    field_simp
    ring
  have h16 : (∑ j, ρ j ^ 2) / (16 * β) ≤ m / (8 * β) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hE hcoef]

/--
Then
`a = ρ₁/(4β) + ∑_t q_t/(4096β) ψ_t` satisfies
`E_β(a, ρ) ≥ β⁻¹ (‖ρ‖²/16 + (q_*²/8192) · #pieces)`: KP's `D₃ = 1/8192` becomes `q_*²/8192`.
-/
theorem marked_gaussian_energy_ge (G : Multigraph V E) (B : SpinWaves.BipartiteDegreeFour G)
    {β : ℝ} (hβ : 0 < β) (ρ : V → ℝ) {b : Bool}
    (hb : (1 / 2 : ℝ) * ∑ j, ρ j ^ 2 ≤ ∑ j, colorPart B ρ b j ^ 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : ι → V → ℝ) (q : ι → ℝ) {qStar : ℝ}
    (hqStar : 0 ≤ qStar) (hpair : ∀ t, Multigraph.pairing (ψ t) ρ = q t)
    (hgap : ∀ t, qStar ≤ |q t|) (henergy : ∀ t, G.energy (ψ t) ≤ 4096)
    (hdisj : ∀ t t', t ≠ t' → ∀ e, G.grad (ψ t) e = 0 ∨ G.grad (ψ t') e = 0)
    (hbase : ∀ t e, G.grad (colorPart B ρ b) e = 0 ∨ G.grad (ψ t) e = 0) :
    ((∑ j, ρ j ^ 2) / 16 + qStar ^ 2 / 8192 * Fintype.card ι) / β ≤
      translationEnergy (fun u => β / 2 * u ^ 2) (gradLinear G)
        (fun j => 1 / (4 * β) * colorPart B ρ b j + ∑ t, q t / (β * 4096) * ψ t j) ρ := by
  classical
  -- the base wave and the square pieces form one gradient-disjoint family indexed by `Option ι`
  let a : Option ι → V → ℝ := fun o => match o with
    | none => fun j => 1 / (4 * β) * colorPart B ρ b j
    | some t => fun j => q t / (β * 4096) * ψ t j
  have hg : ∀ (c : ℝ) (f : V → ℝ) (e : E),
      (gradLinear G) (fun j => c * f j) e = c * G.grad f e := by
    intro c f e
    show G.grad (fun j => c * f j) e = c * G.grad f e
    unfold Multigraph.grad
    ring
  have hdisjA : ∀ o ∈ (Finset.univ : Finset (Option ι)), ∀ o' ∈ Finset.univ, o ≠ o' → ∀ e,
      (gradLinear G) (a o) e = 0 ∨ (gradLinear G) (a o') e = 0 := by
    intro o _ o' _ hne e
    cases o with
    | none =>
      cases o' with
      | none => exact absurd rfl hne
      | some t' =>
        show (gradLinear G) (fun j => _ * _) e = 0 ∨ (gradLinear G) (fun j => _ * _) e = 0
        rw [hg, hg]
        rcases hbase t' e with h | h
        · exact Or.inl (by rw [h, mul_zero])
        · exact Or.inr (by rw [h, mul_zero])
    | some t =>
      cases o' with
      | none =>
        show (gradLinear G) (fun j => _ * _) e = 0 ∨ (gradLinear G) (fun j => _ * _) e = 0
        rw [hg, hg]
        rcases hbase t e with h | h
        · exact Or.inr (by rw [h, mul_zero])
        · exact Or.inl (by rw [h, mul_zero])
      | some t' =>
        show (gradLinear G) (fun j => _ * _) e = 0 ∨ (gradLinear G) (fun j => _ * _) e = 0
        rw [hg, hg]
        rcases hdisj t t' (fun h => hne (by rw [h])) e with h | h
        · exact Or.inl (by rw [h, mul_zero])
        · exact Or.inr (by rw [h, mul_zero])
  have hsum : (fun j => 1 / (4 * β) * colorPart B ρ b j + ∑ t, q t / (β * 4096) * ψ t j) =
      fun j => ∑ o : Option ι, a o j := by
    funext j
    rw [Fintype.sum_option]
  rw [hsum, SpinWave.translationEnergy_sum_of_grad_disjoint Finset.univ
    (fun u => β / 2 * u ^ 2) (by simp) (gradLinear G) a ρ hdisjA, Fintype.sum_option]
  have hbaseE := translationEnergy_colorPart_ge G B hβ ρ hb
  have hsq : ∀ t, qStar ^ 2 / (8192 * β) ≤
      translationEnergy (fun u => β / 2 * u ^ 2) (gradLinear G) (a (some t)) ρ := by
    intro t
    show _ ≤ translationEnergy _ _ (fun j => q t / (β * 4096) * ψ t j) ρ
    rw [translationEnergy_gaussian_const_mul, hpair t]
    have hq2 : qStar ^ 2 ≤ q t ^ 2 := by
      have := hgap t
      nlinarith [abs_nonneg (q t), sq_abs (q t)]
    have hcoef : 0 ≤ β / 2 * (q t / (β * 4096)) ^ 2 := by positivity
    have key : q t / (β * 4096) * q t - β / 2 * (q t / (β * 4096)) ^ 2 * 4096 =
        q t ^ 2 / (8192 * β) := by
      field_simp
      ring
    have h1 : qStar ^ 2 / (8192 * β) ≤ q t ^ 2 / (8192 * β) :=
      div_le_div_of_nonneg_right hq2 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left (henergy t) hcoef]
  have hsqsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hsq t
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsqsum
  have hsplit : ((∑ j, ρ j ^ 2) / 16 + qStar ^ 2 / 8192 * Fintype.card ι) / β =
      (∑ j, ρ j ^ 2) / (16 * β) + Fintype.card ι * (qStar ^ 2 / (8192 * β)) := by
    field_simp
  rw [hsplit]
  exact add_le_add hbaseE hsqsum

end Gain

/-! ### Square-wave profiles against real densities -/

section Profile

variable {V : Type} {E : Type} [Fintype V] [DecidableEq V]
  (G : Multigraph V E) (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)

/-- KP's P4.7 pairing `⟨ψ̃, ϱ*⟩ = q` for a **real** density (the marked composite): the profile
pairs to the patch charge when the components avoid the support and the rest of the support lies
beyond `S + 1`. -/
theorem pairing_squareWaveProfile_real {s : Finset V} (k : ℕ) {ρ : V → ℝ}
    (hoff : ∀ j, ρ j ≠ 0 → j ∉ SpinWaves.densityPlusUnion G N₁ centerOf)
    (hfar : ∀ j, ρ j ≠ 0 → j ∉ s → 2 ^ (k - 1) + 1 ≤ SpinWaves.P47.setDist G s j) :
    Multigraph.pairing (SpinWaves.P47.squareWaveProfile G N₁ centerOf s k) ρ = ∑ j ∈ s, ρ j := by
  classical
  have hrS := SpinWaves.P47.plateau_le_support k
  have hterm : ∀ j, SpinWaves.P47.squareWaveProfile G N₁ centerOf s k j * ρ j =
      if j ∈ s then ρ j else 0 := by
    intro j
    by_cases hj0 : ρ j = 0
    · simp [hj0]
    · have hjU := hoff j hj0
      unfold SpinWaves.P47.squareWaveProfile
      rw [SpinWaves.P47.flatten_of_not_mem G N₁ centerOf _ _ hjU]
      by_cases hjs : j ∈ s
      · rw [SpinWaves.P47.ramp_eq_one hrS (by
          rw [SpinWaves.P47.setDist_eq_zero_of_mem G hjs]; exact Nat.zero_le _),
          one_mul, ite_eq_left hjs]
      · rw [SpinWaves.P47.ramp_eq_zero hrS (hfar j hj0 hjs), zero_mul, ite_eq_right hjs]
  unfold Multigraph.pairing
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

end Profile

/-! ### The marked patch charge (marked  -/

section Patch

variable {boundary : SquareBoundary} {L : ℕ}

/-- **The marked patch charge** ( for the marked composite): for a neutral cluster of a KP
ensemble and a neutral mark with gapped proper restrictions, the patch of every separated square
of the composite support carries charge at least `η` in absolute value. -/
theorem marked_patchCharge_ge (hL : 1 < L) {ϱ₀ : ChargeDensity L} (hϱ₀ : ϱ₀ ≠ 0)
    (hmark : ∑ j, ϱ₀ j = 0) {ξ η : ℝ} (hη : η ≤ 1)
    (hgap : ∀ S : Finset (Fin L × Fin L), (∃ j ∈ S, ϱ₀ j ≠ 0) → (∃ j ∉ S, ϱ₀ j ≠ 0) →
      IsGapped η (ξ * ((∑ j ∈ S, ϱ₀ j : ℤ) : ℝ)))
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hb : IsScaleSeparated boundary L N) (hc : NeutralSplitsAreCharged boundary L N)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L ϱ₀ N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) {T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (k : PositiveSquareScale)
    (Cov : {Cov : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val (supportProxy (markedSupport L ϱ₀ C)) Cov})
    {s : Finset (Fin L × Fin L)}
    (hs : s ∈ separatedSquares boundary L (supportProxy (markedSupport L ϱ₀ C)) k Cov) :
    η ≤ |setCharge (markedDensity ξ ϱ₀ (satellite L C T)) (markedSupport L ϱ₀ C ∩ s)| := by
  have hsupp : chargeSupport (supportProxy (markedSupport L ϱ₀ C)) = markedSupport L ϱ₀ C :=
    chargeSupport_supportProxy _
  have hA : (markedSupport L ϱ₀ C ∩ s).Nonempty := by
    obtain ⟨z, hz⟩ := separatedSquare_patch_nonempty boundary L _ k Cov s hs
    rw [hsupp] at hz
    exact ⟨z, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hz).2, (Finset.mem_inter.1 hz).1⟩⟩
  have hB : (markedSupport L ϱ₀ C \ s).Nonempty := by
    obtain ⟨y, hy0, hys⟩ := SpinWaves.P47.exists_support_not_mem_separatedSquare boundary hs
    have hyX : y ∈ markedSupport L ϱ₀ C := by rw [← hsupp]; exact mem_chargeSupport'.2 hy0
    exact ⟨y, Finset.mem_sdiff.2 ⟨hyX, hys⟩⟩
  have hthr : squareSeparationThreshold k ≤
      (squareDistance boundary L (markedSupport L ϱ₀ C ∩ s) (markedSupport L ϱ₀ C \ s) : ℝ) := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_squareDistance_eq boundary L _ _ hA hB
    rw [hxy]
    refine pointwise_separation_of_separatedSquare boundary L _ k Cov s hs x
      (Finset.mem_inter.1 hx).2 y ?_
    rw [hsupp]
    exact hy
  have hdiam : squareDiameter boundary L (markedSupport L ϱ₀ C ∩ s) ≤ 2 * (2 ^ k.val - 1) := by
    obtain ⟨a, ha, b, hb', hab⟩ := exists_squareDiameter_eq boundary L _ hA
    rw [hab]
    exact SpinWaves.P47.latticeDistance_le_of_mem_separatedSquare boundary hL hs
      (Finset.mem_inter.1 ha).2 (Finset.mem_inter.1 hb').2
  have hsep : 2 * (chargeCoverScale : ℝ) *
      ((min (squareDiameter boundary L (markedSupport L ϱ₀ C ∩ s))
        (squareDiameter boundary L (markedSupport L ϱ₀ C \ s)) : ℕ) : ℝ) ^
          chargeCoverExponent ≤
      squareDistance boundary L (markedSupport L ϱ₀ C ∩ s) (markedSupport L ϱ₀ C \ s) := by
    refine le_trans ?_ hthr
    have hmin : min (squareDiameter boundary L (markedSupport L ϱ₀ C ∩ s))
        (squareDiameter boundary L (markedSupport L ϱ₀ C \ s)) < 2 ^ (k.val + 1) := by
      have := Nat.one_le_two_pow (n := k.val)
      have h3 := (min_le_left (squareDiameter boundary L (markedSupport L ϱ₀ C ∩ s))
        (squareDiameter boundary L (markedSupport L ϱ₀ C \ s))).trans hdiam
      rw [pow_succ]
      omega
    have hα : (0 : ℝ) < chargeCoverExponent := by norm_num [chargeCoverExponent]
    have hminR : ((min (squareDiameter boundary L (markedSupport L ϱ₀ C ∩ s))
        (squareDiameter boundary L (markedSupport L ϱ₀ C \ s)) : ℕ) : ℝ) <
          (2 : ℝ) ^ (k.val + 1) := by
      exact_mod_cast hmin
    have hpow : ((min (squareDiameter boundary L (markedSupport L ϱ₀ C ∩ s))
        (squareDiameter boundary L (markedSupport L ϱ₀ C \ s)) : ℕ) : ℝ) ^
          chargeCoverExponent ≤ (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := by
      calc _ ≤ ((2 : ℝ) ^ (k.val + 1)) ^ chargeCoverExponent :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hminR.le hα.le
        _ = (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
    unfold squareSeparationThreshold
    exact mul_le_mul_of_nonneg_left hpow (by norm_num [chargeCoverScale])
  exact markedComposite_charged_split hL hϱ₀ hmark hη hgap hens hb hc hC hCn hT s hA hB hsep

/-- **The Coulomb-B patch charge**: for the dipole `δ_o − δ_x` and a neutral cluster, every
separated-square patch of the composite carries charge at least `η = min(ξ, 1 − ξ)`. With
`marked_gaussian_energy_ge` this is KP's energy clause with `D₃ = η²/8192`. -/
theorem dipole_patchCharge_ge (hL : 1 < L) {o x : Fin L × Fin L} (hox : o ≠ x) (ξ : ℝ)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hb : IsScaleSeparated boundary L N) (hc : NeutralSplitsAreCharged boundary L N)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) {T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (k : PositiveSquareScale)
    (Cov : {Cov : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val
        (supportProxy (markedSupport L (dipoleMark o x) C)) Cov})
    {s : Finset (Fin L × Fin L)}
    (hs : s ∈ separatedSquares boundary L
      (supportProxy (markedSupport L (dipoleMark o x) C)) k Cov) :
    dipoleGap ξ ≤ |setCharge (markedDensity ξ (dipoleMark o x) (satellite L C T))
      (markedSupport L (dipoleMark o x) C ∩ s)| :=
  marked_patchCharge_ge hL (dipoleMark_ne_zero hox) (sum_univ_dipoleMark o x)
    (dipoleGap_le_one ξ) (fun S h1 h2 => dipole_isGapped_restriction ξ S h1 h2) hens hb hc hC
    hCn hT k Cov hs

end Patch

end FroehlichSpencer.BKT.Generic.Marked
