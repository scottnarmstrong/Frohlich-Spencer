/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAInterface

/-!
# One terminal profile: the flat-core ramp and its single-piece clauses

For a charged selected square `s ∈ P'_j(ρ)` with cluster `K` and a profile potential `f`
(`IsProfilePotential`), the piece is `ψ = clamp(3/2 − f/2^j, 0, 1)` on bounded faces and `0` at
the wired root (`profilePiece`): value `1` where `f ≤ 2^{j−1}` (on `K` and its first neighbours),
`0` where `f ≥ 3·2^{j−1}`.

Write `N` for the sites within `(9/4)·2^j` of `K`
(`IsProfileNear`); the support clause of the potential puts every site with `f < 2^{j+1}` in `N`.

* a nonzero gradient sits on a lattice edge with both ends in `N`; root edges have zero gradient,
  since `N` has depth `≥ (7/4)·2^j` (`exists_near_of_grad_ne_zero`);
* `|∇ψ| ≤ 2^{−j}` (`abs_grad_profilePiece_le`);
* at most `100·4^{j+3}` nonzero gradients (`card_grad_profilePiece_ne_zero_le`), and energy
  `≤ 6400` (`energy_profilePiece_le`);
* the pairing with `ϱ` is the cluster charge `Q(K)` (`pairing_profilePiece`);
* support in the density domain about `routineCenter` (`support_profilePiece_subset`) and gradients
  in `routineS` (`grad_profilePiece_mem_routineS`).

The near lemmas used for the other clauses: a density `σ ≠ ρ` with charge in `N`, or with a profile
of its own whose `N` meets this one at a smaller or equal scale, is neutral and tiny, i.e. in the
collapse family (`mem_profileCollapseFamily_of_near_support`,
`mem_profileCollapseFamily_of_near_near`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-! ## The ramp and the piece -/

/-- The flat-core ramp at scale `j`: `1` for `n ≤ 2^j/2`, `0` for `n ≥ 3·2^j/2`, slope `2^{-j}`. -/
def profileRamp (j : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (3 / 2 - t / 2 ^ j))

theorem profileRamp_eq_one {j : ℕ} {t : ℝ} (h : t ≤ 2 ^ j / 2) : profileRamp j t = 1 := by
  unfold profileRamp
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have : t / 2 ^ j ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem profileRamp_eq_zero {j : ℕ} {t : ℝ} (h : 3 * 2 ^ j / 2 ≤ t) : profileRamp j t = 0 := by
  unfold profileRamp
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have : 3 / 2 ≤ t / 2 ^ j := by rw [le_div_iff₀ hp]; linarith
  have := min_le_right (1 : ℝ) (3 / 2 - t / 2 ^ j)
  rw [max_eq_left (by linarith)]

theorem lt_of_profileRamp_ne_zero {j : ℕ} {t : ℝ} (h : profileRamp j t ≠ 0) :
    t < 3 * 2 ^ j / 2 := by
  by_contra h'
  exact h (profileRamp_eq_zero (not_lt.mp h'))

theorem abs_clamp_sub_le (a b : ℝ) : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem abs_profileRamp_sub_le (j : ℕ) (t u : ℝ) :
    |profileRamp j t - profileRamp j u| ≤ |t - u| / 2 ^ j := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  refine (abs_clamp_sub_le _ _).trans (le_of_eq ?_)
  rw [show 3 / 2 - t / 2 ^ j - (3 / 2 - u / 2 ^ j) = -((t - u) / 2 ^ j) by ring,
    abs_neg, abs_div, abs_of_pos hp]

/-- **The profile** of a potential at scale `j`: the ramp on bounded faces, `0` at the root. -/
def profilePiece (j : ℕ) (f : Site L → ℝ) : RotatorDualFace L → ℝ
  | none => 0
  | some x => profileRamp j (f x)

@[simp] theorem profilePiece_none (j : ℕ) (f : Site L → ℝ) : profilePiece j f none = 0 := rfl

@[simp] theorem profilePiece_some (j : ℕ) (f : Site L → ℝ) (x : Site L) :
    profilePiece j f (some x) = profileRamp j (f x) := rfl

/-- The chosen profile potential (Hilbert choice; a profile potential whenever one exists). -/
def profilePotential (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K : Finset (Site L)) : Site L → ℝ :=
  Classical.epsilon (IsProfilePotential F ρ j K)

theorem profilePotential_spec {F : Finset (ChargeDensity L)} {ρ : ChargeDensity L} {j : ℕ}
    {K : Finset (Site L)} (h : ∃ f, IsProfilePotential F ρ j K f) :
    IsProfilePotential F ρ j K (profilePotential F ρ j K) :=
  Classical.epsilon_spec h

/-! ## The context of one piece -/

/-- A charged selected square of a density of a boundary-separated ensemble, with a potential. -/
structure ProfileContext (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (s : Finset (Site L)) (f : Site L → ℝ) : Prop where
  separated : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F
  nonzero : ∀ σ ∈ F, σ ≠ 0
  mem : ρ ∈ F
  one_le : 1 ≤ j
  selected : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ
    (boundaryEntropyMinimumCover ρ j)
  square : ChargedSelectedSquare ρ j s
  potential : IsProfilePotential F ρ j (chargeSupport (chargeRestriction ρ s)) f

/-- The sites within `(9/4)·2^j` of the cluster. -/
def IsProfileNear (ρ : ChargeDensity L) (j : ℕ) (s : Finset (Site L)) (x : Site L) : Prop :=
  ∃ k ∈ chargeSupport (chargeRestriction ρ s), euclideanSiteDistance x k ≤ 9 / 4 * 2 ^ j

/-- The near sites as a finite set. -/
def profileNearSet (ρ : ChargeDensity L) (j : ℕ) (s : Finset (Site L)) : Finset (Site L) := by
  classical
  exact Finset.univ.filter fun x => IsProfileNear ρ j s x

theorem mem_profileNearSet {ρ : ChargeDensity L} {j : ℕ} {s : Finset (Site L)} {x : Site L} :
    x ∈ profileNearSet ρ j s ↔ IsProfileNear ρ j s x := by
  classical
  unfold profileNearSet
  simp

theorem two_le_two_pow {j : ℕ} (hj : 1 ≤ j) : (2 : ℝ) ≤ 2 ^ j := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj

theorem cluster_subset {ρ : ChargeDensity L} {s : Finset (Site L)} {k : Site L}
    (hk : k ∈ chargeSupport (chargeRestriction ρ s)) : k ∈ s ∧ k ∈ chargeSupport ρ :=
  (mem_chargeSupport_restriction_iff ρ s k).mp hk

section Context

variable {F : Finset (ChargeDensity L)} {ρ : ChargeDensity L} {j : ℕ} {s : Finset (Site L)}
  {f : Site L → ℝ}

theorem ProfileContext.cluster_nonempty (h : ProfileContext F ρ j s f) :
    (chargeSupport (chargeRestriction ρ s)).Nonempty :=
  chargeSupport_nonempty_of_ne_zero (chargeRestriction ρ s)
    (fun h0 => h.square.charged (by simp [h0, totalCharge]))

theorem ProfileContext.near_of_lt (h : ProfileContext F ρ j s f) {x : Site L}
    (hx : f x < 2 ^ (j + 1)) : IsProfileNear ρ j s x := by
  have hc := h.potential.support x hx
  obtain ⟨k, hk, y, hy, heq⟩ := exists_setDist_eq h.cluster_nonempty (Finset.singleton_nonempty x)
  rw [Finset.mem_singleton.mp hy] at heq
  refine ⟨k, hk, ?_⟩
  rw [siteDist_comm, ← heq]
  have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  linarith

theorem ProfileContext.near_of_ramp_ne_zero (h : ProfileContext F ρ j s f) {x : Site L}
    (hx : profileRamp j (f x) ≠ 0) : IsProfileNear ρ j s x := by
  refine h.near_of_lt ((lt_of_profileRamp_ne_zero hx).trans_le ?_)
  have : (0 : ℝ) < 2 ^ j := by positivity
  rw [pow_succ]
  linarith

/-- Near sites are deep: depth `≥ (7/4)·2^j`. -/
theorem ProfileContext.depth_of_near (h : ProfileContext F ρ j s f) {x : Site L}
    (hx : IsProfileNear ρ j s x) : 7 / 4 * (2 : ℝ) ^ j ≤ siteBoundaryDepth x := by
  obtain ⟨k, hk, hxk⟩ := hx
  have h1 := h.square.depth k hk
  have h2 := depth_le_add_siteDist k x
  rw [siteDist_comm] at h2
  have h3 : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
  linarith


/-- A near charge of `ρ` lies in the cluster. -/
theorem ProfileContext.mem_cluster_of_near (h : ProfileContext F ρ j s f) {x : Site L}
    (hx : IsProfileNear ρ j s x) (hxρ : x ∈ chargeSupport ρ) :
    x ∈ chargeSupport (chargeRestriction ρ s) := by
  obtain ⟨k, hk, hxk⟩ := hx
  by_cases hxs : x ∈ s
  · exact (mem_chargeSupport_restriction_iff ρ s x).mpr ⟨hxs, hxρ⟩
  · have h1 := h.square.far k hk x hxρ hxs
    have h2 := two_pow_le_selectionSeparation j
    rw [siteDist_comm] at hxk
    have : (0 : ℝ) < 2 ^ j := by positivity
    linarith

/-- Far from the cluster the ramp vanishes. -/
theorem ProfileContext.ramp_eq_zero_of_not_near (h : ProfileContext F ρ j s f) {x : Site L}
    (hx : ¬ IsProfileNear ρ j s x) : profileRamp j (f x) = 0 := by
  by_contra hne
  exact hx (h.near_of_ramp_ne_zero hne)

/-- The ramp is `1` within `ℓ¹` distance `2^{j−1}` of the cluster. -/
theorem ProfileContext.ramp_eq_one_of_l1 (h : ProfileContext F ρ j s f) {x k : Site L}
    (hk : k ∈ chargeSupport (chargeRestriction ρ s)) (hxk : (l1 x k : ℝ) ≤ 2 ^ j / 2) :
    profileRamp j (f x) = 1 := by
  apply profileRamp_eq_one
  have h1 := le_add_l1_of_lipschitz h.potential.lipschitz x k
  rw [h.potential.zero k hk, zero_add] at h1
  linarith

/-! ### Gradients -/

theorem squareZero_edge_cases (e : SquareZeroBond L) :
    (∃ x y : Site L, (squareZero L).src e = some x ∧ (squareZero L).tgt e = some y ∧
      l1 x y = 1) ∨
    (∃ x : Site L, (squareZero L).src e = some x ∧ (squareZero L).tgt e = none) := by
  cases e with
  | inl e₀ => exact Or.inl ⟨_, _, rfl, rfl, l1_of_edge (e := Sum.inl e₀) rfl rfl⟩
  | inr b => exact Or.inr ⟨_, rfl, rfl⟩

/-- **A nonzero gradient sits on a lattice edge with both ends near the cluster.** -/
theorem ProfileContext.exists_near_of_grad_ne_zero (h : ProfileContext F ρ j s f) (hL : 1 < L)
    {e : SquareZeroBond L} (he : (squareZero L).grad (profilePiece j f) e ≠ 0) :
    ∃ x y : Site L, (squareZero L).src e = some x ∧ (squareZero L).tgt e = some y ∧
      l1 x y = 1 ∧ f x < 2 ^ (j + 1) ∧ f y < 2 ^ (j + 1) := by
  have hj2 := two_le_two_pow h.one_le
  have hp : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  rcases squareZero_edge_cases e with ⟨x, y, hs, ht, hxy⟩ | ⟨x, hs, ht⟩
  · refine ⟨x, y, hs, ht, hxy, ?_⟩
    rw [Multigraph.grad, hs, ht, profilePiece_some, profilePiece_some] at he
    have cxy := h.potential.lipschitz x y hxy
    have cyx := h.potential.lipschitz y x (by rw [l1_comm]; exact hxy)
    by_cases hx0 : profileRamp j (f x) = 0
    · have hy0 : profileRamp j (f y) ≠ 0 := fun hy0 => he (by rw [hx0, hy0, sub_zero])
      have := lt_of_profileRamp_ne_zero hy0
      constructor <;> linarith
    · have := lt_of_profileRamp_ne_zero hx0
      constructor <;> linarith
  · exfalso
    apply he
    rw [Multigraph.grad, hs, ht, profilePiece_some, profilePiece_none, sub_zero]
    apply h.ramp_eq_zero_of_not_near
    intro hnear
    have h1 := h.depth_of_near hnear
    have h2 : (siteBoundaryDepth x : ℝ) ≤ 1 := by exact_mod_cast depth_le_one_of_root_edge hL hs ht
    linarith

/-- **The gradient bound** `|∇ψ| ≤ 2^{−j}`. -/
theorem ProfileContext.abs_grad_profilePiece_le (h : ProfileContext F ρ j s f) (hL : 1 < L)
    (e : SquareZeroBond L) : |(squareZero L).grad (profilePiece j f) e| ≤ 1 / 2 ^ j := by
  by_cases he : (squareZero L).grad (profilePiece j f) e = 0
  · rw [he, abs_zero]; positivity
  obtain ⟨x, y, hs, ht, hxy, -, -⟩ := h.exists_near_of_grad_ne_zero hL he
  rw [Multigraph.grad, hs, ht, profilePiece_some, profilePiece_some]
  refine (abs_profileRamp_sub_le j (f x) (f y)).trans ?_
  have cxy := h.potential.lipschitz x y hxy
  have cyx := h.potential.lipschitz y x (by rw [l1_comm]; exact hxy)
  have : |f x - f y| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact div_le_div_of_nonneg_right this (by positivity)

/-- The near sites number at most `961·4^j`. -/
theorem ProfileContext.card_near_le (h : ProfileContext F ρ j s f) :
    ((profileNearSet ρ j s).card : ℝ) ≤ 961 * 4 ^ j := by
  have hj2 := two_le_two_pow h.one_le
  obtain ⟨k₀, hk₀⟩ := h.cluster_nonempty
  have hdiam : euclideanSetDiameter s ≤ Real.sqrt 2 * 2 ^ j :=
    freeSquare_euclideanDiameter_le h.square.square
  have hsqrt : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hbox : ∀ x ∈ profileNearSet ρ j s,
      |((x : Site L).1.val : ℝ) - ((k₀.1.val : ℝ), (k₀.2.val : ℝ)).1| ≤ 15 / 4 * 2 ^ j ∧
      |((x : Site L).2.val : ℝ) - ((k₀.1.val : ℝ), (k₀.2.val : ℝ)).2| ≤ 15 / 4 * 2 ^ j := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_profileNearSet.mp hx
    have hkk₀ : euclideanSiteDistance k k₀ ≤ Real.sqrt 2 * 2 ^ j :=
      (siteDist_le_diam (cluster_subset hk).1 (cluster_subset hk₀).1).trans hdiam
    have htri := euclideanSiteDistance_triangle x k k₀
    have hx₀ : euclideanSiteDistance x k₀ ≤ 15 / 4 * 2 ^ j := by nlinarith
    exact ⟨(abs_fst_le_siteDist x k₀).trans hx₀, (abs_snd_le_siteDist x k₀).trans hx₀⟩
  have hcard := card_le_of_separated (fun x : Site L => x) (by norm_num : (0 : ℝ) < 1 / 2)
    ((k₀.1.val : ℝ), (k₀.2.val : ℝ)) hbox
    (fun x _ y _ hxy => lt_of_lt_of_le (by norm_num) (one_le_siteDist hxy))
  refine hcard.trans ?_
  have h4 : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  have hpos : (0 : ℝ) ≤ 4 * (15 / 4 * 2 ^ j) / (1 / 2) + 2 := by positivity
  nlinarith

/-- **The edge count**: at most `100·4^{j+3}` nonzero gradients. -/
theorem ProfileContext.card_grad_profilePiece_ne_zero_le (h : ProfileContext F ρ j s f)
    (hL : 1 < L) :
    ((Finset.univ.filter fun e : SquareZeroBond L =>
      (squareZero L).grad (profilePiece j f) e ≠ 0).card : ℝ) ≤ 100 * 4 ^ (j + 3) := by
  classical
  set N := profileNearSet ρ j s
  have hsub : (Finset.univ.filter fun e : SquareZeroBond L =>
      (squareZero L).grad (profilePiece j f) e ≠ 0) ⊆
      N.biUnion fun x => Finset.univ.filter fun e : SquareZeroBond L =>
        (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x := by
    intro e he
    obtain ⟨x, y, hs, -, -, hx, -⟩ := h.exists_near_of_grad_ne_zero hL (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨x, mem_profileNearSet.mpr (h.near_of_lt hx),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩⟩
  have hc : (Finset.univ.filter fun e : SquareZeroBond L =>
      (squareZero L).grad (profilePiece j f) e ≠ 0).card ≤ 4 * N.card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun x _ => card_incident_le_four x).trans (by simp [mul_comm])))
  have hcR : ((Finset.univ.filter fun e : SquareZeroBond L =>
      (squareZero L).grad (profilePiece j f) e ≠ 0).card : ℝ) ≤ 4 * N.card := by
    exact_mod_cast hc
  have hN := h.card_near_le
  have h4 : (4 : ℝ) ^ (j + 3) = 64 * 4 ^ j := by ring
  rw [h4]
  nlinarith

/-- **The energy** of one profile is at most `6400`. -/
theorem ProfileContext.energy_profilePiece_le (h : ProfileContext F ρ j s f) (hL : 1 < L) :
    (squareZero L).energy (profilePiece j f) ≤ 6400 := by
  classical
  unfold Multigraph.energy
  set G := fun e : SquareZeroBond L => (squareZero L).grad (profilePiece j f) e
  have hsplit : ∑ e, G e ^ 2 = ∑ e ∈ Finset.univ.filter (fun e => G e ≠ 0), G e ^ 2 := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun e _ => by split_ifs with he <;> simp_all
  rw [hsplit]
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hterm : ∀ e ∈ Finset.univ.filter (fun e => G e ≠ 0), G e ^ 2 ≤ (1 / 2 ^ j) ^ 2 := by
    intro e _
    have := h.abs_grad_profilePiece_le hL e
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc := h.card_grad_profilePiece_ne_zero_le hL
  have h4 : (4 : ℝ) ^ (j + 3) = 64 * (2 ^ j) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
  rw [h4] at hc
  have hsq : (1 / (2 : ℝ) ^ j) ^ 2 * (2 ^ j) ^ 2 = 1 := by field_simp
  have hnn : (0 : ℝ) ≤ (1 / 2 ^ j) ^ 2 := by positivity
  calc ((Finset.univ.filter fun e => G e ≠ 0).card : ℝ) * (1 / 2 ^ j) ^ 2
      ≤ (100 * (64 * (2 ^ j) ^ 2)) * (1 / 2 ^ j) ^ 2 := mul_le_mul_of_nonneg_right hc hnn
    _ = 6400 * ((1 / (2 : ℝ) ^ j) ^ 2 * (2 ^ j) ^ 2) := by ring
    _ = 6400 := by rw [hsq, mul_one]

/-! ### Pairing -/

/-- **The pairing** of the profile with `ϱ` is the cluster charge. -/
theorem ProfileContext.pairing_profilePiece (h : ProfileContext F ρ j s f) :
    Multigraph.pairing (profilePiece j f) (fun v => (neutralizeAtWiredRoot ρ v : ℝ)) =
      (totalCharge (chargeRestriction ρ s) : ℝ) := by
  classical
  unfold Multigraph.pairing totalCharge
  rw [Fintype.sum_option, profilePiece_none, zero_mul, zero_add]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [profilePiece_some, neutralizeAtWiredRoot_some]
  by_cases hx : x ∈ chargeSupport (chargeRestriction ρ s)
  · have hxs := (mem_chargeSupport_restriction_iff ρ s x).mp hx
    rw [h.ramp_eq_one_of_l1 hx (by rw [l1_self, Nat.cast_zero]; positivity), one_mul]
    simp [chargeRestriction, hxs.1]
  · by_cases hxρ : x ∈ chargeSupport ρ
    · have hxs : x ∉ s := fun hxs => hx ((mem_chargeSupport_restriction_iff ρ s x).mpr ⟨hxs, hxρ⟩)
      rw [h.ramp_eq_zero_of_not_near fun hn => hx (h.mem_cluster_of_near hn hxρ), zero_mul]
      simp [chargeRestriction, hxs]
    · have hρx : ρ x = 0 := by simpa [chargeSupport] using hxρ
      simp [chargeRestriction, hρx]

/-! ### Locality -/

/-- Gradients lie in `routineS`. -/
theorem ProfileContext.grad_profilePiece_mem_routineS (h : ProfileContext F ρ j s f) (hL : 1 < L)
    {e : SquareZeroBond L} (he : (squareZero L).grad (profilePiece j f) e ≠ 0) :
    e ∈ routineS (neutralizeAtWiredRoot ρ) := by
  classical
  obtain ⟨x, y, hs, -, -, hx, -⟩ := h.exists_near_of_grad_ne_zero hL he
  obtain ⟨k, hk, hxk⟩ := h.near_of_lt hx
  unfold routineS
  rw [siteRestrict_neutralize]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Or.inl hs, k, (cluster_subset hk).2, ?_⟩
  have hsize := h.square.size
  have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  have : (0 : ℝ) < 2 ^ j := by positivity
  linarith

theorem dist_le_densityDiameter {V E : Type*} [Fintype V] (G : Multigraph V E)
    {ϱ : V → ℤ} {u w : V} (hu : ϱ u ≠ 0) (hw : ϱ w ≠ 0) :
    G.toSimpleGraph.dist u w ≤ G.densityDiameter ϱ := by
  unfold Multigraph.densityDiameter
  have hu' : u ∈ Finset.univ.filter fun j => ϱ j ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
  have hw' : w ∈ Finset.univ.filter fun j => ϱ j ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
  have hp : (u, w) ∈ (Finset.univ.filter fun j => ϱ j ≠ 0) ×ˢ
      (Finset.univ.filter fun j => ϱ j ≠ 0) := Finset.mem_product.mpr ⟨hu', hw'⟩
  exact Finset.le_sup (f := fun p : V × V => G.toSimpleGraph.dist p.1 p.2) hp

/-- **Support in the density domain** about `routineCenter`. -/
theorem ProfileContext.support_profilePiece_subset (h : ProfileContext F ρ j s f) (hL : 1 < L) :
    Function.support (profilePiece j f) ⊆
      (squareZero L).densityDomain (neutralizeAtWiredRoot ρ)
        (routineCenter (neutralizeAtWiredRoot ρ)) := by
  classical
  intro v hv
  cases v with
  | none => exact absurd rfl hv
  | some x =>
  have hnear := h.near_of_ramp_ne_zero hv
  obtain ⟨k, hk, hxk⟩ := hnear
  have hkρ := (cluster_subset hk).2
  have hρ0 : ρ ≠ 0 := h.nonzero ρ h.mem
  obtain ⟨c, hc, hcen, -⟩ := routineCenter_spec hρ0
  have hG := squareZero_connected L hL
  set D := (squareZero L).densityDiameter (neutralizeAtWiredRoot ρ)
  have hkϱ : neutralizeAtWiredRoot ρ (some k) ≠ 0 := by
    simpa [chargeSupport] using hkρ
  have hcϱ : neutralizeAtWiredRoot ρ (some c) ≠ 0 := by
    simpa [chargeSupport] using hc
  have hkc := dist_le_densityDiameter (squareZero L) hkϱ hcϱ
  have hxk' : (squareZero L).toSimpleGraph.dist (some x) (some k) ≤ l1 x k := dist_some_le_l1 x k
  have hl1 : (l1 x k : ℝ) ≤ 27 / 8 * 2 ^ j := by
    have := l1_le_three_halves_siteDist x k
    linarith
  have hdepthk := h.square.depth k hk
  have h4 : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  -- the cluster sits at wired distance more than `l1 x k` from another charge of `ϱ`
  have hD : l1 x k < D := by
    by_cases hQ : totalCharge ρ = 0
    · obtain ⟨y, hy, hys⟩ : ∃ y ∈ chargeSupport ρ, y ∉ s := by
        by_contra hall
        push Not at hall
        apply h.square.charged
        have : chargeRestriction ρ s = ρ := by
          funext z
          by_cases hzs : z ∈ s
          · simp [chargeRestriction, hzs]
          · have hz0 : ρ z = 0 := by
              by_contra hz
              exact hzs (hall z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩))
            simp [chargeRestriction, hzs, hz0]
        rw [this]
        exact hQ
      have hyϱ : neutralizeAtWiredRoot ρ (some y) ≠ 0 := by simpa [chargeSupport] using hy
      have hky := dist_le_densityDiameter (squareZero L) hkϱ hyϱ
      have hmin := (min_l1_depth_le_dist hL k y).trans hky
      have hfar := h.square.far k hk y hy hys
      have hsep := two_pow_le_selectionSeparation j
      have hl1ky : euclideanSiteDistance k y ≤ l1 k y := siteDist_le_l1 k y
      have hdy : (0 : ℝ) ≤ siteBoundaryDepth y := Nat.cast_nonneg _
      have hlt : (l1 x k : ℝ) < D := by
        rcases le_total (l1 k y) (siteBoundaryDepth k + siteBoundaryDepth y) with hm | hm
        · rw [min_eq_left hm] at hmin
          have : (l1 k y : ℝ) ≤ D := by exact_mod_cast hmin
          linarith
        · rw [min_eq_right hm] at hmin
          have : ((siteBoundaryDepth k + siteBoundaryDepth y : ℕ) : ℝ) ≤ D := by exact_mod_cast hmin
          push_cast at this
          linarith
      exact_mod_cast hlt
    · have hnone : neutralizeAtWiredRoot ρ none ≠ 0 := by
        simpa [neutralizeAtWiredRoot, totalCharge] using hQ
      have hkn := dist_le_densityDiameter (squareZero L) hkϱ hnone
      rw [squareZero_distance_root_eq_siteBoundaryDepth hL] at hkn
      have hlt : (l1 x k : ℝ) < D := by
        have : (siteBoundaryDepth k : ℝ) ≤ D := by exact_mod_cast hkn
        linarith
      exact_mod_cast hlt
  show (squareZero L).toSimpleGraph.dist (some x) (routineCenter (neutralizeAtWiredRoot ρ)) < 2 * D
  rw [hcen]
  have htri := hG.dist_triangle (u := some x) (v := some k) (w := some c)
  omega

/-! ### The near lemmas -/

/-- A density close to `ρ` (closer than `M·2^{j+1}`) is smaller and `M d_Λ(σ)^α ≤ D`. -/
theorem ProfileContext.rpow_le_of_close (h : ProfileContext F ρ j s f) {σ : ChargeDensity L}
    (hσ : σ ∈ F) (hne : σ ≠ ρ) {k z : Site L} (hk : k ∈ chargeSupport ρ)
    (hz : z ∈ chargeSupport σ) {D : ℝ} (hkz : euclideanSiteDistance k z ≤ D)
    (hD : D < (chargeCoverScale : ℝ) * 2 ^ (j + 1)) :
    (chargeCoverScale : ℝ) * boundaryAdjustedSize σ ^ chargeCoverExponent ≤ D := by
  have hsep := h.separated ρ h.mem σ hσ (Ne.symm hne)
  have hdist := (setDist_le_siteDist hk hz).trans hkz
  have hρ1 := one_le_boundaryAdjustedSize (h.nonzero ρ h.mem)
  have hM : (0 : ℝ) < chargeCoverScale := by rw [chargeCoverScale_eq]; norm_num
  by_cases hle : boundaryAdjustedSize ρ ≤ boundaryAdjustedSize σ
  · exfalso
    rw [min_eq_left hle] at hsep
    have h1 := le_rpow_self hρ1 one_le_chargeCoverExponent
    have h2 := h.square.size
    have h3 : (chargeCoverScale : ℝ) * 2 ^ (j + 1) ≤
        (chargeCoverScale : ℝ) * boundaryAdjustedSize ρ ^ chargeCoverExponent :=
      mul_le_mul_of_nonneg_left (h2.trans h1) hM.le
    linarith
  · rw [min_eq_right (not_le.mp hle).le] at hsep
    linarith

/-- **A charge of `σ ≠ ρ` near the cluster makes `σ` neutral and tiny.** -/
theorem ProfileContext.mem_profileCollapseFamily_of_near_support (h : ProfileContext F ρ j s f)
    {σ : ChargeDensity L} (hσ : σ ∈ F) (hne : σ ≠ ρ) {z : Site L} (hz : z ∈ chargeSupport σ)
    (hnear : IsProfileNear ρ j s z) :
    σ ∈ profileCollapseFamily F ρ j (chargeSupport (chargeRestriction ρ s)) := by
  classical
  obtain ⟨k, hk, hzk⟩ := hnear
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hM := chargeCoverScale_eq
  have hsmall := h.rpow_le_of_close hσ hne (cluster_subset hk).2 hz (D := 9 / 4 * 2 ^ j)
    (by rw [siteDist_comm]; exact hzk) (by rw [hM, pow_succ]; linarith)
  have hσ1 := one_le_boundaryAdjustedSize (h.nonzero σ hσ)
  refine Finset.mem_filter.mpr ⟨hσ, hne, ?_, by linarith, z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  rotate_left
  · rw [profileA3NeutralNeighborhood, mem_boundaryEnergyNeighborhood_iff]
    exact ⟨z, hz, by rw [siteDist_self]; linarith⟩
  · rw [mem_boundaryEnergyNeighborhood_iff]
    exact ⟨k, hk, by rw [siteDist_comm]; exact hzk⟩
  by_contra hQ
  have h1 := depth_le_two_boundaryAdjustedSize hQ hz
  have h2 := h.depth_of_near ⟨k, hk, hzk⟩
  have h3 := le_rpow_self hσ1 one_le_chargeCoverExponent
  rw [hM] at hsmall
  nlinarith

/-- **Two profiles of distinct densities meeting at scales `j' ≤ j`**: the smaller-scale density
`σ` is in the collapse family of `ρ`, and its near set lies in `E_σ`. -/
theorem ProfileContext.mem_profileCollapseFamily_of_near_near (h : ProfileContext F ρ j s f)
    {σ : ChargeDensity L} {j' : ℕ} {s' : Finset (Site L)} {f' : Site L → ℝ}
    (h' : ProfileContext F σ j' s' f') (hne : σ ≠ ρ) (hjj : j' ≤ j) {x : Site L}
    (hx : IsProfileNear ρ j s x) (hx' : IsProfileNear σ j' s' x) :
    σ ∈ profileCollapseFamily F ρ j (chargeSupport (chargeRestriction ρ s)) ∧
      ∀ y, IsProfileNear σ j' s' y → y ∈ profileA3NeutralNeighborhood σ := by
  classical
  obtain ⟨k, hk, hxk⟩ := hx
  obtain ⟨k', hk', hxk'⟩ := hx'
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hpj : (2 : ℝ) ^ j' ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hjj
  have hM := chargeCoverScale_eq
  have hkk' : euclideanSiteDistance k k' ≤ 9 / 2 * 2 ^ j := by
    have := euclideanSiteDistance_triangle k x k'
    rw [siteDist_comm k x] at this
    linarith
  have hσ := h'.mem
  have hsmall := h.rpow_le_of_close hσ hne (cluster_subset hk).2 (cluster_subset hk').2 hkk'
    (by rw [hM, pow_succ]; linarith)
  have hsize' := h'.square.size
  have hsize'' : (2 : ℝ) ^ (j' + 1) = 2 * 2 ^ j' := by ring
  have hσ1 := one_le_boundaryAdjustedSize (h.nonzero σ hσ)
  have hE : ∀ y, IsProfileNear σ j' s' y → y ∈ profileA3NeutralNeighborhood σ := by
    intro y hy
    obtain ⟨k'', hk'', hyk''⟩ := hy
    rw [profileA3NeutralNeighborhood, mem_boundaryEnergyNeighborhood_iff]
    refine ⟨k'', (cluster_subset hk'').2, ?_⟩
    rw [siteDist_comm]
    linarith
  refine ⟨Finset.mem_filter.mpr ⟨hσ, hne, ?_, by linarith, x, Finset.mem_inter.mpr
    ⟨hE x ⟨k', hk', hxk'⟩, ?_⟩⟩, hE⟩
  · by_contra hQ
    have h1 := depth_le_two_boundaryAdjustedSize hQ (cluster_subset hk').2
    have h2 := h.depth_of_near ⟨k, hk, hxk⟩
    have h3 := depth_le_add_siteDist x k'
    have h4 := le_rpow_self hσ1 one_le_chargeCoverExponent
    rw [hM] at hsmall
    nlinarith
  · rw [mem_boundaryEnergyNeighborhood_iff]
    exact ⟨k, hk, by rw [siteDist_comm]; exact hxk⟩

end Context

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
