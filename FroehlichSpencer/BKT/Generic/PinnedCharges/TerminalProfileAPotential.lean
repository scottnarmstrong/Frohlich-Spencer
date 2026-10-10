/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAAssembly

/-!
# The collapsed lattice distance: the existence half of the support control

It is
truncated at `T = 2^{j+1}`, the only range the ramp reads.

* `profileLattice`: the nearest-neighbour lattice (`l1 = 1`) on the sites;
* `collapsedCost 𝓔 w`: the paid steps of a lattice walk `w` (`IsCollapsedStep`);
* `collapsedDistance 𝓔 K T x = min(T, min_w collapsedCost 𝓔 w)` over walks from `K` to `x`.

Its properties: `= 0` on `K`, 1-Lipschitz on lattice steps, constant across free steps, `≤` the
cost of every walk from `K`, and below `T` it is attained by a walk (`exists_walk_of_lt`).

With
`𝓔` the neighbourhoods of `profileCollapseFamily`, `profileCollapsedPotential` satisfies the
`zero`, `lipschitz` and `collapse` clauses of `IsProfilePotential`
(`isProfilePotential_of_supportControl`).

So the input of part (A) reduces to the support clause
for this one potential:

* `TerminalCollapsedSupportControl`: the terminal decomposition's `ProfileA3CollapsedSupportControl` for
  `profileCollapsedPotential` on every charged selected square of every comb terminal;
* `terminalSupportControl_of_collapsed`, `theoremC_of_collapsedSupportControl`,
  `exists_transition_of_collapsedSupportControl`;
* `TerminalCollapsedSupportControlLarge`, the same clause at scales `j ≥ 14` only, suffices
  (`terminalCollapsedSupportControl_of_large`).

When the collapse family is empty (in particular at every scale `j ≤ 13`, since
`M = 2^16 > 5·2^13`), the support control holds outright: the distance is then the truncated lattice
distance, which dominates the Euclidean one (`collapsedSupportControl_of_family_eq_empty`,
`profileCollapseFamily_eq_empty_of_le_thirteen`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open Filter
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-! ## The collapsed lattice distance -/

/-- The nearest-neighbour lattice on the sites: steps of `ℓ¹` length one. -/
def profileLattice (L : ℕ) : SimpleGraph (Site L) where
  Adj x y := l1 x y = 1
  symm := ⟨fun _ _ h => by rwa [l1_comm]⟩
  loopless := ⟨fun x h => by rw [l1_self] at h; exact absurd h (by norm_num)⟩

theorem profileLattice_adj {x y : Site L} : (profileLattice L).Adj x y ↔ l1 x y = 1 := Iff.rfl

/-- A step is free when both of its ends lie in one collapsed set. -/
def IsCollapsedStep (𝓔 : Finset (Finset (Site L))) (x y : Site L) : Prop :=
  ∃ E ∈ 𝓔, x ∈ E ∧ y ∈ E

instance (𝓔 : Finset (Finset (Site L))) (x y : Site L) : Decidable (IsCollapsedStep 𝓔 x y) := by
  unfold IsCollapsedStep
  infer_instance

/-- The paid length of a lattice walk: the number of its steps that are not free. -/
def collapsedCost (𝓔 : Finset (Finset (Site L))) {x y : Site L}
    (w : (profileLattice L).Walk x y) : ℕ :=
  w.darts.countP fun d => ¬ IsCollapsedStep 𝓔 d.fst d.snd

theorem collapsedCost_nil (𝓔 : Finset (Finset (Site L))) (x : Site L) :
    collapsedCost 𝓔 (SimpleGraph.Walk.nil : (profileLattice L).Walk x x) = 0 := by
  simp [collapsedCost]

/-- Appending a step adds one paid step, or none if the step is free. -/
theorem collapsedCost_concat (𝓔 : Finset (Finset (Site L))) {x y z : Site L}
    (w : (profileLattice L).Walk x y) (h : (profileLattice L).Adj y z) :
    collapsedCost 𝓔 (w.concat h) =
      collapsedCost 𝓔 w + if IsCollapsedStep 𝓔 y z then 0 else 1 := by
  unfold collapsedCost
  rw [SimpleGraph.Walk.darts_concat, List.concat_eq_append, List.countP_append]
  by_cases hf : IsCollapsedStep 𝓔 y z <;> simp [hf]

/-- The paid length is at most the length. -/
theorem collapsedCost_le_length (𝓔 : Finset (Finset (Site L))) {x y : Site L}
    (w : (profileLattice L).Walk x y) : collapsedCost 𝓔 w ≤ w.length := by
  unfold collapsedCost
  rw [← SimpleGraph.Walk.length_darts]
  exact List.countP_le_length

/-- The costs of the walks from `K` to `x`, together with the truncation level `T`. -/
def collapsedCostSet (𝓔 : Finset (Finset (Site L))) (K : Finset (Site L)) (T : ℕ) (x : Site L) :
    Set ℕ :=
  insert T {c | ∃ k ∈ K, ∃ w : (profileLattice L).Walk k x, collapsedCost 𝓔 w = c}

/-- **The collapsed lattice distance** from `K`, truncated at `T`. -/
def collapsedDistance (𝓔 : Finset (Finset (Site L))) (K : Finset (Site L)) (T : ℕ)
    (x : Site L) : ℕ :=
  sInf (collapsedCostSet 𝓔 K T x)

section Distance

variable {𝓔 : Finset (Finset (Site L))} {K : Finset (Site L)} {T : ℕ}

theorem collapsedDistance_le_trunc (x : Site L) : collapsedDistance 𝓔 K T x ≤ T :=
  Nat.sInf_le (Set.mem_insert _ _)

/-- The distance is at most the paid length of any walk from `K`. -/
theorem collapsedDistance_le_cost {k x : Site L} (hk : k ∈ K) (w : (profileLattice L).Walk k x) :
    collapsedDistance 𝓔 K T x ≤ collapsedCost 𝓔 w :=
  Nat.sInf_le (Set.mem_insert_of_mem _ ⟨k, hk, w, rfl⟩)

theorem collapsedDistance_eq_zero {x : Site L} (hx : x ∈ K) : collapsedDistance 𝓔 K T x = 0 :=
  Nat.eq_zero_of_le_zero ((collapsedDistance_le_cost hx SimpleGraph.Walk.nil).trans_eq
    (collapsedCost_nil 𝓔 x))

/-- **Below the truncation the distance is attained** by a walk from `K`. -/
theorem exists_walk_of_lt {x : Site L} (hx : collapsedDistance 𝓔 K T x < T) :
    ∃ k ∈ K, ∃ w : (profileLattice L).Walk k x, collapsedCost 𝓔 w = collapsedDistance 𝓔 K T x := by
  have hmem : collapsedDistance 𝓔 K T x ∈ collapsedCostSet 𝓔 K T x :=
    Nat.sInf_mem ⟨T, Set.mem_insert _ _⟩
  rcases (Set.mem_insert_iff.mp hmem) with h | h
  · exact absurd h hx.ne
  · exact h

/-- Extending an optimal walk by one step. -/
theorem collapsedDistance_le_of_step {x y : Site L} (h : (profileLattice L).Adj x y) :
    collapsedDistance 𝓔 K T y ≤
      collapsedDistance 𝓔 K T x + if IsCollapsedStep 𝓔 x y then 0 else 1 := by
  by_cases hlt : collapsedDistance 𝓔 K T x < T
  · obtain ⟨k, hk, w, hw⟩ := exists_walk_of_lt hlt
    have := collapsedDistance_le_cost (𝓔 := 𝓔) (T := T) hk (w.concat h)
    rw [collapsedCost_concat, hw] at this
    exact this
  · have h1 := collapsedDistance_le_trunc (𝓔 := 𝓔) (K := K) (T := T) y
    have h2 : T ≤ collapsedDistance 𝓔 K T x := not_lt.mp hlt
    omega

/-- **Lipschitz**: one lattice step changes the distance by at most one. -/
theorem collapsedDistance_le_add_one {x y : Site L} (h : l1 x y = 1) :
    collapsedDistance 𝓔 K T y ≤ collapsedDistance 𝓔 K T x + 1 := by
  have := collapsedDistance_le_of_step (𝓔 := 𝓔) (K := K) (T := T) (profileLattice_adj.mpr h)
  split_ifs at this <;> omega

/-- **Collapse**: a free step does not change the distance. -/
theorem collapsedDistance_eq_of_collapsed {x y : Site L} (h : l1 x y = 1)
    (hc : IsCollapsedStep 𝓔 x y) : collapsedDistance 𝓔 K T x = collapsedDistance 𝓔 K T y := by
  have h1 := collapsedDistance_le_of_step (𝓔 := 𝓔) (K := K) (T := T) (profileLattice_adj.mpr h)
  have hc' : IsCollapsedStep 𝓔 y x := by
    obtain ⟨E, hE, hx, hy⟩ := hc
    exact ⟨E, hE, hy, hx⟩
  have h2 := collapsedDistance_le_of_step (𝓔 := 𝓔) (K := K) (T := T)
    (profileLattice_adj.mpr (by rw [l1_comm]; exact h))
  simp only [hc, hc', ↓reduceIte, add_zero] at h1 h2
  omega

/-- A lattice walk moves at most one `ℓ¹` unit per step. -/
theorem l1_le_walk_length {x y : Site L} (w : (profileLattice L).Walk x y) :
    l1 x y ≤ w.length := by
  induction w with
  | nil => simp [l1_self]
  | cons h p ih =>
    rename_i a b c
    have h1 : l1 a b = 1 := h
    have := l1_triangle a b c
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **With nothing collapsed**, the support control holds: the distance is the truncated lattice
distance, which dominates the Euclidean distance. -/
theorem collapsedSupportControl_of_empty (j : ℕ) (K : Finset (Site L)) :
    ProfileA3CollapsedSupportControl j K
      (fun x => (collapsedDistance (∅ : Finset (Finset (Site L))) K (2 ^ (j + 1)) x : ℝ)) := by
  intro x hx
  have hx' : ((collapsedDistance (∅ : Finset (Finset (Site L))) K (2 ^ (j + 1)) x : ℕ) : ℝ) <
      ((2 ^ (j + 1) : ℕ) : ℝ) := by push_cast; exact hx
  have hlt : collapsedDistance (∅ : Finset (Finset (Site L))) K (2 ^ (j + 1)) x < 2 ^ (j + 1) := by
    exact_mod_cast hx'
  show euclideanSetDistance K {x} ≤
    9 / 8 * ((collapsedDistance (∅ : Finset (Finset (Site L))) K (2 ^ (j + 1)) x : ℕ) : ℝ)
  obtain ⟨k, hk, w, hw⟩ := exists_walk_of_lt hlt
  have hcost : collapsedCost (∅ : Finset (Finset (Site L))) w = w.length := by
    unfold collapsedCost
    rw [← SimpleGraph.Walk.length_darts]
    exact List.countP_eq_length.mpr fun d _ => by simp [IsCollapsedStep]
  have h1 := setDist_le_siteDist hk (Finset.mem_singleton_self x)
  have h2 := siteDist_le_l1 k x
  have h3 : (l1 k x : ℝ) ≤ w.length := by exact_mod_cast l1_le_walk_length w
  rw [← hw, hcost]
  have h4 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  linarith

end Distance

/-! ## The profile potential -/

/-- The collapsed sets of the scale-`j` profile of `ρ` with cluster `K`. -/
def profileCollapsedSets (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K : Finset (Site L)) : Finset (Finset (Site L)) :=
  (profileCollapseFamily F ρ j K).image profileA3NeutralNeighborhood

/-- **The profile potential**: the collapsed lattice distance from `K`, truncated at `2^{j+1}`. -/
def profileCollapsedPotential (F : Finset (ChargeDensity L)) (ρ : ChargeDensity L) (j : ℕ)
    (K : Finset (Site L)) (x : Site L) : ℝ :=
  (collapsedDistance (profileCollapsedSets F ρ j K) K (2 ^ (j + 1)) x : ℝ)

/-- **The existence half**: the collapsed potential has the `zero`, `lipschitz` and `collapse`
clauses, so it is a profile potential as soon as it has the support clause. -/
theorem isProfilePotential_of_supportControl {F : Finset (ChargeDensity L)} {ρ : ChargeDensity L}
    {j : ℕ} {K : Finset (Site L)}
    (h : ProfileA3CollapsedSupportControl j K (profileCollapsedPotential F ρ j K)) :
    IsProfilePotential F ρ j K (profileCollapsedPotential F ρ j K) where
  zero x hx := by
    unfold profileCollapsedPotential
    rw [collapsedDistance_eq_zero hx, Nat.cast_zero]
  lipschitz x y hxy := by
    unfold profileCollapsedPotential
    have := collapsedDistance_le_add_one (𝓔 := profileCollapsedSets F ρ j K) (K := K)
      (T := 2 ^ (j + 1)) (by rw [l1_comm]; exact hxy)
    exact_mod_cast this
  collapse σ hσ x hx y hy hxy := by
    unfold profileCollapsedPotential
    have hc : IsCollapsedStep (profileCollapsedSets F ρ j K) x y :=
      ⟨profileA3NeutralNeighborhood σ, Finset.mem_image_of_mem _ hσ, hx, hy⟩
    rw [collapsedDistance_eq_of_collapsed (K := K) (T := 2 ^ (j + 1)) hxy hc]
  support := h

/-- With an empty collapse family the support clause holds outright. -/
theorem collapsedSupportControl_of_family_eq_empty {F : Finset (ChargeDensity L)}
    {ρ : ChargeDensity L} {j : ℕ} {K : Finset (Site L)}
    (h : profileCollapseFamily F ρ j K = ∅) :
    ProfileA3CollapsedSupportControl j K (profileCollapsedPotential F ρ j K) := by
  unfold profileCollapsedPotential profileCollapsedSets
  rw [h, Finset.image_empty]
  exact collapsedSupportControl_of_empty j K

/-- At scales `j ≤ 13` nothing is collapsed (`M = 2^16 > 5·2^13`). -/
theorem profileCollapseFamily_eq_empty_of_le_thirteen {F : Finset (ChargeDensity L)}
    (hF : ∀ σ ∈ F, σ ≠ 0) (ρ : ChargeDensity L) {j : ℕ} (hj : j ≤ 13) (K : Finset (Site L)) :
    profileCollapseFamily F ρ j K = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro σ hσ
  unfold profileCollapseFamily at hσ
  obtain ⟨hσF, -, -, hsmall, -⟩ := Finset.mem_filter.mp hσ
  have h1 := one_le_boundaryAdjustedSize (hF σ hσF)
  have h2 := le_rpow_self h1 one_le_chargeCoverExponent
  have h3 : (2 : ℝ) ^ j ≤ 2 ^ 13 := pow_le_pow_right₀ (by norm_num) hj
  rw [chargeCoverScale_eq] at hsmall
  nlinarith

/-! ## The reduced input -/

/-- **The remaining input of part (A)**: the terminal decomposition's support clause for the collapsed potential, on every
charged selected square of every comb terminal. -/
def TerminalCollapsedSupportControl : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T → ∀ ρ ∈ T.F,
    ∀ j ∈ Finset.Icc 1 (layerCutoff (neutralizeAtWiredRoot ρ)),
    ∀ s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j,
      totalCharge (chargeRestriction ρ s) ≠ 0 →
        ProfileA3CollapsedSupportControl j (chargeSupport (chargeRestriction ρ s))
          (profileCollapsedPotential T.F ρ j (chargeSupport (chargeRestriction ρ s)))

/-- The same clause at the scales `j ≥ 14` only, where something can be collapsed. -/
def TerminalCollapsedSupportControlLarge : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T → ∀ ρ ∈ T.F,
    ∀ j ∈ Finset.Icc 14 (layerCutoff (neutralizeAtWiredRoot ρ)),
    ∀ s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j,
      totalCharge (chargeRestriction ρ s) ≠ 0 →
        ProfileA3CollapsedSupportControl j (chargeSupport (chargeRestriction ρ s))
          (profileCollapsedPotential T.F ρ j (chargeSupport (chargeRestriction ρ s)))

/-- The scales `j ≤ 13` are free: there the collapse family is empty. -/
theorem terminalCollapsedSupportControl_of_large (h : TerminalCollapsedSupportControlLarge) :
    TerminalCollapsedSupportControl := by
  intro L N T hT ρ hρ j hj s hs hq
  by_cases hj14 : 14 ≤ j
  · exact h L N T hT ρ hρ j (Finset.mem_Icc.mpr ⟨hj14, (Finset.mem_Icc.mp hj).2⟩) s hs hq
  · exact collapsedSupportControl_of_family_eq_empty
      (profileCollapseFamily_eq_empty_of_le_thirteen hT.geometry.ensemble.1 ρ (by omega) _)

/-- **The existence half of `TerminalSupportControl`**: the collapsed potential is a profile
potential once it has the support clause. -/
theorem terminalSupportControl_of_collapsed (h : TerminalCollapsedSupportControl) :
    TerminalSupportControl :=
  fun L N T hT ρ hρ j hj s hs hq =>
    ⟨_, isProfilePotential_of_supportControl (h L N T hT ρ hρ j hj s hs hq)⟩

/-- **FS81 Theorem C, conditional only on the support clause of the collapsed potential.** -/
theorem theoremC_of_collapsedSupportControl (h : TerminalCollapsedSupportControl) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_supportControl (terminalSupportControl_of_collapsed h)

/-- **The Kosterlitz–Thouless transition, conditional only on the same clause.** -/
theorem exists_transition_of_collapsedSupportControl (h : TerminalCollapsedSupportControl) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_supportControl (terminalSupportControl_of_collapsed h)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
