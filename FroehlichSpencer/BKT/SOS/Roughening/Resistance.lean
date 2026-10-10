/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Potential
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineGraph
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAGeometry
public import FroehlichSpencer.BKT.Surface.SquareZeroConnected

/-!
# The logarithmic resistance of the wired box (the dipole tilt construction: FS81 (7.23), `C(0) − C(x) ≥ c log|x|`)

FS81's shift (7.22) gains `ε² σ(β)(C(0) − C(x))`, with `C` the lattice Green function; on the
pinned box the gain is the effective resistance `R(u, v)` of `squareZero L`
(`Tilt.dipoleResistance`). It is bounded below by Nash–Williams
(`Multigraph.pairing_pointDipole_ge_log_of_levelCut_bound`) with the `ℓ^∞` shells around `u`,
capped at the boundary depth of `u` (`shellLevel`): every shell cut has at most `4 · 4(2k+1)`
edges, so

`R(u, v) ≥ (1/32) log(1 + min(‖u − v‖_∞, depth(u)))` (`log_le_dipoleResistance_squareZero`).

For `u` at distance at least `‖u − v‖_∞` from the outside this is FS81's `c log(1 + |x|)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site SquareZeroBond siteBoundaryDepth)
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer (l1 l1_freeEdge card_incident_le_four
  depth_le_one_of_root_edge)
open FroehlichSpencer.BKT.SOS.Tilt

variable {L : ℕ}

/-- The `ℓ^∞` distance of two bounded faces. -/
def linfDist (x y : Site L) : ℕ :=
  max (Int.natAbs ((x.1.val : ℤ) - y.1.val)) (Int.natAbs ((x.2.val : ℤ) - y.2.val))

theorem linfDist_comm (x y : Site L) : linfDist x y = linfDist y x := by
  unfold linfDist; omega

theorem linfDist_self (x : Site L) : linfDist x x = 0 := by
  simp [linfDist]

/-- The Nash–Williams levels around `u`: `ℓ^∞` shells capped at the boundary depth of `u`, the
wired exterior at the cap. -/
def shellLevel (u : Site L) : Option (Fin L × Fin L) → ℕ :=
  fun k => k.elim (siteBoundaryDepth u) fun x => min (linfDist x u) (siteBoundaryDepth u)

/-- The levels change by at most one along every edge of `squareZero L`. -/
theorem shellLevel_step (hL : 1 < L) (u : Site L) (e : SquareZeroBond L) :
    shellLevel u ((squareZero L).src e) ≤ shellLevel u ((squareZero L).tgt e) + 1 ∧
      shellLevel u ((squareZero L).tgt e) ≤ shellLevel u ((squareZero L).src e) + 1 := by
  cases e with
  | inl f =>
    have h1 : l1 ((squareFree L).src f) ((squareFree L).tgt f) = 1 := l1_freeEdge f
    simp only [squareZero, Sum.elim_inl, shellLevel, Option.elim]
    unfold l1 at h1
    unfold linfDist
    constructor <;> omega
  | inr b =>
    have hd := depth_le_one_of_root_edge hL (e := Sum.inr b) (x := b.1)
      (by simp only [squareZero, Sum.elim_inr]) (by simp only [squareZero, Sum.elim_inr])
    simp only [squareZero, Sum.elim_inr, shellLevel, Option.elim]
    generalize b.1 = x at hd ⊢
    obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := x
    obtain ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ := u
    simp only [siteBoundaryDepth, linfDist] at hd ⊢
    constructor <;> omega

/-- The `ℓ^∞` shell of radius `k` has at most `8k + 4` faces. -/
theorem card_shell_le (u : Site L) (k : ℕ) :
    (Finset.univ.filter fun x : Site L => linfDist x u = k).card ≤ 8 * k + 4 := by
  classical
  set T : Finset (ℤ × ℤ) := ({-(k : ℤ), (k : ℤ)} ×ˢ Finset.Icc (-(k : ℤ)) k) ∪
    (Finset.Icc (-(k : ℤ)) k ×ˢ {-(k : ℤ), (k : ℤ)}) with hT
  have hinj := Finset.card_le_card_of_injOn
    (fun x : Site L => ((x.1.val : ℤ) - u.1.val, (x.2.val : ℤ) - u.2.val))
    (s := Finset.univ.filter fun x : Site L => linfDist x u = k) (t := T)
    (fun x hx => by
      have hk := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      unfold linfDist at hk
      simp only [hT, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_product,
        Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]
      omega)
    (fun x _ y _ hxy => by
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  have hpair : ({-(k : ℤ), (k : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have hIcc : (Finset.Icc (-(k : ℤ)) k).card = 2 * k + 1 := by
    rw [Int.card_Icc]; omega
  have hTcard : T.card ≤ 8 * k + 4 := by
    calc T.card ≤ ({-(k : ℤ), (k : ℤ)} ×ˢ Finset.Icc (-(k : ℤ)) k).card +
          (Finset.Icc (-(k : ℤ)) k ×ˢ {-(k : ℤ), (k : ℤ)}).card := Finset.card_union_le _ _
      _ = ({-(k : ℤ), (k : ℤ)} : Finset ℤ).card * (2 * k + 1) +
          (2 * k + 1) * ({-(k : ℤ), (k : ℤ)} : Finset ℤ).card := by
          rw [Finset.card_product, Finset.card_product, hIcc]
      _ ≤ 2 * (2 * k + 1) + (2 * k + 1) * 2 := by
          gcongr
      _ = 8 * k + 4 := by ring
  exact hinj.trans hTcard

/-- Every shell cut of the capped levels has at most `32(k+1)` edges below the cap. -/
theorem card_levelCut_shellLevel_le (u : Site L) {k : ℕ} (hk : k < siteBoundaryDepth u) :
    (((squareZero L).levelCut (shellLevel u) k).card : ℝ) ≤ 32 * ((k + 1 : ℕ) : ℝ) := by
  classical
  set shell := Finset.univ.filter fun x : Site L => linfDist x u = k with hshell
  set inc : Site L → Finset (SquareZeroBond L) := fun x => Finset.univ.filter fun e =>
    (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x with hinc
  have hsub : (squareZero L).levelCut (shellLevel u) k ⊆ shell.biUnion inc := by
    intro e he
    simp only [Multigraph.levelCut, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [Finset.mem_biUnion]
    have hlev : ∀ z : Option (Fin L × Fin L), shellLevel u z = k →
        ∃ x : Site L, z = some x ∧ linfDist x u = k := by
      intro z hz
      cases z with
      | none => simp only [shellLevel, Option.elim] at hz; omega
      | some x =>
        refine ⟨x, rfl, ?_⟩
        simp only [shellLevel, Option.elim] at hz
        omega
    rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain ⟨x, hx, hxk⟩ := hlev _ h1
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxk⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hx⟩⟩
    · obtain ⟨x, hx, hxk⟩ := hlev _ h1
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxk⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hx⟩⟩
  have hcard : ((squareZero L).levelCut (shellLevel u) k).card ≤ 4 * (8 * k + 4) := by
    calc ((squareZero L).levelCut (shellLevel u) k).card ≤ (shell.biUnion inc).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ shell, (inc x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ shell, 4 := Finset.sum_le_sum fun x _ => card_incident_le_four x
      _ = 4 * shell.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 * (8 * k + 4) := Nat.mul_le_mul_left 4 (card_shell_le u k)
  have h : ((squareZero L).levelCut (shellLevel u) k).card ≤ 32 * (k + 1) := by omega
  exact_mod_cast h

/-- **The logarithmic resistance of the wired box**:
`R(u, v) ≥ (1/32) log(1 + min(‖u − v‖_∞, depth(u)))`. -/
theorem log_le_dipoleResistance_squareZero (hL : 1 < L) (u v : Site L) :
    (1 / 32) * Real.log (((min (linfDist u v) (siteBoundaryDepth u) + 1 : ℕ) : ℝ)) ≤
      dipoleResistance (squareZero L) (squareZero_connected L hL) (some u) (some v) := by
  classical
  set r := min (linfDist u v) (siteBoundaryDepth u) with hr
  have hp : shellLevel u (some u) = 0 := by
    simp [shellLevel, linfDist_self]
  have hrq : r ≤ shellLevel u (some v) := by
    simp only [shellLevel, Option.elim, hr, linfDist_comm v u]
    exact le_rfl
  have h := Multigraph.pairing_pointDipole_ge_log_of_levelCut_bound (squareZero L)
    (squareZero_connected L hL) (shellLevel u) (shellLevel_step hL u) hp hrq 32 (by norm_num)
    (fun k hk => card_levelCut_shellLevel_le u
      (lt_of_lt_of_le (Finset.mem_range.mp hk) (min_le_right _ _)))
  exact h

end FroehlichSpencer.BKT.SOS.Roughening

end
