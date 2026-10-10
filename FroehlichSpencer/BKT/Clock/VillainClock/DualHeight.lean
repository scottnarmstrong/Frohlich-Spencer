/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.MarkedCurrentSelection
public import FroehlichSpencer.BKT.Clock.VillainClock.ModularCharge
public import FroehlichSpencer.BKT.Rotator.FreeBoxBijection
import Mathlib.Tactic

/-!
# Clock face heights and residue currents on the free square

On the free spin square `rotatorFreeGraph L` the residue currents `j : E → ℤ_N` whose divergence
vanishes modulo `N` at every site are exactly the coboundaries of clock face heights
`h : faces → ℤ_N`, with the exterior face pinned to `0`. This is the `ℤ_N` form of the integer bijection `rotatorNeutralCurrentHeightEquiv`, and it is the planar step of the
Kramers–Wannier duality of the Villain clock.

* `clockFaceCurrent hN h`: the residue current `h(src*) − h(tgt*) mod N` of a clock face height;
* `clockFaceCurrent_neutral`, `clockFaceCurrent_injective`;
* `exists_rotatorCurrent_of_sum_eq_zero`: every integer charge of total zero is the divergence of
  an integer current (row sums, then the last column);
* **`sum_neutralResidue_eq_sum_clockFaceHeight`**: summing over residue currents that are
  divergence free modulo `N` is summing over clock face heights.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain

/-! ### Residues -/

section Residue

variable {N : ℕ}

/-- The residue of an integer in `Fin N`. -/
def intResidue (hN : 0 < N) (m : ℤ) : Fin N :=
  ⟨(m % (N : ℤ)).toNat, by
    have h0 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have h1 : m % (N : ℤ) < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    omega⟩

theorem intResidue_cast (hN : 0 < N) (m : ℤ) : ((intResidue hN m : ℕ) : ℤ) = m % N := by
  have h0 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  simp only [intResidue]
  exact Int.toNat_of_nonneg h0

theorem intResidue_zmod (hN : 0 < N) (m : ℤ) :
    (((intResidue hN m : ℕ) : ℤ) : ZMod N) = (m : ZMod N) := by
  rw [intResidue_cast, ZMod.intCast_mod]

theorem intResidue_eq_of_zmod (hN : 0 < N) (m : ℤ) (a : Fin N)
    (h : (m : ZMod N) = (((a : ℕ) : ℤ) : ZMod N)) : intResidue hN m = a := by
  apply Fin.ext
  have hc := intResidue_zmod hN m
  rw [h] at hc
  have hmod := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp hc
  have h1 := (intResidue hN m).isLt
  have h2 := a.isLt
  obtain ⟨t, ht⟩ := hmod
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hlt1 : ((intResidue hN m : ℕ) : ℤ) < N := by exact_mod_cast h1
  have hlt2 : ((a : ℕ) : ℤ) < N := by exact_mod_cast h2
  have hge1 : (0 : ℤ) ≤ ((intResidue hN m : ℕ) : ℤ) := by positivity
  have hge2 : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := by positivity
  have ht0 : t = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (N : ℤ) * t ≤ -N := by nlinarith
      linarith
    · have : (N : ℤ) ≤ (N : ℤ) * t := by nlinarith
      linarith
  subst ht0
  omega

theorem zmod_fin_ext {a b : Fin N} (h : (((a : ℕ) : ℤ) : ZMod N) = (((b : ℕ) : ℤ) : ZMod N)) :
    a = b := by
  apply Fin.ext
  rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h

end Residue

/-! ### Divergences modulo `N` -/

section Divergence

variable {V E : Type*} [Fintype E] [DecidableEq V] {N : ℕ}

/-- A residue current congruent to an integer current has the congruent divergence. -/
theorem residueCurrentDivergence_zmod (G : Multigraph V E) (j : E → Fin N) (q : E → ℤ)
    (hjq : ∀ e, (((j e : ℕ) : ℤ) : ZMod N) = (q e : ZMod N)) (v : V) :
    ((residueCurrentDivergence G j v : ℤ) : ZMod N) = ((currentDivergence G q v : ℤ) : ZMod N) := by
  unfold residueCurrentDivergence currentDivergence
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs
    · simpa using hjq e
    · rfl
  · refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs
    · simpa using hjq e
    · rfl

end Divergence

/-! ### Clock face heights -/

section FaceHeight

variable {L N : ℕ}

/-- The integer lift of a clock face height, pinned to `0` on the exterior face. -/
def clockFaceLift (h : SquareFreeVertex L → Fin N) : RotatorFaceHeight L :=
  ⟨fun f => match f with
    | none => 0
    | some p => ((h p : ℕ) : ℤ), rfl⟩

/-- The residue current of a clock face height: `h(src*) − h(tgt*)` modulo `N`. -/
def clockFaceCurrent (hN : 0 < N) (h : SquareFreeVertex L → Fin N)
    (e : RotatorInternalBond L) : Fin N :=
  intResidue hN (rotatorFaceHeightCurrent (clockFaceLift h) e)

theorem clockFaceCurrent_zmod (hN : 0 < N) (h : SquareFreeVertex L → Fin N)
    (e : RotatorInternalBond L) :
    (((clockFaceCurrent hN h e : ℕ) : ℤ) : ZMod N) =
      ((rotatorFaceHeightCurrent (clockFaceLift h) e : ℤ) : ZMod N) :=
  intResidue_zmod hN _

/-- The current of a clock face height is divergence free modulo `N`. -/
theorem clockFaceCurrent_neutral (hN : 0 < N) (h : SquareFreeVertex L → Fin N)
    (v : RotatorSpinSite L) :
    (N : ℤ) ∣ residueCurrentDivergence (rotatorFreeGraph L) (clockFaceCurrent hN h) v := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
    residueCurrentDivergence_zmod (rotatorFreeGraph L) _
      (rotatorFaceHeightCurrent (clockFaceLift h)) (clockFaceCurrent_zmod hN h) v]
  have h0 := rotatorFaceHeightCurrent_neutral (clockFaceLift h) v
  change currentDivergence (rotatorFreeGraph L) _ v = 0 at h0
  rw [h0, Int.cast_zero]

/-- A clock face height is determined by its residue current. -/
theorem clockFaceCurrent_injective (hN : 0 < N) :
    Function.Injective (clockFaceCurrent (L := L) hN) := by
  intro h g heq
  have hcur : ∀ e : RotatorInternalBond L,
      ((rotatorFaceHeightCurrent (clockFaceLift h) e : ℤ) : ZMod N) =
        ((rotatorFaceHeightCurrent (clockFaceLift g) e : ℤ) : ZMod N) := by
    intro e
    rw [← clockFaceCurrent_zmod hN h e, ← clockFaceCurrent_zmod hN g e, heq]
  funext p
  rcases p with ⟨i, j⟩
  have hrow : ∀ n (hn : n < L),
      ((((h (⟨n, hn⟩, j) : ℕ) : ℤ) : ZMod N)) = ((((g (⟨n, hn⟩, j) : ℕ) : ℤ) : ZMod N)) := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hc := hcur (.inr (verticalDualEdgeData ⟨0, by omega⟩ j))
        rw [rotatorFaceHeightCurrent_vertical, rotatorFaceHeightCurrent_vertical] at hc
        have hLpos : 0 < L := by omega
        simp only [lt_self_iff_false, dite_false, hLpos, dite_true, zero_sub,
          Int.cast_neg] at hc
        simpa [clockFaceLift] using hc
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        have hc := hcur (.inr (verticalDualEdgeData ⟨n + 1, by omega⟩ j))
        rw [rotatorFaceHeightCurrent_vertical, rotatorFaceHeightCurrent_vertical] at hc
        have h1 : 0 < n + 1 := by omega
        simp only [h1, dite_true, hn, Int.cast_sub] at hc
        simp only [clockFaceLift] at hc
        have hsub : n + 1 - 1 = n := by omega
        simp only [hsub] at hc
        rw [hprev] at hc
        exact sub_right_injective hc
  exact zmod_fin_ext (hrow i.val i.isLt)

end FaceHeight

/-! ### Routing a neutral charge -/

section Routing

variable {L : ℕ}

/-- A site charge on the free square, extended by zero to all natural coordinates. -/
def chargeNat (c : RotatorSpinSite L → ℤ) (x y : ℕ) : ℤ :=
  if h : x < L + 1 ∧ y < L + 1 then c (⟨x, h.1⟩, ⟨y, h.2⟩) else 0

/-- The row prefix sum `∑_{k ≤ x} c(k, y)`. -/
def chargeRowPrefix (c : RotatorSpinSite L → ℤ) (y x : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (x + 1), chargeNat c k y

/-- The column prefix sum of the row totals, `∑_{k ≤ y} ∑_x c(x, k)`. -/
def chargeColumnPrefix (c : RotatorSpinSite L → ℤ) (y : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (y + 1), chargeRowPrefix c k L

/-- The routing current: each row carries its charge to the last column along horizontal bonds,
and the last column carries the row totals upward. -/
def routingCurrent (c : RotatorSpinSite L → ℤ) : RotatorInternalBond L → ℤ
  | .inl e => chargeRowPrefix c e.2.val e.1.1.val
  | .inr e => if e.1.val = L then chargeColumnPrefix c e.2.1.val else 0

theorem routingCurrent_horizontal (c : RotatorSpinSite L → ℤ) (i : Fin L) (j : Fin (L + 1)) :
    rotatorHorizontalCurrent (routingCurrent c) i j = chargeRowPrefix c j.val i.val := by
  simp [rotatorHorizontalCurrent, routingCurrent, horizontalDualEdgeData]

theorem routingCurrent_vertical (c : RotatorSpinSite L → ℤ) (x : Fin (L + 1)) (j : Fin L) :
    rotatorVerticalCurrent (routingCurrent c) x j =
      if x.val = L then chargeColumnPrefix c j.val else 0 := by
  unfold rotatorVerticalCurrent routingCurrent verticalDualEdgeData
  simp

theorem chargeRowPrefix_succ (c : RotatorSpinSite L → ℤ) (y x : ℕ) :
    chargeRowPrefix c y (x + 1) = chargeRowPrefix c y x + chargeNat c (x + 1) y := by
  unfold chargeRowPrefix
  rw [Finset.sum_range_succ]

theorem chargeColumnPrefix_succ (c : RotatorSpinSite L → ℤ) (y : ℕ) :
    chargeColumnPrefix c (y + 1) = chargeColumnPrefix c y + chargeRowPrefix c (y + 1) L := by
  unfold chargeColumnPrefix
  rw [Finset.sum_range_succ]

theorem chargeColumnPrefix_last (c : RotatorSpinSite L → ℤ) :
    chargeColumnPrefix c L = ∑ v, c v := by
  calc
    chargeColumnPrefix c L = ∑ k : Fin (L + 1), ∑ x : Fin (L + 1), c (x, k) := by
      unfold chargeColumnPrefix chargeRowPrefix
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [chargeNat, x.isLt, k.isLt]
    _ = ∑ v, c v := by rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **Routing.** Every integer charge of total zero on the free square is the divergence of an
integer current. -/
theorem rotatorCurrentDivergence_routingCurrent (c : RotatorSpinSite L → ℤ)
    (hc : ∑ v, c v = 0) (v : RotatorSpinSite L) :
    rotatorCurrentDivergence (routingCurrent c) v = c v := by
  rcases v with ⟨x, y⟩
  rw [rotatorCurrentDivergence_formula]
  have hxy : chargeNat c x.val y.val = c (x, y) := by simp [chargeNat, x.isLt, y.isLt]
  have hA : (if hx : x.val < L then rotatorHorizontalCurrent (routingCurrent c) ⟨x.val, hx⟩ y
      else 0) = if x.val < L then chargeRowPrefix c y.val x.val else 0 := by
    by_cases hx : x.val < L
    · simp only [hx, ↓reduceDIte, ↓reduceIte, routingCurrent_horizontal]
    · simp only [hx, ↓reduceDIte, ↓reduceIte]
  have hB : (if hy : y.val < L then rotatorVerticalCurrent (routingCurrent c) x ⟨y.val, hy⟩
      else 0) = if y.val < L ∧ x.val = L then chargeColumnPrefix c y.val else 0 := by
    by_cases hy : y.val < L
    · by_cases hx : x.val = L
      · simp only [hy, hx, ↓reduceDIte, ↓reduceIte, routingCurrent_vertical, and_self]
      · simp only [hy, hx, ↓reduceDIte, ↓reduceIte, routingCurrent_vertical, and_false]
    · simp only [hy, ↓reduceDIte, ↓reduceIte, false_and]
  have hC : (if hx : 0 < x.val then rotatorHorizontalCurrent (routingCurrent c)
      ⟨x.val - 1, by have _h := x.isLt; omega⟩ y else 0) =
        if 0 < x.val then chargeRowPrefix c y.val (x.val - 1) else 0 := by
    by_cases hx : 0 < x.val
    · simp only [hx, ↓reduceDIte, ↓reduceIte, routingCurrent_horizontal]
    · simp only [hx, ↓reduceDIte, ↓reduceIte]
  have hD : (if hy : 0 < y.val then rotatorVerticalCurrent (routingCurrent c) x
      ⟨y.val - 1, by have _h := y.isLt; omega⟩ else 0) =
        if 0 < y.val ∧ x.val = L then chargeColumnPrefix c (y.val - 1) else 0 := by
    by_cases hy : 0 < y.val
    · by_cases hx : x.val = L
      · simp only [hy, hx, ↓reduceDIte, ↓reduceIte, routingCurrent_vertical, and_self]
      · simp only [hy, hx, ↓reduceDIte, ↓reduceIte, routingCurrent_vertical, and_false]
    · simp only [hy, ↓reduceDIte, ↓reduceIte, false_and]
  rw [hA, hB, hC, hD]
  by_cases hxL : x.val < L
  · have hne : ¬ x.val = L := by omega
    simp only [hxL, hne, ↓reduceIte, and_false, add_zero, sub_zero]
    by_cases hx0 : 0 < x.val
    · simp only [hx0, ↓reduceIte]
      obtain ⟨x', hx'⟩ : ∃ x', x.val = x' + 1 := ⟨x.val - 1, by omega⟩
      rw [hx', chargeRowPrefix_succ, show x' + 1 - 1 = x' by omega]
      rw [hx'] at hxy
      rw [hxy]
      ring
    · have hx00 : x.val = 0 := by omega
      simp only [hx0, ↓reduceIte, sub_zero]
      rw [hx00]
      rw [hx00] at hxy
      simp [chargeRowPrefix, hxy]
  · have hxeq : x.val = L := by have := x.isLt; omega
    simp only [hxeq, lt_self_iff_false, ↓reduceIte, and_true, zero_add]
    by_cases hL0 : L = 0
    · -- a single site: the charge vanishes
      have hsingle : ∑ v, c v = c (x, y) := by
        rw [Fintype.sum_eq_single (x, y)]
        intro w hw
        exfalso
        apply hw
        have h1 := w.1.isLt
        have h2 := w.2.isLt
        have h3 := x.isLt
        have h4 := y.isLt
        ext <;> simp <;> omega
      rw [← hsingle, hc]
      have hy0 : y.val = 0 := by have := y.isLt; omega
      simp [hL0, hy0]
    · have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
      have hrow : chargeRowPrefix c y.val (L - 1) = chargeRowPrefix c y.val L - c (x, y) := by
        have hs := chargeRowPrefix_succ c y.val (L - 1)
        have hL1 : L - 1 + 1 = L := by omega
        rw [hL1] at hs
        have hcl : chargeNat c L y.val = c (x, y) := by
          have hxL' : x = ⟨L, by omega⟩ := Fin.ext hxeq
          rw [hxL']
          simp [chargeNat, y.isLt]
        rw [hcl] at hs
        linarith
      simp only [hLpos, ↓reduceIte, hrow]
      by_cases hyL : y.val < L
      · simp only [hyL, ↓reduceIte]
        by_cases hy0 : 0 < y.val
        · simp only [hy0, ↓reduceIte]
          obtain ⟨y', hy'⟩ : ∃ y', y.val = y' + 1 := ⟨y.val - 1, by omega⟩
          rw [hy', show y' + 1 - 1 = y' by omega, chargeColumnPrefix_succ, ← hy']
          ring
        · have hy00 : y.val = 0 := by omega
          simp only [hy00]
          simp [chargeColumnPrefix]
      · have hyeq : y.val = L := by have := y.isLt; omega
        have hy0 : 0 < y.val := by omega
        simp only [hyL, hy0, ↓reduceIte]
        have hlast := chargeColumnPrefix_last c
        rw [hc] at hlast
        have hs := chargeColumnPrefix_succ c (L - 1)
        rw [show L - 1 + 1 = L by omega, hlast] at hs
        rw [hyeq]
        linarith

/-- Every integer charge of total zero is the divergence of an integer current. -/
theorem exists_rotatorCurrent_of_sum_eq_zero (c : RotatorSpinSite L → ℤ) (hc : ∑ v, c v = 0) :
    ∃ r : RotatorInternalBond L → ℤ, ∀ v, rotatorCurrentDivergence r v = c v :=
  ⟨routingCurrent c, rotatorCurrentDivergence_routingCurrent c hc⟩

end Routing

/-! ### The bijection -/

section Bijection

variable {L N : ℕ}

theorem currentDivergence_sub_mul {V E : Type*} [Fintype E] [DecidableEq V] (G : Multigraph V E)
    (a b : E → ℤ) (m : ℤ) (v : V) :
    currentDivergence G (fun e => a e - m * b e) v =
      currentDivergence G a v - m * currentDivergence G b v := by
  unfold currentDivergence
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  have h1 : ∀ e, (if G.src e = v then a e - m * b e else 0) =
      (if G.src e = v then a e else 0) - m * (if G.src e = v then b e else 0) := by
    intro e
    split_ifs <;> ring
  have h2 : ∀ e, (if G.tgt e = v then a e - m * b e else 0) =
      (if G.tgt e = v then a e else 0) - m * (if G.tgt e = v then b e else 0) := by
    intro e
    split_ifs <;> ring
  simp only [h1, h2, Finset.sum_sub_distrib]
  ring

/-- **Surjectivity.** Every residue current that is divergence free modulo `N` is the current of a
clock face height. -/
theorem exists_clockFaceCurrent_eq (hN : 0 < N) (j : RotatorInternalBond L → Fin N)
    (hj : ∀ v, (N : ℤ) ∣ residueCurrentDivergence (rotatorFreeGraph L) j v) :
    ∃ h : SquareFreeVertex L → Fin N, clockFaceCurrent hN h = j := by
  classical
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  let q₀ : RotatorInternalBond L → ℤ := fun e => ((j e : ℕ) : ℤ)
  let c : RotatorSpinSite L → ℤ := fun v => residueCurrentDivergence (rotatorFreeGraph L) j v / N
  have hc : ∀ v, residueCurrentDivergence (rotatorFreeGraph L) j v = N * c v := fun v =>
    (Int.mul_ediv_cancel' (hj v)).symm
  have hcsum : ∑ v, c v = 0 := by
    have h0 := sum_residueCurrentDivergence_eq_zero (rotatorFreeGraph L) j
    simp only [hc, ← Finset.mul_sum] at h0
    exact (mul_eq_zero.mp h0).resolve_left hNz
  obtain ⟨r, hr⟩ := exists_rotatorCurrent_of_sum_eq_zero c hcsum
  let q : RotatorInternalBond L → ℤ := fun e => q₀ e - N * r e
  have hq : ∀ v, rotatorCurrentDivergence q v = 0 := by
    intro v
    change currentDivergence (rotatorFreeGraph L) (fun e => q₀ e - N * r e) v = 0
    rw [currentDivergence_sub_mul]
    have h1 : currentDivergence (rotatorFreeGraph L) q₀ v =
        residueCurrentDivergence (rotatorFreeGraph L) j v := rfl
    have h2 : currentDivergence (rotatorFreeGraph L) r v = c v := hr v
    rw [h1, h2, hc v]
    ring
  let H := rotatorHeightFromCurrent q
  have hH : rotatorFaceHeightCurrent H = q := rotatorHeightFromCurrent_current q hq
  refine ⟨fun p => intResidue hN (H.1 (some p)), ?_⟩
  funext e
  apply intResidue_eq_of_zmod
  have hlift : ∀ f, ((((clockFaceLift fun p => intResidue hN (H.1 (some p))).1 f : ℤ)) :
      ZMod N) = ((H.1 f : ℤ) : ZMod N) := by
    intro f
    cases f with
    | none => simp [clockFaceLift, H.2]
    | some p => exact intResidue_zmod hN _
  change (((clockFaceLift fun p => intResidue hN (H.1 (some p))).1
      ((rotatorDualGraph L).src e) - (clockFaceLift fun p => intResidue hN (H.1 (some p))).1
        ((rotatorDualGraph L).tgt e) : ℤ) : ZMod N) = _
  push_cast
  rw [hlift, hlift]
  have hqe : H.1 ((rotatorDualGraph L).src e) - H.1 ((rotatorDualGraph L).tgt e) = q e :=
    congrFun hH e
  have hcast : (((H.1 ((rotatorDualGraph L).src e) : ℤ) : ZMod N) -
      ((H.1 ((rotatorDualGraph L).tgt e) : ℤ) : ZMod N)) = ((q e : ℤ) : ZMod N) := by
    rw [← hqe]
    push_cast
    ring
  rw [hcast]
  simp only [q, q₀]
  push_cast
  simp

/-- **The current/height correspondence.** Summing over residue currents that are divergence free
modulo `N` is summing over clock face heights. -/
theorem sum_neutralResidue_eq_sum_clockFaceHeight {M : Type*} [AddCommMonoid M] (hN : 0 < N)
    (F : (RotatorInternalBond L → Fin N) → M) :
    (∑ j : RotatorInternalBond L → Fin N,
        if ∀ v, (N : ℤ) ∣ residueCurrentDivergence (rotatorFreeGraph L) j v then F j else 0) =
      ∑ h : SquareFreeVertex L → Fin N, F (clockFaceCurrent hN h) := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image (f := F) (s := Finset.univ)
    (fun a _ b _ hab => clockFaceCurrent_injective hN hab)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hj
    exact exists_clockFaceCurrent_eq hN j hj
  · rintro ⟨h, rfl⟩
    exact clockFaceCurrent_neutral hN h

end Bijection

end FroehlichSpencer.BKT.Clock.VillainClock

end
