/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ClockReduction
public import FroehlichSpencer.BKT.Clock.Peierls.ConfigurationField
public import FroehlichSpencer.BKT.Clock.Peierls.FieldSplittingSquare
public import FroehlichSpencer.BKT.Clock.Peierls.GenericGradient
public import FroehlichSpencer.BKT.Clock.Peierls.StraightPath
public import FroehlichSpencer.BKT.Clock.Peierls.WeightRemoval
public import FroehlichSpencer.BKT.Clock.Peierls.Removal
import Mathlib.Tactic

/-! # Finite clock contour removal

For any plaquette-saturated set of nonzero clock edges, integrate the complementary closed field
to obtain a removed clock configuration. Recording the original edge differences on the contour
makes this map injective and pays one clock energy gap per contour edge.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Rotator
open GenericGradient

/-- Configurations whose nonzero edge field is saturated on every plaquette meeting `S`. -/
noncomputable def clockContourEvent (n L : ℕ) [NeZero n] (S : Finset (RotatorInternalBond L)) :
    Finset (RotatorSpinSite L → Fin n) := by
  classical
  exact Finset.univ.filter fun σ =>
    (∀ e ∈ S, clockConfigurationField σ e ≠ 0) ∧
      squareFreePlaquetteSaturated (clockConfigurationField σ) S

def clockBoxOrigin (L : ℕ) : RotatorSpinSite L :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

/-- A closed complementary field integrates to a clock configuration with the same spin at the
origin. -/
theorem exists_clockContourRemovedConfig (n L : ℕ) (_hn : 0 < n) [NeZero n]
    (S : Finset (RotatorInternalBond L))
    (σ : RotatorSpinSite L → Fin n)
    (hsaturated : squareFreePlaquetteSaturated (clockConfigurationField σ) S) :
    ∃ σ' : RotatorSpinSite L → Fin n,
      σ' (clockBoxOrigin L) = σ (clockBoxOrigin L) ∧
        clockConfigurationField σ' =
          restrictEdgeFieldOutside S (clockConfigurationField σ) := by
  let side := L + 1
  have hsplit := squareFreePlaquetteClosed_restrict_split (clockConfigurationField σ) S
    (clockConfigurationField_closed σ) hsaturated
  obtain ⟨f, hf⟩ := squareFreeEdgeField_isGradient
    (restrictEdgeFieldOutside S (clockConfigurationField σ)) hsplit.2
  let origin : SquareFreeVertex side := clockBoxOrigin L
  let zroot := clockConfigurationZMod σ origin
  let g : SquareFreeVertex side → ZMod n := fun v => f v + (zroot - f origin)
  have hgroot : g origin = zroot := by
    simp [g]
  have hgfield : (squareFreeGraph side).grad g =
      restrictEdgeFieldOutside S (clockConfigurationField σ) := by
    funext e
    have he := hf e
    change f ((squareFreeGraph (L + 1)).src e) - f ((squareFreeGraph (L + 1)).tgt e) = _ at he
    change f ((squareFreeGraph (L + 1)).src e) + (zroot - f origin) -
        (f ((squareFreeGraph (L + 1)).tgt e) + (zroot - f origin)) = _
    calc
      _ = f ((squareFreeGraph (L + 1)).src e) - f ((squareFreeGraph (L + 1)).tgt e) := by
        abel
      _ = restrictEdgeFieldOutside S (clockConfigurationField σ) e := he
  let σ' : RotatorSpinSite L → Fin n := fun v => (ZMod.finEquiv n).symm (g v)
  have hzg : clockConfigurationZMod σ' = g := by
    funext v
    simp [clockConfigurationZMod, σ']
  refine ⟨σ', ?_, ?_⟩
  · have h := congrFun hzg origin
    apply (ZMod.finEquiv n).injective
    calc
      (ZMod.finEquiv n) (σ' origin) = g origin := h
      _ = zroot := hgroot
      _ = (ZMod.finEquiv n) (σ origin) := rfl
  · rw [clockConfigurationField, hzg]
    exact hgfield

private theorem clockContourRemovedConfig_spec (n L : ℕ) (hn : 0 < n)
    [NeZero n]
    (S : Finset (RotatorInternalBond L))
    (σ : RotatorSpinSite L → Fin n)
    (hsaturated : squareFreePlaquetteSaturated (clockConfigurationField σ) S) :
    ∃ σ' : RotatorSpinSite L → Fin n,
      σ' (clockBoxOrigin L) = σ (clockBoxOrigin L) ∧
        clockConfigurationField σ' =
          restrictEdgeFieldOutside S (clockConfigurationField σ) :=
  exists_clockContourRemovedConfig n L hn S σ hsaturated

private noncomputable def clockContourRemovedConfig (n L : ℕ) (hn : 0 < n)
    [NeZero n]
    (S : Finset (RotatorInternalBond L))
    (σ : RotatorSpinSite L → Fin n)
    (hsaturated : squareFreePlaquetteSaturated (clockConfigurationField σ) S) :
    RotatorSpinSite L → Fin n :=
  Classical.choose (clockContourRemovedConfig_spec n L hn S σ hsaturated)

private theorem clockContourRemovedConfig_root (n L : ℕ) (hn : 0 < n)
    [NeZero n]
    (S : Finset (RotatorInternalBond L)) (σ : RotatorSpinSite L → Fin n)
    (hsaturated : squareFreePlaquetteSaturated (clockConfigurationField σ) S) :
    clockContourRemovedConfig n L hn S σ hsaturated (clockBoxOrigin L) =
      σ (clockBoxOrigin L) :=
  (Classical.choose_spec (clockContourRemovedConfig_spec n L hn S σ hsaturated)).1

private theorem clockContourRemovedConfig_field (n L : ℕ) (hn : 0 < n)
    [NeZero n]
    (S : Finset (RotatorInternalBond L)) (σ : RotatorSpinSite L → Fin n)
    (hsaturated : squareFreePlaquetteSaturated (clockConfigurationField σ) S) :
    clockConfigurationField (clockContourRemovedConfig n L hn S σ hsaturated) =
      restrictEdgeFieldOutside S (clockConfigurationField σ) :=
  (Classical.choose_spec (clockContourRemovedConfig_spec n L hn S σ hsaturated)).2

private theorem finEquiv_eq_natCast_val {n : ℕ} [NeZero n] (x : Fin n) :
    (x.val : ZMod n) = ZMod.finEquiv n x := by
  have hval : (ZMod.finEquiv n x).val = x.val := by
    cases n with
    | zero => exact Fin.elim0 x
    | succ n => rfl
  rw [← hval]
  exact ZMod.natCast_zmod_val (ZMod.finEquiv n x)

private theorem clockEdgeDifference_eq_field {n L : ℕ} [NeZero n]
    (σ : RotatorSpinSite L → Fin n) (e : RotatorInternalBond L) :
    clockEdgeDifference σ e = clockConfigurationField σ e := by
  change ((σ ((squareFreeGraph (L + 1)).src e)).val : ZMod n) -
      ((σ ((squareFreeGraph (L + 1)).tgt e)).val : ZMod n) =
    ZMod.finEquiv n (σ ((squareFreeGraph (L + 1)).src e)) -
      ZMod.finEquiv n (σ ((squareFreeGraph (L + 1)).tgt e))
  rw [finEquiv_eq_natCast_val, finEquiv_eq_natCast_val]

private theorem clockContourRemovedConfig_bad_equal (n L : ℕ) (hn : 2 ≤ n)
    [NeZero n]
    (S : Finset (RotatorInternalBond L))
    (σ : RotatorSpinSite L → Fin n)
    (hsaturated : squareFreePlaquetteSaturated (clockConfigurationField σ) S)
    (e : RotatorInternalBond L)
    (he : e ∈ S) :
    (clockContourRemovedConfig n L (by omega) S σ hsaturated
      ((rotatorFreeGraph L).src e)) =
    (clockContourRemovedConfig n L (by omega) S σ hsaturated
      ((rotatorFreeGraph L).tgt e)) := by
  have hout := congrFun (clockContourRemovedConfig_field n L (by omega) S σ hsaturated) e
  simp [restrictEdgeFieldOutside, he] at hout
  have hzero : clockConfigurationField
      (clockContourRemovedConfig n L (by omega) S σ hsaturated) e = 0 := hout
  have hstates : (clockConfigurationZMod
      (clockContourRemovedConfig n L (by omega) S σ hsaturated)
        ((rotatorFreeGraph L).src e)) =
      clockConfigurationZMod
        (clockContourRemovedConfig n L (by omega) S σ hsaturated)
          ((rotatorFreeGraph L).tgt e) := by
    simpa [clockConfigurationField, Multigraph.grad, rotatorFreeGraph] using
      sub_eq_zero.mp hzero
  exact (ZMod.finEquiv n).injective hstates

/-- The removed configuration and the edge differences on `S` determine the original
configuration uniquely. -/
private theorem clockContourEncoding_injective (n L : ℕ) (hn : 2 ≤ n)
    [NeZero n]
    (S : Finset (RotatorInternalBond L))
    (A : Finset (RotatorSpinSite L → Fin n))
    (hA : ∀ σ ∈ A,
      (∀ e ∈ S, clockConfigurationField σ e ≠ 0) ∧
        squareFreePlaquetteSaturated (clockConfigurationField σ) S) :
    Function.Injective (fun σ : {σ : RotatorSpinSite L → Fin n // σ ∈ A} =>
      (clockContourRemovedConfig n L (by omega) S σ.1 (hA σ.1 σ.2).2,
        fun e : {e : RotatorInternalBond L // e ∈ S} =>
          clockConfigurationField σ.1 e.1)) := by
  intro σ τ hpair
  have hremoved := congrArg Prod.fst hpair
  have hlabel := congrArg Prod.snd hpair
  apply Subtype.ext
  funext v
  let origin := clockBoxOrigin L
  have hrootZ : clockConfigurationZMod σ.1 origin = clockConfigurationZMod τ.1 origin := by
    have hrootFin : σ.1 origin = τ.1 origin :=
      (clockContourRemovedConfig_root n L (by omega) S σ.1 (hA σ.1 σ.2).2).symm.trans
        ((congrFun hremoved origin).trans
          (clockContourRemovedConfig_root n L (by omega) S τ.1 (hA τ.1 τ.2).2))
    exact congrArg (ZMod.finEquiv n) hrootFin
  have hfield : clockConfigurationField σ.1 = clockConfigurationField τ.1 := by
    funext e
    by_cases he : e ∈ S
    · have hl := congrFun hlabel ⟨e, he⟩
      exact hl
    · have hs := congrFun (clockContourRemovedConfig_field n L (by omega) S σ.1
        (hA σ.1 σ.2).2) e
      have ht := congrFun (clockContourRemovedConfig_field n L (by omega) S τ.1
        (hA τ.1 τ.2).2) e
      have hremovedField := congrArg clockConfigurationField hremoved
      calc
        clockConfigurationField σ.1 e =
            restrictEdgeFieldOutside S (clockConfigurationField σ.1) e := by
              simp [restrictEdgeFieldOutside, he]
        _ = clockConfigurationField (clockContourRemovedConfig n L (by omega) S σ.1
              (hA σ.1 σ.2).2) e := hs.symm
        _ = clockConfigurationField (clockContourRemovedConfig n L (by omega) S τ.1
              (hA τ.1 τ.2).2) e := congrFun hremovedField e
        _ = restrictEdgeFieldOutside S (clockConfigurationField τ.1) e := ht
        _ = clockConfigurationField τ.1 e := by simp [restrictEdgeFieldOutside, he]
  have hside := L.add_one_pos
  have hv : clockConfigurationZMod σ.1 v = clockConfigurationZMod τ.1 v := by
    let i := v.1.val
    let j := v.2.val
    let x : RotatorSpinSite L := (⟨i, by omega⟩, ⟨0, by omega⟩)
    have hhσ := clockConfigurationSegmentSum_eq_endpoints σ.1 0 0 i (by omega) (by omega)
    have hhτ := clockConfigurationSegmentSum_eq_endpoints τ.1 0 0 i (by omega) (by omega)
    have vvσ := clockConfigurationVerticalSegmentSum_eq_endpoints σ.1 i 0 j (by omega) (by omega)
    have vvτ := clockConfigurationVerticalSegmentSum_eq_endpoints τ.1 i 0 j (by omega) (by omega)
    have hsum :
        squareFreeHorizontalSegmentSum (clockConfigurationField σ.1) 0 0 i +
            squareFreeVerticalSegmentSum (clockConfigurationField σ.1) i 0 j =
          squareFreeHorizontalSegmentSum (clockConfigurationField τ.1) 0 0 i +
            squareFreeVerticalSegmentSum (clockConfigurationField τ.1) i 0 j := by
      rw [hfield]
    rw [hhσ, hhτ, vvσ, vvτ] at hsum
    have hdrop : clockConfigurationZMod σ.1 origin - clockConfigurationZMod σ.1 v =
        clockConfigurationZMod τ.1 origin - clockConfigurationZMod τ.1 v := by
      simpa [origin, x, clockBoxOrigin] using hsum
    calc
      clockConfigurationZMod σ.1 v =
          clockConfigurationZMod σ.1 origin -
            (clockConfigurationZMod σ.1 origin - clockConfigurationZMod σ.1 v) := by abel
      _ = clockConfigurationZMod τ.1 origin -
            (clockConfigurationZMod τ.1 origin - clockConfigurationZMod τ.1 v) := by
              rw [hdrop, hrootZ]
      _ = clockConfigurationZMod τ.1 v := by abel
  exact (ZMod.finEquiv n).injective hv

/-- Fixed-contour Gibbs weight bound. The label uses all `n` residues, which only coarsens the
standard `n - 1` nonzero-label count and is absorbed into the low-temperature threshold. -/
theorem clockContourEvent_weight_le (n L : ℕ) (hn : 2 ≤ n) (β : ℝ) (hβ : 0 ≤ β)
    [NeZero n] (S : Finset (RotatorInternalBond L)) {k : ℕ} (hcard : S.card = k) :
    (∑ σ : {σ : RotatorSpinSite L → Fin n // σ ∈ clockContourEvent n L S},
      clockBoxWeight n L β σ.1) ≤
        ((n : ℝ) * Real.exp (-(β * clockEnergyGap n))) ^ k *
          clockBoxPartitionSum n L β := by
  classical
  let A := clockContourEvent n L S
  let Label := {e : RotatorInternalBond L // e ∈ S} → ZMod n
  have hpropsFor : ∀ σ : {σ : RotatorSpinSite L → Fin n // σ ∈ A},
      (∀ e ∈ S, clockConfigurationField σ.1 e ≠ 0) ∧
        squareFreePlaquetteSaturated (clockConfigurationField σ.1) S := by
    intro σ
    simpa [A, clockContourEvent] using σ.2
  let remove : {σ : RotatorSpinSite L → Fin n // σ ∈ A} →
      (RotatorSpinSite L → Fin n) × Label := fun σ =>
    (clockContourRemovedConfig n L (by omega) S σ.1
        (hpropsFor σ).2,
      fun e => clockConfigurationField σ.1 e.1)
  have hAevent : ∀ σ ∈ A,
      (∀ e ∈ S, clockConfigurationField σ e ≠ 0) ∧
        squareFreePlaquetteSaturated (clockConfigurationField σ) S := by
    intro σ hσ
    simpa [A, clockContourEvent] using hσ
  have hinj : Function.Injective remove := by
    intro σ τ h
    exact clockContourEncoding_injective n L hn S A hAevent h
  have hlabelCard : Fintype.card Label = n ^ k := by
    dsimp [Label]
    have hcardSub : Fintype.card {e : RotatorInternalBond L // e ∈ S} = S.card := by
      simp
    rw [Fintype.card_fun, hcardSub, hcard]
    simp [ZMod.card]
  have hlabelBound : (Fintype.card Label : ℝ) ≤ ((n + 1 : ℕ) - 1 : ℝ) ^ k := by
    rw [hlabelCard]
    have hreal : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by norm_num
    rw [hreal]
    norm_cast
  have hweight : ∀ σ : {σ : RotatorSpinSite L → Fin n // σ ∈ A},
      clockBoxWeight n L β σ.1 ≤
        Real.exp (-(β * clockEnergyGap n) * (k : ℝ)) *
          clockBoxWeight n L β (remove σ).1 := by
    intro σ
    have hprops := hAevent σ.1 (by simpa [A, clockContourEvent] using σ.2)
    have hfield := clockContourRemovedConfig_field n L (by omega) S σ.1 hprops.2
    have hbad (e : RotatorInternalBond L) (he : e ∈ S) :
        σ.1 ((rotatorFreeGraph L).src e) ≠ σ.1 ((rotatorFreeGraph L).tgt e) := by
      intro heq
      exact ((clockConfigurationField_ne_zero_iff σ.1 e).mp (hprops.1 e he)) heq
    have hequal (e : RotatorInternalBond L) (he : e ∈ S) :
        (remove σ).1 ((rotatorFreeGraph L).src e) =
          (remove σ).1 ((rotatorFreeGraph L).tgt e) :=
      clockContourRemovedConfig_bad_equal n L hn S σ.1 hprops.2 e he
    have hoff (e : RotatorInternalBond L) (he : e ∉ S) :
        clockEdgeDifference σ.1 e = clockEdgeDifference (remove σ).1 e := by
      rw [clockEdgeDifference_eq_field σ.1 e,
        clockEdgeDifference_eq_field (remove σ).1 e]
      rw [hfield]
      simp [restrictEdgeFieldOutside, he]
    have hlocal := clockBoxWeight_le_of_contour_removal n L hn β hβ S σ.1
      (remove σ).1 hbad hequal hoff
    rw [hcard] at hlocal
    exact hlocal
  have hW : ∀ σ, 0 ≤ clockBoxWeight n L β σ := fun σ =>
    (clockBoxWeight_pos n L β σ).le
  have hremoval := weightedContourRemoval (n + 1) k β (clockEnergyGap n)
    (clockBoxWeight n L β) A remove hinj hweight hW hlabelBound
  simpa [A, remove, clockBoxPartitionSum] using hremoval

end FroehlichSpencer.BKT.Clock.Peierls

end
