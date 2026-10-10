/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Potential.NashWilliams
public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import FroehlichSpencer.BKT.Lattice2D.Torus
public import Mathlib.Data.Nat.Dist

/-!
# Logarithmic Green lower bounds on square graphs

This module specializes the finite-graph Nash–Williams estimate to the free
square and periodic square carriers.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Lattice2D

open Multigraph

theorem card_productRadiusShell_le_four {A B : Type*} [Fintype A] [Fintype B]
    (dA : A → ℕ) (dB : B → ℕ) (signA : A → Bool) (signB : B → Bool)
    (hinjA : ∀ x y, dA x = dA y → signA x = signA y → x = y)
    (hinjB : ∀ x y, dB x = dB y → signB x = signB y → x = y)
    (k : ℕ) :
    (Finset.univ.filter (fun x : A × B => dA x.1 + dB x.2 = k)).card ≤ 4 * (k + 1) := by
  classical
  let shell : Finset (A × B) :=
    Finset.univ.filter (fun x => dA x.1 + dB x.2 = k)
  let code : ↥shell → Fin (k + 1) × Bool × Bool := fun x =>
    (⟨dA x.1.1, by
      have hx := (Finset.mem_filter.mp x.2).2
      omega⟩, signA x.1.1, signB x.1.2)
  have hinj : Function.Injective code := by
    intro x y hxy
    have hfirst := congrArg Prod.fst hxy
    have hsigns := congrArg Prod.snd hxy
    have hda : dA x.1.1 = dA y.1.1 := congrArg Fin.val hfirst
    have hsa : signA x.1.1 = signA y.1.1 := congrArg Prod.fst hsigns
    have hsb : signB x.1.2 = signB y.1.2 := congrArg Prod.snd hsigns
    have hx := (Finset.mem_filter.mp x.2).2
    have hy := (Finset.mem_filter.mp y.2).2
    have hdb : dB x.1.2 = dB y.1.2 := by omega
    have h₁ : x.1.1 = y.1.1 := hinjA _ _ hda hsa
    have h₂ : x.1.2 = y.1.2 := hinjB _ _ hdb hsb
    apply Subtype.ext
    exact Prod.ext h₁ h₂
  have hcard := Fintype.card_le_of_injective code hinj
  have hnum : Fintype.card (Fin (k + 1) × Bool × Bool) = 4 * (k + 1) := by
    simp [Fintype.card_prod]
    omega
  have hcard' : shell.card ≤ 4 * (k + 1) := by
    simpa only [Fintype.card_coe, hnum] using hcard
  change shell.card ≤ 4 * (k + 1)
  exact hcard'

theorem fin_dist_sign_injective {L : ℕ} (p : Fin L) :
    ∀ x y : Fin L, Nat.dist p.val x.val = Nat.dist p.val y.val →
      decide (p.val ≤ x.val) = decide (p.val ≤ y.val) → x = y := by
  intro x y hdist hsign
  apply Fin.ext
  by_cases hx : p.val ≤ x.val
  · by_cases hy : p.val ≤ y.val
    · have h := hdist
      simp [Nat.dist] at h
      omega
    · simp [hx, hy] at hsign
  · by_cases hy : p.val ≤ y.val
    · simp [hx, hy] at hsign
    · have h := hdist
      simp [Nat.dist] at h
      omega

def freeRadius {L : ℕ} (p x : SquareFreeVertex L) : ℕ :=
  Nat.dist p.1.val x.1.val + Nat.dist p.2.val x.2.val

theorem freeRadius_shell_card_le {L : ℕ} (p : SquareFreeVertex L) (k : ℕ) :
    (Finset.univ.filter (fun x : SquareFreeVertex L => freeRadius p x = k)).card ≤
      4 * (k + 1) := by
  change (Finset.univ.filter (fun x : Fin L × Fin L =>
    Nat.dist p.1.val x.1.val + Nat.dist p.2.val x.2.val = k)).card ≤ 4 * (k + 1)
  exact card_productRadiusShell_le_four
    (fun x : Fin L => Nat.dist p.1.val x.val)
    (fun x : Fin L => Nat.dist p.2.val x.val)
    (fun x : Fin L => decide (p.1.val ≤ x.val))
    (fun x : Fin L => decide (p.2.val ≤ x.val))
    (fin_dist_sign_injective p.1) (fin_dist_sign_injective p.2) k

theorem natDist_succ_le (a n : ℕ) :
    Nat.dist a (n + 1) ≤ Nat.dist a n + 1 ∧
      Nat.dist a n ≤ Nat.dist a (n + 1) + 1 := by
  constructor <;> simp [Nat.dist] <;> omega

theorem freeRadius_edge_step {L : ℕ} (p : SquareFreeVertex L) (e : SquareFreeEdge L) :
    freeRadius p ((squareFreeGraph L).src e) ≤
        freeRadius p ((squareFreeGraph L).tgt e) + 1 ∧
      freeRadius p ((squareFreeGraph L).tgt e) ≤
        freeRadius p ((squareFreeGraph L).src e) + 1 := by
  cases e with
  | inl e =>
      rcases e with ⟨i, j⟩
      have hi := natDist_succ_le p.1.val i.val
      simpa [freeRadius, squareFreeGraph, Nat.dist] using
        (show Nat.dist p.1.val i.val + Nat.dist p.2.val j.val ≤
            Nat.dist p.1.val (i.val + 1) + Nat.dist p.2.val j.val + 1 ∧
          Nat.dist p.1.val (i.val + 1) + Nat.dist p.2.val j.val ≤
            Nat.dist p.1.val i.val + Nat.dist p.2.val j.val + 1 from by omega)
  | inr e =>
      rcases e with ⟨i, j⟩
      have hj := natDist_succ_le p.2.val j.val
      simpa [freeRadius, squareFreeGraph, Nat.dist] using
        (show Nat.dist p.1.val i.val + Nat.dist p.2.val j.val ≤
            Nat.dist p.1.val i.val + Nat.dist p.2.val (j.val + 1) + 1 ∧
          Nat.dist p.1.val i.val + Nat.dist p.2.val (j.val + 1) ≤
            Nat.dist p.1.val i.val + Nat.dist p.2.val j.val + 1 from by omega)

def squareFreeEdgeSourceDirection {L : ℕ} (e : SquareFreeEdge L) :
    SquareFreeVertex L × Bool :=
  match e with
  | .inl e => ((e.1.1, e.2), false)
  | .inr e => ((e.1, e.2.1), true)

theorem squareFreeEdgeSourceDirection_injective {L : ℕ} :
    Function.Injective (@squareFreeEdgeSourceDirection L) := by
  intro e e' h
  cases e with
  | inl e =>
      cases e' with
      | inl e' =>
          have hs : (e.1.1, e.2) = (e'.1.1, e'.2) := congrArg Prod.fst h
          have h₁ : e.1 = e'.1 := Subtype.ext
            (congrArg (fun z : SquareFreeVertex L => z.1) hs)
          have h₂ : e.2 = e'.2 :=
            congrArg (fun z : SquareFreeVertex L => z.2) hs
          exact congrArg Sum.inl (Prod.ext h₁ h₂)
      | inr e' =>
          have hb : false = true := congrArg Prod.snd h
          cases hb
  | inr e =>
      cases e' with
      | inl e' =>
          have hb : true = false := congrArg Prod.snd h
          cases hb
      | inr e' =>
          have hs : (e.1, e.2.1) = (e'.1, e'.2.1) := congrArg Prod.fst h
          have h₁ : e.1 = e'.1 :=
            congrArg (fun z : SquareFreeVertex L => z.1) hs
          have h₂ : e.2 = e'.2 := Subtype.ext
            (congrArg (fun z : SquareFreeVertex L => z.2) hs)
          exact congrArg Sum.inr (Prod.ext h₁ h₂)

theorem squareFree_levelCut_card_le {L : ℕ} (p : SquareFreeVertex L) (k : ℕ) :
    ((squareFreeGraph L).levelCut (freeRadius p) k).card ≤ 24 * (k + 1) := by
  classical
  let shell₀ : Finset (SquareFreeVertex L) :=
    Finset.univ.filter fun x => freeRadius p x = k
  let shell₁ : Finset (SquareFreeVertex L) :=
    Finset.univ.filter fun x => freeRadius p x = k + 1
  let srcShell : Finset (SquareFreeVertex L) := shell₀ ∪ shell₁
  have hcutSrc : ∀ e ∈ (squareFreeGraph L).levelCut (freeRadius p) k,
      ((squareFreeEdgeSourceDirection e).1 ∈ srcShell) := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with h | h
    · have hs := h.1
      have hsrc : (squareFreeEdgeSourceDirection e).1 =
          (squareFreeGraph L).src e := by cases e <;> rfl
      rw [hsrc]
      change (squareFreeGraph L).src e ∈ shell₀ ∪ shell₁
      rw [Finset.mem_union]
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    · have hs := h.2
      have hsrc : (squareFreeEdgeSourceDirection e).1 =
          (squareFreeGraph L).src e := by cases e <;> rfl
      rw [hsrc]
      change (squareFreeGraph L).src e ∈ shell₀ ∪ shell₁
      rw [Finset.mem_union]
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  let encode : {e // e ∈ (squareFreeGraph L).levelCut (freeRadius p) k} →
      ↥srcShell × Bool := fun e =>
        (⟨(squareFreeEdgeSourceDirection e.1).1, hcutSrc e.1 e.2⟩,
          (squareFreeEdgeSourceDirection e.1).2)
  have hencode : Function.Injective encode := by
    intro e e' h
    apply Subtype.ext
    apply squareFreeEdgeSourceDirection_injective
    exact Prod.ext
      (congrArg (fun z : ↥srcShell × Bool => z.1.1) h)
      (congrArg (fun z : ↥srcShell × Bool => z.2) h)
  have hcard : ((squareFreeGraph L).levelCut (freeRadius p) k).card ≤
      2 * srcShell.card := by
    have h₁ := Fintype.card_le_of_injective encode hencode
    have hprod : Fintype.card (↥srcShell × Bool) = srcShell.card * 2 := by simp
    simpa only [Fintype.card_coe, hprod, Nat.mul_comm] using h₁
  have hshell : srcShell.card ≤ shell₀.card + shell₁.card := by
    dsimp [srcShell]
    exact Finset.card_union_le shell₀ shell₁
  have h₀ : shell₀.card ≤ 4 * (k + 1) := by
    simpa [shell₀] using freeRadius_shell_card_le p k
  have h₁ : shell₁.card ≤ 4 * (k + 2) := by
    simpa [shell₁, Nat.add_assoc] using freeRadius_shell_card_le p (k + 1)
  have hn : ((squareFreeGraph L).levelCut (freeRadius p) k).card ≤
      2 * (4 * (k + 1) + 4 * (k + 2)) := le_trans hcard (Nat.mul_le_mul_left 2 (le_trans hshell (Nat.add_le_add h₀ h₁)))
  omega

theorem pathGraph_walk_up {L : ℕ} (x : Fin L) :
    ∀ (n : ℕ) (y : Fin L), x.val + n = y.val →
      ∃ w : (SimpleGraph.pathGraph L).Walk x y, w.length = n
  | 0, y, h => by
      have hxy : x = y := Fin.ext (by simpa using h)
      subst y
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | n + 1, y, h => by
      let z : Fin L := ⟨x.val + n, by omega⟩
      obtain ⟨w, hw⟩ := pathGraph_walk_up x n z rfl
      have hadj : (SimpleGraph.pathGraph L).Adj z y := by
        rw [SimpleGraph.pathGraph_adj]
        left
        dsimp [z]
        omega
      refine ⟨w.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), ?_⟩
      simp [hw]

theorem pathGraph_walk_length_natDist {L : ℕ} (x y : Fin L) :
    ∃ w : (SimpleGraph.pathGraph L).Walk x y, w.length = Nat.dist x.val y.val := by
  by_cases hxy : x.val ≤ y.val
  · let n := y.val - x.val
    have hsum : x.val + n = y.val := Nat.add_sub_of_le hxy
    obtain ⟨w, hw⟩ := pathGraph_walk_up x n y hsum
    exact ⟨w, by simpa [n, Nat.dist_eq_sub_of_le hxy] using hw⟩
  · have hyx : y.val < x.val := by omega
    let n := x.val - y.val
    have hsum : y.val + n = x.val := Nat.add_sub_of_le (Nat.le_of_lt hyx)
    obtain ⟨w, hw⟩ := pathGraph_walk_up y n x hsum
    refine ⟨w.reverse, ?_⟩
    calc
      w.reverse.length = w.length := SimpleGraph.Walk.length_reverse w
      _ = n := hw
      _ = Nat.dist x.val y.val := by
        simp [n, Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hyx)]

theorem squareFree_distance_le_radius {L : ℕ} (p q : SquareFreeVertex L) :
    (squareFreeGraph L).toSimpleGraph.dist p q ≤ freeRadius p q := by
  rw [squareFreeGraph_toSimpleGraph]
  obtain ⟨w₁, h₁⟩ := pathGraph_walk_length_natDist p.1 q.1
  obtain ⟨w₂, h₂⟩ := pathGraph_walk_length_natDist p.2 q.2
  let w := (w₁.boxProdLeft (SimpleGraph.pathGraph L) p.2).append
    (w₂.boxProdRight (SimpleGraph.pathGraph L) q.1)
  have hlen : w.length = freeRadius p q := by
    rw [SimpleGraph.Walk.length_append]
    change (SimpleGraph.Walk.map
      ((SimpleGraph.pathGraph L).boxProdLeft (SimpleGraph.pathGraph L) p.2).toHom w₁).length +
      (SimpleGraph.Walk.map
        ((SimpleGraph.pathGraph L).boxProdRight (SimpleGraph.pathGraph L) q.1).toHom w₂).length = _
    rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_map]
    simpa [freeRadius] using congrArg₂ Nat.add h₁ h₂
  rw [← hlen]
  exact SimpleGraph.dist_le w

/-- The free-square Green dipole form grows at least logarithmically with
graph distance. This formalizes the Dirichlet-principle lower bound for
the logarithmic Green estimate cited by Kharash–Peled, arXiv:1711.04720v1,
p. 3. -/
theorem squareFree_pairing_dipole_ge_log {L : ℕ} (hL : 0 < L)
    (p q : SquareFreeVertex L) :
    (1 / 24 : ℝ) * Real.log
        (↑(((squareFreeGraph L).toSimpleGraph.dist p q) + 1) : ℝ) ≤
      Multigraph.pairing (dipole p q)
        (-(squareFreeGraph L).greenOp (squareFreeGraph_connected hL) (dipole p q)) := by
  let G := squareFreeGraph L
  let s := freeRadius p
  have hG : G.Connected := squareFreeGraph_connected hL
  have hstep : ∀ e, s (G.src e) ≤ s (G.tgt e) + 1 ∧
      s (G.tgt e) ≤ s (G.src e) + 1 := by
    intro e
    simpa [G, s] using freeRadius_edge_step p e
  have hp : s p = 0 := by simp [s, freeRadius]
  have hcount : ∀ k ∈ Finset.range (s q),
      ((G.levelCut s k).card : ℝ) ≤ 24 * (↑(k + 1) : ℝ) := by
    intro k hk
    have hc := squareFree_levelCut_card_le p k
    exact_mod_cast hc
  have hbase := Multigraph.pairing_pointDipole_ge_log_of_levelCut_bound
    (G := G) hG s hstep hp le_rfl 24 (by norm_num) hcount
  have hd := squareFree_distance_le_radius p q
  have hdreal :
      (↑((G.toSimpleGraph.dist p q) + 1) : ℝ) ≤ ↑(s q + 1) := by
    exact_mod_cast Nat.add_le_add_right hd 1
  have hlog := Real.log_le_log (by positivity :
    0 < (↑((G.toSimpleGraph.dist p q) + 1) : ℝ)) hdreal
  have hscale : (1 / 24 : ℝ) * Real.log
      (↑((G.toSimpleGraph.dist p q) + 1) : ℝ) ≤
      (1 / 24 : ℝ) * Real.log (↑(s q + 1) : ℝ) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hsource : Multigraph.pointDipole p q = dipole p q := by
    rfl
  simpa [G, hsource] using hscale.trans hbase

/-- The cyclic distance on `ZMod n`, computed from the canonical difference
representative. -/
def torusCoordDistance (n : ℕ) (p x : ZMod n) : ℕ :=
  min (x - p).val (n - (x - p).val)

/-- A Boolean choice of the shorter orientation around a cyclic coordinate. -/
def torusCoordSign (n : ℕ) (p x : ZMod n) : Bool :=
  decide ((x - p).val ≤ n - (x - p).val)

/-- The sum of the two cyclic coordinate distances from `p`. -/
def torusRadius {n : ℕ} [NeZero n] (p x : TorusVertex n) : ℕ :=
  torusCoordDistance n p.1 x.1 + torusCoordDistance n p.2 x.2

private theorem cyclicValue_succ_step {n a : ℕ} (hn : 2 < n) (ha : a < n) :
    let b := (a + 1) % n
    min a (n - a) ≤ min b (n - b) + 1 ∧
      min b (n - b) ≤ min a (n - a) + 1 := by
  dsimp
  by_cases hwrap : a + 1 < n
  · have hb : (a + 1) % n = a + 1 := Nat.mod_eq_of_lt hwrap
    rw [hb]
    have hcmp₁ := le_total a (n - a)
    have hcmp₂ := le_total (a + 1) (n - (a + 1))
    rcases hcmp₁ with h₁ | h₁ <;> rcases hcmp₂ with h₂ | h₂ <;>
      simp [h₁, h₂] <;> omega
  · have hlast : a + 1 = n := by omega
    have hb : (a + 1) % n = 0 := by rw [hlast, Nat.mod_self]
    rw [hb]
    have ha' : a = n - 1 := by omega
    rw [ha']
    have hmin : min (n - 1) (n - (n - 1)) = 1 := by
      have hsub : n - (n - 1) = 1 := by omega
      rw [hsub, Nat.min_eq_right (by omega)]
    rw [hmin]
    simp

theorem torusCoordDistSign_injective {n : ℕ} [NeZero n] (p : ZMod n) :
    ∀ x y : ZMod n, torusCoordDistance n p x = torusCoordDistance n p y →
      torusCoordSign n p x = torusCoordSign n p y → x = y := by
  intro x y hdist hsign
  let a := (x - p).val
  let b := (y - p).val
  have haLt : a < n := ZMod.val_lt (x - p)
  have hbLt : b < n := ZMod.val_lt (y - p)
  have hbranch : (a ≤ n - a) = (b ≤ n - b) := by
    simpa [torusCoordSign, a, b] using congrArg id hsign
  have hdist' : min a (n - a) = min b (n - b) := by
    simpa [torusCoordDistance, a, b] using hdist
  have hab : a = b := by
    by_cases ha : a ≤ n - a
    · have hb : b ≤ n - b := by rwa [← hbranch]
      rw [Nat.min_eq_left ha, Nat.min_eq_left hb] at hdist'
      exact hdist'
    · have hb : ¬ b ≤ n - b := by
        intro hb
        exact ha (hbranch.mpr hb)
      have ha' : n - a ≤ a := le_of_not_ge ha
      have hb' : n - b ≤ b := le_of_not_ge hb
      rw [Nat.min_eq_right ha', Nat.min_eq_right hb'] at hdist'
      omega
  have hsub : x - p = y - p := ZMod.val_injective n hab
  have hadd := congrArg (fun z : ZMod n => z + p) hsub
  simpa using hadd

theorem torusRadius_shell_card_le {n : ℕ} [NeZero n]
    (p : TorusVertex n) (k : ℕ) :
    (Finset.univ.filter (fun x : TorusVertex n => torusRadius p x = k)).card ≤
      4 * (k + 1) := by
  change (Finset.univ.filter (fun x : ZMod n × ZMod n =>
    torusCoordDistance n p.1 x.1 + torusCoordDistance n p.2 x.2 = k)).card ≤
      4 * (k + 1)
  exact card_productRadiusShell_le_four
    (torusCoordDistance n p.1) (torusCoordDistance n p.2)
    (torusCoordSign n p.1) (torusCoordSign n p.2)
    (torusCoordDistSign_injective p.1) (torusCoordDistSign_injective p.2) k

private theorem torusCoordDistance_add_one_step {n : ℕ} (hn : 2 < n)
    [NeZero n] (p x : ZMod n) :
    torusCoordDistance n p x ≤ torusCoordDistance n p (x + 1) + 1 ∧
      torusCoordDistance n p (x + 1) ≤ torusCoordDistance n p x + 1 := by
  let a := (x - p).val
  have ha : a < n := ZMod.val_lt (x - p)
  have hval : (x + 1 - p).val = (a + 1) % n := by
    have hshift : x + 1 - p = (x - p) + 1 := by ring
    rw [hshift, ZMod.val_add]
    have hvone : (1 : ZMod n).val = 1 := by
      exact @ZMod.val_one n ⟨by omega⟩
    rw [hvone]
  have hnow : torusCoordDistance n p x = min a (n - a) := by
    simp [torusCoordDistance, a]
  have hnext : torusCoordDistance n p (x + 1) =
      min ((a + 1) % n) (n - ((a + 1) % n)) := by
    simp [torusCoordDistance, hval, a]
  have h := cyclicValue_succ_step hn ha
  simpa [hnow, hnext] using h

theorem torusRadius_edge_step {n : ℕ} (hn : 2 < n) [NeZero n]
    (p : TorusVertex n) (e : TorusEdge n) :
    torusRadius p ((torusGraph n hn).src e) ≤
        torusRadius p ((torusGraph n hn).tgt e) + 1 ∧
      torusRadius p ((torusGraph n hn).tgt e) ≤
        torusRadius p ((torusGraph n hn).src e) + 1 := by
  rcases e with ⟨⟨x, y⟩, direction⟩
  cases direction
  · have h := torusCoordDistance_add_one_step hn p.1 x
    simpa [torusRadius, torusGraph, torusStep] using
      (show torusCoordDistance n p.1 x + torusCoordDistance n p.2 y ≤
          torusCoordDistance n p.1 (x + 1) + torusCoordDistance n p.2 y + 1 ∧
        torusCoordDistance n p.1 (x + 1) + torusCoordDistance n p.2 y ≤
          torusCoordDistance n p.1 x + torusCoordDistance n p.2 y + 1 from by omega)
  · have h := torusCoordDistance_add_one_step hn p.2 y
    simpa [torusRadius, torusGraph, torusStep] using
      (show torusCoordDistance n p.1 x + torusCoordDistance n p.2 y ≤
          torusCoordDistance n p.1 x + torusCoordDistance n p.2 (y + 1) + 1 ∧
        torusCoordDistance n p.1 x + torusCoordDistance n p.2 (y + 1) ≤
          torusCoordDistance n p.1 x + torusCoordDistance n p.2 y + 1 from by omega)

def torusEdgeSourceDirection {n : ℕ} (e : TorusEdge n) : TorusVertex n × Bool := e

theorem torusEdgeSourceDirection_injective {n : ℕ} :
    Function.Injective (@torusEdgeSourceDirection n) := by
  intro e e' h
  exact h

theorem torus_levelCut_card_le {n : ℕ} (hn : 2 < n) [NeZero n]
    (p : TorusVertex n) (k : ℕ) :
    ((torusGraph n hn).levelCut (torusRadius p) k).card ≤ 24 * (k + 1) := by
  classical
  let G := torusGraph n hn
  let shell₀ : Finset (TorusVertex n) :=
    Finset.univ.filter fun x => torusRadius p x = k
  let shell₁ : Finset (TorusVertex n) :=
    Finset.univ.filter fun x => torusRadius p x = k + 1
  let srcShell : Finset (TorusVertex n) := shell₀ ∪ shell₁
  have hcutSrc : ∀ e ∈ G.levelCut (torusRadius p) k,
      (torusEdgeSourceDirection e).1 ∈ srcShell := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with h | h
    · have hs := h.1
      have hsrc : (torusEdgeSourceDirection e).1 = G.src e := by rfl
      rw [hsrc, Finset.mem_union]
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    · have hs := h.2
      have hsrc : (torusEdgeSourceDirection e).1 = G.src e := by rfl
      rw [hsrc, Finset.mem_union]
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  let encode : {e // e ∈ G.levelCut (torusRadius p) k} → ↥srcShell × Bool :=
    fun e => (⟨(torusEdgeSourceDirection e.1).1, hcutSrc e.1 e.2⟩,
      (torusEdgeSourceDirection e.1).2)
  have hencode : Function.Injective encode := by
    intro e e' h
    apply Subtype.ext
    apply torusEdgeSourceDirection_injective
    exact Prod.ext
      (congrArg (fun z : ↥srcShell × Bool => z.1.1) h)
      (congrArg (fun z : ↥srcShell × Bool => z.2) h)
  have hcard : (G.levelCut (torusRadius p) k).card ≤ 2 * srcShell.card := by
    have h₁ := Fintype.card_le_of_injective encode hencode
    have hprod : Fintype.card (↥srcShell × Bool) = srcShell.card * 2 := by simp
    simpa only [Fintype.card_coe, hprod, Nat.mul_comm] using h₁
  have hshell : srcShell.card ≤ shell₀.card + shell₁.card := by
    dsimp [srcShell]
    exact Finset.card_union_le shell₀ shell₁
  have h₀ : shell₀.card ≤ 4 * (k + 1) := by
    simpa [shell₀] using torusRadius_shell_card_le p k
  have h₁ : shell₁.card ≤ 4 * (k + 2) := by
    simpa [shell₁, Nat.add_assoc] using torusRadius_shell_card_le p (k + 1)
  have hn' : (G.levelCut (torusRadius p) k).card ≤
      2 * (4 * (k + 1) + 4 * (k + 2)) :=
    le_trans hcard (Nat.mul_le_mul_left 2
      (le_trans hshell (Nat.add_le_add h₀ h₁)))
  change (G.levelCut (torusRadius p) k).card ≤ 24 * (k + 1)
  omega

private def torusRightWalkExact (n : ℕ) (hn : 2 < n) (x y : ZMod n) :
    (k : ℕ) → (torusGraph n hn).toSimpleGraph.Walk (x, y) (x + k, y)
  | 0 => by
      exact SimpleGraph.Walk.nil.copy rfl (Prod.ext (by simp) rfl)
  | k + 1 => by
      have hend : (x + 1) + (k : ZMod n) =
          x + ((k + 1 : ℕ) : ZMod n) := by rw [Nat.cast_succ]; ring
      exact SimpleGraph.Walk.cons (torus_right_adj n hn x y)
        ((torusRightWalkExact n hn (x + 1) y k).copy rfl (Prod.ext hend rfl))

private theorem torusRightWalkExact_length (n : ℕ) (hn : 2 < n)
    (x y : ZMod n) : ∀ k, (torusRightWalkExact n hn x y k).length = k
  | 0 => by simp [torusRightWalkExact]
  | k + 1 => by
      simp only [torusRightWalkExact, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_copy]
      rw [torusRightWalkExact_length n hn (x + 1) y k]

private def torusUpWalkExact (n : ℕ) (hn : 2 < n) (x y : ZMod n) :
    (k : ℕ) → (torusGraph n hn).toSimpleGraph.Walk (x, y) (x, y + k)
  | 0 => by
      exact SimpleGraph.Walk.nil.copy rfl (Prod.ext rfl (by simp))
  | k + 1 => by
      have hend : (y + 1) + (k : ZMod n) =
          y + ((k + 1 : ℕ) : ZMod n) := by rw [Nat.cast_succ]; ring
      exact SimpleGraph.Walk.cons (torus_up_adj n hn x y)
        ((torusUpWalkExact n hn x (y + 1) k).copy rfl (Prod.ext rfl hend))

private theorem torusUpWalkExact_length (n : ℕ) (hn : 2 < n)
    (x y : ZMod n) : ∀ k, (torusUpWalkExact n hn x y k).length = k
  | 0 => by simp [torusUpWalkExact]
  | k + 1 => by
      simp only [torusUpWalkExact, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_copy]
      rw [torusUpWalkExact_length n hn x (y + 1) k]

private theorem torusHorizontalShortestWalk {n : ℕ} (hn : 2 < n)
    [NeZero n] (x y v : ZMod n) :
    ∃ w : (torusGraph n hn).toSimpleGraph.Walk (x, v) (y, v),
      w.length = torusCoordDistance n x y := by
  let z := y - x
  let a := z.val
  have ha : a < n := ZMod.val_lt z
  by_cases hshort : a ≤ n - a
  · have hdist : torusCoordDistance n x y = a := by
      simp [torusCoordDistance, z, a, Nat.min_eq_left hshort]
    have hz : (↑a : ZMod n) = z := ZMod.natCast_zmod_val z
    have hend : x + (↑a : ZMod n) = y := by
      rw [hz]
      dsimp [z]
      abel
    let w := torusRightWalkExact n hn x v a
    refine ⟨w.copy rfl (Prod.ext hend rfl), ?_⟩
    rw [SimpleGraph.Walk.length_copy, torusRightWalkExact_length]
    exact hdist.symm
  · have hlong : n - a ≤ a := le_of_not_ge hshort
    have haPos : 0 < a := by omega
    have hdist : torusCoordDistance n x y = n - a := by
      have hmin : min a (n - a) = n - a := Nat.min_eq_right hlong
      simpa [torusCoordDistance, z, a] using hmin
    have hnegval : (-z).val = n - a := by
      rw [ZMod.neg_val']
      exact Nat.mod_eq_of_lt (by omega)
    have hnegcast : (↑(n - a) : ZMod n) = -z := by
      calc
        (↑(n - a) : ZMod n) = (↑(-z).val : ZMod n) := by rw [hnegval]
        _ = -z := ZMod.natCast_zmod_val (-z)
    have hend : y + (↑(n - a) : ZMod n) = x := by
      rw [hnegcast]
      dsimp [z]
      abel
    let w := torusRightWalkExact n hn y v (n - a)
    have hw : w.length = n - a := torusRightWalkExact_length n hn y v (n - a)
    refine ⟨w.reverse.copy (Prod.ext hend rfl) rfl, ?_⟩
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      hw]
    exact hdist.symm

private theorem torusVerticalShortestWalk {n : ℕ} (hn : 2 < n)
    [NeZero n] (x y v : ZMod n) :
    ∃ w : (torusGraph n hn).toSimpleGraph.Walk (v, x) (v, y),
      w.length = torusCoordDistance n x y := by
  let z := y - x
  let a := z.val
  have ha : a < n := ZMod.val_lt z
  by_cases hshort : a ≤ n - a
  · have hdist : torusCoordDistance n x y = a := by
      simp [torusCoordDistance, z, a, Nat.min_eq_left hshort]
    have hz : (↑a : ZMod n) = z := ZMod.natCast_zmod_val z
    have hend : x + (↑a : ZMod n) = y := by
      rw [hz]
      dsimp [z]
      abel
    let w := torusUpWalkExact n hn v x a
    refine ⟨w.copy rfl (Prod.ext rfl hend), ?_⟩
    rw [SimpleGraph.Walk.length_copy, torusUpWalkExact_length]
    exact hdist.symm
  · have hlong : n - a ≤ a := le_of_not_ge hshort
    have haPos : 0 < a := by omega
    have hdist : torusCoordDistance n x y = n - a := by
      have hmin : min a (n - a) = n - a := Nat.min_eq_right hlong
      simpa [torusCoordDistance, z, a] using hmin
    have hnegval : (-z).val = n - a := by
      rw [ZMod.neg_val']
      exact Nat.mod_eq_of_lt (by omega)
    have hnegcast : (↑(n - a) : ZMod n) = -z := by
      calc
        (↑(n - a) : ZMod n) = (↑(-z).val : ZMod n) := by rw [hnegval]
        _ = -z := ZMod.natCast_zmod_val (-z)
    have hend : y + (↑(n - a) : ZMod n) = x := by
      rw [hnegcast]
      dsimp [z]
      abel
    let w := torusUpWalkExact n hn v y (n - a)
    have hw : w.length = n - a := torusUpWalkExact_length n hn v y (n - a)
    refine ⟨w.reverse.copy (Prod.ext rfl hend) rfl, ?_⟩
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      hw]
    exact hdist.symm

theorem torus_distance_le_radius {n : ℕ} (hn : 2 < n) [NeZero n]
    (p q : TorusVertex n) :
    (torusGraph n hn).toSimpleGraph.dist p q ≤ torusRadius p q := by
  obtain ⟨w₁, h₁⟩ := torusHorizontalShortestWalk hn p.1 q.1 p.2
  obtain ⟨w₂, h₂⟩ := torusVerticalShortestWalk hn p.2 q.2 q.1
  let w := w₁.append w₂
  have hlen : w.length = torusRadius p q := by
    rw [SimpleGraph.Walk.length_append]
    simpa [torusRadius] using congrArg₂ Nat.add h₁ h₂
  rw [← hlen]
  exact SimpleGraph.dist_le w

/-- The square-torus Green dipole form grows at least logarithmically with
graph distance, uniformly in the side length. This is the periodic
lower bound for the logarithmic Green estimate cited by Kharash–Peled,
arXiv:1711.04720v1, p. 3. -/
theorem torus_pairing_dipole_ge_log {n : ℕ} (hn : 2 < n) [NeZero n]
    (p q : TorusVertex n) :
    (1 / 24 : ℝ) * Real.log
        (↑(((torusGraph n hn).toSimpleGraph.dist p q) + 1) : ℝ) ≤
      Multigraph.pairing (dipole p q)
        (-(torusGraph n hn).greenOp (torusGraph_connected n hn) (dipole p q)) := by
  let G := torusGraph n hn
  let s := torusRadius p
  have hG : G.Connected := torusGraph_connected n hn
  have hstep : ∀ e, s (G.src e) ≤ s (G.tgt e) + 1 ∧
      s (G.tgt e) ≤ s (G.src e) + 1 := by
    intro e
    simpa [G, s] using torusRadius_edge_step hn p e
  have hp : s p = 0 := by simp [s, torusRadius, torusCoordDistance]
  have hcount : ∀ k ∈ Finset.range (s q),
      ((G.levelCut s k).card : ℝ) ≤ 24 * (↑(k + 1) : ℝ) := by
    intro k hk
    have hc := torus_levelCut_card_le hn p k
    exact_mod_cast hc
  have hbase := Multigraph.pairing_pointDipole_ge_log_of_levelCut_bound
    (G := G) hG s hstep hp le_rfl 24 (by norm_num) hcount
  have hd := torus_distance_le_radius hn p q
  have hdreal :
      (↑((G.toSimpleGraph.dist p q) + 1) : ℝ) ≤ ↑(s q + 1) := by
    exact_mod_cast Nat.add_le_add_right hd 1
  have hlog := Real.log_le_log (by positivity :
    0 < (↑((G.toSimpleGraph.dist p q) + 1) : ℝ)) hdreal
  have hscale : (1 / 24 : ℝ) * Real.log
      (↑(G.toSimpleGraph.dist p q + 1) : ℝ) ≤
      (1 / 24 : ℝ) * Real.log (↑(s q + 1) : ℝ) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hsource : Multigraph.pointDipole p q = dipole p q := rfl
  simpa [G, hsource] using hscale.trans hbase

end FroehlichSpencer.BKT.Lattice2D

end
