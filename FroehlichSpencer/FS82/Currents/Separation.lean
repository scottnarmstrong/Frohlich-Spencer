/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.Geometry

/-!
# Discrete separation gap for closed unit cubical links

Coordinate gap for FS82 dual-link separation.
-/

public section

open FroehlichSpencer.FS82.Cubical

namespace FroehlichSpencer.FS82.Currents


@[expose] noncomputable def endpointParam {B : Cubical.Box 4} (e : Link B) (b : Bool) : ℝ :=
  (e.base e.axis).val + if b then 1 else 0

@[expose] noncomputable def endpointPoint {B : Cubical.Box 4} (e : Link B) (b : Bool) : Point :=
  linkPointAt e (endpointParam e b)

theorem endpointPoint_axis {B : Cubical.Box 4} (e : Link B) (b : Bool) :
    endpointPoint e b e.axis = endpointParam e b := by
  simp [endpointPoint, endpointParam, linkPointAt]

theorem linkPointAt_axis {B : Cubical.Box 4} (e : Link B) (t : ℝ) :
    linkPointAt e t e.axis = t := by
  simp [linkPointAt]

theorem endpointPoint_other {B : Cubical.Box 4} (e : Link B) (b : Bool) (k : Fin 4)
    (hk : k ≠ e.axis) : endpointPoint e b k = (e.base k).val := by
  simp [endpointPoint, endpointParam, linkPointAt, Function.update_of_ne hk]

theorem linkPointAt_other {B : Cubical.Box 4} (e : Link B) (t : ℝ) (k : Fin 4)
    (hk : k ≠ e.axis) : linkPointAt e t k = (e.base k).val := by
  simp [linkPointAt, Function.update_of_ne hk]

theorem endpointPoint_mem {B : Cubical.Box 4} (e : Link B) (b : Bool) :
    endpointPoint e b ∈ linkSegment e := by
  refine ⟨endpointParam e b, ?_, ?_, rfl⟩
  · cases b <;> simp [endpointParam]
  · cases b <;> simp [endpointParam]

private theorem abs_left_clamp {a b t : ℝ}
    (ht₀ : a ≤ t) (_ht₁ : t ≤ a + 1) (hb : b ≤ a) :
    |a - b| ≤ |t - b| := by
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

private theorem abs_right_clamp {a b t : ℝ}
    (_ht₀ : a ≤ t) (ht₁ : t ≤ a + 1) (hb : a + 1 ≤ b) :
    |(a + 1) - b| ≤ |t - b| := by
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  linarith

private theorem endpoint_param_closest {B : Cubical.Box 4} (e : Link B)
    (b : ℤ) (t : ℝ) (ht₀ : (e.base e.axis).val ≤ t)
    (ht₁ : t ≤ (e.base e.axis).val + 1) :
    ∃ be : Bool,
      |endpointParam e be - (b : ℝ)| ≤ |t - (b : ℝ)| := by
  by_cases hb : b ≤ (e.base e.axis).val
  · refine ⟨false, ?_⟩
    simpa [endpointParam] using abs_left_clamp
      (a := (e.base e.axis).val) (b := (b : ℝ)) ht₀ ht₁ (by exact_mod_cast hb)
  · have hb' : (e.base e.axis).val + 1 ≤ b := by omega
    refine ⟨true, ?_⟩
    simpa [endpointParam] using abs_right_clamp
      (a := (e.base e.axis).val) (b := (b : ℝ)) ht₀ ht₁ (by exact_mod_cast hb')

private theorem parallel_endpoint_params_close {a b : ℤ} {t s : ℝ}
    (ht₀ : (a : ℝ) ≤ t) (ht₁ : t ≤ (a : ℝ) + 1)
    (hs₀ : (b : ℝ) ≤ s) (hs₁ : s ≤ (b : ℝ) + 1) :
    ∃ ba bb : Bool,
      |((a : ℝ) + if ba then 1 else 0) - ((b : ℝ) + if bb then 1 else 0)| ≤
        |t - s| := by
  rcases lt_trichotomy a b with hab | hab | hab
  · by_cases htouch : a + 1 = b
    · refine ⟨true, false, ?_⟩
      dsimp
      have htouchR : (a : ℝ) + 1 = (b : ℝ) := by exact_mod_cast htouch
      rw [htouchR]
      norm_num
    · have hgap : a + 1 < b := by omega
      refine ⟨true, false, ?_⟩
      dsimp
      have hgapR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (le_of_lt hgap)
      rw [abs_of_nonpos (by linarith)]
      have hs_t : (b : ℝ) - ((a : ℝ) + 1) ≤ s - t := by linarith
      rw [abs_of_nonpos (by linarith : t - s ≤ 0)]
      linarith
  · subst b
    exact ⟨false, false, by simp⟩
  · by_cases htouch : b + 1 = a
    · refine ⟨false, true, ?_⟩
      dsimp
      have htouchR : (b : ℝ) + 1 = (a : ℝ) := by exact_mod_cast htouch
      rw [htouchR]
      norm_num
    · have hgap : b + 1 < a := by omega
      refine ⟨false, true, ?_⟩
      dsimp
      have hgapR : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast (le_of_lt hgap)
      rw [abs_of_nonneg (by linarith)]
      have ht_s : (a : ℝ) - ((b : ℝ) + 1) ≤ t - s := by linarith
      rw [abs_of_nonneg (by linarith : 0 ≤ t - s)]
      linarith

private theorem endpoint_pair_distance_le_of_segment_points {B : Cubical.Box 4}
    (e f : Link B) (t s : ℝ)
    (ht₀ : (e.base e.axis).val ≤ t) (ht₁ : t ≤ (e.base e.axis).val + 1)
    (hs₀ : (f.base f.axis).val ≤ s) (hs₁ : s ≤ (f.base f.axis).val + 1) :
    ∃ be bf : Bool,
      dist (endpointPoint e be) (endpointPoint f bf) ≤
        dist (linkPointAt e t) (linkPointAt f s) := by
  classical
  by_cases haxes : e.axis = f.axis
  · have hparams := parallel_endpoint_params_close
      (a := (e.base e.axis).val) (b := (f.base f.axis).val)
      ht₀ ht₁ hs₀ hs₁
    obtain ⟨be, bf, hparam⟩ := hparams
    refine ⟨be, bf, ?_⟩
    have hcoord : ∀ k : Fin 4,
        dist ((endpointPoint e be) k) ((endpointPoint f bf) k) ≤
          dist ((linkPointAt e t) k) ((linkPointAt f s) k) := by
      intro k
      by_cases hk : k = e.axis
      · subst k
        have hfEnd : endpointPoint f bf e.axis = endpointParam f bf := by
          rw [haxes]
          exact endpointPoint_axis f bf
        have hfSeg : linkPointAt f s e.axis = s := by
          rw [haxes]
          exact linkPointAt_axis f s
        rw [endpointPoint_axis, hfEnd, linkPointAt_axis, hfSeg]
        rw [Real.dist_eq]
        change |endpointParam e be - endpointParam f bf| ≤ |t - s|
        exact hparam
      · have hkf : f.axis ≠ k := by
          intro h
          exact hk (haxes.trans h).symm
        rw [endpointPoint_other e be k hk,
          endpointPoint_other f bf k (Ne.symm hkf),
          linkPointAt_other e t k hk,
          linkPointAt_other f s k (Ne.symm hkf)]
    have hsquare :
        dist (endpointPoint e be) (endpointPoint f bf)^2 ≤
          dist (linkPointAt e t) (linkPointAt f s)^2 := by
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
      apply Finset.sum_le_sum
      intro k hk
      have hc := hcoord k
      exact (sq_le_sq₀ (by positivity) (by positivity)).2 hc
    exact (sq_le_sq₀ (by positivity) (by positivity)).1 hsquare
  · have haxisNe : f.axis ≠ e.axis := Ne.symm haxes
    obtain ⟨be, hbe⟩ := endpoint_param_closest e (f.base e.axis).val t ht₀ ht₁
    obtain ⟨bf, hbf⟩ := endpoint_param_closest f (e.base f.axis).val s hs₀ hs₁
    refine ⟨be, bf, ?_⟩
    have hcoord : ∀ k : Fin 4,
        dist ((endpointPoint e be) k) ((endpointPoint f bf) k) ≤
          dist ((linkPointAt e t) k) ((linkPointAt f s) k) := by
      intro k
      by_cases hke : k = e.axis
      · subst k
        rw [endpointPoint_axis, endpointPoint_other f bf e.axis haxes,
          linkPointAt_axis, linkPointAt_other f s e.axis haxes]
        simpa [Real.dist_eq] using hbe
      · by_cases hkf : k = f.axis
        · subst k
          rw [endpointPoint_other e be f.axis haxisNe,
            endpointPoint_axis, linkPointAt_other e t f.axis haxisNe,
            linkPointAt_axis]
          simpa [Real.dist_eq, abs_sub_comm] using hbf
        · rw [endpointPoint_other e be k hke, endpointPoint_other f bf k hkf,
            linkPointAt_other e t k hke, linkPointAt_other f s k hkf]
    have hsquare :
        dist (endpointPoint e be) (endpointPoint f bf)^2 ≤
          dist (linkPointAt e t) (linkPointAt f s)^2 := by
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
      apply Finset.sum_le_sum
      intro k hk
      have hc := hcoord k
      exact (sq_le_sq₀ (by positivity) (by positivity)).2 hc
    exact (sq_le_sq₀ (by positivity) (by positivity)).1 hsquare

private noncomputable def endpointIntCoord {B : Cubical.Box 4} (e : Link B) (b : Bool) (k : Fin 4) : ℤ :=
  (e.base k).val + if e.axis = k ∧ b then 1 else 0

private theorem endpointPoint_coord {B : Cubical.Box 4} (e : Link B) (b : Bool) (k : Fin 4) :
    endpointPoint e b k = (endpointIntCoord e b k : ℝ) := by
  by_cases hk : k = e.axis
  · subst k
    rw [endpointPoint_axis]
    simp [endpointParam, endpointIntCoord]
  · rw [endpointPoint_other e b k hk]
    simp [endpointIntCoord, Ne.symm hk]

private theorem endpoint_dist_sq_int {B : Cubical.Box 4} (e f : Link B) (be bf : Bool) :
    ∃ n : ℤ,
      dist (endpointPoint e be) (endpointPoint f bf)^2 = (n : ℝ) := by
  let n : ℤ := ∑ k : Fin 4,
    (endpointIntCoord e be k - endpointIntCoord f bf k)^2
  refine ⟨n, ?_⟩
  rw [EuclideanSpace.dist_sq_eq]
  dsimp [n]
  calc
    (∑ k : Fin 4, dist ((endpointPoint e be).ofLp k) ((endpointPoint f bf).ofLp k)^2) =
        ∑ k : Fin 4,
          (((endpointIntCoord e be k - endpointIntCoord f bf k)^2 : ℤ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [endpointPoint_coord, endpointPoint_coord, Real.dist_eq,
        ← Int.cast_sub, Int.cast_pow, sq_abs]
    _ = ((∑ k : Fin 4,
          (endpointIntCoord e be k - endpointIntCoord f bf k)^2 : ℤ) : ℝ) := by
      norm_cast

private theorem endpoint_distance_le_one_of_lt_sqrt_two {B : Cubical.Box 4}
    (e f : Link B) (be bf : Bool)
    (hd : dist (endpointPoint e be) (endpointPoint f bf) < Real.sqrt 2) :
    dist (endpointPoint e be) (endpointPoint f bf) ≤ 1 := by
  obtain ⟨n, hn⟩ := endpoint_dist_sq_int e f be bf
  have hnonneg : 0 ≤ (n : ℝ) := by rw [← hn]; positivity
  have hlt : (n : ℝ) < 2 := by
    rw [← hn]
    have hsq : dist (endpointPoint e be) (endpointPoint f bf)^2 <
        (Real.sqrt 2)^2 := (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg 2)).2 hd
    rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)] at hsq
    exact hsq
  have hnlt : n < 2 := by exact_mod_cast hlt
  have hnle : n ≤ 1 := by omega
  have hsqle : dist (endpointPoint e be) (endpointPoint f bf)^2 ≤ 1 := by
    rw [hn]
    exact_mod_cast (show (n : ℝ) ≤ 1 by exact_mod_cast hnle)
  have hsqle' : dist (endpointPoint e be) (endpointPoint f bf)^2 ≤ (1 : ℝ)^2 := by
    nlinarith [hsqle]
  exact (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).1 hsqle'

theorem linkDistance_gt_one_implies_sqrt_two_le {B : Cubical.Box 4}
    (e f : Link B) (h : 1 < linkDistance e f) :
    Real.sqrt 2 ≤ linkDistance e f := by
  apply le_csInf
  · refine ⟨dist (vertexPoint e.base) (vertexPoint f.base), ?_⟩
    exact ⟨vertexPoint e.base, sourcePoint_mem_linkSegment e,
      vertexPoint f.base, sourcePoint_mem_linkSegment f, rfl⟩
  · rintro r ⟨x, hx, y, hy, rfl⟩
    rcases hx with ⟨t, ht₀, ht₁, rfl⟩
    rcases hy with ⟨s, hs₀, hs₁, rfl⟩
    obtain ⟨be, bf, hendpoint⟩ :=
      endpoint_pair_distance_le_of_segment_points e f t s ht₀ ht₁ hs₀ hs₁
    by_contra hnot
    have hsmall : dist (linkPointAt e t) (linkPointAt f s) < Real.sqrt 2 :=
      lt_of_not_ge hnot
    have hendpointSmall :
        dist (endpointPoint e be) (endpointPoint f bf) < Real.sqrt 2 :=
      lt_of_le_of_lt hendpoint hsmall
    have hleOne := endpoint_distance_le_one_of_lt_sqrt_two e f be bf hendpointSmall
    have hdist := linkDistance_le_dist e f (endpointPoint_mem e be) (endpointPoint_mem f bf)
    linarith

end FroehlichSpencer.FS82.Currents
