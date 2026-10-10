/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.Separation
public import FroehlichSpencer.FS82.Currents.SelectedCurrentLinks
public import FroehlichSpencer.FS82.Moment.CurrentDecay
public import FroehlichSpencer.FS82.Currents.Expansion

/-!
# Shared plaquettes force the source link distance below `sqrt 2`
-/

public section

namespace FroehlichSpencer.FS82.Currents.PlaquetteDistance

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Currents.SelectedCurrentLinks
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Moment.CurrentDecay

variable {B : SourceBox}

theorem geometryAxis_eq_linkDirection (e : SourceDualOneCells B) :
    Currents.axis e = linkDirection e := by
  have hmem : Currents.axis e ∈ dualCellAxes e.1 := by
    rw [Currents.axes_eq_singleton]
    simp
  rw [linkAxes_eq_singleton] at hmem
  exact Finset.mem_singleton.mp hmem

theorem geometryBase_val_eq_linkBaseCoordinate (e : SourceDualOneCells B)
    (i : Fin 4) :
    (Currents.base e i).val = linkBaseCoordinate e i := by
  cases hi : e.1 i <;>
    simp [Currents.base, coordToBumpedAnchor, linkBaseCoordinate, hi]

theorem incidentPlaquette_data {e : SourceDualOneCells B}
    {p : SourceDualTwoCells B} (he : linkIncidentPlaquette e p) :
    ∃ i : Fin 4, ∃ v : Fin (B i), ∃ n : Fin (B i + 1),
      e.1 i = Sum.inl v ∧ p.1 i = Sum.inr n ∧
      (n.val = v.val ∨ n.val = v.val + 1) ∧
      ∀ k, k ≠ i → p.1 k = e.1 k := by
  rcases he with ⟨i, v, hiv, hup | hlo⟩
  · refine ⟨i, v, ⟨v.val + 1, by omega⟩, hiv, ?_, ?_, ?_⟩
    · have h := congrArg (fun c : DualCell 4 B => c i) hup
      simpa [dualUpperFace] using h
    · exact Or.inr rfl
    · intro k hki
      have h := congrArg (fun c : DualCell 4 B => c k) hup
      simpa [dualUpperFace, Function.update_of_ne hki] using h
  · refine ⟨i, v, ⟨v.val, by omega⟩, hiv, ?_, ?_, ?_⟩
    · have h := congrArg (fun c : DualCell 4 B => c i) hlo
      simpa [dualLowerFace] using h
    · exact Or.inl rfl
    · intro k hki
      have h := congrArg (fun c : DualCell 4 B => c k) hlo
      simpa [dualLowerFace, Function.update_of_ne hki] using h

theorem source_link_axis_not_transverse (e : SourceDualOneCells B)
    {i : Fin 4} (hleft : ∃ v, e.1 i = Sum.inl v) :
    i ≠ linkDirection e := by
  intro h
  subst i
  rcases hleft with ⟨v, hv⟩
  have hr := linkCoord_isRight_iff e (linkDirection e) |>.mpr rfl
  rw [hv] at hr
  contradiction

theorem sourceBase_eq_of_cellCoord_eq (e f : SourceDualOneCells B)
    (i : Fin 4) (h : e.1 i = f.1 i) :
    Currents.base e i = Currents.base f i := by
  apply Fin.ext
  simp only [Currents.base, coordToBumpedAnchor]
  rw [h]

theorem endpointPoint_coord {e : Link B} (b : Bool) (k : Fin 4) :
    endpointPoint e b k =
      if k = axis e then endpointParam e b else (base e k).val := by
  by_cases h : k = axis e
  · subst k
    simp [endpointPoint_axis]
  · rw [endpointPoint_other e b k h]
    simp [h]

theorem endpointParam_formula {e : Link B} (b : Bool) :
    endpointParam e b = (base e (Currents.axis e)).val + if b then 1 else 0 := rfl

theorem distance_ge_one_of_one_coord_difference (x y : Point) (i : Fin 4)
    (hcoord : |x i - y i| = 1) : 1 ≤ dist x y := by
  have hsq : dist x y ^ 2 = ∑ k : Fin 4, dist (x k) (y k) ^ 2 := by
    simpa using EuclideanSpace.dist_sq_eq x y
  have hterm : dist (x i) (y i) ^ 2 ≤ dist x y ^ 2 := by
    rw [hsq]
    exact Finset.single_le_sum (fun k hk => sq_nonneg (dist (x k) (y k)))
      (Finset.mem_univ i)
  rw [Real.dist_eq] at hterm
  rw [hcoord] at hterm
  have hnonneg : 0 ≤ dist x y := dist_nonneg
  nlinarith

theorem linkDistance_eq_one_of_parallel_opposite {e f : Link B}
    (i : Fin 4) (hie : i ≠ axis e) (hif : i ≠ axis f)
    (hgap : |((base e i).val : ℝ) - ((base f i).val : ℝ)| = 1)
    (hother : ∀ k, k ≠ i → base e k = base f k) :
    linkDistance e f = 1 := by
  have hbase : dist (vertexPoint (base e)) (vertexPoint (base f)) = 1 := by
    have hsq : dist (vertexPoint (base e)) (vertexPoint (base f)) ^ 2 =
        ∑ k : Fin 4,
          dist ((vertexPoint (base e)) k) ((vertexPoint (base f)) k) ^ 2 := by
      simpa using EuclideanSpace.dist_sq_eq
        (vertexPoint (base e)) (vertexPoint (base f))
    have hsum : (∑ k : Fin 4,
        dist ((vertexPoint (base e)) k) ((vertexPoint (base f)) k) ^ 2) = 1 := by
      have hzero : ∀ k, k ≠ i →
          dist ((vertexPoint (base e)) k) ((vertexPoint (base f)) k) ^ 2 = 0 := by
        intro k hki
        rw [Real.dist_eq]
        change |((base e k).val : ℝ) - ((base f k).val : ℝ)| ^ 2 = 0
        have hv := congrArg Fin.val (hother k hki)
        rw [hv]
        simp
      rw [Finset.sum_eq_single i]
      · have hcoord : |((vertexPoint (base e)) i) -
            ((vertexPoint (base f)) i)| = 1 := by
          simpa [vertexPoint] using hgap
        rw [Real.dist_eq, hcoord]
        norm_num
      · intro k hk hki
        exact hzero k hki
      · simp
    have hsquare : dist (vertexPoint (base e))
        (vertexPoint (base f)) ^ 2 = 1 := hsq.trans hsum
    have hn : 0 ≤ dist (vertexPoint (base e)) (vertexPoint (base f)) := dist_nonneg
    nlinarith
  apply le_antisymm
  · exact linkDistance_le_dist e f (sourcePoint_mem_linkSegment e)
      (sourcePoint_mem_linkSegment f) |>.trans_eq hbase
  · apply le_csInf
    · refine ⟨dist (vertexPoint (base e)) (vertexPoint (base f)), ?_⟩
      exact ⟨vertexPoint (base e), sourcePoint_mem_linkSegment e,
        vertexPoint (base f), sourcePoint_mem_linkSegment f, rfl⟩
    · rintro r ⟨x, hx, y, hy, rfl⟩
      rcases hx with ⟨t, ht0, ht1, rfl⟩
      rcases hy with ⟨s, hs0, hs1, rfl⟩
      have hcoord : |(linkPointAt e t) i - (linkPointAt f s) i| = 1 := by
        rw [linkPointAt_other e t i hie, linkPointAt_other f s i hif]
        exact hgap
      exact distance_ge_one_of_one_coord_difference _ _ i hcoord

theorem linkDistance_lt_sqrt_two_of_sharedPlaquette {e f : SourceDualOneCells B}
    (hne : e ≠ f)
    (h : ∃ p : SourceDualTwoCells B,
      linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) :
    linkDistance e f < Real.sqrt 2 := by
  classical
  obtain ⟨p, hpe, hpf⟩ := h
  obtain ⟨i, vi, ni, hEi, hPiE, hSideE, hOtherE⟩ := incidentPlaquette_data hpe
  obtain ⟨j, vj, nj, hFj, hPjF, hSideF, hOtherF⟩ := incidentPlaquette_data hpf
  let de := linkDirection e
  let df := linkDirection f
  have hEiNe : i ≠ de := by
    simpa [de] using source_link_axis_not_transverse e ⟨vi, hEi⟩
  have hFjNe : j ≠ df := by
    simpa [df] using source_link_axis_not_transverse f ⟨vj, hFj⟩
  have hAxisLinkE : Currents.axis e = de := by
    simpa [Link.axis, de] using geometryAxis_eq_linkDirection e
  have hAxisLinkF : Currents.axis f = df := by
    simpa [Link.axis, df] using geometryAxis_eq_linkDirection f
  by_cases haxes : de = df
  · have hij : i = j := by
      by_contra hne
      have hji : j ≠ i := by
        intro hji
        exact hne hji.symm
      have hjde : j ≠ de := by simpa [de, df, haxes] using hFjNe
      have hleftE : ∃ w, e.1 j = Sum.inl w :=
        linkCoord_isLeft_of_ne_direction e (by simpa [de] using hjde)
      rcases hleftE with ⟨w, hw⟩
      have hpLeft := hOtherE j hji
      rw [hpLeft, hw] at hPjF
      cases hPjF
    subst j
    have hcells_ne : vi ≠ vj := by
      intro hv
      apply hne
      apply Subtype.ext
      funext k
      by_cases hk : k = i
      · subst k
        rw [hEi, hFj, hv]
      · have hpEq : e.1 k = f.1 k := by
          calc
            e.1 k = p.1 k := (hOtherE k hk).symm
            _ = f.1 k := hOtherF k hk
        exact hpEq
    have hni : ni.val = nj.val := by
      have hpEq := hPiE.symm.trans hPjF
      exact congrArg Fin.val (Sum.inr.inj hpEq)
    have hgapNat : vi.val + 1 = vj.val + 1 + 1 ∨
        vj.val + 1 = vi.val + 1 + 1 := by
      rcases hSideE with helo | hehi <;>
        rcases hSideF with hflo | hfhi
      · have : vi.val = vj.val := by omega
        exact False.elim (hcells_ne (Fin.ext this))
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
      · have : vi.val = vj.val := by omega
        exact False.elim (hcells_ne (Fin.ext this))
    have hbaseEi : (Currents.base e i).val = vi.val + 1 := by
      simp [geometryBase_val_eq_linkBaseCoordinate, linkBaseCoordinate, hEi]
    have hbaseFi : (Currents.base f i).val = vj.val + 1 := by
      simp [geometryBase_val_eq_linkBaseCoordinate, linkBaseCoordinate, hFj]
    have hgapReal : |((Currents.base e i).val : ℝ) -
        ((Currents.base f i).val : ℝ)| = 1 := by
      rw [hbaseEi, hbaseFi]
      push_cast
      rcases hgapNat with h | h
      · have hr : (vi.val : ℝ) + 1 = (vj.val : ℝ) + 2 := by exact_mod_cast h
        rw [hr]
        norm_num
      · have hr : (vj.val : ℝ) + 1 = (vi.val : ℝ) + 2 := by exact_mod_cast h
        rw [hr]
        norm_num [abs_sub_comm]
    have hother : ∀ k, k ≠ i → Currents.base e k = Currents.base f k := by
      intro k hki
      apply sourceBase_eq_of_cellCoord_eq
      calc
        e.1 k = p.1 k := (hOtherE k hki).symm
        _ = f.1 k := hOtherF k hki
    have hdist : linkDistance e f = 1 :=
      linkDistance_eq_one_of_parallel_opposite i
        (by simpa [hAxisLinkE, de] using hEiNe)
        (by simpa [hAxisLinkF, haxes, de, df] using hEiNe)
        hgapReal hother
    rw [hdist]
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  · have hi_eq_df : i = df := by
      by_contra hne
      have hdfi : df ≠ i := by intro h; exact hne h.symm
      have hpE : p.1 df = e.1 df := hOtherE df hdfi
      have hpF : p.1 df = f.1 df := hOtherF df hFjNe.symm
      have hleft : ∃ w, e.1 df = Sum.inl w :=
        linkCoord_isLeft_of_ne_direction e (by
          intro h
          exact haxes (by simpa [de, df] using h.symm))
      rcases hleft with ⟨w, hw⟩
      have hright := (linkCoord_isRight_iff f df).mpr rfl
      have heq : e.1 df = f.1 df := hpE.symm.trans hpF
      rw [← heq, hw] at hright
      simp at hright
    have hj_eq_de : j = de := by
      by_contra hne
      have hdej : de ≠ j := by intro h; exact hne h.symm
      have hdeI : de ≠ i := by rw [hi_eq_df]; exact haxes
      have hpE : p.1 de = e.1 de := hOtherE de hdeI
      have hpF : p.1 de = f.1 de := hOtherF de hdej
      have hleft : ∃ w, f.1 de = Sum.inl w :=
        linkCoord_isLeft_of_ne_direction f (by
          intro h
          exact haxes (by simpa [de, df] using h))
      rcases hleft with ⟨w, hw⟩
      have hright := (linkCoord_isRight_iff e de).mpr rfl
      have heq : e.1 de = f.1 de := hpE.symm.trans hpF
      rw [heq, hw] at hright
      simp at hright
    subst i
    subst j
    have hdeF : de ≠ df := haxes
    have hbaseEde : (Currents.base e de).val = nj.val := by
      have hpEq : e.1 de = Sum.inr nj := by
        calc
          e.1 de = p.1 de := (hOtherE de hdeF).symm
          _ = Sum.inr nj := hPjF
      simp [geometryBase_val_eq_linkBaseCoordinate, linkBaseCoordinate, hpEq]
    have hbaseFde : (Currents.base f de).val = vj.val + 1 := by
      simp [geometryBase_val_eq_linkBaseCoordinate, linkBaseCoordinate, hFj]
    have hbaseFdf : (Currents.base f df).val = ni.val := by
      have hdfde : df ≠ de := by intro h; exact hdeF h.symm
      have hpEq : f.1 df = Sum.inr ni := by
        calc
          f.1 df = p.1 df := (hOtherF df hdfde).symm
          _ = Sum.inr ni := hPiE
      simp [geometryBase_val_eq_linkBaseCoordinate, linkBaseCoordinate, hpEq]
    have hbaseEdf : (Currents.base e df).val = vi.val + 1 := by
      simp [geometryBase_val_eq_linkBaseCoordinate, linkBaseCoordinate, hEi]
    have heEndCoord : ∃ be : Bool,
        endpointParam e be = (Currents.base f de).val := by
      rcases hSideF with hflo | hfhi
      · refine ⟨true, ?_⟩
        rw [endpointParam_formula, hAxisLinkE]
        simp
        rw [hbaseEde, hbaseFde]
        exact_mod_cast congrArg Nat.succ hflo
      · refine ⟨false, ?_⟩
        rw [endpointParam_formula, hAxisLinkE]
        simp
        rw [hbaseEde, hbaseFde]
        exact_mod_cast hfhi
    have hfEndCoord : ∃ bf : Bool,
        endpointParam f bf = (Currents.base e df).val := by
      rcases hSideE with helo | hehi
      · refine ⟨true, ?_⟩
        rw [endpointParam_formula, hAxisLinkF]
        simp
        rw [hbaseFdf, hbaseEdf]
        exact_mod_cast congrArg Nat.succ helo
      · refine ⟨false, ?_⟩
        rw [endpointParam_formula, hAxisLinkF]
        simp
        rw [hbaseFdf, hbaseEdf]
        exact_mod_cast hehi
    obtain ⟨be, hbe⟩ := heEndCoord
    obtain ⟨bf, hbf⟩ := hfEndCoord
    have hpoints : endpointPoint e be = endpointPoint f bf := by
      apply congrArg (WithLp.toLp 2)
      funext k
      change endpointPoint e be k = endpointPoint f bf k
      rw [endpointPoint_coord, endpointPoint_coord]
      by_cases hke : k = de
      · subst k
        simp [hAxisLinkE, hAxisLinkF, hdeF, hbe]
      · by_cases hkf : k = df
        · subst k
          have hdfE : df ≠ de := by
            intro h
            exact hdeF h.symm
          simp [hAxisLinkE, hAxisLinkF, hdfE, hbf]
        · have hcell : e.1 k = f.1 k := by
            have hkdf : k ≠ df := hkf
            have hkde : k ≠ de := hke
            calc
              e.1 k = p.1 k := (hOtherE k (by simpa [df] using hkdf)).symm
              _ = f.1 k := hOtherF k (by simpa [de] using hkde)
          have hb := sourceBase_eq_of_cellCoord_eq e f k hcell
          simp [hAxisLinkE, hAxisLinkF, hke, hkf, hb]
    have hle := linkDistance_le_dist e f (endpointPoint_mem e be)
      (endpointPoint_mem f bf)
    rw [hpoints, dist_self] at hle
    have hnonneg := linkDistance_nonneg e f
    rw [le_antisymm hle hnonneg]
    exact lt_of_le_of_lt (by norm_num : (0 : ℝ) ≤ 0)
      (Real.sqrt_pos.2 (by norm_num))


end FroehlichSpencer.FS82.Currents.PlaquetteDistance

end
