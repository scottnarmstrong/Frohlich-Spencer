/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Regions
public import FroehlichSpencer.T12.InductionDefs
public import FroehlichSpencer.T12.Annuli

/-!
# The first-exit cases

(The low radial cut itself is
`exists_lowCut` in `FroehlichSpencer.T12.Regions`.)
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

/-- A lattice walk from `y ∉ R` toward `a ∈ R` leaves `R` through a vertex of `∂ᵥR` within
`ρ ≥ |a − y|` of `a`. -/
theorem exists_boundary_near {ν : ℕ} {R : Set (Site ν)} {a y : Site ν} {ρ : ℝ} (ha : a ∈ R)
    (hy : y ∉ R) (hρ : siteDist ν a y ≤ ρ) :
    ∃ u ∈ vertexBoundary R, siteDist ν a u ≤ ρ := by
  have key : ∀ (m : ℕ) (y : Site ν), ∑ j, (y j - a j).natAbs ≤ m → y ∉ R →
      siteDist ν a y ≤ ρ → ∃ u ∈ vertexBoundary R, siteDist ν a u ≤ ρ := by
    intro m
    induction m with
    | zero =>
      intro y hm hy hd
      by_cases hya : y = a
      · exact absurd (hya ▸ ha) hy
      · obtain ⟨y', -, -, h3⟩ := exists_step a y hya
        omega
    | succ m ih =>
      intro y hm hy hd
      by_cases hya : y = a
      · exact absurd (hya ▸ ha) hy
      · obtain ⟨y', h1, h2, h3⟩ := exists_step a y hya
        by_cases hy'R : y' ∈ R
        · exact ⟨y', ⟨hy'R, y, h1, hy⟩, h2.trans hd⟩
        · exact ih y' (by omega) hy'R (h2.trans hd)
  exact key _ y le_rfl hy hρ


theorem firstExit_cases {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (k : ℕ) {R : Set (Site ν)}
    (hRadm : Admissible P.K₀ (restrictedClasses P Λ v) (k + 1) R)
    (hRdiam : DiamLE (siteDist ν) R (3 * scaleD P.K₀ (k + 1) / 2))
    (hRS : ∀ x ∈ R, x ∉ singularSetsIn P Λ v (k + 1)) :
    (∀ x ∈ R, x ∉ singularSetsIn P Λ v k) ∨
      ∃ C ∈ restrictedClasses P Λ v k, nbhd C (4 * scaleD P.K₀ k) ⊆ R ∧
        ∀ x ∈ R, x ∈ singularSetsIn P Λ v k → x ∈ C := by
  by_cases h : ∀ x ∈ R, x ∉ singularSetsIn P Λ v k
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨x, hxR, hxS⟩ := h
  have hD := scaleD_pos P.K₀ k
  have hD1 := scaleD_pos P.K₀ (k + 1)
  have hg : IsGentle P (fun B => B ∩ Λ) k v
      (chainCluster (siteDist ν) (singularSetsIn P Λ v k) (2 * scaleR P.K₀ k) x) := by
    by_contra hng
    exact hRS x hxR
      ((mem_singularSetsGen_succ_iff P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v k x).2 ⟨hxS, hng⟩)
  set C := chainCluster (siteDist ν) (singularSetsIn P Λ v k) (2 * scaleR P.K₀ k) x with hCdef
  have hCcls : C ∈ restrictedClasses P Λ v k := ⟨⟨x, hxS, rfl⟩, hg⟩
  have hxC : x ∈ C := mem_chainCluster_self hxS
  obtain ⟨-, hdiamC, -⟩ := hg
  have hall : ∀ x' ∈ R, x' ∈ singularSetsIn P Λ v k → x' ∈ C := by
    intro x' hx'R hx'S
    refine mem_chainCluster_of_lt hxC hx'S ?_
    have := hRdiam x hxR x' hx'R
    rw [scaleR_eq_scaleD_succ]
    linarith
  refine ⟨C, hCcls, ?_, hall⟩
  have hbd : ∀ {a z : Site ν}, a ∈ C → a ∈ R → z ∉ R →
      siteDist ν a z ≤ 4 * scaleD P.K₀ k → False := by
    intro a z haC haR hzR hd
    obtain ⟨u, hu, hau⟩ := exists_boundary_near haR hzR hd
    exact Set.disjoint_left.1 (hRadm k (Nat.lt_succ_self k) C hCcls) hu
      ⟨a, haC, by rw [siteDist_comm]; exact hau⟩
  rintro y ⟨c, hc, hyc⟩
  have hcx : siteDist ν c x ≤ scaleD P.K₀ k := hdiamC c hc x hxC
  have hcR : c ∈ R := by
    by_contra hcR
    exact hbd hxC hxR hcR (by rw [siteDist_comm]; linarith)
  by_contra hyR
  exact hbd hc hcR hyR (by rw [siteDist_comm]; exact hyc)


theorem lowCut_interface_sep {ν : ℕ} {C B : Set (Site ν)} {d : ℝ} (hd : 3 / 2 ≤ d)
    (hB : B ⊆ nbhd C (d / 3)) {b q c' : Site ν} (hb : b ∈ B) (hq : siteDist ν q b ≤ 1)
    (hc' : c' ∉ nbhd C (4 * d)) : 3 * d ≤ siteDist ν c' q := by
  obtain ⟨c, hc, hbc⟩ := hB hb
  have hfar : 4 * d < siteDist ν c' c := by
    by_contra h
    exact hc' ⟨c, hc, not_lt.1 h⟩
  have h1 := siteDist_triangle ν c' c q
  have h2 := siteDist_triangle ν q c b
  linarith

end FroehlichSpencer.T12

end
