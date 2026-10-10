/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAPotential

/-!
# Shortcut decomposition of a collapsed lattice path (TWC)

For a family `𝓔` of collapsed sets, the **free steps** are the lattice steps with both ends in one
set of `𝓔` (`profileFreeGraph`), and the **zero-cost components** are the classes of the
free-step reachability relation (`collapsedComponent`). A lattice path is a list of sites with
consecutive `ℓ¹` distance one; its paid length is `pathCost` (the steps that are not free).

`exists_collapsedPathData`, the shortcut decomposition: let `δ` bound the Euclidean diameter of
every component. Then every lattice path from `a` to `b` has a finite set `V` of components it
visits, with positions `pos`, such that:

* `eucl(a, b) ≤ cost + Σ_{C ∈ V} δ C`;
* `0 ≤ pos C` and `pos C + δ C ≤ cost + Σ_V δ`;
* each `C ∈ V` has a point within `pos C` of `a`;
* two distinct `C, C' ∈ V` have points within `|pos C − pos C'|` of each other.

The proof enters the first collapsed site's component `C`, jumps to the last visit of `C` (the
displacement inside costs at most `δ C`), leaves `C` by a paid step (a free step would stay in
`C`), and recurses on the rest, which never returns to `C`. No minimality of the path is used.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-! ## Free steps and zero-cost components -/

/-- A site lies in some collapsed set. -/
def InCollapsed (𝓔 : Finset (Finset (Site L))) (y : Site L) : Prop := ∃ E ∈ 𝓔, y ∈ E

instance (𝓔 : Finset (Finset (Site L))) (y : Site L) : Decidable (InCollapsed 𝓔 y) := by
  unfold InCollapsed
  infer_instance

theorem inCollapsed_left {𝓔 : Finset (Finset (Site L))} {x y : Site L}
    (h : IsCollapsedStep 𝓔 x y) : InCollapsed 𝓔 x := by
  obtain ⟨E, hE, hx, -⟩ := h
  exact ⟨E, hE, hx⟩

/-- The free-step graph: lattice steps with both ends in one collapsed set. -/
def profileFreeGraph (𝓔 : Finset (Finset (Site L))) : SimpleGraph (Site L) where
  Adj x y := l1 x y = 1 ∧ IsCollapsedStep 𝓔 x y
  symm := ⟨fun x y h => ⟨by rw [l1_comm]; exact h.1, by
    obtain ⟨E, hE, hx, hy⟩ := h.2
    exact ⟨E, hE, hy, hx⟩⟩⟩
  loopless := ⟨fun x h => by have := h.1; rw [l1_self] at this; exact absurd this (by norm_num)⟩

/-- The zero-cost component of a site: the sites free-reachable from it. -/
def collapsedComponent (𝓔 : Finset (Finset (Site L))) (y : Site L) : Finset (Site L) := by
  classical
  exact Finset.univ.filter fun z => (profileFreeGraph 𝓔).Reachable y z

theorem mem_collapsedComponent {𝓔 : Finset (Finset (Site L))} {y z : Site L} :
    z ∈ collapsedComponent 𝓔 y ↔ (profileFreeGraph 𝓔).Reachable y z := by
  classical
  unfold collapsedComponent
  simp

theorem mem_collapsedComponent_self (𝓔 : Finset (Finset (Site L))) (y : Site L) :
    y ∈ collapsedComponent 𝓔 y :=
  mem_collapsedComponent.mpr SimpleGraph.Reachable.rfl

theorem collapsedComponent_eq_of_mem {𝓔 : Finset (Finset (Site L))} {y z : Site L}
    (h : z ∈ collapsedComponent 𝓔 y) : collapsedComponent 𝓔 z = collapsedComponent 𝓔 y := by
  have hyz := mem_collapsedComponent.mp h
  ext w
  rw [mem_collapsedComponent, mem_collapsedComponent]
  exact ⟨fun hzw => hyz.trans hzw, fun hyw => hyz.symm.trans hyw⟩

/-- Distinct components are disjoint. -/
theorem disjoint_collapsedComponent {𝓔 : Finset (Finset (Site L))} {y y' : Site L}
    (hne : collapsedComponent 𝓔 y ≠ collapsedComponent 𝓔 y') :
    Disjoint (collapsedComponent 𝓔 y) (collapsedComponent 𝓔 y') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hne ((collapsedComponent_eq_of_mem hz).symm.trans (collapsedComponent_eq_of_mem hz'))

/-! ## Lattice paths and their paid length -/

/-- The paid length of a list of sites: its consecutive pairs that are not free steps. -/
def pathCost (𝓔 : Finset (Finset (Site L))) : List (Site L) → ℕ
  | a :: b :: rest => (if IsCollapsedStep 𝓔 a b then 0 else 1) + pathCost 𝓔 (b :: rest)
  | _ => 0

@[simp] theorem pathCost_nil (𝓔 : Finset (Finset (Site L))) : pathCost 𝓔 [] = 0 := rfl

@[simp] theorem pathCost_singleton (𝓔 : Finset (Finset (Site L))) (a : Site L) :
    pathCost 𝓔 [a] = 0 := rfl

theorem pathCost_cons_cons (𝓔 : Finset (Finset (Site L))) (a b : Site L) (rest : List (Site L)) :
    pathCost 𝓔 (a :: b :: rest) =
      (if IsCollapsedStep 𝓔 a b then 0 else 1) + pathCost 𝓔 (b :: rest) := rfl

theorem ite_paid {𝓔 : Finset (Finset (Site L))} {a b : Site L} (h : ¬ IsCollapsedStep 𝓔 a b) :
    (if IsCollapsedStep 𝓔 a b then 0 else 1 : ℕ) = 1 := by
  simp [h]

/-- The paid length splits at an interior site. -/
theorem pathCost_append_cons (𝓔 : Finset (Finset (Site L))) (xs : List (Site L)) (y : Site L)
    (ys : List (Site L)) :
    pathCost 𝓔 (xs ++ y :: ys) = pathCost 𝓔 (xs ++ [y]) + pathCost 𝓔 (y :: ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp [pathCost_cons_cons]
    | cons x' xs'' =>
      simp only [List.cons_append] at ih ⊢
      rw [pathCost_cons_cons, pathCost_cons_cons, ih]
      ring

/-- Away from the collapsed sets every step is paid. -/
theorem pathCost_append_singleton_of_not {𝓔 : Finset (Finset (Site L))} (pre : List (Site L))
    (u : Site L) (h : ∀ z ∈ pre, ¬ InCollapsed 𝓔 z) : pathCost 𝓔 (pre ++ [u]) = pre.length := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have ha : ¬ InCollapsed 𝓔 a := h a (List.mem_cons_self ..)
    have ih' := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    cases pre with
    | nil =>
      simp only [List.cons_append, List.nil_append, pathCost_cons_cons, pathCost_singleton]
      rw [ite_paid fun hc => ha (inCollapsed_left hc)]
      simp
    | cons b pre' =>
      simp only [List.cons_append] at ih' ⊢
      rw [pathCost_cons_cons, ite_paid fun hc => ha (inCollapsed_left hc), ih']
      simp only [List.length_cons]
      ring

theorem pathCost_eq_length_of_not {𝓔 : Finset (Finset (Site L))} (l : List (Site L))
    (a : Site L) (h : ∀ z ∈ a :: l, ¬ InCollapsed 𝓔 z) : pathCost 𝓔 (a :: l) = l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have ha : ¬ InCollapsed 𝓔 a := h a (List.mem_cons_self ..)
    rw [pathCost_cons_cons, ite_paid fun hc => ha (inCollapsed_left hc),
      ih b fun z hz => h z (List.mem_cons_of_mem _ hz)]
    simp only [List.length_cons]
    ring

/-- A lattice path moves at most one Euclidean unit per step. -/
theorem siteDist_le_length_of_isChain (l : List (Site L)) (a b : Site L)
    (hc : List.IsChain (fun x y => l1 x y = 1) (a :: l)) (hb : (a :: l).getLast? = some b) :
    euclideanSiteDistance a b ≤ l.length := by
  induction l generalizing a with
  | nil =>
    simp only [List.getLast?_singleton, Option.some.injEq] at hb
    subst hb
    rw [siteDist_self]
    simp
  | cons c l ih =>
    rw [List.isChain_cons_cons] at hc
    have hb' : (c :: l).getLast? = some b := by
      rw [List.getLast?_cons_cons] at hb
      exact hb
    have h1 := ih c hc.2 hb'
    have h2 : euclideanSiteDistance a c ≤ 1 := by
      have := siteDist_le_l1 a c
      rw [hc.1] at this
      simpa using this
    have h3 := euclideanSiteDistance_triangle a c b
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem getLast?_append_cons {α : Type*} (xs : List α) (y : α) (ys : List α) :
    (xs ++ y :: ys).getLast? = (y :: ys).getLast? := by
  rw [List.getLast?_append, List.getLast?_eq_some_getLast (List.cons_ne_nil y ys), Option.some_or]

/-! ## Splitting a list at its first and last marked element -/

theorem exists_split_first {α : Type*} (P : α → Prop) [DecidablePred P] :
    ∀ l : List α, (∃ y ∈ l, P y) →
      ∃ pre u post, l = pre ++ u :: post ∧ P u ∧ ∀ z ∈ pre, ¬ P z
  | [], h => by obtain ⟨y, hy, -⟩ := h; simp at hy
  | a :: l, h => by
    by_cases ha : P a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · have h' : ∃ y ∈ l, P y := by
        obtain ⟨y, hy, hPy⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd hPy ha
        · exact ⟨y, hy, hPy⟩
      obtain ⟨pre, u, post, rfl, hu, hpre⟩ := exists_split_first P l h'
      refine ⟨a :: pre, u, post, rfl, hu, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      · exact hpre z hz

theorem exists_split_last {α : Type*} (P : α → Prop) [DecidablePred P] :
    ∀ l : List α, (∃ y ∈ l, P y) →
      ∃ pre u post, l = pre ++ u :: post ∧ P u ∧ ∀ z ∈ post, ¬ P z
  | [], h => by obtain ⟨y, hy, -⟩ := h; simp at hy
  | a :: l, h => by
    by_cases h' : ∃ y ∈ l, P y
    · obtain ⟨pre, u, post, rfl, hu, hpost⟩ := exists_split_last P l h'
      exact ⟨a :: pre, u, post, rfl, hu, hpost⟩
    · push Not at h'
      have ha : P a := by
        obtain ⟨y, hy, hPy⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hPy
        · exact absurd hPy (h' y hy)
      exact ⟨[], a, l, rfl, ha, h'⟩

/-! ## The shortcut decomposition -/

/-- **The shortcut decomposition of a lattice path.** -/
theorem exists_collapsedPathData (𝓔 : Finset (Finset (Site L))) (δ : Finset (Site L) → ℝ)
    (hδ : ∀ y, InCollapsed 𝓔 y → 0 ≤ δ (collapsedComponent 𝓔 y) ∧
      ∀ z ∈ collapsedComponent 𝓔 y, ∀ z' ∈ collapsedComponent 𝓔 y,
        euclideanSiteDistance z z' ≤ δ (collapsedComponent 𝓔 y)) :
    ∀ (l : List (Site L)) (a b : Site L), List.IsChain (fun x y => l1 x y = 1) (a :: l) →
      (a :: l).getLast? = some b →
      ∃ (V : Finset (Finset (Site L))) (pos : Finset (Site L) → ℝ),
        (∀ C ∈ V, ∃ y ∈ a :: l, InCollapsed 𝓔 y ∧ C = collapsedComponent 𝓔 y) ∧
        euclideanSiteDistance a b ≤ pathCost 𝓔 (a :: l) + ∑ C ∈ V, δ C ∧
        (∀ C ∈ V, 0 ≤ pos C ∧ pos C + δ C ≤ pathCost 𝓔 (a :: l) + ∑ C ∈ V, δ C) ∧
        (∀ C ∈ V, ∃ u ∈ C, euclideanSiteDistance a u ≤ pos C) ∧
        (∀ C ∈ V, ∀ C' ∈ V, C ≠ C' →
          ∃ u ∈ C, ∃ u' ∈ C', euclideanSiteDistance u u' ≤ |pos C - pos C'|) := by
  classical
  intro l
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  intro a b hc hb
  by_cases hE : ∃ y ∈ a :: l, InCollapsed 𝓔 y
  swap
  · -- no collapsed site: every step is paid
    push Not at hE
    refine ⟨∅, fun _ => 0, by simp, ?_, by simp, by simp, by simp⟩
    rw [pathCost_eq_length_of_not l a hE, Finset.sum_empty, add_zero]
    exact siteDist_le_length_of_isChain l a b hc hb
  -- the first collapsed site `u` and its component `C`
  obtain ⟨pre, u, mid, hsplit, hu, hpre⟩ := exists_split_first (InCollapsed 𝓔) (a :: l) hE
  set C := collapsedComponent 𝓔 u with hCdef
  obtain ⟨hδC, hδdiam⟩ := hδ u hu
  -- the last visit `u'` of `C`
  obtain ⟨pre2, u', post, hsplit2, hu', hpost⟩ :=
    exists_split_last (· ∈ C) (u :: mid) ⟨u, List.mem_cons_self .., mem_collapsedComponent_self 𝓔 u⟩
  have hfull : a :: l = (pre ++ pre2) ++ u' :: post := by rw [hsplit, hsplit2, List.append_assoc]
  -- the prefix up to `u`
  have hpreDist : euclideanSiteDistance a u ≤ pre.length := by
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      rw [hsplit.1, siteDist_self]; simp
    | cons p₀ pre' =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨hpa, hl⟩ := hsplit
      subst hpa
      have hc' : List.IsChain (fun x y => l1 x y = 1) (a :: (pre' ++ [u])) := by
        have hc2 := hc
        rw [hl, show a :: (pre' ++ u :: mid) = (a :: (pre' ++ [u])) ++ mid by simp] at hc2
        exact hc2.left_of_append
      have hlast : (a :: (pre' ++ [u])).getLast? = some u := by
        rw [show a :: (pre' ++ [u]) = (a :: pre') ++ [u] by simp, getLast?_append_cons]
        rfl
      have := siteDist_le_length_of_isChain (pre' ++ [u]) a u hc' hlast
      simpa using this
  have hcostPre : pathCost 𝓔 (pre ++ [u]) = pre.length :=
    pathCost_append_singleton_of_not pre u hpre
  have hcostSplit : pathCost 𝓔 (a :: l) =
      pre.length + pathCost 𝓔 (pre2 ++ [u']) + pathCost 𝓔 (u' :: post) := by
    rw [hsplit, pathCost_append_cons, hcostPre, hsplit2, pathCost_append_cons]
    ring
  have huu' : euclideanSiteDistance u u' ≤ δ C :=
    hδdiam u (mem_collapsedComponent_self 𝓔 u) u' hu'
  have hlenFull : l.length + 1 = pre.length + pre2.length + 1 + post.length := by
    have := congrArg List.length hfull
    simp only [List.length_cons, List.length_append] at this
    omega
  have huFull : u ∈ a :: l := by rw [hsplit]; simp
  cases post with
  | nil =>
    -- the path ends in `C`
    have hbu : b = u' := by
      rw [hfull, getLast?_append_cons] at hb
      simp only [List.getLast?_singleton, Option.some.injEq] at hb
      exact hb.symm
    subst hbu
    refine ⟨{C}, fun _ => (pre.length : ℝ), ?_, ?_, ?_, ?_, ?_⟩
    · intro C' hC'
      rw [Finset.mem_singleton.mp hC']
      exact ⟨u, huFull, hu, rfl⟩
    · rw [Finset.sum_singleton]
      have h1 := euclideanSiteDistance_triangle a u b
      have : (pre.length : ℝ) ≤ pathCost 𝓔 (a :: l) := by exact_mod_cast (by omega :
        pre.length ≤ pathCost 𝓔 (a :: l))
      linarith
    · intro C' hC'
      rw [Finset.mem_singleton.mp hC', Finset.sum_singleton]
      have : (pre.length : ℝ) ≤ pathCost 𝓔 (a :: l) := by exact_mod_cast (by omega :
        pre.length ≤ pathCost 𝓔 (a :: l))
      exact ⟨Nat.cast_nonneg _, by linarith⟩
    · intro C' hC'
      rw [Finset.mem_singleton.mp hC']
      exact ⟨u, mem_collapsedComponent_self 𝓔 u, hpreDist⟩
    · intro C₁ h₁ C₂ h₂ hne
      exact absurd ((Finset.mem_singleton.mp h₁).trans (Finset.mem_singleton.mp h₂).symm) hne
  | cons p post' =>
    -- the exit step is paid, and the rest never returns to `C`
    have hcTail : List.IsChain (fun x y => l1 x y = 1) (u' :: p :: post') := by
      have hc2 := hc
      rw [hfull] at hc2
      exact hc2.right_of_append
    have hup : l1 u' p = 1 := (List.isChain_cons_cons.mp hcTail).1
    have hpC : p ∉ C := hpost p (List.mem_cons_self ..)
    have hpaid : ¬ IsCollapsedStep 𝓔 u' p := by
      intro hcol
      apply hpC
      exact mem_collapsedComponent.mpr
        ((mem_collapsedComponent.mp hu').trans (SimpleGraph.Adj.reachable ⟨hup, hcol⟩))
    have hcostExit : pathCost 𝓔 (u' :: p :: post') = 1 + pathCost 𝓔 (p :: post') := by
      rw [pathCost_cons_cons, ite_paid hpaid]
    have hcostGe : (pre.length : ℝ) + 1 + pathCost 𝓔 (p :: post') ≤ pathCost 𝓔 (a :: l) := by
      have : pre.length + 1 + pathCost 𝓔 (p :: post') ≤ pathCost 𝓔 (a :: l) := by
        rw [hcostSplit, hcostExit]; omega
      exact_mod_cast this
    have hbp : (p :: post').getLast? = some b := by
      rw [hfull, getLast?_append_cons, List.getLast?_cons_cons] at hb
      exact hb
    obtain ⟨V'', pos'', hV1, hV2, hV3, hV4, hV5⟩ :=
      ih post'.length (by have := hlenFull; simp only [List.length_cons] at this; omega)
        post' rfl p b (List.isChain_cons_cons.mp hcTail).2 hbp
    have hCV : C ∉ V'' := by
      intro hC
      obtain ⟨y, hy, -, hyC⟩ := hV1 C hC
      have hyC' : y ∈ C := by rw [hyC]; exact mem_collapsedComponent_self 𝓔 y
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hpC hyC'
      · exact hpost y (List.mem_cons_of_mem _ hy) hyC'
    have hu'p : euclideanSiteDistance u' p ≤ 1 := by
      have := siteDist_le_l1 u' p
      rw [hup] at this
      simpa using this
    set pos : Finset (Site L) → ℝ := fun C₀ =>
      if C₀ = C then (pre.length : ℝ) else pre.length + δ C + 1 + pos'' C₀ with hpos
    have hposC : pos C = pre.length := by simp [hpos]
    have hposV : ∀ C₀ ∈ V'', pos C₀ = pre.length + δ C + 1 + pos'' C₀ := by
      intro C₀ hC₀
      have : C₀ ≠ C := fun h => hCV (h ▸ hC₀)
      simp [hpos, this]
    have hsum : ∑ C₀ ∈ insert C V'', δ C₀ = δ C + ∑ C₀ ∈ V'', δ C₀ := Finset.sum_insert hCV
    have hpreNN : (0 : ℝ) ≤ pre.length := Nat.cast_nonneg _
    refine ⟨insert C V'', pos, ?_, ?_, ?_, ?_, ?_⟩
    · intro C₀ hC₀
      rcases Finset.mem_insert.mp hC₀ with rfl | hC₀
      · exact ⟨u, huFull, hu, rfl⟩
      · obtain ⟨y, hy, hyE, hyC⟩ := hV1 C₀ hC₀
        refine ⟨y, ?_, hyE, hyC⟩
        rw [hfull]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
    · rw [hsum]
      have h1 := euclideanSiteDistance_triangle a u b
      have h2 := euclideanSiteDistance_triangle u u' b
      have h3 := euclideanSiteDistance_triangle u' p b
      linarith
    · intro C₀ hC₀
      rw [hsum]
      rcases Finset.mem_insert.mp hC₀ with rfl | hC₀
      · rw [hposC]
        have := Finset.sum_nonneg fun C₁ (h : C₁ ∈ V'') => (hV3 C₁ h).1
        have h4 : ∀ C₁ ∈ V'', 0 ≤ δ C₁ := fun C₁ h => by
          obtain ⟨y, -, hyE, hyC⟩ := hV1 C₁ h
          rw [hyC]; exact (hδ y hyE).1
        have := Finset.sum_nonneg h4
        have : (0 : ℝ) ≤ pathCost 𝓔 (p :: post') := Nat.cast_nonneg _
        exact ⟨hpreNN, by linarith⟩
      · rw [hposV C₀ hC₀]
        obtain ⟨h5, h6⟩ := hV3 C₀ hC₀
        exact ⟨by linarith, by linarith⟩
    · intro C₀ hC₀
      rcases Finset.mem_insert.mp hC₀ with rfl | hC₀
      · exact ⟨u, mem_collapsedComponent_self 𝓔 u, by rw [hposC]; exact hpreDist⟩
      · obtain ⟨y, hy, hpy⟩ := hV4 C₀ hC₀
        refine ⟨y, hy, ?_⟩
        rw [hposV C₀ hC₀]
        have h1 := euclideanSiteDistance_triangle a u y
        have h2 := euclideanSiteDistance_triangle u u' y
        have h3 := euclideanSiteDistance_triangle u' p y
        linarith
    · -- the exit point of `C` against the entry points of the later components
      have hCfirst : ∀ C₀ ∈ V'', ∃ v ∈ C, ∃ v' ∈ C₀,
          euclideanSiteDistance v v' ≤ |pos C - pos C₀| := by
        intro C₀ hC₀
        obtain ⟨y, hy, hpy⟩ := hV4 C₀ hC₀
        refine ⟨u', hu', y, hy, ?_⟩
        rw [hposC, hposV C₀ hC₀, abs_sub_comm]
        have h1 := euclideanSiteDistance_triangle u' p y
        have hpos'' := (hV3 C₀ hC₀).1
        rw [abs_of_nonneg (by linarith)]
        linarith
      intro C₁ h₁ C₂ h₂ hne
      rcases Finset.mem_insert.mp h₁ with rfl | h₁ <;> rcases Finset.mem_insert.mp h₂ with rfl | h₂
      · exact absurd rfl hne
      · exact hCfirst C₂ h₂
      · obtain ⟨v, hv, v', hv', hd⟩ := hCfirst C₁ h₁
        refine ⟨v', hv', v, hv, ?_⟩
        rw [siteDist_comm, abs_sub_comm]
        exact hd
      · obtain ⟨v, hv, v', hv', hd⟩ := hV5 C₁ h₁ C₂ h₂ hne
        refine ⟨v, hv, v', hv', ?_⟩
        rw [hposV C₁ h₁, hposV C₂ h₂]
        have : pre.length + δ C + 1 + pos'' C₁ - (pre.length + δ C + 1 + pos'' C₂) =
          pos'' C₁ - pos'' C₂ := by ring
        rw [this]
        exact hd

/-! ## Walks as lattice paths -/

theorem isChain_support {x y : Site L} (w : (profileLattice L).Walk x y) :
    List.IsChain (fun a b => l1 a b = 1) w.support :=
  w.isChain_adj_support

theorem support_eq_cons_tail {x y : Site L} (w : (profileLattice L).Walk x y) :
    w.support = x :: w.support.tail :=
  w.cons_tail_support.symm

theorem getLast?_support {x y : Site L} (w : (profileLattice L).Walk x y) :
    w.support.getLast? = some y := by
  rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil w),
    SimpleGraph.Walk.getLast_support]

/-- The paid length of a walk is the paid length of its support. -/
theorem collapsedCost_eq_pathCost (𝓔 : Finset (Finset (Site L))) {x y : Site L}
    (w : (profileLattice L).Walk x y) : collapsedCost 𝓔 w = pathCost 𝓔 w.support := by
  induction w with
  | nil => simp [collapsedCost]
  | cons h p ih =>
    rename_i a b c
    rw [SimpleGraph.Walk.support_cons, support_eq_cons_tail p, pathCost_cons_cons,
      ← support_eq_cons_tail p, ← ih]
    unfold collapsedCost
    rw [SimpleGraph.Walk.darts_cons, List.countP_cons]
    by_cases hc : IsCollapsedStep 𝓔 a b <;> simp [hc, add_comm]

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
