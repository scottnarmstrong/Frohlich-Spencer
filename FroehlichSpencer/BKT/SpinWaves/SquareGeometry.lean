/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SquareCarriers
public import FroehlichSpencer.BKT.SpinWaves.Initial
public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import FroehlichSpencer.BKT.Lattice2D.Torus

/-! # Square spin-wave geometry

The square-lattice bipartition is the parity of the sum of the coordinates (KP p. 2).
The free-square proof uses the canonical positive-step classification from `Bridge.SquareCarriers`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

private theorem squareFree_source_count_le_two {L : ℕ} (p : Fin L × Fin L) :
    (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge L =>
      (Lattice2D.squareFreeGraph L).src e = p).card ≤ 2 := by
  classical
  let code : {e : Lattice2D.SquareFreeEdge L //
      (Lattice2D.squareFreeGraph L).src e = p} → Bool := fun x =>
    match x.1 with
    | .inl _ => false
    | .inr _ => true
  have hinj : Function.Injective code := by
    intro x y hxy
    rcases x with ⟨ex, hx⟩
    rcases y with ⟨ey, hy⟩
    apply Subtype.ext
    cases ex with
    | inl ex =>
      cases ey with
      | inl ey =>
        have hx' : (ex.1.1, ex.2) = p := by simpa [Lattice2D.squareFreeGraph] using hx
        have hy' : (ey.1.1, ey.2) = p := by simpa [Lattice2D.squareFreeGraph] using hy
        have h1 : ex.1.1 = ey.1.1 := (congrArg Prod.fst hx').trans (congrArg Prod.fst hy').symm
        have h2 : ex.2 = ey.2 := (congrArg Prod.snd hx').trans (congrArg Prod.snd hy').symm
        have hp : ex = ey := Prod.ext (Subtype.ext h1) h2
        subst ey
        rfl
      | inr ey => simp [code] at hxy
    | inr ex =>
      cases ey with
      | inl ey => simp [code] at hxy
      | inr ey =>
        have hx' : (ex.1, ex.2.1) = p := by simpa [Lattice2D.squareFreeGraph] using hx
        have hy' : (ey.1, ey.2.1) = p := by simpa [Lattice2D.squareFreeGraph] using hy
        have h1 : ex.1 = ey.1 := (congrArg Prod.fst hx').trans (congrArg Prod.fst hy').symm
        have h2 : ex.2.1 = ey.2.1 := (congrArg Prod.snd hx').trans (congrArg Prod.snd hy').symm
        have hp : ex = ey := Prod.ext h1 (Subtype.ext h2)
        subst ey
        rfl
  have hcard : Fintype.card {e : Lattice2D.SquareFreeEdge L //
      (Lattice2D.squareFreeGraph L).src e = p} ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective code hinj
  have hcard' : Fintype.card {e : Lattice2D.SquareFreeEdge L //
      (Lattice2D.squareFreeGraph L).src e = p} =
      (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge L =>
        (Lattice2D.squareFreeGraph L).src e = p).card := by
    exact Fintype.card_subtype
      (fun e : Lattice2D.SquareFreeEdge L =>
        (Lattice2D.squareFreeGraph L).src e = p)
  rw [hcard'] at hcard
  exact hcard.trans_eq Fintype.card_bool

private theorem squareFree_target_count_le_two {L : ℕ} (p : Fin L × Fin L) :
    (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge L =>
      (Lattice2D.squareFreeGraph L).tgt e = p).card ≤ 2 := by
  classical
  let code : {e : Lattice2D.SquareFreeEdge L //
      (Lattice2D.squareFreeGraph L).tgt e = p} → Bool := fun x =>
    match x.1 with
    | .inl _ => false
    | .inr _ => true
  have hinj : Function.Injective code := by
    intro x y hxy
    rcases x with ⟨ex, hx⟩
    rcases y with ⟨ey, hy⟩
    apply Subtype.ext
    cases ex with
    | inl ex =>
      cases ey with
      | inl ey =>
        have hx' : ((⟨ex.1.1.val + 1, ex.1.property⟩ : Fin L), ex.2) = p := by
          simpa [Lattice2D.squareFreeGraph] using hx
        have hy' : ((⟨ey.1.1.val + 1, ey.1.property⟩ : Fin L), ey.2) = p := by
          simpa [Lattice2D.squareFreeGraph] using hy
        have hxval : ex.1.1.val + 1 = p.1.val := by
          simpa using congrArg (fun z : Fin L × Fin L => z.1.val) hx'
        have hyval : ey.1.1.val + 1 = p.1.val := by
          simpa using congrArg (fun z : Fin L × Fin L => z.1.val) hy'
        have h1val : ex.1.1.val = ey.1.1.val :=
          Nat.add_right_cancel (hxval.trans hyval.symm)
        have h1 : ex.1.1 = ey.1.1 := Fin.ext h1val
        have h2 : ex.2 = ey.2 := (congrArg Prod.snd hx').trans (congrArg Prod.snd hy').symm
        have hp : ex = ey := Prod.ext (Subtype.ext h1) h2
        subst ey
        rfl
      | inr ey => simp [code] at hxy
    | inr ex =>
      cases ey with
      | inl ey => simp [code] at hxy
      | inr ey =>
        have hx' : (ex.1, (⟨ex.2.1.val + 1, ex.2.property⟩ : Fin L)) = p := by
          simpa [Lattice2D.squareFreeGraph] using hx
        have hy' : (ey.1, (⟨ey.2.1.val + 1, ey.2.property⟩ : Fin L)) = p := by
          simpa [Lattice2D.squareFreeGraph] using hy
        have h1 : ex.1 = ey.1 := (congrArg Prod.fst hx').trans (congrArg Prod.fst hy').symm
        have hxval : ex.2.1.val + 1 = p.2.val := by
          simpa using congrArg (fun z : Fin L × Fin L => z.2.val) hx'
        have hyval : ey.2.1.val + 1 = p.2.val := by
          simpa using congrArg (fun z : Fin L × Fin L => z.2.val) hy'
        have h2val : ex.2.1.val = ey.2.1.val :=
          Nat.add_right_cancel (hxval.trans hyval.symm)
        have h2 : ex.2.1 = ey.2.1 := Fin.ext h2val
        have hp : ex = ey := Prod.ext h1 (Subtype.ext h2)
        subst ey
        rfl
  have hcard : Fintype.card {e : Lattice2D.SquareFreeEdge L //
      (Lattice2D.squareFreeGraph L).tgt e = p} ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective code hinj
  have hcard' : Fintype.card {e : Lattice2D.SquareFreeEdge L //
      (Lattice2D.squareFreeGraph L).tgt e = p} =
      (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge L =>
        (Lattice2D.squareFreeGraph L).tgt e = p).card := by
    exact Fintype.card_subtype
      (fun e : Lattice2D.SquareFreeEdge L =>
        (Lattice2D.squareFreeGraph L).tgt e = p)
  rw [hcard'] at hcard
  exact hcard.trans_eq Fintype.card_bool

/-- In the internal positive-step free square, at most two edges start and at most two end at any
vertex: there is at most one candidate in each coordinate direction. -/
theorem squareFreeGraph_endpointDegree_le_four {L : ℕ} (p : Fin L × Fin L) :
    (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge L =>
      (Lattice2D.squareFreeGraph L).src e = p).card +
      (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge L =>
        (Lattice2D.squareFreeGraph L).tgt e = p).card ≤ 4 := by
  have hs := squareFree_source_count_le_two p
  have ht := squareFree_target_count_le_two p
  omega

private theorem torusStep_injective {L : ℕ} (b : Bool) :
    Function.Injective (Lattice2D.torusStep L b) := by
  intro p q hpq
  cases p with
  | mk x y =>
    cases q with
    | mk x' y' =>
      cases b
      · change (x + 1, y) = (x' + 1, y') at hpq
        rcases Prod.mk.inj hpq with ⟨hx, hy⟩
        exact Prod.ext (add_right_cancel hx) hy
      · change (x, y + 1) = (x', y' + 1) at hpq
        rcases Prod.mk.inj hpq with ⟨hx, hy⟩
        exact Prod.ext hx (add_right_cancel hy)

private theorem torus_source_count_le_two {L : ℕ} (hL : 2 < L) [NeZero L]
    (p : Lattice2D.TorusVertex L) :
    (Finset.univ.filter fun e : Lattice2D.TorusEdge L =>
      (Lattice2D.torusGraph L hL).src e = p).card ≤ 2 := by
  classical
  let code : {e : Lattice2D.TorusEdge L //
      (Lattice2D.torusGraph L hL).src e = p} → Bool := fun x => x.1.2
  have hinj : Function.Injective code := by
    intro x y hxy
    rcases x with ⟨ex, hx⟩
    rcases y with ⟨ey, hy⟩
    apply Subtype.ext
    have hx' : ex.1 = p := by simpa [Lattice2D.torusGraph] using hx
    have hy' : ey.1 = p := by simpa [Lattice2D.torusGraph] using hy
    exact Prod.ext (hx'.trans hy'.symm) hxy
  have hcard : Fintype.card {e : Lattice2D.TorusEdge L //
      (Lattice2D.torusGraph L hL).src e = p} ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective code hinj
  have hcard' : Fintype.card {e : Lattice2D.TorusEdge L //
      (Lattice2D.torusGraph L hL).src e = p} =
      (Finset.univ.filter fun e : Lattice2D.TorusEdge L =>
        (Lattice2D.torusGraph L hL).src e = p).card := by
    exact Fintype.card_subtype
      (fun e : Lattice2D.TorusEdge L =>
        (Lattice2D.torusGraph L hL).src e = p)
  rw [hcard'] at hcard
  exact hcard.trans_eq Fintype.card_bool

private theorem torus_target_count_le_two {L : ℕ} (hL : 2 < L) [NeZero L]
    (p : Lattice2D.TorusVertex L) :
    (Finset.univ.filter fun e : Lattice2D.TorusEdge L =>
      (Lattice2D.torusGraph L hL).tgt e = p).card ≤ 2 := by
  classical
  let code : {e : Lattice2D.TorusEdge L //
      (Lattice2D.torusGraph L hL).tgt e = p} → Bool := fun x => x.1.2
  have hinj : Function.Injective code := by
    intro x y hxy
    rcases x with ⟨ex, hx⟩
    rcases y with ⟨ey, hy⟩
    apply Subtype.ext
    have hx' : Lattice2D.torusStep L ex.2 ex.1 = p := by
      simpa [Lattice2D.torusGraph] using hx
    have hy' : Lattice2D.torusStep L ey.2 ey.1 = p := by
      simpa [Lattice2D.torusGraph] using hy
    change ex.2 = ey.2 at hxy
    rw [← hxy] at hy'
    exact Prod.ext ((torusStep_injective ex.2) (hx'.trans hy'.symm)) hxy
  have hcard : Fintype.card {e : Lattice2D.TorusEdge L //
      (Lattice2D.torusGraph L hL).tgt e = p} ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective code hinj
  have hcard' : Fintype.card {e : Lattice2D.TorusEdge L //
      (Lattice2D.torusGraph L hL).tgt e = p} =
      (Finset.univ.filter fun e : Lattice2D.TorusEdge L =>
        (Lattice2D.torusGraph L hL).tgt e = p).card := by
    exact Fintype.card_subtype
      (fun e : Lattice2D.TorusEdge L =>
        (Lattice2D.torusGraph L hL).tgt e = p)
  rw [hcard'] at hcard
  exact hcard.trans_eq Fintype.card_bool

/-- On the internal torus carrier there are exactly two edges starting and exactly two edges
ending at each vertex, one per coordinate direction. -/
theorem torusGraph_endpointDegree_eq_four {L : ℕ} (hL : 2 < L) [NeZero L]
    (p : Lattice2D.TorusVertex L) :
    (Finset.univ.filter fun e : Lattice2D.TorusEdge L =>
      (Lattice2D.torusGraph L hL).src e = p).card +
      (Finset.univ.filter fun e : Lattice2D.TorusEdge L =>
        (Lattice2D.torusGraph L hL).tgt e = p).card = 4 := by
  classical
  have hsrc_le := torus_source_count_le_two hL p
  have htgt_le := torus_target_count_le_two hL p
  let e₁ : Lattice2D.TorusEdge L := (p, false)
  let e₂ : Lattice2D.TorusEdge L := (p, true)
  have hsrc₁ : e₁ ∈ Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).src e = p) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [e₁, Lattice2D.torusGraph]
  have hsrc₂ : e₂ ∈ Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).src e = p) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [e₂, Lattice2D.torusGraph]
  have hsrc_ne : e₁ ≠ e₂ := by simp [e₁, e₂]
  have hsrc_lower : 2 ≤ (Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).src e = p)).card := by
    have hsub : ({e₁, e₂} : Finset (Lattice2D.TorusEdge L)) ⊆
        Finset.univ.filter (fun e => (Lattice2D.torusGraph L hL).src e = p) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hsrc₁
      · exact hsrc₂
    have hcard : ({e₁, e₂} : Finset (Lattice2D.TorusEdge L)).card = 2 := by
      simp [hsrc_ne]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hsrc : (Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).src e = p)).card = 2 := by
    omega
  let e₃ : Lattice2D.TorusEdge L := ((p.1 - 1, p.2), false)
  let e₄ : Lattice2D.TorusEdge L := ((p.1, p.2 - 1), true)
  have htgt₃ : e₃ ∈ Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).tgt e = p) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change Lattice2D.torusStep L false (p.1 - 1, p.2) = p
    simp [Lattice2D.torusStep]
  have htgt₄ : e₄ ∈ Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).tgt e = p) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change Lattice2D.torusStep L true (p.1, p.2 - 1) = p
    simp [Lattice2D.torusStep]
  have htgt_ne : e₃ ≠ e₄ := by simp [e₃, e₄]
  have htgt_lower : 2 ≤ (Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).tgt e = p)).card := by
    have hsub : ({e₃, e₄} : Finset (Lattice2D.TorusEdge L)) ⊆
        Finset.univ.filter (fun e => (Lattice2D.torusGraph L hL).tgt e = p) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact htgt₃
      · exact htgt₄
    have hcard : ({e₃, e₄} : Finset (Lattice2D.TorusEdge L)).card = 2 := by
      simp [htgt_ne]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have htgt : (Finset.univ.filter
      (fun e : Lattice2D.TorusEdge L => (Lattice2D.torusGraph L hL).tgt e = p)).card = 2 := by
    omega
  omega

private theorem adj_color_ne {V : Type*} {E : Type*} [DecidableEq V]
    (G : Multigraph V E) (color : V → Bool)
    (hcolor : ∀ e, color (G.src e) ≠ color (G.tgt e)) {x y : V}
    (hxy : G.Adj x y) : color x ≠ color y := by
  rcases hxy with ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
  · simpa [hs, ht] using hcolor e
  · simpa [hs, ht] using (hcolor e).symm

/-- A neutral density of graph diameter one on a connected bipartite graph has equal squared
mass on the two color classes. This is the diameter-one balance used in KP (4.21), p. 23.
-/
theorem neutral_diameter_one_colorMass {V : Type*} {E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (color : V → Bool)
    (hcolor : ∀ e, color (G.src e) ≠ color (G.tgt e)) (ρ : V → ℤ) (center : V)
    (hcenter : G.IsDensityCenter ρ center) (hneutral : ∑ j, ρ j = 0)
    (hdiam : G.densityDiameter ρ = 1) :
    colorMass color ρ (color center) = (∑ j, (ρ j : ℝ) ^ 2) / 2 := by
  classical
  obtain ⟨k, hk, hdistCk⟩ := hcenter.2
  have hc : ρ center ≠ 0 := hcenter.1
  have hdist (x y : V) (hx : ρ x ≠ 0) (hy : ρ y ≠ 0) :
      G.toSimpleGraph.dist x y ≤ 1 := by
    let supp := Finset.univ.filter fun z => ρ z ≠ 0
    have hx' : x ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    have hy' : y ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    have hs := Finset.le_sup
      (f := fun p : V × V => G.toSimpleGraph.dist p.1 p.2) (b := (x, y))
      (Finset.mem_product.mpr ⟨hx', hy'⟩)
    dsimp [supp] at hs
    change G.toSimpleGraph.dist x y ≤ G.densityDiameter ρ at hs
    simpa [hdiam] using hs
  have hdistCkOne : G.toSimpleGraph.dist center k = 1 := by
    rw [← hdiam]
    exact hdistCk.symm
  have hck : center ≠ k := by
    intro heq
    have hzero : G.toSimpleGraph.dist center k = 0 := by simp [heq]
    rw [hdistCkOne] at hzero
    norm_num at hzero
  have hCkAdj : G.toSimpleGraph.Adj center k :=
    SimpleGraph.dist_eq_one_iff_adj.mp hdistCkOne
  have hCkMult : G.Adj center k := by
    change (SimpleGraph.fromRel G.Adj).Adj center k at hCkAdj
    rcases ((SimpleGraph.fromRel_adj G.Adj center k).mp hCkAdj).2 with h | h
    · exact h
    · exact G.adj_symm h
  have hcolorsCk : color center ≠ color k := adj_color_ne G color hcolor hCkMult
  have hsupport : ∀ x, ρ x ≠ 0 → x = center ∨ x = k := by
    intro x hx
    by_cases hxc : x = center
    · exact Or.inl hxc
    · have hdistXC := hdist x center hx hc
      have hposXC : 0 < G.toSimpleGraph.dist x center := by
        exact (hG.preconnected x center).pos_dist_of_ne hxc
      have hdistXC1 : G.toSimpleGraph.dist x center = 1 := by omega
      have hAdjXC : G.toSimpleGraph.Adj x center :=
        SimpleGraph.dist_eq_one_iff_adj.mp hdistXC1
      have hMultXC : G.Adj x center := by
        change (SimpleGraph.fromRel G.Adj).Adj x center at hAdjXC
        rcases ((SimpleGraph.fromRel_adj G.Adj x center).mp hAdjXC).2 with h | h
        · exact h
        · exact G.adj_symm h
      have hcolorsXC : color x ≠ color center := adj_color_ne G color hcolor hMultXC
      by_cases hxk : x = k
      · exact Or.inr hxk
      · have hdistXK := hdist x k hx hk
        have hposXK : 0 < G.toSimpleGraph.dist x k :=
          (hG.preconnected x k).pos_dist_of_ne hxk
        have hdistXK1 : G.toSimpleGraph.dist x k = 1 := by omega
        have hAdjXK : G.toSimpleGraph.Adj x k :=
          SimpleGraph.dist_eq_one_iff_adj.mp hdistXK1
        have hMultXK : G.Adj x k := by
          change (SimpleGraph.fromRel G.Adj).Adj x k at hAdjXK
          rcases ((SimpleGraph.fromRel_adj G.Adj x k).mp hAdjXK).2 with h | h
          · exact h
          · exact G.adj_symm h
        have hcolorsXK : color x ≠ color k := adj_color_ne G color hcolor hMultXK
        cases hcColor : color center <;> cases hkColor : color k <;>
          cases hxColor : color x <;> simp_all
  have hkNotCenter : k ∈ (Finset.univ.erase center) := by
    simp [hck.symm]
  have hsumErase : (∑ x ∈ Finset.univ.erase center, ρ x) = ρ k := by
    apply Finset.sum_eq_single_of_mem k hkNotCenter
    intro x hx hxk
    have hxzero : ρ x = 0 := by
      by_contra hxne
      have hcases := hsupport x hxne
      rcases hcases with hxc' | hxk'
      · exact (Finset.mem_erase.mp hx).1 hxc'
      · exact hxk hxk'
    exact hxzero
  have hsumDecomp : (∑ x ∈ Finset.univ.erase center, ρ x) + ρ center =
      ∑ x, ρ x := Finset.sum_erase_add _ _ (Finset.mem_univ center)
  have hneutralPair : ρ k + ρ center = 0 := by
    rw [hsumErase] at hsumDecomp
    rw [hneutral] at hsumDecomp
    exact hsumDecomp
  have hkval : (ρ k : ℝ) = -(ρ center : ℝ) := by exact_mod_cast (eq_neg_of_add_eq_zero_left hneutralPair)
  have hsumSqErase :
      (∑ x ∈ Finset.univ.erase center, (ρ x : ℝ) ^ 2) = (ρ k : ℝ) ^ 2 := by
    apply Finset.sum_eq_single_of_mem k hkNotCenter
    intro x hx hxk
    have hxzero : ρ x = 0 := by
      by_contra hxne
      have hcases := hsupport x hxne
      rcases hcases with hxc' | hxk'
      · exact (Finset.mem_erase.mp hx).1 hxc'
      · exact hxk hxk'
    simp [hxzero]
  have hsumSqDecomp :
      (∑ x ∈ Finset.univ.erase center, (ρ x : ℝ) ^ 2) + (ρ center : ℝ) ^ 2 =
        ∑ x, (ρ x : ℝ) ^ 2 := Finset.sum_erase_add _ _ (Finset.mem_univ center)
  have htotal : ∑ x, (ρ x : ℝ) ^ 2 = 2 * (ρ center : ℝ) ^ 2 := by
    rw [hsumSqErase] at hsumSqDecomp
    rw [hkval] at hsumSqDecomp
    nlinarith [hsumSqDecomp]
  have hcolorSum : colorMass color ρ (color center) = (ρ center : ℝ) ^ 2 := by
    unfold colorMass
    let term : V → ℝ := fun x =>
      if color x = color center then (ρ x : ℝ) ^ 2 else 0
    have hsum : (∑ x, term x) = term center := by
      apply Finset.sum_eq_single_of_mem center (Finset.mem_univ center)
      intro x hx hxc
      by_cases hxzero : ρ x = 0
      · simp [term, hxzero]
      · rcases hsupport x hxzero with hxc' | hxk'
        · exact (hxc hxc').elim
        · subst x
          simp [term, hcolorsCk.symm]
    simpa [term] using hsum
  rw [hcolorSum, htotal]
  ring

/-- Parity coloring of the free or periodic square, by the sum of its coordinates. -/
def squareParityColor {L : ℕ} (p : Fin L × Fin L) : Bool :=
  decide ((p.1.val + p.2.val) % 2 = 0)

private theorem natParity_ne_of_modEq_step {L a b : ℕ} (hEven : Even L)
    (h : (a : ℤ) ≡ (b : ℤ) + 1 [ZMOD L]) : a % 2 ≠ b % 2 := by
  have h2 : (a : ℤ) ≡ (b : ℤ) + 1 [ZMOD 2] := by
    apply Int.ModEq.of_dvd (m := 2) (n := L)
    · rcases hEven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    · exact h
  have hdvd := h2.dvd
  rcases hdvd with ⟨k, hk⟩
  have ha : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have hb : b % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

private theorem natParity_ne_of_modEq_step_rev {L a b : ℕ} (hEven : Even L)
    (h : (b : ℤ) ≡ (a : ℤ) + 1 [ZMOD L]) : a % 2 ≠ b % 2 := by
  intro heq
  have h2 : (b : ℤ) ≡ (a : ℤ) + 1 [ZMOD 2] := by
    apply Int.ModEq.of_dvd (m := 2) (n := L)
    · rcases hEven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    · exact h
  have hdvd := h2.dvd
  rcases hdvd with ⟨k, hk⟩
  have ha : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have hb : b % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- Every edge of the free square changes the parity coloring. -/
theorem squareFree_color_edge {L : ℕ} (e : SquareFreeEdge L) :
    squareParityColor e.1.1 ≠ squareParityColor e.1.2 := by
  rcases squareFreeEdge_classification e with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · simp [squareParityColor]
    have hsum : e.1.2.1.val + e.1.2.2.val =
        e.1.1.1.val + e.1.1.2.val + 1 := by omega
    rw [hsum]
    omega
  · simp [squareParityColor]
    have hsum : e.1.2.1.val + e.1.2.2.val =
        e.1.1.1.val + e.1.1.2.val + 1 := by omega
    rw [hsum]
    omega

/-- Every edge of an even periodic square changes the parity coloring. The modulo-`L` edge
relation reduces to the modulo-two parity relation because `L` is even; this includes `L = 2`.
-/
theorem squarePeriodic_color_edge {L : ℕ} (hEven : Even L) (e : SquarePeriodicEdge L) :
    squareParityColor e.1.1 ≠ squareParityColor e.1.2 := by
  rcases e.2.2 with ⟨hcoord, hstep | hstep⟩ | ⟨hcoord, hstep | hstep⟩
  · simp [squareParityColor, hcoord]
    have hpar := natParity_ne_of_modEq_step hEven hstep
    omega
  · simp [squareParityColor, hcoord]
    have hpar := natParity_ne_of_modEq_step_rev hEven hstep
    omega
  · simp [squareParityColor, hcoord]
    have hpar := natParity_ne_of_modEq_step hEven hstep
    omega
  · simp [squareParityColor, hcoord]
    have hpar := natParity_ne_of_modEq_step_rev hEven hstep
    omega

/--
The free square has the canonical parity coloring, endpoint degree at most four, and
the diameter-one neutral mass balance (KP pp. 2, 23).

Degree is counted on the internal
positive-step carrier and transported through the edge equivalence.
-/
def squareFreeBipartiteDegreeFour (L : ℕ) (hL : 1 < L) :
    BipartiteDegreeFour (squareFree L) where
  color := squareParityColor
  color_edge := by
    intro e
    simpa [squareFree] using squareFree_color_edge e
  endpointDegree_le_four := by
    intro j
    let I := squareFreeSourceGraphIsomorphism L
    calc
      (Finset.univ.filter fun e => (squareFree L).src e = j).card +
          (Finset.univ.filter fun e => (squareFree L).tgt e = j).card =
        (Finset.univ.filter fun e => (Lattice2D.squareFreeGraph L).src e = I.vertices j).card +
          (Finset.univ.filter fun e => (Lattice2D.squareFreeGraph L).tgt e = I.vertices j).card :=
            I.endpointDegree_eq j
      _ ≤ 4 := squareFreeGraph_endpointDegree_le_four (I.vertices j)
  neutral_diameter_one_mass := by
    intro ρ center hcenter hneutral hdiam
    exact neutral_diameter_one_colorMass (squareFree L)
      (squareFree_connected L hL) squareParityColor squareFree_color_edge
      ρ center hcenter hneutral hdiam

/--
The even periodic square has the parity coloring and degree-four bound of KP p. 2.

For side two the bound is transported through the canonical square isomorphism; for side at
least four it is transported to the oriented internal torus.

The diameter-one balance is the
same bipartite neutrality argument as in the free case.
-/
def squarePeriodicBipartiteDegreeFour_of_neZero (L : ℕ) [NeZero L]
    (hEven : Even L) (hL : 1 < L) :
    BipartiteDegreeFour (squarePeriodic L) where
  color := squareParityColor
  color_edge := by
    intro e
    simpa [squarePeriodic] using squarePeriodic_color_edge hEven e
  endpointDegree_le_four := by
    intro j
    by_cases htwo : L = 2
    · subst L
      let I := squarePeriodicTwoIsomorphism
      let J := squareFreeSourceGraphIsomorphism 2
      calc
        (Finset.univ.filter fun e => (squarePeriodic 2).src e = j).card +
            (Finset.univ.filter fun e => (squarePeriodic 2).tgt e = j).card =
        (Finset.univ.filter fun e => (squareFree 2).src e = I.vertices j).card +
            (Finset.univ.filter fun e => (squareFree 2).tgt e = I.vertices j).card := by
              simpa [I, squarePeriodicTwoIsomorphism] using (I.endpointDegree_eq j).symm
        _ = (Finset.univ.filter fun e =>
              (Lattice2D.squareFreeGraph 2).src e = J.vertices (I.vertices j)).card +
            (Finset.univ.filter fun e =>
              (Lattice2D.squareFreeGraph 2).tgt e = J.vertices (I.vertices j)).card := by
              simpa [J] using J.endpointDegree_eq (I.vertices j)
        _ ≤ 4 := by
              exact squareFreeGraph_endpointDegree_le_four (J.vertices (I.vertices j))
    · have hfour : 4 ≤ L := by
        rcases hEven with ⟨k, hk⟩
        omega
      let I := squarePeriodicTorusIsomorphism_of_four hfour
      calc
        (Finset.univ.filter fun e => (squarePeriodic L).src e = j).card +
            (Finset.univ.filter fun e => (squarePeriodic L).tgt e = j).card =
          (Finset.univ.filter fun e => (Lattice2D.torusGraph L (by omega)).src e =
              I.vertices j).card +
            (Finset.univ.filter fun e => (Lattice2D.torusGraph L (by omega)).tgt e =
              I.vertices j).card := I.endpointDegree_eq j
        _ = 4 := torusGraph_endpointDegree_eq_four (by omega) (I.vertices j)
        _ ≤ 4 := Nat.le_refl 4
  neutral_diameter_one_mass := by
    intro ρ center hcenter hneutral hdiam
    exact neutral_diameter_one_colorMass (squarePeriodic L)
      (squarePeriodic_connected L hL) squareParityColor
      (fun e => squarePeriodic_color_edge hEven e)
      ρ center hcenter hneutral hdiam

/-- The degree-four bipartite data for every even periodic square of side greater than one.
The nonzero-side witness needed by the internal torus is inferred directly from `hL`. -/
def squarePeriodicBipartiteDegreeFour (L : ℕ) (hEven : Even L) (hL : 1 < L) :
    BipartiteDegreeFour (squarePeriodic L) :=
  @squarePeriodicBipartiteDegreeFour_of_neZero L ⟨by omega⟩ hEven hL

end FroehlichSpencer.BKT.SpinWaves

end
