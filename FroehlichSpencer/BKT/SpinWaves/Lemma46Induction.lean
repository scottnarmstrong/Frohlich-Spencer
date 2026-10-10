/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Lemma46Arithmetic
public import FroehlichSpencer.BKT.SpinWaves.ShellPacking
public import FroehlichSpencer.BKT.SpinWaves.Prop47Statements
public import FroehlichSpencer.BKT.Reduction.T22SeparationBridge

/-!
# Finite-subensemble induction for KP Lemma 4.6
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

universe u v

/- The strong KP form carries the unique scale and both inductive geometric bounds. -/
abbrev lemma46FiniteSubensembleInvariant {V : Type u} {E : Type v} [Fintype V]
    [Fintype E] (G : Multigraph V E) (I : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) : Prop := lemma46StrongBoundaryInvariant G I centerOf

/--
The neutral-neutral clause of KP T2.2(b), used when the distinguished density in L4.6 is
itself neutral.

Its supports and diameters are measured by the graph API.
-/
def KPTheorem22bNeutralSeparation {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (M α : ℝ) : Prop :=
  ∀ ρ ∈ N₀, ∀ σ ∈ N₀, ρ ≠ σ →
    M * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^ α ≤
      (↑(densitySupportDistance G ρ σ) : ℝ)

theorem KPTheorem22bNeutralSeparation.neutral_support_distance {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
    {N₀ : Finset (V → ℤ)} {ρ σ : V → ℤ} {M α : ℝ}
    (hsep : KPTheorem22bNeutralSeparation G N₀ M α)
    (hρ : ρ ∈ N₀) (hσ : σ ∈ N₀) (hne : ρ ≠ σ) {x y : V}
    (hx : ρ x ≠ 0) (hy : σ y ≠ 0) :
    M * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^ α ≤
      (↑(G.toSimpleGraph.dist x y) : ℝ) := by
  exact le_trans (hsep ρ hρ σ hσ hne) <|
    Nat.cast_le.mpr (densitySupportDistance_le G ρ σ hx hy)

/-- The boundary-shell packing shell-packing input needed only in the merge case of the strong induction invariant.
It is the boundary-shell estimate from the boundary-shell estimate, with the scale and diameter conclusions supplied
by the finite-subensemble transition. The estimate is expressed as a local hypothesis of the induction. -/
def lemma46BoundaryPackingStep {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq (V → ℤ)] (G : Multigraph V E)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V) : Prop :=
  ∀ (I : Finset (V → ℤ)) (ρ : V → ℤ) (m : ℕ),
    I ⊆ N₀ → ρ ∈ N₀ → ρ ∉ I →
    (∑ x, ρ x = 0) → G.IsDensityCenter ρ (centerOf ρ) →
    (∀ σ ∈ N₀, ∑ x, σ x = 0) →
    (∀ σ ∈ N₀, G.IsDensityCenter σ (centerOf σ)) →
    KPTheorem22bNeutralSeparation G N₀ (2 ^ 16 : ℝ) (7 / 4 : ℝ) →
    1 ≤ m → G.densityDiameter ρ = m →
    (∀ σ ∈ I, G.densityDiameter σ ≤ m) →
    lemma46FiniteSubensembleInvariant G I centerOf →
    ∀ c : DensityPlusComponent G (insert ρ I) centerOf,
      (∃ x ∈ G.densityDomainPlus ρ (centerOf ρ),
        x ∈ densityPlusComponentVertices G (insert ρ I) centerOf c) →
      densityPlusComponentDiameter G (insert ρ I) centerOf c ≤ 5 * m →
      (densityPlusExternalBoundary G (insert ρ I) centerOf c).card ≤ 16 * m

/-- Every old-union vertex in a new induced-union component that meets the newly added `D⁺`
domain belongs to an old component touching that domain. This is the component-merging step in
the finite-subensemble induction. -/
theorem exists_adjacent_oldComponent_of_newComponent {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq (V → ℤ)] {G : Multigraph V E} (I : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (ρ : V → ℤ) (c : DensityPlusComponent G (insert ρ I) centerOf)
    {x y : V} (hx : x ∈ G.densityDomainPlus ρ (centerOf ρ))
    (hxc : x ∈ densityPlusComponentVertices G (insert ρ I) centerOf c)
    (hyc : y ∈ densityPlusComponentVertices G (insert ρ I) centerOf c)
    (hyA : y ∉ G.densityDomainPlus ρ (centerOf ρ)) :
    ∃ c' : DensityPlusComponent G I centerOf,
      y ∈ densityPlusComponentVertices G I centerOf c' ∧
      ∃ a ∈ G.densityDomainPlus ρ (centerOf ρ),
        ∃ b ∈ densityPlusComponentVertices G I centerOf c',
          a = b ∨ G.toSimpleGraph.Adj a b := by
  let U := densityPlusUnion G I centerOf
  let U' := densityPlusUnion G (insert ρ I) centerOf
  let A := G.densityDomainPlus ρ (centerOf ρ)
  let H := G.toSimpleGraph.induce (U : Set V)
  let H' := G.toSimpleGraph.induce (U' : Set V)
  have hyU : y ∈ U := by
    have hyU' : y ∈ U' := ((mem_densityPlusComponentVertices G (insert ρ I) centerOf c y).1 hyc).1
    rcases (mem_densityPlusUnion_insert G I centerOf ρ y).1 hyU' with hyA' | hyU'
    · exact (hyA hyA').elim
    · exact hyU'
  have hxU' : x ∈ U' :=
    (mem_densityPlusUnion_insert G I centerOf ρ x).2 (Or.inl hx)
  have hyU' : y ∈ U' :=
    (mem_densityPlusUnion_insert G I centerOf ρ y).2 (Or.inr hyU)
  rcases (mem_densityPlusComponentVertices G (insert ρ I) centerOf c x).1 hxc with
    ⟨_, hxclass⟩
  rcases (mem_densityPlusComponentVertices G (insert ρ I) centerOf c y).1 hyc with
    ⟨_, hyclass⟩
  have hclass : H'.connectedComponentMk ⟨x, hxU'⟩ = H'.connectedComponentMk ⟨y, hyU'⟩ :=
    hxclass.trans hyclass.symm
  have hreach : H'.Reachable ⟨x, hxU'⟩ ⟨y, hyU'⟩ :=
    (SimpleGraph.ConnectedComponent.eq).mp hclass
  let Q : U' → Prop := fun z => z.1 ∈ A ∨
    ∃ hz : z.1 ∈ U, ∃ a ∈ A, ∃ b : U,
      G.toSimpleGraph.Adj a b.1 ∧ H.Reachable b ⟨z.1, hz⟩
  have hstep {u v : U'} (hadj : H'.Adj u v) (hu : Q u) : Q v := by
    by_cases hvA : v.1 ∈ A
    · exact Or.inl hvA
    · have hvU : v.1 ∈ U := by
        rcases (mem_densityPlusUnion_insert G I centerOf ρ v.1).1 v.2 with hvA' | hvU
        · exact (hvA hvA').elim
        · exact hvU
      have hadjG : G.toSimpleGraph.Adj u.1 v.1 := SimpleGraph.induce_adj.mp hadj
      rcases hu with huA | ⟨huU, a, ha, b, hab, hreachOld⟩
      · exact Or.inr ⟨hvU, u.1, huA, ⟨v.1, hvU⟩, hadjG,
          ⟨SimpleGraph.Walk.nil⟩⟩
      · have hadjOld : H.Adj ⟨u.1, huU⟩ ⟨v.1, hvU⟩ := SimpleGraph.induce_adj.mpr hadjG
        exact Or.inr ⟨hvU, a, ha, b, hab, hreachOld.trans hadjOld.reachable⟩
  have hwalk {u v : U'} (p : H'.Walk u v) : Q u → Q v := by
    induction p with
    | nil => exact id
    | @cons u v w hadj p ih =>
        intro hu
        exact ih (hstep hadj hu)
  have hQ : Q ⟨y, hyU'⟩ := hwalk (Classical.choice hreach) (Or.inl hx)
  rcases hQ with hyA' | ⟨hyU, a, ha, b, hab, hreachOld⟩
  · exact (hyA hyA').elim
  let c' : DensityPlusComponent G I centerOf := H.connectedComponentMk b
  have hyclassOld : H.connectedComponentMk ⟨y, hyU⟩ = c' :=
    (SimpleGraph.ConnectedComponent.sound hreachOld).symm
  have hyCompOld : y ∈ densityPlusComponentVertices G I centerOf c' :=
    (mem_densityPlusComponentVertices G I centerOf c' y).2 ⟨hyU, hyclassOld⟩
  have hbCompOld : b.1 ∈ densityPlusComponentVertices G I centerOf c' :=
    (mem_densityPlusComponentVertices G I centerOf c' b.1).2 ⟨b.2, rfl⟩
  exact ⟨c', hyCompOld, a, ha, b.1, hbCompOld, Or.inr hab⟩

/-- A path in the enlarged union component that avoids the newly inserted domain remains a path
in the old induced union. This is the unchanged-component case of the finite-subensemble
induction. -/
theorem reachable_old_of_newComponent_avoiding_domain {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq (V → ℤ)] {G : Multigraph V E} (I : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (ρ : V → ℤ) (c : DensityPlusComponent G (insert ρ I) centerOf)
    {x y : V} (hxU : x ∈ densityPlusUnion G I centerOf)
    (hxC : x ∈ densityPlusComponentVertices G (insert ρ I) centerOf c)
    (hyC : y ∈ densityPlusComponentVertices G (insert ρ I) centerOf c)
    (havoid : ∀ z ∈ densityPlusComponentVertices G (insert ρ I) centerOf c,
      z ∉ G.densityDomainPlus ρ (centerOf ρ)) :
    ∃ hyU : y ∈ densityPlusUnion G I centerOf,
      (G.toSimpleGraph.induce (densityPlusUnion G I centerOf : Set V)).Reachable
        ⟨x, hxU⟩ ⟨y, hyU⟩ := by
  let U := densityPlusUnion G I centerOf
  let U' := densityPlusUnion G (insert ρ I) centerOf
  let H := G.toSimpleGraph.induce (U : Set V)
  let H' := G.toSimpleGraph.induce (U' : Set V)
  have hyU' : y ∈ U' := ((mem_densityPlusComponentVertices G (insert ρ I) centerOf c y).1 hyC).1
  have hxU' : x ∈ U' := (mem_densityPlusUnion_insert G I centerOf ρ x).2 (Or.inr hxU)
  rcases (mem_densityPlusComponentVertices G (insert ρ I) centerOf c x).1 hxC with
    ⟨_, hxclass⟩
  have hclass : H'.connectedComponentMk ⟨x, hxU'⟩ = H'.connectedComponentMk
      ⟨y, hyU'⟩ :=
    ((mem_densityPlusComponentVertices G (insert ρ I) centerOf c x).1 hxC).2.trans
      (((mem_densityPlusComponentVertices G (insert ρ I) centerOf c y).1 hyC).2.symm)
  have hfull : H'.Reachable ⟨x, hxU'⟩ ⟨y, hyU'⟩ :=
    (SimpleGraph.ConnectedComponent.eq).mp hclass
  let Q : U' → Prop := fun z => ∃ hz : z.1 ∈ U, H.Reachable ⟨x, hxU⟩ ⟨z.1, hz⟩
  have hstep {u v : U'} (hadj : H'.Adj u v) (hu : Q u) : Q v := by
    rcases hu with ⟨huU, hreachOld⟩
    have hsub : (U : Set V) ⊆ (U' : Set V) := by
      intro z hz
      exact (mem_densityPlusUnion_insert G I centerOf ρ z).2 (Or.inr hz)
    have hreachNew := hreachOld.map (G.toSimpleGraph.induceHomOfLE hsub).toHom
    have hadjG : G.toSimpleGraph.Adj u.1 v.1 := SimpleGraph.induce_adj.mp hadj
    have hreachV := hreachNew.trans hadj.reachable
    have hclassV : H'.connectedComponentMk ⟨v.1, v.2⟩ = c := by
      have hxC' : H'.connectedComponentMk ⟨x, hxU'⟩ = c :=
        (mem_densityPlusComponentVertices G (insert ρ I) centerOf c x).1 hxC |>.2
      exact (SimpleGraph.ConnectedComponent.sound hreachV).symm.trans hxC'
    have hvC : v.1 ∈ densityPlusComponentVertices G (insert ρ I) centerOf c :=
      (mem_densityPlusComponentVertices G (insert ρ I) centerOf c v.1).2 ⟨v.2, hclassV⟩
    have hvnotA := havoid v.1 hvC
    have hvU : v.1 ∈ U := by
      rcases (mem_densityPlusUnion_insert G I centerOf ρ v.1).1 v.2 with hvA | hvU
      · exact (hvnotA hvA).elim
      · exact hvU
    have hadjOld : H.Adj ⟨u.1, huU⟩ ⟨v.1, hvU⟩ := SimpleGraph.induce_adj.mpr hadjG
    exact ⟨hvU, hreachOld.trans hadjOld.reachable⟩
  have hwalk {u v : U'} (p : H'.Walk u v) : Q u → Q v := by
    induction p with
    | nil => exact id
    | @cons u v w hadj p ih =>
        intro hu
        exact ih (hstep hadj hu)
  have hQ : Q ⟨y, hyU'⟩ := hwalk (Classical.choice hfull) ⟨hxU, ⟨SimpleGraph.Walk.nil⟩⟩
  exact ⟨hQ.1, hQ.2⟩

/-- Old induced-component vertices embed in the new component whenever one old vertex already
belongs to it. The inclusion of the old union in the enlarged union is the only graph map used.
-/
theorem oldComponent_subset_newComponent_of_mem {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq (V → ℤ)] {G : Multigraph V E} (I : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (ρ : V → ℤ)
    (cOld : DensityPlusComponent G I centerOf)
    (cNew : DensityPlusComponent G (insert ρ I) centerOf) {x : V}
    (hxOld : x ∈ densityPlusComponentVertices G I centerOf cOld)
    (hxNew : x ∈ densityPlusComponentVertices G (insert ρ I) centerOf cNew) :
    densityPlusComponentVertices G I centerOf cOld ⊆
      densityPlusComponentVertices G (insert ρ I) centerOf cNew := by
  intro y hy
  let U := densityPlusUnion G I centerOf
  let U' := densityPlusUnion G (insert ρ I) centerOf
  let H := G.toSimpleGraph.induce (U : Set V)
  let H' := G.toSimpleGraph.induce (U' : Set V)
  rcases (mem_densityPlusComponentVertices G I centerOf cOld x).1 hxOld with
    ⟨hxU, hxclass⟩
  rcases (mem_densityPlusComponentVertices G I centerOf cOld y).1 hy with
    ⟨hyU, hyclass⟩
  have hreachOld : H.Reachable ⟨x, hxU⟩ ⟨y, hyU⟩ :=
    (SimpleGraph.ConnectedComponent.eq).mp (hxclass.trans hyclass.symm)
  have hsub : (U : Set V) ⊆ (U' : Set V) := by
    intro z hz
    exact (mem_densityPlusUnion_insert G I centerOf ρ z).2 (Or.inr hz)
  have hreachNew := hreachOld.map (G.toSimpleGraph.induceHomOfLE hsub).toHom
  rcases (mem_densityPlusComponentVertices G (insert ρ I) centerOf cNew x).1 hxNew with
    ⟨hxU', hxclassNew⟩
  have hyclassNew : H'.connectedComponentMk ⟨y, hsub hyU⟩ = cNew := by
    exact (SimpleGraph.ConnectedComponent.sound hreachNew).symm.trans hxclassNew
  exact (mem_densityPlusComponentVertices G (insert ρ I) centerOf cNew y).2
    ⟨hsub hyU, hyclassNew⟩

/-- A component of the previously added sub-ensemble that touches the new maximal density's
`D⁺` domain must have a maximal density below one twelfth of the new scale. This is the key
lower-scale exclusion in the finite-subensemble induction for KP Lemma 4.6. -/
theorem lemma46_attached_old_component_scale_lt_twelve {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
    {N₀ I : Finset (V → ℤ)} {ρ σ : V → ℤ}
    (hsep : KPTheorem22bNeutralSeparation G N₀ (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hI : I ⊆ N₀) (hρ : ρ ∈ N₀) (hσ : σ ∈ I) (hne : ρ ≠ σ)
    (hσneutral : ∑ x, σ x = 0)
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hσcenter : G.IsDensityCenter σ (centerOf σ))
    {m : ℕ} (hm : 1 ≤ m) (hρdiam : G.densityDiameter ρ = m)
    (hσdiam : G.densityDiameter σ ≤ m)
    (c : DensityPlusComponent G I centerOf)
    (hσcomponent : σ ∈ densitiesContainedInComponent G I centerOf c)
    (hdiam : densityPlusComponentDiameter G I centerOf c ≤
      5 * G.densityDiameter σ)
    (hcontact : ∃ a ∈ G.densityDomainPlus ρ (centerOf ρ),
      ∃ b ∈ densityPlusComponentVertices G I centerOf c,
        a = b ∨ G.toSimpleGraph.Adj a b) :
    12 * G.densityDiameter σ < m := by
  obtain ⟨a, ha, b, hb, hab⟩ := hcontact
  have hρsupport : ρ (centerOf ρ) ≠ 0 := hρcenter.1
  have hσsupport : σ (centerOf σ) ≠ 0 := hσcenter.1
  have hσpoint := densitySupport_subset_componentVertices G hG I centerOf c
    hσcomponent hσneutral hσcenter hσsupport
  have hρradius : G.toSimpleGraph.dist (centerOf ρ) a ≤ 2 * m := by
    rw [G.toSimpleGraph.dist_comm]
    simpa [hρdiam] using G.dist_le_of_mem_densityDomainPlus hG ha
  have hcontactDist : G.toSimpleGraph.dist a b ≤ 1 := by
    rcases hab with rfl | hadj
    · simp
    · exact (SimpleGraph.dist_eq_one_iff_adj.mpr hadj).le
  have holdDiameter : G.toSimpleGraph.dist b (centerOf σ) ≤
      densityPlusComponentDiameter G I centerOf c :=
    dist_le_densityPlusComponentDiameter G I centerOf c hb hσpoint
  have hdist : G.toSimpleGraph.dist (centerOf ρ) (centerOf σ) ≤
      2 * m + 1 + densityPlusComponentDiameter G I centerOf c := by
    calc
      G.toSimpleGraph.dist (centerOf ρ) (centerOf σ) ≤
          G.toSimpleGraph.dist (centerOf ρ) a +
            G.toSimpleGraph.dist a (centerOf σ) :=
        hG.dist_triangle (u := centerOf ρ) (v := a) (w := centerOf σ)
      _ ≤ G.toSimpleGraph.dist (centerOf ρ) a +
          (G.toSimpleGraph.dist a b + G.toSimpleGraph.dist b (centerOf σ)) :=
        Nat.add_le_add_left (hG.dist_triangle (u := a) (v := b) (w := centerOf σ)) _
      _ ≤ _ := by omega
  have hdist' : G.toSimpleGraph.dist (centerOf ρ) (centerOf σ) ≤ 8 * m := by
    have hdiam' := hdiam
    omega
  by_contra hlarge
  have hσlarge : m ≤ 12 * G.densityDiameter σ := by omega
  have hρlarge : m ≤ 12 * G.densityDiameter ρ := by rw [hρdiam]; omega
  have hscale := lemma46_t22b_scale_gt_nine_of_twelve hm hρlarge hσlarge
  have hpoint := hsep.neutral_support_distance hρ (hI hσ) hne hρsupport hσsupport
  have hupper : (↑(G.toSimpleGraph.dist (centerOf ρ) (centerOf σ)) : ℝ) ≤
      8 * (m : ℝ) := by exact_mod_cast hdist'
  have hcontra : (9 : ℝ) * m < 8 * (m : ℝ) := by
    exact lt_of_lt_of_le hscale (hpoint.trans hupper)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  linarith

/-- The old-component induction estimate used for the diameter transition. A component of the old
union attached to the inserted `D⁺` has diameter strictly below `5m/12`; this follows from the
unique old maximal density and KP Theorem 2.2(b). -/
theorem lemma46_attached_old_component_diameter_lt_five_twelfths
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq (V → ℤ)] {G : Multigraph V E} {N₀ I : Finset (V → ℤ)}
    {ρ : V → ℤ} (hsep : KPTheorem22bNeutralSeparation G N₀ (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hI : I ⊆ N₀) (hρ : ρ ∈ N₀) (hρnotI : ρ ∉ I)
    (hneutral : ∀ σ ∈ N₀, ∑ x, σ x = 0)
    (hcenter : ∀ σ ∈ N₀, G.IsDensityCenter σ (centerOf σ))
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ)) {m : ℕ} (hm : 1 ≤ m)
    (hρdiam : G.densityDiameter ρ = m)
    (hρmax : ∀ σ ∈ I, G.densityDiameter σ ≤ m)
    (hOld : lemma46FiniteSubensembleInvariant G I centerOf)
    (c' : DensityPlusComponent G I centerOf) (y a b : V)
    (ha : a ∈ G.densityDomainPlus ρ (centerOf ρ))
    (hyOld : y ∈ densityPlusComponentVertices G I centerOf c')
    (hb : b ∈ densityPlusComponentVertices G I centerOf c')
    (hab : a = b ∨ G.toSimpleGraph.Adj a b) :
    ∃ τ ∈ densitiesContainedInComponent G I centerOf c',
      (∀ σ ∈ densitiesContainedInComponent G I centerOf c',
        σ ≠ τ → G.densityDiameter σ < G.densityDiameter τ) ∧
      12 * G.densityDiameter τ < m ∧ 12 < m ∧
      12 * densityPlusComponentDiameter G I centerOf c' < 5 * m ∧
      G.toSimpleGraph.dist y a ≤ densityPlusComponentDiameter G I centerOf c' + 1 := by
  have hbUnion : b ∈ densityPlusUnion G I centerOf :=
    ((mem_densityPlusComponentVertices G I centerOf c' b).1 hb).1
  rcases (mem_densityPlusUnion G I centerOf b).1 hbUnion with ⟨σ, hσI, hbσ⟩
  have hσN₀ : σ ∈ N₀ := hI hσI
  have hσneutral := hneutral σ hσN₀
  have hσcenter := hcenter σ hσN₀
  have hσcomponent : σ ∈ densitiesContainedInComponent G I centerOf c' := by
    apply (mem_densitiesContainedInComponent G I centerOf c' σ).2
    refine ⟨hσI, ?_⟩
    exact densityDomainPlus_subset_componentVertices_of_mem G hG I centerOf c'
      hσI hσneutral hσcenter hbσ hb
  have hfamily : (densitiesContainedInComponent G I centerOf c').Nonempty := ⟨σ, hσcomponent⟩
  obtain ⟨τ, hτcomponent, hτmax, hdiam, _hboundary⟩ := hOld c' hfamily
  have hτI : τ ∈ I := (mem_densitiesContainedInComponent G I centerOf c' τ).1 hτcomponent |>.1
  have hτN₀ : τ ∈ N₀ := hI hτI
  have hτneutral := hneutral τ hτN₀
  have hτcenter := hcenter τ hτN₀
  have hτdiam : G.densityDiameter τ ≤ m := hρmax τ hτI
  have hτne : τ ≠ ρ := by
    intro hEq
    subst τ
    exact hρnotI hτI
  have hscale := lemma46_attached_old_component_scale_lt_twelve hsep hG centerOf hI hρ hτI
    hτne.symm hτneutral hρcenter hτcenter hm hρdiam hτdiam c' hτcomponent hdiam
    ⟨a, ha, b, hb, hab⟩
  have hτone : 1 ≤ G.densityDiameter τ :=
    G.one_le_densityDiameter_of_neutral hG τ (fun h => hτcenter.1 (by simp [h])) hτneutral
  have hsmall : 12 < m := by omega
  have hdiam' : 12 * densityPlusComponentDiameter G I centerOf c' < 5 * m := by omega
  have hdist : G.toSimpleGraph.dist y a ≤ densityPlusComponentDiameter G I centerOf c' + 1 := by
    have hby : G.toSimpleGraph.dist y b ≤ densityPlusComponentDiameter G I centerOf c' :=
      dist_le_densityPlusComponentDiameter G I centerOf c' hyOld hb
    have hba : G.toSimpleGraph.dist b a ≤ 1 := by
      rcases hab with rfl | hadj
      · simp
      · exact (SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm).le
    calc
      G.toSimpleGraph.dist y a ≤ G.toSimpleGraph.dist y b + G.toSimpleGraph.dist b a :=
        hG.dist_triangle (u := y) (v := b) (w := a)
      _ ≤ _ := by omega
  exact ⟨τ, hτcomponent, hτmax, hscale, hsmall, hdiam', hdist⟩

/-- Every point of a new component outside the inserted `D⁺` has a short route to that domain:
it lies in an old component whose scale and diameter are controlled by the previous strong
invariant and T2.2(b). -/
theorem lemma46_externalPoint_attached_bound {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} {N₀ I : Finset (V → ℤ)} {ρ : V → ℤ}
    (hsep : KPTheorem22bNeutralSeparation G N₀ (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hI : I ⊆ N₀) (hρ : ρ ∈ N₀) (hρnotI : ρ ∉ I)
    (hneutral : ∀ σ ∈ N₀, ∑ x, σ x = 0)
    (hcenter : ∀ σ ∈ N₀, G.IsDensityCenter σ (centerOf σ))
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ)) {m : ℕ} (hm : 1 ≤ m)
    (hρdiam : G.densityDiameter ρ = m) (hρmax : ∀ σ ∈ I, G.densityDiameter σ ≤ m)
    (hOld : lemma46FiniteSubensembleInvariant G I centerOf)
    (c : DensityPlusComponent G (insert ρ I) centerOf)
    {x y : V} (hx : x ∈ G.densityDomainPlus ρ (centerOf ρ))
    (hxc : x ∈ densityPlusComponentVertices G (insert ρ I) centerOf c)
    (hyc : y ∈ densityPlusComponentVertices G (insert ρ I) centerOf c)
    (hyA : y ∉ G.densityDomainPlus ρ (centerOf ρ)) :
    ∃ a ∈ G.densityDomainPlus ρ (centerOf ρ), ∃ dOld : ℕ,
      12 < m ∧ 12 * dOld < 5 * m ∧
      G.toSimpleGraph.dist y a ≤ dOld + 1 := by
  obtain ⟨cOld, hyOld, a, ha, b, hb, hab⟩ :=
    exists_adjacent_oldComponent_of_newComponent (G := G) I centerOf ρ c hx hxc hyc hyA
  obtain ⟨τ, _hτ, _hτmax, _hτscale, hmSmall, hdiam, hdist⟩ :=
    lemma46_attached_old_component_diameter_lt_five_twelfths hsep hG centerOf hI hρ
      hρnotI hneutral hcenter hρcenter hm hρdiam hρmax hOld cOld y a b ha hyOld hb hab
  exact ⟨a, ha, densityPlusComponentDiameter G I centerOf cOld, hmSmall, hdiam, hdist⟩

/-- If a component of the enlarged union misses the newly inserted `D⁺`, it is an unchanged old
component. Its unique maximal density and the factor-five diameter bound therefore pass directly
from the induction hypothesis. -/
theorem lemma46_unchangedComponent_invariant {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} {N₀ I : Finset (V → ℤ)} {ρ : V → ℤ}
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hI : I ⊆ N₀) (hρ : ρ ∈ N₀)
    (hρneutral : ∑ x, ρ x = 0) (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hneutral : ∀ σ ∈ N₀, ∑ x, σ x = 0)
    (hcenter : ∀ σ ∈ N₀, G.IsDensityCenter σ (centerOf σ))
    (hOld : lemma46FiniteSubensembleInvariant G I centerOf)
    (c : DensityPlusComponent G (insert ρ I) centerOf)
    (havoid : ∀ x ∈ densityPlusComponentVertices G (insert ρ I) centerOf c,
      x ∉ G.densityDomainPlus ρ (centerOf ρ))
    (hfamily : (densitiesContainedInComponent G (insert ρ I) centerOf c).Nonempty) :
    ∃ σ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c,
      (∀ τ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c,
        τ ≠ σ → G.densityDiameter τ < G.densityDiameter σ) ∧
      densityPlusComponentDiameter G (insert ρ I) centerOf c ≤ 5 * G.densityDiameter σ ∧
      (densityPlusExternalBoundary G (insert ρ I) centerOf c).card ≤
        16 * G.densityDiameter σ := by
  obtain ⟨σ₀, hσ₀component⟩ := hfamily
  have hσ₀mem : σ₀ ∈ insert ρ I :=
    (mem_densitiesContainedInComponent G (insert ρ I) centerOf c σ₀).1 hσ₀component |>.1
  have hσ₀N₀ : σ₀ ∈ N₀ := by
    rcases Finset.mem_insert.mp hσ₀mem with hEq | hσ₀I
    · exact hEq ▸ hρ
    · exact hI hσ₀I
  have hσ₀I : σ₀ ∈ I := by
    rcases Finset.mem_insert.mp hσ₀mem with hEq | hσ₀I
    · subst σ₀
      have hρD := G.mem_densityDomainPlus_of_center hG hρneutral hρcenter hρcenter.1
      have hρnew := densityDomainPlus_subset_componentVertices G (insert ρ I) centerOf c
        hσ₀component hρD
      exact False.elim (havoid (centerOf ρ) hρnew hρD)
    · exact hσ₀I
  have hσ₀neutral := hneutral σ₀ hσ₀N₀
  have hσ₀center := hcenter σ₀ hσ₀N₀
  have hzD : centerOf σ₀ ∈ G.densityDomainPlus σ₀ (centerOf σ₀) :=
    G.mem_densityDomainPlus_of_center hG hσ₀neutral hσ₀center hσ₀center.1
  have hzNew : centerOf σ₀ ∈ densityPlusComponentVertices G (insert ρ I) centerOf c :=
    densityDomainPlus_subset_componentVertices G (insert ρ I) centerOf c hσ₀component hzD
  have hzNotA := havoid (centerOf σ₀) hzNew
  have hzUnion : centerOf σ₀ ∈ densityPlusUnion G I centerOf := by
    have hzUnion' := (mem_densityPlusComponentVertices G (insert ρ I) centerOf c
      (centerOf σ₀)).1 hzNew |>.1
    rcases (mem_densityPlusUnion_insert G I centerOf ρ (centerOf σ₀)).1 hzUnion' with hzA | hzU
    · exact (hzNotA hzA).elim
    · exact hzU
  let cOld : DensityPlusComponent G I centerOf :=
    (densityPlusInducedGraph G I centerOf).connectedComponentMk ⟨centerOf σ₀, hzUnion⟩
  have hzOld : centerOf σ₀ ∈ densityPlusComponentVertices G I centerOf cOld :=
    (mem_densityPlusComponentVertices G I centerOf cOld (centerOf σ₀)).2 ⟨hzUnion, rfl⟩
  have hOldSubset : densityPlusComponentVertices G I centerOf cOld ⊆
      densityPlusComponentVertices G (insert ρ I) centerOf c :=
    oldComponent_subset_newComponent_of_mem I centerOf ρ cOld c hzOld hzNew
  have hNewSubset : densityPlusComponentVertices G (insert ρ I) centerOf c ⊆
      densityPlusComponentVertices G I centerOf cOld := by
    intro y hy
    obtain ⟨hyU, hreach⟩ := reachable_old_of_newComponent_avoiding_domain I centerOf ρ c
      hzUnion hzNew hy havoid
    have hclass : (densityPlusInducedGraph G I centerOf).connectedComponentMk ⟨y, hyU⟩ = cOld :=
      (SimpleGraph.ConnectedComponent.sound hreach).symm
    exact (mem_densityPlusComponentVertices G I centerOf cOld y).2 ⟨hyU, hclass⟩
  have hverticesEq : densityPlusComponentVertices G (insert ρ I) centerOf c =
      densityPlusComponentVertices G I centerOf cOld := by
    apply Finset.Subset.antisymm hNewSubset hOldSubset
  have hσ₀old : σ₀ ∈ densitiesContainedInComponent G I centerOf cOld := by
    apply (mem_densitiesContainedInComponent G I centerOf cOld σ₀).2
    refine ⟨hσ₀I, ?_⟩
    exact densityDomainPlus_subset_componentVertices_of_mem G hG I centerOf cOld
      hσ₀I hσ₀neutral hσ₀center hzD hzOld
  have hOldFamily : (densitiesContainedInComponent G I centerOf cOld).Nonempty :=
    ⟨σ₀, hσ₀old⟩
  obtain ⟨τ, hτold, hτstrict, hτdiam, hτboundary⟩ := hOld cOld hOldFamily
  have hτmem : τ ∈ I := (mem_densitiesContainedInComponent G I centerOf cOld τ).1 hτold |>.1
  have hτN₀ : τ ∈ N₀ := hI hτmem
  have hτneutral := hneutral τ hτN₀
  have hτcenter := hcenter τ hτN₀
  have hτnew : τ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c := by
    apply (mem_densitiesContainedInComponent G (insert ρ I) centerOf c τ).2
    refine ⟨Finset.mem_insert_of_mem hτmem, ?_⟩
    have hsubset := oldComponent_subset_newComponent_of_mem I centerOf ρ cOld c hzOld hzNew
    intro x hx
    exact hsubset (densityDomainPlus_subset_componentVertices G I centerOf cOld hτold hx)
  have hstrict : ∀ σ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c,
      σ ≠ τ → G.densityDiameter σ < G.densityDiameter τ := by
    intro σ hσ hne
    have hσmem : σ ∈ insert ρ I :=
      (mem_densitiesContainedInComponent G (insert ρ I) centerOf c σ).1 hσ |>.1
    have hσI : σ ∈ I := by
      rcases Finset.mem_insert.mp hσmem with hEq | hσI
      · subst σ
        have hρD := G.mem_densityDomainPlus_of_center hG hρneutral hρcenter hρcenter.1
        have hρnew := densityDomainPlus_subset_componentVertices G (insert ρ I) centerOf c
          hσ hρD
        exact False.elim (havoid (centerOf ρ) hρnew hρD)
      · exact hσI
    have hσN₀ : σ ∈ N₀ := hI hσI
    have hzσD : centerOf σ ∈ G.densityDomainPlus σ (centerOf σ) :=
      G.mem_densityDomainPlus_of_center hG (hneutral σ hσN₀)
        (hcenter σ hσN₀) (hcenter σ hσN₀).1
    have hzσNew := densityDomainPlus_subset_componentVertices G (insert ρ I) centerOf c hσ hzσD
    have hzσNotA := havoid (centerOf σ) hzσNew
    have hzσUnion' := (mem_densityPlusComponentVertices G (insert ρ I) centerOf c
      (centerOf σ)).1 hzσNew |>.1
    have hzσUnion : centerOf σ ∈ densityPlusUnion G I centerOf := by
      rcases (mem_densityPlusUnion_insert G I centerOf ρ (centerOf σ)).1 hzσUnion' with hA | hU
      · exact (hzσNotA hA).elim
      · exact hU
    obtain ⟨_, hreach⟩ := reachable_old_of_newComponent_avoiding_domain I centerOf ρ c
      hzUnion hzNew hzσNew havoid
    have hclass : (densityPlusInducedGraph G I centerOf).connectedComponentMk
        ⟨centerOf σ, hzσUnion⟩ = cOld := (SimpleGraph.ConnectedComponent.sound hreach).symm
    have hσold : σ ∈ densitiesContainedInComponent G I centerOf cOld := by
      apply (mem_densitiesContainedInComponent G I centerOf cOld σ).2
      refine ⟨?_, ?_⟩
      · exact hσI
      · exact densityDomainPlus_subset_componentVertices_of_mem G hG I centerOf cOld
          hσI (hneutral σ hσN₀) (hcenter σ hσN₀) hzσD
          ((mem_densityPlusComponentVertices G I centerOf cOld (centerOf σ)).2
            ⟨hzσUnion, hclass⟩)
    exact hτstrict σ hσold (by
      intro hEq
      exact hne hEq)
  have hdiamNew : densityPlusComponentDiameter G (insert ρ I) centerOf c ≤
      densityPlusComponentDiameter G I centerOf cOld := by
    unfold densityPlusComponentDiameter
    apply Finset.sup_le
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    exact dist_le_densityPlusComponentDiameter G I centerOf cOld (hNewSubset hp₁)
      (hNewSubset hp₂)
  have hboundaryEq : densityPlusExternalBoundary G (insert ρ I) centerOf c =
      densityPlusExternalBoundary G I centerOf cOld := by
    apply Finset.ext
    intro z
    simp [densityPlusExternalBoundary, hverticesEq]
  exact ⟨τ, hτnew, hstrict, hdiamNew.trans hτdiam, by
    rw [hboundaryEq]
    exact hτboundary⟩

/-- Every old density contained in a new component that meets the inserted `D⁺` is assigned to
an old component attached to that `D⁺`. The contact may be an overlap or an edge. -/
theorem exists_oldComponent_for_otherDensity {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} {I : Finset (V → ℤ)} {ρ : V → ℤ}
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G (insert ρ I) centerOf)
    {σ : V → ℤ} (hσI : σ ∈ I)
    (hσfull : σ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c)
    (hσneutral : ∑ x, σ x = 0) (hσcenter : G.IsDensityCenter σ (centerOf σ))
    {x₀' : V} (hx₀A : x₀' ∈ G.densityDomainPlus ρ (centerOf ρ))
    (hx₀c : x₀' ∈ densityPlusComponentVertices G (insert ρ I) centerOf c) :
    ∃ cOld : DensityPlusComponent G I centerOf,
      σ ∈ densitiesContainedInComponent G I centerOf cOld ∧
      ∃ a ∈ G.densityDomainPlus ρ (centerOf ρ),
        ∃ b ∈ densityPlusComponentVertices G I centerOf cOld,
          a = b ∨ G.toSimpleGraph.Adj a b := by
  have hzD : centerOf σ ∈ G.densityDomainPlus σ (centerOf σ) :=
    G.mem_densityDomainPlus_of_center hG hσneutral hσcenter hσcenter.1
  have hzNew : centerOf σ ∈ densityPlusComponentVertices G (insert ρ I) centerOf c :=
    densityDomainPlus_subset_componentVertices G (insert ρ I) centerOf c hσfull hzD
  by_cases hza : centerOf σ ∈ G.densityDomainPlus ρ (centerOf ρ)
  · have hzUnion : centerOf σ ∈ densityPlusUnion G I centerOf :=
      (mem_densityPlusUnion G I centerOf (centerOf σ)).2 ⟨σ, hσI, hzD⟩
    let cOld : DensityPlusComponent G I centerOf :=
      (densityPlusInducedGraph G I centerOf).connectedComponentMk ⟨centerOf σ, hzUnion⟩
    have hzOld : centerOf σ ∈ densityPlusComponentVertices G I centerOf cOld :=
      (mem_densityPlusComponentVertices G I centerOf cOld (centerOf σ)).2 ⟨hzUnion, rfl⟩
    have hσold : σ ∈ densitiesContainedInComponent G I centerOf cOld := by
      apply (mem_densitiesContainedInComponent G I centerOf cOld σ).2
      refine ⟨hσI, ?_⟩
      exact densityDomainPlus_subset_componentVertices_of_mem G hG I centerOf cOld
        hσI hσneutral hσcenter hzD hzOld
    exact ⟨cOld, hσold, centerOf σ, hza, centerOf σ, hzOld, Or.inl rfl⟩
  · obtain ⟨cOld, hzOld, a, ha, b, hb, hab⟩ :=
      exists_adjacent_oldComponent_of_newComponent (G := G) (I := I)
        (centerOf := centerOf) (ρ := ρ) (c := c) (x := x₀') (y := centerOf σ)
        hx₀A hx₀c hzNew hza
    have hσold : σ ∈ densitiesContainedInComponent G I centerOf cOld := by
      apply (mem_densitiesContainedInComponent G I centerOf cOld σ).2
      refine ⟨hσI, ?_⟩
      exact densityDomainPlus_subset_componentVertices_of_mem G hG I centerOf cOld
        hσI hσneutral hσcenter hzD hzOld
    exact ⟨cOld, hσold, a, ha, b, hb, hab⟩

/-- The merge transition for the strong finite-subensemble invariant. The maximal-scale density is
strictly larger than every old density absorbed into the component; its `D⁺` controls the new
component diameter by the factor five. The final conjunct is precisely the local  packing
step supplied by `lemma46BoundaryPackingStep`. -/
theorem lemma46_mergedComponent_invariant {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} {N₀ I : Finset (V → ℤ)} {ρ : V → ℤ}
    (hsep : KPTheorem22bNeutralSeparation G N₀ (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hpack : lemma46BoundaryPackingStep G N₀ centerOf)
    (hI : I ⊆ N₀) (hρ : ρ ∈ N₀) (hρnotI : ρ ∉ I)
    (hneutral : ∀ σ ∈ N₀, ∑ x, σ x = 0)
    (hcenter : ∀ σ ∈ N₀, G.IsDensityCenter σ (centerOf σ))
    (hρneutral : ∑ x, ρ x = 0) (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    {m : ℕ} (hm : 1 ≤ m) (hρdiam : G.densityDiameter ρ = m)
    (hρmax : ∀ σ ∈ I, G.densityDiameter σ ≤ m)
    (hOld : lemma46FiniteSubensembleInvariant G I centerOf)
    (c : DensityPlusComponent G (insert ρ I) centerOf)
    (hmeet : ∃ x ∈ G.densityDomainPlus ρ (centerOf ρ),
      x ∈ densityPlusComponentVertices G (insert ρ I) centerOf c) :
    ∃ σ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c,
      (∀ τ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c,
        τ ≠ σ → G.densityDiameter τ < G.densityDiameter σ) ∧
      densityPlusComponentDiameter G (insert ρ I) centerOf c ≤ 5 * G.densityDiameter σ ∧
      (densityPlusExternalBoundary G (insert ρ I) centerOf c).card ≤
        16 * G.densityDiameter σ := by
  obtain ⟨x₀, hx₀A, hx₀c⟩ := hmeet
  have hρcomponent : ρ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c := by
    apply (mem_densitiesContainedInComponent G (insert ρ I) centerOf c ρ).2
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    exact densityDomainPlus_subset_componentVertices_of_mem G hG (insert ρ I)
      centerOf c (Finset.mem_insert_self _ _) hρneutral hρcenter hx₀A hx₀c
  have hstrict : ∀ σ ∈ densitiesContainedInComponent G (insert ρ I) centerOf c,
      σ ≠ ρ → G.densityDiameter σ < G.densityDiameter ρ := by
    intro σ hσ hσne
    have hσins : σ ∈ insert ρ I :=
      (mem_densitiesContainedInComponent G (insert ρ I) centerOf c σ).1 hσ |>.1
    rcases Finset.mem_insert.mp hσins with hEq | hσI
    · exact (hσne hEq).elim
    · have hσN₀ := hI hσI
      have hσneutral := hneutral σ hσN₀
      have hσcenter := hcenter σ hσN₀
      obtain ⟨cOld, hσOld, a, ha, b, hb, hab⟩ :=
        exists_oldComponent_for_otherDensity hG centerOf c hσI hσ hσneutral hσcenter
          hx₀A hx₀c
      obtain ⟨τ, hτOld, hτmax, hτdiam, _hτboundary⟩ := hOld cOld
        ⟨σ, hσOld⟩
      have hτI : τ ∈ I :=
        (mem_densitiesContainedInComponent G I centerOf cOld τ).1 hτOld |>.1
      have hτN₀ := hI hτI
      have hτneutral := hneutral τ hτN₀
      have hτcenter := hcenter τ hτN₀
      have hτdiam_le : G.densityDiameter τ ≤ m := hρmax τ hτI
      have hτneρ : τ ≠ ρ := by
        intro heq
        subst τ
        exact hρnotI hτI
      have hτsmall := lemma46_attached_old_component_scale_lt_twelve hsep hG centerOf
        hI hρ hτI hτneρ.symm hτneutral hρcenter hτcenter hm hρdiam hτdiam_le cOld hτOld hτdiam
        ⟨a, ha, b, hb, hab⟩
      have hσleτ : G.densityDiameter σ ≤ G.densityDiameter τ := by
        by_cases hEq : σ = τ
        · rw [hEq]
        · exact Nat.le_of_lt (hτmax σ hσOld hEq)
      have : G.densityDiameter σ < m := by omega
      simpa [hρdiam] using this
  have hdiam : densityPlusComponentDiameter G (insert ρ I) centerOf c ≤ 5 * m := by
    unfold densityPlusComponentDiameter
    apply Finset.sup_le
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpx, hpy⟩
    by_cases hpxA : p.1 ∈ G.densityDomainPlus ρ (centerOf ρ)
    · by_cases hpyA : p.2 ∈ G.densityDomainPlus ρ (centerOf ρ)
      · exact (densityDomainPlus_diameter_le_four G hG ρ (centerOf ρ) hpxA hpyA).trans
          (by omega)
      · obtain ⟨a, ha, d, hd, hds, hdist⟩ := lemma46_externalPoint_attached_bound hsep
          hG centerOf hI hρ hρnotI hneutral hcenter hρcenter hm hρdiam hρmax hOld c
          hx₀A hx₀c hpy hpyA
        have hab := densityDomainPlus_diameter_le_four G hG ρ (centerOf ρ) hpxA ha
        have hxy := hG.dist_triangle (u := p.1) (v := a) (w := p.2)
        have hdist' : G.toSimpleGraph.dist a p.2 ≤ d + 1 := by
          rw [G.toSimpleGraph.dist_comm]
          exact hdist
        omega
    · obtain ⟨a, ha, d₁, hd₁, hds₁, hdist₁⟩ := lemma46_externalPoint_attached_bound hsep
        hG centerOf hI hρ hρnotI hneutral hcenter hρcenter hm hρdiam hρmax hOld c
        hx₀A hx₀c hpx hpxA
      by_cases hpyA : p.2 ∈ G.densityDomainPlus ρ (centerOf ρ)
      · have hab := densityDomainPlus_diameter_le_four G hG ρ (centerOf ρ) ha hpyA
        have hxy := hG.dist_triangle (u := p.1) (v := a) (w := p.2)
        have hdist' : G.toSimpleGraph.dist a p.1 ≤ d₁ + 1 := by
          rw [G.toSimpleGraph.dist_comm]
          exact hdist₁
        omega
      · obtain ⟨b, hb, d₂, hd₂, hds₂, hdist₂⟩ := lemma46_externalPoint_attached_bound hsep
          hG centerOf hI hρ hρnotI hneutral hcenter hρcenter hm hρdiam hρmax hOld c
          hx₀A hx₀c hpy hpyA
        have hab := densityDomainPlus_diameter_le_four G hG ρ (centerOf ρ) ha hb
        have hxy₁ := hG.dist_triangle (u := p.1) (v := a) (w := p.2)
        have hxy₂ := hG.dist_triangle (u := a) (v := b) (w := p.2)
        have hdist₁' : G.toSimpleGraph.dist a p.1 ≤ d₁ + 1 := by
          rw [G.toSimpleGraph.dist_comm]
          exact hdist₁
        have hdist₂' : G.toSimpleGraph.dist b p.2 ≤ d₂ + 1 := by
          rw [G.toSimpleGraph.dist_comm]
          exact hdist₂
        omega
  have hboundary := hpack I ρ m hI hρ hρnotI hρneutral hρcenter hneutral hcenter hsep hm
    hρdiam hρmax hOld c ⟨x₀, hx₀A, hx₀c⟩ hdiam
  refine ⟨ρ, hρcomponent, ?_, ?_, ?_⟩
  · simpa [hρdiam] using hstrict
  · simpa [hρdiam] using hdiam
  · simpa [hρdiam] using hboundary

/-- Strong induction over finite subensembles, adding densities in decreasing diameter order.
Each step removes a largest density; components that miss its `D⁺` are unchanged, and components
that meet it use the merge transition above. The boundary packing input is explicit. -/
theorem lemma46_finiteSubensembleInvariant_of_boundaryPacking {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} {N₀ : Finset (V → ℤ)}
    (hsep : KPTheorem22bNeutralSeparation G N₀ (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hpack : ∀ I ⊆ N₀, lemma46BoundaryPackingStep G N₀ centerOf)
    (hneutral : ∀ ρ ∈ N₀, ∑ x, ρ x = 0)
    (hcenter : ∀ ρ ∈ N₀, G.IsDensityCenter ρ (centerOf ρ)) :
    ∀ I ⊆ N₀, lemma46FiniteSubensembleInvariant G I centerOf := by
  have hmain : ∀ n (I : Finset (V → ℤ)), I.card = n → I ⊆ N₀ →
      lemma46FiniteSubensembleInvariant G I centerOf := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I hcard hI
      classical
      by_cases hInonempty : I.Nonempty
      · obtain ⟨ρ, hρI, hρmax⟩ := Finset.exists_max_image I G.densityDiameter hInonempty
        let J := I.erase ρ
        have hJsub : J ⊂ I := Finset.erase_ssubset hρI
        have hJN₀ : J ⊆ N₀ := fun σ hσ => hI (Finset.mem_of_mem_erase hσ)
        have hIcardpos : 0 < I.card := Finset.card_pos.mpr ⟨ρ, hρI⟩
        have hJcard : J.card < n := by
          have hErase : J.card + 1 = I.card := by
            simp [J, hρI]
            omega
          omega
        have hOld := ih J.card hJcard J rfl hJN₀
        have hρN₀ := hI hρI
        have hρneutral := hneutral ρ hρN₀
        have hρcenter := hcenter ρ hρN₀
        have hρneJ : ρ ∉ J := by simp [J]
        have hmax : ∀ σ ∈ J, G.densityDiameter σ ≤ G.densityDiameter ρ := by
          intro σ hσ
          exact hρmax σ (Finset.mem_of_mem_erase hσ)
        have hρdiamPos : 1 ≤ G.densityDiameter ρ :=
          G.one_le_densityDiameter_of_neutral hG ρ (fun h => hρcenter.1 (by simp [h])) hρneutral
        have hnew : insert ρ J = I := by
          simp [J, hρI]
        rw [← hnew]
        intro c hfamily
        by_cases hmeet : ∃ x ∈ G.densityDomainPlus ρ (centerOf ρ),
            x ∈ densityPlusComponentVertices G (insert ρ J) centerOf c
        · exact lemma46_mergedComponent_invariant hsep hG centerOf (hpack J hJN₀)
            hJN₀ hρN₀ hρneJ hneutral hcenter hρneutral hρcenter hρdiamPos rfl hmax hOld c hmeet
        · apply lemma46_unchangedComponent_invariant hG centerOf hJN₀ hρN₀ hρneutral hρcenter
            hneutral hcenter hOld c ?_ hfamily
          intro x hxC hxA
          exact hmeet ⟨x, hxA, hxC⟩
      · intro c hfamily
        obtain ⟨σ, hσ⟩ := hfamily
        have hσmem : σ ∈ I := (mem_densitiesContainedInComponent G I centerOf c σ).1 hσ |>.1
        exact (hInonempty ⟨σ, hσmem⟩).elim
  intro I hI
  exact hmain I.card I rfl hI

/-- T2.2(b) in the exact spin-wave component API follows from `IsScaleSeparated` in the charge
API. The root lies in the neutral ensemble here, so both clauses are instances of its pairwise
neutral separation clause. -/
theorem kpTheorem22bSeparation_of_scaleSeparated {L : ℕ} {E : Type}
    [Fintype E] (boundary : SquareBoundary)
    (Λ : Multigraph (Fin L × Fin L) E)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    {N : Finset (Fin L × Fin L → ℤ)} (hscale : IsScaleSeparated boundary L N) :
    KPTheorem22bNeutralSeparation Λ (neutralPart N) (2 ^ 16 : ℝ) (7 / 4 : ℝ) := by
  intro ρ hρ σ hσ hne
  have hρN : ρ ∈ N := (mem_neutralPart.mp hρ).1
  have hσN : σ ∈ N := (mem_neutralPart.mp hσ).1
  have hdist' := IsScaleSeparated.le_densitySupportDistance boundary Λ hdist hscale hρN hσN hne
  exact_mod_cast hdist'

/-- A component of the induced union always contains at least one full enlarged density domain,
provided each member has the neutral connectedness hypotheses. -/
theorem densitiesContainedInComponent_nonempty {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} (hG : G.toSimpleGraph.Connected)
    (I : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (hneutral : ∀ ρ ∈ I, ∑ x, ρ x = 0)
    (hcenter : ∀ ρ ∈ I, G.IsDensityCenter ρ (centerOf ρ))
    (c : DensityPlusComponent G I centerOf) :
    (densitiesContainedInComponent G I centerOf c).Nonempty := by
  obtain ⟨z, hzc⟩ := Quot.exists_rep c
  rcases (mem_densityPlusUnion G I centerOf z.1).1 z.2 with ⟨ρ, hρI, hzD⟩
  have hρneutral := hneutral ρ hρI
  have hρcenter := hcenter ρ hρI
  have hzC : z.1 ∈ densityPlusComponentVertices G I centerOf c := by
    apply (mem_densityPlusComponentVertices G I centerOf c z.1).2
    exact ⟨z.2, hzc⟩
  have hρC : ρ ∈ densitiesContainedInComponent G I centerOf c := by
    apply (mem_densitiesContainedInComponent G I centerOf c ρ).2
    refine ⟨hρI, ?_⟩
    exact densityDomainPlus_subset_componentVertices_of_mem G hG I centerOf c
      hρI hρneutral hρcenter hzD hzC
  exact ⟨ρ, hρC⟩

/-- Conditional component-separation package for KP Lemma 4.6(1). Once the finite-subensemble
invariant supplies the unique maximizing densities and their factor-five diameter bounds, this is
exactly the `Lemma46Arithmetic` reduction of T2.2(b) to the component distance. -/
theorem lemma46_component_separation_of_finiteInvariant {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} {N₀ : Finset (V → ℤ)}
    (hsep : KPTheorem22bNeutralSeparation G N₀ (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hneutral : ∀ ρ ∈ N₀, ∑ x, ρ x = 0)
    (hcenter : ∀ ρ ∈ N₀, G.IsDensityCenter ρ (centerOf ρ))
    (hInv : lemma46FiniteSubensembleInvariant G N₀ centerOf)
    (c c' : DensityPlusComponent G N₀ centerOf) (hc : c ≠ c')
    (hcFamily : (densitiesContainedInComponent G N₀ centerOf c).Nonempty)
    (hc'Family : (densitiesContainedInComponent G N₀ centerOf c').Nonempty) :
    ((2 ^ 16 : ℝ) / 25) *
        (↑(min (densityPlusComponentDiameter G N₀ centerOf c)
          (densityPlusComponentDiameter G N₀ centerOf c') : ℕ) : ℝ) ^ (7 / 4 : ℝ) ≤
      (↑(densityPlusComponentDistance G N₀ centerOf c c' +
        densityPlusComponentDiameter G N₀ centerOf c +
        densityPlusComponentDiameter G N₀ centerOf c') : ℝ) := by
  obtain ⟨ρ, hρcomponent, hρstrict, hρdiam, _hρboundary⟩ := hInv c hcFamily
  obtain ⟨σ, hσcomponent, hσstrict, hσdiam, _hσboundary⟩ := hInv c' hc'Family
  have hρN₀ : ρ ∈ N₀ := (mem_densitiesContainedInComponent G N₀ centerOf c ρ).1
    hρcomponent |>.1
  have hσN₀ : σ ∈ N₀ := (mem_densitiesContainedInComponent G N₀ centerOf c' σ).1
    hσcomponent |>.1
  have hρneutral := hneutral ρ hρN₀
  have hσneutral := hneutral σ hσN₀
  have hρcenter := hcenter ρ hρN₀
  have hσcenter := hcenter σ hσN₀
  have hρneσ : ρ ≠ σ := by
    intro hEq
    subst σ
    have hzD := G.mem_densityDomainPlus_of_center hG hρneutral hρcenter hρcenter.1
    have hzC := densityDomainPlus_subset_componentVertices G N₀ centerOf c hρcomponent hzD
    have hzC' := densityDomainPlus_subset_componentVertices G N₀ centerOf c' hσcomponent hzD
    have hclass := (mem_densityPlusComponentVertices G N₀ centerOf c (centerOf ρ)).1 hzC |>.2
    have hclass' := (mem_densityPlusComponentVertices G N₀ centerOf c' (centerOf ρ)).1 hzC' |>.2
    exact hc (hclass.symm.trans hclass')
  have hsupport := hsep ρ hρN₀ σ hσN₀ hρneσ
  have hgeom := densitySupportDistance_le_componentDistance_add G hG N₀ centerOf c c'
    hρcomponent hσcomponent hρneutral hσneutral hρcenter hσcenter
    ⟨centerOf ρ, hρcenter.1⟩ ⟨centerOf σ, hσcenter.1⟩
  have hgeom' : (↑(densitySupportDistance G ρ σ) : ℝ) ≤
      (↑(densityPlusComponentDistance G N₀ centerOf c c' +
        densityPlusComponentDiameter G N₀ centerOf c +
        densityPlusComponentDiameter G N₀ centerOf c') : ℝ) := by
    exact_mod_cast hgeom
  exact lemma46_pair_scale_bound hρdiam hσdiam (by norm_num) (by norm_num) (by norm_num)
    hsupport hgeom'

/-- Root-scale arithmetic for a neutral distinguished density. Comparability gives only half of
the T2.2(b) pair scale, `d(ρ)/2`; the loss `128` still absorbs the factor ten between the
component and the comparison scale. -/
theorem lemma46_root_scale_bound_half {dE dρ : ℕ} (hdE : 4 ≤ dE)
    (hscale : dE ≤ 5 * dρ) :
    ((2 ^ 16 : ℝ) / 128) * (dE : ℝ) ^ (7 / 4 : ℝ) + dE ≤
      (2 ^ 16 : ℝ) * ((dρ : ℝ) / 2) ^ (7 / 4 : ℝ) := by
  let d : ℝ := dE
  let q : ℝ := dρ
  have hd0 : 0 < d := by dsimp [d]; exact_mod_cast (by omega : 0 < dE)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hscale' : d ≤ 5 * q := by
    dsimp [d, q]
    exact_mod_cast hscale
  have hdiv : d / 10 ≤ q / 2 := by dsimp [d, q]; linarith
  have hten : (10 : ℝ) ^ (7 / 4 : ℝ) < 100 := by
    calc
      (10 : ℝ) ^ (7 / 4 : ℝ) < (10 : ℝ) ^ (2 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        norm_num
      _ = 100 := by norm_num [Real.rpow_natCast]
  have hdivPow : (d / 10) ^ (7 / 4 : ℝ) =
      d ^ (7 / 4 : ℝ) / (10 : ℝ) ^ (7 / 4 : ℝ) :=
    Real.div_rpow (le_of_lt hd0) (by norm_num : 0 ≤ (10 : ℝ)) _
  have hrecip : (1 : ℝ) / 100 ≤ 1 / (10 : ℝ) ^ (7 / 4 : ℝ) := by
    apply one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 10) _)
    exact le_of_lt hten
  have hdPow0 : 0 ≤ d ^ (7 / 4 : ℝ) := Real.rpow_nonneg (le_of_lt hd0) _
  have hquarter : d ^ (7 / 4 : ℝ) / 100 ≤ (d / 10) ^ (7 / 4 : ℝ) := by
    rw [hdivPow]
    calc
      d ^ (7 / 4 : ℝ) / 100 = d ^ (7 / 4 : ℝ) * (1 / 100) := by ring
      _ ≤ d ^ (7 / 4 : ℝ) * (1 / (10 : ℝ) ^ (7 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip hdPow0
      _ = d ^ (7 / 4 : ℝ) / (10 : ℝ) ^ (7 / 4 : ℝ) := by ring
  have hmonotone : (d / 10) ^ (7 / 4 : ℝ) ≤ (q / 2) ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hdiv (by norm_num)
  have hdge1 : 1 ≤ d := by dsimp [d]; exact_mod_cast (by omega : 1 ≤ dE)
  have hdPowLe : d ≤ d ^ (7 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hdge1 (by norm_num : (1 : ℝ) ≤ 7 / 4)
    simpa [Real.rpow_one, d] using h
  have hcoef : (1 : ℝ) / 128 + 1 / (2 ^ 16 : ℝ) ≤ 1 / 100 := by norm_num
  have hsmall : d ^ (7 / 4 : ℝ) / 128 + d / (2 ^ 16 : ℝ) ≤
      d ^ (7 / 4 : ℝ) / 100 := by
    calc
      d ^ (7 / 4 : ℝ) / 128 + d / (2 ^ 16 : ℝ) ≤
          d ^ (7 / 4 : ℝ) / 128 + d ^ (7 / 4 : ℝ) / (2 ^ 16 : ℝ) := by
            exact add_le_add (le_refl _) <|
              div_le_div_of_nonneg_right hdPowLe (by norm_num : (0 : ℝ) ≤ 2 ^ 16)
      _ = d ^ (7 / 4 : ℝ) * ((1 : ℝ) / 128 + 1 / (2 ^ 16 : ℝ)) := by ring
      _ ≤ d ^ (7 / 4 : ℝ) / 100 := by nlinarith [hcoef, hdPow0]
  calc
    ((2 ^ 16 : ℝ) / 128) * d ^ (7 / 4 : ℝ) + d =
        (2 ^ 16 : ℝ) * (d ^ (7 / 4 : ℝ) / 128 + d / (2 ^ 16 : ℝ)) := by ring
    _ ≤ (2 ^ 16 : ℝ) * (d ^ (7 / 4 : ℝ) / 100) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ ≤ (2 ^ 16 : ℝ) * (d / 10) ^ (7 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hquarter (by norm_num)
    _ ≤ (2 ^ 16 : ℝ) * (q / 2) ^ (7 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hmonotone (by norm_num)

/-- The same root-scale estimate for components of diameter at most three; the half-scale
T2.2(b) separation is already far larger than the requested component bound. -/
theorem lemma46_root_scale_bound_half_small {dE dρ : ℕ} (hdE : dE < 4)
    (hρ : 1 ≤ dρ) :
    ((2 ^ 16 : ℝ) / 128) * (dE : ℝ) ^ (7 / 4 : ℝ) + dE ≤
      (2 ^ 16 : ℝ) * ((dρ : ℝ) / 2) ^ (7 / 4 : ℝ) := by
  have hdE3 : (dE : ℝ) ≤ 3 := by exact_mod_cast (by omega : dE ≤ 3)
  have hpowE : (dE : ℝ) ^ (7 / 4 : ℝ) ≤ (3 : ℝ) ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hdE3 (by norm_num)
  have hpow3 : (3 : ℝ) ^ (7 / 4 : ℝ) ≤ 9 := by
    calc
      (3 : ℝ) ^ (7 / 4 : ℝ) ≤ (3 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 9 := by norm_num [Real.rpow_natCast]
  have hρhalf : (1 : ℝ) / 2 ≤ (dρ : ℝ) / 2 := by
    have hρ' : (1 : ℝ) ≤ (dρ : ℝ) := by exact_mod_cast hρ
    exact div_le_div_of_nonneg_right hρ' (by norm_num)
  have hpowhalf : (1 : ℝ) / 4 ≤ ((dρ : ℝ) / 2) ^ (7 / 4 : ℝ) := by
    have hbase : (1 : ℝ) / 2 ≤ (dρ : ℝ) / 2 := hρhalf
    have hmono : ((1 : ℝ) / 2) ^ (7 / 4 : ℝ) ≤ ((dρ : ℝ) / 2) ^ (7 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hbase (by norm_num)
    have hquarter : (1 : ℝ) / 4 ≤ (1 / 2 : ℝ) ^ (7 / 4 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (by norm_num : (7 / 4 : ℝ) ≤ 2)
      norm_num at h
      exact h
    exact hquarter.trans hmono
  have hupper : ((2 ^ 16 : ℝ) / 128) * (dE : ℝ) ^ (7 / 4 : ℝ) + dE ≤
      (2 ^ 16 : ℝ) / 4 := by
    have hdE' : (dE : ℝ) ≤ 3 := hdE3
    have hpowE' : (dE : ℝ) ^ (7 / 4 : ℝ) ≤ 9 := hpowE.trans hpow3
    nlinarith
  have hrhs : (2 ^ 16 : ℝ) / 4 ≤
      (2 ^ 16 : ℝ) * ((dρ : ℝ) / 2) ^ (7 / 4 : ℝ) := by
    nlinarith [hpowhalf]
  exact hupper.trans hrhs

/--
Conditional component-to-root package for KP Lemma 4.6(2).

It applies the T2.2(b)
root-support separation to the finite-subensemble invariant's maximal density and then invokes
`lemma46_component_root_separation_bound`.
-/
theorem lemma46_root_separation_of_finiteInvariant {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq (V → ℤ)]
    {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {ρstar : V → ℤ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar (2 ^ 16 : ℝ) (7 / 4 : ℝ))
    (hG : G.toSimpleGraph.Connected) (centerOf : (V → ℤ) → V)
    (hneutral : ∀ ρ ∈ N₀, ∑ x, ρ x = 0)
    (hcenter : ∀ ρ ∈ N₀, G.IsDensityCenter ρ (centerOf ρ))
    (hInv : lemma46FiniteSubensembleInvariant G N₀ centerOf)
    (c : DensityPlusComponent G N₀ centerOf)
    (hcFamily : (densitiesContainedInComponent G N₀ centerOf c).Nonempty)
    (hρstarNonneutral : ∑ x, ρstar x ≠ 0)
    (hρstarSupport : ∃ x, ρstar x ≠ 0)
    (hdE : 4 ≤ densityPlusComponentDiameter G N₀ centerOf c) :
    ((2 ^ 16 : ℝ) / 128) *
        (↑(densityPlusComponentDiameter G N₀ centerOf c) : ℝ) ^ (7 / 4 : ℝ) ≤
      (↑(densityPlusComponentRootDistance G N₀ centerOf c ρstar) : ℝ) := by
  obtain ⟨ρ, hρcomponent, hρstrict, hρdiam, _hρboundary⟩ := hInv c hcFamily
  have hρN₀ : ρ ∈ N₀ := (mem_densitiesContainedInComponent G N₀ centerOf c ρ).1
    hρcomponent |>.1
  have hρneutral := hneutral ρ hρN₀
  have hρcenter := hcenter ρ hρN₀
  have hρne : ρ ≠ ρstar := by
    intro hEq
    apply hρstarNonneutral
    simpa [hEq] using hρneutral
  exact lemma46_component_root_separation_bound hsep hG centerOf c hρN₀ hρne
    hρcomponent hρneutral hρcenter ⟨centerOf ρ, hρcenter.1⟩ hρstarSupport
    hdE hρdiam


/-- The boundary-shell packing input needed to establish the strong induction invariant on a square carrier. It asks
for the local  boundary-shell packing step for each neutral subensemble and root. -/
def l46BoundaryPackingInput {L : ℕ} {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) : Prop :=
  ∀ centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L,
    (∀ ρ : Fin L × Fin L → ℤ, ρ ≠ 0 → Λ.IsDensityCenter ρ (centerOf ρ)) →
    ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N →
      ∀ ρstar ∈ neutralPart N, ∀ I ⊆ neutralPart N,
        lemma46BoundaryPackingStep Λ (neutralPart N) centerOf

/--
L4.6 on one square carrier, conditional only on the merge shell-packing proposition
`l46BoundaryPackingInput`.

The exact `L46Step` clauses follow from the strong finite-subensemble
induction, the support-distance estimates, and the boundary conversion in `ShellPacking`.
-/
theorem l46Step_of_boundaryPacking (boundary : SquareBoundary) {L : ℕ} {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E)
    (hG : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (hpack : l46BoundaryPackingInput Λ) :
    L46Step boundary Λ := by
  intro centerOf hcenterAdmissible N hN _hAtMost hscale _hSplit ρstar hρstar c
  let N₀ := neutralPart N
  let I := Λ.comparableDensities N₀ ρstar
  have hIle : I ⊆ N₀ := Λ.comparableDensities_subset N₀ ρstar
  have hdist' : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y := hdist
  have hsep := kpTheorem22bSeparation_of_scaleSeparated boundary Λ hdist' hscale
  have hM : (2 ^ 16 : ℝ) = 65536 := by norm_num
  have hneutralN₀ : ∀ ρ ∈ N₀, ∑ x, ρ x = 0 := by
    intro ρ hρ
    exact (mem_neutralPart.mp hρ).2
  have hcenterN₀ : ∀ ρ ∈ N₀, Λ.IsDensityCenter ρ (centerOf ρ) := by
    intro ρ hρ
    exact hcenterAdmissible ρ (hN.1 ρ (mem_neutralPart.mp hρ |>.1))
  have hInvN₀ : ∀ J ⊆ N₀, lemma46FiniteSubensembleInvariant Λ J centerOf :=
    lemma46_finiteSubensembleInvariant_of_boundaryPacking hsep hG centerOf
      (fun J hJ => hpack centerOf hcenterAdmissible N hN ρstar hρstar J hJ)
      hneutralN₀ hcenterN₀
  have hInv : lemma46FiniteSubensembleInvariant Λ I centerOf := hInvN₀ I hIle
  have hneutralI : ∀ ρ ∈ I, ∑ x, ρ x = 0 := fun ρ hρ => hneutralN₀ ρ (hIle hρ)
  have hcenterI : ∀ ρ ∈ I, Λ.IsDensityCenter ρ (centerOf ρ) := fun ρ hρ =>
    hcenterN₀ ρ (hIle hρ)
  have hcFamily : (densitiesContainedInComponent Λ I centerOf c).Nonempty :=
    densitiesContainedInComponent_nonempty hG I centerOf hneutralI hcenterI c
  have hsepI : KPTheorem22bNeutralSeparation Λ I (2 ^ 16 : ℝ) (7 / 4 : ℝ) := by
    intro ρ hρ σ hσ hne
    exact hsep ρ (hIle hρ) σ (hIle hσ) hne
  constructor
  · intro c' hc'
    have hc'Family : (densitiesContainedInComponent Λ I centerOf c').Nonempty :=
      densitiesContainedInComponent_nonempty hG I centerOf hneutralI hcenterI c'
    have hbound := lemma46_component_separation_of_finiteInvariant hsepI hG centerOf
      hneutralI hcenterI hInv c c' hc' hcFamily hc'Family
    simpa [I, N₀, chargeCoverScale, chargeCoverExponent, hM] using hbound
  constructor
  · obtain ⟨ρ, hρcomponent, _hρmax, hdiam, _hboundary⟩ := hInv c hcFamily
    have hρI : ρ ∈ I := (mem_densitiesContainedInComponent Λ I centerOf c ρ).1
      hρcomponent |>.1
    have hρN : ρ ∈ N := (mem_neutralPart.mp (hIle hρI)).1
    have hρneutral := hneutralI ρ hρI
    have hρcenter := hcenterI ρ hρI
    obtain ⟨_hρN₀, hρscale, hρneStar⟩ := (Λ.mem_comparableDensities).1 hρI
    have hρsupport : ∃ x, ρ x ≠ 0 := by
      by_contra hempty
      apply hN.1 ρ hρN
      funext x
      by_contra hx
      exact hempty ⟨x, hx⟩
    have hρstarN : ρstar ∈ N := (mem_neutralPart.mp hρstar).1
    have hρstarSupport : ∃ x, ρstar x ≠ 0 := by
      by_contra hempty
      apply hN.1 ρstar hρstarN
      funext x
      by_contra hx
      exact hempty ⟨x, hx⟩
    have hρdiamPos : 1 ≤ Λ.densityDiameter ρ :=
      Λ.one_le_densityDiameter_of_neutral hG ρ
        (fun h => hρcenter.1 (by simp [h])) hρneutral
    have hhalf := IsScaleSeparated.half_le_densitySupportDistance boundary Λ hdist' hscale
      hρN hρstarN hρneStar.symm hρscale
    have hhalf' : (2 ^ 16 : ℝ) * ((Λ.densityDiameter ρ : ℝ) / 2) ^ (7 / 4 : ℝ) ≤
        (↑(densitySupportDistance Λ ρ ρstar) : ℝ) := by exact_mod_cast hhalf
    have hgeom := densitySupportDistance_le_componentRootDistance_add Λ hG I centerOf c
      hρcomponent hρneutral hρcenter hρsupport hρstarSupport
    have hgeom' : (↑(densitySupportDistance Λ ρ ρstar) : ℝ) ≤
        (↑(densityPlusComponentRootDistance Λ I centerOf c ρstar) : ℝ) +
          densityPlusComponentDiameter Λ I centerOf c := by exact_mod_cast hgeom
    by_cases hdE : 4 ≤ densityPlusComponentDiameter Λ I centerOf c
    · have harith := lemma46_root_scale_bound_half hdE hdiam
      have hrootBound : ((2 ^ 16 : ℝ) / 128) *
          (↑(densityPlusComponentDiameter Λ I centerOf c) : ℝ) ^ (7 / 4 : ℝ) ≤
          (↑(densityPlusComponentRootDistance Λ I centerOf c ρstar) : ℝ) := by linarith
      simpa [I, N₀, chargeCoverScale, chargeCoverExponent, hM] using hrootBound
    · have hdEsmall : densityPlusComponentDiameter Λ I centerOf c < 4 := lt_of_not_ge hdE
      have harith := lemma46_root_scale_bound_half_small hdEsmall hρdiamPos
      have hrootBound : ((2 ^ 16 : ℝ) / 128) *
          (↑(densityPlusComponentDiameter Λ I centerOf c) : ℝ) ^ (7 / 4 : ℝ) ≤
          (↑(densityPlusComponentRootDistance Λ I centerOf c ρstar) : ℝ) := by linarith
      simpa [I, N₀, chargeCoverScale, chargeCoverExponent, hM] using hrootBound
  · have hboundary := lemma46_externalBoundary_card_le_of_strongInvariant hG I centerOf
      hneutralI hcenterI hInv c hcFamily
    simpa [I, N₀] using hboundary

/-- The exact KP Lemma 4.6 statement follows once boundary-shell packing discharges the local boundary-shell packing
input on the free and even-periodic square carriers. -/
theorem l46Statement_of_boundaryPacking :
    (∀ L : ℕ, 1 < L → l46BoundaryPackingInput (squareFree L)) →
    (∀ L : ℕ, 1 < L → Even L → l46BoundaryPackingInput (squarePeriodic L)) →
    l46Statement := by
  intro hfree hperiodic L hL
  constructor
  · exact l46Step_of_boundaryPacking .free (squareFree L) (squareFree_connected L hL)
      (fun _ _ => rfl) (hfree L hL)
  · intro hEven
    exact l46Step_of_boundaryPacking .periodic (squarePeriodic L)
      (squarePeriodic_connected L hL) (fun _ _ => rfl) (hperiodic L hL hEven)


end FroehlichSpencer.BKT.SpinWaves

end
