/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Green
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Tactic.Ring

/-!
# Transport of finite multigraph potential theory

An isomorphism consists of bijections on vertices and edges, with each edge's
endpoint pair preserved up to reversal. This makes the arbitrary orientation
of the multigraph invisible to its Laplacian, energy, and Green operator.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v w x

/-- An isomorphism of finite multigraphs, allowing each edge orientation to
be preserved or reversed. -/
structure Multigraph.Isomorphism {V : Type u} {E : Type v}
    {W : Type w} {F : Type x} (G : Multigraph V E) (H : Multigraph W F) where
  /-- The bijection of vertex carriers. -/
  vertices : V ≃ W
  /-- The bijection of edge carriers. -/
  edges : E ≃ F
  /-- Corresponding edges have the same unordered endpoint pair. -/
  endpoints : ∀ e,
    (H.src (edges e) = vertices (G.src e) ∧
      H.tgt (edges e) = vertices (G.tgt e)) ∨
    (H.src (edges e) = vertices (G.tgt e) ∧
      H.tgt (edges e) = vertices (G.src e))

namespace Multigraph.Isomorphism

variable {V : Type u} {E : Type v} {W : Type w} {F : Type x}
variable {G : Multigraph V E} {H : Multigraph W F}

/-- The total number of edge ends at a vertex is preserved by a multigraph isomorphism,
including isomorphisms which reverse some edge orientations. -/
theorem endpointDegree_eq (I : Isomorphism G H) [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq W] (v : V) :
    (Finset.univ.filter fun e => G.src e = v).card +
        (Finset.univ.filter fun e => G.tgt e = v).card =
      (Finset.univ.filter fun e => H.src e = I.vertices v).card +
        (Finset.univ.filter fun e => H.tgt e = I.vertices v).card := by
  classical
  have hterm (e : E) :
      (if G.src e = v then 1 else 0) + (if G.tgt e = v then 1 else 0) =
        (if H.src (I.edges e) = I.vertices v then 1 else 0) +
          (if H.tgt (I.edges e) = I.vertices v then 1 else 0) := by
    rcases I.endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simp [hs, ht, I.vertices.injective.eq_iff]
    · simp [hs, ht, I.vertices.injective.eq_iff]
      omega
  have hsum :
      (∑ e, if G.src e = v then 1 else 0) +
          (∑ e, if G.tgt e = v then 1 else 0) =
        (∑ e', if H.src e' = I.vertices v then 1 else 0) +
          (∑ e', if H.tgt e' = I.vertices v then 1 else 0) := by
    calc
      _ = ∑ e, ((if G.src e = v then 1 else 0) +
          (if G.tgt e = v then 1 else 0)) := by rw [Finset.sum_add_distrib]
      _ = ∑ e', ((if H.src e' = I.vertices v then 1 else 0) +
          (if H.tgt e' = I.vertices v then 1 else 0)) := by
        exact (Fintype.sum_equiv I.edges
          (fun e => (if G.src e = v then 1 else 0) + (if G.tgt e = v then 1 else 0))
          (fun e' => (if H.src e' = I.vertices v then 1 else 0) +
            (if H.tgt e' = I.vertices v then 1 else 0)) hterm)
      _ = _ := by rw [Finset.sum_add_distrib]
  have hcardGsrc : (Finset.univ.filter fun e => G.src e = v).card =
      ∑ e, if G.src e = v then 1 else 0 := by
    exact Finset.card_filter (fun e => G.src e = v) Finset.univ
  have hcardGtgt : (Finset.univ.filter fun e => G.tgt e = v).card =
      ∑ e, if G.tgt e = v then 1 else 0 := by
    exact Finset.card_filter (fun e => G.tgt e = v) Finset.univ
  have hcardHsrc : (Finset.univ.filter fun e => H.src e = I.vertices v).card =
      ∑ e, if H.src e = I.vertices v then 1 else 0 := by
    exact Finset.card_filter (fun e => H.src e = I.vertices v) Finset.univ
  have hcardHtgt : (Finset.univ.filter fun e => H.tgt e = I.vertices v).card =
      ∑ e, if H.tgt e = I.vertices v then 1 else 0 := by
    exact Finset.card_filter (fun e => H.tgt e = I.vertices v) Finset.univ
  rw [hcardGsrc, hcardGtgt, hcardHsrc, hcardHtgt]
  exact hsum

/-- Push a vertex function forward through a graph isomorphism. -/
def pushField (I : Isomorphism G H) {R : Type*} (f : V → R) : W → R :=
  fun w => f (I.vertices.symm w)

/-- Pull a vertex function back through a graph isomorphism. -/
def pullField (I : Isomorphism G H) {R : Type*} (f : W → R) : V → R :=
  fun v => f (I.vertices v)

@[simp]
theorem pushField_apply (I : Isomorphism G H) {R : Type*} (f : V → R) (w : W) :
    I.pushField f w = f (I.vertices.symm w) := rfl

@[simp]
theorem pullField_apply (I : Isomorphism G H) {R : Type*} (f : W → R) (v : V) :
    I.pullField f v = f (I.vertices v) := rfl

@[simp]
theorem pull_pushField (I : Isomorphism G H) {R : Type*} (f : V → R) :
    I.pullField (I.pushField f) = f := by
  funext v
  simp [pushField, pullField]

@[simp]
theorem push_pullField (I : Isomorphism G H) {R : Type*} (f : W → R) :
    I.pushField (I.pullField f) = f := by
  funext w
  simp [pushField, pullField]

/-- Adjacency is preserved and reflected by an endpoint-pair isomorphism. -/
theorem adj_iff (I : Isomorphism G H) [DecidableEq V] [DecidableEq W]
    {v₁ v₂ : V} : H.Adj (I.vertices v₁) (I.vertices v₂) ↔ G.Adj v₁ v₂ := by
  constructor
  · rintro ⟨e', ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
    · let e := I.edges.symm e'
      have he : I.edges e = e' := I.edges.apply_symm_apply e'
      rw [← he] at hs ht
      rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
      · have hv₁ : G.src e = v₁ := I.vertices.injective (hsrc.symm.trans hs)
        have hv₂ : G.tgt e = v₂ := I.vertices.injective (htgt.symm.trans ht)
        exact ⟨e, Or.inl ⟨hv₁, hv₂⟩⟩
      · have hv₂ : G.tgt e = v₁ := I.vertices.injective (hsrc.symm.trans hs)
        have hv₁ : G.src e = v₂ := I.vertices.injective (htgt.symm.trans ht)
        exact ⟨e, Or.inr ⟨hv₁, hv₂⟩⟩
    · let e := I.edges.symm e'
      have he : I.edges e = e' := I.edges.apply_symm_apply e'
      rw [← he] at hs ht
      rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
      · have hv₂ : G.src e = v₂ := I.vertices.injective (hsrc.symm.trans hs)
        have hv₁ : G.tgt e = v₁ := I.vertices.injective (htgt.symm.trans ht)
        exact ⟨e, Or.inr ⟨hv₂, hv₁⟩⟩
      · have hv₁ : G.tgt e = v₂ := I.vertices.injective (hsrc.symm.trans hs)
        have hv₂ : G.src e = v₁ := I.vertices.injective (htgt.symm.trans ht)
        exact ⟨e, Or.inl ⟨hv₂, hv₁⟩⟩
  · rintro ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
    · rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
      · exact ⟨I.edges e, Or.inl ⟨hsrc.trans (congrArg I.vertices hs),
          htgt.trans (congrArg I.vertices ht)⟩⟩
      · exact ⟨I.edges e, Or.inr ⟨hsrc.trans (congrArg I.vertices ht),
          htgt.trans (congrArg I.vertices hs)⟩⟩
    · rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
      · exact ⟨I.edges e, Or.inr ⟨hsrc.trans (congrArg I.vertices hs),
          htgt.trans (congrArg I.vertices ht)⟩⟩
      · exact ⟨I.edges e, Or.inl ⟨hsrc.trans (congrArg I.vertices ht),
          htgt.trans (congrArg I.vertices hs)⟩⟩

private theorem adj_symm [DecidableEq V] {a b : V} (h : G.Adj a b) : G.Adj b a := by
  rcases h with ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
  · exact ⟨e, Or.inr ⟨hs, ht⟩⟩
  · exact ⟨e, Or.inl ⟨hs, ht⟩⟩

private theorem adj_ne [DecidableEq V] {a b : V} (h : G.Adj a b) : a ≠ b := by
  intro hab
  rcases h with ⟨e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
  · exact G.src_ne_tgt e (hs.trans (hab.trans ht.symm))
  · exact G.src_ne_tgt e (hs.trans (hab.symm.trans ht.symm))

/-- The underlying simple graphs are isomorphic. -/
def simpleGraphIso (I : Isomorphism G H) [DecidableEq V] [DecidableEq W] :
    G.toSimpleGraph ≃g H.toSimpleGraph where
  toEquiv := I.vertices
  map_rel_iff' := by
    intro v w
    change I.vertices v ≠ I.vertices w ∧
      (H.Adj (I.vertices v) (I.vertices w) ∨ H.Adj (I.vertices w) (I.vertices v)) ↔
      v ≠ w ∧ (G.Adj v w ∨ G.Adj w v)
    constructor
    · rintro ⟨_, h | h⟩
      · have hg := I.adj_iff.mp h
        exact ⟨adj_ne hg, Or.inl hg⟩
      · have hg := I.adj_iff.mp (adj_symm h)
        exact ⟨adj_ne hg, Or.inl hg⟩
    · rintro ⟨hne, h | h⟩
      · have hh := I.adj_iff.mpr h
        exact ⟨fun heq => hne (I.vertices.injective heq), Or.inl hh⟩
      · have hh := I.adj_iff.mpr (adj_symm h)
        exact ⟨fun heq => hne (I.vertices.injective heq), Or.inl hh⟩

/-- Connectedness is invariant under multigraph isomorphism. -/
theorem connected_iff (I : Isomorphism G H) [DecidableEq V] [DecidableEq W] :
    G.Connected ↔ H.Connected :=
  SimpleGraph.Iso.connected_iff I.simpleGraphIso

/-- Graph isomorphisms preserve the simple-graph distance, including the value zero assigned
to pairs that are not connected. -/
theorem dist_transport (I : Isomorphism G H) [DecidableEq V] [DecidableEq W]
    (v w : V) :
    H.toSimpleGraph.dist (I.vertices v) (I.vertices w) =
      G.toSimpleGraph.dist v w := by
  let J := I.simpleGraphIso
  change H.toSimpleGraph.dist (J v) (J w) = G.toSimpleGraph.dist v w
  rw [SimpleGraph.dist_eq_sInf, SimpleGraph.dist_eq_sInf]
  congr 1
  apply Set.ext
  intro n
  constructor
  · rintro ⟨p, rfl⟩
    let q := p.map J.symm.toHom
    refine ⟨q.copy (by simp) (by simp), ?_⟩
    simp [q]
  · rintro ⟨p, rfl⟩
    exact ⟨p.map J.toHom, by simp⟩

/-- The Laplacian commutes with transport of vertex functions. -/
theorem laplacian_transport (I : Isomorphism G H) [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq W] (f : V → ℝ) (v : V) :
    H.laplacian (I.pushField f) (I.vertices v) = G.laplacian f v := by
  classical
  unfold laplacian
  rw [← I.edges.sum_comp]
  apply Finset.sum_congr rfl
  intro e he
  rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
  · simp [pushField, hsrc, htgt, I.vertices.injective.eq_iff]
  · simp [pushField, hsrc, htgt, I.vertices.injective.eq_iff]
    ring

/-- The Dirichlet energy is invariant under graph isomorphism, including
independent reversals of edge orientations. -/
theorem energy_transport (I : Isomorphism G H) [Fintype E] [Fintype F]
    (f : V → ℝ) : H.energy (I.pushField f) = G.energy f := by
  classical
  unfold energy
  rw [← I.edges.sum_comp]
  apply Finset.sum_congr rfl
  intro e he
  rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
  · simp [Multigraph.grad, pushField, hsrc, htgt]
  · simp [Multigraph.grad, pushField, hsrc, htgt]
    ring

/-- The vertex pairing is invariant under transport. -/
theorem pairing_transport (I : Isomorphism G H) [Fintype V] [Fintype W]
    {R : Type*} [CommRing R] (f g : V → R) :
    pairing (I.pushField f) (I.pushField g) = pairing f g := by
  classical
  unfold pairing pushField
  exact (Fintype.sum_equiv I.vertices (fun v => f v * g v)
    (fun w => f (I.vertices.symm w) * g (I.vertices.symm w))
    (by intro v; simp)).symm

/-- Arithmetic means are preserved when a function is transported. -/
theorem vertexMean_pushField (I : Isomorphism G H) [Fintype V] [Fintype W]
    (f : V → ℝ) :
    vertexMean W (I.pushField f) = vertexMean V f := by
  unfold vertexMean
  have hsum : ∑ w, I.pushField f w = ∑ v, f v := by
    unfold pushField
    exact (Fintype.sum_equiv I.vertices (fun v => f v)
      (fun w => f (I.vertices.symm w)) (by intro v; simp)).symm
  rw [hsum, Fintype.card_congr I.vertices]

/-- The mean-zero Green operator commutes with transport under a graph
isomorphism. -/
theorem greenOp_transport (I : Isomorphism G H)
    [Fintype V] [Fintype E] [DecidableEq V]
    [Fintype W] [Fintype F] [DecidableEq W]
    (hG : G.Connected) (f : V → ℝ) :
    I.pushField (G.greenOp hG f) =
      H.greenOp (I.connected_iff.mp hG) (I.pushField f) := by
  classical
  let hH := I.connected_iff.mp hG
  let u := G.greenOp hG f
  let w := H.greenOp hH (I.pushField f)
  have hu : ∑ v, u v = 0 := G.greenOp_sum_eq_zero hG f
  have hw : ∑ v, I.pullField w v = 0 := by
    calc
      ∑ v, I.pullField w v = ∑ y, w y := by
        unfold pullField
        exact Fintype.sum_equiv I.vertices
          (fun v => w (I.vertices v)) (fun y => w y) (by intro v; rfl)
      _ = 0 := H.greenOp_sum_eq_zero hH (I.pushField f)
  have hmean := I.vertexMean_pushField f
  have hproj : I.pullField
        ((zeroSumProjection hH.nonempty (I.pushField f) : zeroSumSubmodule W) : W → ℝ) =
      ((zeroSumProjection hG.nonempty f : zeroSumSubmodule V) : V → ℝ) := by
    funext v
    simp [pullField, pushField, zeroSumProjection_apply, hmean]
  have hHlap : H.laplacian w =
      ((zeroSumProjection hH.nonempty (I.pushField f) : zeroSumSubmodule W) : W → ℝ) :=
    H.laplacian_greenOp_eq_zeroSumProjection hH (I.pushField f)
  have hUlap : G.laplacian u =
      ((zeroSumProjection hG.nonempty f : zeroSumSubmodule V) : V → ℝ) :=
    G.laplacian_greenOp_eq_zeroSumProjection hG f
  have hΔw : G.laplacian (I.pullField w) =
      ((zeroSumProjection hG.nonempty f : zeroSumSubmodule V) : V → ℝ) := by
    funext v
    calc
      G.laplacian (I.pullField w) v =
          H.laplacian (I.pushField (I.pullField w)) (I.vertices v) :=
        (I.laplacian_transport (I.pullField w) v).symm
      _ = H.laplacian w (I.vertices v) := by simp
      _ = ((zeroSumProjection hH.nonempty (I.pushField f) : zeroSumSubmodule W) : W → ℝ)
          (I.vertices v) :=
        congrFun hHlap (I.vertices v)
      _ = ((zeroSumProjection hG.nonempty f : zeroSumSubmodule V) : V → ℝ) v := by
        have hp := congrFun hproj v
        exact hp
  have hΔu : G.laplacian u = G.laplacian (I.pullField w) := by
    rw [hUlap, hΔw]
  have hsub : G.laplacian (u - I.pullField w) = 0 := by
    change (G.laplacianₗ ℝ) (u - I.pullField w) = 0
    rw [(G.laplacianₗ ℝ).map_sub]
    change G.laplacian u - G.laplacian (I.pullField w) = 0
    rw [hΔu, sub_self]
  obtain ⟨c, hc⟩ := (G.laplacian_eq_zero_iff_exists_const hG
    (u - I.pullField w)).mp hsub
  have hsumSub : ∑ v, (u v - I.pullField w v) = 0 := by
    rw [Finset.sum_sub_distrib, hu, hw, sub_self]
  have hsumConst : ∑ v : V, c = 0 := by
    calc
      ∑ v : V, c = ∑ v, (u v - I.pullField w v) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (congrFun hc v).symm
      _ = 0 := hsumSub
  have hcardc : (Fintype.card V : ℝ) * c = 0 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsumConst
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (Fintype.card_pos_iff.mpr hG.nonempty))
  have hc0 : c = 0 := (mul_eq_zero.mp hcardc).resolve_left hcard
  have huw : u = I.pullField w := by
    funext v
    have hval := congrFun hc v
    change u v - I.pullField w v = c at hval
    rw [hc0] at hval
    exact sub_eq_zero.mp hval
  have hpushed := congrArg I.pushField huw
  simpa [u, w, pushField, pullField] using hpushed

end Multigraph.Isomorphism

end FroehlichSpencer.BKT

end
