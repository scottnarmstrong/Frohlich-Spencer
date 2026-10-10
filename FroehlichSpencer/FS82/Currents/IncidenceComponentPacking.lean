/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.ComponentPacking
public import FroehlichSpencer.FS82.Currents.ShortCurrentShell
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# FS82 ComponentPacking component connectivity and packing estimates
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents.ComponentPacking

open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

noncomputable section
open Classical

/--
The finite graph whose vertices are one current component's links and
whose edges join distinct links incident at a common finite `Λ*` vertex.
-/
@[expose] def componentLinkGraph {B : Box 4} (j : IntegerCurrent B)
    (c : CurrentComponentClass j) : SimpleGraph (currentComponentSupport j c) where
  Adj e f := e.val ≠ f.val ∧ linksShareFiniteVertex e.val f.val
  symm := Std.Symm.mk (by
    intro e f h
    rcases h with ⟨hne, v, hve, hvf⟩
    exact ⟨hne.symm, v, hvf, hve⟩)
  loopless := Std.Irrefl.mk (by
    intro e h
    have hne := h.1
    exact hne rfl)

theorem currentComponentSupport_reachable {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j)
    {e f : Link B} (he : e ∈ currentComponentSupport j c)
    (hf : f ∈ currentComponentSupport j c) :
    (componentLinkGraph j c).Reachable
      ⟨e, he⟩ ⟨f, hf⟩ := by
  have hgen : Relation.EqvGen (currentLinkStep j) e f :=
    (currentComponentOf_eq_iff j e f).1
      ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  have hclass_eq : ∀ {x y}, Relation.EqvGen (currentLinkStep j) x y →
      currentComponentOf j x = currentComponentOf j y := by
    intro x y h
    induction h with
    | rel x y hxy =>
        exact currentComponentOf_eq_of_shareVertex j hxy.1 hxy.2.1 hxy.2.2
    | refl x => rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hsupport_transfer : ∀ {x y}, Relation.EqvGen (currentLinkStep j) x y →
      (x ∈ j.support ↔ y ∈ j.support) := by
    intro x y h
    induction h with
    | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
    | refl x => exact Iff.rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hreach : ∀ {x y} (h : Relation.EqvGen (currentLinkStep j) x y),
      (hx : x ∈ j.support) → (hy : y ∈ j.support) →
      (hxclass : currentComponentOf j x = c) →
      (hyclass : currentComponentOf j y = c) →
      (componentLinkGraph j c).Reachable
        ⟨x, Finset.mem_filter.mpr ⟨hx, hxclass⟩⟩
        ⟨y, Finset.mem_filter.mpr ⟨hy, hyclass⟩⟩ := by
    intro x y h
    induction h with
    | rel x y hxy =>
        intro hx hy hxclass hyclass
        by_cases hEq : x = y
        · subst y
          exact SimpleGraph.Reachable.refl _
        · have hadj : (componentLinkGraph j c).Adj
              ⟨x, Finset.mem_filter.mpr ⟨hx, hxclass⟩⟩
              ⟨y, Finset.mem_filter.mpr ⟨hy, hyclass⟩⟩ :=
            ⟨hEq, hxy.2.2⟩
          exact hadj.reachable
    | refl x =>
        intro hx hy hxclass hyclass
        have hxy : (⟨x, Finset.mem_filter.mpr ⟨hx, hxclass⟩⟩ :
            currentComponentSupport j c) =
          ⟨x, Finset.mem_filter.mpr ⟨hy, hyclass⟩⟩ := by
          apply Subtype.ext
          rfl
        rw [← hxy]
    | symm x y hxy ih =>
        intro hy hx hyclass hxclass
        exact (ih hx hy hxclass hyclass).symm
    | trans x y z hxy hyz ihxy ihyz =>
        intro hx hz hxclass hzclass
        have hymem : y ∈ j.support := (hsupport_transfer hxy).1 hx
        have hyclass : currentComponentOf j y = c := by
          calc
            currentComponentOf j y = currentComponentOf j x := (hclass_eq hxy).symm
            _ = c := hxclass
        exact (ihxy hx hymem hxclass hyclass).trans
          (ihyz hymem hz hyclass hzclass)
  have heclass : currentComponentOf j e = c := (Finset.mem_filter.mp he).2
  have hfclass : currentComponentOf j f = c := (Finset.mem_filter.mp hf).2
  exact hreach hgen (Finset.mem_filter.mp he).1
    (Finset.mem_filter.mp hf).1 heclass hfclass

theorem currentComponent_has_bounded_link_path {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j)
    {e f : Link B} (he : e ∈ currentComponentSupport j c)
    (hf : f ∈ currentComponentSupport j c) :
    ∃ p : (componentLinkGraph j c).Walk ⟨e, he⟩ ⟨f, hf⟩,
      p.IsPath ∧ p.length ≤ (currentComponentSupport j c).card := by
  classical
  obtain ⟨p, hp, hlen⟩ :=
    (currentComponentSupport_reachable j c he hf).exists_path_of_dist
  refine ⟨p, hp, ?_⟩
  have hcard := hp.length_lt
  have hcard' : p.length < (currentComponentSupport j c).card := by
    simpa [componentLinkGraph] using hcard
  exact Nat.le_of_lt hcard'

-- Replacements for these `/e²` names: `SourcePacking.sourceComponentActivityL5` and `SourcePacking.sourceComponentCpackPrime`.


end
end FroehlichSpencer.FS82.Currents.ComponentPacking

end
