/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.SharedCoverSelector

/-! # Deduplicating compatible parent constraints

The source selector may prescribe the same target parent from multiple
separated squares. This module quotients a finite indexed family by equality
of its support patches. If intersecting patches have identical parent data,
the distinct patches are disjoint and the simultaneous replacement theorem
applies. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- A finite family of parent constraints with compatible overlaps can be
imposed in a common minimum cover after duplicate patches are identified. -/
theorem exists_minimumSquareCover_containing_compatible_parents
    {I : Type} [DecidableEq I]
    (boundary : SquareBoundary) (L k : ℕ) (ρ : ChargeDensity L)
    (indices : Finset I)
    (patch parent : I → Finset (Fin L × Fin L))
    (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsMinimumSquareCover boundary L k ρ C)
    (hnonempty : ∀ i ∈ indices, (patch i).Nonempty)
    (hsubsupport : ∀ i ∈ indices, patch i ⊆ chargeSupport ρ)
    (hcompatible : ∀ i ∈ indices, ∀ j ∈ indices,
      (patch i ∩ patch j).Nonempty → patch i = patch j ∧ parent i = parent j)
    (hallowed : ∀ i ∈ indices, parent i ∈ kpSquares boundary L k)
    (hexact : ∀ i ∈ indices, parent i ∩ chargeSupport ρ = patch i)
    (hlocal : ∀ i ∈ indices, ∀ s ∈ C, SquareMeetsPatch (patch i) s →
      SquareLocalToPatch (chargeSupport ρ) (patch i) s) :
    ∃ C', IsMinimumSquareCover boundary L k ρ C' ∧
      ∀ i ∈ indices, parent i ∈ C' := by
  classical
  let patches := indices.image patch
  let parentOfPatch : Finset (Fin L × Fin L) → Finset (Fin L × Fin L) := fun p =>
    if hp : p ∈ patches then parent (Classical.choose (Finset.mem_image.mp hp)) else ∅
  have hparentOfPatch_eq (p : Finset (Fin L × Fin L)) (hp : p ∈ patches) :
      parentOfPatch p = parent (Classical.choose (Finset.mem_image.mp hp)) := by
    simp [parentOfPatch, hp]
  have hchosen (p : Finset (Fin L × Fin L)) (hp : p ∈ patches) :
      Classical.choose (Finset.mem_image.mp hp) ∈ indices ∧
        patch (Classical.choose (Finset.mem_image.mp hp)) = p :=
    Classical.choose_spec (Finset.mem_image.mp hp)
  have hparent_choice_eq (p : Finset (Fin L × Fin L)) (hp : p ∈ patches)
      (i : I) (hi : i ∈ indices) (heq : patch i = p) :
      parentOfPatch p = parent i := by
    let i₀ := Classical.choose (Finset.mem_image.mp hp)
    have hi₀ := hchosen p hp
    have hpatchEq : patch i₀ = patch i := hi₀.2.trans heq.symm
    have hmeet : (patch i₀ ∩ patch i).Nonempty := by
      rcases hnonempty i₀ hi₀.1 with ⟨x, hx⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, hpatchEq ▸ hx⟩⟩
    have hparentEq := (hcompatible i₀ hi₀.1 i hi hmeet).2
    calc
      parentOfPatch p = parent i₀ := by
        simpa [i₀] using hparentOfPatch_eq p hp
      _ = parent i := hparentEq
  have hnonemptyP : ∀ p ∈ patches, p.Nonempty := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hnonempty i hi
  have hsubsupportP : ∀ p ∈ patches, p ⊆ chargeSupport ρ := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hsubsupport i hi
  have hdisjointP : ∀ p ∈ patches, ∀ q ∈ patches, p ≠ q → Disjoint p q := by
    intro p hp q hq hpq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hmeet : (patch i ∩ patch j).Nonempty :=
      ⟨x, Finset.mem_inter.mpr ⟨hxi, hxj⟩⟩
    have hpatchEq := (hcompatible i hi j hj hmeet).1
    exact hpq hpatchEq
  have hallowedP : ∀ p ∈ patches, parentOfPatch p ∈ kpSquares boundary L k := by
    intro p hp
    let i₀ := Classical.choose (Finset.mem_image.mp hp)
    have hi₀ := hchosen p hp
    rw [hparentOfPatch_eq p hp]
    exact hallowed i₀ hi₀.1
  have hexactP : ∀ p ∈ patches, parentOfPatch p ∩ chargeSupport ρ = p := by
    intro p hp
    let i₀ := Classical.choose (Finset.mem_image.mp hp)
    have hi₀ := hchosen p hp
    calc
      parentOfPatch p ∩ chargeSupport ρ = parent i₀ ∩ chargeSupport ρ :=
        congrArg (fun t : Finset (Fin L × Fin L) => t ∩ chargeSupport ρ)
          (hparent_choice_eq p hp i₀ hi₀.1 hi₀.2)
      _ = patch i₀ := hexact i₀ hi₀.1
      _ = p := hi₀.2
  have hlocalP : ∀ p ∈ patches, ∀ s ∈ C, SquareMeetsPatch p s →
      SquareLocalToPatch (chargeSupport ρ) p s := by
    intro p hp s hs hmeet
    let i₀ := Classical.choose (Finset.mem_image.mp hp)
    have hi₀ := hchosen p hp
    have hmeet₀ : SquareMeetsPatch (patch i₀) s := by
      rcases hmeet with ⟨x, hx, hxs⟩
      exact ⟨x, Eq.mp (congrArg (fun t : Finset (Fin L × Fin L) => x ∈ t)
        hi₀.2.symm) hx, hxs⟩
    intro x hxS hxSupport
    have hx₀ := hlocal i₀ hi₀.1 s hs hmeet₀ x hxS hxSupport
    exact Eq.mp (congrArg (fun t : Finset (Fin L × Fin L) => x ∈ t) hi₀.2) hx₀
  obtain ⟨C', hC', hparents, -⟩ := exists_minimumSquareCover_containing_parents
    boundary L k ρ patches parentOfPatch C hC hnonemptyP hsubsupportP hdisjointP
    hallowedP hexactP hlocalP
  refine ⟨C', hC', ?_⟩
  intro i hi
  have hmem : patch i ∈ patches := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hchosenEq := hparent_choice_eq (patch i) hmem i hi rfl
  rw [← hchosenEq]
  exact hparents (patch i) hmem

end FroehlichSpencer.BKT

end
