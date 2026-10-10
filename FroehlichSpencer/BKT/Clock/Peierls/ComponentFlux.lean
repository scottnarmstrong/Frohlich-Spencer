/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Flux decomposes over components of the nonzero support -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

variable {E P A : Type*} [Fintype E] [DecidableEq E] [Fintype P]
  [AddCommGroup A] [DecidableEq A]

/-- The induced graph on labels where the field is nonzero. -/
def clockPeierlsBadGraph (G : SimpleGraph E) (η : E → A) :
    SimpleGraph {e : E // η e ≠ 0} :=
  G.induce {e | η e ≠ 0}

/-- Connected components of the bad induced graph form a finite type because its vertex type is
finite. -/
noncomputable instance clockPeierlsBadGraph_componentFintype
    (G : SimpleGraph E) (η : E → A) :
    Fintype (clockPeierlsBadGraph G η).ConnectedComponent :=
  Fintype.ofFinite _

/-- The support in `E` of one connected component of the nonzero-support graph. -/
noncomputable def clockPeierlsComponentSupport (G : SimpleGraph E) (η : E → A)
    (c : (clockPeierlsBadGraph G η).ConnectedComponent) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ he : η e ≠ 0, (clockPeierlsBadGraph G η).connectedComponentMk ⟨e, he⟩ = c

omit [DecidableEq E] in
theorem mem_clockPeierlsComponentSupport_iff (G : SimpleGraph E) (η : E → A)
    (c : (clockPeierlsBadGraph G η).ConnectedComponent) (e : E) :
    e ∈ clockPeierlsComponentSupport G η c ↔
      ∃ he : η e ≠ 0, (clockPeierlsBadGraph G η).connectedComponentMk ⟨e, he⟩ = c := by
  classical
  simp [clockPeierlsComponentSupport]

/-- The flux from a finite indexed edge family that lies in one bad connected component. -/
noncomputable def clockPeierlsComponentFlux (G : SimpleGraph E) (η : E → A)
    (p : P → E)
    (c : (clockPeierlsBadGraph G η).ConnectedComponent) : A :=
  ∑ i : P, if p i ∈ clockPeierlsComponentSupport G η c then η (p i) else 0

/-- The total flux of a finite indexed edge family. -/
def clockPeierlsPathFlux (η : E → A) (p : P → E) : A :=
  ∑ i : P, η (p i)

omit [DecidableEq E] in
/-- A nonzero label belongs to exactly the component containing its induced-graph vertex. -/
theorem mem_clockPeierlsComponentSupport_iff_componentMk
    (G : SimpleGraph E) (η : E → A)
    (e : E) (he : η e ≠ 0) (c : (clockPeierlsBadGraph G η).ConnectedComponent) :
    e ∈ clockPeierlsComponentSupport G η c ↔
      (clockPeierlsBadGraph G η).connectedComponentMk ⟨e, he⟩ = c := by
  rw [mem_clockPeierlsComponentSupport_iff]
  constructor
  · rintro ⟨he', hcomp⟩
    have hproof : he' = he := Subsingleton.elim _ _
    subst he'
    exact hcomp
  · intro hcomp
    exact ⟨he, hcomp⟩

/-- The total field sum is the sum of its restrictions to all components of the nonzero support. -/
theorem clockPeierlsPathFlux_eq_sum_componentFlux
    (G : SimpleGraph E) (η : E → A) (p : P → E) :
    clockPeierlsPathFlux η p =
      ∑ c : (clockPeierlsBadGraph G η).ConnectedComponent,
        clockPeierlsComponentFlux G η p c := by
  classical
  unfold clockPeierlsPathFlux clockPeierlsComponentFlux
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hzero : η (p i) = 0
  · simp [hzero]
  · let c₀ := (clockPeierlsBadGraph G η).connectedComponentMk ⟨p i, hzero⟩
    have hmem (c : (clockPeierlsBadGraph G η).ConnectedComponent) :
        p i ∈ clockPeierlsComponentSupport G η c ↔ c₀ = c := by
      rw [mem_clockPeierlsComponentSupport_iff_componentMk G η (p i) hzero c]
    calc
      η (p i) = ∑ c : (clockPeierlsBadGraph G η).ConnectedComponent,
          if p i ∈ clockPeierlsComponentSupport G η c then η (p i) else 0 := by
            rw [Fintype.sum_eq_single c₀]
            · simp [hmem c₀]
            · intro c hne
              simp [hmem c, hne.symm]

/-- A component with nonzero restricted flux meets the indexed edge family. -/
theorem clockPeierlsComponentFlux_ne_zero_imp_meets
    (G : SimpleGraph E) (η : E → A) (p : P → E)
    (c : (clockPeierlsBadGraph G η).ConnectedComponent)
    (hflux : clockPeierlsComponentFlux G η p c ≠ 0) :
    ∃ i : P, p i ∈ clockPeierlsComponentSupport G η c := by
  by_contra hmeet
  have hnot : ∀ i : P, p i ∉ clockPeierlsComponentSupport G η c := by
    intro i hi
    exact hmeet ⟨i, hi⟩
  unfold clockPeierlsComponentFlux at hflux
  apply hflux
  simp [hnot]

/-- If the total flux is nonzero, some bad connected component has nonzero flux and meets the
indexed edge family. -/
theorem exists_componentFlux_ne_zero_of_pathFlux_ne_zero
    (G : SimpleGraph E) (η : E → A) (p : P → E)
    (htotal : clockPeierlsPathFlux η p ≠ 0) :
    ∃ c : (clockPeierlsBadGraph G η).ConnectedComponent,
      clockPeierlsComponentFlux G η p c ≠ 0 ∧
        ∃ i : P, p i ∈ clockPeierlsComponentSupport G η c := by
  classical
  have hsome : ∃ c : (clockPeierlsBadGraph G η).ConnectedComponent,
      clockPeierlsComponentFlux G η p c ≠ 0 := by
    by_contra h
    have hall : ∀ c : (clockPeierlsBadGraph G η).ConnectedComponent,
        clockPeierlsComponentFlux G η p c = 0 := by
      intro c
      by_contra hc
      exact h ⟨c, hc⟩
    apply htotal
    rw [clockPeierlsPathFlux_eq_sum_componentFlux G η p]
    simp [hall]
  obtain ⟨c, hflux⟩ := hsome
  exact ⟨c, hflux, clockPeierlsComponentFlux_ne_zero_imp_meets G η p c hflux⟩

end FroehlichSpencer.BKT.Clock.Peierls

end
