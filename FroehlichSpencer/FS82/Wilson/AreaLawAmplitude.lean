/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawActivity
public import FroehlichSpencer.FS82.Wilson.AreaLawSource
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Summing the nonzero amplitudes on a fixed support

For a fixed plaquette support, the Gaussian amplitude sum factors into one
copy of the nonzero one-plaquette activity per support plaquette.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

abbrev AreaLawNonzeroInt := {z : ℤ // z ≠ 0}

noncomputable def areaLawNonzeroGaussianAtom (β : ℝ) (z : AreaLawNonzeroInt) : ℝ :=
  Real.exp (-((z.1 : ℝ) ^ 2) / (2 * β))

private theorem nonzeroGaussianActivity_eq_subtype_tsum (β : ℝ) :
    nonzeroGaussianActivity β =
      ∑' z : AreaLawNonzeroInt, areaLawNonzeroGaussianAtom β z := by
  classical
  let f : ℤ → ℝ := fun z => Real.exp (-((z : ℝ) ^ 2) / (2 * β))
  change (∑' z : ℤ, if z = 0 then 0 else f z) =
    ∑' z : {z : ℤ // z ≠ 0}, f z
  calc
    (∑' z : ℤ, if z = 0 then 0 else f z) =
        ∑' z : ℤ, ({z : ℤ | z ≠ 0}.indicator f) z := by
          apply tsum_congr
          intro z
          by_cases hz : z = 0 <;> simp [Set.indicator, hz]
    _ = ∑' z : {z : ℤ // z ≠ 0}, f z :=
          (tsum_subtype {z : ℤ | z ≠ 0} f).symm

private theorem areaLawNonzeroGaussianAtom_summable (β : ℝ) (hβ : 0 < β) :
    Summable (areaLawNonzeroGaussianAtom β) := by
  have h := villainCharacterCoeff_summable β hβ
  change Summable (fun z : {z : ℤ // z ≠ 0} =>
    Real.exp (-((z.1 : ℝ) ^ 2) / (2 * β)))
  exact h.subtype {z : ℤ | z ≠ 0}

theorem areaLawNonzeroGaussianAtom_hasSum (β : ℝ) (hβ : 0 < β) :
    HasSum (areaLawNonzeroGaussianAtom β) (nonzeroGaussianActivity β) := by
  apply (areaLawNonzeroGaussianAtom_summable β hβ).hasSum_iff.mpr
  exact (nonzeroGaussianActivity_eq_subtype_tsum β).symm

private theorem areaLaw_nonzeroGaussian_assignment_hasSum_fin
    (β : ℝ) (hβ : 0 < β) :
    ∀ n : ℕ,
      HasSum
        (fun f : Fin n → AreaLawNonzeroInt =>
          ∏ i, areaLawNonzeroGaussianAtom β (f i))
        (nonzeroGaussianActivity β ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      let atom := areaLawNonzeroGaussianAtom β
      let e : (Fin (n + 1) → AreaLawNonzeroInt) ≃
          AreaLawNonzeroInt × (Fin n → AreaLawNonzeroInt) :=
        ((finSuccEquiv n).piCongrLeft (fun _ => AreaLawNonzeroInt)).trans
          Equiv.piOptionEquivProd
      have hAtom := areaLawNonzeroGaussianAtom_hasSum β hβ
      have hprodNonneg (p : AreaLawNonzeroInt × (Fin n → AreaLawNonzeroInt)) :
          0 ≤ atom p.1 * ∏ i, atom (p.2 i) := by
        apply mul_nonneg (Real.exp_pos _).le
        exact Finset.prod_nonneg fun i hi => (Real.exp_pos _).le
      have hprodSummable :
          Summable (fun p : AreaLawNonzeroInt × (Fin n → AreaLawNonzeroInt) =>
            atom p.1 * ∏ i, atom (p.2 i)) := by
        rw [summable_prod_of_nonneg hprodNonneg]
        constructor
        · intro z
          simpa using ih.summable.mul_left (atom z)
        · have houter := hAtom.summable.mul_right
            (∑' f : Fin n → AreaLawNonzeroInt, ∏ i, atom (f i))
          apply houter.congr
          intro z
          change atom z * ∑' f : Fin n → AreaLawNonzeroInt, ∏ i, atom (f i) =
            ∑' f : Fin n → AreaLawNonzeroInt, atom z * ∏ i, atom (f i)
          rw [← tsum_mul_left]
      apply e.symm.hasSum_iff.mp
      convert hAtom.mul ih hprodSummable using 1
      · funext p
        change (∏ i : Fin (n + 1), atom ((e.symm p) i)) =
          atom p.1 * ∏ i : Fin n, atom (p.2 i)
        rw [Fin.prod_univ_succ]
        have hzero : (e.symm p) 0 = p.1 := by
          simp [e, Equiv.trans_apply, finSuccEquiv,
            Equiv.piCongrLeft, Equiv.piOptionEquivProd]
        have hsucc (i : Fin n) : (e.symm p) i.succ = p.2 i := by
          simp [e, Equiv.trans_apply, finSuccEquiv,
            Equiv.piCongrLeft, Equiv.piOptionEquivProd, finSuccEquiv']
        rw [hzero]
        apply congrArg (fun x : ℝ => atom p.1 * x)
        apply Finset.prod_congr rfl
        intro i hi
        rw [hsucc]
      · simp [pow_succ, mul_comm]

@[expose] noncomputable def areaLawFieldOfAmplitudes {B : Box 4}
    (S : Finset (PrimalPlaquettes B))
    (g : S → AreaLawNonzeroInt) : PrimalPlaquettes B → ℤ :=
  fun p => if hp : p ∈ S then (g ⟨p, hp⟩).1 else 0

theorem areaLawFieldOfAmplitudes_support {B : Box 4}
    (S : Finset (PrimalPlaquettes B))
    (g : S → AreaLawNonzeroInt) :
    plaquetteFieldSupport (areaLawFieldOfAmplitudes S g) = S := by
  classical
  ext p
  simp only [plaquetteFieldSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hp : p ∈ S
  · constructor
    · intro _
      exact hp
    · intro _
      simpa [areaLawFieldOfAmplitudes, hp] using
        (g ⟨p, hp⟩).property
  · simp [areaLawFieldOfAmplitudes, hp]

noncomputable def areaLawAmplitudeFieldEquiv {B : Box 4}
    (S : Finset (PrimalPlaquettes B)) :
    (S → AreaLawNonzeroInt) ≃
      {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m = S} where
  toFun g := ⟨areaLawFieldOfAmplitudes S g, areaLawFieldOfAmplitudes_support S g⟩
  invFun f := fun p => ⟨f.1 p.1, by
    have hp : p.1 ∈ plaquetteFieldSupport f.1 := by rw [f.2]; exact p.2
    exact (Finset.mem_filter.mp hp).2⟩
  left_inv g := by
    funext p
    apply Subtype.ext
    simp [areaLawFieldOfAmplitudes, p.2]
  right_inv f := by
    apply Subtype.ext
    funext p
    by_cases hp : p ∈ S
    · simp [areaLawFieldOfAmplitudes, hp]
    · have hm : f.1 p = 0 := by
        by_contra hne
        apply hp
        rw [← f.2]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      simp [areaLawFieldOfAmplitudes, hp, hm]

private theorem dualGaussianProduct_fieldOfAmplitudes {B : Box 4}
    (β : ℝ) (S : Finset (PrimalPlaquettes B))
    (g : S → AreaLawNonzeroInt) :
    dualGaussianProduct β (areaLawFieldOfAmplitudes S g) =
      ∏ p : S, areaLawNonzeroGaussianAtom β (g p) := by
  classical
  unfold dualGaussianProduct
  let gVal : PrimalPlaquettes B → AreaLawNonzeroInt := fun p =>
    if hp : p ∈ S then g ⟨p, hp⟩ else ⟨1, by norm_num⟩
  have hterm (p : PrimalPlaquettes B) :
      Real.exp (-((areaLawFieldOfAmplitudes S g p : ℤ) : ℝ) ^ 2 / (2 * β)) =
        (if p ∈ S then areaLawNonzeroGaussianAtom β (gVal p) else 1) := by
    by_cases hp : p ∈ S
    · simp [areaLawFieldOfAmplitudes, areaLawNonzeroGaussianAtom, gVal, hp]
    · simp [areaLawFieldOfAmplitudes, hp]
  calc
    (∏ p : PrimalPlaquettes B,
        Real.exp (-((areaLawFieldOfAmplitudes S g p : ℤ) : ℝ) ^ 2 / (2 * β))) =
      ∏ p : PrimalPlaquettes B,
        if hp : p ∈ S then areaLawNonzeroGaussianAtom β (gVal p) else 1 := by
          apply Finset.prod_congr rfl
          intro p hp
          exact hterm p
    _ = ∏ p ∈ S, areaLawNonzeroGaussianAtom β (gVal p) := by
          simp only [dite_eq_ite]
          rw [Finset.prod_ite_mem_eq]
    _ = ∏ p : S, areaLawNonzeroGaussianAtom β (g p) := by
          calc
            ∏ p ∈ S, areaLawNonzeroGaussianAtom β (gVal p) =
                ∏ p : S, areaLawNonzeroGaussianAtom β (gVal p) :=
                  (Finset.prod_coe_sort S
                    (fun p => areaLawNonzeroGaussianAtom β (gVal p))).symm
            _ = ∏ p : S, areaLawNonzeroGaussianAtom β (g p) := by
                  apply Finset.prod_congr rfl
                  intro p hp
                  simp [gVal, p.2]

theorem dualGaussianProduct_exactSupport_tsum {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (S : Finset (PrimalPlaquettes B)) :
    (∑' m : {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m = S},
      dualGaussianProduct β m.1) = nonzeroGaussianActivity β ^ S.card := by
  let e := areaLawAmplitudeFieldEquiv S
  calc
    (∑' m : {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m = S},
      dualGaussianProduct β m.1) =
      ∑' g : S → AreaLawNonzeroInt,
        dualGaussianProduct β (e g).1 := (e.tsum_eq _).symm
    _ = ∑' g : S → AreaLawNonzeroInt,
        ∏ p : S, areaLawNonzeroGaussianAtom β (g p) := by
          apply tsum_congr
          intro g
          exact dualGaussianProduct_fieldOfAmplitudes β S g
    _ = nonzeroGaussianActivity β ^ S.card := by
          let eFin : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
          let ePi : (Fin (Fintype.card S) → AreaLawNonzeroInt) ≃
              (S → AreaLawNonzeroInt) :=
            eFin.piCongrLeft (fun _ => AreaLawNonzeroInt)
          let fFin : (Fin (Fintype.card S) → AreaLawNonzeroInt) → ℝ := fun f =>
            ∏ i, areaLawNonzeroGaussianAtom β (f i)
          have hfin := areaLaw_nonzeroGaussian_assignment_hasSum_fin β hβ
            (Fintype.card S)
          have hsum := ePi.symm.hasSum_iff.mpr hfin
          have hsum' : HasSum
              (fun g : S → AreaLawNonzeroInt =>
                ∏ p : S, areaLawNonzeroGaussianAtom β (g p))
              (nonzeroGaussianActivity β ^ Fintype.card S) := by
            convert hsum using 1
            funext g
            change (∏ p : S, areaLawNonzeroGaussianAtom β (g p)) =
              ∏ i : Fin (Fintype.card S),
                areaLawNonzeroGaussianAtom β ((ePi.symm g) i)
            simp only [ePi, Equiv.piCongrLeft_symm_apply]
            exact (Equiv.prod_comp eFin
              (fun p : S => areaLawNonzeroGaussianAtom β (g p))).symm
          simpa only [Fintype.card_coe] using hsum'.tsum_eq

end FroehlichSpencer.FS82.Wilson

end
