module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

private def finSuccIntEquiv (n : ℕ) : (Fin (n + 1) → ℤ) ≃ ℤ × (Fin n → ℤ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  right_inv p := by
    rcases p with ⟨z, f⟩
    rfl

private theorem summable_fin_pi_prod (g : ℤ → ℝ) (hg : Summable g) :
    ∀ n : ℕ, Summable (fun f : Fin n → ℤ => ∏ i, g (f i)) := by
  intro n
  induction n with
  | zero =>
      exact (hasSum_fintype _).summable
  | succ n ih =>
      let f : (Fin (n + 1) → ℤ) → ℝ := fun v => ∏ i, g (v i)
      let e := finSuccIntEquiv n
      have hgn : Summable (fun z : ℤ => ‖g z‖) := hg.norm
      have hfn : Summable (fun v : Fin n → ℤ => ‖∏ i, g (v i)‖) := ih.norm
      have hprod : Summable (fun p : ℤ × (Fin n → ℤ) => g p.1 * ∏ i, g (p.2 i)) :=
        summable_mul_of_summable_norm (R := ℝ) (f := g)
          (g := fun v : Fin n → ℤ => ∏ i, g (v i)) hgn hfn
      have hcomp : Summable (f ∘ e.symm) := by
        apply hprod.congr
        intro p
        rcases p with ⟨z, v⟩
        change g z * ∏ i : Fin n, g (v i) =
          ∏ i : Fin (n + 1), g (Fin.cases z v i)
        rw [Fin.prod_univ_succ]
        simp
      exact (Equiv.summable_iff (f := f) e.symm).mp hcomp

theorem summable_pi_prod_of_summable {ι : Type*} [Fintype ι]
    (g : ℤ → ℝ) (hg : Summable g) :
    Summable (fun n : ι → ℤ => ∏ i, g (n i)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eπ : (ι → ℤ) ≃ (Fin (Fintype.card ι) → ℤ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℤ) e
  have hfin := summable_fin_pi_prod g hg (Fintype.card ι)
  let fFin : (Fin (Fintype.card ι) → ℤ) → ℝ := fun f => ∏ j, g (f j)
  have hcomp : Summable
      (fFin ∘ eπ) := (Equiv.summable_iff (f := fFin) eπ).mpr hfin
  apply hcomp.congr
  intro n
  simpa [fFin, Function.comp_apply, eπ, Equiv.piCongrLeft,
    Equiv.piCongrLeft'_symm_apply] using
    (Equiv.prod_comp e.symm (fun i => g (n i)))

end FroehlichSpencer.FS82.Poisson
