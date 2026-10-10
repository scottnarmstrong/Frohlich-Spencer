module
public import FroehlichSpencer.FS82.Gaussian.AxisHodge

public section
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical
open scoped BigOperators

variable {B : SourceBox}

@[expose] noncomputable def axisEdgeZero (i : Fin 4) : DualCoord B i :=
  Sum.inr ⟨0, Nat.zero_lt_succ _⟩

abbrev AxisSliceBase (i : Fin 4) :=
  {c : DualCell 4 B // c i = axisEdgeZero i}

noncomputable instance axisSliceBaseFintype (i : Fin 4) :
    Fintype (AxisSliceBase (B := B) i) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun c : DualCell 4 B => c i = axisEdgeZero i)
    (by intro c; simp)


@[expose] noncomputable def axisSliceBase (i : Fin 4) (c : DualCell 4 B) :
    AxisSliceBase (B := B) i :=
  ⟨Function.update c i (axisEdgeZero i), by simp [axisEdgeZero]⟩

@[expose] noncomputable def axisSliceEquiv (i : Fin 4) :
    DualCell 4 B ≃ AxisSliceBase (B := B) i × DualCoord B i where
  toFun c := (axisSliceBase i c, c i)
  invFun p := Function.update p.1.1 i p.2
  left_inv c := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [axisSliceBase, axisEdgeZero]
    · simp [axisSliceBase, Function.update_of_ne hki]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k
        simp [axisSliceBase, axisEdgeZero, p.1.2]
      · simp [axisSliceBase, Function.update_of_ne hki]
    · simp

theorem sum_dualCell_eq_sum_axisSlice {M : Type*} [AddCommMonoid M]
    (i : Fin 4)
    (F : DualCell 4 B → M) :
    (∑ c : DualCell 4 B, F c) =
      ∑ b : AxisSliceBase (B := B) i, ∑ u : DualCoord B i,
        F (Function.update b.1 i u) := by
  classical
  calc
    (∑ c : DualCell 4 B, F c) =
        ∑ p : AxisSliceBase (B := B) i × DualCoord B i,
          F (Function.update p.1.1 i p.2) := by
            exact Fintype.sum_equiv (axisSliceEquiv (B := B) i)
              (fun c => F c)
              (fun p : AxisSliceBase (B := B) i × DualCoord B i =>
                F (Function.update p.1.1 i p.2)) (by
                  intro c
                  exact congrArg F ((axisSliceEquiv (B := B) i).left_inv c).symm)
    _ = ∑ b : AxisSliceBase (B := B) i, ∑ u : DualCoord B i,
          F (Function.update b.1 i u) := Fintype.sum_prod_type _

end FroehlichSpencer.FS82.Gaussian
