module
public import FroehlichSpencer.FS82.Gaussian.AxisBoundary
public section
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical
variable {B : SourceBox}
set_option linter.unusedSimpArgs false in
theorem axisStencilCoefficient_symm (i : Fin 4) (x y : DualCell 4 B) :
    dualExteriorDifferenceAxisStencilBasis i x y =
      dualExteriorDifferenceAxisAdjointStencilBasis i y x := by
  classical
  cases hxi : x i with
  | inr ex =>
      cases hyi : y i with
      | inl vy =>
          simp [dualExteriorDifferenceAxisStencilBasis,
            dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi]
      | inr ey =>
          by_cases hp : 0 < ey.val
          · by_cases hlt : ey.val < B i
            · have hprev : Function.update y i
                  (Sum.inl ⟨ey.val - 1, by omega⟩) ≠ x := by
                intro h
                have hi := congrArg (fun c : DualCell 4 B => c i) h
                simp [Function.update_self, hxi] at hi
              have hnext : Function.update y i
                  (Sum.inl ⟨ey.val, hlt⟩) ≠ x := by
                intro h
                have hi := congrArg (fun c : DualCell 4 B => c i) h
                simp [Function.update_self, hxi] at hi
              simp [dualExteriorDifferenceAxisStencilBasis,
                dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                hp, hlt, hprev, hnext]
            · have hprev : Function.update y i
                  (Sum.inl ⟨ey.val - 1, by omega⟩) ≠ x := by
                intro h
                have hi := congrArg (fun c : DualCell 4 B => c i) h
                simp [Function.update_self, hxi] at hi
              simp [dualExteriorDifferenceAxisStencilBasis,
                dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                hp, hlt, hprev]
          · by_cases hlt : ey.val < B i
            · have hnext : Function.update y i
                  (Sum.inl ⟨ey.val, hlt⟩) ≠ x := by
                intro h
                have hi := congrArg (fun c : DualCell 4 B => c i) h
                simp [Function.update_self, hxi] at hi
              simp [dualExteriorDifferenceAxisStencilBasis,
                dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                hp, hlt, hnext]
            · simp [dualExteriorDifferenceAxisStencilBasis,
                dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                hp, hlt]
  | inl vx =>
      cases hyi : y i with
      | inl vy =>
          have hupper : Function.update x i
              (Sum.inr ⟨vx.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt vx.isLt)⟩) ≠ y := by
            intro h
            have hc := (Function.update_eq_iff.mp h).1
            simp [hyi] at hc
          have hlower : Function.update x i
              (Sum.inr ⟨vx.val, Nat.lt_succ_of_le vx.isLt.le⟩) ≠ y := by
            intro h
            have hc := (Function.update_eq_iff.mp h).1
            simp [hyi] at hc
          simp [dualExteriorDifferenceAxisStencilBasis,
            dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
            dualUpperFace, dualLowerFace, hupper, hlower]
      | inr ey =>
          by_cases hoff : ∀ k, k ≠ i → x k = y k
          · have hoff' : ∀ k, k ≠ i → y k = x k := by
              intro k hk
              exact (hoff k hk).symm
            have hrank := dualVertexRankBefore_eq_of_eq_off_axis x y i hoff
            have hupper : Function.update x i
                (Sum.inr ⟨vx.val + 1,
                  Nat.lt_succ_of_le (Nat.succ_le_of_lt vx.isLt)⟩) = y ↔
                vx.val + 1 = ey.val := by
              rw [Function.update_eq_iff]
              constructor
              · rintro ⟨hc, _⟩
                have hc' : Sum.inr (α := Fin (B i)) (⟨vx.val + 1,
                    Nat.lt_succ_of_le (Nat.succ_le_of_lt vx.isLt)⟩ : Fin (B i + 1)) =
                    Sum.inr (α := Fin (B i)) ey := by simpa [hyi] using hc
                exact congrArg Fin.val (Sum.inr.inj hc')
              · intro hv
                refine ⟨?_, hoff⟩
                rw [hyi]
                exact congrArg (Sum.inr (α := Fin (B i)))
                  (Fin.ext (by simpa using hv))
            have hlower : Function.update x i
                (Sum.inr ⟨vx.val, Nat.lt_succ_of_le vx.isLt.le⟩) = y ↔
                vx.val = ey.val := by
              rw [Function.update_eq_iff]
              constructor
              · rintro ⟨hc, _⟩
                have hc' : Sum.inr (α := Fin (B i)) (⟨vx.val,
                    Nat.lt_succ_of_le vx.isLt.le⟩ : Fin (B i + 1)) =
                    Sum.inr (α := Fin (B i)) ey := by simpa [hyi] using hc
                exact congrArg Fin.val (Sum.inr.inj hc')
              · intro hv
                refine ⟨?_, hoff⟩
                rw [hyi]
                exact congrArg (Sum.inr (α := Fin (B i))) (Fin.ext hv)
            have hprev : ∀ hp : 0 < ey.val,
                Function.update y i
                  (Sum.inl ⟨ey.val - 1, by omega⟩) = x ↔
                  ey.val = vx.val + 1 := by
              intro hp
              rw [Function.update_eq_iff]
              constructor
              · rintro ⟨hc, _⟩
                have hc' : Sum.inl (β := Fin (B i + 1))
                    (⟨ey.val - 1, by omega⟩ : Fin (B i)) =
                    Sum.inl (β := Fin (B i + 1)) vx := by simpa [hxi] using hc
                have he := Sum.inl.inj hc'
                have hv : ey.val - 1 = vx.val := congrArg Fin.val he
                have hs : ey.val - 1 + 1 = ey.val := by
                  exact Nat.sub_add_cancel (by omega)
                omega
              · intro hv
                refine ⟨?_, hoff'⟩
                rw [hxi]
                have he : (⟨ey.val - 1, by omega⟩ : Fin (B i)) = vx := by
                  apply Fin.ext
                  calc
                    ey.val - 1 = (vx.val + 1) - 1 := by rw [hv]
                    _ = vx.val := by omega
                exact congrArg (Sum.inl (α := Fin (B i))) he
            have hnext : ∀ hlt : ey.val < B i,
                Function.update y i (Sum.inl ⟨ey.val, hlt⟩) = x ↔
                  ey.val = vx.val := by
              intro hlt
              rw [Function.update_eq_iff]
              constructor
              · rintro ⟨hc, _⟩
                have hc' : Sum.inl (β := Fin (B i + 1))
                    (⟨ey.val, hlt⟩ : Fin (B i)) =
                    Sum.inl (β := Fin (B i + 1)) vx := by simpa [hxi] using hc
                exact congrArg Fin.val (Sum.inl.inj hc')
              · intro hv
                refine ⟨?_, hoff'⟩
                rw [hxi]
                have he : (⟨ey.val, hlt⟩ : Fin (B i)) = vx := by
                  apply Fin.ext
                  exact hv
                exact congrArg (Sum.inl (α := Fin (B i))) he
            have hcoef :
                (if vx.val + 1 = ey.val then (1 : ℝ) else 0) -
                    (if vx.val = ey.val then (1 : ℝ) else 0) =
                  (if 0 < ey.val then
                    (if ey.val = vx.val + 1 then (1 : ℝ) else 0) else 0) -
                    (if ey.val < B i then
                      (if ey.val = vx.val then (1 : ℝ) else 0) else 0) := by
              by_cases hu : vx.val + 1 = ey.val
              · have hp : 0 < ey.val := by omega
                have hn : vx.val ≠ ey.val := by omega
                simp [hu, hp, hn, eq_comm]
              · by_cases hl : vx.val = ey.val
                · have hlt : ey.val < B i := by simpa [hl] using vx.isLt
                  have hne : ey.val ≠ vx.val + 1 := by omega
                  simp [hu, hl, hlt, hne, eq_comm]
                · have hne1 : ey.val ≠ vx.val + 1 := by omega
                  have hne2 : ey.val ≠ vx.val := by omega
                  simp [hu, hl, hne1, hne2, eq_comm]
            have hsign : (-1 : ℝ) ^ dualVertexRankBefore x i =
                (-1 : ℝ) ^ dualVertexRankBefore y i := by rw [hrank]
            simp only [dualExteriorDifferenceAxisStencilBasis,
              dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
              dualUpperFace, dualLowerFace, Pi.smul_apply, smul_eq_mul,
              Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply]
            rw [hsign]
            congr 1
            have hprevEval :
                (if h : 0 < ey.val then
                  Finsupp.single
                    (Function.update y i (Sum.inl ⟨ey.val - 1, by omega⟩))
                    (1 : ℝ)
                else 0) x =
                (if 0 < ey.val then
                  (if ey.val = vx.val + 1 then (1 : ℝ) else 0) else 0) := by
              by_cases hp : 0 < ey.val
              · simp [hp, Finsupp.single_apply, hprev, eq_comm]
              · simp [hp]
            have hnextEval :
                (if h : ey.val < B i then
                  Finsupp.single
                    (Function.update y i (Sum.inl ⟨ey.val, h⟩)) (1 : ℝ)
                else 0) x =
                (if ey.val < B i then
                  (if ey.val = vx.val then (1 : ℝ) else 0) else 0) := by
              by_cases hlt : ey.val < B i
              · simp [hlt, Finsupp.single_apply, hnext, eq_comm]
              · simp [hlt]
            rw [hprevEval, hnextEval]
            have hupperEval :
                (if Function.update x i
                    (Sum.inr ⟨vx.val + 1,
                      Nat.lt_succ_of_le (Nat.succ_le_of_lt vx.isLt)⟩) = y
                  then (1 : ℝ) else 0) =
                (if vx.val + 1 = ey.val then (1 : ℝ) else 0) := by
              exact if_congr hupper rfl rfl
            have hlowerEval :
                (if Function.update x i
                    (Sum.inr ⟨vx.val, Nat.lt_succ_of_le vx.isLt.le⟩) = y
                  then (1 : ℝ) else 0) =
                (if vx.val = ey.val then (1 : ℝ) else 0) := by
              exact if_congr hlower rfl rfl
            rw [hupperEval, hlowerEval]
            exact hcoef
          · push Not at hoff
            obtain ⟨k, hki, hxy⟩ := hoff
            have hupper : Function.update x i
                (Sum.inr ⟨vx.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt vx.isLt)⟩) ≠ y := by
              intro h
              exact hxy ((Function.update_eq_iff.mp h).2 k hki)
            have hlower : Function.update x i
                (Sum.inr ⟨vx.val, Nat.lt_succ_of_le vx.isLt.le⟩) ≠ y := by
              intro h
              exact hxy ((Function.update_eq_iff.mp h).2 k hki)
            by_cases hp : 0 < ey.val
            · have hprev : Function.update y i
                  (Sum.inl ⟨ey.val - 1, by omega⟩) ≠ x := by
                intro h
                exact hxy.symm ((Function.update_eq_iff.mp h).2 k hki)
              by_cases hlt : ey.val < B i
              · have hnext : Function.update y i
                    (Sum.inl ⟨ey.val, hlt⟩) ≠ x := by
                  intro h
                  exact hxy.symm ((Function.update_eq_iff.mp h).2 k hki)
                simp [dualExteriorDifferenceAxisStencilBasis,
                  dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                  hp, hlt, hupper, hlower, hprev, hnext,
                  dualUpperFace, dualLowerFace]
              · simp [dualExteriorDifferenceAxisStencilBasis,
                  dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                  hp, hlt, hupper, hlower, hprev,
                  dualUpperFace, dualLowerFace]
            · by_cases hlt : ey.val < B i
              · have hnext : Function.update y i
                    (Sum.inl ⟨ey.val, hlt⟩) ≠ x := by
                  intro h
                  exact hxy.symm ((Function.update_eq_iff.mp h).2 k hki)
                simp [dualExteriorDifferenceAxisStencilBasis,
                  dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                  hp, hlt, hupper, hlower, hnext,
                  dualUpperFace, dualLowerFace]
              · simp [dualExteriorDifferenceAxisStencilBasis,
                  dualExteriorDifferenceAxisAdjointStencilBasis, hxi, hyi,
                  hp, hlt, hupper, hlower,
                  dualUpperFace, dualLowerFace]
end FroehlichSpencer.FS82.Gaussian
