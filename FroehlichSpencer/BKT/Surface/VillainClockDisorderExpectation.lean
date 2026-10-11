module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Surface.VillainClockDisorderObservable

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT

/-- The finite free-square expectation of (1.32) in the Villain-constrained clock law. -/
noncomputable def villainClockDisorderExpectation (N : ℕ) (hN : 0 < N) (β : ℝ)
    (hβ : 0 < β) (ξ : ℝ) (L r : ℕ) (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  let Λ := Finset.Icc (0 : ℤ) ((2 * L : ℕ) : ℤ) ×ˢ Finset.Icc (0 : ℤ) ((2 * L : ℕ) : ℤ)
  ∫ θ, villainClockDisorderObservable β hβ ξ L r Λ
    (fun m =>
      have h2 : L + L ≤ 2 * L := Nat.le_of_eq (Nat.two_mul L).symm
      have hx : (0 : ℤ) ≤ ((L + m.val + 1 : ℕ) : ℤ) ∧
          ((L + m.val + 1 : ℕ) : ℤ) ≤ ((2 * L : ℕ) : ℤ) :=
        ⟨Int.natCast_nonneg _,
          Int.ofNat_le.2 (Nat.le_trans (Nat.add_le_add_left (Nat.lt_of_lt_of_le m.isLt hr) L) h2)⟩
      ⟨Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2
          ⟨Int.natCast_nonneg L, Int.ofNat_le.2 (Nat.le_trans (Nat.le_add_right L L) h2)⟩⟩,
        Finset.mem_product.2 ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2
          ⟨Int.le_add_one (Int.natCast_nonneg L),
            Int.ofNat_le.2 (Nat.le_trans (Nat.add_le_add_left hL L) h2)⟩⟩⟩) θ
    ∂villainClockModel N hN β hβ Λ

end FroehlichSpencer.BKT

end
