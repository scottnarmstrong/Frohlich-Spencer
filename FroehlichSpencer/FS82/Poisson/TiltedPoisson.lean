module
public import FroehlichSpencer.FS82.Poisson.FinRec
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Complex Matrix
noncomputable section

def finPrimalTerm (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℂ) (x : Fin n → ℤ) : ℂ :=
  cexp (-(Real.pi : ℂ) * finQuad n A x +
    2 * Real.pi * finLinearCoord w x)

def finDualTerm (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℂ) (k : Fin n → ℤ) : ℂ :=
  cexp ((Real.pi : ℂ) * ∑ i, ∑ j,
    (w i - I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) * (w j - I * (k j : ℂ)))

theorem fin_primal_summable (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (w : Fin n → ℂ) :
    Summable (finPrimalTerm n A w) := by
  exact summable_tilted_gaussian A hA w

theorem fin_dual_summable (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (w : Fin n → ℂ) : Summable (finDualTerm n A w) := by
  exact summable_dual_tilted_gaussian A hA w

private theorem scalar_theta_exp_rewrite (a : ℂ) (l : ℤ) (b : ℂ) :
    -Real.pi / a * ((l : ℂ) + I * b) ^ 2 =
      (Real.pi : ℂ) / a * (b - I * (l : ℂ)) ^ 2 := by
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem ofReal_csqrt_pos (a : ℝ) (ha : 0 < a) :
    (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
  have hy : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [← hy, ← Complex.ofReal_cpow ha.le]
  rw [Real.sqrt_eq_rpow]

private theorem scalar_theta_real_prefactor (a : ℝ) (ha : 0 < a) :
    1 / (a : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt a : ℝ) : ℂ)⁻¹ := by
  rw [ofReal_csqrt_pos a ha]
  simp

private theorem fin_det_sqrt_split (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosDef) :
    Real.sqrt A.det = Real.sqrt (finScalar n A) * Real.sqrt (finSchur n A).det := by
  rw [fin_det_split n A hA]
  exact Real.sqrt_mul (le_of_lt (fin_scalar_pos n A hA)) (finSchur n A).det

private theorem fin_scalar_tsum (a : ℝ) (ha : 0 < a) (b : ℂ) :
    (∑' k : ℤ, cexp (-(Real.pi : ℂ) * (a : ℂ) * (k : ℂ)^2 +
      2 * Real.pi * b * (k : ℂ))) =
      ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
        ∑' l : ℤ, cexp ((Real.pi : ℂ) / (a : ℂ) * (b - I * (l : ℂ))^2) := by
  have h := Complex.tsum_exp_neg_quadratic (a := (a : ℂ)) (by simpa using ha) b
  rw [scalar_theta_real_prefactor a ha] at h
  have hterms (l : ℤ) :
      cexp (-Real.pi / (a : ℂ) * ((l : ℂ) + I * b)^2) =
        cexp ((Real.pi : ℂ) / (a : ℂ) * (b - I * (l : ℂ))^2) := by
    rw [scalar_theta_exp_rewrite]
  simpa [mul_assoc] using h.trans (congrArg (fun z : ℂ => ((Real.sqrt a : ℝ) : ℂ)⁻¹ * z)
    (tsum_congr hterms))

private theorem fin_base_poisson :
    ∀ A : Matrix (Fin 0) (Fin 0) ℝ, A.PosDef → ∀ w : Fin 0 → ℂ,
      (∑' x : Fin 0 → ℤ, finPrimalTerm 0 A w x) =
        ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * ∑' k : Fin 0 → ℤ, finDualTerm 0 A w k := by
  intro A hA w
  simp [finPrimalTerm, finDualTerm, finQuad, finLinearCoord]

private theorem fin_poisson (n : ℕ) :
    ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef → ∀ w : Fin n → ℂ,
      (∑' x : Fin n → ℤ, finPrimalTerm n A w x) =
        ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * ∑' k : Fin n → ℤ, finDualTerm n A w k := by
  induction n with
  | zero => exact fin_base_poisson
  | succ n ih =>
      intro A hA w
      let D : Matrix (Fin n) (Fin n) ℝ := blkD A
      let a : ℝ := finScalar n A
      let wTop : Fin n → ℂ := fun i => w (Fin.castSucc i)
      let P (x : Fin n → ℤ) : ℂ :=
        -(Real.pi : ℂ) * finQuad n D x + 2 * Real.pi * finLinearCoord wTop x
      let Q (x : Fin n → ℤ) (k : ℤ) : ℂ :=
        -(Real.pi : ℂ) * (a : ℂ) * (k : ℂ)^2 +
          2 * Real.pi * (w (Fin.last n) - finBilinear n A x) * (k : ℂ)
      let pairTerm (p : (Fin n → ℤ) × ℤ) : ℂ :=
        finPrimalTerm (n + 1) A w (finVector n p.1 p.2)
      have ha : 0 < a := by dsimp [a]; exact fin_scalar_pos n A hA
      have hD : D.PosDef := by
        have hD' := (reA_posdef hA).submatrix (e := Sum.inl)
          (by intro i j hij; exact Sum.inl.inj hij)
        have hEq : D = (reA A).submatrix Sum.inl Sum.inl := by
          ext i j
          rfl
        rw [hEq]
        exact hD'
      have hPrimal := fin_primal_summable (n + 1) A hA w
      have hpair : Summable pairTerm := by
        dsimp [pairTerm, finVector]
        exact ((finSumPiEquiv n).summable_iff
          (f := finPrimalTerm (n + 1) A w)).mpr hPrimal
      have hpair_exp (p : (Fin n → ℤ) × ℤ) :
          pairTerm p = cexp (P p.1 + Q p.1 p.2) := by
        simpa [pairTerm, finPrimalTerm, P, Q, D, a, wTop, finQuad,
          finLinearCoord, finScalar, finVector, finLinear] using
          congrArg cexp (fin_exponent_split n A hA w p.1 p.2)
      have hpair_mixed (p : (Fin n → ℤ) × ℤ) :
          pairTerm p = cexp (P p.1) * cexp (Q p.1 p.2) := by
        rw [hpair_exp, Complex.exp_add]
      let b (x : Fin n → ℤ) : ℂ := w (Fin.last n) - finBilinear n A x
      have hinner (x : Fin n → ℤ) :
          (∑' k : ℤ, pairTerm (x, k)) =
            ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
              ∑' l : ℤ, cexp (finMixedExp n A w x l) := by
        calc
          (∑' k : ℤ, pairTerm (x, k)) =
              ∑' k : ℤ, cexp (P x) * cexp (Q x k) := by
                apply tsum_congr
                intro k
                rw [hpair_mixed]
          _ = cexp (P x) * ∑' k : ℤ, cexp (Q x k) := tsum_mul_left
          _ = cexp (P x) * (((Real.sqrt a : ℝ) : ℂ)⁻¹ *
                ∑' l : ℤ, cexp ((Real.pi : ℂ) / (a : ℂ) *
                  (b x - I * (l : ℂ))^2)) := by
                apply congrArg (fun z : ℂ => cexp (P x) * z)
                dsimp [Q, a, b]
                exact fin_scalar_tsum (finScalar n A) ha
                  (w (Fin.last n) - finBilinear n A x)
          _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
                (∑' l : ℤ, cexp (P x) *
                  cexp ((Real.pi : ℂ) / (a : ℂ) * (b x - I * (l : ℂ))^2)) := by
                calc
                  _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
                        (cexp (P x) *
                          ∑' l : ℤ, cexp ((Real.pi : ℂ) / (a : ℂ) *
                            (b x - I * (l : ℂ))^2)) := by ring
                  _ = _ := by rw [← tsum_mul_left]
          _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
                ∑' l : ℤ, cexp (finMixedExp n A w x l) := by
                congr 1
                apply tsum_congr
                intro l
                rw [← Complex.exp_add]
                dsimp [P, b, finMixedExp, D, a, wTop, finLinearCoord, finLinear]
      have hmix : Summable
          (fun p : (Fin n → ℤ) × ℤ => cexp (finMixedExp n A w p.1 p.2)) :=
        fin_mixed_exp_summable n A hA w
      have hsum_mixed (l : ℤ) :
          (∑' x : Fin n → ℤ, cexp (finMixedExp n A w x l)) =
            cexp ((Real.pi : ℂ) / (a : ℂ) *
                (w (Fin.last n) - I * (l : ℂ))^2) *
              ∑' x : Fin n → ℤ,
                finPrimalTerm n (finSchur n A) (finSchurSource n A w l) x := by
        calc
          _ = ∑' x : Fin n → ℤ,
                cexp ((Real.pi : ℂ) / (a : ℂ) *
                    (w (Fin.last n) - I * (l : ℂ))^2) *
                  finPrimalTerm n (finSchur n A) (finSchurSource n A w l) x := by
              apply tsum_congr
              intro x
              unfold finMixedExp
              dsimp [a]
              rw [fin_schur_complete_square n A hA w x l]
              simp only [finPrimalTerm, finLinearCoord]
              rw [← Complex.exp_add]
          _ = _ := tsum_mul_left
      have hdualSchur (l : ℤ) :=
        ih (finSchur n A) (fin_schur_pos n A hA) (finSchurSource n A w l)
      have hmixSwap : Summable
          (fun p : ℤ × (Fin n → ℤ) => cexp (finMixedExp n A w p.2 p.1)) := by
        have hcomp : Summable
            ((fun p : ℤ × (Fin n → ℤ) => cexp (finMixedExp n A w p.2 p.1)) ∘
              Equiv.prodComm (Fin n → ℤ) ℤ) := by
          convert hmix using 1
          ext p
          rfl
        exact (Equiv.prodComm (Fin n → ℤ) ℤ).summable_iff.mp hcomp
      have hswap :
          (∑' x : Fin n → ℤ, ∑' l : ℤ, cexp (finMixedExp n A w x l)) =
            ∑' l : ℤ, ∑' x : Fin n → ℤ, cexp (finMixedExp n A w x l) := by
        calc
          _ = ∑' p : (Fin n → ℤ) × ℤ, cexp (finMixedExp n A w p.1 p.2) :=
                hmix.tsum_prod.symm
          _ = ∑' p : ℤ × (Fin n → ℤ), cexp (finMixedExp n A w p.2 p.1) :=
                (Equiv.prodComm (Fin n → ℤ) ℤ).tsum_eq
                  (fun p : ℤ × (Fin n → ℤ) => cexp (finMixedExp n A w p.2 p.1))
          _ = _ := hmixSwap.tsum_prod
      have hdualPairSummable := fin_dual_summable (n + 1) A hA w
      have hdualPair : Summable
          (fun p : (Fin n → ℤ) × ℤ =>
            finDualTerm (n + 1) A w (finVector n p.1 p.2)) := by
        dsimp [finVector]
        exact ((finSumPiEquiv n).summable_iff (f := finDualTerm (n + 1) A w)).mpr
          hdualPairSummable
      have hdualTerm (p : (Fin n → ℤ) × ℤ) :
          cexp ((Real.pi : ℂ) / (a : ℂ) *
              (w (Fin.last n) - I * (p.2 : ℂ))^2) *
            finDualTerm n (finSchur n A) (finSchurSource n A w p.2) p.1 =
            finDualTerm (n + 1) A w (finVector n p.1 p.2) := by
        dsimp [finDualTerm]
        rw [fin_dual_quadratic_split n A hA w p.1 p.2]
        rw [← Complex.exp_add]
        congr 1
        dsimp [a]
        rw [div_eq_mul_inv]
        ring
      have hfullSwap : Summable
          (fun q : ℤ × (Fin n → ℤ) =>
            finDualTerm (n + 1) A w (finVector n q.2 q.1)) := by
        have hcomp : Summable
            ((fun q : ℤ × (Fin n → ℤ) =>
              finDualTerm (n + 1) A w (finVector n q.2 q.1)) ∘
              Equiv.prodComm (Fin n → ℤ) ℤ) := by
          convert hdualPair using 1
          ext q
          rfl
        exact (Equiv.prodComm (Fin n → ℤ) ℤ).summable_iff.mp hcomp
      have hweightSwap : Summable
          (fun q : ℤ × (Fin n → ℤ) =>
            cexp ((Real.pi : ℂ) / (a : ℂ) *
              (w (Fin.last n) - I * (q.1 : ℂ))^2) *
              finDualTerm n (finSchur n A) (finSchurSource n A w q.1) q.2) := by
        apply hfullSwap.congr
        intro q
        symm
        exact hdualTerm (q.2, q.1)
      have hweightSwap_tsum :
          (∑' q : ℤ × (Fin n → ℤ),
            cexp ((Real.pi : ℂ) / (a : ℂ) *
              (w (Fin.last n) - I * (q.1 : ℂ))^2) *
              finDualTerm n (finSchur n A) (finSchurSource n A w q.1) q.2) =
            ∑' l : ℤ, cexp ((Real.pi : ℂ) / (a : ℂ) *
              (w (Fin.last n) - I * (l : ℂ))^2) *
              ∑' j : Fin n → ℤ,
              finDualTerm n (finSchur n A) (finSchurSource n A w l) j := by
        rw [hweightSwap.tsum_prod]
        apply tsum_congr
        intro l
        change (∑' j : Fin n → ℤ,
            cexp ((Real.pi : ℂ) / (a : ℂ) *
              (w (Fin.last n) - I * (l : ℂ))^2) *
              finDualTerm n (finSchur n A) (finSchurSource n A w l) j) =
          cexp ((Real.pi : ℂ) / (a : ℂ) *
            (w (Fin.last n) - I * (l : ℂ))^2) *
            ∑' j : Fin n → ℤ,
              finDualTerm n (finSchur n A) (finSchurSource n A w l) j
        rw [tsum_mul_left]
      have hcoef :
          ((Real.sqrt a : ℝ) : ℂ)⁻¹ * ((Real.sqrt (finSchur n A).det : ℝ) : ℂ)⁻¹ =
            ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ := by
        have hroot := congrArg (fun r : ℝ => (r : ℂ)) (fin_det_sqrt_split n A hA)
        rw [hroot]
        rw [Complex.ofReal_mul, mul_inv]
      calc
        (∑' x : Fin (n + 1) → ℤ, finPrimalTerm (n + 1) A w x) =
            ∑' p : (Fin n → ℤ) × ℤ, pairTerm p :=
              ((finSumPiEquiv n).tsum_eq
                (fun x : Fin (n + 1) → ℤ => finPrimalTerm (n + 1) A w x)).symm
        _ = ∑' x : Fin n → ℤ, ∑' k : ℤ, pairTerm (x, k) := hpair.tsum_prod
        _ = ∑' x : Fin n → ℤ,
              ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
                ∑' l : ℤ, cexp (finMixedExp n A w x l) := by
              apply tsum_congr
              intro x
              exact hinner x
        _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
              ∑' x : Fin n → ℤ, ∑' l : ℤ, cexp (finMixedExp n A w x l) := tsum_mul_left
        _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
              ∑' l : ℤ, ∑' x : Fin n → ℤ, cexp (finMixedExp n A w x l) := by
              exact congrArg (fun z : ℂ => ((Real.sqrt a : ℝ) : ℂ)⁻¹ * z) hswap
        _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
              ∑' l : ℤ,
                (cexp ((Real.pi : ℂ) / (a : ℂ) *
                    (w (Fin.last n) - I * (l : ℂ))^2) *
                  (((Real.sqrt (finSchur n A).det : ℝ) : ℂ)⁻¹ *
                    ∑' j : Fin n → ℤ,
                      finDualTerm n (finSchur n A) (finSchurSource n A w l) j)) := by
              congr 1
              apply tsum_congr
              intro l
              rw [hsum_mixed l, hdualSchur l]
        _ = ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
              ∑' p : (Fin n → ℤ) × ℤ,
                cexp ((Real.pi : ℂ) / (a : ℂ) *
                    (w (Fin.last n) - I * (p.2 : ℂ))^2) *
                  finDualTerm n (finSchur n A) (finSchurSource n A w p.2) p.1 := by
              calc
                _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
                      (((Real.sqrt (finSchur n A).det : ℝ) : ℂ)⁻¹ *
                        ∑' l : ℤ, cexp ((Real.pi : ℂ) / (a : ℂ) *
                          (w (Fin.last n) - I * (l : ℂ))^2) *
                          ∑' j : Fin n → ℤ,
                            finDualTerm n (finSchur n A) (finSchurSource n A w l) j) := by
                    congr 1
                    calc
                      _ = ∑' l : ℤ, ((Real.sqrt (finSchur n A).det : ℝ) : ℂ)⁻¹ *
                            (cexp ((Real.pi : ℂ) / (a : ℂ) *
                              (w (Fin.last n) - I * (l : ℂ))^2) *
                              ∑' j : Fin n → ℤ,
                                finDualTerm n (finSchur n A) (finSchurSource n A w l) j) := by
                          apply tsum_congr
                          intro l
                          ring
                      _ = _ := tsum_mul_left
                _ = ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
                      ∑' l : ℤ, cexp ((Real.pi : ℂ) / (a : ℂ) *
                        (w (Fin.last n) - I * (l : ℂ))^2) *
                        ∑' j : Fin n → ℤ,
                          finDualTerm n (finSchur n A) (finSchurSource n A w l) j := by
                    rw [← mul_assoc, hcoef]
                _ = ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
                      ∑' q : ℤ × (Fin n → ℤ),
                        cexp ((Real.pi : ℂ) / (a : ℂ) *
                          (w (Fin.last n) - I * (q.1 : ℂ))^2) *
                          finDualTerm n (finSchur n A) (finSchurSource n A w q.1) q.2 := by
                    congr 1
                    exact hweightSwap_tsum.symm
                _ = ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
                      ∑' p : (Fin n → ℤ) × ℤ,
                        cexp ((Real.pi : ℂ) / (a : ℂ) *
                          (w (Fin.last n) - I * (p.2 : ℂ))^2) *
                          finDualTerm n (finSchur n A) (finSchurSource n A w p.2) p.1 := by
                    congr 1
                    exact ((Equiv.prodComm (Fin n → ℤ) ℤ).tsum_eq
                      (fun q : ℤ × (Fin n → ℤ) =>
                        cexp ((Real.pi : ℂ) / (a : ℂ) *
                          (w (Fin.last n) - I * (q.1 : ℂ))^2) *
                          finDualTerm n (finSchur n A) (finSchurSource n A w q.1) q.2)).symm
        _ = ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
              ∑' p : (Fin n → ℤ) × ℤ,
                finDualTerm (n + 1) A w (finVector n p.1 p.2) := by
              congr 1
              apply tsum_congr
              intro p
              exact hdualTerm p
        _ = ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
              ∑' k : Fin (n + 1) → ℤ, finDualTerm (n + 1) A w k := by
              congr 1
              exact (finSumPiEquiv n).tsum_eq _

def primalQuadraticExp {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (w : ι → ℂ) (x : ι → ℤ) : ℂ :=
  cexp (-(Real.pi : ℂ) *
    (∑ i, ∑ j, (x i : ℂ) * (A i j : ℂ) * (x j : ℂ)) +
      2 * Real.pi * ∑ i, w i * (x i : ℂ))

def dualQuadraticExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (w : ι → ℂ) (k : ι → ℤ) : ℂ :=
  cexp ((Real.pi : ℂ) * ∑ i, ∑ j,
    (w i - I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) * (w j - I * (k j : ℂ)))

theorem summable_primal_quadratic_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (w : ι → ℂ) :
    Summable (primalQuadraticExp A w) := by
  exact summable_tilted_gaussian A hA w

theorem summable_dual_quadratic_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (w : ι → ℂ) :
    Summable (dualQuadraticExp A w) := by
  exact summable_dual_tilted_gaussian A hA w

theorem tsum_cexp_neg_quadratic_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (w : ι → ℂ) :
    (∑' n : ι → ℤ, cexp (-(Real.pi : ℂ) *
        (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ)) +
          2 * Real.pi * ∑ i, w i * (n i : ℂ))) =
      ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
        ∑' k : ι → ℤ, cexp ((Real.pi : ℂ) * ∑ i, ∑ j,
          (w i - I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) * (w j - I * (k j : ℂ))) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E : (Fin (Fintype.card ι) → ℤ) ≃ (ι → ℤ) :=
    Equiv.piCongrLeft (fun _ : ι => ℤ) e.symm
  let A' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    Matrix.reindex e e A
  let w' : Fin (Fintype.card ι) → ℂ := fun i => w (e.symm i)
  have hA' : A'.PosDef := by
    dsimp [A']
    exact hA.submatrix (e := e.symm) e.symm.injective
  have hInv : A'⁻¹ = Matrix.reindex e e A⁻¹ := by
    dsimp [A']
    exact Matrix.inv_reindex e e A
  have hQuad (x : Fin (Fintype.card ι) → ℤ) :
      (∑ i : ι, ∑ j : ι,
        (E x i : ℂ) * (A i j : ℂ) * (E x j : ℂ)) =
      finQuad (Fintype.card ι) A' x := by
    calc
      _ = ∑ i : Fin (Fintype.card ι), ∑ j : ι,
            (E x (e.symm i) : ℂ) * (A (e.symm i) j : ℂ) * (E x j : ℂ) := by
              apply Fintype.sum_equiv e
              intro i
              simp
      _ = ∑ i : Fin (Fintype.card ι), ∑ j : Fin (Fintype.card ι),
            (E x (e.symm i) : ℂ) * (A (e.symm i) (e.symm j) : ℂ) *
              (E x (e.symm j) : ℂ) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Fintype.sum_equiv e
              intro j
              simp
      _ = finQuad (Fintype.card ι) A' x := by
            simp [finQuad, A', Matrix.reindex_apply, E]
  have hLinear (x : Fin (Fintype.card ι) → ℤ) :
      (∑ i : ι, w i * (E x i : ℂ)) =
        finLinearCoord w' x := by
    calc
      _ = ∑ i : Fin (Fintype.card ι), w (e.symm i) * (E x (e.symm i) : ℂ) := by
            apply Fintype.sum_equiv e
            intro i
            simp
      _ = finLinearCoord w' x := by simp [finLinearCoord, w', E]
  have hPrimalReindex :
      (∑' x : ι → ℤ, primalQuadraticExp A w x) =
        ∑' x : Fin (Fintype.card ι) → ℤ,
          finPrimalTerm (Fintype.card ι) A' w' x := by
    calc
      _ = ∑' x : Fin (Fintype.card ι) → ℤ, primalQuadraticExp A w (E x) :=
            (E.tsum_eq (primalQuadraticExp A w)).symm
      _ = _ := by
            apply tsum_congr
            intro x
            simp only [primalQuadraticExp, finPrimalTerm]
            rw [hQuad x, hLinear x]
  have hDualQuad (x : Fin (Fintype.card ι) → ℤ) :
      (∑ i : ι, ∑ j : ι,
        (w i - I * (E x i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) *
          (w j - I * (E x j : ℂ))) =
      ∑ i : Fin (Fintype.card ι), ∑ j : Fin (Fintype.card ι),
        (w' i - I * (x i : ℂ)) * ((A'⁻¹ i j : ℝ) : ℂ) *
          (w' j - I * (x j : ℂ)) := by
    calc
      _ = ∑ i : Fin (Fintype.card ι), ∑ j : ι,
            (w (e.symm i) - I * (E x (e.symm i) : ℂ)) *
              ((A⁻¹ (e.symm i) j : ℝ) : ℂ) *
              (w j - I * (E x j : ℂ)) := by
              apply Fintype.sum_equiv e
              intro i
              simp
      _ = ∑ i : Fin (Fintype.card ι), ∑ j : Fin (Fintype.card ι),
            (w (e.symm i) - I * (E x (e.symm i) : ℂ)) *
              ((A⁻¹ (e.symm i) (e.symm j) : ℝ) : ℂ) *
              (w (e.symm j) - I * (E x (e.symm j) : ℂ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Fintype.sum_equiv e
              intro j
              simp
      _ = _ := by
            simp [w', E, hInv, Matrix.reindex_apply]
  have hDualReindex :
      (∑' k : ι → ℤ, dualQuadraticExp A w k) =
        ∑' k : Fin (Fintype.card ι) → ℤ, finDualTerm (Fintype.card ι) A' w' k := by
    calc
      _ = ∑' k : Fin (Fintype.card ι) → ℤ, dualQuadraticExp A w (E k) :=
            (E.tsum_eq (dualQuadraticExp A w)).symm
      _ = _ := by
            apply tsum_congr
            intro k
            simp only [dualQuadraticExp, finDualTerm]
            rw [hDualQuad k]
  have hdet : A'.det = A.det := by
    dsimp [A']
    exact Matrix.det_reindex_self e A
  change (∑' n : ι → ℤ, primalQuadraticExp A w n) =
    ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * ∑' k : ι → ℤ, dualQuadraticExp A w k
  rw [hPrimalReindex, hDualReindex]
  have hfin := fin_poisson (Fintype.card ι) A' hA' w'
  rw [hdet] at hfin
  exact hfin


end

end FroehlichSpencer.FS82.Poisson
