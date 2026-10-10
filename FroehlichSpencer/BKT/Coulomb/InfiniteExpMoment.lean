/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.SumRule
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# FS81 Theorem 5.1 in infinite volume

The exponential moment `⟨e^{φ(g)}⟩_{Λ_n} = e^{κ⟨g,Cg⟩/2} Ψ_n(g)` with the charge characteristic
function `Ψ_n(g) = ⟨cos (κ ⟨q, C g⟩)⟩_{Λ_n}` (`freeCharFunInternal`, `freeExpMoment_box_eq`).

The
observable `⟨q, C g⟩` is **not local** in the charges (`Cg ~ |x|⁻¹`), so convergence of local
correlations does not give convergence of `Ψ_n`.

Instead:

* `abs_freeCharFun_sub_le`: `|Ψ_n(g) - Ψ_n(g')| ≤ √(δ κ ⟨g-g', C(g-g')⟩)` uniformly in `n`, from
  `|cos a - cos b| ≤ |a - b|`, Cauchy–Schwarz for the positive gas
  (`gasExpectation_abs_sq_le`) and the free charge-fluctuation bound;
* dipole coordinates `g = ∑_x c(x)(δ_x - δ_0)` (`dipoleCombinationInternal`,
  `eq_dipoleCombination`) make this a uniform Lipschitz bound in the coefficients
  (`abs_freeCharFun_dipole_sub_le`);
* **`free_thermodynamic_limit_full_exists`**: one subsequence along which the field and charge
  two-point functions **and** `Ψ_n(g)` for **every** finitely supported zero-sum `g` converge
  (compactness on the countable family of rational dipole combinations, then density plus
  the uniform Lipschitz bound, by a Cauchy argument);
* **`free_infinite_expMoment`** / **`free_thermodynamic_limit_expMoment`**: FS81 Theorem 5.1 in
  infinite volume, `exp((1-δ) κ ⟨g,Cg⟩/2) ≤ lim ⟨e^{φ(g)}⟩_{Λ_n} ≤ exp(κ ⟨g,Cg⟩/2)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology Finset

/-! ### Expectation inequalities for positive gases -/

section Positive

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem gasExpectation_sub (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (F G : (V → ℤ) → ℝ) :
    gasExpectationInternal N T κ lam (fun p => F p - G p) =
      gasExpectationInternal N T κ lam F - gasExpectationInternal N T κ lam G := by
  unfold gasExpectationInternal
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem gasExpectation_add (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (F G : (V → ℤ) → ℝ) :
    gasExpectationInternal N T κ lam (fun p => F p + G p) =
      gasExpectationInternal N T κ lam F + gasExpectationInternal N T κ lam G := by
  unfold gasExpectationInternal
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem gasExpectation_mono (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (hlam : ∀ j n, 0 ≤ lam j n) {F G : (V → ℤ) → ℝ} (hFG : ∀ p, F p ≤ G p) :
    gasExpectationInternal N T κ lam F ≤ gasExpectationInternal N T κ lam G := by
  have := gasExpectation_nonneg N T κ lam hlam (F := fun p => G p - F p) fun p => by
    linarith [hFG p]
  rw [gasExpectation_sub] at this
  linarith

/-- Cauchy–Schwarz for a normalized positive gas: `(⟨|X|⟩)² ≤ ⟨X²⟩`. -/
theorem gasExpectation_abs_sq_le (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (hlam : ∀ j n, 0 ≤ lam j n) (hZ : gasPartitionInternal N T κ lam ≠ 0) (X : (V → ℤ) → ℝ) :
    gasExpectationInternal N T κ lam (fun p => |X p|) ^ 2 ≤
      gasExpectationInternal N T κ lam (fun p => X p ^ 2) := by
  set m := gasExpectationInternal N T κ lam (fun p => |X p|)
  have h := gasExpectation_nonneg N T κ lam hlam (F := fun p => (|X p| - m) ^ 2)
    fun p => sq_nonneg _
  have hexp : (fun p => (|X p| - m) ^ 2) = fun p => (X p ^ 2 - 2 * m * |X p|) + m ^ 2 := by
    funext p; rw [← sq_abs (X p)]; ring
  rw [hexp, gasExpectation_add, gasExpectation_sub, gasExpectation_const_mul] at h
  have h1 : gasExpectationInternal N T κ lam (fun _ => m ^ 2) = m ^ 2 := by
    have := gasExpectation_const_mul N T κ lam (m ^ 2) (fun _ => 1)
    simp only [mul_one] at this
    rw [this, gasExpectation_one N T κ lam hZ, mul_one]
  rw [h1] at h
  nlinarith

theorem abs_gasExpectation_le_abs (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (hlam : ∀ j n, 0 ≤ lam j n) (F : (V → ℤ) → ℝ) :
    |gasExpectationInternal N T κ lam F| ≤ gasExpectationInternal N T κ lam (fun p => |F p|) := by
  rw [abs_le]
  constructor
  · have := gasExpectation_mono N T κ lam hlam (F := fun p => -|F p|) (G := F)
      fun p => neg_abs_le (F p)
    have hn := gasExpectation_const_mul N T κ lam (-1) (fun p => |F p|)
    simp only [neg_one_mul] at hn
    linarith
  · exact gasExpectation_mono N T κ lam hlam fun p => le_abs_self (F p)

end Positive

/-! ### Dipole combinations -/

/-- The zero-sum test function `∑_{x ∈ [-R,R]²} c(x) (δ_x - δ_0)`. -/
def dipoleCombinationInternal (R : ℕ) (c : boxInternal R → ℝ) (u : ℤ × ℤ) : ℝ :=
  ∑ x, c x * dipoleTestInternal x.1 u

theorem dipoleCombination_supported (R : ℕ) (c : boxInternal R → ℝ) :
    SupportedInBox R (dipoleCombinationInternal R c) := by
  intro u hu
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [dipoleTest_supported x.2 u hu, mul_zero]

theorem sum_dipoleCombination (R : ℕ) (c : boxInternal R → ℝ) :
    ∑ u ∈ boxInternal R, dipoleCombinationInternal R c u = 0 := by
  unfold dipoleCombinationInternal
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [← Finset.mul_sum, sum_dipoleTest_box x.2, mul_zero]

theorem eq_dipoleCombination {R : ℕ} {f : ℤ × ℤ → ℝ} (hf : SupportedInBox R f)
    (hf0 : ∑ x ∈ boxInternal R, f x = 0) :
    f = dipoleCombinationInternal R (fun x => f x.1) := by
  funext u
  unfold dipoleCombinationInternal dipoleTestInternal
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [Finset.sum_coe_sort (boxInternal R) (fun x => if u = x then f x else 0),
    Finset.sum_coe_sort (boxInternal R) (fun x => if u = 0 then f x else 0),
    Finset.sum_ite_eq]
  have h2 : (∑ i ∈ boxInternal R, if u = 0 then f i else 0) = 0 := by
    split_ifs
    · exact hf0
    · simp
  rw [h2, sub_zero]
  split_ifs with hu
  · rfl
  · exact hf u hu

theorem dipoleCombination_sub (R : ℕ) (c c' : boxInternal R → ℝ) :
    (fun u => dipoleCombinationInternal R c u - dipoleCombinationInternal R c' u) =
      dipoleCombinationInternal R (c - c') := by
  funext u
  simp only [dipoleCombinationInternal, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem abs_dipoleTest_le (x u : ℤ × ℤ) : |dipoleTestInternal x u| ≤ 1 := by
  unfold dipoleTestInternal
  split_ifs <;> norm_num

theorem abs_dipoleCombination_le (R : ℕ) (c : boxInternal R → ℝ) (u : ℤ × ℤ) :
    |dipoleCombinationInternal R c u| ≤ ∑ x, |c x| := by
  unfold dipoleCombinationInternal
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_dipoleTest_le _ _)

/-- `∑_{u,v ∈ [-R,R]²} a(u - v)`. -/
def kernelMassInternal (R : ℕ) : ℝ :=
  ∑ u ∈ boxInternal R, ∑ v ∈ boxInternal R, potentialKernelInternal (u - v)

theorem kernelMass_nonneg (R : ℕ) : 0 ≤ kernelMassInternal R :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => potentialKernel_nonneg _

theorem wholePlaneQuad_dipoleCombination_le (R : ℕ) (c : boxInternal R → ℝ) :
    wholePlaneQuadInternal R (dipoleCombinationInternal R c) ≤
      kernelMassInternal R * (∑ x, |c x|) ^ 2 := by
  unfold wholePlaneQuadInternal kernelMassInternal
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  have hu := abs_dipoleCombination_le R c u
  have hv := abs_dipoleCombination_le R c v
  have ha := potentialKernel_nonneg (u - v)
  have hprod : |dipoleCombinationInternal R c u * dipoleCombinationInternal R c v| ≤
      (∑ x, |c x|) ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hu hv (abs_nonneg _) ((abs_nonneg _).trans hu)
  have := neg_abs_le (dipoleCombinationInternal R c u * dipoleCombinationInternal R c v)
  nlinarith

/-! ### The charge characteristic function in the boxes -/

/-- `Ψ_n(g) = ⟨cos (κ ⟨q, C g⟩)⟩_{Λ_n}`, so that `⟨e^{φ(g)}⟩_{Λ_n} = e^{κ⟨g,Cg⟩/2} Ψ_n(g)`. -/
def freeCharFunInternal (κ z : ℝ) (n : ℕ) (g : ℤ × ℤ → ℝ) : ℝ :=
  freeGasExpectationInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ z
    (fun p => Real.cos (κ * freeChargePairingInternal (Subtype.val : boxInternal n → ℤ × ℤ)
      (fun v => g v.1) p))

theorem freeExpMoment_box_eq (κ z : ℝ) (n : ℕ) (g : ℤ × ℤ → ℝ) :
    freeExpMomentInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ z (fun v => g v.1) 1 =
      Real.exp (κ * freeQuadInternal (Subtype.val : boxInternal n → ℤ × ℤ) (fun v => g v.1) / 2) *
        freeCharFunInternal κ z n g := by
  unfold freeExpMomentInternal freeCharFunInternal
  simp only [one_pow, mul_one, one_mul]

theorem abs_freeCharFun_le (κ : ℝ) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) (g : ℤ × ℤ → ℝ) :
    |freeCharFunInternal κ z n g| ≤ 1 :=
  abs_gasExpectation_le 1 _ κ _ (fun _ m => hardCoreWeight_nonneg hz m)
    (freeGasPartition_pos _ κ hz) fun _ _ => Real.abs_cos_le_one _

theorem freeChargePairing_sub {V : Type*} [Fintype V] (pos : V → ℤ × ℤ) (f f' : V → ℝ)
    (p : V → ℤ) :
    freeChargePairingInternal pos (f - f') p =
      freeChargePairingInternal pos f p - freeChargePairingInternal pos f' p := by
  unfold freeChargePairingInternal
  rw [map_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.sub_apply]
  ring

/-- **Uniform Lipschitz bound** of the box characteristic functions, from the free
charge-fluctuation bound: `|Ψ_n(g) - Ψ_n(g')| ≤ √(δ κ ⟨g - g', C (g - g')⟩)` for zero-sum test
functions in `[-R, R]² ⊆ Λ_n`. -/
theorem abs_freeCharFun_sub_le {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {n R : ℕ} (hRn : R ≤ n) {g g' : ℤ × ℤ → ℝ}
    (hg : SupportedInBox R g) (hg' : SupportedInBox R g')
    (hg0 : ∑ x ∈ boxInternal R, g x = 0) (hg0' : ∑ x ∈ boxInternal R, g' x = 0) :
    |freeCharFunInternal κ z n g - freeCharFunInternal κ z n g'| ≤
      Real.sqrt (δ * κ * wholePlaneQuadInternal R (fun u => g u - g' u)) := by
  have hlam : ∀ (j : boxInternal n) m, 0 ≤ (fun _ => hardCoreWeightInternal z) j m :=
    fun _ m => hardCoreWeight_nonneg hz m
  have hZ := (freeGasPartition_pos (Subtype.val : boxInternal n → ℤ × ℤ) κ hz).ne'
  have hd : SupportedInBox R (fun u => g u - g' u) := fun u hu => by simp [hg u hu, hg' u hu]
  have hd0 : ∑ v : boxInternal n, (fun u => g u - g' u) v.1 = 0 := by
    rw [Finset.sum_coe_sort (boxInternal n) (fun u => g u - g' u),
      sum_box_eq_of_supported hRn hd, Finset.sum_sub_distrib, hg0, hg0', sub_zero]
  have hfl := free_chargeFluctuation_le h (boxInternal n) κ hκ hκκ₀ z hz hzκ _ hd0
  rw [freeQuad_box_eq hRn hd] at hfl
  set P := fun p : boxInternal n → ℤ => κ * freeChargePairingInternal
    (Subtype.val : boxInternal n → ℤ × ℤ) (fun v => g v.1 - g' v.1) p
  have hPsplit : ∀ p, κ * freeChargePairingInternal (Subtype.val : boxInternal n → ℤ × ℤ)
      (fun v => g v.1) p - κ * freeChargePairingInternal (Subtype.val : boxInternal n → ℤ × ℤ)
      (fun v => g' v.1) p = P p := by
    intro p
    rw [← mul_sub, ← freeChargePairing_sub]
    rfl
  unfold freeCharFunInternal freeGasExpectationInternal
  rw [← gasExpectation_sub]
  refine (abs_gasExpectation_le_abs 1 _ κ _ hlam _).trans ?_
  have hmono : gasExpectationInternal 1 (freePotentialOpInternal (Subtype.val : boxInternal n → ℤ × ℤ))
      κ (fun _ => hardCoreWeightInternal z) (fun p => |Real.cos (κ * freeChargePairingInternal
        Subtype.val (fun v => g v.1) p) - Real.cos (κ * freeChargePairingInternal Subtype.val
          (fun v => g' v.1) p)|) ≤
      gasExpectationInternal 1 (freePotentialOpInternal (Subtype.val : boxInternal n → ℤ × ℤ))
        κ (fun _ => hardCoreWeightInternal z) (fun p => |P p|) :=
    gasExpectation_mono 1 _ κ _ hlam fun p => by
      rw [← hPsplit]; exact Real.abs_cos_sub_cos_le _ _
  refine hmono.trans ?_
  have hcs := gasExpectation_abs_sq_le 1 _ κ _ hlam hZ P
  have hnn : 0 ≤ gasExpectationInternal 1 (freePotentialOpInternal (Subtype.val : boxInternal n → ℤ × ℤ))
      κ (fun _ => hardCoreWeightInternal z) (fun p => |P p|) :=
    gasExpectation_nonneg 1 _ κ _ hlam fun p => abs_nonneg _
  rw [Real.le_sqrt hnn (by
    have := gasExpectation_nonneg 1 (freePotentialOpInternal (Subtype.val : boxInternal n → ℤ × ℤ))
      κ _ hlam (fun p => sq_nonneg (P p))
    unfold freeGasExpectationInternal at hfl
    linarith)]
  unfold freeGasExpectationInternal at hfl
  exact hcs.trans hfl

/-- Lipschitz bound in the dipole coefficients, uniform in the volume. -/
theorem abs_freeCharFun_dipole_sub_le {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (hδ : 0 ≤ δ) (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {n R : ℕ} (hRn : R ≤ n) (c c' : boxInternal R → ℝ) :
    |freeCharFunInternal κ z n (dipoleCombinationInternal R c) -
        freeCharFunInternal κ z n (dipoleCombinationInternal R c')| ≤
      Real.sqrt (δ * κ * kernelMassInternal R) * ∑ x, |c x - c' x| := by
  refine (abs_freeCharFun_sub_le h κ hκ hκκ₀ z hz hzκ hRn (dipoleCombination_supported R c)
    (dipoleCombination_supported R c') (sum_dipoleCombination R c)
    (sum_dipoleCombination R c')).trans ?_
  rw [dipoleCombination_sub]
  have hq := wholePlaneQuad_dipoleCombination_le R (c - c')
  have hA := kernelMass_nonneg R
  rw [← Real.sqrt_sq (Finset.sum_nonneg fun x _ => abs_nonneg (c x - c' x)), ← Real.sqrt_mul
    (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  simp only [Pi.sub_apply] at hq
  have : 0 ≤ δ * κ := by positivity
  nlinarith

/-! ### ′: joint existence of all thermodynamic limits (field, charge, exponential moments) -/

/-- **Existence of a joint thermodynamic limit** for the free boxes: along one subsequence the
field and charge two-point functions converge, and the characteristic functions `Ψ_n(g)` (hence
the exponential moments `⟨e^{φ(g)}⟩_{Λ_n}`) converge for **every** finitely supported zero-sum
test function `g`. The proof uses compactness on the countable family of rational dipole
combinations and the uniform Lipschitz bound `abs_freeCharFun_dipole_sub_le`. -/
theorem free_thermodynamic_limit_full_exists {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ S : ℤ × ℤ → ℤ × ℤ → ℝ,
      (∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop (𝓝 (Γ x y))) ∧
      (∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
        (𝓝 (S x y))) ∧
      ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g → ∑ x ∈ boxInternal R, g x = 0 →
        ∃ m : ℝ, Tendsto (fun k => freeCharFunInternal κ z (φ k) g) atTop (𝓝 m) := by
  obtain ⟨φ, hφ, l, hl⟩ := exists_subseq_tendsto_pointwise
    (ι := (Bool × (ℤ × ℤ) × (ℤ × ℤ)) ⊕ (Σ R : ℕ, boxInternal R → ℚ))
    (fun n i => match i with
      | Sum.inl i => if i.1 then freeFieldCorrelationInternal κ z n i.2.1 i.2.2
          else freeChargeCorrelationInternal κ z n i.2.1 i.2.2
      | Sum.inr ⟨R, c⟩ => freeCharFunInternal κ z n (dipoleCombinationInternal R fun x => (c x : ℝ)))
    (fun i => match i with
      | Sum.inl i => if i.1 then fieldCorrelationBoundInternal κ i.2.1 i.2.2 else 1
      | Sum.inr _ => 1)
    (fun n i => by
      rcases i with ⟨b, x, y⟩ | ⟨R, c⟩
      · cases b
        · exact abs_freeChargeCorrelation_le κ hz n x y
        · exact abs_freeFieldCorrelation_le h hδ1 κ hκ hκκ₀ z hz hzκ n x y
      · exact abs_freeCharFun_le κ hz n _)
  refine ⟨φ, hφ, fun x y => l (Sum.inl (true, x, y)), fun x y => l (Sum.inl (false, x, y)),
    fun x y => by simpa using hl (Sum.inl (true, x, y)),
    fun x y => by simpa using hl (Sum.inl (false, x, y)), fun R g hg hg0 => ?_⟩
  -- convergence on rational dipole combinations
  have hrat : ∀ c : boxInternal R → ℚ, Tendsto (fun k => freeCharFunInternal κ z (φ k)
      (dipoleCombinationInternal R fun x => (c x : ℝ))) atTop (𝓝 (l (Sum.inr ⟨R, c⟩))) :=
    fun c => by simpa using hl (Sum.inr ⟨R, c⟩)
  rw [eq_dipoleCombination hg hg0]
  set c : boxInternal R → ℝ := fun x => g x.1
  set L := Real.sqrt (δ * κ * kernelMassInternal R)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hev : ∀ᶠ k in atTop, R ≤ φ k := hφ.tendsto_atTop.eventually_ge_atTop R
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun η hη => ?_)
  -- a rational approximation of the coefficients
  set ρ := η / (3 * (L + 1) * ((Fintype.card (boxInternal R) : ℝ) + 1))
  have hρ : 0 < ρ := by positivity
  choose c' hc' using fun x : boxInternal R => exists_rat_btwn (show c x - ρ < c x + ρ by linarith)
  have hclose : ∑ x, |c x - (c' x : ℝ)| ≤ (Fintype.card (boxInternal R) : ℝ) * ρ := by
    calc ∑ x, |c x - (c' x : ℝ)| ≤ ∑ _x : boxInternal R, ρ :=
          Finset.sum_le_sum fun x _ => by
            rw [abs_le]; constructor <;> linarith [(hc' x).1, (hc' x).2]
      _ = (Fintype.card (boxInternal R) : ℝ) * ρ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsmall : L * ∑ x, |c x - (c' x : ℝ)| < η / 3 := by
    have hcard : (0 : ℝ) ≤ Fintype.card (boxInternal R) := by positivity
    calc L * ∑ x, |c x - (c' x : ℝ)| ≤ L * ((Fintype.card (boxInternal R) : ℝ) * ρ) :=
          mul_le_mul_of_nonneg_left hclose hL
      _ < η / 3 := by
          rw [show L * ((Fintype.card (boxInternal R) : ℝ) * ρ) =
            η / 3 * (L / (L + 1) * ((Fintype.card (boxInternal R) : ℝ) /
              ((Fintype.card (boxInternal R) : ℝ) + 1))) by simp only [ρ]; field_simp]
          have h1 : L / (L + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
          have h2 : (Fintype.card (boxInternal R) : ℝ) / ((Fintype.card (boxInternal R) : ℝ) + 1) < 1 := by
            rw [div_lt_one (by linarith)]; linarith
          have h3 : L / (L + 1) * ((Fintype.card (boxInternal R) : ℝ) /
              ((Fintype.card (boxInternal R) : ℝ) + 1)) < 1 :=
            (mul_le_of_le_one_right (by positivity) h2.le).trans_lt h1
          nlinarith
  obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.1 (hrat c').cauchySeq (η / 3) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hev
  refine ⟨max N1 N2, fun a ha b hb => ?_⟩
  have ha2 : R ≤ φ a := hN2 a (le_of_max_le_right ha)
  have hb2 : R ≤ φ b := hN2 b (le_of_max_le_right hb)
  have e1 := abs_freeCharFun_dipole_sub_le h hδ κ hκ hκκ₀ z hz hzκ ha2 c (fun x => (c' x : ℝ))
  have e2 := abs_freeCharFun_dipole_sub_le h hδ κ hκ hκκ₀ z hz hzκ hb2 c (fun x => (c' x : ℝ))
  have e3 := hN1 a (le_of_max_le_left ha) b (le_of_max_le_left hb)
  rw [Real.dist_eq] at e3 ⊢
  set A := freeCharFunInternal κ z (φ a) (dipoleCombinationInternal R c)
  set B := freeCharFunInternal κ z (φ b) (dipoleCombinationInternal R c)
  set A' := freeCharFunInternal κ z (φ a) (dipoleCombinationInternal R fun x => (c' x : ℝ))
  set B' := freeCharFunInternal κ z (φ b) (dipoleCombinationInternal R fun x => (c' x : ℝ))
  calc |A - B| ≤ |A - A'| + |A' - B'| + |B' - B| := by
        have := abs_sub_le A A' B
        have := abs_sub_le A' B' B
        linarith
    _ < η / 3 + η / 3 + η / 3 := by
        rw [abs_sub_comm B' B]
        linarith
    _ = η := by ring

/-! ### FS81 Theorem 5.1 in infinite volume -/

/-- **FS81 Theorem 5.1 in infinite volume** (free b.c.). Along any subsequence on which the
characteristic function `Ψ_n(g)` of a finitely supported zero-sum test function converges (all
of them do along the joint limit of `free_thermodynamic_limit_full_exists`), the exponential
moments `⟨e^{φ(g)}⟩_{Λ_n}` converge to `M(g) = e^{κ⟨g,Cg⟩/2} lim Ψ`, and
`exp((1 - δ) κ ⟨g, C g⟩/2) ≤ M(g) ≤ exp(κ ⟨g, C g⟩/2)` (apply to `u g` for (5.4)). -/
theorem free_infinite_expMoment {δ α κ₀ : ℝ} (h5 : FreeExpMomentBoundInternal δ α κ₀)
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {φ : ℕ → ℕ} (hφ : StrictMono φ) {R : ℕ}
    {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) (hg0 : ∑ x ∈ boxInternal R, g x = 0) {m : ℝ}
    (hm : Tendsto (fun k => freeCharFunInternal κ z (φ k) g) atTop (𝓝 m)) :
    Tendsto (fun k => freeExpMomentInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ) κ z
        (fun v => g v.1) 1) atTop
      (𝓝 (Real.exp (κ * wholePlaneQuadInternal R g / 2) * m)) ∧
    Real.exp ((1 - δ) * κ * wholePlaneQuadInternal R g / 2) ≤
      Real.exp (κ * wholePlaneQuadInternal R g / 2) * m ∧
    Real.exp (κ * wholePlaneQuadInternal R g / 2) * m ≤
      Real.exp (κ * wholePlaneQuadInternal R g / 2) := by
  have hev : ∀ᶠ k in atTop, R ≤ φ k := hφ.tendsto_atTop.eventually_ge_atTop R
  have hrep : ∀ k, R ≤ φ k → freeExpMomentInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ) κ z
      (fun v => g v.1) 1 = Real.exp (κ * wholePlaneQuadInternal R g / 2) *
        freeCharFunInternal κ z (φ k) g := fun k hk => by
    rw [freeExpMoment_box_eq, freeQuad_box_eq hk hg]
  have hlim : Tendsto (fun k => freeExpMomentInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ) κ z
      (fun v => g v.1) 1) atTop (𝓝 (Real.exp (κ * wholePlaneQuadInternal R g / 2) * m)) :=
    (hm.const_mul _).congr' (hev.mono fun k hk => (hrep k hk).symm)
  have hm1 : |m| ≤ 1 := le_of_tendsto (continuous_abs.tendsto m |>.comp hm)
    (Eventually.of_forall fun k => abs_freeCharFun_le κ hz (φ k) g)
  refine ⟨hlim, ge_of_tendsto hlim (hev.mono fun k hk => ?_), ?_⟩
  · have hsum : ∑ v : boxInternal (φ k), g v.1 = 0 := by
      rw [Finset.sum_coe_sort (boxInternal (φ k)) g, sum_box_eq_of_supported hk hg, hg0]
    have := h5 (boxInternal (φ k)) κ hκ hκκ₀ z hz hzκ (fun v => g v.1) hsum 1
    rw [freeQuad_box_eq hk hg] at this
    simp only [one_pow, one_mul] at this
    rw [show (1 - δ) * κ * wholePlaneQuadInternal R g / 2 =
      κ * (1 - δ) * wholePlaneQuadInternal R g / 2 by ring]
    exact this
  · have := (abs_le.1 hm1).2
    have hpos := Real.exp_pos (κ * wholePlaneQuadInternal R g / 2)
    nlinarith

/-- **Packaged**: for `0 < δ < 1` and `α` there is `κ₀` such that for `κ > κ₀` and
`0 ≤ z ≤ e^{κ/17 + α}` a joint thermodynamic limit of the free states exists in which the field
and charge two-point functions and **all** exponential moments of finitely supported zero-sum
test functions converge; in every such limit FS81 Theorem 5.1 holds:
`exp((1 - δ) κ ⟨g, C g⟩/2) ≤ lim ⟨e^{φ(g)}⟩_{Λ_n} ≤ exp(κ ⟨g, C g⟩/2)`. -/
theorem free_thermodynamic_limit_expMoment (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ S : ℤ × ℤ → ℤ × ℤ → ℝ,
        (∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (Γ x y))) ∧
        (∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (S x y))) ∧
        ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g → ∑ x ∈ boxInternal R, g x = 0 →
          ∃ M : ℝ, Tendsto (fun k => freeExpMomentInternal
              (Subtype.val : boxInternal (φ k) → ℤ × ℤ) κ z (fun v => g v.1) 1) atTop (𝓝 M) ∧
            Real.exp ((1 - δ) * κ * wholePlaneQuadInternal R g / 2) ≤ M ∧
            M ≤ Real.exp (κ * wholePlaneQuadInternal R g / 2)) := by
  obtain ⟨κ₁, hκ₁, h2⟩ := free_secondMoment_lower_bound δ hδ α
  obtain ⟨κ₂, hκ₂, h5⟩ := free_expMoment_lower_bound δ hδ α
  refine ⟨max κ₁ κ₂, lt_max_of_lt_left hκ₁, fun κ hκ z hz hzκ => ?_⟩
  have hκ1 : κ₁ < κ := lt_of_le_of_lt (le_max_left _ _) hκ
  have hκ2 : κ₂ < κ := lt_of_le_of_lt (le_max_right _ _) hκ
  have hκpos : 0 < κ := hκ₁.trans hκ1
  obtain ⟨φ, hφ, Γ, S, hΓ, hS, hΨ⟩ :=
    free_thermodynamic_limit_full_exists h2 hδ.le hδ1.le κ hκpos hκ1 z hz hzκ
  refine ⟨φ, hφ, Γ, S, hΓ, hS, fun R g hg hg0 => ?_⟩
  obtain ⟨m, hm⟩ := hΨ R g hg hg0
  have := free_infinite_expMoment h5 κ hκpos hκ2 z hz hzκ hφ hg hg0 hm
  exact ⟨_, this.1, this.2.1, this.2.2⟩

end FroehlichSpencer.BKT.Coulomb
