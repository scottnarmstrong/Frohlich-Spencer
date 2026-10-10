/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.FreeGas
public import FroehlichSpencer.BKT.Coulomb.LatticeCalculus
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Thermodynamic limits: FS81 Theorem A in infinite volume and the screening obstruction

FS81 p. 530 ("a thermodynamic limit `Λ ↑ ℤ²` can always be constructed by a compactness
argument"), Theorem A (J p. 532, (1.19)) and the Remarks on J p. 567. Free boundary conditions on
the boxes `Λ_n = [-n, n]²` (`boxInternal n`), FS81's whole-plane potential `C = -a`.

* Finite-volume objects: the charge two-point function `S_n(x,y) = ⟨q(x) q(y)⟩_{Λ_n}`
  (`freeChargeCorrelationInternal`; `q(x) = 0` off the box) and the field two-point function
  `Γ_n(x,y) = ⟨(φ(x)-φ(0))(φ(y)-φ(0))⟩_{Λ_n}` (`freeFieldCorrelationInternal`, the polarized
  free field second moment of the dipoles `δ_x - δ_0`; `0` when `x` or `y` is outside the box).
  For a zero-sum `f` supported in `[-R, R]² ⊆ Λ_n`,
  `⟨φ(f)²⟩_{Λ_n} = ∑_{x,y} f(x) f(y) Γ_n(x,y)` (`freeSecondMoment_box_eq_sum`).
* `free_chargeFluctuation_dirichlet`: `⟨⟨q, g⟩²⟩_Λ ≤ (δ/κ) D(g)` for every test function `g`
  with `Λ ⊇ supp Δg`, from the free bound of `Coulomb/FreeGas.lean` with `f = -Δg` and the
  whole-plane Green identity `C(-Δg) = g`.
* Uniform bounds: `|S_n| ≤ 1` (hard core) and `|Γ_n(x,y)| ≤` a bound independent of `n`
  (positivity of the finite-volume field form from Theorem A with `δ ≤ 1`, and
  `⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩` from positivity of the gas).
* **** `free_thermodynamic_limit_exists`: subsequential limits `Γ`, `S` exist (Tychonoff +
  first countability, `exists_subseq_tendsto_pointwise`).
* **** `free_infinite_theoremA`: for every limit `Γ`, the infinite-volume second moment
  `⟨φ(f)²⟩ = ∑ f(x) f(y) Γ(x,y)` is the limit of the finite-volume second moments and
  `(1 - δ) κ ⟨f, C f⟩ ≤ ⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩` — FS81 Theorem A as stated, in the thermodynamic
  limit.
* ** (test-function form)** `free_infinite_screening`: for every limit `S`,
  `0 ≤ ∑ g(x) g(y) S(x,y) ≤ (δ/κ) D(g)`.
* `free_thermodynamic_limit` packages the three.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology

/-! ### Linearity and positivity of gas expectations -/

section GasLinear

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem gasExpectation_sum (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    {ι : Type*} (s : Finset ι) (F : ι → (V → ℤ) → ℝ) :
    gasExpectationInternal N T κ lam (fun p => ∑ i ∈ s, F i p) =
      ∑ i ∈ s, gasExpectationInternal N T κ lam (F i) := by
  unfold gasExpectationInternal
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem gasExpectation_nonneg (N : ℕ) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ)
    (hlam : ∀ j n, 0 ≤ lam j n) {F : (V → ℤ) → ℝ} (hF : ∀ p, 0 ≤ F p) :
    0 ≤ gasExpectationInternal N T κ lam F := by
  unfold gasExpectationInternal gasPartitionInternal
  have hw : ∀ p, 0 ≤ gasWeightInternal T κ lam p := by
    intro p
    unfold gasWeightInternal
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg fun j _ => hlam j _) (Real.exp_pos _).le
    · exact le_rfl
  exact div_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (hF p))
    (Finset.sum_nonneg fun p _ => hw p)

theorem hardCoreWeight_nonneg {z : ℝ} (hz : 0 ≤ z) (n : ℤ) : 0 ≤ hardCoreWeightInternal z n := by
  unfold hardCoreWeightInternal; split_ifs <;> positivity

end GasLinear

/-! ### Charges and test functions on boxes -/

section Box

/-- The charge at the lattice point `x` of a configuration on the sites `Λ` (zero off `Λ`). -/
def chargeAtInternal {Λ : Finset (ℤ × ℤ)} (p : Λ → ℤ) (x : ℤ × ℤ) : ℝ :=
  ∑ v, if v.1 = x then (p v : ℝ) else 0

theorem sum_chargeAt_mul {Λ : Finset (ℤ × ℤ)} (p : Λ → ℤ) {R : ℕ} {g : ℤ × ℤ → ℝ}
    (hg : SupportedInBox R g) {s : Finset (ℤ × ℤ)} (hs : boxInternal R ⊆ s) :
    ∑ x ∈ s, chargeAtInternal p x * g x = ∑ v, (p v : ℝ) * g v.1 := by
  simp only [chargeAtInternal, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_eq]
  split_ifs with hv
  · rfl
  · rw [hg v.1 fun h => hv (hs h), mul_zero]

/-- The free charge two-point function `⟨q(x) q(y)⟩` in the box `Λ_n = [-n, n]²`. -/
def freeChargeCorrelationInternal (κ z : ℝ) (n : ℕ) (x y : ℤ × ℤ) : ℝ :=
  freeGasExpectationInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ z
    (fun p => chargeAtInternal p x * chargeAtInternal p y)

/-- The charge-fluctuation quadratic form as a double sum of two-point functions. -/
theorem freeGasExpectation_sq_eq_sum {Λ : Finset (ℤ × ℤ)} (κ z : ℝ) {R : ℕ}
    {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    freeGasExpectationInternal (Subtype.val : Λ → ℤ × ℤ) κ z
        (fun p => (∑ v, (p v : ℝ) * g v.1) ^ 2) =
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y *
        freeGasExpectationInternal (Subtype.val : Λ → ℤ × ℤ) κ z
          (fun p => chargeAtInternal p x * chargeAtInternal p y) := by
  have hexp : ∀ p : Λ → ℤ, (∑ v, (p v : ℝ) * g v.1) ^ 2 =
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
        g x * g y * (chargeAtInternal p x * chargeAtInternal p y) := by
    intro p
    rw [← sum_chargeAt_mul p hg subset_rfl, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  simp_rw [hexp]
  unfold freeGasExpectationInternal
  rw [gasExpectation_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [gasExpectation_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact gasExpectation_const_mul _ _ _ _ _ _

/-- **Free-b.c. screening obstruction, Dirichlet form** (/): for `g` supported in
`[-R, R]²` and `Λ ⊇ [-(R+1), R+1]²`, `⟨⟨q, g⟩²⟩_Λ ≤ (δ/κ) D(g)`. -/
theorem free_chargeFluctuation_dirichlet {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (Λ : Finset (ℤ × ℤ)) (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g)
    (hΛ : boxInternal (R + 1) ⊆ Λ) :
    freeGasExpectationInternal (Subtype.val : Λ → ℤ × ℤ) κ z
        (fun p => (∑ v, (p v : ℝ) * g v.1) ^ 2) ≤
      δ / κ * latticeDirichletInternal g := by
  set f : Λ → ℝ := fun v => -latticeLaplacianInternal g v.1 with hfdef
  have hf : ∑ v, f v = 0 := by
    simp only [hfdef, Finset.sum_neg_distrib]
    rw [Finset.sum_coe_sort Λ (fun x => latticeLaplacianInternal g x),
      sum_laplacian_eq_zero hg hΛ, neg_zero]
  have hpot : ∀ v : Λ, -(freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ) f v) = g v.1 := by
    intro v
    rw [freePotentialOp_apply]
    simp only [hfdef, mul_neg, Finset.sum_neg_distrib, neg_neg]
    rw [Finset.sum_coe_sort Λ (fun y => potentialKernelInternal (v.1 - y) *
      latticeLaplacianInternal g y), sum_potentialKernel_mul_laplacian hg hΛ]
  have hQ : freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f = latticeDirichletInternal g := by
    unfold freeQuadInternal
    simp_rw [hpot]
    have hsupp : SupportedInBox R fun x => g x * -(latticeLaplacianInternal g x) :=
      fun x hx => by simp [hg x hx]
    rw [← finsum_mul_neg_laplacian hg, hsupp.finsum_eq_sum
      ((box_mono (Nat.le_succ R)).trans hΛ), ← Finset.sum_coe_sort Λ]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hfdef]
    ring
  have hP : ∀ p, freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) f p =
      ∑ v, (p v : ℝ) * g v.1 := by
    intro p
    unfold freeChargePairingInternal
    simp_rw [hpot]
  have hb := free_chargeFluctuation_le h Λ κ hκ hκκ₀ z hz hzκ f hf
  simp_rw [hP, hQ] at hb
  have hsc : freeGasExpectationInternal (Subtype.val : Λ → ℤ × ℤ) κ z
      (fun p => (κ * ∑ v, (p v : ℝ) * g v.1) ^ 2) =
      κ ^ 2 * freeGasExpectationInternal (Subtype.val : Λ → ℤ × ℤ) κ z
        (fun p => (∑ v, (p v : ℝ) * g v.1) ^ 2) := by
    unfold freeGasExpectationInternal
    rw [← gasExpectation_const_mul]
    congr 1; funext p; ring
  rw [hsc] at hb
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  nlinarith

end Box

/-! ### Compactness -/

/-- **Existence of subsequential limits** for a pointwise bounded sequence of functions on a
countable set (Tychonoff + first countability). -/
theorem exists_subseq_tendsto_pointwise {ι : Type*} [Countable ι] (u : ℕ → ι → ℝ) (B : ι → ℝ)
    (hB : ∀ n i, |u n i| ≤ B i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l : ι → ℝ, ∀ i, Tendsto (fun k => u (φ k) i) atTop (𝓝 (l i)) := by
  have hK : IsCompact (Set.univ.pi fun i => Set.Icc (-B i) (B i)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨l, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := u) fun n =>
    Set.mem_univ_pi.2 fun i => abs_le.1 (hB n i)
  exact ⟨φ, hφ, l, fun i => tendsto_pi_nhds.1 hlim i⟩

/-! ### The free field bilinear form -/

section FieldForm

variable {V : Type*} [Fintype V] [DecidableEq V] (pos : V → ℤ × ℤ) (κ z : ℝ)

/-- The polarized free field second moment `⟨φ(f) φ(g)⟩_Λ = κ ⟨f, C g⟩ - κ² ⟨⟨q,Cf⟩⟨q,Cg⟩⟩_Λ`. -/
def freeFieldFormInternal (f g : V → ℝ) : ℝ :=
  κ * ∑ v, f v * -(freePotentialOpInternal pos g v) -
    freeGasExpectationInternal pos κ z
      (fun p => (κ * freeChargePairingInternal pos f p) * (κ * freeChargePairingInternal pos g p))

theorem freeFieldForm_self (f : V → ℝ) :
    freeFieldFormInternal pos κ z f f = freeSecondMomentInternal pos κ z f := by
  unfold freeFieldFormInternal freeSecondMomentInternal freeQuadInternal
  congr 2
  funext p
  ring

omit [DecidableEq V] in
theorem freeChargePairing_add (f g : V → ℝ) (p : V → ℤ) :
    freeChargePairingInternal pos (f + g) p =
      freeChargePairingInternal pos f p + freeChargePairingInternal pos g p := by
  unfold freeChargePairingInternal
  rw [map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.add_apply]
  ring

omit [DecidableEq V] in
theorem freeChargePairing_smul (c : ℝ) (f : V → ℝ) (p : V → ℤ) :
    freeChargePairingInternal pos (c • f) p = c * freeChargePairingInternal pos f p := by
  unfold freeChargePairingInternal
  rw [map_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq V] in
theorem freeChargePairing_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → V → ℝ)
    (p : V → ℤ) :
    freeChargePairingInternal pos (∑ i ∈ s, c i • F i) p =
      ∑ i ∈ s, c i * freeChargePairingInternal pos (F i) p := by
  unfold freeChargePairingInternal
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  ring

omit [DecidableEq V] in
theorem sum_mul_neg_freePotentialOp_symm (f g : V → ℝ) :
    ∑ v, f v * -(freePotentialOpInternal pos g v) = ∑ v, g v * -(freePotentialOpInternal pos f v) := by
  rw [sum_mul_neg_freePotentialOp, sum_mul_neg_freePotentialOp, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [← potentialKernel_neg, neg_sub]
  ring

theorem freeFieldForm_comm (f g : V → ℝ) :
    freeFieldFormInternal pos κ z f g = freeFieldFormInternal pos κ z g f := by
  unfold freeFieldFormInternal
  rw [sum_mul_neg_freePotentialOp_symm]
  congr 2
  funext p
  ring

/-- Bilinear expansion of the field form along finite linear combinations. -/
theorem freeFieldForm_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → V → ℝ) :
    freeFieldFormInternal pos κ z (∑ i ∈ s, c i • F i) (∑ j ∈ s, c j • F j) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * freeFieldFormInternal pos κ z (F i) (F j) := by
  unfold freeFieldFormInternal
  simp_rw [freeChargePairing_sum_smul]
  have h1 : ∑ v, (∑ i ∈ s, c i • F i) v * -(freePotentialOpInternal pos (∑ j ∈ s, c j • F j) v) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * ∑ v, F i v * -(freePotentialOpInternal pos (F j) v) := by
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have h2 : freeGasExpectationInternal pos κ z (fun p =>
      (κ * ∑ i ∈ s, c i * freeChargePairingInternal pos (F i) p) *
        (κ * ∑ j ∈ s, c j * freeChargePairingInternal pos (F j) p)) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * freeGasExpectationInternal pos κ z (fun p =>
        (κ * freeChargePairingInternal pos (F i) p) * (κ * freeChargePairingInternal pos (F j) p)) := by
    have hexp : ∀ p : V → ℤ, (κ * ∑ i ∈ s, c i * freeChargePairingInternal pos (F i) p) *
        (κ * ∑ j ∈ s, c j * freeChargePairingInternal pos (F j) p) =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * ((κ * freeChargePairingInternal pos (F i) p) *
          (κ * freeChargePairingInternal pos (F j) p)) := by
      intro p
      rw [show ∀ A B : ℝ, (κ * A) * (κ * B) = (A * B) * κ ^ 2 from fun A B => by ring,
        Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hexp]
    unfold freeGasExpectationInternal
    rw [gasExpectation_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gasExpectation_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact gasExpectation_const_mul _ _ _ _ _ _
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end FieldForm

/-! ### Boxes `Λ_n = [-n, n]²`: two-point functions -/

section Boxes

theorem zero_mem_box (n : ℕ) : (0 : ℤ × ℤ) ∈ boxInternal n := by
  rw [mem_box_iff]; simp

/-- The dipole test function `δ_x - δ_0`. -/
def dipoleTestInternal (x u : ℤ × ℤ) : ℝ :=
  (if u = x then 1 else 0) - (if u = 0 then 1 else 0)

/-- `⟨f, C f⟩` for a test function supported in `[-R, R]²`, with FS81's free potential. -/
def wholePlaneQuadInternal (R : ℕ) (f : ℤ × ℤ → ℝ) : ℝ :=
  -∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * potentialKernelInternal (x - y)

/-- The free field two-point function `⟨(φ(x) - φ(0)) (φ(y) - φ(0))⟩_{Λ_n}` (set to `0` when `x`
or `y` lies outside the box, where the field is not defined). -/
def freeFieldCorrelationInternal (κ z : ℝ) (n : ℕ) (x y : ℤ × ℤ) : ℝ :=
  if x ∈ boxInternal n ∧ y ∈ boxInternal n then
    freeFieldFormInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ z
      (fun v => dipoleTestInternal x v.1) (fun v => dipoleTestInternal y v.1)
  else 0

theorem sum_box_eq_of_supported {n R : ℕ} (hRn : R ≤ n) {F : ℤ × ℤ → ℝ}
    (hF : SupportedInBox R F) : ∑ x ∈ boxInternal n, F x = ∑ x ∈ boxInternal R, F x :=
  (Finset.sum_subset (box_mono hRn) fun x _ hx => hF x hx).symm

theorem restrict_eq_sum_dipole {n R : ℕ} {f : ℤ × ℤ → ℝ}
    (hf : SupportedInBox R f) (hf0 : ∑ x ∈ boxInternal R, f x = 0) :
    (fun v : boxInternal n => f v.1) =
      ∑ x ∈ boxInternal R, f x • fun v : boxInternal n => dipoleTestInternal x v.1 := by
  funext v
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dipoleTestInternal, mul_sub,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hf0, zero_mul, sub_zero]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact hf _ h

theorem freeSecondMoment_box_eq_sum (κ z : ℝ) {n R : ℕ} (hRn : R ≤ n) {f : ℤ × ℤ → ℝ}
    (hf : SupportedInBox R f) (hf0 : ∑ x ∈ boxInternal R, f x = 0) :
    freeSecondMomentInternal (Subtype.val : boxInternal n → ℤ × ℤ) κ z (fun v => f v.1) =
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * freeFieldCorrelationInternal κ z n x y := by
  rw [← freeFieldForm_self, restrict_eq_sum_dipole (n := n) hf hf0, freeFieldForm_sum_smul]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [freeFieldCorrelationInternal, ite_eq_left ⟨box_mono hRn hx, box_mono hRn hy⟩]

theorem freeQuad_box_eq {n R : ℕ} (hRn : R ≤ n) {f : ℤ × ℤ → ℝ} (hf : SupportedInBox R f) :
    freeQuadInternal (Subtype.val : boxInternal n → ℤ × ℤ) (fun v => f v.1) =
      wholePlaneQuadInternal R f := by
  unfold freeQuadInternal wholePlaneQuadInternal
  rw [sum_mul_neg_freePotentialOp]
  congr 1
  rw [Finset.sum_coe_sort (boxInternal n) (fun x => ∑ v : boxInternal n,
      f x * f v.1 * potentialKernelInternal (x - v.1))]
  have hin : ∀ x, ∑ v : boxInternal n, f x * f v.1 * potentialKernelInternal (x - v.1) =
      ∑ y ∈ boxInternal R, f x * f y * potentialKernelInternal (x - y) := by
    intro x
    rw [Finset.sum_coe_sort (boxInternal n) (fun y => f x * f y * potentialKernelInternal (x - y))]
    exact sum_box_eq_of_supported hRn (fun y hy => by simp [hf y hy])
  simp_rw [hin]
  exact sum_box_eq_of_supported hRn (fun x hx => by simp [hf x hx])

theorem freeQuad_nonneg {V : Type*} [Fintype V] (pos : V → ℤ × ℤ) (f : V → ℝ)
    (hf : ∑ v, f v = 0) : 0 ≤ freeQuadInternal pos f := by
  refine ge_of_tendsto (tendsto_sum_mul_neg_torusPullbackOp pos f f hf)
    (Eventually.of_forall fun n => ?_)
  rw [sum_mul_neg_torusPullbackOp]
  have h := (squarePeriodic (torusSideInternal n)).pairing_greenOp_nonneg
    (squarePeriodic_connected _ (one_lt_torusSide n))
    (latticePushInternal (torusSideInternal n) pos f) (by rw [sum_latticePush]; exact hf)
  simpa [Multigraph.pairing, torusGreenOpInternal] using h

theorem freeSecondMoment_le {V : Type*} [Fintype V] [DecidableEq V] (pos : V → ℤ × ℤ) (κ : ℝ)
    {z : ℝ} (hz : 0 ≤ z) (f : V → ℝ) :
    freeSecondMomentInternal pos κ z f ≤ κ * freeQuadInternal pos f := by
  unfold freeSecondMomentInternal
  have : 0 ≤ freeGasExpectationInternal pos κ z
      (fun p => (κ * freeChargePairingInternal pos f p) ^ 2) :=
    gasExpectation_nonneg _ _ _ _ (fun _ n => hardCoreWeight_nonneg hz n) fun p => sq_nonneg _
  linarith

theorem freeFieldForm_eq_quarter {V : Type*} [Fintype V] [DecidableEq V] (pos : V → ℤ × ℤ)
    (κ z : ℝ) (F G : V → ℝ) :
    4 * freeFieldFormInternal pos κ z F G =
      freeSecondMomentInternal pos κ z (F + G) - freeSecondMomentInternal pos κ z (F - G) := by
  have hp := freeFieldForm_sum_smul pos κ z (Finset.univ : Finset (Fin 2)) ![1, 1] ![F, G]
  have hm := freeFieldForm_sum_smul pos κ z (Finset.univ : Finset (Fin 2)) ![1, -1] ![F, G]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    neg_smul, one_mul, mul_one, neg_mul, mul_neg, neg_neg] at hp hm
  rw [← freeFieldForm_self, ← freeFieldForm_self, ← sub_eq_add_neg] at *
  rw [hp, hm, freeFieldForm_comm pos κ z G F]
  ring

end Boxes

/-! ### Uniform bounds -/

section Bounds

/-- `max(|x|_∞, |y|_∞)`. -/
def pairRadiusInternal (x y : ℤ × ℤ) : ℕ :=
  max (max x.1.natAbs x.2.natAbs) (max y.1.natAbs y.2.natAbs)

theorem mem_box_of_natAbs_le {x : ℤ × ℤ} {R : ℕ} (h1 : x.1.natAbs ≤ R) (h2 : x.2.natAbs ≤ R) :
    x ∈ boxInternal R := by
  rw [mem_box_iff]
  constructor
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h2

theorem mem_box_pairRadius_left (x y : ℤ × ℤ) : x ∈ boxInternal (pairRadiusInternal x y) :=
  mem_box_of_natAbs_le (by unfold pairRadiusInternal; omega) (by unfold pairRadiusInternal; omega)

theorem mem_box_pairRadius_right (x y : ℤ × ℤ) : y ∈ boxInternal (pairRadiusInternal x y) :=
  mem_box_of_natAbs_le (by unfold pairRadiusInternal; omega) (by unfold pairRadiusInternal; omega)

theorem pairRadius_le {x y : ℤ × ℤ} {n : ℕ} (hx : x ∈ boxInternal n) (hy : y ∈ boxInternal n) :
    pairRadiusInternal x y ≤ n := by
  rw [mem_box_iff] at hx hy
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hx hy
  unfold pairRadiusInternal
  have h1 : x.1.natAbs ≤ n := by exact_mod_cast hx.1
  have h2 : x.2.natAbs ≤ n := by exact_mod_cast hx.2
  have h3 : y.1.natAbs ≤ n := by exact_mod_cast hy.1
  have h4 : y.2.natAbs ≤ n := by exact_mod_cast hy.2
  omega

theorem dipoleTest_supported {x : ℤ × ℤ} {R : ℕ} (hx : x ∈ boxInternal R) :
    SupportedInBox R (dipoleTestInternal x) := by
  intro u hu
  have h1 : u ≠ x := fun h => hu (h ▸ hx)
  have h2 : u ≠ 0 := fun h => hu (h ▸ zero_mem_box R)
  simp [dipoleTestInternal, h1, h2]

theorem sum_dipoleTest_box {x : ℤ × ℤ} {R : ℕ} (hx : x ∈ boxInternal R) :
    ∑ u ∈ boxInternal R, dipoleTestInternal x u = 0 := by
  simp [dipoleTestInternal, Finset.sum_sub_distrib, Finset.sum_ite_eq', hx, zero_mem_box]

theorem wholePlaneQuad_nonneg {R : ℕ} {f : ℤ × ℤ → ℝ} (hf : SupportedInBox R f)
    (hf0 : ∑ x ∈ boxInternal R, f x = 0) : 0 ≤ wholePlaneQuadInternal R f := by
  rw [← freeQuad_box_eq (n := R) le_rfl hf]
  refine freeQuad_nonneg _ _ ?_
  rw [Finset.sum_coe_sort (boxInternal R) f]
  exact hf0

/-- The volume-independent bound on the field two-point function. -/
def fieldCorrelationBoundInternal (κ : ℝ) (x y : ℤ × ℤ) : ℝ :=
  κ * (wholePlaneQuadInternal (pairRadiusInternal x y)
      (fun u => dipoleTestInternal x u + dipoleTestInternal y u) +
    wholePlaneQuadInternal (pairRadiusInternal x y)
      (fun u => dipoleTestInternal x u - dipoleTestInternal y u)) / 4

theorem abs_freeFieldCorrelation_le {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (hδ1 : δ ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) (n : ℕ) (x y : ℤ × ℤ) :
    |freeFieldCorrelationInternal κ z n x y| ≤ fieldCorrelationBoundInternal κ x y := by
  set R := pairRadiusInternal x y
  have hxR := mem_box_pairRadius_left x y
  have hyR := mem_box_pairRadius_right x y
  have hsP : SupportedInBox R (fun u => dipoleTestInternal x u + dipoleTestInternal y u) :=
    (dipoleTest_supported hxR).add (dipoleTest_supported hyR)
  have hsM : SupportedInBox R (fun u => dipoleTestInternal x u - dipoleTestInternal y u) := by
    intro u hu
    simp [dipoleTest_supported hxR u hu, dipoleTest_supported hyR u hu]
  have hzP : ∑ u ∈ boxInternal R, (dipoleTestInternal x u + dipoleTestInternal y u) = 0 := by
    rw [Finset.sum_add_distrib, sum_dipoleTest_box hxR, sum_dipoleTest_box hyR, add_zero]
  have hzM : ∑ u ∈ boxInternal R, (dipoleTestInternal x u - dipoleTestInternal y u) = 0 := by
    rw [Finset.sum_sub_distrib, sum_dipoleTest_box hxR, sum_dipoleTest_box hyR, sub_zero]
  have hQP := wholePlaneQuad_nonneg hsP hzP
  have hQM := wholePlaneQuad_nonneg hsM hzM
  unfold freeFieldCorrelationInternal
  split_ifs with hxy
  · have hRn := pairRadius_le hxy.1 hxy.2
    set F : boxInternal n → ℝ := fun v => dipoleTestInternal x v.1
    set G : boxInternal n → ℝ := fun v => dipoleTestInternal y v.1
    have hsum : ∀ {g : ℤ × ℤ → ℝ}, SupportedInBox R g → ∑ u ∈ boxInternal R, g u = 0 →
        ∑ v : boxInternal n, g v.1 = 0 := by
      intro g hg hg0
      rw [Finset.sum_coe_sort (boxInternal n) g, sum_box_eq_of_supported hRn hg, hg0]
    have hP0 := hsum hsP hzP
    have hM0 := hsum hsM hzM
    have hlowP := h (boxInternal n) κ hκ hκκ₀ z hz hzκ (F + G) hP0
    have hlowM := h (boxInternal n) κ hκ hκκ₀ z hz hzκ (F - G) hM0
    have hupP := freeSecondMoment_le (Subtype.val : boxInternal n → ℤ × ℤ) κ hz (F + G)
    have hupM := freeSecondMoment_le (Subtype.val : boxInternal n → ℤ × ℤ) κ hz (F - G)
    have eP : freeQuadInternal (Subtype.val : boxInternal n → ℤ × ℤ) (F + G) =
        wholePlaneQuadInternal R (fun u => dipoleTestInternal x u + dipoleTestInternal y u) :=
      freeQuad_box_eq hRn hsP
    have eM : freeQuadInternal (Subtype.val : boxInternal n → ℤ × ℤ) (F - G) =
        wholePlaneQuadInternal R (fun u => dipoleTestInternal x u - dipoleTestInternal y u) :=
      freeQuad_box_eq hRn hsM
    rw [eP] at hlowP hupP
    rw [eM] at hlowM hupM
    have h4 := freeFieldForm_eq_quarter (Subtype.val : boxInternal n → ℤ × ℤ) κ z F G
    have hδ' : 0 ≤ 1 - δ := by linarith
    have l1 : 0 ≤ (1 - δ) * κ * wholePlaneQuadInternal R
        (fun u => dipoleTestInternal x u + dipoleTestInternal y u) := by positivity
    have l2 : 0 ≤ (1 - δ) * κ * wholePlaneQuadInternal R
        (fun u => dipoleTestInternal x u - dipoleTestInternal y u) := by positivity
    unfold fieldCorrelationBoundInternal
    rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_zero]
    unfold fieldCorrelationBoundInternal
    positivity

/-- The charge at a site of a hard-core configuration. -/
theorem chargeAt_eq {Λ : Finset (ℤ × ℤ)} (p : Λ → ℤ) (x : ℤ × ℤ) :
    chargeAtInternal p x = if h : x ∈ Λ then (p ⟨x, h⟩ : ℝ) else 0 := by
  unfold chargeAtInternal
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨x, h⟩ (fun v _ hv => by
      rw [ite_eq_right]; exact fun hvx => hv (Subtype.ext hvx)) (by simp)]
    simp
  · exact Finset.sum_eq_zero fun v _ => by rw [ite_eq_right]; exact fun hvx => h (hvx ▸ v.2)

theorem abs_gasExpectation_le {V : Type*} [Fintype V] [DecidableEq V] (N : ℕ)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) (hlam : ∀ j n, 0 ≤ lam j n)
    (hZ : 0 < gasPartitionInternal N T κ lam) {F : (V → ℤ) → ℝ} {B : ℝ}
    (hF : ∀ p ∈ chargeConfigsInternal V N, |F p| ≤ B) :
    |gasExpectationInternal N T κ lam F| ≤ B := by
  have hw : ∀ p, 0 ≤ gasWeightInternal T κ lam p := by
    intro p
    unfold gasWeightInternal
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg fun j _ => hlam j _) (Real.exp_pos _).le
    · exact le_rfl
  unfold gasExpectationInternal
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  calc |∑ p ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam p * F p|
      ≤ ∑ p ∈ chargeConfigsInternal V N, |gasWeightInternal T κ lam p * F p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ chargeConfigsInternal V N, gasWeightInternal T κ lam p * B := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [abs_mul, abs_of_nonneg (hw p)]
        exact mul_le_mul_of_nonneg_left (hF p hp) (hw p)
    _ = B * gasPartitionInternal N T κ lam := by
        rw [gasPartitionInternal, ← Finset.sum_mul, mul_comm]

theorem abs_freeChargeCorrelation_le (κ : ℝ) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) (x y : ℤ × ℤ) :
    |freeChargeCorrelationInternal κ z n x y| ≤ 1 := by
  unfold freeChargeCorrelationInternal freeGasExpectationInternal
  refine abs_gasExpectation_le 1 _ κ _ (fun _ n => hardCoreWeight_nonneg hz n)
    (freeGasPartition_pos _ κ hz) fun p hp => ?_
  simp only [chargeConfigsInternal, Fintype.mem_piFinset, Finset.mem_Icc] at hp
  have hb : ∀ w, |chargeAtInternal p w| ≤ 1 := by
    intro w
    rw [chargeAt_eq]
    split_ifs with hw
    · have := hp ⟨w, hw⟩
      rw [abs_le]
      constructor <;> exact_mod_cast (by omega)
    · simp
  rw [abs_mul]
  calc |chargeAtInternal p x| * |chargeAtInternal p y| ≤ 1 * 1 :=
        mul_le_mul (hb x) (hb y) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end Bounds

/-! ### : existence of thermodynamic limit points (free b.c., boxes `Λ_n = [-n, n]²`) -/

section Limits

/-- **, existence.** Along some subsequence of the boxes `Λ_n`, the free field two-point
functions `Γ_n(x,y) = ⟨(φ(x)-φ(0))(φ(y)-φ(0))⟩_{Λ_n}` and the charge two-point functions
`S_n(x,y) = ⟨q(x) q(y)⟩_{Λ_n}` converge for **every** `x, y ∈ ℤ²` (FS81 p. 530: "a thermodynamic
limit `Λ ↑ ℤ²` can always be constructed by a compactness argument"). No limit is taken before
its existence is proved; nothing is defined by a default value. -/
theorem free_thermodynamic_limit_exists {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (hδ1 : δ ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ S : ℤ × ℤ → ℤ × ℤ → ℝ,
      (∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop (𝓝 (Γ x y))) ∧
      (∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
        (𝓝 (S x y))) := by
  obtain ⟨φ, hφ, l, hl⟩ := exists_subseq_tendsto_pointwise
    (ι := Bool × (ℤ × ℤ) × (ℤ × ℤ))
    (fun n i => if i.1 then freeFieldCorrelationInternal κ z n i.2.1 i.2.2
      else freeChargeCorrelationInternal κ z n i.2.1 i.2.2)
    (fun i => if i.1 then fieldCorrelationBoundInternal κ i.2.1 i.2.2 else 1)
    (fun n i => by
      rcases i with ⟨b, x, y⟩
      cases b
      · exact abs_freeChargeCorrelation_le κ hz n x y
      · exact abs_freeFieldCorrelation_le h hδ1 κ hκ hκκ₀ z hz hzκ n x y)
  exact ⟨φ, hφ, fun x y => l (true, x, y), fun x y => l (false, x, y),
    fun x y => by simpa using hl (true, x, y), fun x y => by simpa using hl (false, x, y)⟩

/-- ** FS81 Theorem A in infinite volume** (J p. 532, (1.19), `c₁ = (1 - δ) κ`). Along any
thermodynamic limit of the free field two-point functions, the infinite-volume second moment
`⟨φ(f)²⟩ = ∑_{x,y} f(x) f(y) Γ(x,y)` of every finitely supported zero-sum `f` is the limit of
the finite-volume sine-Gordon second moments, and
`(1 - δ) κ ⟨f, C f⟩ ≤ ⟨φ(f)²⟩ ≤ κ ⟨f, C f⟩` with FS81's whole-plane potential `C = -a`. -/
theorem free_infinite_theoremA {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {Γ : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hΓ : ∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop (𝓝 (Γ x y)))
    {R : ℕ} {f : ℤ × ℤ → ℝ} (hf : SupportedInBox R f) (hf0 : ∑ x ∈ boxInternal R, f x = 0) :
    Tendsto (fun k => freeSecondMomentInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ) κ z
        (fun v => f v.1)) atTop
      (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y)) ∧
    (1 - δ) * κ * wholePlaneQuadInternal R f ≤
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ∧
    ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ≤
      κ * wholePlaneQuadInternal R f := by
  have hev : ∀ᶠ k in atTop, R ≤ φ k := hφ.tendsto_atTop.eventually_ge_atTop R
  have hlim : Tendsto (fun k => freeSecondMomentInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ)
      κ z (fun v => f v.1)) atTop
      (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y)) := by
    refine Tendsto.congr' ?_ (tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ =>
      (hΓ x y).const_mul (f x * f y))
    filter_upwards [hev] with k hk
    exact (freeSecondMoment_box_eq_sum κ z hk hf hf0).symm
  have hsum : ∀ k, R ≤ φ k → ∑ v : boxInternal (φ k), f v.1 = 0 := fun k hk => by
    rw [Finset.sum_coe_sort (boxInternal (φ k)) f, sum_box_eq_of_supported hk hf, hf0]
  refine ⟨hlim, ge_of_tendsto hlim ?_, le_of_tendsto hlim ?_⟩
  · filter_upwards [hev] with k hk
    have := h (boxInternal (φ k)) κ hκ hκκ₀ z hz hzκ (fun v => f v.1) (hsum k hk)
    rwa [freeQuad_box_eq hk hf] at this
  · filter_upwards [hev] with k hk
    have := freeSecondMoment_le (Subtype.val : boxInternal (φ k) → ℤ × ℤ) κ hz (fun v => f v.1)
    rwa [freeQuad_box_eq hk hf] at this

/-- ** (test-function form): the screening obstruction in infinite volume.** Along any
thermodynamic limit `S` of the free charge two-point functions, for every finitely supported
test function `g`, `0 ≤ ∑_{x,y} g(x) g(y) S(x,y) ≤ (δ/κ) ∑_{edges} (g_x - g_y)²`. Debye
screening would make the middle term `≈ κ⁻¹ D(g)` for slowly varying `g`. -/
theorem free_infinite_screening {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {S : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hS : ∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
      (𝓝 (S x y)))
    {R : ℕ} {g : ℤ × ℤ → ℝ} (hg : SupportedInBox R g) :
    0 ≤ ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * S x y ∧
      ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * S x y ≤
        δ / κ * latticeDirichletInternal g := by
  have hev : ∀ᶠ k in atTop, R + 1 ≤ φ k := hφ.tendsto_atTop.eventually_ge_atTop (R + 1)
  have hlim : Tendsto (fun k => ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
      g x * g y * freeChargeCorrelationInternal κ z (φ k) x y) atTop
      (𝓝 (∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * S x y)) :=
    tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => (hS x y).const_mul _
  have hrep : ∀ k, ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R,
      g x * g y * freeChargeCorrelationInternal κ z (φ k) x y =
      freeGasExpectationInternal (Subtype.val : boxInternal (φ k) → ℤ × ℤ) κ z
        (fun p => (∑ v, (p v : ℝ) * g v.1) ^ 2) := fun k =>
    (freeGasExpectation_sq_eq_sum κ z hg).symm
  refine ⟨ge_of_tendsto hlim (Eventually.of_forall fun k => ?_), le_of_tendsto hlim ?_⟩
  · rw [hrep]
    exact gasExpectation_nonneg _ _ _ _ (fun _ n => hardCoreWeight_nonneg hz n)
      fun p => sq_nonneg _
  · filter_upwards [hev] with k hk
    rw [hrep]
    exact free_chargeFluctuation_dirichlet h _ κ hκ hκκ₀ z hz hzκ hg (box_mono hk)

end Limits

/-- ** +  + , packaged** (free boundary conditions, boxes `Λ_n = [-n, n]²`): for
`0 < δ < 1` and `α` there is `κ₀`, such that for `κ > κ₀` and `0 ≤ z ≤ e^{κ/17 + α}`
thermodynamic limit points of the field and charge two-point functions exist, every field limit
satisfies FS81 Theorem A in infinite volume, and every charge limit satisfies the
test-function screening obstruction. -/
theorem free_thermodynamic_limit (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ S : ℤ × ℤ → ℤ × ℤ → ℝ,
        (∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (Γ x y))) ∧
        (∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (S x y)))) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ Γ : ℤ × ℤ → ℤ × ℤ → ℝ,
        (∀ x y, Tendsto (fun k => freeFieldCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (Γ x y))) →
        ∀ (R : ℕ) (f : ℤ × ℤ → ℝ), SupportedInBox R f → ∑ x ∈ boxInternal R, f x = 0 →
          (1 - δ) * κ * wholePlaneQuadInternal R f ≤
            ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ∧
          ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, f x * f y * Γ x y ≤
            κ * wholePlaneQuadInternal R f) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ S : ℤ × ℤ → ℤ × ℤ → ℝ,
        (∀ x y, Tendsto (fun k => freeChargeCorrelationInternal κ z (φ k) x y) atTop
          (𝓝 (S x y))) →
        ∀ (R : ℕ) (g : ℤ × ℤ → ℝ), SupportedInBox R g →
          0 ≤ ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * S x y ∧
          ∑ x ∈ boxInternal R, ∑ y ∈ boxInternal R, g x * g y * S x y ≤
            δ / κ * latticeDirichletInternal g) := by
  obtain ⟨κ₀, hκ₀, h⟩ := free_secondMoment_lower_bound δ hδ α
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ z hz hzκ => ?_⟩
  have hκ : 0 < κ := hκ₀.trans hκκ₀
  refine ⟨free_thermodynamic_limit_exists h hδ1.le κ hκ hκκ₀ z hz hzκ,
    fun φ hφ Γ hΓ R f hf hf0 => ?_, fun φ hφ S hS R g hg =>
      free_infinite_screening h κ hκ hκκ₀ z hz hzκ hφ hS hg⟩
  have := free_infinite_theoremA h κ hκ hκκ₀ z hz hzκ hφ hΓ hf hf0
  exact ⟨this.2.1, this.2.2⟩

end FroehlichSpencer.BKT.Coulomb
