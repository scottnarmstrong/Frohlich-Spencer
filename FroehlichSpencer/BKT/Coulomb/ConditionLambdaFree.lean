/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.FreeGas
public import FroehlichSpencer.BKT.Coulomb.ConditionLambda
import Mathlib.Tactic

/-!
# General Condition-λ gases with FS81's free boundary condition

FS81 §5.2 (J pp. 570–572) for the gas of FS81 p. 529 (i): charges on a finite `Λ ⊂ ℤ²` with the
**whole-plane** potential `C = -a` (`freePotentialOpInternal`), a single even charge weight `λ`
satisfying Condition λ (`ConditionLambdaInternal`, `Coulomb/ConditionLambda.lean`), signed
weights allowed.

* `conditionLambda_hardCore`: the hard-core activity family of FS81 Theorem 5.1 is a
  Condition-λ family (`C = max 1 (e^α/2)`, `α' = 0`, `ε = 1/17`), uniformly in `z`.
* `CutoffBoundInternal.pullback`, `cutoffSumBound_of_tendsto`: the cutoff bounds transport to
  sub-lattices and pass to limits of potentials.
* `free_chargeEnergy_ge`: FS81's free neutral energy is coercive, `E(q) ≥ ‖q‖²/16` (limit of
  the periodic squares).
* **`free_conditionLambda_bound`**: for `δ > 0` and `(C, α, ε)` with `ε < 1/16` there is `κ₀`,
  independent of `Λ`, such that for `κ > κ₀` FS81 Theorems 5.1 and A hold at every frequency
  cutoff (multiplied by `Z_N`) and **without cutoff** (`FullBoundInternal`: gate, `Z_N → Z ≥ 0`,
  inequalities multiplied by `Z`).
* `free_conditionLambda_physical`: for physical `λ` (`λ ≥ 0`, `λ(0) = 1`): `Z ≥ 1`,
  `⟨e^{u φ(f)}⟩_Λ ≥ exp (u² κ (1 - δ) ⟨f, C f⟩/2)` and
  `(1 - δ) κ ⟨f, C f⟩ ≤ ⟨φ(f)²⟩_Λ ≤ κ ⟨f, C f⟩`.
* `tendsto_torus_cutoff_expMoment`, `tendsto_torus_cutoff_secondMoment`,
  `tendsto_free_cutoff_moments`: the free functionals (defined by the representation formulas)
  are iterated limits, periodic volume `n → ∞` then cutoff `N → ∞`, of genuine sine-Gordon field
  functionals.

The order of limits is: square bounds at cutoff `N` ( KP T1.5) → periodic limit `n → ∞` at
fixed `N` (finite sums) → cutoff removal `N → ∞` (gate).

No pointwise Fourier series of `λ̂` and
no printed (5.39) inequality is used .
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology

/-- **Consistency with the neutral gas:** the hard-core weights of FS81 Theorem 5.1's activity range
`0 ≤ z ≤ e^{κ/17 + α}` satisfy Condition λ with `C = max 1 (e^α/2)`, `α' = 0`, `ε = 1/17`,
uniformly in `z`, and are physical; so `free_conditionLambda_bound` contains the hard-core
results of `Coulomb/FreeGas.lean` (for `κ` above a possibly larger threshold). -/
theorem conditionLambda_hardCore {α κ z : ℝ} (hz : 0 ≤ z) (hzκ : z ≤ Real.exp (κ / 17 + α)) :
    ConditionLambdaInternal (max 1 (Real.exp α / 2)) 0 (1 / 17) κ (hardCoreWeightInternal z) ∧
      PhysicalWeightInternal (hardCoreWeightInternal z) := by
  refine ⟨⟨hardCoreWeight_neg z, fun n => ?_⟩, by simp [hardCoreWeightInternal], fun n => ?_⟩
  · unfold hardCoreWeightInternal
    split_ifs with h0 h1
    · subst h0
      simp
    · have hn : (n : ℝ) ^ 2 = 1 := by rcases h1 with rfl | rfl <;> norm_num
      rw [hn, abs_of_nonneg (by positivity), mul_one, zero_add]
      have hexp : z / 2 ≤ Real.exp α / 2 * Real.exp (1 / 17 * κ) := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        have : κ / 17 + α = α + 1 / 17 * κ := by ring
        rw [this] at hzκ
        linarith
      exact hexp.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    · simp only [abs_zero]
      exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le
  · unfold hardCoreWeightInternal
    split_ifs <;> positivity

section Transport

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The cutoff bounds transport from a domain `W`, with charges confined to the image of an
injective `e : V → W`, to the gas on `V` with the pulled-back potential. -/
theorem CutoffBoundInternal.pullback {e : V → W} (he : Function.Injective e) {N : ℕ}
    {T : (W → ℝ) →ₗ[ℝ] W → ℝ} {κ δ : ℝ} {lam : ℤ → ℝ}
    (h : CutoffBoundInternal N T κ δ (regionWeightInternal (Finset.univ.image e) lam)) :
    CutoffBoundInternal N (pullbackOpInternal T e) κ δ (fun _ => lam) := by
  obtain ⟨hZ, hf⟩ := h
  refine ⟨by rwa [← gasPartition_region_eq he], fun f hf0 => ?_⟩
  have hF : ∑ w, pushRealInternal e f w = 0 := by
    have := sum_pushReal_mul e f (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hf0]
  obtain ⟨hcos, hsq⟩ := hf (pushRealInternal e f) hF
  have hQ : ∑ w, pushRealInternal e f w * -(T (pushRealInternal e f) w) =
      ∑ v, f v * -(pullbackOpInternal T e f v) := by
    rw [sum_pushReal_mul]; rfl
  have hX : ∀ p : V → ℤ, ∑ w, (extendConfigInternal e p w : ℝ) * -(T (pushRealInternal e f) w) =
      ∑ v, (p v : ℝ) * -(pullbackOpInternal T e f v) := by
    intro p; rw [sum_extendConfig_mul]; rfl
  refine ⟨fun u => ?_, ?_⟩
  · have := hcos u
    rw [gasExpectation_region_eq he, hQ] at this
    simpa only [hX] using this
  · have := hsq
    rw [gasExpectation_region_eq he, hQ] at this
    simpa only [hX] using this

end Transport

section Limit

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The multiplied cutoff bounds pass to limits of potentials that converge on neutral data. -/
theorem cutoffSumBound_of_tendsto (N : ℕ) (Tn : ℕ → (V → ℝ) →ₗ[ℝ] V → ℝ)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ δ : ℝ) (lam : V → ℤ → ℝ)
    (hE : ∀ p : V → ℤ, ∑ j, p j = 0 →
      Tendsto (fun n => chargeEnergyInternal (Tn n) p) atTop (𝓝 (chargeEnergyInternal T p)))
    (hpair : ∀ g f : V → ℝ, ∑ v, f v = 0 →
      Tendsto (fun n => ∑ v, g v * -(Tn n f v)) atTop (𝓝 (∑ v, g v * -(T f v))))
    (h : ∀ᶠ n in atTop, CutoffSumBoundInternal N (Tn n) κ δ lam) :
    CutoffSumBoundInternal N T κ δ lam := by
  have hw : ∀ p, Tendsto (fun n => gasWeightInternal (Tn n) κ lam p) atTop
      (𝓝 (gasWeightInternal T κ lam p)) := by
    intro p
    unfold gasWeightInternal
    split_ifs with hp
    · exact tendsto_const_nhds.mul
        ((Real.continuous_exp.tendsto _).comp ((hE p hp).const_mul (-κ)))
    · exact tendsto_const_nhds
  have hZ : Tendsto (fun n => gasPartitionInternal N (Tn n) κ lam) atTop
      (𝓝 (gasPartitionInternal N T κ lam)) :=
    tendsto_finsetSum _ fun p _ => hw p
  refine ⟨ge_of_tendsto hZ (h.mono fun n hn => hn.1), fun f hf => ⟨fun u => ?_, ?_⟩⟩
  · have hQ := hpair f f hf
    have hX : ∀ p : V → ℤ, Tendsto (fun n => ∑ j, (p j : ℝ) * -(Tn n f j)) atTop
        (𝓝 (∑ j, (p j : ℝ) * -(T f j))) := fun p => hpair _ f hf
    refine le_of_tendsto_of_tendsto
      ((((Real.continuous_exp.tendsto _).comp
        (((hQ.const_mul (δ * κ)).div_const 2).neg.mul_const (u ^ 2))).mul hZ))
      (tendsto_finsetSum _ fun p _ => (hw p).mul
        ((Real.continuous_cos.tendsto _).comp (((hX p).const_mul κ).const_mul u)))
      (h.mono fun n hn => ?_)
    exact (hn.2 f hf).1 u
  · have hQ := hpair f f hf
    have hX : ∀ p : V → ℤ, Tendsto (fun n => ∑ j, (p j : ℝ) * -(Tn n f j)) atTop
        (𝓝 (∑ j, (p j : ℝ) * -(T f j))) := fun p => hpair _ f hf
    refine le_of_tendsto_of_tendsto
      (tendsto_finsetSum _ fun p _ => (hw p).mul (((hX p).const_mul κ).pow 2))
      ((hQ.const_mul (δ * κ)).mul hZ) (h.mono fun n hn => (hn.2 f hf).2)

end Limit

section Free

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **FS81's free neutral energy is coercive**: `E(q) ≥ ‖q‖²/16` for every neutral `q` on a finite
set of distinct lattice points, with the whole-plane potential `C = -a` (limit of the periodic
squares, where `chargeEnergy_ge_of_degree` applies). -/
theorem free_chargeEnergy_ge (pos : V → ℤ × ℤ) (hpos : Function.Injective pos) (p : V → ℤ)
    (hp : ∑ j, p j = 0) :
    (∑ j, (p j : ℝ) ^ 2) / 16 ≤ chargeEnergyInternal (freePotentialOpInternal pos) p := by
  refine ge_of_tendsto (tendsto_chargeEnergy_torusPullbackOp pos p hp) ?_
  filter_upwards [eventually_injective_latticeToSquare pos hpos] with n hinj
  have hinj' : Function.Injective (torusSiteMapInternal pos n) := hinj
  have hsq : ∑ w, (extendConfigInternal (torusSiteMapInternal pos n) p w : ℝ) ^ 2 =
      ∑ j, (p j : ℝ) ^ 2 := by
    have := sum_extendConfig_mul (torusSiteMapInternal pos n) p
      (fun w => (extendConfigInternal (torusSiteMapInternal pos n) p w : ℝ))
    simp only [extendConfig_apply hinj'] at this
    simpa only [sq] using this
  rw [torusPullbackOpInternal, ← chargeEnergy_extendConfig, ← hsq]
  exact chargeEnergy_ge_of_degree _ (squarePeriodic_connected _ (one_lt_torusSide n))
    (SpinWaves.squarePeriodicBipartiteDegreeFour _ (even_torusSide n)
      (one_lt_torusSide n)).endpointDegree_le_four
    (torusGreenOpInternal n) (isLaplacianPseudoinverse_torusGreenOp n) _
    (by rw [sum_extendConfig]; exact hp)

/-- The cutoff sine-Gordon weights on `Λ_{L_n}^per` with charges (weight `λ`, cutoff `N`) confined
to the image of the sites. -/
abbrev torusCutoffWeightsInternal (pos : V → ℤ × ℤ) (n N : ℕ) (lam : ℤ → ℝ) :
    Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℝ → ℝ :=
  fun j => sineGordonWeightInternal N
    (regionWeightInternal (Finset.univ.image (torusSiteMapInternal pos n)) lam j)

theorem torus_cutoff_gasExpectation_eq (pos : V → ℤ × ℤ) (n : ℕ)
    (hinj : Function.Injective (torusSiteMapInternal pos n)) (N : ℕ) (κ : ℝ) (lam : ℤ → ℝ)
    (Φ : ℝ → ℝ) (f : V → ℝ) :
    gasExpectationInternal N (torusGreenOpInternal n) κ
        (regionWeightInternal (Finset.univ.image (torusSiteMapInternal pos n)) lam)
        (fun q => Φ (∑ j, (q j : ℝ) *
          -(torusGreenOpInternal n (latticePushInternal (torusSideInternal n) pos f) j))) =
      gasExpectationInternal N (torusPullbackOpInternal pos n) κ (fun _ => lam)
        (fun p => Φ (∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v))) := by
  rw [gasExpectation_region_eq hinj]
  congr 1
  funext p
  congr 1
  rw [sum_extendConfig_mul]
  rfl

/-- The free-b.c. cutoff sine-Gordon functional `e^{κ⟨f,Cf⟩u²/2} ⟨cos (u κ ⟨q, C f⟩)⟩_N`. -/
def freeCutoffExpMomentInternal (pos : V → ℤ × ℤ) (N : ℕ) (κ : ℝ) (lam : ℤ → ℝ) (f : V → ℝ)
    (u : ℝ) : ℝ :=
  Real.exp (κ * freeQuadInternal pos f / 2 * u ^ 2) *
    gasExpectationInternal N (freePotentialOpInternal pos) κ (fun _ => lam)
      (fun p => Real.cos (u * (κ * freeChargePairingInternal pos f p)))

/-- The free-b.c. cutoff field second moment `κ⟨f,Cf⟩ - ⟨(κ ⟨q, C f⟩)²⟩_N`. -/
def freeCutoffSecondMomentInternal (pos : V → ℤ × ℤ) (N : ℕ) (κ : ℝ) (lam : ℤ → ℝ)
    (f : V → ℝ) : ℝ :=
  κ * freeQuadInternal pos f -
    gasExpectationInternal N (freePotentialOpInternal pos) κ (fun _ => lam)
      (fun p => (κ * freeChargePairingInternal pos f p) ^ 2)

/-- **The free cutoff functional is the periodic thermodynamic limit** of genuine sine-Gordon field
functionals on `Λ_{L_n}^per` (FS81 p. 531, `dμ_κ = lim dμ_{κ,Ω}`), for every cutoff `N` with
`Z_N ≠ 0` (e.g. physical weights). -/
theorem tendsto_torus_cutoff_expMoment (pos : V → ℤ × ℤ) (hpos : Function.Injective pos) (κ : ℝ)
    (hκ : 0 < κ) (N : ℕ) (lam : ℤ → ℝ) (hev : ∀ n, lam (-n) = lam n)
    (hZ : gasPartitionInternal N (freePotentialOpInternal pos) κ (fun _ => lam) ≠ 0)
    (f : V → ℝ) (hf : ∑ v, f v = 0) (u : ℝ)
    (root : ∀ n, Fin (torusSideInternal n) × Fin (torusSideInternal n)) :
    Tendsto (fun n => weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusCutoffWeightsInternal pos n N lam)
        (fun φ => Real.exp (u * ∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j)))
      atTop (𝓝 (freeCutoffExpMomentInternal pos N κ lam f u)) := by
  have hrep : ∀ᶠ n in atTop,
      Real.exp (κ * (∑ v, f v * -(torusPullbackOpInternal pos n f v)) / 2 * u ^ 2) *
        gasExpectationInternal N (torusPullbackOpInternal pos n) κ (fun _ => lam)
          (fun p => Real.cos (u * (κ * ∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v)))) =
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusCutoffWeightsInternal pos n N lam)
        (fun φ => Real.exp (u * ∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j)) := by
    filter_upwards [eventually_injective_latticeToSquare pos hpos] with n hinj
    rw [weightedGFFExpectation_exp_mul_sineGordon (squarePeriodic (torusSideInternal n))
      (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n) N _
      (regionWeight_neg _ hev) (torusGreenOpInternal n)
      (isLaplacianPseudoinverse_torusGreenOp n) (latticePushInternal (torusSideInternal n) pos f)
      (by rw [sum_latticePush]; exact hf) u,
      torus_cutoff_gasExpectation_eq pos n hinj N κ lam (fun x => Real.cos (u * (κ * x))) f,
      ← sum_mul_neg_torusPullbackOp]
  refine Tendsto.congr' hrep ?_
  unfold freeCutoffExpMomentInternal freeQuadInternal freeChargePairingInternal
  refine Tendsto.mul ((Real.continuous_exp.tendsto _).comp
    ((((tendsto_sum_mul_neg_torusPullbackOp pos f f hf).const_mul κ).div_const 2).mul_const _)) ?_
  refine tendsto_gasExpectation_of_tendsto N _ _ κ _ _ _
    (fun p hp => tendsto_chargeEnergy_torusPullbackOp pos p hp) (fun p => ?_) hZ
  exact (Real.continuous_cos.tendsto _).comp
    (((tendsto_sum_mul_neg_torusPullbackOp pos _ f hf).const_mul κ).const_mul u)

/-- **The free cutoff second moment is the periodic thermodynamic limit** of the sine-Gordon
second moments on `Λ_{L_n}^per`, for physical weights. -/
theorem tendsto_torus_cutoff_secondMoment (pos : V → ℤ × ℤ) (hpos : Function.Injective pos)
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (lam : ℤ → ℝ) (hev : ∀ n, lam (-n) = lam n)
    (hphys : PhysicalWeightInternal lam) (f : V → ℝ) (hf : ∑ v, f v = 0)
    (root : ∀ n, Fin (torusSideInternal n) × Fin (torusSideInternal n)) :
    Tendsto (fun n => weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusCutoffWeightsInternal pos n N lam)
        (fun φ => (∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j) ^ 2))
      atTop (𝓝 (freeCutoffSecondMomentInternal pos N κ lam f)) := by
  have hrep : ∀ᶠ n in atTop,
      κ * (∑ v, f v * -(torusPullbackOpInternal pos n f v)) -
        gasExpectationInternal N (torusPullbackOpInternal pos n) κ (fun _ => lam)
          (fun p => (κ * ∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v)) ^ 2) =
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusCutoffWeightsInternal pos n N lam)
        (fun φ => (∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j) ^ 2) := by
    filter_upwards [eventually_injective_latticeToSquare pos hpos] with n hinj
    have hZn : gasPartitionInternal N (torusGreenOpInternal n) κ
        (regionWeightInternal (Finset.univ.image (torusSiteMapInternal pos n)) lam) ≠ 0 :=
      (gasPartition_pos N _ κ _ (regionWeight_nonneg _ hphys.2)
        (fun j => by rw [regionWeight_zero _ hphys.1]; exact one_pos)).ne'
    rw [weightedGFFExpectation_sq_sineGordon (squarePeriodic (torusSideInternal n))
      (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n) N _
      (regionWeight_neg _ hev) (torusGreenOpInternal n)
      (isLaplacianPseudoinverse_torusGreenOp n) (latticePushInternal (torusSideInternal n) pos f)
      (by rw [sum_latticePush]; exact hf) hZn,
      torus_cutoff_gasExpectation_eq pos n hinj N κ lam (fun x => (κ * x) ^ 2) f,
      ← sum_mul_neg_torusPullbackOp]
  refine Tendsto.congr' hrep ?_
  unfold freeCutoffSecondMomentInternal freeQuadInternal freeChargePairingInternal
  refine ((tendsto_sum_mul_neg_torusPullbackOp pos f f hf).const_mul κ).sub ?_
  refine tendsto_gasExpectation_of_tendsto N _ _ κ _ _ _
    (fun p hp => tendsto_chargeEnergy_torusPullbackOp pos p hp) (fun p => ?_)
    (gasPartition_pos N _ κ _ (fun _ => hphys.2) (fun _ => by rw [hphys.1]; exact one_pos)).ne'
  exact ((tendsto_sum_mul_neg_torusPullbackOp pos _ f hf).const_mul κ).pow 2

/-- Removing the cutoff in the free functionals: `freeCutoffExpMomentInternal → fullExpMomentInternal`
and `freeCutoffSecondMomentInternal → fullSecondMomentInternal` as `N → ∞`, given the gate and
`Z ≠ 0`. Together with `tendsto_torus_cutoff_expMoment` and `tendsto_torus_cutoff_secondMoment`
this identifies the free Condition-λ functionals as iterated limits (`n → ∞`, then `N → ∞`) of
sine-Gordon field functionals. -/
theorem tendsto_free_cutoff_moments (pos : V → ℤ × ℤ) (κ : ℝ) (lam : ℤ → ℝ)
    (h : GateInternal (freePotentialOpInternal pos) κ (fun _ => lam))
    (hZ : fullGasPartitionInternal (freePotentialOpInternal pos) κ (fun _ => lam) ≠ 0)
    (f : V → ℝ) (u : ℝ) :
    Tendsto (fun N => freeCutoffExpMomentInternal pos N κ lam f u) atTop
        (𝓝 (fullExpMomentInternal (freePotentialOpInternal pos) κ (fun _ => lam) f u)) ∧
      Tendsto (fun N => freeCutoffSecondMomentInternal pos N κ lam f) atTop
        (𝓝 (fullSecondMomentInternal (freePotentialOpInternal pos) κ (fun _ => lam) f)) := by
  refine ⟨tendsto_const_nhds.mul
    (tendsto_gasExpectation_cutoff h hZ _ 1 fun q => abs_cos_le_quadratic _ q),
    tendsto_const_nhds.sub (tendsto_gasExpectation_cutoff h hZ _ _
      fun q => abs_sq_pairing_le_quadratic κ (fun j => -(freePotentialOpInternal pos f j)) q)⟩

end Free

/-- FS81 Theorems 5.1 and A for the general Condition-λ gas with **free boundary conditions**
(FS81's whole-plane potential, p. 529 (i)) on every finite `Λ ⊂ ℤ²`, threshold `κ₀`: for
`κ > κ₀` and every normalized Condition-λ weight `λ` (constants `C, α, ε`, signed allowed),
the bounds hold at every frequency cutoff (`CutoffSumBoundInternal`) and without cutoff
(`FullBoundInternal`). -/
def FreeConditionLambdaBoundInternal (δ C α ε κ₀ : ℝ) : Prop :=
  ∀ (Λ : Finset (ℤ × ℤ)) (κ : ℝ), κ₀ < κ → ∀ lam : ℤ → ℝ, ConditionLambdaInternal C α ε κ lam →
    lam 0 = 1 →
      (∀ N, CutoffSumBoundInternal N (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ δ
        (fun _ => lam)) ∧
      FullBoundInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ δ (fun _ => lam)

/-- **FS81 Theorems 5.1 and A for general Condition-λ gases, free b.c.** (J pp. 570–572 with
p. 529 (i)): for `δ > 0` and `(C, α, ε)` with `ε < 1/16` there is `κ₀`, independent of `Λ`, with
`FreeConditionLambdaBoundInternal δ C α ε κ₀`. The cutoff bounds are periodic-square limits of
`conditionLambda_cutoff_bound` (applied with constant `max 1 C` to the region weights); the
cutoff is then removed by the gate with `free_chargeEnergy_ge`. -/
theorem free_conditionLambda_bound (δ : ℝ) (hδ : 0 < δ) (C α ε : ℝ) (hε : ε < 1 / 16) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ FreeConditionLambdaBoundInternal δ C α ε κ₀ := by
  obtain ⟨κ₁, hκ₁, hcut⟩ := conditionLambda_cutoff_bound δ hδ (max 1 C) α ε hε
  have hd : 0 < 1 / 16 - ε := by linarith
  refine ⟨max κ₁ (α / (1 / 16 - ε)), lt_max_of_lt_left hκ₁, fun Λ κ hκ lam hlam h0 => ?_⟩
  have hκ1 : κ₁ < κ := (le_max_left _ _).trans_lt hκ
  have hκα : α < κ * (1 / 16 - ε) := (div_lt_iff₀ hd).1 ((le_max_right _ _).trans_lt hκ)
  have hκ0 : 0 ≤ κ := (hκ₁.trans hκ1).le
  have hN : ∀ N, CutoffSumBoundInternal N (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ δ
      (fun _ => lam) := by
    intro N
    refine cutoffSumBound_of_tendsto N
      (fun n => torusPullbackOpInternal (Subtype.val : Λ → ℤ × ℤ) n) _ κ δ _
      (fun p hp => tendsto_chargeEnergy_torusPullbackOp _ p hp)
      (fun g f hf => tendsto_sum_mul_neg_torusPullbackOp _ g f hf) ?_
    filter_upwards [eventually_injective_latticeToSquare (Subtype.val : Λ → ℤ × ℤ)
      Subtype.val_injective] with n hinj
    have hinj' : Function.Injective (torusSiteMapInternal (Subtype.val : Λ → ℤ × ℤ) n) := hinj
    exact (CutoffBoundInternal.pullback hinj'
      (((hcut _ (one_lt_torusSide n)).2 (even_torusSide n)) κ hκ1 _
        (fun j => conditionLambda_regionWeight _ hlam j) (fun j => regionWeight_zero _ h0 j) N _
        (isLaplacianPseudoinverse_torusGreenOp n))).toSum
  exact ⟨hN, fullBound_of_cutoffSum (gate_of_conditionLambda hκ0 (fun _ => hlam)
    (fun q hq => free_chargeEnergy_ge (Subtype.val : Λ → ℤ × ℤ) Subtype.val_injective q hq) hκα)
    hN⟩

/-- **Physical Condition-λ gases with free b.c.** (`λ ≥ 0`, `λ(0) = 1`): `Z ≥ 1`, FS81 Theorem 5.1
`⟨e^{u φ(f)}⟩_Λ ≥ exp (u² κ (1 - δ) ⟨f, C f⟩/2)` and FS81 Theorem A
`(1 - δ) κ ⟨f, C f⟩ ≤ ⟨φ(f)²⟩_Λ ≤ κ ⟨f, C f⟩`, without frequency cutoff. -/
theorem free_conditionLambda_physical {δ C α ε κ₀ : ℝ}
    (h : FreeConditionLambdaBoundInternal δ C α ε κ₀) (Λ : Finset (ℤ × ℤ)) (κ : ℝ)
    (hκ : κ₀ < κ) (lam : ℤ → ℝ) (hlam : ConditionLambdaInternal C α ε κ lam)
    (hphys : PhysicalWeightInternal lam) (f : Λ → ℝ) (hf : ∑ v, f v = 0) :
    1 ≤ fullGasPartitionInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ
        (fun _ => lam) ∧
      (∀ u : ℝ, Real.exp (u ^ 2 * κ * (1 - δ) * freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f / 2) ≤
        fullExpMomentInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ
          (fun _ => lam) f u) ∧
      (1 - δ) * κ * freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f ≤
        fullSecondMomentInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ
          (fun _ => lam) f ∧
      fullSecondMomentInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ
          (fun _ => lam) f ≤ κ * freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f := by
  obtain ⟨-, hfull⟩ := h Λ κ hκ lam hlam hphys.1
  have hZ := one_le_fullGasPartition hfull.1.summable (fun _ => hphys.2) (fun _ => hphys.1)
  have hZpos : 0 < fullGasPartitionInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ
      (fun _ => lam) := zero_lt_one.trans_le hZ
  exact ⟨hZ, fun u => hfull.expMoment_ge hZpos f hf u, hfull.secondMoment_ge hZpos f hf,
    fullSecondMoment_le (fun q => gasWeight_nonneg_of_physical _ κ (fun _ => hphys.2) q)
      hZpos.le f⟩

end FroehlichSpencer.BKT.Coulomb
