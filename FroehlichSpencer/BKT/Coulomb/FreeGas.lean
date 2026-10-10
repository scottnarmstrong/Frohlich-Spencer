/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.Screening
public import FroehlichSpencer.BKT.Coulomb.TorusKernel
import Mathlib.Tactic

/-!
# The FS81 free-boundary gas on a finite set

Here `C = -a` (`Coulomb/PotentialKernel.lean`) and the gas on sites
`V` with positions `pos : V → ℤ²` is the neutral gas's neutral gas with the linear map
`freePotentialOpInternal pos`, `T_free f (v) = ∑_u a(pos v - pos u) f(u)`.

Every theorem below is
stated for `Λ : Finset (ℤ × ℤ)` with sites `↥Λ`, uniformly in `Λ`.

* **Transport** (`gasExpectation_region_eq`): the gas on a graph `W` with charges confined to
  the image of an injective `e : V → W` is exactly the gas on `V` with the pulled-back potential
  `pullbackOpInternal T e`.
* **Periodic approximation**: sites are reduced modulo `L_n = 2n + 4` into the periodic
  square `Λ_{L_n}^per`, eventually injectively (`eventually_injective_latticeToSquare`); by the branch mixture
  (`Coulomb/TorusKernel.lean`) the pulled-back energies and pairings converge to the free ones
  on neutral arguments, so gas expectations converge (`tendsto_gasExpectation_of_tendsto`).
* `freeExpMomentInternal` and `freeSecondMomentInternal` are FS81's free-b.c. sine-Gordon
  functional `⟨e^{u φ(f)}⟩_Λ` and field second moment `⟨φ(f)²⟩_Λ`, **defined** by the
  representation formulas (5.12) and (1.17) and **characterized** as the limits of the
  sine-Gordon functionals of the periodic squares (`tendsto_torus_expMoment`,
  `tendsto_torus_secondMoment`), i.e.

FS81's `dμ_κ = lim dμ_{κ,Ω}` with periodic `Ω` (p. 531).

No infinite-volume Gaussian measure is constructed.
* ** theorems**: `free_expMoment_lower_bound` (FS81 Theorem 5.1, free b.c.),
  `free_secondMoment_lower_bound` (FS81 Theorem A, free b.c.) and `free_chargeFluctuation_le`,
  each with a threshold `κ₀(δ, α)` independent of `Λ`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology

section Transport

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Extension of a charge configuration along `e : V → W` (by zero off the image). -/
def extendConfigInternal (e : V → W) (p : V → ℤ) (w : W) : ℤ :=
  ∑ v, if e v = w then p v else 0

/-- Push-forward of a real function along `e : V → W`. -/
def pushRealInternal (e : V → W) (f : V → ℝ) (w : W) : ℝ :=
  ∑ v, if e v = w then f v else 0

/-- The push-forward as a linear map. -/
def pushRealLinearInternal (e : V → W) : (V → ℝ) →ₗ[ℝ] W → ℝ where
  toFun := pushRealInternal e
  map_add' f g := by
    funext w
    simp only [pushRealInternal, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  map_smul' c f := by
    funext w
    simp only [pushRealInternal, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp

/-- The potential pulled back along `e`: `(T* f)(v) = T (push f) (e v)`. -/
def pullbackOpInternal (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (e : V → W) : (V → ℝ) →ₗ[ℝ] V → ℝ :=
  LinearMap.funLeft ℝ ℝ e ∘ₗ T ∘ₗ pushRealLinearInternal e

omit [DecidableEq V] [Fintype W] in
theorem pullbackOp_apply (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (e : V → W) (f : V → ℝ) (v : V) :
    pullbackOpInternal T e f v = T (pushRealInternal e f) (e v) := rfl

omit [DecidableEq V] in
theorem sum_pushReal_mul (e : V → W) (g : V → ℝ) (h : W → ℝ) :
    ∑ w, pushRealInternal e g w * h w = ∑ v, g v * h (e v) := by
  simp only [pushRealInternal, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_eq]
  simp

omit [DecidableEq V] [Fintype W] in
theorem extendConfig_cast (e : V → W) (p : V → ℤ) :
    (fun w => ((extendConfigInternal e p w : ℤ) : ℝ)) = pushRealInternal e (fun v => (p v : ℝ)) := by
  funext w
  simp only [extendConfigInternal, pushRealInternal]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

omit [DecidableEq V] in
theorem sum_extendConfig_mul (e : V → W) (p : V → ℤ) (h : W → ℝ) :
    ∑ w, (extendConfigInternal e p w : ℝ) * h w = ∑ v, (p v : ℝ) * h (e v) := by
  have := sum_pushReal_mul e (fun v => (p v : ℝ)) h
  rw [← this, ← extendConfig_cast]

omit [DecidableEq V] in
theorem sum_extendConfig (e : V → W) (p : V → ℤ) :
    ∑ w, extendConfigInternal e p w = ∑ v, p v := by
  have := sum_extendConfig_mul e p (fun _ => 1)
  simp only [mul_one] at this
  exact_mod_cast this

omit [Fintype W] in
theorem extendConfig_apply {e : V → W} (he : Function.Injective e) (p : V → ℤ) (v : V) :
    extendConfigInternal e p (e v) = p v := by
  simp only [extendConfigInternal, he.eq_iff]
  simp

omit [DecidableEq V] [Fintype W] in
theorem extendConfig_apply_of_forall_ne {e : V → W} (p : V → ℤ) {w : W} (hw : ∀ v, e v ≠ w) :
    extendConfigInternal e p w = 0 := by
  simp [extendConfigInternal, hw]

omit [DecidableEq V] in
theorem chargeEnergy_extendConfig (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (e : V → W) (p : V → ℤ) :
    chargeEnergyInternal T (extendConfigInternal e p) =
      chargeEnergyInternal (pullbackOpInternal T e) p := by
  unfold chargeEnergyInternal
  rw [extendConfig_cast, sum_extendConfig_mul]
  rfl

theorem prod_regionWeight_extendConfig {e : V → W} (he : Function.Injective e) (lam : ℤ → ℝ)
    (p : V → ℤ) :
    ∏ w, regionWeightInternal (Finset.univ.image e) lam w (extendConfigInternal e p w) =
      ∏ v, lam (p v) := by
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image e)) (fun w _ hw => ?_),
    Finset.prod_image (fun v _ v' _ h => he h)]
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp [regionWeightInternal, extendConfig_apply he]
  · have hne : ∀ v, e v ≠ w := fun v h => hw (Finset.mem_image.2 ⟨v, Finset.mem_univ _, h⟩)
    simp [regionWeightInternal, hw, extendConfig_apply_of_forall_ne p hne]

theorem gasWeight_extendConfig {e : V → W} (he : Function.Injective e)
    (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (κ : ℝ) (lam : ℤ → ℝ) (p : V → ℤ) :
    gasWeightInternal T κ (regionWeightInternal (Finset.univ.image e) lam)
        (extendConfigInternal e p) =
      gasWeightInternal (pullbackOpInternal T e) κ (fun _ => lam) p := by
  unfold gasWeightInternal
  rw [sum_extendConfig, prod_regionWeight_extendConfig he, chargeEnergy_extendConfig]

omit [Fintype W] in
theorem extendConfig_comp {e : V → W} (he : Function.Injective e) (p : V → ℤ) :
    (fun v => extendConfigInternal e p (e v)) = p := by
  funext v; exact extendConfig_apply he p v

theorem extendConfig_mem {e : V → W} (he : Function.Injective e) {N : ℕ} {p : V → ℤ}
    (hp : p ∈ chargeConfigsInternal V N) : extendConfigInternal e p ∈ chargeConfigsInternal W N := by
  simp only [chargeConfigsInternal, Fintype.mem_piFinset, Finset.mem_Icc] at hp ⊢
  intro w
  by_cases hw : ∃ v, e v = w
  · obtain ⟨v, rfl⟩ := hw
    rw [extendConfig_apply he]
    exact hp v
  · push Not at hw
    rw [extendConfig_apply_of_forall_ne p hw]
    omega

/-- **Transport.** The neutral gas on `W` with charges confined to `e(V)` is the gas on `V` with
the pulled-back potential. -/
theorem sum_region_eq {e : V → W} (he : Function.Injective e) (T : (W → ℝ) →ₗ[ℝ] W → ℝ)
    (κ : ℝ) (lam : ℤ → ℝ) (N : ℕ) (G : (W → ℤ) → ℝ) :
    ∑ q ∈ chargeConfigsInternal W N,
        gasWeightInternal T κ (regionWeightInternal (Finset.univ.image e) lam) q * G q =
      ∑ p ∈ chargeConfigsInternal V N,
        gasWeightInternal (pullbackOpInternal T e) κ (fun _ => lam) p *
          G (extendConfigInternal e p) := by
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => extendConfigInternal e p)
    (fun p hp _ => extendConfig_mem he hp) ?_ ?_ ?_
  · intro p₁ _ _ p₂ _ _ h
    rw [← extendConfig_comp he p₁, ← extendConfig_comp he p₂, h]
  · intro q hq hne
    have hsupp : ∀ w, (∀ v, e v ≠ w) → q w = 0 := by
      intro w hw
      by_contra hqw
      apply hne
      unfold gasWeightInternal
      split_ifs
      · rw [Finset.prod_eq_zero (Finset.mem_univ w) (by
          have : w ∉ Finset.univ.image e := by simpa using hw
          simp [regionWeightInternal, this, hqw])]
        ring
      · ring
    have hq' : extendConfigInternal e (fun v => q (e v)) = q := by
      funext w
      by_cases hw : ∃ v, e v = w
      · obtain ⟨v, rfl⟩ := hw
        exact extendConfig_apply he _ v
      · push Not at hw
        rw [extendConfig_apply_of_forall_ne _ hw, hsupp w hw]
    refine ⟨fun v => q (e v), ?_, ?_, hq'⟩
    · simp only [chargeConfigsInternal, Fintype.mem_piFinset] at hq ⊢
      exact fun v => hq (e v)
    · rw [← gasWeight_extendConfig he, hq']
      exact hne
  · intro p _ _
    rw [gasWeight_extendConfig he]

theorem gasPartition_region_eq {e : V → W} (he : Function.Injective e)
    (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (κ : ℝ) (lam : ℤ → ℝ) (N : ℕ) :
    gasPartitionInternal N T κ (regionWeightInternal (Finset.univ.image e) lam) =
      gasPartitionInternal N (pullbackOpInternal T e) κ (fun _ => lam) := by
  have := sum_region_eq he T κ lam N (fun _ => 1)
  simpa [gasPartitionInternal] using this

theorem gasExpectation_region_eq {e : V → W} (he : Function.Injective e)
    (T : (W → ℝ) →ₗ[ℝ] W → ℝ) (κ : ℝ) (lam : ℤ → ℝ) (N : ℕ) (G : (W → ℤ) → ℝ) :
    gasExpectationInternal N T κ (regionWeightInternal (Finset.univ.image e) lam) G =
      gasExpectationInternal N (pullbackOpInternal T e) κ (fun _ => lam)
        (fun p => G (extendConfigInternal e p)) := by
  unfold gasExpectationInternal
  rw [sum_region_eq he, gasPartition_region_eq he]

end Transport

/-! ### The FS81 free-boundary potential -/

section Free

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- FS81 p. 529 (i): `T_free f (v) = ∑_u a(pos v - pos u) f(u)`. The free potential is
`C = -T_free`, i.e. `C(i, j) = -a(i - j)`, the whole-plane Green function restricted to the
sites. -/
def freePotentialOpInternal (pos : V → ℤ × ℤ) : (V → ℝ) →ₗ[ℝ] V → ℝ where
  toFun f v := ∑ u, potentialKernelInternal (pos v - pos u) * f u
  map_add' f g := by
    funext v
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring

omit [DecidableEq V] in
theorem freePotentialOp_apply (pos : V → ℤ × ℤ) (f : V → ℝ) (v : V) :
    freePotentialOpInternal pos f v = ∑ u, potentialKernelInternal (pos v - pos u) * f u := rfl

omit [DecidableEq V] in
/-- The free pairing `⟨g, C f⟩ = -∑_{u,v} g(u) f(v) a(pos u - pos v)`. -/
theorem sum_mul_neg_freePotentialOp (pos : V → ℤ × ℤ) (g f : V → ℝ) :
    ∑ u, g u * -(freePotentialOpInternal pos f u) =
      -∑ u, ∑ v, g u * f v * potentialKernelInternal (pos u - pos v) := by
  simp only [freePotentialOp_apply, Finset.mul_sum, ← Finset.sum_neg_distrib, mul_neg]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/-- Gibbs weights, partition functions and expectations depend continuously on the energies of
neutral configurations. -/
theorem tendsto_gasExpectation_of_tendsto (N : ℕ) (Tn : ℕ → (V → ℝ) →ₗ[ℝ] V → ℝ)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : V → ℤ → ℝ) (Fn : ℕ → (V → ℤ) → ℝ)
    (F : (V → ℤ) → ℝ)
    (hE : ∀ p : V → ℤ, ∑ j, p j = 0 →
      Tendsto (fun n => chargeEnergyInternal (Tn n) p) atTop (𝓝 (chargeEnergyInternal T p)))
    (hF : ∀ p, Tendsto (fun n => Fn n p) atTop (𝓝 (F p)))
    (hZ : gasPartitionInternal N T κ lam ≠ 0) :
    Tendsto (fun n => gasExpectationInternal N (Tn n) κ lam (Fn n)) atTop
      (𝓝 (gasExpectationInternal N T κ lam F)) := by
  have hw : ∀ p, Tendsto (fun n => gasWeightInternal (Tn n) κ lam p) atTop
      (𝓝 (gasWeightInternal T κ lam p)) := by
    intro p
    unfold gasWeightInternal
    split_ifs with h
    · exact tendsto_const_nhds.mul
        ((Real.continuous_exp.tendsto _).comp ((hE p h).const_mul (-κ)))
    · exact tendsto_const_nhds
  unfold gasExpectationInternal gasPartitionInternal at *
  exact (tendsto_finsetSum _ fun p _ => (hw p).mul (hF p)).div
    (tendsto_finsetSum _ fun p _ => hw p) hZ

omit [DecidableEq V] in
/-- Reduction modulo `L_n` is eventually injective on a finite set of distinct lattice points. -/
theorem eventually_injective_latticeToSquare (pos : V → ℤ × ℤ) (hpos : Function.Injective pos) :
    ∀ᶠ n in atTop, Function.Injective fun v => latticeToSquareInternal (torusSideInternal n) (pos v) := by
  set R := ∑ v, ((pos v).1.natAbs + (pos v).2.natAbs)
  have hR : ∀ v, (pos v).1.natAbs ≤ R ∧ (pos v).2.natAbs ≤ R := by
    intro v
    have := Finset.single_le_sum (f := fun v => (pos v).1.natAbs + (pos v).2.natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    constructor <;> omega
  filter_upwards [eventually_ge_atTop R] with n hn
  intro u v huv
  set L := torusSideInternal n
  have hL : 2 * R < L := by unfold L torusSideInternal; omega
  have h := (squareTorusVertexEquiv L).symm.injective huv
  simp only [torusPointInternal, Prod.mk.injEq] at h
  have hcoord : ∀ a b : ℤ, a.natAbs ≤ R → b.natAbs ≤ R → (a : ZMod L) = b → a = b := by
    intro a b ha hb hab
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b L).1 hab
    have : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]; constructor <;> omega)
    omega
  apply hpos
  exact Prod.ext (hcoord _ _ (hR u).1 (hR v).1 h.1) (hcoord _ _ (hR u).2 (hR v).2 h.2)

end Free

/-! ### Periodic approximation of the free gas -/

section Periodic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The site map `V → Λ_{L_n}^per`. -/
def torusSiteMapInternal (pos : V → ℤ × ℤ) (n : ℕ) :
    V → Fin (torusSideInternal n) × Fin (torusSideInternal n) :=
  fun v => latticeToSquareInternal (torusSideInternal n) (pos v)

/--
The Green operator of the periodic square `Λ_{L_n}^per`.
-/
def torusGreenOpInternal (n : ℕ) :
    (Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℝ) →ₗ[ℝ]
      Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℝ :=
  (squarePeriodic (torusSideInternal n)).greenOp (squarePeriodic_connected _ (one_lt_torusSide n))

theorem isLaplacianPseudoinverse_torusGreenOp (n : ℕ) :
    (squarePeriodic (torusSideInternal n)).IsLaplacianPseudoinverse (torusGreenOpInternal n) := by
  have hG := squarePeriodic_connected _ (one_lt_torusSide n)
  exact ⟨fun f hf => ⟨(squarePeriodic _).laplacian_greenOp_of_sum_eq_zero hG f hf,
    (squarePeriodic _).greenOp_laplacian_of_sum_eq_zero hG f hf⟩,
    (squarePeriodic _).greenOp_const hG⟩

/-- The periodic potential pulled back to the sites: `T_n f (v) = T_{L_n} (push f) (pos v)`. -/
def torusPullbackOpInternal (pos : V → ℤ × ℤ) (n : ℕ) : (V → ℝ) →ₗ[ℝ] V → ℝ :=
  pullbackOpInternal (torusGreenOpInternal n) (torusSiteMapInternal pos n)

omit [DecidableEq V] in
theorem pushReal_torusSiteMap (pos : V → ℤ × ℤ) (n : ℕ) (f : V → ℝ) :
    pushRealInternal (torusSiteMapInternal pos n) f = latticePushInternal (torusSideInternal n) pos f :=
  rfl

omit [DecidableEq V] in
theorem sum_mul_neg_torusPullbackOp (pos : V → ℤ × ℤ) (n : ℕ) (g f : V → ℝ) :
    ∑ v, g v * -(torusPullbackOpInternal pos n f v) =
      ∑ w, latticePushInternal (torusSideInternal n) pos g w *
        -(torusGreenOpInternal n (latticePushInternal (torusSideInternal n) pos f) w) := by
  rw [sum_latticePush_mul]
  rfl

omit [DecidableEq V] in
/-- **the branch mixture on the sites.** For zero-sum `f`, `⟨g, C_n f⟩ → ⟨g, C f⟩` (free potential). -/
theorem tendsto_sum_mul_neg_torusPullbackOp (pos : V → ℤ × ℤ) (g f : V → ℝ)
    (hf : ∑ v, f v = 0) :
    Tendsto (fun n => ∑ v, g v * -(torusPullbackOpInternal pos n f v)) atTop
      (𝓝 (∑ v, g v * -(freePotentialOpInternal pos f v))) := by
  simp_rw [sum_mul_neg_torusPullbackOp, sum_mul_neg_freePotentialOp]
  exact tendsto_pairing_latticePush pos g f hf

omit [DecidableEq V] in
theorem tendsto_chargeEnergy_torusPullbackOp (pos : V → ℤ × ℤ) (p : V → ℤ) (hp : ∑ j, p j = 0) :
    Tendsto (fun n => chargeEnergyInternal (torusPullbackOpInternal pos n) p) atTop
      (𝓝 (chargeEnergyInternal (freePotentialOpInternal pos) p)) := by
  unfold chargeEnergyInternal
  refine (tendsto_sum_mul_neg_torusPullbackOp pos _ _ ?_).div_const 2
  exact_mod_cast hp

/-! #### The FS81 free-boundary hard-core gas -/

/-- FS81 (1.9), free b.c.: the hard-core gas on the sites `V` with the whole-plane potential. -/
def freeGasExpectationInternal (pos : V → ℤ × ℤ) (κ z : ℝ) (F : (V → ℤ) → ℝ) : ℝ :=
  gasExpectationInternal 1 (freePotentialOpInternal pos) κ (fun _ => hardCoreWeightInternal z) F

/-- `⟨f, C f⟩` with FS81's free potential. -/
def freeQuadInternal (pos : V → ℤ × ℤ) (f : V → ℝ) : ℝ :=
  ∑ v, f v * -(freePotentialOpInternal pos f v)

/-- `⟨q, C f⟩` with FS81's free potential. -/
def freeChargePairingInternal (pos : V → ℤ × ℤ) (f : V → ℝ) (p : V → ℤ) : ℝ :=
  ∑ v, (p v : ℝ) * -(freePotentialOpInternal pos f v)

/-- FS81 (5.6)/(5.12), free b.c.: `⟨e^{u φ(f)}⟩_Λ = e^{κ⟨f,Cf⟩u²/2} ⟨cos (u κ ⟨q, C f⟩)⟩_Λ`. The
right side is the sine-Gordon representation of the free-b.c. gas; `tendsto_torus_expMoment`
identifies it with the limit of the sine-Gordon functionals of the periodic squares. -/
def freeExpMomentInternal (pos : V → ℤ × ℤ) (κ z : ℝ) (f : V → ℝ) (u : ℝ) : ℝ :=
  Real.exp (κ * freeQuadInternal pos f / 2 * u ^ 2) *
    freeGasExpectationInternal pos κ z (fun p => Real.cos (u * (κ * freeChargePairingInternal pos f p)))

/-- FS81 (1.17), free b.c.: `⟨φ(f)²⟩_Λ = κ ⟨f, C f⟩ - κ² ⟨⟨q, C f⟩²⟩_Λ`; identified with the
limit of the periodic field second moments in `tendsto_torus_secondMoment`. -/
def freeSecondMomentInternal (pos : V → ℤ × ℤ) (κ z : ℝ) (f : V → ℝ) : ℝ :=
  κ * freeQuadInternal pos f -
    freeGasExpectationInternal pos κ z (fun p => (κ * freeChargePairingInternal pos f p) ^ 2)

theorem freeGasPartition_pos (pos : V → ℤ × ℤ) (κ : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    0 < gasPartitionInternal 1 (freePotentialOpInternal pos) κ (fun _ => hardCoreWeightInternal z) :=
  gasPartition_pos 1 _ κ _ (fun _ n => by
      unfold hardCoreWeightInternal; split_ifs <;> positivity)
    (fun _ => by simp [hardCoreWeightInternal])

end Periodic

/-! #### The free functionals are periodic thermodynamic limits -/

section Limits

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The hard-core sine-Gordon weights on `Λ_{L_n}^per` with charges confined to the image of the
sites. -/
abbrev torusWeightsInternal (pos : V → ℤ × ℤ) (n : ℕ) (z : ℝ) :=
  hardCoreSineGordonInternal (Finset.univ.image (torusSiteMapInternal pos n)) z

theorem torus_gasExpectation_eq (pos : V → ℤ × ℤ) (n : ℕ)
    (hinj : Function.Injective (torusSiteMapInternal pos n)) (κ z : ℝ) (Φ : ℝ → ℝ)
    (f : V → ℝ) :
    gasExpectationInternal 1 (torusGreenOpInternal n) κ
        (regionWeightInternal (Finset.univ.image (torusSiteMapInternal pos n))
          (hardCoreWeightInternal z))
        (fun q => Φ (∑ j, (q j : ℝ) *
          -(torusGreenOpInternal n (latticePushInternal (torusSideInternal n) pos f) j))) =
      gasExpectationInternal 1 (torusPullbackOpInternal pos n) κ (fun _ => hardCoreWeightInternal z)
        (fun p => Φ (∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v))) := by
  rw [gasExpectation_region_eq hinj]
  congr 1
  funext p
  congr 1
  rw [sum_extendConfig_mul]
  rfl

/-- **The free sine-Gordon functional is the periodic thermodynamic limit** (FS81 (1.16) with
`dμ_κ = lim dμ_{κ,Ω}`, periodic `Ω`, p. 531): the sine-Gordon expectations of `e^{u φ(f)}` on
`Λ_{L_n}^per`, with charges confined to the sites, converge to `freeExpMomentInternal`. -/
theorem tendsto_torus_expMoment (pos : V → ℤ × ℤ) (hpos : Function.Injective pos) (κ : ℝ)
    (hκ : 0 < κ) {z : ℝ} (hz : 0 ≤ z) (f : V → ℝ) (hf : ∑ v, f v = 0) (u : ℝ)
    (root : ∀ n, Fin (torusSideInternal n) × Fin (torusSideInternal n)) :
    Tendsto (fun n => weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusWeightsInternal pos n z)
        (fun φ => Real.exp (u * ∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j)))
      atTop (𝓝 (freeExpMomentInternal pos κ z f u)) := by
  have hrep : ∀ᶠ n in atTop,
      Real.exp (κ * (∑ v, f v * -(torusPullbackOpInternal pos n f v)) / 2 * u ^ 2) *
        gasExpectationInternal 1 (torusPullbackOpInternal pos n) κ
          (fun _ => hardCoreWeightInternal z)
          (fun p => Real.cos (u * (κ * ∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v)))) =
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusWeightsInternal pos n z)
        (fun φ => Real.exp (u * ∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j)) := by
    filter_upwards [eventually_injective_latticeToSquare pos hpos] with n hinj
    rw [weightedGFFExpectation_exp_mul_sineGordon (squarePeriodic (torusSideInternal n))
      (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n) 1 _
      (regionWeight_neg _ (hardCoreWeight_neg z)) (torusGreenOpInternal n)
      (isLaplacianPseudoinverse_torusGreenOp n) (latticePushInternal (torusSideInternal n) pos f)
      (by rw [sum_latticePush]; exact hf) u,
      torus_gasExpectation_eq pos n hinj κ z (fun x => Real.cos (u * (κ * x))) f,
      ← sum_mul_neg_torusPullbackOp]
  refine Tendsto.congr' hrep ?_
  unfold freeExpMomentInternal freeGasExpectationInternal freeQuadInternal freeChargePairingInternal
  refine Tendsto.mul ((Real.continuous_exp.tendsto _).comp
    ((((tendsto_sum_mul_neg_torusPullbackOp pos f f hf).const_mul κ).div_const 2).mul_const _)) ?_
  refine tendsto_gasExpectation_of_tendsto 1 _ _ κ _ _ _
    (fun p hp => tendsto_chargeEnergy_torusPullbackOp pos p hp) (fun p => ?_)
    (freeGasPartition_pos pos κ hz).ne'
  exact (Real.continuous_cos.tendsto _).comp
    (((tendsto_sum_mul_neg_torusPullbackOp pos _ f hf).const_mul κ).const_mul u)

/-- **The free field second moment is the periodic thermodynamic limit** of the sine-Gordon
second moments `⟨φ(f)²⟩` on `Λ_{L_n}^per` (`z ≥ 0`). -/
theorem tendsto_torus_secondMoment (pos : V → ℤ × ℤ) (hpos : Function.Injective pos) (κ : ℝ)
    (hκ : 0 < κ) {z : ℝ} (hz : 0 ≤ z) (f : V → ℝ) (hf : ∑ v, f v = 0)
    (root : ∀ n, Fin (torusSideInternal n) × Fin (torusSideInternal n)) :
    Tendsto (fun n => weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusWeightsInternal pos n z)
        (fun φ => (∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j) ^ 2))
      atTop (𝓝 (freeSecondMomentInternal pos κ z f)) := by
  have hrep : ∀ᶠ n in atTop,
      κ * (∑ v, f v * -(torusPullbackOpInternal pos n f v)) - κ ^ 2 *
        gasExpectationInternal 1 (torusPullbackOpInternal pos n) κ
          (fun _ => hardCoreWeightInternal z)
          (fun p => (∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v)) ^ 2) =
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusWeightsInternal pos n z)
        (fun φ => (∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j) ^ 2) := by
    filter_upwards [eventually_injective_latticeToSquare pos hpos] with n hinj
    rw [hardCore_secondMoment_eq (squarePeriodic (torusSideInternal n))
      (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n) _ z hz
      (torusGreenOpInternal n) (isLaplacianPseudoinverse_torusGreenOp n)
      (latticePushInternal (torusSideInternal n) pos f) (by rw [sum_latticePush]; exact hf),
      torus_gasExpectation_eq pos n hinj κ z (fun x => x ^ 2) f,
      ← sum_mul_neg_torusPullbackOp]
  refine Tendsto.congr' hrep ?_
  unfold freeSecondMomentInternal freeGasExpectationInternal freeQuadInternal
    freeChargePairingInternal
  have hsq : ∀ F : (V → ℤ) → ℝ, gasExpectationInternal 1 (freePotentialOpInternal pos) κ
      (fun _ => hardCoreWeightInternal z) (fun p => (κ * F p) ^ 2) =
      κ ^ 2 * gasExpectationInternal 1 (freePotentialOpInternal pos) κ
        (fun _ => hardCoreWeightInternal z) (fun p => F p ^ 2) := by
    intro F
    rw [← gasExpectation_const_mul]
    congr 1; funext p; ring
  rw [hsq]
  refine ((tendsto_sum_mul_neg_torusPullbackOp pos f f hf).const_mul κ).sub
    (Tendsto.const_mul _ ?_)
  refine tendsto_gasExpectation_of_tendsto 1 _ _ κ _ _ _
    (fun p hp => tendsto_chargeEnergy_torusPullbackOp pos p hp) (fun p => ?_)
    (freeGasPartition_pos pos κ hz).ne'
  exact (tendsto_sum_mul_neg_torusPullbackOp pos _ f hf).pow 2

end Limits

/-! ### FS81 Theorem 5.1 and Theorem A with free boundary conditions -/

/-- FS81 Theorem 5.1 (J p. 564, (5.4)) with **free b.c.** (p. 529 (i)) on every finite
`Λ ⊂ ℤ²`, threshold `κ₀`. -/
def FreeExpMomentBoundInternal (δ α κ₀ : ℝ) : Prop :=
  ∀ (Λ : Finset (ℤ × ℤ)) (κ : ℝ), 0 < κ → κ₀ < κ →
    ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      ∀ f : Λ → ℝ, ∑ v, f v = 0 → ∀ u : ℝ,
        Real.exp (u ^ 2 * κ * (1 - δ) * freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f / 2) ≤
          freeExpMomentInternal (Subtype.val : Λ → ℤ × ℤ) κ z f u

/-- FS81 Theorem A (J p. 532, (1.19), `c₁ = (1 - δ) κ`) with **free b.c.** on every finite
`Λ ⊂ ℤ²`, threshold `κ₀`. -/
def FreeSecondMomentBoundInternal (δ α κ₀ : ℝ) : Prop :=
  ∀ (Λ : Finset (ℤ × ℤ)) (κ : ℝ), 0 < κ → κ₀ < κ →
    ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      ∀ f : Λ → ℝ, ∑ v, f v = 0 →
        (1 - δ) * κ * freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f ≤
          freeSecondMomentInternal (Subtype.val : Λ → ℤ × ℤ) κ z f

/-- **FS81 Theorem 5.1, free boundary conditions** : for each `δ > 0` and `α` there is
`κ₀`, independent of the finite set `Λ ⊂ ℤ²`, such that the free-b.c. sine-Gordon functional
satisfies `⟨e^{u φ(f)}⟩_Λ ≥ exp (u² κ (1 - δ) ⟨f, C f⟩ / 2)` with FS81's whole-plane potential
`C = -a`, for `κ > κ₀`, `0 ≤ z ≤ e^{κ/17 + α}` and every zero-sum `f`. Proof: the periodic
bounds of `hardCore_expMoment_lower_bound` pass to the limit `tendsto_torus_expMoment`. -/
theorem free_expMoment_lower_bound (δ : ℝ) (hδ : 0 < δ) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ FreeExpMomentBoundInternal δ α κ₀ := by
  obtain ⟨κ₀, hκ₀, h⟩ := hardCore_expMoment_lower_bound δ hδ α
  refine ⟨κ₀, hκ₀, fun Λ κ hκ hκκ₀ z hz hzκ f hf u => ?_⟩
  have hbound : ∀ n, Real.exp (u ^ 2 * κ * (1 - δ) *
      (∑ v, f v * -(torusPullbackOpInternal (Subtype.val : Λ → ℤ × ℤ) n f v)) / 2) ≤
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) 0
        (torusWeightsInternal (Subtype.val : Λ → ℤ × ℤ) n z)
        (fun φ => Real.exp (u * ∑ j, φ j *
          latticePushInternal (torusSideInternal n) (Subtype.val : Λ → ℤ × ℤ) f j)) := by
    intro n
    have hb := ((h (torusSideInternal n) (one_lt_torusSide n)).2 (even_torusSide n)) 0
      (Finset.univ.image (torusSiteMapInternal (Subtype.val : Λ → ℤ × ℤ) n)) κ hκ hκκ₀ z hz hzκ
    have := hb.2 (torusGreenOpInternal n) (isLaplacianPseudoinverse_torusGreenOp n)
      (latticePushInternal (torusSideInternal n) Subtype.val f) (by rw [sum_latticePush]; exact hf) u
    rwa [← sum_mul_neg_torusPullbackOp] at this
  refine le_of_tendsto_of_tendsto' ?_ (tendsto_torus_expMoment _ Subtype.val_injective κ hκ hz f hf u
    (fun _ => 0)) hbound
  exact (Real.continuous_exp.tendsto _).comp
    (((tendsto_sum_mul_neg_torusPullbackOp _ f f hf).const_mul _).div_const 2)

/-- **FS81 Theorem A, free boundary conditions** : `⟨φ(f)²⟩_Λ ≥ (1 - δ) κ ⟨f, C f⟩` with
FS81's whole-plane potential, uniformly in the finite set `Λ ⊂ ℤ²`. -/
theorem free_secondMoment_lower_bound (δ : ℝ) (hδ : 0 < δ) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ FreeSecondMomentBoundInternal δ α κ₀ := by
  obtain ⟨κ₀, hκ₀, h⟩ := hardCore_secondMoment_lower_bound δ hδ α
  refine ⟨κ₀, hκ₀, fun Λ κ hκ hκκ₀ z hz hzκ f hf => ?_⟩
  have hbound : ∀ n, (1 - δ) * κ *
      (∑ v, f v * -(torusPullbackOpInternal (Subtype.val : Λ → ℤ × ℤ) n f v)) ≤
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) 0
        (torusWeightsInternal (Subtype.val : Λ → ℤ × ℤ) n z)
        (fun φ => (∑ j, φ j *
          latticePushInternal (torusSideInternal n) (Subtype.val : Λ → ℤ × ℤ) f j) ^ 2) := by
    intro n
    have := ((h (torusSideInternal n) (one_lt_torusSide n)).2 (even_torusSide n)) 0
      (Finset.univ.image (torusSiteMapInternal (Subtype.val : Λ → ℤ × ℤ) n)) κ hκ
      hκκ₀ z hz hzκ (torusGreenOpInternal n) (isLaplacianPseudoinverse_torusGreenOp n)
      (latticePushInternal (torusSideInternal n) Subtype.val f) (by rw [sum_latticePush]; exact hf)
    rwa [← sum_mul_neg_torusPullbackOp] at this
  exact le_of_tendsto_of_tendsto' (((tendsto_sum_mul_neg_torusPullbackOp _ f f hf).const_mul _))
    (tendsto_torus_secondMoment _ Subtype.val_injective κ hκ hz f hf (fun _ => 0)) hbound

/-- The free-b.c. charge-fluctuation bound (finite-volume screening obstruction with FS81's
potential): `⟨(κ ⟨q, C f⟩)²⟩_Λ ≤ δ κ ⟨f, C f⟩`. -/
theorem free_chargeFluctuation_le {δ α κ₀ : ℝ} (h : FreeSecondMomentBoundInternal δ α κ₀)
    (Λ : Finset (ℤ × ℤ)) (κ : ℝ) (hκ : 0 < κ) (hκκ₀ : κ₀ < κ) (z : ℝ) (hz : 0 ≤ z)
    (hzκ : z ≤ Real.exp (κ / 17 + α)) (f : Λ → ℝ) (hf : ∑ v, f v = 0) :
    freeGasExpectationInternal (Subtype.val : Λ → ℤ × ℤ) κ z
        (fun p => (κ * freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) f p) ^ 2) ≤
      δ * κ * freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) f := by
  have := h Λ κ hκ hκκ₀ z hz hzκ f hf
  unfold freeSecondMomentInternal at this
  linarith

end FroehlichSpencer.BKT.Coulomb
