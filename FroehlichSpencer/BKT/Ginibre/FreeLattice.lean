/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.PairSystem
public import FroehlichSpencer.BKT.Rotator.Ginibre.FreeLimit

/-!
# Free-boundary abelian models on finite domains of `ℤ²` and their thermodynamic limit

A `FreeModel` is a single-site measure `ν` with real Fourier coefficients forming an equivalence
kernel, and a bond weight `w` such that `(w, w)` and `(w, 1)` are Ginibre pairs. On a finite
domain `Λ ⊆ ℤ²` its free-boundary state puts the weight `w(θ_i − θ_j)` on every nearest-neighbour
pair of `Λ`. The two-point function `⟨cos(ξ(θ_u − θ_v))⟩_Λ` is nonnegative, increases with the
domain and is translation invariant; along the centered squares it converges, and the limit is
defined only through this proved convergence. It dominates every finite-volume value, is the limit
along every increasing exhausting sequence, and is translation invariant. Comparison of two models
whose single-site measures form an equivalence kernel and whose bond weights form a Ginibre pair
passes to the limits.
-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

/-- A free-boundary nearest-neighbour model with Ginibre structure. -/
structure FreeModel where
  /-- The single-site reference measure. -/
  ν : Measure ℝ
  /-- Its real Fourier coefficients. -/
  lam : ℤ → ℝ
  /-- The bond weight `w(θ_i − θ_j)`. -/
  w : ℝ → ℝ
  isFinite : IsFiniteMeasure ν
  fourier : HasRealFourier ν lam
  mass_ne_zero : ν Set.univ ≠ 0
  kernel : HasEquivKernel lam lam
  bond : IsBondWeight w
  pair : ∀ (V : Type) [Fintype V], IsGinibrePair V w w
  pair_one : ∀ (V : Type) [Fintype V], IsGinibrePair V w fun _ => 1

namespace FreeModel

variable (M : FreeModel)

attribute [instance] FreeModel.isFinite

/-- The bond weights of the free-boundary state on `Λ`: `w` on positive nearest-neighbour steps,
`1` on all other ordered pairs. -/
def bondWeight (Λ : Finset (ℤ × ℤ)) (b : Λ × Λ) : ℝ → ℝ :=
  if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then M.w else fun _ => 1

/-- The free-boundary state on the finite domain `Λ`. -/
def gibbs (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  pairGibbs M.ν (bondFrequency Λ) (M.bondWeight Λ)

/-- The finite-volume two-point function `⟨cos(ξ(θ_u − θ_v))⟩_Λ`. -/
def twoPoint (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : ℝ :=
  ∫ θ, Real.cos (ξ * (latticeAngle θ u - latticeAngle θ v)) ∂M.gibbs Λ

theorem isBondWeight_bondWeight (Λ : Finset (ℤ × ℤ)) (b : Λ × Λ) :
    IsBondWeight (M.bondWeight Λ b) := by
  unfold bondWeight
  split_ifs
  exacts [M.bond, isBondWeight_one]

theorem isGinibrePair_bondWeight (Λ : Finset (ℤ × ℤ)) (b : Λ × Λ) :
    IsGinibrePair Λ (M.bondWeight Λ b) (M.bondWeight Λ b) := by
  unfold bondWeight
  split_ifs
  exacts [M.pair Λ, isGinibrePair_one]

theorem twoPoint_eq_integral_cos (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    M.twoPoint ξ Λ u v =
      ∫ θ, Real.cos (phase (twoPointFrequency Λ ξ u v) θ) ∂M.gibbs Λ := by
  simp only [twoPoint, phase_twoPointFrequency]

/-- Ginibre I for the two-point function. -/
theorem twoPoint_nonneg (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : 0 ≤ M.twoPoint ξ Λ u v := by
  rw [twoPoint_eq_integral_cos]
  exact integral_cos_pairGibbs_nonneg M.fourier M.mass_ne_zero M.kernel
    (M.isBondWeight_bondWeight Λ) (M.isGinibrePair_bondWeight Λ) _

theorem twoPoint_le_one (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : M.twoPoint ξ Λ u v ≤ 1 := by
  rw [twoPoint_eq_integral_cos]
  exact integral_cos_pairGibbs_le_one M.mass_ne_zero (M.isBondWeight_bondWeight Λ) _

theorem twoPoint_comm (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    M.twoPoint ξ Λ u v = M.twoPoint ξ Λ v u := by
  unfold twoPoint
  congr 1
  funext θ
  rw [← Real.cos_neg]
  congr 1
  ring

/-- **Domain monotonicity.** -/
theorem twoPoint_mono_domain (ξ : ℤ) {Λ Λ' : Finset (ℤ × ℤ)} (hΛ : Λ ⊆ Λ') {u v : ℤ × ℤ}
    (hu : u ∈ Λ) (hv : v ∈ Λ) : M.twoPoint ξ Λ u v ≤ M.twoPoint ξ Λ' u v := by
  classical
  rw [twoPoint_eq_integral_cos, twoPoint_eq_integral_cos]
  let ι : Λ → Λ' := fun x => ⟨x.1, hΛ x.2⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  let w'' : Λ' × Λ' → ℝ → ℝ := fun b =>
    if (b.1 : ℤ × ℤ) ∈ Λ ∧ (b.2 : ℤ × ℤ) ∈ Λ then M.bondWeight Λ' b else fun _ => 1
  have hw'' : ∀ b, IsBondWeight (w'' b) := fun b => by
    simp only [w'']
    split_ifs
    exacts [M.isBondWeight_bondWeight Λ' b, isBondWeight_one]
  have hW : ∀ θ' : Λ' → ℝ, pairWeight (bondFrequency Λ') w'' θ' =
      pairWeight (bondFrequency Λ) (M.bondWeight Λ) (θ' ∘ ι) := fun θ' => by
    simp only [pairWeight, phase_bondFrequency]
    symm
    refine Fintype.prod_of_injective (Prod.map ι ι) (hι.prodMap hι) _ _ (fun b hb => ?_)
      (fun a => ?_)
    · simp only [w'']
      rw [ite_eq_right]
      rintro ⟨h₁, h₂⟩
      exact hb ⟨(⟨b.1, h₁⟩, ⟨b.2, h₂⟩), rfl⟩
    · simp only [w'', Prod.map_fst, Prod.map_snd, ι, Finset.coe_mem, and_self, ite_true,
        Function.comp_apply]
      rfl
  have htransfer := integral_comp_pairGibbs M.mass_ne_zero (M.isBondWeight_bondWeight Λ) hw'' hι hW
    (f := fun θ => Real.cos (phase (twoPointFrequency Λ ξ u v) θ))
    (Real.continuous_cos.comp (continuous_phase _)).measurable
  have hphase : ∀ θ' : Λ' → ℝ, phase (twoPointFrequency Λ ξ u v) (θ' ∘ ι) =
      phase (twoPointFrequency Λ' ξ u v) θ' := fun θ' => by
    rw [phase_twoPointFrequency, phase_twoPointFrequency]
    simp only [latticeAngle, dite_eq_left hu, dite_eq_left hv, dite_eq_left (hΛ hu),
      dite_eq_left (hΛ hv), Function.comp_apply, ι]
  simp only [hphase] at htransfer
  rw [gibbs, gibbs, ← htransfer]
  refine integral_cos_pairGibbs_le M.fourier M.fourier M.mass_ne_zero M.mass_ne_zero M.kernel
    (M.isBondWeight_bondWeight Λ') hw'' (fun b => ?_) _
  simp only [w'']
  split_ifs
  · exact M.isGinibrePair_bondWeight Λ' b
  · unfold bondWeight
    split_ifs
    exacts [M.pair_one Λ', isGinibrePair_one]

/-- **Translation invariance** of the finite-volume two-point function. -/
theorem twoPoint_translate (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v w : ℤ × ℤ) :
    M.twoPoint ξ (translateDomain Λ w) (u + w) (v + w) = M.twoPoint ξ Λ u v := by
  classical
  unfold twoPoint gibbs
  have h := integral_comp_pairGibbs (d := bondFrequency Λ)
    (d' := bondFrequency (translateDomain Λ w)) M.mass_ne_zero (M.isBondWeight_bondWeight Λ)
    (M.isBondWeight_bondWeight (translateDomain Λ w)) (translateEquiv Λ w).injective
    (fun θ' => ?_) (f := fun θ => Real.cos (ξ * (latticeAngle θ u - latticeAngle θ v))) ?_
  · simpa only [latticeAngle_translate] using h
  · have hshift (x y e : ℤ × ℤ) : y + w = x + w + e ↔ y = x + e := by
      rw [add_right_comm, add_left_inj]
    have hbw : ∀ a : Λ × Λ, M.bondWeight (translateDomain Λ w)
        (((translateEquiv Λ w).prodCongr (translateEquiv Λ w)) a) = M.bondWeight Λ a := by
      intro a
      have hiff : LatticeStep ((((translateEquiv Λ w).prodCongr (translateEquiv Λ w)) a).1 :
          ℤ × ℤ) ((((translateEquiv Λ w).prodCongr (translateEquiv Λ w)) a).2 : ℤ × ℤ) ↔
          LatticeStep (a.1 : ℤ × ℤ) (a.2 : ℤ × ℤ) := by
        show LatticeStep ((a.1 : ℤ × ℤ) + w) ((a.2 : ℤ × ℤ) + w) ↔ _
        simp only [LatticeStep, hshift]
      unfold bondWeight
      by_cases h : LatticeStep (a.1 : ℤ × ℤ) (a.2 : ℤ × ℤ)
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]
    simp only [pairWeight, phase_bondFrequency]
    symm
    refine Fintype.prod_equiv ((translateEquiv Λ w).prodCongr (translateEquiv Λ w)) _ _
      (fun a => ?_)
    rw [hbw a]
    rfl
  · exact (Real.continuous_cos.comp (continuous_const.mul
      ((continuous_latticeAngle u).sub (continuous_latticeAngle v)))).measurable

/-! ### The free thermodynamic limit -/

/-- **Existence of the free thermodynamic limit** of the two-point function. -/
theorem exists_tendsto_twoPoint (ξ : ℤ) (u v : ℤ × ℤ) :
    ∃ g : ℝ, Tendsto (fun L : ℕ => M.twoPoint ξ (freeBox L) u v) atTop (𝓝 g) := by
  set L₀ := max (boxRadius u) (boxRadius v)
  have hu (k : ℕ) : u ∈ freeBox (k + L₀) :=
    mem_freeBox_of_boxRadius_le ((le_max_left _ _).trans (Nat.le_add_left _ _))
  have hv (k : ℕ) : v ∈ freeBox (k + L₀) :=
    mem_freeBox_of_boxRadius_le ((le_max_right _ _).trans (Nat.le_add_left _ _))
  have hmono : Monotone fun k : ℕ => M.twoPoint ξ (freeBox (k + L₀)) u v := fun k k' hk =>
    M.twoPoint_mono_domain ξ (freeBox_mono (Nat.add_le_add_right hk _)) (hu k) (hv k)
  have hbdd : BddAbove (Set.range fun k : ℕ => M.twoPoint ξ (freeBox (k + L₀)) u v) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact M.twoPoint_le_one _ _ _ _
  exact ⟨_, (tendsto_add_atTop_iff_nat L₀).mp (tendsto_atTop_ciSup hmono hbdd)⟩

/-- The infinite-volume free two-point function, defined from `exists_tendsto_twoPoint`. -/
def twoPointLimit (ξ : ℤ) (u v : ℤ × ℤ) : ℝ :=
  Classical.choose (M.exists_tendsto_twoPoint ξ u v)

theorem tendsto_twoPointLimit (ξ : ℤ) (u v : ℤ × ℤ) :
    Tendsto (fun L : ℕ => M.twoPoint ξ (freeBox L) u v) atTop (𝓝 (M.twoPointLimit ξ u v)) :=
  Classical.choose_spec (M.exists_tendsto_twoPoint ξ u v)

theorem twoPoint_le_twoPointLimit (ξ : ℤ) {Λ : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} (hu : u ∈ Λ)
    (hv : v ∈ Λ) : M.twoPoint ξ Λ u v ≤ M.twoPointLimit ξ u v := by
  obtain ⟨L₁, hL₁⟩ := exists_subset_freeBox Λ
  refine ge_of_tendsto (M.tendsto_twoPointLimit ξ u v) ?_
  filter_upwards [eventually_ge_atTop L₁] with L hL
  exact M.twoPoint_mono_domain ξ (hL₁.trans (freeBox_mono hL)) hu hv

/-- Independence of the exhausting sequence. -/
theorem tendsto_twoPoint_of_exhaustion (ξ : ℤ) (u v : ℤ × ℤ) {Λs : ℕ → Finset (ℤ × ℤ)}
    (hmono : Monotone Λs) (hexh : ∀ z, ∃ k, z ∈ Λs k) :
    Tendsto (fun k => M.twoPoint ξ (Λs k) u v) atTop (𝓝 (M.twoPointLimit ξ u v)) := by
  have huv : ∀ᶠ k in atTop, u ∈ Λs k ∧ v ∈ Λs k := by
    filter_upwards [eventually_subset_of_exhaustion hmono hexh {u, v}] with k hk
    exact ⟨hk (by simp), hk (by simp)⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL, hL₀⟩ := (((M.tendsto_twoPointLimit ξ u v).eventually
      (lt_mem_nhds ha)).and (eventually_ge_atTop (max (boxRadius u) (boxRadius v)))).exists
    have hu : u ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_left _ _).trans hL₀)
    have hv : v ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_right _ _).trans hL₀)
    filter_upwards [eventually_subset_of_exhaustion hmono hexh (freeBox L)] with k hk
    exact hL.trans_le (M.twoPoint_mono_domain ξ hk hu hv)
  · filter_upwards [huv] with k hk
    exact (M.twoPoint_le_twoPointLimit ξ hk.1 hk.2).trans_lt ha

/-- Translation invariance of the infinite-volume two-point function. -/
theorem twoPointLimit_translate (ξ : ℤ) (u v w : ℤ × ℤ) :
    M.twoPointLimit ξ (u + w) (v + w) = M.twoPointLimit ξ u v := by
  have hmono : Monotone fun k => translateDomain (freeBox k) w := fun k k' hk =>
    Finset.map_subset_map.mpr (freeBox_mono hk)
  have hexh : ∀ z, ∃ k, z ∈ translateDomain (freeBox k) w := fun z =>
    ⟨boxRadius (z - w), mem_translateDomain.mpr (mem_freeBox_of_boxRadius_le le_rfl)⟩
  have h := M.tendsto_twoPoint_of_exhaustion ξ (u + w) (v + w) hmono hexh
  simp only [twoPoint_translate] at h
  exact tendsto_nhds_unique h (M.tendsto_twoPointLimit ξ u v)

theorem twoPointLimit_nonneg (ξ : ℤ) (u v : ℤ × ℤ) : 0 ≤ M.twoPointLimit ξ u v :=
  ge_of_tendsto' (M.tendsto_twoPointLimit ξ u v) fun _ => M.twoPoint_nonneg _ _ _ _

theorem twoPointLimit_le_one (ξ : ℤ) (u v : ℤ × ℤ) : M.twoPointLimit ξ u v ≤ 1 :=
  le_of_tendsto' (M.tendsto_twoPointLimit ξ u v) fun _ => M.twoPoint_le_one _ _ _ _

theorem twoPointLimit_comm (ξ : ℤ) (u v : ℤ × ℤ) : M.twoPointLimit ξ u v = M.twoPointLimit ξ v u := by
  have h := M.tendsto_twoPointLimit ξ u v
  simp only [M.twoPoint_comm ξ _ u v] at h
  exact tendsto_nhds_unique h (M.tendsto_twoPointLimit ξ v u)

end FreeModel

/-! ### Comparison of two models -/

/-- **Comparison of two free models.** If the single-site coefficients of `M₁, M₂` form an
equivalence kernel and `(M₁.w, M₂.w)` is a Ginibre pair, the two-point functions of `M₂` are below
those of `M₁` in every finite domain. -/
theorem FreeModel.twoPoint_le_of_pair (M₁ M₂ : FreeModel) (hK : HasEquivKernel M₁.lam M₂.lam)
    (hpair : ∀ (V : Type) [Fintype V], IsGinibrePair V M₁.w M₂.w) (ξ : ℤ) (Λ : Finset (ℤ × ℤ))
    (u v : ℤ × ℤ) : M₂.twoPoint ξ Λ u v ≤ M₁.twoPoint ξ Λ u v := by
  rw [FreeModel.twoPoint_eq_integral_cos, FreeModel.twoPoint_eq_integral_cos]
  refine integral_cos_pairGibbs_le M₁.fourier M₂.fourier M₁.mass_ne_zero M₂.mass_ne_zero hK
    (M₁.isBondWeight_bondWeight Λ) (M₂.isBondWeight_bondWeight Λ) (fun b => ?_) _
  unfold FreeModel.bondWeight
  split_ifs
  exacts [hpair Λ, isGinibrePair_one]

theorem FreeModel.twoPointLimit_le_of_pair (M₁ M₂ : FreeModel) (hK : HasEquivKernel M₁.lam M₂.lam)
    (hpair : ∀ (V : Type) [Fintype V], IsGinibrePair V M₁.w M₂.w) (ξ : ℤ) (u v : ℤ × ℤ) :
    M₂.twoPointLimit ξ u v ≤ M₁.twoPointLimit ξ u v :=
  le_of_tendsto_of_tendsto' (M₂.tendsto_twoPointLimit ξ u v) (M₁.tendsto_twoPointLimit ξ u v)
    fun _ => FreeModel.twoPoint_le_of_pair M₁ M₂ hK hpair _ _ _ _

end FroehlichSpencer.BKT.Ginibre

end
