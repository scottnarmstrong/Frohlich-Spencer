/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.Normalization
import Mathlib.Tactic

/-!
# The root average of the rooted GFF

The rooted Gaussian free field `gffMeasure G hG β hβ root` has density
`1_{[−π, π)}(φ(root)) e^{−(β/2) E(φ)}`. Its root coordinate is uniform on a period and independent
of the root-relative field.

* `rootSplit`, `measurePreserving_rootSplit`, `integral_eq_integral_glueRoot`: Lebesgue measure on
  `V → ℝ` splits as `ℝ × ({j ≠ root} → ℝ)`.
* **`integral_gffMeasure_rootAverage`**: for bounded measurable `Φ`,
  `E[Φ] = (2π)⁻¹ ∫_{[−π, π)} E[Φ(φ − φ(root) + t)] dt`. The proof translates the non-root
  coordinates by `u − t` inside Fubini and uses the shift invariance of the energy.

The root factor `F_N(φ(root))` of the Fejér weight thus becomes a nonnegative mixture over root
offsets `t`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open MeasureTheory FroehlichSpencer.BKT

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-! ### Splitting off the root coordinate -/

/-- The field with root value `u` and values `y` off the root. -/
def glueRoot (root : V) (u : ℝ) (y : {j // ¬ j = root} → ℝ) : V → ℝ :=
  fun j => if h : j = root then u else y ⟨j, h⟩

/-- The field `φ` re-rooted at the value `t`: `φ − φ(root) + t`. -/
def rerootField (root : V) (t : ℝ) (φ : V → ℝ) : V → ℝ := fun j => φ j - φ root + t

/-- The root splitting `(V → ℝ) ≃ ℝ × ({j ≠ root} → ℝ)`, volume preserving. -/
def rootSplit (root : V) : (V → ℝ) ≃ᵐ ℝ × ({j // ¬ j = root} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => ℝ) (· = root)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique {j // j = root} ℝ)
      (MeasurableEquiv.refl _))

theorem measurePreserving_rootSplit (root : V) :
    MeasurePreserving (rootSplit root) volume volume := by
  unfold rootSplit
  refine MeasurePreserving.trans (volume_preserving_piEquivPiSubtypeProd (fun _ : V => ℝ) _) ?_
  have h := (volume_preserving_funUnique {j // j = root} ℝ).prod
    (MeasurePreserving.id (volume : Measure ({j // ¬ j = root} → ℝ)))
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  convert h using 4
  funext z
  rfl

omit [Fintype V] in
theorem rootSplit_apply (root : V) (φ : V → ℝ) :
    rootSplit root φ = (φ root, fun w : {j // ¬ j = root} => φ w) := rfl

omit [Fintype V] in
theorem rootSplit_symm_apply (root : V) (u : ℝ) (y : {j // ¬ j = root} → ℝ) :
    (rootSplit root).symm (u, y) = glueRoot root u y := by
  rw [MeasurableEquiv.symm_apply_eq, rootSplit_apply]
  refine Prod.ext ?_ ?_
  · simp [glueRoot]
  · funext w
    simp [glueRoot, w.2]

theorem integral_eq_integral_glueRoot (root : V) (F : (V → ℝ) → ℝ) (hF : Integrable F) :
    ∫ φ, F φ = ∫ u, ∫ y, F (glueRoot root u y) := by
  have hmp := measurePreserving_rootSplit root
  have hsymm : MeasurePreserving (rootSplit root).symm volume volume := hmp.symm _
  rw [← hsymm.integral_comp (rootSplit root).symm.measurableEmbedding]
  have hint : Integrable (fun z : ℝ × ({j // ¬ j = root} → ℝ) => F ((rootSplit root).symm z))
      (volume.prod volume) :=
    (hsymm.integrable_comp_emb (rootSplit root).symm.measurableEmbedding).2 hF
  rw [show (volume : Measure (ℝ × ({j // ¬ j = root} → ℝ))) = volume.prod volume from rfl,
    integral_prod _ hint]
  simp only [rootSplit_symm_apply]

/-! ### Shift invariance -/

omit [Fintype V] [DecidableEq V] in
theorem energy_add_const (G : Multigraph V E) (φ : V → ℝ) (c : ℝ) :
    G.energy (fun j => φ j + c) = G.energy φ := by
  unfold Multigraph.energy Multigraph.grad
  congr 1
  funext e
  ring

omit [Fintype V] in
theorem glueRoot_add (root : V) (u : ℝ) (y : {j // ¬ j = root} → ℝ) (c : ℝ) :
    glueRoot root (u + c) (fun w => y w + c) = fun j => glueRoot root u y j + c := by
  funext j
  unfold glueRoot
  split_ifs <;> rfl

omit [Fintype V] in
theorem rerootField_glueRoot (root : V) (t u : ℝ) (y : {j // ¬ j = root} → ℝ) :
    rerootField root t (glueRoot root u y) = glueRoot root t (fun w => y w - u + t) := by
  funext j
  by_cases h : j = root
  · subst h
    simp [rerootField, glueRoot]
  · simp [rerootField, glueRoot, h]

/-! ### The root average of the rooted GFF -/

variable (G : Multigraph V E)

/-- The slice integral `J(t) = ∫ Φ(t, y) e^{-(β/2) E(t, y)} dy` at root value `t`. -/
def rootSlice (β : ℝ) (root : V) (Φ : (V → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ y, Φ (glueRoot root t y) * Real.exp (-(β / 2) * G.energy (glueRoot root t y))

omit [Fintype V] in
theorem gffDensity_glueRoot (β : ℝ) (root : V) (u : ℝ) (y : {j // ¬ j = root} → ℝ) :
    gffDensity G β root (glueRoot root u y) =
      Set.indicator (Set.Ico (-Real.pi) Real.pi) (fun _ => (1 : ℝ)) u *
        Real.exp (-(β / 2) * G.energy (glueRoot root u y)) := by
  unfold gffDensity gffRootWindow
  have hroot : glueRoot root u y root = u := by simp [glueRoot]
  by_cases hu : u ∈ Set.Ico (-Real.pi) Real.pi
  · rw [Set.indicator_of_mem (by simpa [hroot] using hu),
      Set.indicator_of_mem hu, one_mul]
  · rw [Set.indicator_of_notMem (by simpa [hroot] using hu),
      Set.indicator_of_notMem hu, zero_mul]

omit [Fintype V] [DecidableEq V] in
theorem measurable_rerootField (root : V) (t : ℝ) : Measurable (rerootField root t) := by
  unfold rerootField
  fun_prop

/-- The slice of `Φ ρ` at root value `u` is `1_{[−π, π)}(u) J(u)`. -/
theorem integral_slice_eq (β : ℝ) (root : V) (Φ : (V → ℝ) → ℝ) (u : ℝ) :
    ∫ y, Φ (glueRoot root u y) * gffDensity G β root (glueRoot root u y) =
      Set.indicator (Set.Ico (-Real.pi) Real.pi) (fun _ => (1 : ℝ)) u *
        rootSlice G β root Φ u := by
  simp_rw [gffDensity_glueRoot]
  unfold rootSlice
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- The slice of `Φ(re-root at t) ρ` at root value `u` is `1_{[−π, π)}(u) J(t)`: translate the
non-root coordinates by `u − t` and use the shift invariance of the energy. -/
theorem integral_slice_reroot_eq (β : ℝ) (root : V) (Φ : (V → ℝ) → ℝ) (t u : ℝ) :
    ∫ y, Φ (rerootField root t (glueRoot root u y)) *
        gffDensity G β root (glueRoot root u y) =
      Set.indicator (Set.Ico (-Real.pi) Real.pi) (fun _ => (1 : ℝ)) u *
        rootSlice G β root Φ t := by
  set c : {j // ¬ j = root} → ℝ := fun _ => u - t with hc
  rw [← integral_add_right_eq_self _ c]
  have hpt : ∀ z : {j // ¬ j = root} → ℝ,
      Φ (rerootField root t (glueRoot root u (z + c))) *
          gffDensity G β root (glueRoot root u (z + c)) =
        Set.indicator (Set.Ico (-Real.pi) Real.pi) (fun _ => (1 : ℝ)) u *
          (Φ (glueRoot root t z) * Real.exp (-(β / 2) * G.energy (glueRoot root t z))) := by
    intro z
    have h1 : rerootField root t (glueRoot root u (z + c)) = glueRoot root t z := by
      rw [rerootField_glueRoot]
      congr 1
      funext w
      simp only [hc, Pi.add_apply]
      ring
    have h2 : glueRoot root u (z + c) = fun j => glueRoot root t z j + (u - t) := by
      have := glueRoot_add root t z (u - t)
      rw [show t + (u - t) = u by ring] at this
      rw [← this]
      congr 1
    rw [h1, gffDensity_glueRoot, h2, energy_add_const]
    ring
  simp_rw [hpt]
  unfold rootSlice
  rw [integral_const_mul]

/-- **The root average of the rooted GFF.** For a bounded measurable `Φ`, the rooted GFF
expectation of `Φ` is the average over the root window of the expectations of `Φ` evaluated at
the field re-rooted at `t`: `E[Φ] = (2π)⁻¹ ∫_{[−π, π)} E[Φ(φ − φ(root) + t)] dt`. -/
theorem integral_gffMeasure_rootAverage (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V)
    (Φ : (V → ℝ) → ℝ) (hΦm : Measurable Φ) {C : ℝ} (hΦb : ∀ φ, |Φ φ| ≤ C) :
    ∫ φ, Φ φ ∂gffMeasure G hG β hβ root =
      (2 * Real.pi)⁻¹ * ∫ t in Set.Ico (-Real.pi) Real.pi,
        ∫ φ, Φ (rerootField root t φ) ∂gffMeasure G hG β hβ root := by
  have hρ := integrable_gffDensity G hG β hβ root
  have hbdd : ∀ Ψ : (V → ℝ) → ℝ, Measurable Ψ → (∀ φ, |Ψ φ| ≤ C) →
      Integrable (fun φ => Ψ φ * gffDensity G β root φ) := fun Ψ hΨm hΨb =>
    hρ.bdd_mul (c := C) hΨm.aestronglyMeasurable (ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs]; exact hΨb φ)
  have hint0 := hbdd Φ hΦm hΦb
  have hintt : ∀ t, Integrable (fun φ => Φ (rerootField root t φ) * gffDensity G β root φ) :=
    fun t => hbdd _ (hΦm.comp (measurable_rerootField root t)) fun φ => hΦb _
  set Z := gffPartitionFunction G β root with hZ
  have hZpos : 0 < Z := gffPartitionFunction_pos G hG β hβ root
  rw [(gffMeasure_integral_eq_div G hG β hβ root Φ hint0).2]
  have hinner : ∀ t, ∫ φ, Φ (rerootField root t φ) ∂gffMeasure G hG β hβ root =
      2 * Real.pi * rootSlice G β root Φ t / Z := by
    intro t
    rw [(gffMeasure_integral_eq_div G hG β hβ root _ (hintt t)).2,
      integral_eq_integral_glueRoot root _ (hintt t)]
    simp_rw [integral_slice_reroot_eq]
    rw [integral_mul_const, integral_indicator measurableSet_Ico]
    simp
    rw [max_eq_left (by positivity), ← hZ]
    ring
  simp_rw [hinner]
  rw [integral_eq_integral_glueRoot root _ hint0]
  simp_rw [integral_slice_eq]
  have hind : ∀ u, Set.indicator (Set.Ico (-Real.pi) Real.pi) (fun _ => (1 : ℝ)) u *
      rootSlice G β root Φ u =
      Set.indicator (Set.Ico (-Real.pi) Real.pi) (rootSlice G β root Φ) u := by
    intro u
    by_cases hu : u ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hu]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Ico]
  have hconst : ∫ t in Set.Ico (-Real.pi) Real.pi, 2 * Real.pi * rootSlice G β root Φ t / Z =
      2 * Real.pi / Z * ∫ t in Set.Ico (-Real.pi) Real.pi, rootSlice G β root Φ t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  rw [hconst, ← hZ]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
