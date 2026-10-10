/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Transform
public import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Averaging Stieltjes transforms over a kernel

For a probability measure `P` on `Ω` and a finite kernel `κ : Kernel Ω ℝ`, the Stieltjes transform
of the averaged measure `P.bind κ` is the `P`-average of the transforms `stieltjes (κ ω) z`, the
mass of the average is the average mass, and almost-sure convergence of the transforms with
uniformly bounded masses gives convergence of the averaged transforms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set

namespace FroehlichSpencer.Infra

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem isFiniteMeasure_bind (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ)
    [IsFiniteKernel κ] : IsFiniteMeasure (P.bind κ) := by
  obtain ⟨C, hC, hCle⟩ := IsFiniteKernel.exists_univ_le (κ := κ)
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable κ)]
  calc ∫⁻ ω, κ ω univ ∂P ≤ ∫⁻ _, C ∂P := lintegral_mono fun ω => hCle ω
    _ = C := by simp
    _ < ⊤ := hC

private theorem integral_bind_aux (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : Integrable f (P.bind κ)) : ∫ t, f t ∂(P.bind κ) = ∫ ω, ∫ t, f t ∂κ ω ∂P := by
  have h := Kernel.integral_comp (η := κ) (κ := Kernel.const Unit P) (a := ()) (f := f)
    (by simpa [Kernel.comp_apply, Kernel.const_apply] using hf)
  simpa [Kernel.comp_apply, Kernel.const_apply] using h

theorem stieltjes_bind (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ)
    [IsFiniteKernel κ] {z : ℂ} (hz : 0 < z.im) :
    stieltjes (P.bind κ) z = ∫ ω, stieltjes (κ ω) z ∂P := by
  have := isFiniteMeasure_bind P κ
  exact integral_bind_aux P κ (integrable_inv_ofReal_sub _ hz)

theorem measureReal_bind_univ (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ)
    [IsFiniteKernel κ] : (P.bind κ).real univ = ∫ ω, (κ ω).real univ ∂P := by
  have := isFiniteMeasure_bind P κ
  have h := integral_bind_aux P κ (f := fun _ => (1 : ℝ)) (integrable_const _)
  simpa using h

theorem tendsto_stieltjes_bind (P : Measure Ω) [IsProbabilityMeasure P] {κs : ℕ → Kernel Ω ℝ}
    [∀ n, IsFiniteKernel (κs n)] {M : ℝ} (hM : ∀ n ω, (κs n ω).real univ ≤ M)
    {μ : Measure ℝ} [IsFiniteMeasure μ] {z : ℂ} (hz : 0 < z.im)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => stieltjes (κs n ω) z) atTop (𝓝 (stieltjes μ z))) :
    Tendsto (fun n => stieltjes (P.bind (κs n)) z) atTop (𝓝 (stieltjes μ z)) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => stieltjes (κs n ω) z) P := fun n =>
    (StronglyMeasurable.integral_kernel (κ := κs n)
      (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
      (Complex.measurable_ofReal.sub_const z).inv.stronglyMeasurable).aestronglyMeasurable
  simp_rw [stieltjes_bind P _ hz]
  have := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun n ω => stieltjes (κs n ω) z) (f := fun _ => stieltjes μ z)
    (fun _ => M / z.im) hmeas (integrable_const _)
    (fun n => Eventually.of_forall fun ω => by
      have : IsFiniteMeasure (κs n ω) := inferInstance
      exact (norm_stieltjes_le (κs n ω) hz).trans
        (div_le_div_of_nonneg_right (hM n ω) hz.le)) h
  simpa using this

end FroehlichSpencer.Infra
