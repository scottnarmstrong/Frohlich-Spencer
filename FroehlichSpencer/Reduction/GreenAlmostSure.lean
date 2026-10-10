/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Norm
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Surface.GreenFunctionSpec
public import FroehlichSpencer.Surface.LatticeLength
import Mathlib.Analysis.PSeries

/-!
# Borel–Cantelli reduction from T1.2 to almost-sure decay (FS83 abstract)
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.Reduction


section Helpers

private theorem summable_prod_pi (f : ℤ → ℝ) (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    ∀ n : ℕ, Summable (fun x : Fin n → ℤ => ∏ i, f (x i)) := by
  intro n
  induction n with
  | zero => exact .of_finite
  | succ n ih =>
    have h := hf.mul_of_nonneg ih hf0 (fun x => Finset.prod_nonneg fun i _ => hf0 _)
    have h2 : Summable ((fun x : Fin (n + 1) → ℤ => ∏ i, f (x i)) ∘
        (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))) := by
      refine h.congr fun p => ?_
      simp [Fin.prod_univ_succ]
    exact (Equiv.summable_iff _).1 h2

private theorem summable_int_rpow (q : ℝ) (hq : 1 < q) :
    Summable (fun z : ℤ => (1 + |(z : ℝ)|) ^ (-q)) := by
  have hn : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-q)) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -q < -1 by linarith))
    refine this.congr fun n => ?_
    simp [add_comm]
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine hn.congr fun n => ?_
    simp
  · refine hn.congr fun n => ?_
    simp

private theorem abs_le_latticeLength {ν : ℕ} (x : Site ν) (i : Fin ν) :
    |(x i : ℝ)| ≤ latticeLength ν x := by
  unfold latticeLength
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun j : Fin ν => ((x j : ℝ)) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private theorem latticeLength_nonneg {ν : ℕ} (x : Site ν) : 0 ≤ latticeLength ν x :=
  Real.sqrt_nonneg _

private theorem summable_latticeLength (ν : ℕ) (hν : 0 < ν) (p : ℝ) (hp : (ν : ℝ) < p) :
    Summable (fun x : Site ν => (1 + latticeLength ν x) ^ (-p)) := by
  have hνR : (0 : ℝ) < ν := by exact_mod_cast hν
  set q : ℝ := p / ν with hqdef
  have hq : 1 < q := by rw [hqdef, lt_div_iff₀ hνR]; linarith
  have hS := summable_prod_pi _ (fun z : ℤ => Real.rpow_nonneg (by positivity) _)
    (summable_int_rpow q hq) ν
  refine hS.of_nonneg_of_le (fun x => Real.rpow_nonneg (by linarith [latticeLength_nonneg x]) _)
    fun x => ?_
  have hL := latticeLength_nonneg x
  have hprod : ∏ i, (1 + |(x i : ℝ)|) ≤ (1 + latticeLength ν x) ^ ν := by
    calc ∏ i, (1 + |(x i : ℝ)|) ≤ ∏ _i : Fin ν, (1 + latticeLength ν x) := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => by linarith [abs_le_latticeLength x i])
      _ = _ := by simp
  have hpos : 0 < ∏ i, (1 + |(x i : ℝ)|) := Finset.prod_pos fun i _ => by positivity
  calc (1 + latticeLength ν x) ^ (-p)
      = (((1 + latticeLength ν x) ^ ν : ℝ)) ^ (-q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        congr 1
        rw [hqdef]; field_simp
    _ ≤ (∏ i, (1 + |(x i : ℝ)|)) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos hpos hprod (by linarith)
    _ = ∏ i, (1 + |(x i : ℝ)|) ^ (-q) :=
        (Real.finsetProd_rpow _ _ (fun i _ => by positivity) _).symm

private theorem core (ν : ℕ) (hν : 0 < ν) (μ : Measure (Configuration ν))
    [IsProbabilityMeasure μ] (K p : ℝ) (hp : (ν : ℝ) < p) (hK : 0 ≤ K)
    (A : Site ν → Set (Configuration ν))
    (h : ∀ x : Site ν, 1 ≤ latticeLength ν x → MeasurableSet (A x) ∧
      ENNReal.ofReal (1 - K / Real.rpow (latticeLength ν x / 2) p) ≤ μ (A x)) :
    MeasurableSet {v | ∃ R : ℝ, ∀ x : Site ν, R ≤ latticeLength ν x → v ∈ A x} ∧
      μ {v | ∃ R : ℝ, ∀ x : Site ν, R ≤ latticeLength ν x → v ∈ A x} = 1 := by
  have hp0 : 0 < p := by
    have : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
    linarith
  set S : Set (Configuration ν) := {v | ∃ R : ℝ, ∀ x : Site ν, R ≤ latticeLength ν x → v ∈ A x}
    with hSdef
  have hSeq : S = ⋃ n : ℕ, ⋂ x : Site ν, ⋂ (_ : (n : ℝ) + 1 ≤ latticeLength ν x), A x := by
    ext v
    simp only [hSdef, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨R, hR⟩
      obtain ⟨n, hn⟩ := exists_nat_ge R
      exact ⟨n, fun x hx => hR x (by linarith)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n + 1, hn⟩
  have hmeas : MeasurableSet S := by
    rw [hSeq]
    refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun x =>
      MeasurableSet.iInter fun hx => (h x ?_).1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨hmeas, ?_⟩
  -- bad sets
  classical
  let F : Site ν → Set (Configuration ν) := fun x =>
    if 1 ≤ latticeLength ν x then (A x)ᶜ else ∅
  let C : ℝ := K * 4 ^ p
  let b : Site ν → ℝ := fun x => C * (1 + latticeLength ν x) ^ (-p)
  have hbs : Summable b := (summable_latticeLength ν hν p hp).mul_left C
  have hb0 : ∀ x, 0 ≤ b x := fun x => by
    have := latticeLength_nonneg x
    have : 0 ≤ C := by positivity
    positivity
  have hFb : ∀ x, μ (F x) ≤ ENNReal.ofReal (b x) := by
    intro x
    by_cases hx : 1 ≤ latticeLength ν x
    · simp only [F, hx, ↓reduceIte]
      obtain ⟨hm, hlow⟩ := h x hx
      set L := latticeLength ν x with hL
      have hc : μ (A x)ᶜ ≤ ENNReal.ofReal (K / Real.rpow (L / 2) p) := by
        rw [prob_compl_eq_one_sub hm, tsub_le_iff_right]
        have h0 : (0 : ℝ) ≤ K / Real.rpow (L / 2) p := by
          rw [Real.rpow_eq_pow]; positivity
        have hadd := ENNReal.ofReal_add_le (p := 1 - K / Real.rpow (L / 2) p)
          (q := K / Real.rpow (L / 2) p)
        rw [sub_add_cancel, ENNReal.ofReal_one] at hadd
        calc (1 : ENNReal) ≤ _ := hadd
          _ ≤ μ (A x) + ENNReal.ofReal (K / Real.rpow (L / 2) p) := by gcongr
          _ = _ := add_comm _ _
      refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
      have hLpos : 0 < L := by linarith
      have h1 : ((1 + L) / 4) ^ p ≤ (L / 2) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp0.le
      have h4 : 0 < ((1 + L) / 4) ^ p := by positivity
      calc K / Real.rpow (L / 2) p ≤ K / ((1 + L) / 4) ^ p := by
            rw [Real.rpow_eq_pow]
            exact div_le_div_of_nonneg_left hK h4 h1
        _ = b x := by
            simp only [b, C, ← hL]
            rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by positivity)]
            field_simp
    · simp [F, hx]
  have hsum : ∑' x, μ (F x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hFb)
    rw [← ENNReal.ofReal_tsum_of_nonneg hb0 hbs]
    exact ENNReal.ofReal_ne_top
  have hae := ae_finite_setOfPred_mem hsum
  have hS : ∀ᵐ v ∂μ, v ∈ S := by
    filter_upwards [hae] with v hv
    obtain ⟨B, hB⟩ := (hv.image (latticeLength ν)).bddAbove
    refine ⟨|B| + 1, fun x hx => ?_⟩
    have h1 : 1 ≤ latticeLength ν x := by linarith [abs_nonneg B]
    by_contra hvx
    have hmem : x ∈ {x | v ∈ F x} := by
      simp only [Set.mem_ofPred_eq, F, h1, ↓reduceIte]
      exact hvx
    have := hB ⟨x, hmem, rfl⟩
    linarith [le_abs_self B]
  exact (prob_compl_eq_zero_iff hmeas).1 (ae_iff.1 hS)

end Helpers

/--
The exact T1.2 statement, copied binder-for-binder as a proposition for
the conditional Borel–Cantelli reduction.
-/
def T12Statement (ν : ℕ) (hν : 0 < ν) : Prop :=
    ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ) (x : Site ν),
          ∀ (N : ℝ), 0 < N →
            let S : Set (Configuration ν) :=
              {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖greenFunction ν hν
                    ((E : ℂ) + (ε : ℂ) * Complex.I) (by simpa using hε)
                    v (0 : Site ν) x‖ ≤
                  Real.exp (m * (N - latticeLength ν x))}
            ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤
                    configurationMeasure ν law S) ∧
              (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
                highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                    configurationMeasure ν law S)

/--
Conditional Borel–Cantelli reduction from T1.2 to almost-sure exponential
decay.
-/
theorem green_almostSure_decay_of_T12 (ν : ℕ) (hν : 0 < ν) (hT : T12Statement ν hν) :
    ∃ (largeDisorder : ℝ → ℝ) (highEnergy : ℝ → ℝ → ℝ),
      (∀ m, 0 < m → 0 < largeDisorder m) ∧
      (∀ γ m, 0 < γ → 0 < m → 0 < highEnergy γ m) ∧
      ∀ (m : ℝ), 0 < m →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ),
          let S : Set (Configuration ν) :=
            {v | ∃ R : ℝ, ∀ x : Site ν, R ≤ latticeLength ν x →
              ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖greenFunction ν hν
                    ((E : ℂ) + (ε : ℂ) * Complex.I) (by simpa using hε)
                    v (0 : Site ν) x‖ ≤
                  Real.exp (-(m / 2) * latticeLength ν x)}
          ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder m) →
              MeasurableSet S ∧ configurationMeasure ν law S = 1) ∧
            (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
              highEnergy γ m ≤ |E - 2 * (ν : ℝ)| →
              MeasurableSet S ∧ configurationMeasure ν law S = 1) := by
  obtain ⟨LD, HE, Kp, Kg, hLD, hHE, hKp, hKg, hmain⟩ := hT
  have hνR : (0 : ℝ) < ν := by exact_mod_cast hν
  have hp : (ν : ℝ) < (ν : ℝ) + 1 := by linarith
  have hp0 : (0 : ℝ) < (ν : ℝ) + 1 := by linarith
  refine ⟨fun m => LD ((ν : ℝ) + 1) m, fun γ m => HE γ ((ν : ℝ) + 1) m,
    fun m hm => hLD _ m hm hp0, fun γ m hγ hm => hHE γ _ m hγ hm hp0, ?_⟩
  intro m hm law _ E
  dsimp only
  have hexp : ∀ x : Site ν, m * (latticeLength ν x / 2 - latticeLength ν x) =
      -(m / 2) * latticeLength ν x := fun x => by ring
  have hhalf : ∀ x : Site ν, 1 ≤ latticeLength ν x → 0 < latticeLength ν x / 2 :=
    fun x hx => by linarith
  have : IsProbabilityMeasure (configurationMeasure ν law) := by
    unfold configurationMeasure; infer_instance
  let A : Site ν → Set (Configuration ν) := fun x => {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
        ‖greenFunction ν hν ((E : ℂ) + (ε : ℂ) * Complex.I) (by simpa using hε)
          v (0 : Site ν) x‖ ≤ Real.exp (-(m / 2) * latticeLength ν x)}
  refine ⟨fun hbd => ?_, fun γ hγ hlaw hE => ?_⟩
  · obtain ⟨δ, hδ, hδle⟩ := hbd
    refine core ν hν (configurationMeasure ν law) (Kp ((ν : ℝ) + 1)) ((ν : ℝ) + 1) hp
      (hKp _ hp0) A ?_
    intro x hx
    have key := (hmain m _ hm hp0 law E x _ (hhalf x hx)).1 ⟨δ, hδ, hδle⟩
    simp only [hexp] at key
    exact key
  · refine core ν hν (configurationMeasure ν law) (Kg γ ((ν : ℝ) + 1) m) ((ν : ℝ) + 1) hp
      (hKg _ _ _ hγ hm hp0) A ?_
    intro x hx
    have key := (hmain m _ hm hp0 law E x _ (hhalf x hx)).2 γ hγ hlaw hE
    simp only [hexp] at key
    exact key

end FroehlichSpencer.Reduction

end
