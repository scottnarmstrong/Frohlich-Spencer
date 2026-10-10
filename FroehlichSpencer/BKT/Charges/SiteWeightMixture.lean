/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import FroehlichSpencer.BKT.Charges.BasicLemmaIdentity
public import FroehlichSpencer.BKT.Surface.SubGaussian

/-! # The finite site-frequency mixture (KP §4.2.3)

The finite frequency range is indexed by the subtype `1 ≤ q ≤ N`. This is the
finite interpretation required by KP's finite trigonometric-polynomial data. -/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.BKT

/-- The positive Fourier modes available to a polynomial of degree `N`. -/
abbrev SiteMode (N : ℕ) := {q : ℕ // q ∈ Finset.Icc 1 N}

/-- The normalization `C(N) = ∑_{q=1}^N exp(-q²)`. -/
noncomputable def siteModeNormalization (N : ℕ) : ℝ :=
  ∑ q : SiteMode N, Real.exp (-((q.1 : ℝ) ^ 2))

/-- The Gibbs weight assigned to one mode at one site. -/
noncomputable def siteModeWeight (N : ℕ) (q : SiteMode N) : ℝ :=
  Real.exp (-((q.1 : ℝ) ^ 2)) / siteModeNormalization N

/-- The site-dependent coefficient in KP (4.15). -/
noncomputable def siteModeCoefficient (N : ℕ) (hat : ℕ → ℝ)
    (q : SiteMode N) : ℝ :=
  2 * siteModeNormalization N * Real.exp ((q.1 : ℝ) ^ 2) * hat q.1

/-- A finite product choice of one positive Fourier mode at every site. -/
abbrev SiteFrequencyVector {V : Type*} (N : V → ℕ) :=
  ∀ j, SiteMode (N j)

/-- The product convex weight associated to a frequency vector. -/
noncomputable def siteFrequencyWeight {V : Type*} [Fintype V]
    (N : V → ℕ) (q : SiteFrequencyVector N) : ℝ :=
  ∏ j, siteModeWeight (N j) (q j)

/-- The sitewise cosine factor associated to a frequency vector. -/
noncomputable def siteFrequencyFactor {V : Type*} [Fintype V]
    (N : V → ℕ) (hat : V → ℕ → ℝ) (ψ : V → ℝ)
    (q : SiteFrequencyVector N) (j : V) : ℝ :=
  1 + siteModeCoefficient (N j) (hat j) (q j) * Real.cos ((q j).1 * ψ j)

/-- `C(N)` is positive when the polynomial has at least one positive mode. -/
theorem siteModeNormalization_pos {N : ℕ} (hN : 0 < N) :
    0 < siteModeNormalization N := by
  classical
  unfold siteModeNormalization
  apply Finset.sum_pos
  · intro q hq
    positivity
  · refine ⟨⟨1, Finset.mem_Icc.mpr ⟨by omega, hN⟩⟩, ?_⟩
    simp

/-- At a site the mode weights are positive and sum to one. -/
theorem siteModeWeight_positive_sum {N : ℕ} (hN : 0 < N) :
    (∀ q : SiteMode N, 0 < siteModeWeight N q) ∧
      (∑ q : SiteMode N, siteModeWeight N q) = 1 := by
  constructor
  · intro q
    unfold siteModeWeight
    exact div_pos (Real.exp_pos _) (siteModeNormalization_pos hN)
  · unfold siteModeWeight
    simp_rw [div_eq_mul_inv]
    calc
      (∑ q : SiteMode N,
          Real.exp (-((q.1 : ℝ) ^ 2)) * (siteModeNormalization N)⁻¹) =
          (∑ q : SiteMode N, Real.exp (-((q.1 : ℝ) ^ 2))) *
            (siteModeNormalization N)⁻¹ := by rw [← Finset.sum_mul]
      _ = siteModeNormalization N * (siteModeNormalization N)⁻¹ := by rfl
      _ = 1 := mul_inv_cancel₀ (ne_of_gt (siteModeNormalization_pos hN))

/-- One-site weighted expansion of a normalized trigonometric polynomial. -/
theorem siteMode_mixture_eq {N : ℕ} (hN : 0 < N)
    (hat : ℕ → ℝ) (lam : ℝ → ℝ)
    (hlam : ∀ φ, lam φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 N,
      hat q * Real.cos (q * φ)) (φ : ℝ) :
    (∑ q : SiteMode N, siteModeWeight N q *
      (1 + siteModeCoefficient N hat q * Real.cos (q.1 * φ))) = lam φ := by
  classical
  have hC : 0 < siteModeNormalization N := siteModeNormalization_pos hN
  have hsum_modes (f : ℕ → ℝ) :
      (∑ q : SiteMode N, f q.1) = ∑ q ∈ Finset.Icc 1 N, f q := by
    rw [Finset.univ_eq_attach (Finset.Icc 1 N)]
    exact Finset.sum_attach _ _
  have hunit : (∑ q : SiteMode N, siteModeWeight N q) = 1 :=
    (siteModeWeight_positive_sum hN).2
  calc
    _ = ∑ q : SiteMode N,
        (siteModeWeight N q + 2 * hat q.1 * Real.cos (q.1 * φ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold siteModeWeight siteModeCoefficient
      have hexp : Real.exp (-((q.1 : ℝ) ^ 2)) * Real.exp ((q.1 : ℝ) ^ 2) = 1 := by
        rw [← Real.exp_add]
        simp
      field_simp [ne_of_gt hC]
      calc
        Real.exp (-((q.1 : ℝ) ^ 2)) *
            (1 + siteModeNormalization N * 2 * Real.exp ((q.1 : ℝ) ^ 2) *
              hat q.1 * Real.cos (q.1 * φ)) =
            Real.exp (-((q.1 : ℝ) ^ 2)) +
              Real.exp (-((q.1 : ℝ) ^ 2)) *
                (siteModeNormalization N * 2 * Real.exp ((q.1 : ℝ) ^ 2) *
                  hat q.1 * Real.cos (q.1 * φ)) := by ring
        _ = Real.exp (-((q.1 : ℝ) ^ 2)) +
              siteModeNormalization N * 2 * hat q.1 * Real.cos (q.1 * φ) := by
          congr 1
          calc
            Real.exp (-((q.1 : ℝ) ^ 2)) *
                (siteModeNormalization N * 2 * Real.exp ((q.1 : ℝ) ^ 2) *
                  hat q.1 * Real.cos (q.1 * φ)) =
                (Real.exp (-((q.1 : ℝ) ^ 2)) * Real.exp ((q.1 : ℝ) ^ 2)) *
                  (siteModeNormalization N * 2 * hat q.1 * Real.cos (q.1 * φ)) := by ring
            _ = siteModeNormalization N * 2 * hat q.1 * Real.cos (q.1 * φ) := by
              rw [hexp]
              ring
    _ = (∑ q : SiteMode N, siteModeWeight N q) +
        ∑ q : SiteMode N, 2 * hat q.1 * Real.cos (q.1 * φ) := by
      rw [Finset.sum_add_distrib]
    _ = 1 + 2 * ∑ q ∈ Finset.Icc 1 N, hat q * Real.cos (q * φ) := by
      rw [hunit]
      congr 1
      calc
        (∑ q : SiteMode N, 2 * hat q.1 * Real.cos (q.1 * φ)) =
            ∑ q ∈ Finset.Icc 1 N, 2 * (hat q * Real.cos (q * φ)) := by
          calc
            _ = ∑ q : SiteMode N, 2 * (hat q.1 * Real.cos (q.1 * φ)) := by
              apply Finset.sum_congr rfl
              intro q hq
              ring
            _ = _ := hsum_modes (fun q => 2 * (hat q * Real.cos (q * φ)))
        _ = 2 * ∑ q ∈ Finset.Icc 1 N, hat q * Real.cos (q * φ) := by
          rw [← Finset.mul_sum]
    _ = lam φ := (hlam φ).symm

/-- The product mixture (4.14) with the corrected finite frequency range and
site-indexed coefficient (4.15). -/
theorem siteFrequency_mixture_eq {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → ℕ) (hN : ∀ j, 0 < N j) (hat : V → ℕ → ℝ)
    (lam : V → ℝ → ℝ)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (N j),
      hat j q * Real.cos (q * φ)) (ψ : V → ℝ) :
    (∏ j, lam j (ψ j)) =
      ∑ q : SiteFrequencyVector N,
        siteFrequencyWeight N q *
          (∏ j, siteFrequencyFactor N hat ψ q j) := by
  classical
  calc
    (∏ j, lam j (ψ j)) =
        ∏ j, ∑ q : SiteMode (N j),
          siteModeWeight (N j) q *
            (1 + siteModeCoefficient (N j) (hat j) q * Real.cos (q.1 * ψ j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (siteMode_mixture_eq (hN j) (hat j) (lam j) (hlam j) (ψ j)).symm
    _ = ∑ q : SiteFrequencyVector N, ∏ j,
          siteModeWeight (N j) (q j) *
            (1 + siteModeCoefficient (N j) (hat j) (q j) *
              Real.cos ((q j).1 * ψ j)) := Fintype.prod_sum _
    _ = ∑ q : SiteFrequencyVector N,
          siteFrequencyWeight N q *
            (∏ j, siteFrequencyFactor N hat ψ q j) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [siteFrequencyWeight, siteFrequencyFactor]
      rw [Finset.prod_mul_distrib]

/-- The outer frequency weights form a strictly positive probability vector. -/
theorem siteFrequencyWeight_positive_sum {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → ℕ) (hN : ∀ j, 0 < N j) :
    (∀ q : SiteFrequencyVector N, 0 < siteFrequencyWeight N q) ∧
      (∑ q : SiteFrequencyVector N, siteFrequencyWeight N q) = 1 := by
  classical
  constructor
  · intro q
    unfold siteFrequencyWeight
    exact Finset.prod_pos fun j hj =>
      (siteModeWeight_positive_sum (hN j)).1 (q j)
  · unfold siteFrequencyWeight
    have hlocal : ∀ j, (∑ q : SiteMode (N j), siteModeWeight (N j) q) = 1 :=
      fun j => (siteModeWeight_positive_sum (hN j)).2
    calc
      (∑ q : SiteFrequencyVector N, ∏ j, siteModeWeight (N j) (q j)) =
          ∏ j, ∑ q : SiteMode (N j), siteModeWeight (N j) q :=
        (Fintype.prod_sum _).symm
      _ = ∏ j, 1 := by apply Finset.prod_congr rfl; intro j hj; exact hlocal j
      _ = 1 := by simp

/--
The coefficient bound inherited from the sub-Gaussian Fourier
coefficient bound.
-/
theorem siteModeCoefficient_abs_le {Γ η θ β : ℝ} {N : ℕ}
    (hN : 0 < N) (hat : ℕ → ℝ)
    (hhat : ∀ q : ℕ, 1 ≤ q → |hat q| ≤ Γ * Real.exp ((η + θ / β) * q ^ 2))
    (q : SiteMode N) :
    |siteModeCoefficient N hat q| ≤
      2 * siteModeNormalization N * Γ *
        Real.exp ((η + θ / β + 1) * (q.1 : ℝ) ^ 2) := by
  have hC : 0 < siteModeNormalization N := siteModeNormalization_pos hN
  have hq : 1 ≤ q.1 := (Finset.mem_Icc.mp q.2).1
  unfold siteModeCoefficient
  rw [abs_mul, abs_of_pos (show 0 < 2 * siteModeNormalization N *
    Real.exp ((q.1 : ℝ) ^ 2) by positivity)]
  calc
    (2 * siteModeNormalization N * Real.exp ((q.1 : ℝ) ^ 2)) * |hat q.1| ≤
        (2 * siteModeNormalization N * Real.exp ((q.1 : ℝ) ^ 2)) *
          (Γ * Real.exp ((η + θ / β) * q.1 ^ 2)) := by
      gcongr
      exact hhat q.1 hq
    _ = 2 * siteModeNormalization N * Γ *
        Real.exp ((η + θ / β + 1) * (q.1 : ℝ) ^ 2) := by
      calc
        _ = 2 * siteModeNormalization N * Γ *
            (Real.exp ((q.1 : ℝ) ^ 2) *
              Real.exp ((η + θ / β) * (q.1 : ℝ) ^ 2)) := by ring
        _ = 2 * siteModeNormalization N * Γ *
            Real.exp ((q.1 : ℝ) ^ 2 + (η + θ / β) * (q.1 : ℝ) ^ 2) := by
          rw [← Real.exp_add]
        _ = 2 * siteModeNormalization N * Γ *
            Real.exp ((η + θ / β + 1) * (q.1 : ℝ) ^ 2) := by
          congr 2
          ring

/-- A one-site term is the cosine factor of the corresponding point charge. -/
theorem siteFrequencyFactor_eq_pointCharge {L : ℕ}
    (N : (Fin L × Fin L) → ℕ) (hat : (Fin L × Fin L) → ℕ → ℝ)
    (ψ : (Fin L × Fin L) → ℝ) (q : SiteFrequencyVector N)
    (j : Fin L × Fin L) :
    siteFrequencyFactor N hat ψ q j =
      1 + siteModeCoefficient (N j) (hat j) (q j) *
        Real.cos (chargePhase ψ (pointCharge j (q j).1 : ChargeDensity L)) := by
  rw [chargePhase_pointCharge]
  rfl

/-- The finite ensemble of point charges selected by a site-frequency vector. -/
noncomputable def siteFrequencyChargeFamily {L : ℕ}
    (N : (Fin L × Fin L) → ℕ) (q : SiteFrequencyVector N) :
    ChargeEnsemble L :=
  Finset.univ.image fun j => pointCharge j ((q j).1 : ℤ)

/-- A positive frequency vector gives a genuine ensemble of nonzero
single-site charge densities with disjoint supports. -/
theorem siteFrequencyChargeFamily_isEnsemble {L : ℕ}
    (N : (Fin L × Fin L) → ℕ)
    (q : SiteFrequencyVector N) :
    IsBKTEnsemble (siteFrequencyChargeFamily N q) := by
  classical
  have hqpos (j : Fin L × Fin L) : 0 < (q j).1 :=
    (Finset.mem_Icc.mp (q j).2).1
  have hnonzero (j : Fin L × Fin L) : ((q j).1 : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hqpos j))
  have hsupport (j : Fin L × Fin L) :
      Function.support (pointCharge j ((q j).1 : ℤ)) = {j} := by
    ext x
    change pointCharge j ((q j).1 : ℤ) x ≠ 0 ↔ x = j
    by_cases hx : x = j
    · subst x
      simp [pointCharge]
      exact_mod_cast (Nat.ne_of_gt (hqpos j))
    · simp [pointCharge, hx]
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hρ
    intro hzero
    have hv := congrFun hzero j
    simp [pointCharge] at hv
    have hvNat : (q j).1 = 0 := by exact_mod_cast hv
    exact (Nat.ne_of_gt (hqpos j)) hvNat
  · intro ρ hρ σ hσ hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hσ
    have hjk : j ≠ k := by
      intro h
      subst k
      exact hne rfl
    rw [hsupport j, hsupport k]
    exact Set.disjoint_singleton.mpr hjk

/-- Distinct sites give distinct point-charge densities whenever each charge
is nonzero. -/
theorem pointCharge_siteMap_injective {L : ℕ} (q : (Fin L × Fin L) → ℤ)
    (hq : ∀ j, q j ≠ 0) :
    Function.Injective (fun j => pointCharge j (q j)) := by
  intro j k h
  by_contra hjk
  have hval := congrFun h j
  simp [pointCharge, hjk] at hval
  exact hq j hval

/-- The coefficient function on charge densities that encodes the selected
sitewise Fourier modes. It is supported exactly on the single-site family. -/
noncomputable def siteFrequencyChargeCoefficient {L : ℕ}
    (N : (Fin L × Fin L) → ℕ) (hat : (Fin L × Fin L) → ℕ → ℝ)
    (q : SiteFrequencyVector N) : ChargeDensity L → ℝ := fun ρ =>
  ∑ j, if ρ = pointCharge j ((q j).1 : ℤ) then
    siteModeCoefficient (N j) (hat j) (q j) else 0

/-- Evaluating the charge coefficient at a selected point charge recovers its
sitewise Fourier coefficient. -/
theorem siteFrequencyChargeCoefficient_at_site {L : ℕ}
    (N : (Fin L × Fin L) → ℕ) (hat : (Fin L × Fin L) → ℕ → ℝ)
    (q : SiteFrequencyVector N) (j : Fin L × Fin L) :
    siteFrequencyChargeCoefficient N hat q
        (pointCharge j ((q j).1 : ℤ)) =
      siteModeCoefficient (N j) (hat j) (q j) := by
  classical
  have hqpos (i : Fin L × Fin L) : 0 < (q i).1 :=
    (Finset.mem_Icc.mp (q i).2).1
  have hqnonzero (i : Fin L × Fin L) : ((q i).1 : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hqpos i))
  have hinj := pointCharge_siteMap_injective
    (fun i => ((q i).1 : ℤ)) hqnonzero
  unfold siteFrequencyChargeCoefficient
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have heq : pointCharge j ((q j).1 : ℤ) ≠ pointCharge i ((q i).1 : ℤ) := by
      intro heq
      exact hij (hinj heq.symm)
    simp [heq]
  · simp

/-- The product over the point-charge ensemble is precisely the product of
sitewise factors in (4.14). -/
theorem siteFrequencyChargeProduct_eq {L : ℕ}
    (N : (Fin L × Fin L) → ℕ) (hat : (Fin L × Fin L) → ℕ → ℝ)
    (ψ : (Fin L × Fin L) → ℝ) (q : SiteFrequencyVector N) :
    chargeFactorProduct (siteFrequencyChargeFamily N q)
        (siteFrequencyChargeCoefficient N hat q) ψ =
      ∏ j, siteFrequencyFactor N hat ψ q j := by
  classical
  have hqnonzero (j : Fin L × Fin L) : ((q j).1 : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((Finset.mem_Icc.mp (q j).2).1))
  have hinj := pointCharge_siteMap_injective
    (fun j => ((q j).1 : ℤ)) hqnonzero
  unfold chargeFactorProduct siteFrequencyChargeFamily
  rw [Finset.prod_image hinj.injOn]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [chargeFactor, siteFrequencyChargeCoefficient_at_site,
    siteFrequencyFactor_eq_pointCharge]

/--
Every  sub-Gaussian polynomial supplies finite site-mixture data.
-/
theorem exists_siteMixtureData {V : Type*}
    (Γ η θ β : ℝ) (lam : V → ℝ → ℝ)
    (hlam : ∀ j, IsSubGaussian Γ η θ β (lam j)) :
    ∃ N : V → ℕ, (∀ j, 0 < N j) ∧
      ∃ hat : V → ℕ → ℝ,
        (∀ j q, N j < q → hat j q = 0) ∧
        (∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (N j),
          hat j q * Real.cos (q * φ)) ∧
        (∀ j q, 1 ≤ q → |hat j q| ≤ Γ * Real.exp ((η + θ / β) * q ^ 2)) := by
  classical
  choose N hN hat htail hrepr hbound using hlam
  exact ⟨N, hN, hat, htail, hrepr, hbound⟩

/--
The finite convex-mixture equation and all sitewise coefficient bounds
follow directly from the sub-Gaussian witnesses.
-/
theorem subGaussian_siteFrequency_mixture {V : Type*} [Fintype V] [DecidableEq V]
    (Γ η θ β : ℝ) (lam : V → ℝ → ℝ)
    (hlam : ∀ j, IsSubGaussian Γ η θ β (lam j)) :
    ∃ N : V → ℕ, ∃ hat : V → ℕ → ℝ,
      (∀ j, 0 < N j) ∧
      (∀ j q, N j < q → hat j q = 0) ∧
      (∀ ψ : V → ℝ, ∏ j, lam j (ψ j) =
        ∑ q : SiteFrequencyVector N,
          siteFrequencyWeight N q * (∏ j, siteFrequencyFactor N hat ψ q j)) ∧
      (∀ q : SiteFrequencyVector N, 0 < siteFrequencyWeight N q) ∧
      (∑ q : SiteFrequencyVector N, siteFrequencyWeight N q) = 1 ∧
      (∀ j (q : SiteMode (N j)),
        |siteModeCoefficient (N j) (hat j) q| ≤
          2 * siteModeNormalization (N j) * Γ *
            Real.exp ((η + θ / β + 1) * (q.1 : ℝ) ^ 2)) := by
  classical
  obtain ⟨N, hN, hat, htail, hrepr, hbound⟩ :=
    exists_siteMixtureData Γ η θ β lam hlam
  refine ⟨N, hat, hN, htail, ?_, ?_, ?_, ?_⟩
  · intro ψ
    exact siteFrequency_mixture_eq N hN hat lam hrepr ψ
  · exact (siteFrequencyWeight_positive_sum N hN).1
  · exact (siteFrequencyWeight_positive_sum N hN).2
  · intro j q
    exact siteModeCoefficient_abs_le (hN j) (hat j) (hbound j) q

/-- The finite sub-Gaussian mixture written directly as charge-factor products
over ensembles of single-site densities. -/
theorem subGaussian_siteChargeProduct_mixture {L : ℕ}
    (Γ η θ β : ℝ) (lam : (Fin L × Fin L) → ℝ → ℝ)
    (hlam : ∀ j, IsSubGaussian Γ η θ β (lam j)) :
    ∃ N : (Fin L × Fin L) → ℕ, ∃ hat : (Fin L × Fin L) → ℕ → ℝ,
      (∀ j, 0 < N j) ∧
      (∀ j q, N j < q → hat j q = 0) ∧
      (∀ ψ, ∏ j, lam j (ψ j) =
        ∑ q : SiteFrequencyVector N,
          siteFrequencyWeight N q *
            chargeFactorProduct (siteFrequencyChargeFamily N q)
              (siteFrequencyChargeCoefficient N hat q) ψ) ∧
      (∀ q : SiteFrequencyVector N, 0 < siteFrequencyWeight N q) ∧
      (∑ q : SiteFrequencyVector N, siteFrequencyWeight N q) = 1 ∧
      (∀ j (q : SiteMode (N j)),
        |siteModeCoefficient (N j) (hat j) q| ≤
          2 * siteModeNormalization (N j) * Γ *
            Real.exp ((η + θ / β + 1) * (q.1 : ℝ) ^ 2)) := by
  classical
  obtain ⟨N, hat, hN, htail, hmix, hweight, hsum, hbound⟩ :=
    subGaussian_siteFrequency_mixture Γ η θ β lam hlam
  refine ⟨N, hat, hN, htail, ?_, hweight, hsum, hbound⟩
  intro ψ
  rw [hmix ψ]
  apply Finset.sum_congr rfl
  intro q hq
  rw [siteFrequencyChargeProduct_eq]

end FroehlichSpencer.BKT

end
