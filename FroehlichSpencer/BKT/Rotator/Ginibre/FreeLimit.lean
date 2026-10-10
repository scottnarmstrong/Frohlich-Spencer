/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.Lattice
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The free thermodynamic limit of the plane-rotator two-point function

FS81, J p. 533: "The thermodynamic limit `⟨-⟩(β)` of the states `{⟨·⟩_Λ(β)}` is known to exist, a
consequence of correlation inequalities [11]" (Ginibre). For the two-point functions this is proved
here for every `β ≥ 0` and integer `ξ`: along the centered squares `[-L, L]²` the free-boundary
two-point function `⟨cos(ξ(θ_u - θ_v))⟩` is eventually nondecreasing (domain monotonicity) and
bounded by `1`, so it converges. The limit is defined only through this proved convergence. It
dominates every finite-volume value, is the limit along every increasing exhausting sequence of
finite domains (independence of `{Λ}`, J p. 535), and is translation invariant.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

/-- The centered square `[-L, L]²` of `ℤ²`. -/
def freeBox (L : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L

/-- The sup-norm radius of a point of `ℤ²`. -/
def boxRadius (z : ℤ × ℤ) : ℕ :=
  max z.1.natAbs z.2.natAbs

theorem mem_freeBox {L : ℕ} {z : ℤ × ℤ} : z ∈ freeBox L ↔ -(L : ℤ) ≤ z.1 ∧ z.1 ≤ L ∧
    -(L : ℤ) ≤ z.2 ∧ z.2 ≤ L := by
  simp only [freeBox, Finset.mem_product, Finset.mem_Icc, and_assoc]

theorem mem_freeBox_of_boxRadius_le {L : ℕ} {z : ℤ × ℤ} (h : boxRadius z ≤ L) :
    z ∈ freeBox L := by
  have h₁ : z.1.natAbs ≤ L := (le_max_left _ _).trans h
  have h₂ : z.2.natAbs ≤ L := (le_max_right _ _).trans h
  rw [mem_freeBox]
  omega

theorem freeBox_mono : Monotone freeBox := by
  intro L L' h z hz
  rw [mem_freeBox] at hz ⊢
  have : (L : ℤ) ≤ L' := by exact_mod_cast h
  omega

theorem exists_subset_freeBox (Λ : Finset (ℤ × ℤ)) : ∃ L, Λ ⊆ freeBox L :=
  ⟨Λ.sup boxRadius, fun _ hz => mem_freeBox_of_boxRadius_le (Finset.le_sup hz)⟩

/-- **Existence of the free thermodynamic limit** of the two-point function. -/
theorem exists_tendsto_freeTwoPoint {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) :
    ∃ g : ℝ, Tendsto (fun L : ℕ => freeTwoPoint β ξ (freeBox L) u v) atTop (𝓝 g) := by
  set L₀ := max (boxRadius u) (boxRadius v)
  have hu (k : ℕ) : u ∈ freeBox (k + L₀) :=
    mem_freeBox_of_boxRadius_le ((le_max_left _ _).trans (Nat.le_add_left _ _))
  have hv (k : ℕ) : v ∈ freeBox (k + L₀) :=
    mem_freeBox_of_boxRadius_le ((le_max_right _ _).trans (Nat.le_add_left _ _))
  have hmono : Monotone fun k : ℕ => freeTwoPoint β ξ (freeBox (k + L₀)) u v := fun k k' hk =>
    freeTwoPoint_mono_domain hβ ξ (freeBox_mono (Nat.add_le_add_right hk _)) (hu k) (hv k)
  have hbdd : BddAbove (Set.range fun k : ℕ => freeTwoPoint β ξ (freeBox (k + L₀)) u v) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact freeTwoPoint_le_one _ _ _ _ _
  exact ⟨_, (tendsto_add_atTop_iff_nat L₀).mp (tendsto_atTop_ciSup hmono hbdd)⟩

/-- The infinite-volume free two-point function `⟨cos(ξ(θ_u - θ_v))⟩(β)`, `β ≥ 0`, defined as the
limit whose existence is `exists_tendsto_freeTwoPoint`. -/
def freeTwoPointLimit (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) : ℝ :=
  Classical.choose (exists_tendsto_freeTwoPoint hβ ξ u v)

/-- Characterization: the finite-volume two-point functions on the centered squares converge to
`freeTwoPointLimit`. -/
theorem tendsto_freeTwoPointLimit {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) :
    Tendsto (fun L : ℕ => freeTwoPoint β ξ (freeBox L) u v) atTop
      (𝓝 (freeTwoPointLimit β hβ ξ u v)) :=
  Classical.choose_spec (exists_tendsto_freeTwoPoint hβ ξ u v)

/-- Every finite-volume free two-point function is a lower bound for the limit. -/
theorem freeTwoPoint_le_freeTwoPointLimit {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) {Λ : Finset (ℤ × ℤ)}
    {u v : ℤ × ℤ} (hu : u ∈ Λ) (hv : v ∈ Λ) :
    freeTwoPoint β ξ Λ u v ≤ freeTwoPointLimit β hβ ξ u v := by
  obtain ⟨L₁, hL₁⟩ := exists_subset_freeBox Λ
  refine ge_of_tendsto (tendsto_freeTwoPointLimit hβ ξ u v) ?_
  filter_upwards [eventually_ge_atTop L₁] with L hL
  exact freeTwoPoint_mono_domain hβ ξ (hL₁.trans (freeBox_mono hL)) hu hv

/-- An increasing sequence of finite domains exhausting `ℤ²` eventually contains every finite
set. -/
theorem eventually_subset_of_exhaustion {Λs : ℕ → Finset (ℤ × ℤ)} (hmono : Monotone Λs)
    (hexh : ∀ z, ∃ k, z ∈ Λs k) (Λ : Finset (ℤ × ℤ)) : ∀ᶠ k in atTop, Λ ⊆ Λs k := by
  classical
  choose K hK using hexh
  filter_upwards [eventually_ge_atTop (Λ.sup K)] with k hk z hz
  exact hmono ((Finset.le_sup hz).trans hk) (hK z)

/-- **Independence of the exhausting sequence.** Along every increasing sequence of finite domains
exhausting `ℤ²`, the free two-point functions converge to `freeTwoPointLimit`. -/
theorem tendsto_freeTwoPoint_of_exhaustion {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ)
    {Λs : ℕ → Finset (ℤ × ℤ)} (hmono : Monotone Λs) (hexh : ∀ z, ∃ k, z ∈ Λs k) :
    Tendsto (fun k => freeTwoPoint β ξ (Λs k) u v) atTop (𝓝 (freeTwoPointLimit β hβ ξ u v)) := by
  have huv : ∀ᶠ k in atTop, u ∈ Λs k ∧ v ∈ Λs k := by
    filter_upwards [eventually_subset_of_exhaustion hmono hexh {u, v}] with k hk
    exact ⟨hk (by simp), hk (by simp)⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL, hL₀⟩ := (((tendsto_freeTwoPointLimit hβ ξ u v).eventually
      (lt_mem_nhds ha)).and (eventually_ge_atTop (max (boxRadius u) (boxRadius v)))).exists
    have hu : u ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_left _ _).trans hL₀)
    have hv : v ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_right _ _).trans hL₀)
    filter_upwards [eventually_subset_of_exhaustion hmono hexh (freeBox L)] with k hk
    exact hL.trans_le (freeTwoPoint_mono_domain hβ ξ hk hu hv)
  · filter_upwards [huv] with k hk
    exact (freeTwoPoint_le_freeTwoPointLimit hβ ξ hk.1 hk.2).trans_lt ha

/-- **Translation invariance** of the infinite-volume two-point function. -/
theorem freeTwoPointLimit_translate {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v w : ℤ × ℤ) :
    freeTwoPointLimit β hβ ξ (u + w) (v + w) = freeTwoPointLimit β hβ ξ u v := by
  have hmono : Monotone fun k => translateDomain (freeBox k) w := fun k k' hk =>
    Finset.map_subset_map.mpr (freeBox_mono hk)
  have hexh : ∀ z, ∃ k, z ∈ translateDomain (freeBox k) w := fun z =>
    ⟨boxRadius (z - w), mem_translateDomain.mpr (mem_freeBox_of_boxRadius_le le_rfl)⟩
  have h := tendsto_freeTwoPoint_of_exhaustion hβ ξ (u + w) (v + w) hmono hexh
  simp only [freeTwoPoint_translate] at h
  exact tendsto_nhds_unique h (tendsto_freeTwoPointLimit hβ ξ u v)

theorem freeTwoPointLimit_nonneg {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) :
    0 ≤ freeTwoPointLimit β hβ ξ u v :=
  ge_of_tendsto' (tendsto_freeTwoPointLimit hβ ξ u v) fun _ => freeTwoPoint_nonneg hβ _ _ _ _

theorem freeTwoPointLimit_le_one {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ ξ u v ≤ 1 :=
  le_of_tendsto' (tendsto_freeTwoPointLimit hβ ξ u v) fun _ => freeTwoPoint_le_one _ _ _ _ _

theorem freeTwoPointLimit_comm {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ ξ u v = freeTwoPointLimit β hβ ξ v u := by
  have h := tendsto_freeTwoPointLimit hβ ξ u v
  simp only [freeTwoPoint_comm β ξ _ u v] at h
  exact tendsto_nhds_unique h (tendsto_freeTwoPointLimit hβ ξ v u)

theorem freeTwoPointLimit_self {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u : ℤ × ℤ) :
    freeTwoPointLimit β hβ ξ u u = 1 := by
  have h := tendsto_freeTwoPointLimit hβ ξ u u
  simp only [freeTwoPoint_self] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The infinite-volume two-point function is nondecreasing in `β`. -/
theorem freeTwoPointLimit_mono_beta {β β' : ℝ} (hβ : 0 ≤ β) (hββ' : β ≤ β') (ξ : ℤ)
    (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ ξ u v ≤ freeTwoPointLimit β' (hβ.trans hββ') ξ u v :=
  le_of_tendsto_of_tendsto' (tendsto_freeTwoPointLimit hβ ξ u v)
    (tendsto_freeTwoPointLimit (hβ.trans hββ') ξ u v)
    fun _ => freeTwoPoint_mono_beta hβ hββ' _ _ _ _

end FroehlichSpencer.BKT.Rotator.Ginibre

end
