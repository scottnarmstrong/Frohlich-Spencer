/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryGreen
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGGeometry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerMixture
import Mathlib.Tactic

/-!
A marked term of the rooted Fejér
branch `N` has the real composite `σ = ξ ϱ₀ + ϱ^𝒩` (`rootedMarkedComposite`), with the dipole
mark `ϱ₀` (`rootedDipoleMark`) and the integer satellite `ϱ^𝒩 = ∑_T m − ∑_{C ∖ T} m`
(`rootedMarkedSatellite`).

Its integer proxy is `p = ϱ₀ + 2 ϱ^𝒩` (`rootedMarkedProxy`).

This
file fixes the proxy, the face support `X(C)` of the composite (`rootedMarkedSupport`), the
Appendix D adjacency of the marked clusters (`RootedMarkAdjacent`) and the extended ensemble
`rem(C) ∪ {p}` (`rootedMarkedExtension`).

It proves:
* the elementary facts: neutrality, root neutralization, the pointwise support equivalence of
  `σ` and `p`, and the patch-charge transfer from `p` to `σ`;
* the exact statements of the two Appendix D results, as the Props
  `RootedMarkedExtensionGeometry` and `RootedMarkedChargedSplit`.

They are proved in
  `MarkedGeometryProxyCut.lean` as `rootedMarkedExtensionGeometry_holds` (`0 < M`, `0 ≤ α`,
  `0 < n`) and `rootedMarkedChargedSplit_holds` (`1 < M`, `1 ≤ α`, `0 < n`).

That file also
  has `hasFarConstituentCharge_of_mem_rootedMarkedExtension` and the monotonicity
  `rootedMarkAdjacent_monotone`.

## Differences from the design note

1. **Support equivalence without hypotheses.** `σ j ≠ 0 ↔ p j ≠ 0` holds at every face,
   including the root, for `0 < ξ < 1` alone (`rootedMarkedComposite_ne_zero_iff_proxy`):
   - off the mark both are `k` and `2k` for the integer satellite value `k`;
   - on the mark they are `±ξ + k` and `±1 + 2k`.

The design-note signature `rootedMarkedProxy_ne_zero_iff` is kept as written, with its
   unnecessary hypotheses `_hn0`, `_hT`, `_hdisj` unused.

Its `hdisj` (disjoint supports on all
   faces) would fail on branch ensembles with two boundary-charged members, which both charge the
   root.

The identification of the face support with `X(C)`
   (`chargeSupport_siteRestrict_rootedMarkedProxy`) assumes disjoint **face** supports, which
   every Appendix D branch ensemble has.
2. **Adjacency and scale.** `RootedMarkAdjacent M α ϱ C` is
   `dist(supp ϱ|faces, X(C)) < M · min(d_Λ(ϱ|faces), D(C))^α`, with Euclidean distance and
   Appendix D's `d_Λ = boundaryAdjustedSize`.

The cluster size is:
   - `D(C) = diam X(C)` when every member of `C` is face-neutral;
   - `D(C) = max(d_bdry(mark), diam X(C))` otherwise (`rootedClusterSize`).

`D` is monotone in `C` and dominates `d_Λ(p|faces)` for every orientation `T`.

It never uses
   the wired graph metric.
3. **The charged split is the charged half of Appendix D isolation, on boundary-far parts.**
   Members of a branch can be face-charged; the boundary absorbs their charge.

So the
   cut lemma for a part `A = X(C) ∩ S` with `B = X(C) ∖ S` assumes:
   - Appendix D's isolation trigger `2M diam(A)^α ≤ dist(A, B)`;
   - the boundary-far premise `diam(A) < M d_bdry(A)^α`.

It concludes `|σ(A)| ≥ min(ξ, 1 − ξ)` and `p(A) ≠ 0`.

For the proxy this gives only the charged
   half of `HasBoundaryIsolation` on boundary-far constituents (`HasFarConstituentCharge`).

The
   boundary-close half of the isolation clause is not claimed for the proxy.

Selected squares
   (`pinnedPPrime`) are boundary-far: `d_bdry(s) ≥ 2^{j+2}`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges (euclideanSetDistance euclideanSetDiameter
  euclideanBoundaryDistance boundaryAdjustedSize totalCharge chargeEuclideanDiameter
  chargeBoundaryDistance IsConstituent IsPinnedChargeEnsemble IsBoundarySeparated
  AppendixDChargeGeometry neutralizeAtWiredRoot)

/-! ### The satellite -/

section Satellite

variable {V : Type} [Fintype V]

/-- The signed integer satellite `ϱ^𝒩 = ∑_{m ∈ T} m − ∑_{m ∈ C ∖ T} m` of an oriented
cluster. -/
def rootedMarkedSatellite (C T : Finset (V → ℤ)) : V → ℤ :=
  fun j => ∑ m ∈ T, m j - ∑ m ∈ C \ T, m j

/-- The real composite is the fractional mark plus the integer satellite. -/
theorem rootedMarkedComposite_eq (ξ : ℝ) (ρ₀ : V → ℤ) (C T : Finset (V → ℤ)) (j : V) :
    rootedMarkedComposite ξ ρ₀ C T j = ξ * (ρ₀ j : ℝ) + (rootedMarkedSatellite C T j : ℝ) := by
  unfold rootedMarkedComposite rootedMarkedSatellite
  push_cast
  ring

/-- The satellite of a neutral cluster is neutral. -/
theorem sum_rootedMarkedSatellite {C T : Finset (V → ℤ)} (hC : ∀ m ∈ C, ∑ j, m j = 0)
    (hT : T ⊆ C) : ∑ j, rootedMarkedSatellite C T j = 0 := by
  unfold rootedMarkedSatellite
  rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := C \ T),
    Finset.sum_eq_zero (fun m hm => hC m (hT hm)),
    Finset.sum_eq_zero (fun m hm => hC m (Finset.mem_sdiff.1 hm).1), sub_zero]

/-- The satellite vanishes where every cluster member vanishes. -/
theorem rootedMarkedSatellite_eq_zero {C T : Finset (V → ℤ)} (hT : T ⊆ C) {j : V}
    (h : ∀ m ∈ C, m j = 0) : rootedMarkedSatellite C T j = 0 := by
  unfold rootedMarkedSatellite
  rw [Finset.sum_eq_zero fun m hm => h m (hT hm),
    Finset.sum_eq_zero fun m hm => h m (Finset.mem_sdiff.1 hm).1, sub_zero]

/-- Where only the member `m` of the cluster is nonzero, the satellite is `± m`. -/
theorem rootedMarkedSatellite_eq_of_unique {C T : Finset (V → ℤ)} (hT : T ⊆ C) {m : V → ℤ}
    (hm : m ∈ C) {j : V} (h : ∀ m' ∈ C, m' ≠ m → m' j = 0) :
    rootedMarkedSatellite C T j = if m ∈ T then m j else -m j := by
  have hsum : ∀ U ⊆ C, ∑ m' ∈ U, m' j = if m ∈ U then m j else 0 := by
    intro U hU
    rw [Finset.sum_congr rfl fun m' hm' => (show m' j = if m' = m then m j else 0 by
      split_ifs with h'
      · rw [h']
      · exact h m' (hU hm') h'), Finset.sum_ite_eq']
  unfold rootedMarkedSatellite
  rw [hsum T hT, hsum (C \ T) Finset.sdiff_subset]
  by_cases hmT : m ∈ T
  · have h' : m ∉ C \ T := fun h' => (Finset.mem_sdiff.1 h').2 hmT
    simp [hmT, h']
  · have h' : m ∈ C \ T := Finset.mem_sdiff.2 ⟨hm, hmT⟩
    simp [hmT, h']

end Satellite

/-! ### The dipole mark -/

section Mark

theorem rootedCenter_ne_axialSite {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n) :
    center R ≠ axialSite R n hn := by
  intro h
  have hf := congrArg Prod.fst h
  simp [center, axialSite] at hf
  omega

@[simp] theorem rootedDipoleMark_none (R n : ℕ) (hn : n ≤ R) :
    rootedDipoleMark R n hn none = 0 := by
  simp [rootedDipoleMark]

theorem rootedDipoleMark_center (R n : ℕ) (hn : n ≤ R) :
    rootedDipoleMark R n hn (some (center R)) = 1 := by
  simp [rootedDipoleMark]

theorem rootedDipoleMark_axial {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n) :
    rootedDipoleMark R n hn (some (axialSite R n hn)) = -1 := by
  have h : axialSite R n hn ≠ center R := fun h => rootedCenter_ne_axialSite hn hn0 h.symm
  simp [rootedDipoleMark, h]

theorem rootedDipoleMark_some_of_ne {R n : ℕ} (hn : n ≤ R) {x : Site R} (hc : x ≠ center R)
    (ha : x ≠ axialSite R n hn) : rootedDipoleMark R n hn (some x) = 0 := by
  simp [rootedDipoleMark, hc, ha]

/-- The mark takes the values `1`, `−1` and `0`. -/
theorem rootedDipoleMark_cases (R n : ℕ) (hn : n ≤ R) (j : RotatorDualFace (sideLength R)) :
    rootedDipoleMark R n hn j = 1 ∨ rootedDipoleMark R n hn j = -1 ∨
      rootedDipoleMark R n hn j = 0 := by
  unfold rootedDipoleMark
  split_ifs <;> simp

/-- The mark is `±1` on its two faces. -/
theorem rootedDipoleMark_of_mem_sites {R n : ℕ} (hn : n ≤ R) {x : Site R}
    (hx : x = center R ∨ x = axialSite R n hn) :
    rootedDipoleMark R n hn (some x) = 1 ∨ rootedDipoleMark R n hn (some x) = -1 := by
  unfold rootedDipoleMark
  rcases hx with rfl | rfl <;> split_ifs <;> simp_all

/-- The mark charge of a set of faces: `𝟙[center ∈ S] − 𝟙[axial ∈ S]`. -/
theorem sum_rootedDipoleMark_some {R n : ℕ} (hn : n ≤ R) (hn0 : 0 < n) (S : Finset (Site R)) :
    ∑ x ∈ S, rootedDipoleMark R n hn (some x) =
      (if center R ∈ S then 1 else 0) - (if axialSite R n hn ∈ S then 1 else 0) := by
  have hpt : ∀ x : Site R, rootedDipoleMark R n hn (some x) =
      (if x = center R then 1 else 0) - (if x = axialSite R n hn then 1 else 0) := by
    intro x
    by_cases hc : x = center R
    · subst hc
      simp [rootedDipoleMark, rootedCenter_ne_axialSite hn hn0]
    · by_cases ha : x = axialSite R n hn
      · subst ha
        simp [rootedDipoleMark, hc]
      · simp [rootedDipoleMark, hc, ha]
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']

end Mark

/-! ### The proxy -/

section Proxy

variable {R n : ℕ}

/-- The integer proxy `ϱ₀ + 2 ϱ^𝒩` of the rooted marked composite `ξ ϱ₀ + ϱ^𝒩`. -/
def rootedMarkedProxy (R n : ℕ) (hn : n ≤ R)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    RotatorDualFace (sideLength R) → ℤ :=
  fun j => rootedDipoleMark R n hn j + 2 * rootedMarkedSatellite C T j

theorem siteRestrict_rootedMarkedProxy (hn : n ≤ R)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) (x : Site R) :
    siteRestrict (rootedMarkedProxy R n hn C T) x =
      rootedDipoleMark R n hn (some x) + 2 * rootedMarkedSatellite C T (some x) := rfl

@[simp] theorem rootedMarkedProxy_none (hn : n ≤ R)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    rootedMarkedProxy R n hn C T none = 2 * rootedMarkedSatellite C T none := by
  simp [rootedMarkedProxy]

/-- **Neutrality** of the proxy of a neutral cluster (design-note signature). -/
theorem rootedMarkedProxy_sum_zero (hn : n ≤ R) (hn0 : 0 < n)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ))
    (hC : ∀ m ∈ C, ∑ j, m j = 0) (hT : T ⊆ C) :
    ∑ j, rootedMarkedProxy R n hn C T j = 0 := by
  unfold rootedMarkedProxy
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_rootedMarkedSatellite hC hT,
    rootedDipoleMark_sum_zero hn hn0]
  ring

/-- **The composite and its proxy vanish at the same faces**, the root included, for every
`0 < ξ < 1` and every cluster and orientation. -/
theorem rootedMarkedComposite_ne_zero_iff_proxy (hn : n ≤ R) {ξ : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) (C T : Finset (RotatorDualFace (sideLength R) → ℤ))
    (j : RotatorDualFace (sideLength R)) :
    rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T j ≠ 0 ↔
      rootedMarkedProxy R n hn C T j ≠ 0 := by
  rw [rootedMarkedComposite_eq]
  unfold rootedMarkedProxy
  set k := rootedMarkedSatellite C T j
  have hgap := dipoleGap_pos hξ0 hξ1
  rcases rootedDipoleMark_cases R n hn j with h | h | h <;> rw [h]
  · have hg := (isGapped_mul_add_int (ξ := ξ) (k := 1) (Or.inl rfl) k).ne_zero hgap
    push_cast at hg ⊢
    exact ⟨fun _ => by omega, fun _ h0 => hg (by linarith)⟩
  · have hg := (isGapped_mul_add_int (ξ := ξ) (k := -1) (Or.inr rfl) k).ne_zero hgap
    push_cast at hg ⊢
    exact ⟨fun _ => by omega, fun _ h0 => hg (by linarith)⟩
  · push_cast
    simp only [mul_zero, zero_add, ne_eq, Int.cast_eq_zero]
    omega

/-- **The support equivalence** in the design note's signature. The hypotheses `_hn0`, `_hT` and
`_hdisj` are not needed (see `rootedMarkedComposite_ne_zero_iff_proxy`). -/
theorem rootedMarkedProxy_ne_zero_iff (hn : n ≤ R) (_hn0 : 0 < n)
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) (_hT : T ⊆ C)
    (_hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m'))
    (j : RotatorDualFace (sideLength R)) :
    rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T j ≠ 0 ↔
      rootedMarkedProxy R n hn C T j ≠ 0 :=
  rootedMarkedComposite_ne_zero_iff_proxy hn hξ0 hξ1 C T j

/-- A neutral density on the wired carrier is the root neutralization of its face part. -/
theorem neutralizeAtWiredRoot_siteRestrict_of_sum_zero {L : ℕ} (ϱ : RotatorDualFace L → ℤ)
    (h : ∑ j, ϱ j = 0) : neutralizeAtWiredRoot (siteRestrict ϱ) = ϱ := by
  funext j
  cases j with
  | none =>
    rw [Fintype.sum_option] at h
    have hs : ∑ x, siteRestrict ϱ x = ∑ x, ϱ (some x) := rfl
    rw [Generic.PinnedCharges.neutralizeAtWiredRoot_none, hs]
    omega
  | some x => rfl

/-- The proxy of a neutral cluster is the root neutralization of its face part. -/
theorem neutralizeAtWiredRoot_siteRestrict_rootedMarkedProxy (hn : n ≤ R) (hn0 : 0 < n)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ))
    (hC : ∀ m ∈ C, ∑ j, m j = 0) (hT : T ⊆ C) :
    neutralizeAtWiredRoot (siteRestrict (rootedMarkedProxy R n hn C T)) =
      rootedMarkedProxy R n hn C T :=
  neutralizeAtWiredRoot_siteRestrict_of_sum_zero _ (rootedMarkedProxy_sum_zero hn hn0 C T hC hT)

/-- **Patch-charge identity**: `2 σ(S) = p(S) + (2ξ − 1) ϱ₀(S)` for every set `S` of faces. -/
theorem two_mul_sum_rootedMarkedComposite (hn : n ≤ R) (ξ : ℝ)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) (S : Finset (Site R)) :
    2 * ∑ x ∈ S, rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) =
      ((∑ x ∈ S, siteRestrict (rootedMarkedProxy R n hn C T) x : ℤ) : ℝ) +
        (2 * ξ - 1) * ((∑ x ∈ S, rootedDipoleMark R n hn (some x) : ℤ) : ℝ) := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rootedMarkedComposite_eq, siteRestrict_rootedMarkedProxy]
  push_cast
  ring

/-- **Patch-charge transfer** (the fractional cut gap): a set of faces on which the proxy is
charged carries composite charge at least `min(ξ, 1 − ξ)`. A cut of the mark is gapped;
otherwise the composite charge is half the nonzero proxy charge. -/
theorem dipoleGap_le_abs_sum_rootedMarkedComposite (hn : n ≤ R) (hn0 : 0 < n) (ξ : ℝ)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) (S : Finset (Site R))
    (h : ∑ x ∈ S, siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0) :
    dipoleGap ξ ≤ |∑ x ∈ S, rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x)| := by
  set k : ℤ := ∑ x ∈ S, rootedMarkedSatellite C T (some x) with hk
  set μ : ℤ := ∑ x ∈ S, rootedDipoleMark R n hn (some x) with hμ
  have hσ : ∑ x ∈ S, rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) =
      μ * ξ + k := by
    rw [hk, hμ]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [rootedMarkedComposite_eq]
    ring
  have hp : ∑ x ∈ S, siteRestrict (rootedMarkedProxy R n hn C T) x = μ + 2 * k := by
    rw [hk, hμ, Finset.mul_sum, ← Finset.sum_add_distrib]
    rfl
  rw [hσ]
  have hμc := sum_rootedDipoleMark_some hn hn0 S
  rw [← hμ] at hμc
  have hcases : μ = 1 ∨ μ = -1 ∨ μ = 0 := by
    rw [hμc]
    split_ifs <;> simp
  rcases hcases with h1 | h1 | h1
  · exact (isGapped_mul_add_int (ξ := ξ) (Or.inl h1) k).le_abs
  · exact (isGapped_mul_add_int (ξ := ξ) (Or.inr h1) k).le_abs
  · rw [h1, Int.cast_zero, zero_mul, zero_add]
    have hk0 : k ≠ 0 := by
      intro hk0
      apply h
      rw [hp, h1, hk0]
      rfl
    have h1k : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    exact (dipoleGap_le_one ξ).trans h1k

end Proxy

/-! ### The face support of the composite -/

section Support

variable {R n : ℕ}

theorem mem_chargeSupport_siteRestrict {L : ℕ} {ϱ : RotatorDualFace L → ℤ} {x : Fin L × Fin L} :
    x ∈ chargeSupport (siteRestrict ϱ) ↔ ϱ (some x) ≠ 0 :=
  mem_chargeSupport'

/-- The two faces of the dipole mark. -/
def rootedMarkSites (R n : ℕ) (hn : n ≤ R) : Finset (Site R) :=
  {center R, axialSite R n hn}

/-- The face support `X(C)` of the marked composite: the mark and the face supports of the
cluster members. -/
def rootedMarkedSupport (R n : ℕ) (hn : n ≤ R)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) : Finset (Site R) :=
  rootedMarkSites R n hn ∪ C.biUnion fun m => chargeSupport (siteRestrict m)

theorem mem_rootedMarkSites {hn : n ≤ R} {x : Site R} :
    x ∈ rootedMarkSites R n hn ↔ x = center R ∨ x = axialSite R n hn := by
  simp [rootedMarkSites]

theorem mem_rootedMarkedSupport {hn : n ≤ R} {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    {x : Site R} :
    x ∈ rootedMarkedSupport R n hn C ↔
      (x = center R ∨ x = axialSite R n hn) ∨ ∃ m ∈ C, m (some x) ≠ 0 := by
  unfold rootedMarkedSupport
  simp only [Finset.mem_union, mem_rootedMarkSites, Finset.mem_biUnion,
    mem_chargeSupport_siteRestrict]

theorem rootedMarkSites_subset_rootedMarkedSupport (hn : n ≤ R)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    rootedMarkSites R n hn ⊆ rootedMarkedSupport R n hn C :=
  Finset.subset_union_left

theorem chargeSupport_subset_rootedMarkedSupport (hn : n ≤ R)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)} {m : RotatorDualFace (sideLength R) → ℤ}
    (hm : m ∈ C) : chargeSupport (siteRestrict m) ⊆ rootedMarkedSupport R n hn C :=
  (Finset.subset_biUnion_of_mem (fun m => chargeSupport (siteRestrict m)) hm).trans
    Finset.subset_union_right

theorem rootedMarkedSupport_mono (hn : n ≤ R)
    {C C' : Finset (RotatorDualFace (sideLength R) → ℤ)} (h : C ⊆ C') :
    rootedMarkedSupport R n hn C ⊆ rootedMarkedSupport R n hn C' :=
  Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.biUnion_subset_biUnion_of_subset_left _ h)

theorem rootedMarkedSupport_nonempty (hn : n ≤ R)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    (rootedMarkedSupport R n hn C).Nonempty :=
  ⟨center R, rootedMarkSites_subset_rootedMarkedSupport hn C (by simp [rootedMarkSites])⟩

/-- The proxy's face support lies in `X(C)`. -/
theorem chargeSupport_siteRestrict_rootedMarkedProxy_subset (hn : n ≤ R)
    {C T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) :
    chargeSupport (siteRestrict (rootedMarkedProxy R n hn C T)) ⊆ rootedMarkedSupport R n hn C := by
  intro x hx
  have hx' : siteRestrict (rootedMarkedProxy R n hn C T) x ≠ 0 := mem_chargeSupport'.1 hx
  rw [mem_rootedMarkedSupport]
  by_contra hcon
  push Not at hcon
  apply hx'
  rw [siteRestrict_rootedMarkedProxy, rootedDipoleMark_some_of_ne hn hcon.1.1 hcon.1.2,
    rootedMarkedSatellite_eq_zero hT hcon.2]
  rfl

/-- The proxy is odd, hence nonzero, on the two faces of the mark. -/
theorem rootedMarkSites_subset_chargeSupport_proxy (hn : n ≤ R)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    rootedMarkSites R n hn ⊆ chargeSupport (siteRestrict (rootedMarkedProxy R n hn C T)) := by
  intro x hx
  have hv := rootedDipoleMark_of_mem_sites hn (mem_rootedMarkSites.1 hx)
  rw [mem_chargeSupport', siteRestrict_rootedMarkedProxy]
  omega

/-- **The proxy has the face support `X(C)`** when the members of the cluster have pairwise
disjoint face supports. -/
theorem chargeSupport_siteRestrict_rootedMarkedProxy (hn : n ≤ R)
    {C T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (chargeSupport (siteRestrict m)) (chargeSupport (siteRestrict m'))) :
    chargeSupport (siteRestrict (rootedMarkedProxy R n hn C T)) = rootedMarkedSupport R n hn C := by
  refine Finset.Subset.antisymm (chargeSupport_siteRestrict_rootedMarkedProxy_subset hn hT) ?_
  intro x hx
  by_cases hmark : x = center R ∨ x = axialSite R n hn
  · exact rootedMarkSites_subset_chargeSupport_proxy hn C T (mem_rootedMarkSites.2 hmark)
  push Not at hmark
  obtain ⟨m, hmC, hmx⟩ := (mem_rootedMarkedSupport.1 hx).resolve_left (by tauto)
  have hother : ∀ m' ∈ C, m' ≠ m → m' (some x) = 0 := by
    intro m' hm' hne
    by_contra h
    exact Finset.disjoint_left.1 (hdisj m' hm' m hmC hne)
      (mem_chargeSupport_siteRestrict.2 h) (mem_chargeSupport_siteRestrict.2 hmx)
  rw [mem_chargeSupport', siteRestrict_rootedMarkedProxy,
    rootedDipoleMark_some_of_ne hn hmark.1 hmark.2,
    rootedMarkedSatellite_eq_of_unique hT hmC hother]
  split_ifs <;> omega

end Support

/-! ### The Appendix D adjacency of the marked clusters -/

section Adjacency

variable {R n : ℕ}

/-- The size `D(C)` of the cluster side of a marked composite: the diameter of `X(C)` when every
member of `C` is face-neutral, and otherwise the larger of the diameter and the mark's boundary
distance. It is monotone in `C` and bounds `d_Λ` of the proxy's face part for every
orientation. -/
def rootedClusterSize (R n : ℕ) (hn : n ≤ R)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) : ℝ :=
  if ∀ m ∈ C, totalCharge (siteRestrict m) = 0 then
    euclideanSetDiameter (rootedMarkedSupport R n hn C)
  else
    max (euclideanBoundaryDistance (rootedMarkSites R n hn))
      (euclideanSetDiameter (rootedMarkedSupport R n hn C))

/-- The adjacency scale of a member `ϱ` against the marked cluster `C`: the smaller of
`d_Λ(ϱ|faces)` and `D(C)`. -/
def rootedMarkScale (R n : ℕ) (hn : n ≤ R) (ϱ : RotatorDualFace (sideLength R) → ℤ)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) : ℝ :=
  min (boundaryAdjustedSize (siteRestrict ϱ)) (rootedClusterSize R n hn C)

/-- **The Appendix D adjacency of the marked clusters**: a member `ϱ` is adjacent to the cluster
`C` when it violates the Appendix D separation from the composite support,
`dist(supp ϱ|faces, X(C)) < M · min(d_Λ(ϱ|faces), D(C))^α` (Euclidean distance). -/
def RootedMarkAdjacent (M α : ℝ) (R n : ℕ) (hn : n ≤ R)
    (ϱ : RotatorDualFace (sideLength R) → ℤ)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ)) : Prop :=
  euclideanSetDistance (chargeSupport (siteRestrict ϱ)) (rootedMarkedSupport R n hn C) <
    M * rootedMarkScale R n hn ϱ C ^ α

/-- The extended ensemble of a marked term: the remainder of the cluster `C` and the proxy. -/
def rootedMarkedExtension (M α : ℝ) (R n : ℕ) (hn : n ≤ R)
    (N C T : Finset (RotatorDualFace (sideLength R) → ℤ)) :
    Finset (RotatorDualFace (sideLength R) → ℤ) :=
  insert (rootedMarkedProxy R n hn C T) (remainder (RootedMarkAdjacent M α R n hn) N C)

/-- The charged half of Appendix D's isolation clause on boundary-far constituents: every
constituent `ρ₁` of `ρ` with `2M diam(ρ₁)^α ≤ dist(ρ₁, ρ − ρ₁)` and `diam(ρ₁) < M d_bdry(ρ₁)^α`
is charged. -/
def HasFarConstituentCharge {L : ℕ} (M α : ℝ) (ρ : ChargeDensity L) : Prop :=
  ∀ ρ₁, IsConstituent ρ ρ₁ →
    2 * M * chargeEuclideanDiameter ρ₁ ^ α ≤
      euclideanSetDistance (chargeSupport ρ₁) (chargeSupport (fun x => ρ x - ρ₁ x)) →
    chargeEuclideanDiameter ρ₁ < M * chargeBoundaryDistance ρ₁ ^ α →
    totalCharge ρ₁ ≠ 0

end Adjacency

/-! ### The two Appendix D statements (proved in `MarkedGeometryProxyCut.lean`) -/

/-- **The extended ensemble is an Appendix D pinned ensemble.** For a branch ensemble
`N = F.image neutralizeAtWiredRoot` with `F` pinned and boundary-separated, a cluster `C ⊆ N` and
an orientation `T ⊆ C`, the face parts of `rem(C) ∪ {p}`:
* form a pinned, boundary-separated ensemble (at the same `M, α`);
* neutralize back to `rem(C) ∪ {p}`.
In addition `p ∉ rem(C)`, and every remainder member is face-disjoint from `X(C)`. -/
def RootedMarkedExtensionGeometry (M α : ℝ) (R n : ℕ) (hn : n ≤ R) : Prop :=
  ∀ F : Finset (ChargeDensity (sideLength R)), IsPinnedChargeEnsemble F →
    IsBoundarySeparated M α F →
    ∀ C T : Finset (RotatorDualFace (sideLength R) → ℤ),
      C ⊆ F.image neutralizeAtWiredRoot → T ⊆ C →
      IsPinnedChargeEnsemble ((rootedMarkedExtension M α R n hn
          (F.image neutralizeAtWiredRoot) C T).image siteRestrict) ∧
        IsBoundarySeparated M α ((rootedMarkedExtension M α R n hn
          (F.image neutralizeAtWiredRoot) C T).image siteRestrict) ∧
        ((rootedMarkedExtension M α R n hn (F.image neutralizeAtWiredRoot) C T).image
          siteRestrict).image neutralizeAtWiredRoot =
          rootedMarkedExtension M α R n hn (F.image neutralizeAtWiredRoot) C T ∧
        rootedMarkedProxy R n hn C T ∉
          remainder (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot) C ∧
        ∀ ϱ ∈ remainder (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot) C,
          Disjoint (chargeSupport (siteRestrict ϱ)) (rootedMarkedSupport R n hn C)

/-- **The rooted charged-split lemma** (FS81 Theorem 2.3 in Appendix D form). Let `F` carry the
Appendix D geometry, let `C` be a cluster of `F.image neutralizeAtWiredRoot` for the adjacency
`RootedMarkAdjacent M α`, and let `T ⊆ C`. Let `A = X(C) ∩ S` and `B = X(C) ∖ S` be a split of
the composite support such that:
* both parts are nonempty;
* `A` is isolated, `2M diam(A)^α ≤ dist(A, B)`;
* `A` is boundary-far, `diam(A) < M d_bdry(A)^α`.
Then the composite charge of `A` is at least `min(ξ, 1 − ξ)` in absolute value. -/
def RootedMarkedChargedSplit (M α : ℝ) (R n : ℕ) (hn : n ≤ R) : Prop :=
  ∀ F : Finset (ChargeDensity (sideLength R)), AppendixDChargeGeometry M α F →
    ∀ C ∈ clusters (RootedMarkAdjacent M α R n hn) (F.image neutralizeAtWiredRoot),
    ∀ T ⊆ C, ∀ S : Finset (Site R),
      (rootedMarkedSupport R n hn C ∩ S).Nonempty →
      (rootedMarkedSupport R n hn C \ S).Nonempty →
      2 * M * euclideanSetDiameter (rootedMarkedSupport R n hn C ∩ S) ^ α ≤
        euclideanSetDistance (rootedMarkedSupport R n hn C ∩ S)
          (rootedMarkedSupport R n hn C \ S) →
      euclideanSetDiameter (rootedMarkedSupport R n hn C ∩ S) <
        M * euclideanBoundaryDistance (rootedMarkedSupport R n hn C ∩ S) ^ α →
      ∀ ξ : ℝ, dipoleGap ξ ≤ |∑ x ∈ rootedMarkedSupport R n hn C ∩ S,
        rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x)|

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
