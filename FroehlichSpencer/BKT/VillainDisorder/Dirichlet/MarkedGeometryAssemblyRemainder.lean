/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryAssemblyProfiles
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedActivity
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.FejerLayerWitness
import Mathlib.Tactic

/-!
Fix a branch family `F` with the Appendix D geometry, a cluster `C` of the marked adjacency and an
orientation `T ⊆ C`.

The remainder waves are the routine waves of
the remainder members **in the same family** `Fext`
(`markedProfilesG`, `routineWave`).

Then:
* they are orthogonal to the real composite `σ = (ξ − 1/2) ϱ₀ + p/2`: base pieces sit off `X(C)`,
  and each profile is constant on the proxy's face support, which contains both mark faces;
* their gradients avoid those of the composite base wave and of the proxy profiles;
* their activities are renormalized below `1` by the D1 gain argument.

The cover bound uses the
  isolation of the branch family and the bad selected count of the comb terminal.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator

/-! ### Generic facts on assembled waves -/

section Generic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
  {centerOf : (V → ℤ) → V}

/-- Disjoint gradients give a vanishing Laplacian pairing. -/
theorem pairing_laplacian_eq_zero_of_grad_disjoint {f g : V → ℝ}
    (h : ∀ e, G.grad f e = 0 ∨ G.grad g e = 0) : Multigraph.pairing f (G.laplacian g) = 0 := by
  rw [Multigraph.pairing_laplacian_eq_neg_sum_grad_mul, neg_eq_zero]
  exact Finset.sum_eq_zero fun e _ => by rcases h e with h | h <;> simp [h]

/-- An assembled wave is orthogonal to every source its pieces are orthogonal to. -/
theorem pairing_envelopeWave_eq_zero {N₀ : Finset (V → ℤ)} {ρ : V → ℤ}
    (Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ρ) (κ amp : ℝ) (k₀ : ℕ) {f : V → ℝ}
    (h : ∀ t, Multigraph.pairing (Wv.piece t) f = 0) :
    Multigraph.pairing (envelopeWave Wv κ amp k₀) f = 0 := by
  let _ := Wv.finite
  unfold Multigraph.pairing envelopeWave
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  have ht := h t
  unfold Multigraph.pairing at ht
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ht, mul_zero]

/-- An assembled wave avoids the gradient of every field its pieces avoid. -/
theorem grad_envelopeWave_disjoint {N₀ : Finset (V → ℤ)} {ρ : V → ℤ}
    (Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ρ) (κ amp : ℝ) (k₀ : ℕ) {f : V → ℝ}
    (h : ∀ t e, G.grad (Wv.piece t) e = 0 ∨ G.grad f e = 0) (e : E) :
    G.grad (envelopeWave Wv κ amp k₀) e = 0 ∨ G.grad f e = 0 := by
  by_cases hall : ∀ t, G.grad (Wv.piece t) e = 0
  · exact Or.inl (grad_envelopeWave_eq_zero Wv κ amp k₀ hall)
  · push Not at hall
    obtain ⟨t, ht⟩ := hall
    exact Or.inr ((h t e).resolve_left ht)

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The gradient of `c₀ b + ∑_t q_t ψ_t` vanishes where all its parts do. -/
theorem grad_add_sum_eq_zero (c₀ : ℝ) (b : V → ℝ) {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (ψ : ι → V → ℝ) {e : E} (hb : G.grad b e = 0) (hψ : ∀ t, G.grad (ψ t) e = 0) :
    G.grad (fun j => c₀ * b j + ∑ t, q t * ψ t j) e = 0 := by
  unfold Multigraph.grad at *
  have hb' : b (G.src e) = b (G.tgt e) := sub_eq_zero.mp hb
  have hψ' : ∀ t, ψ t (G.src e) = ψ t (G.tgt e) := fun t => sub_eq_zero.mp (hψ t)
  simp only [hb', hψ', sub_self]

/-- **The gain of one assembled wave** from its layer data (the body of `rootedD_gain`). -/
theorem envelopeWave_gain_of_layerData {N₀ : Finset (V → ℤ)} {ϱ : V → ℤ}
    (Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ϱ) {A D₁ α K₀ K₁ : ℝ}
    (hα : Wv.alpha = α) (hK0 : Wv.K₀ = K₀) (hK1 : Wv.K₁ = K₁)
    (hbase : (1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
      ∑ t ∈ (letI := Wv.finite; Finset.univ.filter fun t => Wv.scale t = 0), |Wv.charge t|)
    (hedge : ∀ t, ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤
      100 * 4 ^ Wv.scale t)
    (hcover : A ≤ D₁ * (∑ j, |(ϱ j : ℝ)| +
      ((letI := Wv.finite; (Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℕ) : ℝ)))
    {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁) :
    amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * A ≤
      translationEnergy c (gradLinear G) (envelopeWave Wv κ amp k₀) fun j => (ϱ j : ℝ) := by
  classical
  let _ := Wv.finite
  have hα1 : 1 < α := by rw [← hα]; exact Wv.alpha_gt_one
  have hγ : 0 ≤ gradExponent α := (gradExponent_pos hα1).le
  have hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ 100 * 4 ^ k₀ := by
    intro t ht
    refine (hedge t).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact pow_le_pow_right₀ (by norm_num) ht.le
  have hquad : ∀ s, k₀ ≤ s →
      amp ≤ quadAmplitude κ Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) s := by
    intro s hs
    rw [hK0, hK1, hα]
    refine le_min hquad₁ (hquad₂.trans ?_)
    refine div_le_div_of_nonneg_right ?_ hK₁.le
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hγ
  have hK₀' : 0 < Wv.K₀ := by rw [hK0]; exact hK₀
  have hK₁' : 0 < Wv.K₁ := by rw [hK1]; exact hK₁
  have hampW' : amp * Wv.K₁ ≤ W := by rw [hK1]; exact hampW
  have hexp' : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * Wv.K₁) ≤ amp / 2 := by
    rw [hK1]; exact hexp
  have hgain := translationEnergy_envelopeWave_ge_gain Wv hc hκ hK₀' hK₁' hamp hampW' hk₀ hcount
    hexp' hquad
  refine le_trans ?_ hgain
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  set S : ℝ := ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)
  set Q : ℝ := ∑ t ∈ Finset.univ.filter (fun t => Wv.scale t = 0), |Wv.charge t|
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hcov : A / D₁ ≤ X + S := by rw [div_le_iff₀ hD₁]; linarith [hcover]
  have h1 : amp / (8 * D₁) * A ≤ amp / 8 * (X + S) := by
    rw [show amp / (8 * D₁) * A = amp / 8 * (A / D₁) by field_simp]
    exact mul_le_mul_of_nonneg_left hcov (by positivity)
  have h2 : (1 / 2 : ℝ) * X ≤ Q := hbase
  nlinarith

/-- **The renormalized activity of one assembled wave is at most one**, for the Gaussian cost,
an entropy bound `|K| ≤ e^{D₂ A}` and an amplitude with `D₂ ≤ amp/(8 D₁)`. -/
theorem abs_mul_exp_envelopeWave_le_one {N₀ : Finset (V → ℤ)} {ϱ : V → ℤ}
    (Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ϱ) {A D₁ D₂ α K₀ K₁ Kϱ τ : ℝ}
    (hα : Wv.alpha = α) (hK0 : Wv.K₀ = K₀) (hK1 : Wv.K₁ = K₁)
    (hbase : (1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
      ∑ t ∈ (letI := Wv.finite; Finset.univ.filter fun t => Wv.scale t = 0), |Wv.charge t|)
    (hedge : ∀ t, ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤
      100 * 4 ^ Wv.scale t)
    (hcover : A ≤ D₁ * (∑ j, |(ϱ j : ℝ)| +
      ((letI := Wv.finite; (Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℕ) : ℝ)))
    (hKϱ : |Kϱ| ≤ Real.exp (D₂ * A)) (hA : 0 ≤ A) (hτ : 0 < τ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hs : 0 ≤ amp / (8 * D₁) - D₂)
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (hexp : 100 * 4 ^ k₀ * costMajorant (τ / 2) (τ / 2) (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (τ / 2) * K₀)) :
    |Kϱ| * Real.exp (-gffTranslationEnergy G τ (envelopeWave Wv (τ / 2) amp k₀)
      (fun j => (ϱ j : ℝ))) ≤ 1 := by
  have hgain := envelopeWave_gain_of_layerData Wv hα hK0 hK1 hbase hedge hcover
    (isCostEnvelope_gaussianCost hτ.le (amp * K₁)) (by positivity) hK₀ hK₁ hD₁ hamp le_rfl hk₀
    hexp hquad₁ hquad₂
  rw [translationEnergy_gaussianCost] at hgain
  set En := gffTranslationEnergy G τ (envelopeWave Wv (τ / 2) amp k₀) (fun j => (ϱ j : ℝ))
  have hX : 0 ≤ ∑ j, |(ϱ j : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc |Kϱ| * Real.exp (-En) ≤ Real.exp (D₂ * A) * Real.exp (-En) :=
        mul_le_mul_of_nonneg_right hKϱ (Real.exp_pos _).le
    _ = Real.exp (D₂ * A - En) := by rw [← Real.exp_add]; ring_nf
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h1 : 0 ≤ (amp / (8 * D₁) - D₂) * A := mul_nonneg hs hA
        have h2 : 0 ≤ amp / 8 * ∑ j, |(ϱ j : ℝ)| := by positivity
        nlinarith

end Generic

/-! ### The real composite against the proxy family -/

section Composite

variable {R n : ℕ}

/-- The real composite is `(ξ − 1/2)` times the mark plus half the integer proxy. -/
theorem rootedMarkedComposite_eq_mark_proxy (hn : n ≤ R) (ξ : ℝ)
    (C T : Finset (RotatorDualFace (sideLength R) → ℤ)) (j : RotatorDualFace (sideLength R)) :
    rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T j =
      (ξ - 1 / 2) * (rootedDipoleMark R n hn j : ℝ) +
        1 / 2 * (rootedMarkedProxy R n hn C T j : ℝ) := by
  rw [rootedMarkedComposite_eq]
  unfold rootedMarkedProxy
  push_cast
  ring

/-- Pairing with the dipole mark is the difference of the values at the two mark faces. -/
theorem pairing_rootedDipoleMark (hn : n ≤ R) (hn0 : 0 < n) (f : RotatorDualFace (sideLength R) → ℝ) :
    Multigraph.pairing f (fun j => (rootedDipoleMark R n hn j : ℝ)) =
      f (some (center R)) - f (some (axialSite R n hn)) := by
  classical
  have hca : (some (center R) : RotatorDualFace (sideLength R)) ≠ some (axialSite R n hn) :=
    fun h => rootedCenter_ne_axialSite hn hn0 (Option.some.inj h)
  unfold Multigraph.pairing
  rw [Fintype.sum_eq_add (some (center R)) (some (axialSite R n hn)) hca]
  · dsimp only
    rw [rootedDipoleMark_center, rootedDipoleMark_axial hn hn0]
    push_cast
    ring
  · intro j hj
    have hj' : rootedDipoleMark R n hn j = 0 := by
      simp [rootedDipoleMark, hj.1, hj.2]
    dsimp only
    rw [hj', Int.cast_zero, mul_zero]

/-- **A profile of another member is orthogonal to the real composite.** The proxy's face part
lies in the family; the profile is constant on it, so it kills the mark (both mark faces carry the
proxy), and it is orthogonal to the proxy. -/
theorem ProfileContext.pairing_profilePiece_rootedMarkedComposite (hn : n ≤ R) (hn0 : 0 < n)
    {Fext : Finset (ChargeDensity (sideLength R))} {ρ : ChargeDensity (sideLength R)} {j : ℕ}
    {s : Finset (Generic.PinnedCharges.Site (sideLength R))}
    {f : Generic.PinnedCharges.Site (sideLength R) → ℝ}
    (h : ProfileContext Fext ρ j s f) (ξ : ℝ)
    {C T : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hp : siteRestrict (rootedMarkedProxy R n hn C T) ∈ Fext)
    (hpne : siteRestrict (rootedMarkedProxy R n hn C T) ≠ ρ)
    (hpneut : neutralizeAtWiredRoot (siteRestrict (rootedMarkedProxy R n hn C T)) =
      rootedMarkedProxy R n hn C T) :
    Multigraph.pairing (profilePiece j f) (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) =
      0 := by
  have hsplit : Multigraph.pairing (profilePiece j f)
      (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) =
        (ξ - 1 / 2) * Multigraph.pairing (profilePiece j f)
          (fun j => (rootedDipoleMark R n hn j : ℝ)) +
        1 / 2 * ∑ v, profilePiece j f v *
          (neutralizeAtWiredRoot (siteRestrict (rootedMarkedProxy R n hn C T)) v : ℝ) := by
    rw [hpneut]
    unfold Multigraph.pairing
    simp_rw [rootedMarkedComposite_eq_mark_proxy hn ξ C T, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hc : center R ∈ chargeSupport (siteRestrict (rootedMarkedProxy R n hn C T)) :=
    rootedMarkSites_subset_chargeSupport_proxy hn C T (by simp [rootedMarkSites])
  have ha : axialSite R n hn ∈ chargeSupport (siteRestrict (rootedMarkedProxy R n hn C T)) :=
    rootedMarkSites_subset_chargeSupport_proxy hn C T (by simp [rootedMarkSites])
  rw [hsplit, pairing_rootedDipoleMark hn hn0,
    ProfileContext.profilePiece_eq_of_mem_other h hp hpne hc ha,
    sub_self, h.sum_profilePiece_mul_neutralize_eq_zero hp hpne]
  ring

/-- A base piece at a face off the proxy's face support is orthogonal to the real composite. -/
theorem pairing_basePiece_rootedMarkedComposite (hn : n ≤ R) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    {C T : Finset (RotatorDualFace (sideLength R) → ℤ)} (ϱ : RotatorDualFace (sideLength R) → ℤ)
    {x : Generic.PinnedCharges.Site (sideLength R)}
    (hx : x ∉ chargeSupport (siteRestrict (rootedMarkedProxy R n hn C T))) :
    Multigraph.pairing (basePiece ϱ x) (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) =
      0 := by
  classical
  have hσx : rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x) = 0 := by
    by_contra hne
    apply hx
    rw [mem_chargeSupport']
    exact (rootedMarkedComposite_ne_zero_iff_proxy hn hξ0 hξ1 C T (some x)).mp hne
  unfold Multigraph.pairing
  rw [Finset.sum_eq_single (some x) (fun j _ hj => by simp [basePiece, hj]) (by simp)]
  rw [hσx, mul_zero]

end Composite

/-! ### Two members of a separated family share no edge -/

theorem not_incident_both_of_separated {L : ℕ} {F : Finset (ChargeDensity L)}
    (hens : IsPinnedChargeEnsemble F)
    (hsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ σ : ChargeDensity L} (hρ : ρ ∈ F) (hσ : σ ∈ F) (hρσ : ρ ≠ σ)
    {x y : Generic.PinnedCharges.Site L} (hx : x ∈ chargeSupport ρ) (hy : y ∈ chargeSupport σ)
    {e : SquareZeroBond L}
    (hex : (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x)
    (hey : (squareZero L).src e = some y ∨ (squareZero L).tgt e = some y) : False := by
  have hxy : x ≠ y := fun h => Finset.disjoint_left.mp (hens.2 ρ hρ σ hσ hρσ) hx (h ▸ hy)
  have h1 := siteDist_le_one_of_endpoints hex hey
  have h2 : l1 x y ≠ 0 := by
    intro h0
    apply hxy
    unfold l1 at h0
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have h3 : l1 x y ≤ 1 := by exact_mod_cast h1
  exact l1_ne_one_of_separated hens hsep hρ hσ hρσ hx hy (by omega)

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
