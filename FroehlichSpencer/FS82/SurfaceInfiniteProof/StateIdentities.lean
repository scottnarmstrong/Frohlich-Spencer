module

public import FroehlichSpencer.FS82.SurfaceInfiniteProof.LawIdentities
public import FroehlichSpencer.FS82.Infinite.LimitStateRoot
public import FroehlichSpencer.FS82.Infinite.NonsummabilityPrimal
public import FroehlichSpencer.FS82.Surface.FiniteVillainDualMomentComparisonLogThick
public import Mathlib.Tactic
@[expose] public section

open MeasureTheory
open Filter Topology
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Nonsummability
open FroehlichSpencer.FS82.Moment.Comparison

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable def cubeStateTailStart {β : ℝ} {hβ : 0 < β}
    (L : Infinite.CubeCurvatureLimitState β hβ)
    (P : Finset GlobalPlaquette) : ℕ := by
  classical
  let Pi : Finset Infinite.GlobalIntegerPlaquette := P
  let N0 := Classical.choose (exists_cube_threshold_for_plaquettes Pi)
  let T := max 1 N0
  have hseq : Tendsto L.subsequence atTop atTop :=
    L.strictMono_subsequence.tendsto_atTop
  have hev : ∀ᶠ n in atTop, T ≤ L.subsequence n :=
    (Filter.tendsto_atTop.1 hseq) T
  exact Classical.choose (Filter.eventually_atTop.1 hev)

theorem cubeStateTailStart_spec {β : ℝ} {hβ : 0 < β}
    (L : Infinite.CubeCurvatureLimitState β hβ)
    (P : Finset GlobalPlaquette) (k : ℕ) :
    max 1 (Classical.choose (exists_cube_threshold_for_plaquettes
      (P : Finset Infinite.GlobalIntegerPlaquette))) ≤
      L.subsequence (cubeStateTailStart L P + k) := by
  classical
  let Pi : Finset Infinite.GlobalIntegerPlaquette := P
  let N0 := Classical.choose (exists_cube_threshold_for_plaquettes Pi)
  let T := max 1 N0
  have hseq : Tendsto L.subsequence atTop atTop :=
    L.strictMono_subsequence.tendsto_atTop
  have hbound : ∀ᶠ n in atTop, T ≤ L.subsequence n :=
    (Filter.tendsto_atTop.1 hseq) T
  have hspec := Classical.choose_spec (Filter.eventually_atTop.1 hbound)
  have hk : T ≤ L.subsequence (cubeStateTailStart L P + k) := by
    exact hspec (cubeStateTailStart L P + k) (Nat.le_add_right _ _)
  simpa [Pi, N0, T, cubeStateTailStart] using hk

noncomputable def cubeStateOfInternal {β : ℝ} {hβ : 0 < β}
    (L : Infinite.CubeCurvatureLimitState β hβ) :
    SurfaceInfinite.CubeCurvatureLimitState β hβ where
  subsequence := L.subsequence
  strictMono_subsequence := L.strictMono_subsequence
  tailStart := cubeStateTailStart L
  law := L.law
  positiveCube := by
    intro P k
    have hlarge := cubeStateTailStart_spec L P k
    have hpos : 1 ≤ max 1 (Classical.choose (exists_cube_threshold_for_plaquettes
        (P : Finset Infinite.GlobalIntegerPlaquette))) := le_max_left _ _
    have hN : 1 ≤ L.subsequence (cubeStateTailStart L P + k) := le_trans hpos hlarge
    omega
  contained := by
    intro P k p hp
    let Pi : Finset Infinite.GlobalIntegerPlaquette := P
    let N0 := Classical.choose (exists_cube_threshold_for_plaquettes Pi)
    have hlarge := cubeStateTailStart_spec L P k
    have hN0 : N0 ≤ L.subsequence (cubeStateTailStart L P + k) :=
      le_trans (le_trans (le_max_right _ _) hlarge) (le_rfl)
    have hinternal : Infinite.PlaquetteInCube
        (L.subsequence (cubeStateTailStart L P + k)) p := by
      exact (Classical.choose_spec (exists_cube_threshold_for_plaquettes Pi))
        (L.subsequence (cubeStateTailStart L P + k)) hN0 p hp
    exact (source_inCube_iff (L.subsequence (cubeStateTailStart L P + k))
      (by
        have hpos := cubeStateTailStart_spec L P k
        have hone : 1 ≤ max 1 (Classical.choose
            (exists_cube_threshold_for_plaquettes Pi)) := le_max_left _ _
        omega) p).mpr hinternal
  pointwise := by
    intro P x
    let Pi : Finset Infinite.GlobalIntegerPlaquette := P
    let N0 := Classical.choose (exists_cube_threshold_for_plaquettes Pi)
    have hcontain (k : ℕ) : ∀ p ∈ Pi,
        Infinite.PlaquetteInCube (L.subsequence (cubeStateTailStart L P + k)) p := by
      intro p hp
      have hlarge := cubeStateTailStart_spec L P k
      have hN0 : N0 ≤ L.subsequence (cubeStateTailStart L P + k) :=
        le_trans (le_trans (le_max_right _ _) hlarge) (le_rfl)
      exact (Classical.choose_spec (exists_cube_threshold_for_plaquettes Pi))
        (L.subsequence (cubeStateTailStart L P + k)) hN0 p hp
    have hpos (k : ℕ) : 0 < L.subsequence (cubeStateTailStart L P + k) := by
      have hlarge := cubeStateTailStart_spec L P k
      have hone : 1 ≤ max 1 N0 := le_max_left _ _
      omega
    have hPI (k : ℕ) : ∀ p ∈ Pi,
        Infinite.PlaquetteInCube (L.subsequence (cubeStateTailStart L P + k)) p :=
      hcontain k
    have hfinite (k : ℕ) :
        SurfaceInfinite.cubeCurvatureLaw
            (cubeRegion (L.subsequence (cubeStateTailStart L P + k)) (hpos k))
            β hβ Pi (fun p hp =>
              (source_inCube_iff (L.subsequence (cubeStateTailStart L P + k))
                (hpos k) p).mpr (hcontain k p hp)) =
          Infinite.cubeCurvaturePMFTotal (L.subsequence (cubeStateTailStart L P + k))
            β hβ Pi := by
      have hbridge := cubeCurvatureLaw_eq_internal
        (L.subsequence (cubeStateTailStart L P + k)) (hpos k) β hβ Pi
        (fun p hp => (source_inCube_iff
          (L.subsequence (cubeStateTailStart L P + k)) (hpos k) p).mpr
          (hcontain k p hp))
      rw [hbridge]
      unfold Infinite.cubeCurvaturePMFTotal
      rw [dite_eq_left (hPI k)]
    have hshift : Tendsto (fun k : ℕ => cubeStateTailStart L P + k) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro n
      exact Filter.eventually_atTop.2 ⟨n, fun k hk => le_trans hk (Nat.le_add_left _ _)⟩
    have hconv := (L.pointwise Pi x).comp hshift
    convert hconv using 1
    funext k
    exact congrArg (fun q : PMF (Pi → ℤ) => (q x).toReal) (hfinite k)
  consistent := L.consistent

noncomputable def cubeStateToInternal {β : ℝ} {hβ : 0 < β}
    (L : SurfaceInfinite.CubeCurvatureLimitState β hβ) :
    Infinite.CubeCurvatureLimitState β hβ where
  subsequence := L.subsequence
  strictMono_subsequence := L.strictMono_subsequence
  law := L.law
  pointwise := by
    intro P x
    let tail := L.tailStart P
    have hsub : Tendsto (fun n : ℕ => n - tail) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro m
      exact Filter.eventually_atTop.2 ⟨tail + m, fun n hn => by omega⟩
    let fsrc : ℕ → ℝ := fun n =>
      (SurfaceInfinite.cubeCurvatureLaw
        (cubeRegion (L.subsequence (tail + (n - tail)))
          (L.positiveCube P (n - tail))) β hβ P
        (fun p hp => L.contained P (n - tail) p hp) x).toReal
    have hsrc : Tendsto fsrc atTop (𝓝 ((L.law P x).toReal)) := by
      change Tendsto (fun n =>
        (SurfaceInfinite.cubeCurvatureLaw
          (cubeRegion (L.subsequence (tail + (n - tail)))
            (L.positiveCube P (n - tail))) β hβ P
          (fun p hp => L.contained P (n - tail) p hp) x).toReal) atTop
        (𝓝 ((L.law P x).toReal))
      exact (L.pointwise P x).comp hsub
    let fint : ℕ → ℝ := fun n =>
      ((Infinite.cubeCurvaturePMFTotal (L.subsequence n) β hβ P) x).toReal
    have hevent : fsrc =ᶠ[atTop] fint := by
      filter_upwards [Filter.eventually_atTop.2 ⟨tail, fun n hn => hn⟩] with n hn
      have hidx : tail + (n - tail) = n := by omega
      have hcontained : ∀ p ∈ P,
          Infinite.PlaquetteInCube (L.subsequence (tail + (n - tail))) p := by
        intro p hp
        have hsource := L.contained P (n - tail) p hp
        exact (source_inCube_iff (L.subsequence (tail + (n - tail)))
          (L.positiveCube P (n - tail)) p).mp hsource
      have hpos : 0 < L.subsequence (tail + (n - tail)) :=
        L.positiveCube P (n - tail)
      let hsource : ∀ p ∈ P, inCube
          (cubeRegion (L.subsequence (tail + (n - tail))) hpos) p :=
        fun p hp => L.contained P (n - tail) p hp
      let hPI : ∀ p ∈ P,
          Infinite.PlaquetteInCube (L.subsequence (tail + (n - tail))) p :=
        fun p hp => (source_inCube_iff
          (L.subsequence (tail + (n - tail))) hpos p).mp (hsource p hp)
      have hbridge := cubeCurvatureLaw_eq_internal
        (L.subsequence (tail + (n - tail))) hpos β hβ P hsource
      have hLaw : SurfaceInfinite.cubeCurvatureLaw
          (cubeRegion (L.subsequence (tail + (n - tail))) hpos) β hβ P
          (fun p hp => L.contained P (n - tail) p hp) =
          Infinite.cubeCurvaturePMFTotal (L.subsequence n) β hβ P := by
        rw [hbridge]
        have htotal : Infinite.cubeCurvaturePMFTotal
            (L.subsequence (tail + (n - tail))) β hβ P =
            Infinite.cubeLocalCurvaturePMF
              (L.subsequence (tail + (n - tail))) β hβ P hPI := by
          unfold Infinite.cubeCurvaturePMFTotal
          exact dite_eq_left hPI
        conv_rhs => rw [← hidx]
        rw [htotal]
      exact congrArg (fun q : PMF (P → ℤ) => (q x).toReal) hLaw
    exact Filter.Tendsto.congr' hevent hsrc
  consistent := L.consistent

end FroehlichSpencer.FS82.SurfaceInfinite
