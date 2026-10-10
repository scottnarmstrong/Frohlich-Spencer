/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Combinatorics.Animals
public import FroehlichSpencer.Infra.Combinatorics.UnionBound
public import FroehlichSpencer.Infra.Ergodic.Basic
public import FroehlichSpencer.Infra.Ergodic.Density
public import FroehlichSpencer.Infra.Ergodic.Ergodicity
public import FroehlichSpencer.Infra.Ergodic.LocalErgodic
public import FroehlichSpencer.Infra.Ergodic.Maximal
public import FroehlichSpencer.Infra.Ergodic.MaximalDiscrete
public import FroehlichSpencer.Infra.Ergodic.Pointwise
public import FroehlichSpencer.Infra.Ergodic.Variance
public import FroehlichSpencer.Infra.Green.APriori
public import FroehlichSpencer.Infra.Green.Basic
public import FroehlichSpencer.Infra.Green.CombesThomas
public import FroehlichSpencer.Infra.Green.CombesThomasGap
public import FroehlichSpencer.Infra.Green.EventRegularity
public import FroehlichSpencer.Infra.Green.Existence
public import FroehlichSpencer.Infra.Green.FiniteVolumeRegularity
public import FroehlichSpencer.Infra.Green.InfiniteVolumeRegularity
public import FroehlichSpencer.Infra.Lattice
public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Multiscale.Basic
public import FroehlichSpencer.Multiscale.Clusters
public import FroehlichSpencer.Multiscale.Locality
public import FroehlichSpencer.Multiscale.Measurability
public import FroehlichSpencer.Multiscale.Singular
public import FroehlichSpencer.T12.Annuli
public import FroehlichSpencer.T12.Base
public import FroehlichSpencer.T12.Cubes
public import FroehlichSpencer.T12.Entropy
public import FroehlichSpencer.T12.Events
public import FroehlichSpencer.T12.EventAPI
public import FroehlichSpencer.T12.FirstExit
public import FroehlichSpencer.T12.InductionDefs
public import FroehlichSpencer.T12.Bridge
public import FroehlichSpencer.T12.Residual
public import FroehlichSpencer.T12.Tails
public import FroehlichSpencer.T12.Tower
public import FroehlichSpencer.T12.TowerProb
public import FroehlichSpencer.T12.Exterior
public import FroehlichSpencer.T12.ResonantBlock
public import FroehlichSpencer.T12.GentleRegion
public import FroehlichSpencer.T12.FirstExitIteration
public import FroehlichSpencer.T12.LowCut
public import FroehlichSpencer.T12.LocalEstimates
public import FroehlichSpencer.T12.InductionStep
public import FroehlichSpencer.T12.ScaleChoice
public import FroehlichSpencer.T12.FiniteVolumeT21
public import FroehlichSpencer.T12.TowerGreen
public import FroehlichSpencer.T12.Interpolation
public import FroehlichSpencer.T12.Lemma52
public import FroehlichSpencer.T12.Obstacles
public import FroehlichSpencer.T12.Regions
public import FroehlichSpencer.T12.Resonance
public import FroehlichSpencer.T12.Section5
public import FroehlichSpencer.T12.SubordinateCovers
public import FroehlichSpencer.T12.Theorem51
public import FroehlichSpencer.T12.Theorem22
public import FroehlichSpencer.T12.Assembly.Constants
public import FroehlichSpencer.T12.Assembly.LargeDistance
public import FroehlichSpencer.T12.Assembly.ProbabilityBound
public import FroehlichSpencer.T12.Assembly.SmallDistance
public import FroehlichSpencer.T12.Assembly.T21Interface
public import FroehlichSpencer.IDS.Assembly
public import FroehlichSpencer.IDS.Averaged
public import FroehlichSpencer.IDS.Boundary
public import FroehlichSpencer.IDS.Green
public import FroehlichSpencer.IDS.Trace
public import FroehlichSpencer.Infra.Green.Iteration
public import FroehlichSpencer.Infra.Green.PathExpansion
public import FroehlichSpencer.Infra.ProductMeasure
public import FroehlichSpencer.Infra.Resolvent
public import FroehlichSpencer.Infra.Spectral.Canonical
public import FroehlichSpencer.Infra.Spectral.Count
public import FroehlichSpencer.Infra.Spectral.Interlacing
public import FroehlichSpencer.Infra.Spectral.Location
public import FroehlichSpencer.Infra.Spectral.MinMax
public import FroehlichSpencer.Infra.Spectral.Monotonicity
public import FroehlichSpencer.Infra.Spectral.QuadForm
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Spectral.ResolventNorm
public import FroehlichSpencer.Infra.Spectral.Sorted
public import FroehlichSpencer.Infra.Spectral.Submatrix
public import FroehlichSpencer.Infra.Spectral.Weyl
public import FroehlichSpencer.Infra.Stieltjes.Average
public import FroehlichSpencer.Infra.Stieltjes.Basic
public import FroehlichSpencer.Infra.Stieltjes.Continuity
public import FroehlichSpencer.Infra.Stieltjes.Dense
public import FroehlichSpencer.Infra.Stieltjes.EigenvalueKernel
public import FroehlichSpencer.Infra.Stieltjes.EigenvalueMeasure
public import FroehlichSpencer.Infra.Stieltjes.Existence
public import FroehlichSpencer.Infra.Stieltjes.Inversion
public import FroehlichSpencer.Infra.Stieltjes.Lipschitz
public import FroehlichSpencer.Infra.Stieltjes.Poisson
public import FroehlichSpencer.Infra.Stieltjes.Transform
public import FroehlichSpencer.Infra.Wegner.Averaging
public import FroehlichSpencer.Infra.Wegner.Gaussian
public import FroehlichSpencer.Infra.Wegner.Gershgorin
public import FroehlichSpencer.Infra.Wegner.OneSite
public import FroehlichSpencer.Surface.Site
public import FroehlichSpencer.Surface.LatticeLength
public import FroehlichSpencer.Surface.Laplacian
public import FroehlichSpencer.Surface.DirichletLaplacian
public import FroehlichSpencer.Surface.Hamiltonian
public import FroehlichSpencer.Surface.HamiltonianHermitian
public import FroehlichSpencer.Surface.FiniteGreen
public import FroehlichSpencer.Surface.ConfigurationSpace
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Surface.FiniteEigenvalueCount
public import FroehlichSpencer.Surface.GreenFunction
public import FroehlichSpencer.Surface.GreenFunctionSpec
public import FroehlichSpencer.Surface.GaussianBoundedDensity
public import FroehlichSpencer.Surface.GaussianProbability
public import FroehlichSpencer.Surface.IntegratedDensityOfStates
public import FroehlichSpencer.Surface.IntegratedDensityOfStatesSpec
public import FroehlichSpencer.Surface.GreenFunctionMeasurable
public import FroehlichSpencer.Surface.KuboIntegrandMeasurable
public import FroehlichSpencer.Surface.KuboQuantity
public import FroehlichSpencer.Surface.IsDiffusionCoefficient
public import FroehlichSpencer.Reduction.GreenAlmostSure
public import FroehlichSpencer.Reduction.GreenAPriori
public import FroehlichSpencer.Reduction.DyadicGeometry
public import FroehlichSpencer.Reduction.EventEstimate
public import FroehlichSpencer.Reduction.BadShellBound
public import FroehlichSpencer.Reduction.GlobalKuboBound
public import FroehlichSpencer.Reduction.TendstoKubo
public import FroehlichSpencer.Reduction.T12ImpliesT11
public import FroehlichSpencer.Infra.Wegner.Resonance
public import FroehlichSpencer.T12.Locality

/-!
# Fröhlich–Spencer (1983): absence of diffusion in the Anderson model

Root module of the formalization of J.

Fröhlich and T.

Spencer, *Absence of
diffusion in the Anderson tight binding model for large disorder or low
energy*, Comm.

Math.

Phys. 88 (1983) 151–184.

`FroehlichSpencer.Infra.*` holds generic infrastructure.
-/
