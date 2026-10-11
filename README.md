# Classical theorems of Fröhlich and Spencer, formalized in Lean 4

[![Build and verify](https://github.com/scottnarmstrong/Frohlich-Spencer/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/Frohlich-Spencer/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/Frohlich-Spencer/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/Frohlich-Spencer/actions/workflows/comparators.yml)

A **Lean 4 / Mathlib** formalization of three papers of J. Fröhlich and T. Spencer on phase transitions in lattice systems with an abelian symmetry and on localization: the Kosterlitz–Thouless transition (1981), massless phases of lattice gauge theories and spin systems (1982), and the absence of diffusion in the Anderson model (1983). The two-dimensional multiscale analysis follows the finite-volume presentation of Kharash and Peled. The main results are:

- **The Kosterlitz–Thouless transition.** In the two-dimensional plane rotator, the two-point function decays exponentially at high temperature. At low temperature it is bounded below by a power of the distance and still tends to zero. The same analysis gives the phases of the $`\mathbb Z_n`$ clock models, the absence of screening and the power-law decay of fractional charges in Coulomb gases, disorder bounds for the Villain model, and the roughening transition of the solid-on-solid model.
- **A massless phase in four-dimensional $`U(1)`$ lattice gauge theory.** For the Villain model at large $`\beta`$, the integer-valued gauge field that is dual to the model has the exponential moments of a free massless field, up to a renormalization of the coupling from $`\beta`$ to $`\beta''(\beta)\lt \beta`$ with $`\beta''/\beta\to1`$. By the same method, there is a translation-invariant state whose field-strength correlation is not summable and is the limit, after averaging over translations, of the finite-volume field-strength correlations; the paper reads this as a massless photon. The Wilson loop obeys a perimeter law at large $`\beta`$. Separately, the Wilson loop obeys an area law at small $`\beta`$, and the disorder operator of the $`\mathbb Z_N`$ gauge theories with Wilson's action obeys a perimeter law for large $`N`$.
- **Long-range order in the XY model.** For every $`D\ge3`$ and large $`\beta`$, $`\langle\cos(\theta_x-\theta_y)\rangle\ge e^{-C/\beta}`$ in the Villain XY model on a cube with free boundary conditions, uniformly in the two sites and in the side of the cube.
- **Anderson localization.** For the tight-binding Anderson operator on $`\mathbb Z^\nu`$ at large disorder, or with Gaussian disorder at high energy, the Green function decays exponentially with high probability, uniformly in the imaginary part of the energy, and the Kubo diffusion coefficient vanishes.

Each result is stated in a short Lean file of its own, called an *anchor*. Its definitions are written out in terms of Mathlib and of other anchors, and its proof is one line naming a theorem of the library, so what a theorem says can be read from a small, closed set of files. There are 425 anchors: 313 definitions and 112 theorems and supporting lemmas. The library contains no `sorry`, and every main theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Results formalized

The following lists what is covered from each paper. The formulations and Lean declarations are in the sections below. The papers contain more than is listed; nothing here claims that a paper is formalized in full.

- **J. Fröhlich and T. Spencer, “The Kosterlitz–Thouless transition in two-dimensional Abelian spin systems and the Coulomb gas”, Communications in Mathematical Physics 81 (1981), 527–602** ([DOI](https://doi.org/10.1007/BF01208273)).

  - Theorem C and (6.1): the power-law lower bound for the plane rotator and its harmonics; with (1.30) and (1.31), the existence of the transition.
  - Theorems A and B for Coulomb gases satisfying Condition λ, and for the hard-core gas: in finite volume and for every thermodynamic limit.
  - Theorem D for the Villain model, with free and with wired boundary conditions.
  - §7.1: the phase diagram of the $`\mathbb Z_n`$ clock models, Theorem 7.1, and the disorder bound (7.5) for the clock and the Villain-clock models.
  - §7.2: Theorem 7.3 for the solid-on-solid model and the roughening transition.

- **J. Fröhlich and T. Spencer, “Massless phases and symmetry restoration in Abelian gauge theories and spin systems”, Communications in Mathematical Physics 83 (1982), 411–454** ([DOI](https://doi.org/10.1007/BF01213610)).

  - (2.93): the two-sided bound on the exponential moments of the dual field of the four-dimensional Villain $`U(1)`$ model, in finite volume, on boxes whose shortest side is at least the logarithm of the longest (all cubes among them).
  - (2.90)–(2.93) for every limit state along cubes.
  - §2.11: a translation-invariant limit state in which the correlation of the field strength is not summable, the paper's massless photon; for the dual curvature, and for the limit of the finite-volume correlations of the field strength (2.89).
  - The perimeter law (1.13), (2.8) and the area law (2.7) for the Wilson loop of the Villain model, on cubes and for limit points along cubes.
  - (3.54): the perimeter law for the disorder operator of the $`\mathbb Z_N`$ gauge theories with Wilson's action, $`N`$ large, on cubes.
  - (4.40): long-range order in the Villain XY model for every $`D\ge3`$, in finite volume on cubes.

  Not covered: the existence of the thermodynamic limits, which the paper takes from Ginibre's inequalities; Wilson's action in §2 and §4; the further results the paper cites or sketches.

- **J. Fröhlich and T. Spencer, “Absence of diffusion in the Anderson tight binding model for large disorder or low energy”, Communications in Mathematical Physics 88 (1983), 151–184** ([DOI](https://doi.org/10.1007/BF01209475)).

  - Theorem 1.2: exponential decay of the Green function with polynomially high probability, in finite and in infinite volume.
  - Theorem 1.1: the Kubo diffusion coefficient vanishes; and the almost-sure decay of the Green function.
  - The objects of (1.4), (1.10)–(1.15): the Green function for an arbitrary real potential and the integrated density of states.

- **V. Kharash and R. Peled, “The Fröhlich–Spencer Proof of the Berezinskii–Kosterlitz–Thouless Transition”, [arXiv:1711.04720v1](https://arxiv.org/abs/1711.04720v1) (2017).**

  - Theorems 1.1, 1.3, 1.5 and 1.6: delocalization of the integer-valued Gaussian free field, the power-law lower bound for the Villain model, and the exponential-moment bound and renormalization identity for weighted Gaussian free fields, on finite squares.

Where the proofs depart from the printed text, the changes are listed under [Errata and deviations](#errata-and-deviations).

## Errata and deviations

[The complete list of errata and deviations](docs/ERRATA-AND-DEVIATIONS.md) gives each printed error, its location and correction, then separately records differences in scope, hypotheses, conventions and interpretation. Counts are by entries, including small editorial misprints: FS81: 18 errata and 18 deviations; Kharash–Peled: 48 errata and 10 deviations; FS82: 21 errata and 13 deviations; FS83: 22 errata and 11 deviations.

- **FS81:** the clock disorder lower bound (7.5) requires genuine clock twists; its all-real reading is refuted by a theorem of the library. The SOS interpolation condition (d) is impossible and is replaced by a proved bound. General Coulomb gases require a positive vacancy, and Villain and SOS limit statements specify their limit points and order of limits.
- **Kharash–Peled:** corrections include the free-square edge rule, the wired-degree statement, the line-sum endpoint, missing ensemble products and factors, and the false constituent-distance claim in Lemma 4.3. The results use finite squares and an explicit square-cover convention.
- **FS82:** the Jensen bound (2.101) needs the correct ensemble weights; (2.102) needs the sharp factor 5; the decay-rate and conditional-mean signs are corrected. The proof of (3.54) supplies a separate residual upper bound. Region restrictions, subsequential limits and the finite-volume remainder in (4.38) are listed as deviations.
- **FS83:** corrections restore the mass recurrence, the missing decay factor in (2.24), and both doubled exponents in (1.25). Vanishing diffusion is asserted on the positive-derivative locus of the integrated density of states.

## The Kosterlitz–Thouless transition and two-dimensional systems (FS81)

The models live on $`\mathbb Z^2`$. The *plane rotator* has an angle $`\theta_j`$ at every site and the Gibbs weight $`\exp[\beta\sum_{\langle j\ell\rangle}\cos(\theta_j-\theta_\ell)]`$; in the $`\mathbb Z_n`$ *clock model* the angles are multiples of $`2\pi/n`$; in the *Villain model* the factor $`e^{\beta\cos x}`$ of each bond is replaced by $`\varphi_\beta(x)=\sum_{m\in\mathbb Z}e^{-\beta(x+2\pi m)^2/2}`$. The *harmonic* $`\xi`$ of the two-point function is $`\langle\cos\xi(\theta_j-\theta_\ell)\rangle`$.

The two-point functions are thermodynamic limits with free boundary conditions; their existence is proved for the plane rotator and the clock models (`existsUnique_tendsto_planeRotatorTwoPoint`, `existsUnique_tendsto_clockTwoPoint`). Where a limit is not known to be unique, the statement is about every limit along an exhausting sequence of boxes, and says that at least one exists.

### The plane rotator

Let $`\langle S_j\cdot S_\ell\rangle(\beta)=\langle\cos(\theta_j-\theta_\ell)\rangle(\beta)`$ be the two-point function of the plane rotator on $`\mathbb Z^2`$.

**Theorem C.** There are $`\beta_0`$ and a function $`\beta'(\beta)\to\infty`$, the renormalized inverse temperature, such that for every $`\beta\gt \beta_0`$, $`\beta'(\beta)\gt 1/(4\pi)`$ and there is $`A\gt 0`$ with

```math
\langle S_j\cdot S_\ell\rangle(\beta)\ \ge\ A\,(1+|j-\ell|)^{-1/(2\pi\beta'(\beta))}\qquad\text{for all }j,\ell\in\mathbb Z^2 .
```

Lean: [`FroehlichSpencer.BKT.planeRotator_powerLaw_lower_bound`](FroehlichSpencer/BKT/Surface/PlaneRotatorPowerLaw.lean). The bound (6.1) for every integer harmonic $`\xi\ne0`$ is [`planeRotator_harmonic_powerLaw_lower_bound`](FroehlichSpencer/BKT/Surface/PlaneRotatorHarmonicPowerLaw.lean).

```lean
theorem planeRotator_powerLaw_lower_bound :
    ∃ β₀ : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ < β → 1 / (4 * Real.pi) < β' β ∧
        ∃ A : ℝ, 0 < A ∧ ∀ j ℓ : ℤ × ℤ,
          A * (1 + Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) ^
              (-(1 / (2 * Real.pi * β' β))) ≤
            planeRotatorCorrelation β hβ 1 j ℓ
```

**The transition.** There is $`\beta_c\gt 0`$ such that for $`\beta\lt \beta_c`$ the two-point function is bounded by $`Ce^{-m|j-\ell|}`$ with $`m\gt 0`$, and for $`\beta\gt \beta_c`$ it has no exponential bound and tends to zero uniformly as $`|j-\ell|\to\infty`$.

Lean: [`FroehlichSpencer.BKT.planeRotator_kosterlitzThouless_transition`](FroehlichSpencer/BKT/Surface/PlaneRotatorTransition.lean). The theorem asserts that $`\beta_c`$ exists; it does not compute it and says nothing at $`\beta=\beta_c`$. Above $`\beta_c`$ there is no long-range order. The two ingredients besides Theorem C are the high-temperature decay (1.30), [`planeRotator_highTemperature_expDecay`](FroehlichSpencer/BKT/Surface/PlaneRotatorHighTemperature.lean), and a weak form of the upper bound (1.31): $`0\le\langle S_j\cdot S_\ell\rangle\le K(1+|j-\ell|)^{-c\min(1,1/\beta)}`$ for an absolute $`c\gt 0`$, every $`\beta\gt 0`$ and some $`K=K(\beta)`$, [`planeRotator_powerLaw_upper_bound`](FroehlichSpencer/BKT/Surface/PlaneRotatorPowerLawUpper.lean).

### Coulomb gases

**Theorems A and B.** A lattice Coulomb gas has an integer charge $`q_j`$ at every site, with a priori weight $`\lambda(q_j)`$, and the two-dimensional Coulomb interaction at inverse temperature $`\beta`$. *Condition λ* asks that $`\lambda(q)=\lambda(-q)`$ and $`|\lambda(q)|\le C\,e^{(\alpha+\varepsilon\beta)q^2}`$ for all $`q`$, with $`\varepsilon\lt 1/16`$. Let $`\lambda\ge0`$ satisfy it and have a *vacancy* $`\lambda(0)\ge\nu\gt 0`$. For $`\beta`$ above a threshold that depends on $`C`$, $`\alpha`$, $`\varepsilon`$, $`\nu`$, and on $`\delta`$ in (A) or $`\xi`$ in (B), but not on $`\lambda`$, the gas is summable, thermodynamic limits of the quantities below exist, and every such limit satisfies:

- (A) for each $`\delta\gt 0`$: $`\langle\varphi(g)^2\rangle\ge(1-\delta)\,\beta\,(g,-\Delta^{-1}g)`$ for every finitely supported $`g`$ with $`\sum_jg(j)=0`$, so there is no screening;
- (B) for each $`0\lt \xi\lt 1`$: the correlation of fractional charges $`\pm\xi`$ at $`0`$ and $`x`$ satisfies $`0\le G_\xi(x)\le\mathrm{const}\,|x|^{-\beta'}`$ for $`x\ne0`$, with an exponent $`\beta'=\beta'(\beta,\xi,\varepsilon)\to\infty`$ as $`\beta\to\infty`$ and a constant that may depend on $`\beta`$.

Lean: [`conditionLambdaGas_secondMomentLimit_lower_bound`](FroehlichSpencer/BKT/Surface/ConditionLambdaGasTheoremA.lean) and [`conditionLambdaGas_fracCorrelationLimit_upper_bound`](FroehlichSpencer/BKT/Surface/ConditionLambdaGasTheoremB.lean), both in `FroehlichSpencer.BKT`. The finite-volume forms and the hard-core gas are separate anchors (`conditionLambdaGas_secondMoment_lower_bound`, `conditionLambdaGas_fracCorrelation_upper_bound`, `hardCoreGas_…`).

### Clock models

**The phase diagram.** There are thresholds $`0\lt \beta_h\le\beta_0`$ and $`\bar\beta(n)`$ such that, for the $`\mathbb Z_n`$ clock model:

- for $`n\ge2`$ and $`\beta\lt \beta_h`$, the fundamental harmonic decays exponentially;
- for $`n\ge2`$ and $`\beta\gt \bar\beta(n)`$, every harmonic has long-range order: its two-point function stays above a positive constant at arbitrarily large distances;
- for every margin $`q\in(0,1)`$ there are $`n_1`$ and $`\beta_1(n)\to\infty`$ with $`\beta_0\lt \beta_1(n)\le\bar\beta(n)`$ such that, for $`n\ge n_1`$ and $`\beta\in[\beta_0,\beta_1(n)]`$, the model is massless: every harmonic $`\xi=1,\dots,n-1`$ has a power-law lower bound, and the harmonics with $`\min(\xi/n,1-\xi/n)\ge q`$ have a power-law upper bound.

Lean: [`FroehlichSpencer.BKT.clock_phase_diagram`](FroehlichSpencer/BKT/Surface/ClockPhaseDiagram.lean). The intermediate phase needs $`n`$ large; the theorem does not give a value of $`n_1`$. The comparison of Theorem 7.1(1), rotator $`\le`$ clock, and the high-harmonic bound of Theorem 7.1(2) are [`planeRotatorCorrelation_le_clockCorrelation`](FroehlichSpencer/BKT/Surface/ClockDominatesRotator.lean) and [`clockCorrelation_highHarmonic_upper_bound`](FroehlichSpencer/BKT/Surface/ClockHighHarmonicDecay.lean).

**The disorder operator (7.5).** The disorder operator $`D^\xi_{0x}`$ twists the interaction by the angle $`2\pi\xi`$ across a line from $`0`$ to $`x`$. For $`n\ge n_1(\beta)`$ and the $`\mathbb Z_n`$ twists $`\xi=k/n`$, $`k=1,\dots,n-1`$, a thermodynamic limit of the disorder expectation exists, and every limit is at least $`C(1+r)^{-\xi^2\beta'''/(2\pi)}`$ at $`x=(r,0)`$, $`r\ge1`$, with $`C`$ and $`\beta'''`$ independent of $`k`$.

Lean: [`FroehlichSpencer.BKT.clock_disorder_lowerBound`](FroehlichSpencer/BKT/Surface/ClockDisorderLowerBound.lean). The paper states (7.5) for real $`\xi`$. A negative theorem, [`not_clock_disorder_lowerBound_offGrid`](FroehlichSpencer/BKT/Surface/ClockDisorderOffGrid.lean), shows that the same bound, with one $`\beta'''`$ for all real $`\xi\in(0,1)`$, cannot hold.

**The Villain-clock model (§7.1, Remark 4).** The three statements are repeated for the clock model with Villain action: the correlation comparison [`villain_clock_theorem71_1`](FroehlichSpencer/BKT/Surface/VillainClock/VillainClockTheorem71One.lean), the power-law upper bound for high harmonics on boxes and for the upper limit along free boxes [`villain_clock_theorem71_2`](FroehlichSpencer/BKT/Surface/VillainClock/VillainClockTheorem71Two.lean) (both in `FroehlichSpencer.BKT.Surface.VillainClock`), and the disorder bound on the $`\mathbb Z_N`$ grid for every limit point of an exhaustion by boxes, [`villainClock_disorder_lowerBound_grid_exhausting`](FroehlichSpencer/BKT/Surface/VillainClockDisorderLowerBound.lean).

### The Villain model and the solid-on-solid model

**Theorem D.** For each $`\xi\in(0,1)`$ there is $`\beta_0(\xi)`$ such that for $`\beta\gt \beta_0(\xi)`$ a limit of the disorder expectations of the Villain model along boxes $`[-R,R+1]^2`$ exists, and every such limit satisfies $`\langle D^\xi_{0x}\rangle(\beta)\le\mathrm{const}\,(1+n)^{-\xi^2\beta''}`$ at $`x=(n,0)`$, for some $`\beta''=\beta''(\xi,\beta)\gt 0`$.

Lean: [`FroehlichSpencer.BKT.freeVillain_disorderLimit_upper_bound`](FroehlichSpencer/BKT/Surface/FreeVillainTheoremD.lean); with wired boundary conditions, [`wiredVillain_disorder_upper_bound`](FroehlichSpencer/BKT/Surface/WiredVillainTheoremDFinite.lean) and [`wiredVillain_disorderLimit_upper_bound`](FroehlichSpencer/BKT/Surface/WiredVillainTheoremD.lean).

**Theorem 7.3 and roughening.** For the solid-on-solid model in the box $`\{0,\dots,L-1\}^2`$ with Dirichlet boundary conditions and $`\beta`$ small, there is $`\beta'(\beta)\gt 0`$, tending to $`0`$ with $`\beta`$, such that for $`L`$ large, all sites $`u,v`$ and all real $`\varepsilon`$,

```math
\bigl\langle e^{\varepsilon[\varphi(u)-\varphi(v)]}\bigr\rangle\ \ge\ e^{(\varepsilon^2/\beta')\log(1+r)},\qquad \bigl\langle[\varphi(u)-\varphi(v)]^2\bigr\rangle\ \ge\ \frac1{\beta'}\log(1+r),
```

where $`r`$ is $`|u-v|`$ capped by the distance from $`u`$ to the boundary. The exponential moment is a value in $`[0,\infty]`$; the second moment is finite. There are $`0\lt \beta_0\lt \beta_1`$ such that the height fluctuations $`\langle[\varphi(u)-\varphi(v)]^2\rangle`$ are unbounded over boxes and sites for $`\beta\le\beta_0`$, and bounded uniformly in $`\beta`$, the box and the sites for $`\beta\ge\beta_1`$.

Lean: [`sos_theorem73_dirichlet`](FroehlichSpencer/BKT/Surface/SOSTheorem73Dirichlet.lean) and [`sos_roughening_transition`](FroehlichSpencer/BKT/Surface/SOSRoughening.lean) in `FroehlichSpencer.BKT`. Theorem 7.3 for the state (7.16), read as a limit point with the comb inserted in each finite box, is [`sos_theorem73_literal`](FroehlichSpencer/BKT/Surface/SOSTheorem73Literal.lean).

### The finite-volume theorems of Kharash and Peled

The multiscale argument is carried out on finite squares $`\{0,\dots,L-1\}^2`$, $`L\gt 1`$, following Kharash and Peled. The four theorems hold with constants independent of $`L`$.

- **Theorem 1.1, the integer-valued Gaussian free field.** There is $`c\gt 0`$, and for every $`\varepsilon\gt 0`$ a $`\beta_0\gt 0`$, such that for $`\beta\lt \beta_0`$, on every free square and every periodic square of even side, and for every $`f`$ with $`\sum f=0`$: $`\mathbb E\,e^{\langle m,f\rangle}\ge\exp\bigl[\tfrac{1}{2(1+\varepsilon)\beta}\langle f,-\Delta^{-1}f\rangle\bigr]`$, the corresponding second-moment bound, and $`\mathbb E(m_j-m_k)^2\ge\tfrac c\beta\log(1+\mathrm{dist}(j,k))`$.

  Lean: [`FroehlichSpencer.BKT.integerGFF_delocalization`](FroehlichSpencer/BKT/Surface/IntegerGFFDelocalization.lean).
- **Theorem 1.3, the Villain model.** There are $`\beta_0`$ and $`C\gt 0`$ such that for $`\beta\gt \beta_0`$ and every site $`j`$ of the wired square, $`\mathbb E\cos\theta_j\ge(1+\mathrm{dist}(j,\partial))^{-C/\beta}`$, where $`\partial`$ is the wired boundary.

  Lean: [`FroehlichSpencer.BKT.villain_powerLaw_lower_bound`](FroehlichSpencer/BKT/Surface/VillainPowerLaw.lean).
- **Theorems 1.5 and 1.6, weighted Gaussian free fields.** For site weights that are even trigonometric polynomials with sub-Gaussian coefficients (`IsSubGaussian`, with parameter $`\theta\lt 1/16`$), an exponential-moment lower bound of the same form as in Theorem 1.1 holds at small $`\beta`$; and the Gaussian integral of the product of the weights equals a finite convex combination of integrals of products of factors $`1+z\cos(\cdot)`$ over neutral charge ensembles, with the activity and separation bounds of the renormalization.

  Lean: [`weightedGFF_expMoment_lower_bound`](FroehlichSpencer/BKT/Surface/WeightedGFFExpMoment.lean) and [`weightedGFF_renormalization`](FroehlichSpencer/BKT/Surface/WeightedGFFRenormalization.lean) in `FroehlichSpencer.BKT`, on free and even periodic squares.

## Massless phases in gauge theories and spin systems (FS82)

FS82 treats abelian lattice models whose defects are closed currents: the four-dimensional compact $`U(1)`$ lattice gauge theory, the $`\mathbb Z_N`$ gauge theories, and the classical XY model in dimension $`D\ge3`$. At large $`\beta`$ a renormalization of the currents, built on the multiscale expansion of FS81, shows that the defects only renormalize the coupling of a free massless field. Six groups of statements are formalized. For each, the anchor is linked together with the theorem of the library from which it is proved.

**Scope common to all six.** Every statement is in finite volume, with free boundary conditions for the gauge or spin model, or is a statement about limit points along the centered cubes. In the dual picture the free boundary becomes a field that vanishes outside the box. The paper obtains its infinite-volume expectations from Ginibre's correlation inequalities. That input is not formalized, so no statement below asserts that a thermodynamic limit exists or is unique. All constants are uniform in the volume.

Throughout, $`\varphi_\beta(x)=\sum_{n\in\mathbb Z}\exp[-\tfrac\beta2(x+2\pi n)^2]`$ is the Villain weight, $`d`$ is the lattice exterior derivative and $`\delta`$ its adjoint.

### The dual moment comparison (2.93)

In a box $`\Lambda\subset\mathbb Z^4`$ the Villain $`U(1)`$ model has link angles $`\theta`$ and the weight $`\prod_p\varphi_\beta(d\theta_p)`$ over plaquettes. Its dual is a gas of integer-valued 1-forms $`\alpha`$ on the dual box $`\Lambda^*`$, extended by zero outside it, with weight $`\exp[-\tfrac1{2\beta}\|d\alpha\|^2]`$, taken modulo integer gauge transformations $`\alpha\mapsto\alpha+d\gamma`$. The field strength of the gauge theory corresponds to the curvature $`d\alpha`$. The theorem is a statement about this dual gas; the duality itself is proved in the library and is used for the Wilson loop below.

**Theorem.** There are $`\beta_0\gt 0`$ and a function $`\beta''(\beta)`$ with $`0\lt \beta''(\beta)\lt \beta`$, $`\beta''(\beta)/\beta\to1`$ and $`\beta''(\beta)\to\infty`$ as $`\beta\to\infty`$, such that for every $`\beta\ge\beta_0`$, every log-thick box $`\Lambda`$, every real 1-form $`\mu`$ on $`\Lambda^*`$ with $`\delta\mu=0`$ and support in the interior, and every real $`\varepsilon`$,

```math
\exp\Bigl[\frac{\varepsilon^2\beta''}{2}\,(\mu,V_\Lambda\mu)\Bigr]\le\bigl\langle e^{\varepsilon\,\alpha(\mu)}\bigr\rangle_\Lambda(\beta)\le\exp\Bigl[\frac{\varepsilon^2\beta}{2}\,(\mu,V_\Lambda\mu)\Bigr].
```

Here $`\alpha(\mu)=\sum_\ell\mu_\ell\alpha_\ell`$, and $`V_\Lambda`$ is the inverse of $`\delta d`$ on the co-closed 1-forms of $`\Lambda^*`$, the Coulomb covariance of the box.

Lean: [`FroehlichSpencer.FS82.Surface.fs82FiniteVillainDualMomentComparisonLogThick`](FroehlichSpencer/FS82/Surface/FiniteVillainDualMomentComparisonLogThick.lean). Source: (2.93), in the finite-volume form of §2.12.

```lean
theorem fs82FiniteVillainDualMomentComparisonLogThick :
∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ,
      (∀ β : ℝ, β₀.val ≤ β → 0 < cPack β) ∧
      Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (nhds 0) ∧
      (∀ β : ℝ, β₀.val ≤ β →
        0 < betaDoublePrime cPack β ∧ betaDoublePrime cPack β < β) ∧
      Tendsto (betaDoublePrime cPack) atTop atTop ∧
      ∀ β : ℝ, (hβRange : β₀.val ≤ β) →
        ∀ R : RectBox4,
          IsLogThickRectBox4 R →
        ∀ μ : RealDualField R,
          ∀ hglobal : μ ∈ GlobalCoClosed R,
            ∀ hinterior : IsInteriorSupported R μ,
          ∀ ε : ℝ,
            ENNReal.ofReal
                (Real.exp (ε ^ 2 * betaDoublePrime cPack β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal))) ≤
              discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ∧
            discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ≤
              ENNReal.ofReal
                (Real.exp (ε ^ 2 * β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal)))
```

- The upper bound is the Gaussian bound at coupling $`\beta`$. The lower bound says that the integer constraint costs no more than a change of coupling from $`\beta`$ to $`\beta''`$. Expanding in $`\varepsilon`$ gives $`\beta''(\mu,V_\Lambda\mu)\le\langle\alpha(\mu)^2\rangle_\Lambda\le\beta(\mu,V_\Lambda\mu)`$, which is (2.92): the dual field fluctuates like a free massless field. This second-moment form is a remark, not part of the formal statement.
- A box with sides $`\ell_1,\dots,\ell_4\ge1`$ is *log-thick* if $`\log(1+\max_i\ell_i)\le\min_i\ell_i`$ (`IsLogThickRectBox4`). Every cube is log-thick. Boxes that are thin in one direction are not covered; the paper states (2.93) for an arbitrary finite region.
- $`\beta''(\beta)=\beta\,(1-2\beta\,c(\beta))`$ with $`c(\beta)\gt 0`$ and $`\beta c(\beta)\to0`$; the function $`c`$ is the same for all boxes and all $`\mu`$ (`betaDoublePrime`).
- The moment is a value in $`[0,\infty]`$ (`discreteDualMoment`); its finiteness is part of the upper bound. The condition $`\delta\mu=0`$ is imposed on the extension of $`\mu`$ by zero to $`\mathbb Z^4`$ (`GlobalCoClosed`), and $`\mu`$ vanishes on the links that touch the boundary (`IsInteriorSupported`). For such $`\mu`$ this is the same as $`\delta\mu=0`$ at every vertex of $`\Lambda^*`$.

### Infinite volume: every limit state along cubes (2.90)–(2.93)

A *cube-limit state* is a consistent family of joint laws of the curvatures $`(d\alpha)_p`$ on the finite sets of plaquettes of $`\mathbb Z^4`$, obtained as the limit, along one subsequence of the cubes $`[-N,N]^4`$, of the finite-volume laws. Compactness gives at least one for every $`\beta\gt 0`$ ([`exists_cubeCurvatureLimitState`](FroehlichSpencer/FS82/Infinite/LimitStateLimit.lean)).

**Theorem.** There are $`\beta_0`$ and a function $`\beta''`$ with the same properties as above such that for every $`\beta\ge\beta_0`$, every cube-limit state $`\langle\cdot\rangle`$, every finitely supported real 1-form $`\mu`$ on $`\mathbb Z^4`$ with $`\delta\mu=0`$, every finitely supported 2-form $`\sigma`$ with $`\delta\sigma=\mu`$, and every real $`t`$,

```math
\exp\Bigl[\frac{t^2\beta''}{2}\,(\mu,(-\Delta)^{-1}\mu)\Bigr]\le\bigl\langle e^{t\,(\sigma,d\alpha)}\bigr\rangle\le\exp\Bigl[\frac{t^2\beta}{2}\,(\mu,(-\Delta)^{-1}\mu)\Bigr],
\qquad
(\mu,(-\Delta)^{-1}\mu)=\int_{\mathbb T^4}\frac{\sum_i|\widehat\mu_i(k)|^2}{\sum_i|1-e^{ik_i}|^2}\,dk .
```

Lean: [`FroehlichSpencer.FS82.SurfaceInfinite.source_infiniteVolume_momentComparison`](FroehlichSpencer/FS82/SurfaceInfinite/SourceInfiniteVolumeMomentComparison.lean); library theorem [`FroehlichSpencer.FS82.Infinite.cubeCurvatureLimitState_sourceFilling_mgf_bounds`](FroehlichSpencer/FS82/Infinite/LimitStateRoot.lean). Source: (2.90)–(2.93).

- The integral is over $`\mathbb T^4=(\mathbb R/2\pi\mathbb Z)^4`$ with its normalized Haar measure (`fourierGreenQuadratic`).
- $`(\sigma,d\alpha)=\alpha(\mu)`$ whenever $`\delta\sigma=\mu`$. The state is a state of the gauge-invariant curvature, so the observable is written through a filling $`\sigma`$; one exists for every such $`\mu`$ (Lemma 1 of the paper, formalized).
- The statement holds for *every* cube-limit state. It does not say that the limit along the cubes exists, that the state is unique, or that it is the state the paper obtains from Ginibre's inequalities.

### The photon is massless (the display after (2.91))

**Theorem.** There is $`\beta_1\gt 0`$ such that for every $`\beta\ge\beta_1`$ there is a translation-invariant state $`\langle\cdot\rangle`$ of the dual curvature on $`\mathbb Z^4`$ whose two-point function

```math
C(x)=\bigl\langle (d\alpha)_{p_0}\,(d\alpha)_{p_0+x}\bigr\rangle ,\qquad x\in\mathbb Z^4,
```

for the plaquette $`p_0`$ at the origin in the 0–1 plane, is not absolutely summable: $`\sum_x|C(x)|=\infty`$. The state is a limit, along a subsequence, of the averages over the boxes $`[-s,s]^4`$ of the translates of a cube-limit state.

Lean: [`FroehlichSpencer.FS82.SurfaceInfinite.source_curvatureCorrelation_nonsummable`](FroehlichSpencer/FS82/SurfaceInfinite/SourceCurvatureCorrelationNonsummable.lean); library theorem [`FroehlichSpencer.FS82.Infinite.Nonsummability.fs82_root_nonsummable_fieldStrengthCorrelation`](FroehlichSpencer/FS82/Infinite/NonsummabilityRoot.lean). Source: §2.11, the unnumbered display after (2.91): the field-strength correlation "cannot have summable fall-off".

- Under duality $`(d\alpha)_{p^*}`$ is the field strength $`\Phi_p`$ of (2.89) on the plaquettes parallel to the 2–3 plane. A correlation that decays exponentially would be summable, so in this state the correlation does not decay exponentially: there is no mass gap. This is the sense in which the paper calls the photon massless.
- The statement is about the dual observable, in one selected stationary state and one lattice plane.

**Theorem (the field strength itself).** In the same state, with $`\Phi_p=-i\,\varphi_\beta'(d\theta_p)/\varphi_\beta(d\theta_p)`$ the field strength (2.89) of the Villain model: along one subsequence of the cubes $`\Lambda_{N_k}`$ and for every $`x\ne0`$,

```math
\frac1{|B_{s_k}|}\sum_{a\in B_{s_k}}\bigl\langle\Phi_{p_a}\,\Phi_{p_{a+x}}\bigr\rangle_{\Lambda_{N_k}}(\beta)\ \longrightarrow\ C(x),
```

where $`p_a`$ is the plaquette at $`a`$ in the 2–3 plane, dual to the plaquette of $`C`$, and $`B_s=[-s,s]^4`$ are the averaging boxes of the state. So the finite-volume two-point functions of $`\Phi`$ converge, after averaging over translations, to a function that is not absolutely summable.

Lean: [`FroehlichSpencer.FS82.SurfaceInfinite.source_primalFieldStrength_nonsummable`](FroehlichSpencer/FS82/SurfacePrimal/SourcePrimalFieldStrengthNonsummable.lean), with $`\Phi`$ as [`sourcePrimalFieldStrength`](FroehlichSpencer/FS82/SurfacePrimal/SourcePrimalFieldStrength.lean); library theorem [`FroehlichSpencer.FS82.Infinite.Nonsummability.primal_selectedPrimalFølnerLimit_not_absSummable`](FroehlichSpencer/FS82/Infinite/NonsummabilityPrimalLimit.lean). Source: (2.89) and §2.11.

- The diagonal $`x=0`$ is excluded. There the finite-volume identity has an extra contact term from the derivative in $`\Phi`$, and a single value does not affect summability.
- Neither theorem is about a unique Gibbs state, and no infinite-volume state of the angles $`\theta`$ is constructed.

### Wilson loops: area law, perimeter law and the transition (1.13), (2.7), (2.8)

Let $`W(\mathcal L_{L\times T})=\prod_{xy\in\mathcal L}e^{i\theta_{xy}}`$ be the Wilson loop of an $`L\times T`$ rectangle in the 0–1 plane, in the Villain $`U(1)`$ model with unit charge on the cube $`\Lambda_N=[-N,N]^4`$, $`N\ge\max(L,T)+1`$.

**Theorem.** There are $`0\lt \beta_0\lt \beta_1`$ and $`c\gt 0`$ such that for all $`L,T\ge1`$ and all such cubes the expectation $`\langle W(\mathcal L_{L\times T})\rangle_{\Lambda_N}(\beta)`$ is real and

```math
0\le\langle W(\mathcal L_{L\times T})\rangle_{\Lambda_N}(\beta)\le e^{-c\,LT}\quad(0\lt \beta\le\beta_0),
\qquad
\langle W(\mathcal L_{L\times T})\rangle_{\Lambda_N}(\beta)\ge e^{-d(\beta)(L+T)}\quad(\beta\ge\beta_1),
```

with $`d(\beta)\ge0`$ independent of $`L`$, $`T`$ and $`N`$.

Lean: five roots in `FroehlichSpencer.FS82.Surface`. The library theorems are in `FroehlichSpencer.FS82`:

| Root | Statement | Library theorem |
| --- | --- | --- |
| [`fs82WilsonLoopPerimeterLawCube`](FroehlichSpencer/FS82/Surface/WilsonLoopPerimeterLawCube.lean) | the perimeter law (1.13), (2.8) on the cubes | [`Wilson.fs82_wilson_perimeter_cube`](FroehlichSpencer/FS82/Wilson/PerimeterRoot.lean) |
| [`fs82WilsonLoopAreaLawCube`](FroehlichSpencer/FS82/Surface/WilsonLoopAreaLawCube.lean) | the area law (2.7) on the same cubes | [`Wilson.cubePrimalSheet_smallBeta_areaLaw`](FroehlichSpencer/FS82/Wilson/AreaLawPositioned.lean) (the two inequalities; that the expectation is real is a separate lemma) |
| [`fs82WilsonLoopTransitionCube`](FroehlichSpencer/FS82/Surface/WilsonLoopTransitionCube.lean) | both laws, with $`\beta_0\lt \beta_1`$ | [`Wilson.fs82_wilson_transition_cube`](FroehlichSpencer/FS82/Wilson/AreaLawPositioned.lean) |
| [`fs82WilsonLoopPerimeterLawCubeLimit`](FroehlichSpencer/FS82/Surface/WilsonLoopPerimeterLawCubeLimit.lean) | (2.8) for the sequence $`N\mapsto\langle W\rangle_{\Lambda_N}`$ | [`Wilson.fs82_wilson_perimeter_cube_limit`](FroehlichSpencer/FS82/Wilson/PerimeterLimit.lean) |
| [`fs82WilsonLoopAreaLawCubeLimit`](FroehlichSpencer/FS82/Surface/WilsonLoopAreaLawCubeLimit.lean) | (2.7) for the same sequence | follows from the area root ([`Provider.fs82WilsonLoopAreaLawCubeLimit`](FroehlichSpencer/FS82/Provider/WilsonLoopAreaLawCubeLimit.lean)) |

- The two limit roots say: the sequence has a limit point; every limit point satisfies the bound, and so does the lower limit (perimeter) or the upper limit (area); and so does the limit, if it exists. The existence of the limit (2.6) is not proved.
- The area law is proved for $`\beta\le1/80`$ with $`c=1/2`$, by a separate strong-coupling expansion: the connected surface attached to the loop is extracted and such surfaces are counted. The paper's rate $`c(\beta)\approx\log\beta^{-1}`$ is not claimed. Nothing is said for $`\beta_0\lt \beta\lt \beta_1`$, and no single transition point is asserted.
- The perimeter bound holds for every cube with $`N\ge\max(L,T)+1`$, with one $`d(\beta)`$. This makes explicit the "provided $`\Lambda`$ is large enough" of (1.13).

### $`\mathbb Z_N`$ gauge theories: a perimeter law for the disorder operator (3.54)

On the cube of side $`2M`$ in $`\mathbb Z^4`$, take Wilson's action $`\beta\sum_p\cos(d\theta_p)`$ and weight every link by $`e^{h\cos(N\theta_{xy})}`$, normalized. For $`h=0`$ this is the $`U(1)`$ theory, and as $`h\to\infty`$ the angles are pinned to the $`N`$-th roots of unity: the $`\mathbb Z_N`$ gauge theory. The disorder operator $`D_\xi`$ of an $`L\times T`$ rectangle shifts $`d\theta_p`$ by $`2\pi\xi/N`$ on the $`LT`$ plaquettes dual to the rectangle; its expectation is the ratio of the shifted and unshifted partition functions.

**Theorem.** There is $`C\gt 0`$ such that for every $`\beta\gt 0`$ there is $`N_0(\beta)`$ with: for all $`N\ge N_0(\beta)`$, all integers $`1\le\xi\lt N`$, all $`L,T\ge1`$, every cube with $`M\ge\max(L,T)`$, and every $`h\in[0,\infty)`$,

```math
\langle D_\xi(L\times T)\rangle_{M,h}(\beta)\ \ge\ \exp\Bigl[-C\,\beta\,\Bigl(\frac{\xi}{N}\Bigr)^{2}(L+T)\Bigr],
```

and the same bound holds in the $`\mathbb Z_N`$ theory itself.

Lean: [`FroehlichSpencer.FS82.SurfaceZN.fs82_zn_disorder_perimeter_root`](FroehlichSpencer/FS82/SurfaceZN/fs82_zn_disorder_perimeter_root.lean); library theorem [`FroehlichSpencer.FS82.ZN.fs82_zn_disorder_perimeter_root`](FroehlichSpencer/FS82/ZN/DisorderRoot.lean). Source: (3.54), with the model of (3.6)–(3.8) and the disorder operator of (3.21)–(3.22), (3.28).

- $`C`$ does not depend on $`\beta`$, and $`N_0`$ depends on $`\beta`$ only. The proof gives $`C=12\pi^2+2`$.
- The $`\mathbb Z_N`$ theory is a separate finite sum over $`\mathbb Z_N`$-valued link variables, not the value of the interpolation at an infinite $`h`$; its bound is obtained as $`h\to\infty`$.
- The paper states (3.54) for arbitrary regions. The theorem is for centered cubes, with free boundary conditions. Other boxes are not covered, and no infinite-volume state of the $`\mathbb Z_N`$ theory is constructed.

### Long-range order in the XY model, $`D\ge3`$ (4.40)

The Villain XY model on the cube $`\Lambda_N=[0,2N]^D`$ has an angle $`\theta_x`$ at every site and the weight $`\prod_{\langle xy\rangle}\varphi_\beta(\theta_x-\theta_y)`$ over the bonds of the cube.

**Theorem.** For every $`D\ge3`$ there are $`\beta_0\gt 0`$ and $`C\ge0`$, depending only on $`D`$, such that for every $`\beta\ge\beta_0`$, every $`N\ge0`$ and all sites $`x,y\in\Lambda_N`$,

```math
\langle\cos(\theta_x-\theta_y)\rangle_{\Lambda_N}(\beta)\ \ge\ e^{-C/\beta}.
```

Lean: [`FroehlichSpencer.FS82.SurfaceXY.fs82_xy_spinCorrelation_root`](FroehlichSpencer/FS82/SurfaceXY/fs82_xy_spinCorrelation_root.lean); library theorem [`FroehlichSpencer.FS82.XY.DualD.fs82_xyD_spinCorrelation_root`](FroehlichSpencer/FS82/XY/SpinTheoremD.lean). Source: (4.40), with the model (4.4)–(4.5) and the observable (4.22).

```lean
theorem fs82_xy_spinCorrelation_root :
    ∀ D : ℕ, 3 ≤ D →
      ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧
        ∀ β : ℝ, β₀ ≤ β → ∀ N : ℕ,
          ∀ x y : XYSite (xyCubeFamily D N),
            Real.exp (-(C / β)) ≤ xySpinCorrelation β x y
```

- The bound does not depend on the distance between $`x`$ and $`y`$ or on the size of the cube: the spins are ordered. Since the correlation is at most $`1`$, it tends to $`1`$ as $`\beta\to\infty`$, uniformly in the sites and the cube.
- Three companion anchors hold for $`\beta\gt 0`$ and every box: the partition function is positive, the Gibbs measure is a probability measure, and the correlation above is the integral of $`S_x\cdot S_y`$ against it ([`xyVillainPartition_pos`](FroehlichSpencer/FS82/SurfaceXY/xyVillainPartition_pos.lean), [`xyVillainLaw_isProbabilityMeasure`](FroehlichSpencer/FS82/SurfaceXY/xyVillainLaw_isProbabilityMeasure.lean), [`xySpinCorrelation_eq_integral`](FroehlichSpencer/FS82/SurfaceXY/xySpinCorrelation_eq_integral.lean)).
- The constants are explicit and not optimized: $`\beta_0=\max\{1,(D+b)/\kappa\}`$ with $`\kappa=\pi^2/(4D^2)`$ and $`b=1+\tfrac12\,6^D\log3`$. For $`D=3`$ a separate proof in the library gives the threshold $`\beta_0=144`$ ([`FroehlichSpencer.FS82.XY.xy3_spinCorrelation_lower`](FroehlichSpencer/FS82/XY/SpinRoot3.lean)); it is not one of the anchors.
- (4.40) is printed for the limit $`\Lambda\nearrow\mathbb Z^D`$. The theorem is the finite-volume bound, uniform in the cube; the limit is not taken. Boxes that are not cubes are not covered.

### How the proofs go

The proof of (2.93) follows §2.12 of the paper. The substitution $`\tau=\varepsilon\beta V_\Lambda\mu`$ of (2.94) separates the Gaussian value $`\exp[\tfrac{\varepsilon^2\beta}{2}(\mu,V_\Lambda\mu)]`$ from a remaining factor, which is at most $`1`$; the lower bound on that factor is the content of the theorem. Poisson summation writes it as an average of products of cosines indexed by closed integer currents. The expansion of FS81 groups the currents into separated ensembles with renormalized activities. The result is a mixture, with positive weights, of terms to each of which Jensen's inequality applies, and a packing estimate for the currents bounds every term from below by $`\exp[-c(\beta)\|d\tau\|^2]`$. In the proof $`c(\beta)=Ce^{-\beta/432}`$, the same for all boxes, and this is the change from $`\beta`$ to $`\beta''`$.

The perimeter law, the disorder bound and the XY bound use the same expansion with the field of another source: the surface spanned by the Wilson loop, the sheet of the disorder operator, a path from $`x`$ to $`y`$. In a finite box such a source is not exact, and the new input in each case is a bound on the energy of its non-exact part, the residual of (2.50): by a multiple of $`L+T`$ for the loop and the sheet, and by a constant depending only on $`D`$ for the path. These bounds are proved on cubes, which is why the three theorems are stated there.

## Anderson localization (FS83)

The operator is $`H=-\Delta+v`$ on $`\ell^2(\mathbb Z^\nu)`$, $`\nu\ge1`$, with $`v(x)`$ independent and identically distributed, and $`G(z,v;x,y)`$ is its Green function. $`|x|`$ is the Euclidean length.

**The Green function and the density of states.** For every real potential $`v`$, bounded or not, every $`z`$ with $`\mathrm{Im}z\ne0`$ and every site $`y`$, the equation $`(-\Delta+v-z)\psi=\delta_y`$ has exactly one square-summable solution. For every single-site law with a bounded density there is exactly one function $`N(E)`$ to which the normalized eigenvalue counting functions of the cubes $`[-L,L]^\nu`$ converge, almost surely and for all $`E`$ at once.

Lean: [`FroehlichSpencer.existsUnique_squareSummable_greenSolution`](FroehlichSpencer/Surface/InfiniteGreenWellDefined.lean) and [`FroehlichSpencer.existsUnique_integratedDensityOfStates`](FroehlichSpencer/Surface/IDSWellDefined.lean).

**Theorem 1.2.** For all $`m,p\gt 0`$ there are a constant $`K`$ and thresholds, depending on $`\nu`$, $`m`$, $`p`$ (and on the variance in the Gaussian regime), such that in each of the two regimes below, for every energy $`E`$ in the regime, every site $`x`$ and every $`N\gt 0`$,

```math
\mathbb P\Bigl\{\,|G(E+i\varepsilon,v;0,x)|\le e^{m(N-|x|)}\ \text{ for all real }\varepsilon\ne0\Bigr\}\ \ge\ 1-\frac{K}{N^{p}} .
```

- *Large disorder.* The single-site law has a density bounded by a small constant, and $`E`$ is arbitrary.
- *High energy.* The single-site law is Gaussian with variance $`\gamma`$, and $`|E-2\nu|`$ is at least a constant depending on $`\gamma`$, $`m`$, $`p`$.

Lean: [`FroehlichSpencer.green_probability_bound`](FroehlichSpencer/Surface/T12.lean); for the operator restricted to any finite set $`\Lambda\ni0,x`$ with Dirichlet boundary conditions, uniformly in $`\Lambda`$, [`FroehlichSpencer.finiteVolumeGreen_probability_bound`](FroehlichSpencer/Surface/T12Lambda.lean). The event concerns all $`\varepsilon\ne0`$ simultaneously, and its measurability is part of the conclusion.

**Theorem 1.1.** In the same two regimes (with thresholds depending on $`\nu`$, and on $`\gamma`$ in the Gaussian case), at every energy $`E`$ where the integrated density of states has a derivative $`\rho(E)\gt 0`$,

```math
\lim_{\varepsilon\downarrow0}\ \frac{2\varepsilon^2}{\pi\nu}\sum_{x\in\mathbb Z^\nu}|x|^2\,\mathbb E\,|G(E+i\varepsilon,v;0,x)|^2\ =\ 0 ,
```

that is, the diffusion coefficient $`D(E)`$ defined by the Kubo formula vanishes.

Lean: [`FroehlichSpencer.theorem_1_1`](FroehlichSpencer/Surface/Theorem11.lean). The left side is $`\rho(E)D(E)`$ (`kuboQuantity`, `is_diffusion_coefficient`).

**Almost-sure decay.** In the same regimes, for every $`m\gt 0`$, almost surely there is a radius $`R`$ such that $`|G(E+i\varepsilon,v;0,x)|\le e^{-m|x|/2}`$ for all $`|x|\ge R`$ and all $`\varepsilon\ne0`$.

Lean: [`FroehlichSpencer.green_almostSure_decay`](FroehlichSpencer/Surface/GreenAlmostSure.lean).

## Build and verify

Install [Lean's elan toolchain manager](https://github.com/leanprover/elan). From a fresh checkout, run:

```sh
lake exe cache get
lake build
```

The toolchain is **`leanprover/lean4:v4.35.0-rc2`**. Mathlib is **`v4.35.0-rc2`**, resolved in `lake-manifest.json` to **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. The manifest pins all dependencies. The library has 1,659 Lean files and 365,883 physical lines; a full build compiles every one of them.

To see the axioms of a theorem, for example the root (2.93):

```lean
import FroehlichSpencer.FS82.Surface.FiniteVillainDualMomentComparisonLogThick
#print axioms FroehlichSpencer.FS82.Surface.fs82FiniteVillainDualMomentComparisonLogThick
```

The **Build and verify** workflow builds the library, rejects proof escapes outside comparator Challenges, checks the axioms of every main result in `formalization.yaml`, checks module headers and comparator sizes, and validates the metadata against the pinned v0.4 schema. Continuous integration runs both workflows on every push to `main` and on every pull request.

From the repository root, rerun the public source and axiom checks with:

```sh
python3 -I scripts/check_proofs.py
python3 -I scripts/check_lean_modules.py --root .
python3 -I .github/scripts/check_axioms.py
```

The four [comparator packages](comparators/) check 33 source-facing root statements from FS81, Kharash–Peled, FS82 and FS83. Each Challenge imports only Mathlib and gives literal definitions and theorem statements, with intentional `sorry` obligations. Each Solution proves the selected statements using the library interfaces. Supporting existence and characterization theorems are included where definitions require them. The separate explicit-constant three-dimensional XY estimate is covered by the axiom check; the FS82 comparator covers the all-dimensional root.

To compare all four Solutions with their Challenges and replay them through the bundled independent kernels, run:

```sh
scripts/verify_comparator.sh
```

This requires `bubblewrap` and the tools bundled with the pinned Lean toolchain. Set `SKIP_CACHE_GET=1` if dependencies are already installed. To check just one group, pass, for example, `comparators/FS83/comparator.json`. The **Comparators** workflow runs the same command.

For the optional metadata and registry preparation check, install `PyYAML==6.0.2` and `jsonschema==4.23.0`, then run `scripts/check_palomar.py` with `--schema` pointing to the [pinned v0.4 schema](https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json).

## Library map

The source-facing interfaces are in the `Surface*` directories; each theorem anchor names the library theorem that proves it.

| Directory | Content |
| --- | --- |
| [`FroehlichSpencer/Surface`](FroehlichSpencer/Surface/) | FS83 anchors: the Anderson model, Green function, density of states, Theorems 1.1 and 1.2 |
| [`FroehlichSpencer/T12`](FroehlichSpencer/T12/), [`Multiscale`](FroehlichSpencer/Multiscale/), [`Reduction`](FroehlichSpencer/Reduction/), [`IDS`](FroehlichSpencer/IDS/) | The multiscale analysis of FS83, the reduction of Theorem 1.1 to Theorem 1.2, the integrated density of states |
| [`FroehlichSpencer/BKT/Surface`](FroehlichSpencer/BKT/Surface/) | FS81 and Kharash–Peled anchors |
| [`BKT/Generic`](FroehlichSpencer/BKT/Generic/), [`Charges`](FroehlichSpencer/BKT/Charges/), [`SpinWaves`](FroehlichSpencer/BKT/SpinWaves/), [`Gaussian`](FroehlichSpencer/BKT/Gaussian/) | The multiscale expansion: charge ensembles, renormalization, spin waves, Gaussian fields on finite graphs |
| [`BKT/Rotator`](FroehlichSpencer/BKT/Rotator/), [`Clock`](FroehlichSpencer/BKT/Clock/), [`Coulomb`](FroehlichSpencer/BKT/Coulomb/), [`Villain`](FroehlichSpencer/BKT/Villain/), [`VillainDisorder`](FroehlichSpencer/BKT/VillainDisorder/), [`SOS`](FroehlichSpencer/BKT/SOS/) | The models of FS81 and their thermodynamic limits |
| [`FroehlichSpencer/FS82/Surface`](FroehlichSpencer/FS82/Surface/), [`SurfaceInfinite`](FroehlichSpencer/FS82/SurfaceInfinite/), [`SurfacePrimal`](FroehlichSpencer/FS82/SurfacePrimal/), [`SurfaceZN`](FroehlichSpencer/FS82/SurfaceZN/), [`SurfaceXY`](FroehlichSpencer/FS82/SurfaceXY/) | FS82 anchors: the finite-volume root (2.93) and the Wilson loop; infinite volume and the massless photon; the field strength (2.89); the $`\mathbb Z_N`$ disorder operator; the XY model |
| [`FS82/Provider`](FroehlichSpencer/FS82/Provider/), [`SourceInterface`](FroehlichSpencer/FS82/SourceInterface/), [`PrimalInterface`](FroehlichSpencer/FS82/PrimalInterface/), [`SurfaceInfiniteProof`](FroehlichSpencer/FS82/SurfaceInfiniteProof/), [`SurfacePrimalProof`](FroehlichSpencer/FS82/SurfacePrimalProof/) | The proofs of the FS82 anchors from the library theorems |
| [`FS82/Cubical`](FroehlichSpencer/FS82/Cubical/), [`Gaussian`](FroehlichSpencer/FS82/Gaussian/), [`Poisson`](FroehlichSpencer/FS82/Poisson/) | Cubical complexes of boxes in any dimension, the boundary and Hodge operators, Gaussian measures on co-closed forms, the Poisson summation that produces the dual model |
| [`FS82/Currents`](FroehlichSpencer/FS82/Currents/), [`Moment`](FroehlichSpencer/FS82/Moment/), [`Root`](FroehlichSpencer/FS82/Root/) | The expansion in closed currents, its renormalization and packing estimates, and the proof of (2.93) |
| [`FS82/Infinite`](FroehlichSpencer/FS82/Infinite/) | Limit states along cubes, the Fourier form of the covariance, nonsummability |
| [`FS82/Wilson`](FroehlichSpencer/FS82/Wilson/), [`ZN`](FroehlichSpencer/FS82/ZN/), [`XY`](FroehlichSpencer/FS82/XY/) | Wilson loops, the $`\mathbb Z_N`$ disorder operator, the XY model in dimension $`D\ge3`$ |

## How this was built

The Lean code was written with AI coding agents under the authors' supervision. The authors approved every exact Lean definition and theorem statement, and Lean checks the proofs against those statements. The models and tools are recorded in [`formalization.yaml`](formalization.yaml).

## Authors and citation

The Lean development is by

- **Scott Armstrong** — CNRS and Laboratoire Jacques-Louis Lions, Sorbonne Université; Courant Institute School of Mathematics, Computing, and Data Science, New York University
- **Amélie Loher** — All Souls College, University of Oxford

If you use this formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong was supported by the European Research Council (ERC) under the European Union's Horizon Europe research and innovation programme, grant agreement No. 101200828.
Amélie Loher acknowledges support from the Fondation Sciences Mathématiques de Paris.

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see [`LICENSE`](LICENSE)). The license does not cover the cited papers.
