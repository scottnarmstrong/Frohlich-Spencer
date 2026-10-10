# Errata and deviations

This list separates printed errors from choices about scope, conventions and interpretation. FS81, FS82 and FS83 use the journal page and equation numbers in the README; Kharash–Peled uses arXiv:1711.04720v1. A grouped entry may cover repeated occurrences of the same error. Counts refer to entries, including editorial misprints, rather than to occurrences. Proof supplements are listed as deviations when they fill an omitted argument without establishing that the printed theorem is false.

| Source | Errata | Deviations |
|---|---:|---:|
| FS81 | 18 | 18 |
| Kharash–Peled | 48 | 10 |
| FS82 | 21 | 13 |
| FS83 | 22 | 11 |

## FS81

### Errata

1. **p. 535, (1.40), exhaustion.** The thermodynamic limit is written $\lim_{n\to\infty}$ although $n$ is the fixed clock order. Read $\lim_{\Lambda\uparrow\mathbb Z^2}$, as in the following sentence. No effect on the stated theorems.

2. **p. 535, (1.40), product measure.** A minus sign separates $e^{-\beta H_n(\theta)}$ and $\prod_jd\theta_j$. Read multiplication by the product measure. No effect on the stated theorems.

3. **pp. 550–551, Lemma 3.1, fibre counts.** The counts use $N_{j,m}$ although (3.15) defines $N_{m,j}=\{k:\gamma^m(k)=j\}$. Use $N_{m,j}$ consistently. No effect on the stated theorems.

4. **pp. 548–549, Lemma 3.1, scale offset.** The recurrence uses $\gamma(k)=\lfloor\alpha^{-1}(k-b-2)\rfloor$ but its iteration sets $\delta=b-2$. Iterate with $\delta=b+2$, and recompute the auxiliary constants consistently. No effect on the stated theorems.

5. **p. 551, §4, activity estimate.** The parenthetical $d(\rho)\ge2$ excludes a nearest-neighbour neutral dipole, whose Euclidean diameter is 1. Use $d(\rho)\ge1$ and the full floor count in the scale estimate. No effect on the stated theorems.

6. **p. 562, (4.57) and following bound.** The selected density is $\rho^*$, but the display uses $K(\rho)$ and $z(\rho,\beta)$, and the lower bound uses $A\prime(\rho)$. Use $\rho^*$ in these three places, consistently with (4.58). No effect on the stated theorems.

7. **p. 566, path used after (5.22).** The path begins at $j_0$ and the sum begins at $m=0$, but adjacency is imposed only for $m=1,\ldots,\ell-1$. Impose $|j_m-j_{m+1}|=1$ also for $m=0$. No effect on the stated theorems.

8. **p. 570, (5.39).** The local Fourier expansion prints $\le$, while (5.40) uses an identity. Use the exact identity at finite Fourier cutoff; pass to Gaussian-damped limits, rather than asserting pointwise convergence of the undamped series. No effect on the stated theorems.

9. **p. 575, (5.63).** The absolute-value estimate has a factor $\xi$, while the allowed charges include negative $\xi$. Replace that factor by $|\xi|$. The squared estimate (5.64) is unchanged.

10. **p. 585, Theorem 7.1(2).** The text prints “ther exists”. Read “there exists”. No effect on the stated theorems.

11. **p. 586, local formula preceding (7.8).** The local marked formula prints $\le$, but the surrounding text and summed (7.8) state an identity. Use the exact marked identity; an inequality between signed factors does not establish that identity. No effect on the stated theorems.

12. **p. 587, duplicate (7.9).** The edge-weight definition and the renormalized integral identity both carry (7.9). Distinguish them as “edge weight (7.9)” and “Theorem 7.2 identity (7.9)”. No effect on the stated theorems.

13. **p. 585, (7.5), allowed disorder twists.** The printed all-real reading $0\lt\xi\lt1$ is false with the shared exponent and thresholds. Restrict to genuine clock twists $\xi=k/N$, $1\le k\lt N$. At $\xi=1/(2N)$ the expectation decays exponentially in the seam length. The failure of the all-real statement is a theorem of the library; the clock and Villain-clock lower bounds use the grid restriction. See [ClockDisorderOffGrid](../FroehlichSpencer/BKT/Surface/ClockDisorderOffGrid.lean).

14. **p. 590, §7.2, interpolation condition (d).** The printed bound for the first two derivatives of $\log(I_\beta(\phi+ia)/I_\beta(\phi))$ is $C\beta^{1/3}g(a)$ with $g(a)=O(a^2)$. It is impossible: the first derivative bound forces the analytic logarithm to be affine, and evenness forces it to be constant, contradicting $I_\beta(0)=1$, $I_\beta(1)=e^{-\beta}$. The library proves this impossibility. For Appendix C interpolation the replacement is $C\beta^{2/3}e^{2\pi|a|}$ for both derivatives when $0\lt\beta\le1$ and $\beta^{1/3}|a|\le1/2$; the first derivative has the sharper $C\beta^{2/3}|a|$ bound when also $|a|\le1$. The impossibility theorem is `not_literal_derivative_bound` in the companion Inconsistency module. See [Translation](../FroehlichSpencer/BKT/SOS/Interp/Translation.lean).

15. **p. 598, (B.6).** The cubic imaginary term in $X(\theta)$ has a plus sign. Substituting $h(u)=u^{-3}(\sin u-u)$ into (B.4) gives a minus sign before $i\beta\sinh(r)\sigma^{-3}\theta^3h(\sigma^{-1}\theta)$. Only its size and odd imaginary parity are needed, so the stated theorems are unchanged.

16. **p. 598, before (B.10).** The text asserts $-s|X(\theta)|+\theta^2/2\gt\theta^2/4$ on the whole interval. At $\theta=0$, $X(0)=0$ and this says $0\gt0$. The proof instead uses the exact real contour integral and Gaussian comparison. No effect on the stated theorems.

17. **p. 598, (B.11).** The denominator is printed $\sqrt{2\pi\sigma}$. Combining (B.7) and (B.9) gives $\sqrt{2\pi}\,\sigma$. This agrees with the leading factor in Appendix C. No effect on the stated theorems.

18. **p. 585, Remark 3 after (7.5).** The disorder operator is said to be defined in (1.31), which is a spin-correlation bound. Read (1.32), the definition of $D^\xi$. No effect on the stated theorems.

### Deviations

1. **pp. 530, 571, Condition λ and (5.37)–(5.38).** Theorem A and Theorem B assume symmetric nonnegative activities and a positive vacancy weight, quantitatively $\lambda(0)\ge\nu\gt0$. The paper does not explicitly impose this in Condition λ. Normalize by this positive weight before using constant-one Fourier factors. Zero vacancy is outside the formalized class. See [ConditionLambdaGasTheoremAFinite](../FroehlichSpencer/BKT/Surface/ConditionLambdaGasTheoremAFinite.lean).

2. **pp. 531–532, (1.15)–(1.18).** The second-moment statement uses the test-function pairing (1.15). The exact Stillinger–Lovett constant $M(\beta)=2/\beta$ in (1.18), unconditional absolute infinite sums, and an identification with every screening convention are not asserted.

3. **pp. 532–533, Theorem B, (1.24)–(1.25).** The valid coarse Jensen lower bound (1.24) is retained; its sharper $\xi^2$ version is a separate consequence. Thresholds may depend on the fixed fractional charge and activity. The whole-range upper bound permits a $\beta$-dependent prefactor and is stated for nonzero separation using the Euclidean distance; it does not claim uniform thresholds as $\xi\to0,1$. See [ConditionLambdaGasTheoremBFinite](../FroehlichSpencer/BKT/Surface/ConditionLambdaGasTheoremBFinite.lean).

4. **pp. 533–535, (1.26), (1.35)–(1.38), Theorems C and D.** The plane-rotator and clock free two-point limits are constructed as unique observable limits. Theorem D in boundary condition (1.35) gives existence of limit points along the specified boxes and its bound for every limit point. It does not assert convergence of the entire Villain sequence, uniqueness, or a full Gibbs/DLR characterization. Wired Villain results are stated separately.

5. **pp. 538–539, (2.9)–(2.10).** Finite expansion branches are signed functions or measures. Positive expansion coefficients and positive branch partition functions do not imply pointwise positivity of each branch density. Gaussian damping and cutoff limits are explicit.

6. **pp. 547–549, Lemma 3.1, isolated squares.** The proof strengthens the isolated-square selector by the factor $2^{\alpha/2}$ needed to pass from square side length to Euclidean diameter. Minimum-cover cardinalities and the final theorem are retained.

7. **pp. 554–558, Lemmas 4.3–4.4.** Contour shifts use an interior admissible range and a supremum rather than a maximum on an open strip. Vanishing vertical sides and all conditional integrability arguments are proved explicitly.

8. **p. 562, (4.59).** The printed numerical exponent contains $\ln2$; direct optimization at $R=\sqrt2$ gives $\ln R=\tfrac12\ln2$. The proof allows the weaker positive constant $D=\ln2/[8(\pi+1)]$ and adjusts auxiliary constants. This is a quantitative proof choice, not a claim that the root theorem is false.

9. **pp. 570–573, (5.38)–(5.51).** Infinite Fourier perturbations are implemented by finite truncation and Gaussian-damped limits. Villain disorder uses the explicit continuous charge rescaling through (1.38), rather than interpreting the restricted charge phrase after (5.51) as covering every real strength.

10. **pp. 581–583, (6.25), (6.44).** The proof supplies edge-gradient bounds for contour shifts and an aggregate packing bound for the electrostatic estimate. It does not infer a small edge gradient from the printed site-amplitude sentence, or assume the disk-to-support comparison without proof.

11. **pp. 590–591, (7.16)–(7.18).** The SOS state uses Appendix C interpolation (C.1). The comb is inserted in each finite Dirichlet box before taking limit points. Identification with the printed two-stage construction (vague limit first, then comb) is not asserted. The Dirichlet-box result is also stated separately. All-real moment lower bounds may be extended nonnegative integrals; variance statements include the needed integrability. See [SOSTheorem73Literal](../FroehlichSpencer/BKT/Surface/SOSTheorem73Literal.lean).

12. **p. 594, (7.40) and deduction of (7.18).** The fixed endpoint prefactor in (7.40) alone cannot give the prefactor-one moment inequality or its second derivative at zero. The formalization proves the required moment and variance estimates by a separate argument, with endpoint control and integrability. This fills a proof gap without declaring Theorem 7.3 false.

13. **p. 595, Appendix A, (A.1)–(A.2).** The raw angle integral in (A.1) and the character identity (A.2) differ by $(2\pi)^{|A|}$ unless angle measure is normalized. Use normalized Haar measure, or carry this common factor in numerator and partition function. It cancels in normalized expectations.

14. **pp. 527–602, scope.** The formalization covers the named finite-region and selected limit results in the README. It does not assert sharp critical temperatures, the Ising-interface identification, universality or an independently constructed renormalization-group fixed point, or all possible boundary conditions. Lean’s logarithms, reciprocals and powers are total functions; nonzero-distance and positive-parameter hypotheses delimit the mathematical statements.

15. **pp. 535, 585–587, Theorem E and Theorem 7.1.** The high-harmonic upper bound keeps $\min(\xi/n,1-\xi/n)\ge q$ and the detailed theorem’s $\beta\prime\prime(\beta,n,q)$ dependence. The useful range is $0\lt q\le1/2$. The massless interval is proved with a separately specified predicate and common threshold choices; it is not inferred solely from a pointwise large-$n$ assertion or an endpoint minimum in $q$.

16. **pp. 576, 598–599, (1.34), §6 properties (a)–(d).** The rotator interpolation is the literal Appendix B construction, not the classical Bessel function of arbitrary noninteger order. Integer values are its positive Fourier coefficients. Logarithmic-derivative differences give the branch-independent interpretation of (d); large-$\beta$ translation bounds have existential constants and thresholds. No uniqueness of an analytic interpolant is claimed.

17. **pp. 533–535, 595–596, planar duality and boundaries.** The finite planar correspondence keeps bounded dual faces, an explicit exterior face pinned to zero, and the edges crossing the internal primal bonds. Half-open path indices and orientation signs are translated explicitly; the field rescaling carries the $2\pi$ factors. General boundary extensions mentioned in Appendix D are not silently substituted for this finite correspondence.

18. **pp. 591–593, (7.29)–(7.32).** Complex tilted factors are handled by explicit real-part, reality and integration arguments before applying ordered inequalities. A complex norm bound alone is not used as a pointwise order on complex numbers.

## Kharash–Peled

### Errata

1. **p. 2, §1.1, edges of $\Lambda_L^{\rm free}$.** The edge rule prints $\{|a-b|,|c-d|\}=\{0,1\}$ for vertices $(a,b),(c,d)$. Read $\{|a-c|,|b-d|\}=\{0,1\}$, as on p. 32. The free-square graph in the library uses nearest neighbours. See [SquareFreeEdge](../FroehlichSpencer/BKT/Surface/SquareFreeEdge.lean).

2. **p. 2, §1.1, $\Lambda_L^{\rm zero}$.** The sentence says every vertex of $\Lambda_L^{\rm zero}$ has degree 4. It applies to the original free-box vertices; the wired vertex has degree $4L$. The multiplicity definition of the wired graph is unchanged. See [SquareZero](../FroehlichSpencer/BKT/Surface/SquareZero.lean).

3. **p. 8, §2.1, `2^k×2^k` squares.** The point count is printed $2^{k+1}$. A full square has $2^{2k}$ vertices; a clipped square can have fewer. No effect on the stated theorems.

4. **p. 13, §2.3 Step 3, cross-orthogonality after (2.19).** The display quantifies over $\rho,\rho\prime\in\mathcal N$, but the spin waves are defined only for $\mathcal N_0$. Restrict the display to $\rho,\rho\prime\in\mathcal N_0$. No effect on the stated theorems.

5. **p. 15, §3, proof of T1.5 (after “by Claim 3.1”).** The cosine-addition step prints $1+z(\cos x\cos y-z\sin x\sin y)$. Remove the inner $z$: $1+z(\cos x\cos y-\sin x\sin y)$. No effect on the stated theorems.

6. **p. 15, §3, the normalized measure.** The proposed normalized measure likewise prints a single factor after $Z_{\mathcal N}(0)^{-1}$. Insert the product over $\rho\in\mathcal N$ used to define $Z_{\mathcal N}(0)$. No effect on the stated theorems.

7. **p. 15, proof of Claim 3.1.** $1+z(cos x cos y − z sin x sin y)$. Read instead: $1+z(cos x cos y − sin x sin y)$. No effect on the stated theorems.

8. **p. 18, proof of P2.1 (preimage counts).** The count is called $N_{j,m}$. Read $N_{m,j}=\{k:\gamma^m(k)=j\}$, as defined immediately before. No effect on the stated theorems.

9. **p. 19, proof of L4.3.** "is the inserted". Read instead: "is inserted". No effect on the stated theorems.

10. **p. 20, proof of L4.3.** "the application … have no effect". Read instead: "has". No effect on the stated theorems.

11. **p. 23, proof of L4.5.** "without loss generality". Read instead: "without loss of generality". No effect on the stated theorems.

12. **p. 25, proof of L4.6.** "a connected components". Read instead: "a connected component". No effect on the stated theorems.

13. **p. 25, §4.3.3.** "This fact allow us". Read instead: "allows". No effect on the stated theorems.

14. **p. 27, P4.7 large-scale construction.** "arbitrarily chosen point". Read instead: "an arbitrarily chosen point". No effect on the stated theorems.

15. **p. 28, proof of (4.31).** The proof uses $(\ln(1+t))^2\le t^2$ although it has just stated the valid bound $10t^2$ for $|t|\lt1/2$. The coefficient-one bound fails for negative $t$, for example $t=-1/4$. Restore the factor 10, giving $40d(E)^2/|x_E|_s^2$ rather than $4d(E)^2/|x_E|_s^2$. Only auxiliary constants change.

16. **p. 28, §4.3.4.** "be be". Read instead: "be". No effect on the stated theorems.

17. **p. 29, proof of L4.8.** "that that". Read instead: "that". No effect on the stated theorems.

18. **p. 33, proof of P6.1 (divergence).** The divergence sum is $\sum_{(k,\ell)\in\vec E}n_{(k,j)}$. The summand must be $n_{(k,\ell)}$. No effect on the stated theorems.

19. **p. 34, P6.1 statement.** The expectation is written for $\Lambda_L$. Read the wired domain $\Lambda_L^{\rm zero}$. This is the Villain law used in Proposition 6.1 and the library. See [VillainLaw](../FroehlichSpencer/BKT/Surface/VillainLaw.lean).

20. **p. 34, partition-function identity in the proof of P6.1.** The unnormalized identity includes $Z^{\rm Vil}$ in the denominator and a single factor $(2\pi\beta)^{-1/2}$. Remove the partition-function denominator. The factor is $(2\pi\beta)^{-|E|/2}(2\pi)^{|V|-1}$, one Fourier factor per edge and one angle integral per unpinned vertex. The library proves this expansion; the scalar cancels in normalized expectations. See [CurrentFormula](../FroehlichSpencer/BKT/Villain/CurrentFormula.lean).

21. **p. 34, Proposition 6.1 and Theorem 6.2, (6.2).** The line sums in Proposition 6.1, Theorem 6.2, (6.4), and the integer limit end at $L$. They must end at $L-1$; $t=L$ is outside the stated free or dual square. The corresponding field family is indexed by $\Lambda_L^{\rm free}$. The formalized dual line observable uses the corrected endpoint. See [Expectation](../FroehlichSpencer/BKT/Duality/Expectation.lean).

22. **p. 34, deduction of T1.3 from T6.2.** The condition is printed $y\lt L-1$ although $y$ is a pair. Read $y_1\lt L-1$. No effect on Theorem 1.3.

23. **p. 35, proof of T6.2.** "Same calculation to the calculation … with y is replaced". Read instead: "The same calculation as … with y replaced". No effect on the stated theorems.

24. **p. 36, §6.3.** "where $Δ^p_{2L}$ defined". Read instead: "is defined". No effect on the stated theorems.

25. **p. 38, §7.** "the the". Read instead: "the". No effect on the stated theorems.

26. **p. 39, reference [4].** "Poincar". Read instead: "Poincaré". No effect on the stated theorems.

27. **p. 39, reference [4].** "Birkhuser". Read instead: "Birkhäuser". No effect on the stated theorems.

28. **p. 39, reference [7].** "Yukawaand". Read instead: "Yukawa and". No effect on the stated theorems.

29. **p. 40, references.** "superfluids.(Application". Read instead: "superfluids. (Application". No effect on the stated theorems.

30. **p. 17, Lemma 4.1, adjacency threshold.** The proof drops the $-2$ in the exponent of the adjacency threshold. Retain $2^{\alpha\gamma+b-2}$ consistently. No effect on the stated theorems.

31. **pp. 19–20, Lemma 4.3, property 1.** The claimed pairwise distance bound for constituents after repeated merging is false. At scale 0, singleton inputs at 0, 1, 2, 3 can merge first in pairs and then together, leaving constituents at distance 3. Use connectedness of merge ancestry in the conflict graph, and the first crossing in the merge history. No effect on Theorems 1.5–1.6.

32. **pp. 8, 17, periodic square-cover cutoff.** The diameter-based conclusion that one periodic square suffices at scale $k\ge\log_2(d+1)$ is false. On a 14-cycle row, $\{0,5,9\}$ has diameter 5 but fits in no cyclic interval of length 8. Use coordinate lifts for linked pairs and triples, and the full-domain overflow convention. No effect on the stated root theorems.

33. **p. 29, Lemma 4.8, contour modulus.** The modulus after translation omits the factor $e^{\beta n v^2/2}$, where $n$ is the number of centres. Retain that factor in the Gaussian tail estimate. The contour identity is unchanged. See [ComplexTranslation](../FroehlichSpencer/BKT/Gaussian/ComplexTranslation.lean).

34. **p. 29, Lemma 4.8, empty family.** The statement permits an empty family of centres. Then there is no Gaussian decay and the displayed improper integrals need not exist. Require a nonempty family; allow complex centres for successive shifts. The library proves this corrected contour-shift identity. See [ComplexTranslation](../FroehlichSpencer/BKT/Gaussian/ComplexTranslation.lean).

35. **p. 27, proof of (4.32).** The estimate uses $\mathrm{dist}(E,\rho^*)\le2R_1$ and a resulting factor 3. The geometry requires a larger enclosure; use the thickened annulus and factor 4. Only auxiliary absolute constants change.

36. **p. 38, Claim 6.3.** The squared gradient estimate drops $(2\pi)^2$. Retain it and enlarge the absolute constant $D_5$. No effect on the stated theorems.

37. **p. 21, (4.16), site Fourier coefficients.** The expansion lets $q_j$ range over all positive integers and writes $z(q_j)$, although (4.15) defines a finite site-dependent polynomial. Use $1\le q_j\le N_j$ and $z_j(q_j)$, or extend the coefficients by zero. No effect on the stated theorems.

38. **p. 21, (4.17)–(4.18), distance tests.** The candidate density is included in its own distance tests. Exclude the candidate from the comparison family; its distance to itself is zero. No effect on the stated theorems.

39. **p. 13, Step 4, activity exponent.** The bound derived from (2.7) omits the contribution $+1$ from $e^{\rho(j)^2}$. Restore it. For $\Gamma\lt1$, use $\Gamma_+=\max(1,\Gamma)$ in bounding the support factor by the squared integer-charge norm. A smaller temperature threshold absorbs these constants; no hypothesis $\Gamma\ge1$ is needed.

40. **pp. 26–27, (4.27), sign of the patch profile.** The constructed wave has $+\gamma b$ on a patch whose nonzero charge $q$ can be negative. Use $\mathrm{sign}(q)\gamma b$, so its pairing is $\gamma\ln(6/5)|q|$. The quadratic cost is unchanged and the energy gain is positive. No effect on the stated theorems.

41. **p. 27, (4.29), crossing-edge count.** The boundary-vertex sum counts each external vertex once, although a vertex can be incident to as many as four crossing edges. Restore this multiplicity in the energy bound. Together with the missing factor 10 in (4.31), a safe auxiliary constant is 10240 rather than 256. No effect on the stated theorems.

42. **p. 27, energy bound after (4.28).** The bound introduces $\ln(2/\upsilon)$ with no definition of $\upsilon$. From (4.28) the direct quadratic cost is $\beta\gamma^2C/2$, without this logarithm. Use that cost together with the sign-corrected linear gain. No effect on the stated theorems.

43. **p. 28, reference before (4.33).** The lower bound on the radial bin is attributed to (4.31), the estimate currently being established. Derive it from Lemma 4.6(2) and the corrected (4.32). No effect on the stated theorems.

44. **p. 28, (4.33), packing numerator.** The numerator counts a thin radial bin containing the centres, but their disjoint balls need not lie in that bin. Enlarge it to a thickened annulus before taking the volume ratio; this still yields the bound by an absolute constant times the radial index. No effect on the stated theorems.

45. **p. 29, support sentence before the cross-scale argument.** The text says all nonzero gradients of the base wave $a_0$ lie within distance 1 of each separated square. This fails when charges lie in more than one separated square. Apply that statement only to gradients incident to charges in the chosen square; prove separation from all other charge neighbourhoods. No effect on the stated theorems.

46. **p. 26, Proposition 4.7, small-scale plateau.** The small-scale wave is constant only out to distance 1, but property 2 requires constancy out to $\lceil2^{k-3}\rceil$, which exceeds 1 for some $k\lt10$. Replace it by a tapered cutoff with the required plateau and support. The energy constant is enlarged; the proposition’s conclusion is retained.

47. **p. 26, Proposition 4.7, small-scale separation.** The chain of inequalities drops the term $-4d(\rho\prime)$ when replacing $M(d(\rho\prime)/2)^\alpha$ by a constant. Retain this loss and use the large fixed $M$ to absorb it before deducing separation. No effect on the stated theorems.

48. **p. 24, before Lemma 4.6, component diameter.** The text asserts $d(E)\ge4$ merely from neutrality of the underlying density. A clipped neighbourhood in a small finite domain need not have that diameter. Handle the small-diameter components separately instead of assuming this lower bound. No effect on the stated theorems.

### Deviations

1. **pp. 2–7, Theorems 1.1, 1.3, 1.5–1.6.** Numbering and statements follow arXiv v1. The scope is finite free squares and even-periodic squares for the integer GFF, and wired squares for the Villain magnetization bound. No arbitrary finite-graph, infinite-volume, XY or clock extension is inferred from these statements.

2. **p. 2, (1.2), inverse Laplacian.** The massless inverse is a pseudoinverse characterized on zero-sum functions. Its existence and uniqueness are proved; the root theorem quantifies over every linear map satisfying (1.2). No inverse on the constant mode is assumed. See [LaplacianPseudoinverse](../FroehlichSpencer/BKT/Surface/LaplacianPseudoinverse.lean).

3. **p. 8, square families.** For free boxes use clipped squares when $2^k\le L$ and the whole domain when $2^k\gt L$. The printed clipping formula and subsequent overflow sentence are not literally identical. The formalization follows the overflow sentence and uses $2^{2k}$ only for full squares.

4. **pp. 8, 28–29, separated covers.** Choose an allowed next-scale square containing the clipped centred double, with compatible ancestors. At a free boundary the literal centred double can have an anchor outside the displayed family. This makes the minimum-cover selection explicit; Theorems 1.5–1.6 are unchanged.

5. **pp. 8–9, scale exponent and constants.** The proof fixes $\alpha=7/4$. It does not assert that the auxiliary constants called “absolute” are uniform as $\alpha\downarrow3/2$; the large-scale series degenerates there. The root theorems contain no $\alpha$ parameter.

6. **pp. 23–28, Proposition 4.7, spin-wave construction.** The proof supplies signed profiles for negative patch charge, tapered small-scale cutoffs, full boundary-edge multiplicities, thickened annuli, and packing at clipped boundaries. These replace compressed or unsupported construction steps and enlarge auxiliary constants; the energy and activity conclusions retain their form.

7. **pp. 30–31, passage to integer heights.** The Fejér-cell argument retains the common cell mass $(2\pi)^{|\Lambda|}$ and supplies a summable pinned Gaussian majorant before taking limits. This completes the printed dominated-convergence argument.

8. **pp. 31–32, Proposition 1.2, replica rotation.** The rotation argument is applied to a pinned-root law with its own normalizer, then related to the interval-root law. The root interval square itself is not rotation invariant. Proposition 1.2 is not one of the listed source-facing root theorems.

9. **pp. 36–38, (6.13), Claims 6.3–6.4.** The logarithmic Green estimate and the local small-box contributions are proved explicitly rather than taken as “well known”. Constants absorb the bounded small-distance terms. Theorem 1.3 retains its stated power-law form.

10. **p. 2, domain parameters.** Graph and law definitions are total in the side length, following Lean conventions. Theorems retain the nondegeneracy conditions on the side and evenness for periodic squares. Total values outside those conditions are not additional mathematical claims.

## FS82

### Errata

1. **p. 411, introduction.** The text prints “subgroups is”. Read “subgroups are”. No effect on the stated theorems.

2. **p. 417, high-temperature comparison after (1.16).** The sentence refers to failure of (1.15), which defines an expectation. Read (1.16), the perimeter inequality. No effect on the stated theorems.

3. **p. 422, after (2.29).** The Fourier coefficients are written $\widehat\varphi(n_p)$ and $\widehat\varphi(n_p-1)$ without the temperature index. Read $\widehat\varphi_\beta$ in both places. No effect on the stated theorems.

4. **p. 428, (2.61), norm definition.** The paper defines $\Vert \rho\Vert _p=\sum_b|\rho_b|^p$. Insert the power $1/p$; in particular $\Vert \rho\Vert _2^2=\sum_b\rho_b^2$. The estimates in the library use the sum of squares.

5. **p. 428, (2.64), comparison with (2.63).** The display has $e^{-(\beta/n_{xy})q^2}\le e^{-(\beta/6)q^2}$. As a comparison for the attenuation in (2.63), retain its factor $1/2$: $e^{-(\beta/(2n_{xy}))q^2}\le e^{-(\beta/12)q^2}$. The displayed inequality by itself is valid, but has the wrong coefficient for that application. No effect on the stated theorems.

6. **p. 429, (2.67)–(2.68).** The conditional Gaussian mean is printed $+\ell_b/n_b$. Completing the square in the positive action gives $-\ell_b/n_b$. The formalization uses the negative mean; no estimate changes.

7. **p. 432, phase pairing before (2.83).** The phase is written $(\epsilon_\Lambda,\mu_\rho)_\Lambda$. Use the dual pairing $(\epsilon_\Lambda,\mu_\rho)_{\Lambda^*}$, consistently with its definition. No effect on the stated theorems.

8. **p. 432, (2.83).** The argument divides by $\epsilon_\Lambda(p(\rho))$, which need not be nonzero. Replace this step by the controlled-support filling estimate of Lemma 1, bounding the phase without division by a residual value. The perimeter proof uses the filling estimate.

9. **pp. 432, 436, §2.10 and §2.12, decay rate.** The positive decay rate is printed $(\beta_1-\beta/216)/2$. For $\beta\gt216\beta_1$ this is negative. Use $a(\beta)=(\beta/216-\beta_1)/2\gt0$ in both places. This restores the decaying current envelope and changes no root theorem.

10. **p. 435, (2.101).** The left side has a fixed ensemble index, $\mathscr J_\gamma(\tau)$, while the right side sums over $\gamma$. Use the per-ensemble bound $\mathscr J_\gamma(\tau)\ge Z_\gamma P_\gamma(\tau)$ and then sum with weights $\lambda_\gamma=d_\gamma Z_\gamma/\Xi_\Lambda$, whose sum is 1. The proof of (2.93) uses this normalized aggregate.

11. **p. 435, (2.102).** The estimate $\gamma(z)\le4z$ for $z\le1/2$ fails: $\gamma(1/2)=5/2\gt2$. The sharp estimate on $0\le z\le1/2$ is $\gamma(z)\le5z$. The library proves and uses that estimate; the larger factor only changes generic constants. See [SourceJensen](../FroehlichSpencer/FS82/Moment/SourceJensen.lean).

12. **p. 436, (2.107), placement of the quadratic factor.** The brace places $|(d\tau)_{p_0}|^2$ inside the upper bound for a sum that is independent of $\tau$. Read $\{\sum_L L^{11}e^{-a(\beta)L}\le c(\beta)\}|(d\tau)_{p_0}|^2$. This is the quadratic packing bound used in the proof.

13. **p. 436, (2.107), minimum support length.** The sum starts at $L=4$. Boundary-ending currents of support length 2 and 3 exist, so start at $L=2$. The all-length estimates change the packing constants, not the root conclusion.

14. **p. 437, final coefficient in (2.93).** The journal prints $1-2c(\beta)/\beta$. The preceding algebra gives $1-2\beta c(\beta)$, as in the preprint. The formalized lower coefficient is $\beta\prime\prime=\beta(1-2\beta c_{\rm pack}(\beta))$. See [FiniteVillainDualMomentComparisonLogThick](../FroehlichSpencer/FS82/Surface/FiniteVillainDualMomentComparisonLogThick.lean).

15. **p. 439, (3.11), strict positivity.** The printed strict positivity needs $h\gt0$; at $h=0$ nonconstant Fourier coefficients vanish. Include the positive-coupling hypothesis for the strict claim. No effect on the disorder theorem.

16. **pp. 443–444, (3.37) and (3.39).** The activity bound prints $\exp(1/18)[c_1\beta L(\rho)-c_0\Vert \rho\Vert _1]$. The bracket belongs inside the exponential: $\exp\{[c_1\beta L(\rho)-c_0\Vert \rho\Vert _1]/18\}$. Otherwise a positive activity would be bounded by a possibly negative expression. No effect on the stated theorems.

17. **p. 446, inference (3.53) ⇒ (3.54).** The printed $\Vert \epsilon\Vert ^2\ge c(L+T)$ is a lower bound and cannot give the claimed lower bound for a decreasing exponential in $\Vert \epsilon\Vert ^2$. The formalization supplies the independent upper bound $\Vert \epsilon\Vert ^2\le24\pi^2(\xi/N)^2(L+T)$ for the source residual on centred cubes. It does not reverse the printed inequality without proving this separate bound. See [SourceResidual](../FroehlichSpencer/FS82/ZN/SourceResidual.lean).

18. **p. 449, field preceding (4.19).** The second case says $c_{k+1}\subset\Sigma_k$. Read $\Sigma_{k+1}$, as in the shifted Fourier factors of (4.19). No effect on the stated theorems.

19. **p. 449, Villain formula before (4.21).** The Gaussian action has coefficient $1/2$. Read $1/(2\beta)$, as required by (4.20) and the specialization (4.22). The dual weights in the formalization retain the temperature.

20. **p. 451, positivity after (4.31).** The coefficient is called $c_\gamma$ although the expansion uses $d_\gamma$. Read $d_\gamma\gt0$. No effect on the stated theorems.

21. **p. 452, before (4.39).** The text prints “decays like,” before the decay rate. Remove the comma. No effect on the stated theorems.

### Deviations

1. **pp. 418, 434–437, (2.93).** The finite-volume moment theorem is restricted to log-thick rectangular boxes in $\mathbb Z^4$, with globally co-closed sources supported strictly inside. The paper permits arbitrary finite regions. A single threshold is uniform over the allowed boxes and sources; joint moments use the same covariance form and renormalized coefficient. See [FiniteVillainDualMomentComparisonLogThick](../FroehlichSpencer/FS82/Surface/FiniteVillainDualMomentComparisonLogThick.lean).

2. **pp. 421–424, dual carriers, (2.17)–(2.36).** The physical dual lattice is the half-integer translate. Star-oriented cochains and coordinate-oriented lattice cochains are related by explicit diagonal signs. In degree $k$ the convention is $J_k(c)=(-1)^{\sum\mathrm{axes}(c)+k}c$; in particular the 0–1 sheet has opposite sign in the coordinate-oriented dual 2–3 field. Norms and pairings are preserved.

3. **pp. 423–424, Gaussian and (2.34)–(2.36).** The condition $\delta\mu=0$ means divergence-free at the finite $\Lambda^*$ vertices. Zero extension may have divergence at exterior endpoints. The Gaussian is a normalized finite quotient law, with gauge directions given by gradients on those vertices; it is not an integral over unreduced gauge directions.

4. **pp. 426–427, (2.50)–(2.52).** The finite residual is defined by orthogonal projection: $\epsilon_\Lambda=\sigma-P_{\rm exact}\sigma$. This supplies $\Pi_{\Lambda^*}d\tau=\sigma-\epsilon_\Lambda$ and orthogonality to exact forms. The printed Dirichlet Green-operator formula is not asserted as an exact identity on the chosen finite free complex. It can instead be read using the matching finite Hodge Laplacian.

5. **pp. 419, 427–432, Wilson bounds (2.7)–(2.8).** Area, perimeter and transition results are for fitted rectangular loops in free cubes, with translated versions as specified by their statements. Limit forms give cluster points, bounds for every cluster point and liminf, and bounds for any separately known limit. They do not establish convergence by Ginibre inequalities or arbitrary-region results.

6. **p. 419, small-coupling rate in (2.7).** The proved area law has a fixed sufficient rate, $0\le\Re\langle W\rangle\le e^{-LT/2}$ for $0\lt\beta\le1/80$. The source’s precise asymptotic rate of order $\log(1/\beta)$ and sharp transition point are not asserted. See [AreaLawFinite](../FroehlichSpencer/FS82/Wilson/AreaLawFinite.lean).

7. **pp. 433–434, (2.89)–(2.93), infinite volume.** Limit curvature states are consistent subsequential local states along centred cubes. The moment comparison holds for every such state. Uniqueness, a full Gibbs/DLR characterization, convergence of the whole sequence, and identification with the thermodynamic limit cited in the paper are not asserted.

8. **p. 434, field-strength nonsummability.** The dual-curvature result selects a stationary subsequential state with a correlation that is not absolutely summable. The primal result identifies off-diagonal limits of translation-averaged finite-volume correlations of the observable (2.89), along one common selected subsequence. It asserts neither a diagonal contact limit nor a global primal Gibbs state or pointwise power asymptotic. See [SourcePrimalFieldStrengthNonsummable](../FroehlichSpencer/FS82/SurfacePrimal/SourcePrimalFieldStrengthNonsummable.lean).

9. **p. 440, (3.18).** The finite index expansion is read assignment by assignment, with the Fourier cutoff and its convergence made explicit. It is not an unqualified pointwise identity for an undamped infinite Fourier series.

10. **pp. 445–446, (3.51)–(3.55).** The $\mathbb Z_N$ disorder root is for centred finite free cubes, integer twists $1\le\xi\lt N$, sufficiently large $N$ depending on $\beta$, and a fitted sheet. It covers the interpolating real law and its discrete endpoint. It does not construct an infinite-volume disorder state, treat all finite regions, or identify a universal fixed point. See [fs82_zn_disorder_perimeter_root](../FroehlichSpencer/FS82/SurfaceZN/fs82_zn_disorder_perimeter_root.lean).

11. **pp. 452–453, (4.38)–(4.40).** The finite-volume Jensen bound retains an additive long-current remainder absent from printed (4.38). On cubes this remainder is controlled uniformly in the side. The resulting Villain XY spin lower bound is proved on finite equal-sided cubes in each fixed $D\ge3$, uniformly in the two sites. The cited XY thermodynamic limit and pure-state decomposition are not asserted. See [fs82_xy_spinCorrelation_root](../FroehlichSpencer/FS82/SurfaceXY/fs82_xy_spinCorrelation_root.lean).

12. **pp. 411–454, model scope.** The results use the Villain action in §2 and §4, and Wilson’s action for the discrete gauge result in §3. General Wilson-action extensions, general-rank hypergauge phase classifications, screening at the borderline dimension, Higgs-model consequences, and external expansion theorems not listed in the README are outside scope.

13. **pp. 418–424, normalizations and total definitions.** One representative per oriented cell is used, with integer dual potentials, primal inverse temperature $\beta$, dual action $\Vert d\alpha\Vert ^2/(2\beta)$ and Fourier currents in $2\pi\mathbb Z$. Any Haar/Lebesgue partition factors are carried through and cancel in normalized expectations. Definitions are total; source theorems retain their positivity and nondegeneracy hypotheses.

## FS83

### Errata

1. **p. 155, (1.18).** The energy-integral side ends with an extra $dt$. Remove the terminal $dt$. No effect on the stated theorems.

2. **p. 155, (1.20).** The first line has $e^{itH}$ and the next two have $e^{-itH}$. Use one sign consistently throughout the derivation. No effect on the stated theorems.

3. **p. 155, (1.20) spectral statement.** The text prints $\sigma(H)\cap I=\sigma_{\rm pp}(H)$. The right side must also be restricted to $I$: $\sigma(H)\cap I=\sigma_{\rm pp}(H)\cap I$, or use the corresponding inclusion. No spectral-type theorem based on this sentence is asserted here.

4. **p. 156, (1.25).** The squared Green-function contribution prints $\epsilon^2e^{mN_j}\sum_x|x|^2e^{-m|x|}$. Squaring (1.24) gives $\epsilon^2e^{2mN_j}\sum_x|x|^2e^{-2m|x|}$. Both exponents must double. No effect on the stated theorems.

5. **p. 158, Section 2 opening.** “develop and inductive method”. Read instead: “develop an inductive method.” No effect on the stated theorems.

6. **p. 163, (2.24).** The final exponent is printed as $N-|x|$. Read $m(N-|x|)$. The formalized Green-function bound includes this factor $m$. See [T12Lambda](../FroehlichSpencer/Surface/T12Lambda.lean).

7. **p. 169, iteration of (3.23).** “Greens' functions”. Read instead: “Green's functions.” No effect on the stated theorems.

8. **p. 171, after (4.5).** “Theorem 4.1 follows”. Read instead: “Theorem 4.2 follows.” No effect on the stated theorems.

9. **p. 173, (4.8).** The volume term is printed $V_{\gamma^m(n)}$. Iterating (4.7) requires the primed isolated-volume term $V\prime_{\gamma^m(n)}$. No effect on the stated theorems.

10. **p. 174, (5.8) definition.** The resonance event is written with $H_D(v)$. The argument requires $H_{\bar D}(v)$, the Hamiltonian on the thickened block. This is the block used in the probability proof. See [Section5](../FroehlichSpencer/T12/Section5.lean).

11. **p. 175, independence estimate before (5.19).** The separation is written $\mathrm{dist}(\cdot,\cdot)\ge0$, which does not give disjoint supports. Require strictly positive separation. The probability proof checks disjoint supports before invoking independence. No effect on the stated theorems.

12. **p. 176, (5.21).** The inner product over $c\in C\prime_n(D)$ has an extraneous upper limit $\infty$. Remove it; this is a product over a finite cube family. No effect on the stated theorems.

13. **p. 177, (6.6).** The probability lower bound prints $1-l^p$. Read $1-l^{-p}$. This is the decaying failure probability used in the theorem. No effect on the stated theorems.

14. **p. 182, (B.2).** The resolvent is printed $[H_\Lambda-E+i\epsilon Q_\Lambda(a)]^{-1}$. Read $[H_\Lambda-E-i\epsilon+Q_\Lambda(a)]^{-1}$. No effect on the stated theorems.

15. **p. 182, matrix element after (B.2).** The phase is printed $e^{ia\cdot(x-y)}$. Under the stated $U(-a)GU(a)$ convention it is $e^{-ia\cdot(x-y)}$. Replacing $a$ by $-a$ leaves the bound unchanged. No effect on the stated theorems.

16. **p. 182, (C.2).** The differential is written $d\widehat\lambda(v_j)$. Read $d\lambda(v_j)$. No effect on the stated theorems.

17. **p. 183, (C.4).** The integral of $\chi_\Lambda(\kappa,E)$ omits its measure. Insert $dP$, the configuration probability measure. No effect on the stated theorems.

18. **p. 183, (C.5) preceding display.** The condition on $v_j-E+2\nu$ has an unmatched absolute-value bar. Close the bar around this expression. Separately, the spectral-resonance argument needs the enlarged radius $2\nu+\kappa$, as recorded below. No effect on the stated theorems.

19. **p. 183, (C.5) integration domain.** The integration domain uses capital $V-E+2\nu$. Use the lowercase integration variable $v-E+2\nu$. No effect on the stated theorems.

20. **p. 183, remark after (C.5).** “λ(v_j) is Gaussian”. Read instead: “dλ(v_j) is Gaussian.” No effect on the stated theorems.

21. **p. 164, (3.2).** The printed recurrence subtracts a term with exponent $1/4$ at the next scale. Use $m_{k+1}=m_k-Cd_k^{-1/8}$, equivalently $m_k=m_{\rm base}-C\sum_{i\lt k}d_i^{-1/8}$. This pays the losses in the joint decay/norm induction. The library uses this corrected recurrence. See [Bridge](../FroehlichSpencer/T12/Bridge.lean).

22. **p. 183, Appendix C, before (C.5).** The event $N_\Lambda(E,v)\ge1$ is not the spectral-resonance event and does not imply the printed single-site window of radius $2\nu$. Use resonance within $\kappa$ of $E$ and the Gershgorin window $|v_j-E+2\nu|\le2\nu+\kappa$ (or the safe radius $2\nu+1$ when $\kappa\le1$). The formalization proves the needed spectral-averaging resonance bound. See [Resonance](../FroehlichSpencer/T12/Resonance.lean).

### Deviations

1. **pp. 153–155, (1.10)–(1.15), Theorem 1.1.** The conclusion $D(E)=0$ is stated where the integrated density of states $N$ has a derivative $r\gt0$. The diffusion coefficient is characterized relationally by the Kubo formula. The printed assertion (1.13) that the density is positive everywhere on the spectrum is not used or formalized as a general theorem. See [Theorem11](../FroehlichSpencer/Surface/Theorem11.lean).

2. **pp. 152–153, (1.4), infinite Green function.** The Green function is defined from the proved existence and uniqueness of the square-summable solution of the pointwise lattice equation for a nonreal spectral parameter. This treats arbitrary real potentials without assuming an everywhere-defined bounded infinite Hamiltonian. See [InfiniteGreenWellDefined](../FroehlichSpencer/Surface/InfiniteGreenWellDefined.lean).

3. **pp. 153, 157, Theorems 1.2 and 1.2Λ.** Both regimes are retained: bounded single-site density at large disorder, and Gaussian disorder at sufficiently high energy relative to $2\nu$. The dimension satisfies $\nu\ge1$. Constants may depend on dimension; bounded-density thresholds are chosen uniformly before the law and Gaussian thresholds may depend on its variance. See [T12Lambda](../FroehlichSpencer/Surface/T12Lambda.lean).

4. **pp. 153, 157, probability quantifiers.** The event quantifies simultaneously over all nonzero imaginary parts for a fixed endpoint $x$; constants are uniform in $x$ and in finite regions containing both endpoints. Measurability of the event is an explicit conclusion. This makes the intended quantifier order and probability meaning precise. See [T12](../FroehlichSpencer/Surface/T12.lean).

5. **p. 153, (1.10), integrated density of states.** The exhaustion uses cubes $[-L,L]^\nu$. One full-measure set gives convergence at every real energy simultaneously for every bounded-density single-site law, without mean or variance assumptions. This specifies the source’s thermodynamic-limit convention. See [IDSWellDefined](../FroehlichSpencer/Surface/IDSWellDefined.lean).

6. **pp. 159–160, Condition A, components.** Components are clusters for the chain relation $|x-y|\lt2r_i$, rather than nearest-neighbour components. A component is gentle when it also obeys the diameter and spectral-gap requirements. The gentle set is the union of all such components. This reads “component” in the multiscale sense distinguished from Appendix D’s usual nearest-neighbour meaning.

7. **pp. 164–170, §3 and pp. 183–184, Appendix D.** Discrete thickening and filling, strict geometric buffers, first-exit regions within arbitrary parents, boundary multiplicities, path counts and terminal remainders are supplied explicitly. These complete the paper’s choices and omitted geometric estimates; ambiguous bar/tilde glyphs in the last page are not needed.

8. **pp. 170–177, §§4–6.** The entropy argument includes witness selection, nested occupancy and scale counts. The resonance products include finite scale cutoffs and disjoint-support independence checks. Occurrence and tower bounds use the range-cluster convention. These are complete proof supplements, not changes to the source-facing conclusions.

9. **pp. 182–183, Appendix C.** Finite-volume spectral averaging replaces formal differentiation of the step-valued eigenvalue count and integration by parts. The generic square-root resonance bound suffices in the Gaussian branch; the printed proposed improvement to a linear bound is not required. See [Resonance](../FroehlichSpencer/T12/Resonance.lean).

10. **pp. 151–184, scope and notation.** The release proves the Green-function probability and almost-sure decay conclusions and vanishing Kubo diffusion. It does not infer a separate full spectral-type classification from the discussion after (1.20). Induction labels, punctuation in event subscripts, skipped equation (3.6), and degraded glyphs are identified by their context; no new theorem is attached to those typesetting distinctions.

11. **pp. 180–181, Appendix A, (A.2).** The real-parameter resolvent comparison does not justify the uniform estimate for nonzero imaginary spectral parameter. Replace that step with a convergent Neumann/path expansion under the diagonal gap, valid uniformly in that imaginary parameter. The base decay bound used in the induction follows from this argument.

