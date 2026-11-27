/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Rates.HullWhiteCalibration
public import MathFin.Models.BlackScholes.Call
public import MathFin.Models.Forwards.Black76
public import MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment
public import MathFin.Probability.Brownian.Wiener.WienerIntegralFiltration
public import MathFin.Probability.Gaussian.GaussianPairLinearLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# The Schwartz–Smith two-factor commodity model

The Schwartz–Smith model reads the log spot of a commodity as the sum of a short-term
deviation $\chi$ and an equilibrium level $\xi$:

* $\chi_t = e^{-\kappa t}\chi_0 + \sigma_\chi\int_0^t e^{-\kappa(t-s)}\,dB^1_s$
  (`HullWhite.integratedRate` at zero forcing: Ornstein–Uhlenbeck), and
* $\xi_t = \xi_0 + \nu t + \rho\sigma_\xi B^1_t + \sqrt{1-\rho^2}\,\sigma_\xi B^2_t$
  (drifted Brownian motion), with $B^1, B^2$ independent and correlation $\rho$,
* $\ln S_t = \chi_t + \xi_t$.

The module derives, from that Wiener representation and for $\kappa > 0$, $\rho^2 \le 1$:

* the joint law of $(\chi_t, \xi_t)$: jointly Gaussian with $\operatorname{cov}(\chi_t,\xi_t)
  = \rho\sigma_\chi\sigma_\xi(1-e^{-\kappa t})/\kappa$;
* the law of $\ln S_t$: Gaussian with mean $e^{-\kappa t}\chi_0 + \xi_0 + \nu t$ and variance
  $\sigma_\chi^2(1-e^{-2\kappa t})/(2\kappa) + \sigma_\xi^2 t + 2\rho\sigma_\chi\sigma_\xi(1-e^{-\kappa t})/\kappa$;
* $\ln \mathbb{E}[S_t] = \mathbb{E}[\ln S_t] + \frac12\operatorname{Var}[\ln S_t]$, and the
  long-run intercept of $\ln \mathbb{E}[S_t] - \nu t - \frac12\sigma_\xi^2 t$;
* the futures price $\mathbb{E}[S_T] = $ `schwartzSmithFuturesPrice` (zero interest rate), the
  Black formula for the option on the futures at the term-structure volatility, and the
  Gibson–Schwartz change of variables ($\xi_t = \ln S_t - \chi_t$; the convenience-yield reading
  $\delta_t = \kappa\chi_t$ turns the expected log-spot drift into $\nu - \delta_t$).

The two Gaussian tools the derivation needs are proved here as private helpers: two Wiener
integrals against one motion are jointly Gaussian with covariance the $L^2$ inner product, and
Wiener integrals against independent motions are independent.

## Main definitions

* `schwartzSmithChi` — the short-term deviation $\chi_t$, as `HullWhite.integratedRate`
  at zero forcing.
* `schwartzSmithXi` — the equilibrium level $\xi_t$.
* `schwartzSmithLogSpot` — the log spot $\ln S_t = \chi_t + \xi_t$.
* `schwartzSmithTotalVariance` — the variance of $\ln S_t$, the squared term-structure
  volatility.
* `schwartzSmithFuturesPrice` — the futures price closed form $\exp(e^{-\kappa T}\chi_0 + \xi_0
  + \nu T + v_T/2)$ with $v_T$ the total variance; proved to be $\mathbb{E}[S_T]$.

## Main results

* `schwartzSmithChiXi_covariance` — the cross-covariance of the two factors.
* `schwartzSmithChiXi_hasGaussianLaw` — the two factors are jointly Gaussian.
* `schwartzSmithLogSpot_hasLaw` — the Gaussian law of the log spot.
* `schwartzSmithExpectedSpot` — $\mathbb{E}[S_t]$, the lognormal mean.
* `schwartzSmithLnExpectedSpot_tendsto` — the long-run intercept of $\ln\mathbb{E}[S_t]$.
* `schwartzSmithFuturesPrice_eq_expectedSpot` — the futures price is the expected terminal spot.
* `schwartzSmithFuturesCall` — the option on the futures at the term-structure volatility.
* `schwartzSmithXi_eq_logSpot_sub_chi`, `schwartzSmithGsDrift` — the Gibson–Schwartz change
  of variables and its convenience-yield drift reading.

## References

* [E. Schwartz, J. E. Smith, *Short-Term Derivatives and Long-Term Fundamentals and Their
  Applications in Commodity Markets*][SchwartzSmith2000]
* [K. Binkowski, P. He, N. Kordzakhia, P. Shevchenko, *On the Parameter Estimation in the
  Schwartz-Smith's Two-Factor Model*][BinkowskiEtAl2021], §2 (the open reproduction of the
  model and the closed forms used here; the 2000 paper itself was not read)
* [F. Black, *The pricing of commodity contracts*][Black1976]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 18

## Tags

Schwartz-Smith model, two-factor commodity model, Ornstein-Uhlenbeck, futures price,
term-structure volatility, option on futures, Gibson-Schwartz, convenience yield,
MSC 91G20, MSC 60G15, JEL Q02
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B B₁ B₂ : ℝ≥0 → Ω → ℝ}

/-! ### The path σ-algebra and the independence of the two motions' Wiener integrals

Each Brownian motion generates the σ-algebra `⨆ s, (borel ℝ).comap (B s)` on `Ω` — the pullback
of the product σ-algebra on the path space (`MeasurableSpace.pi` of Mathlib's instance, unfolded
with `comap_iSup` and `comap_comp`). A Wiener integral against `B` is measurable for it (the
step increments are, and `mem_lpMeas_of_stepIndicator` closes), so the Doob–Dynkin lemma
(`StronglyMeasurable.exists_eq_measurable_comp`) factors it through the path, and
`IndepFun.comp` transports the assumed independence of the two motions. -/

/-- The σ-algebra a process `B` generates, as the pullback of the product σ-algebra on the
path space. -/
abbrev processSigma (B : ℝ≥0 → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω s' ↦ B s' ω) (inferInstanceAs (MeasurableSpace (ℝ≥0 → ℝ)))

private lemma processSigma_eq (B : ℝ≥0 → Ω → ℝ) :
    processSigma B = ⨆ s : ℝ≥0, (borel ℝ).comap (B s) := by
  rw [processSigma, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  exact congrArg _ (funext fun s ↦ MeasurableSpace.comap_comp)

private lemma measurable_b_processSigma (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
    Measurable[processSigma B] (B s) := by
  rw [processSigma_eq]
  exact Measurable.iSup' s (fun t ht => ⟨t, ht, rfl⟩)

private lemma stronglyMeasurable_b_processSigma (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ s, Measurable (B s)) (s : ℝ≥0) :
    StronglyMeasurable[processSigma B] (B s) := by
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_b_processSigma B s,
    StronglyMeasurable.isSeparable_range (Measurable.stronglyMeasurable (hBm s))⟩

private lemma aestronglyMeasurable_wienerIntegral_processSigma (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    AEStronglyMeasurable[processSigma B] (fun ω ↦ (wienerIntegralLp B hB T f) ω) μ := by
  have hΦ : (wienerIntegralLp B hB T f) ∈ lpMeas ℝ ℝ (processSigma B) 2 μ := by
    have hm : processSigma B ≤ mΩ := (measurable_pi_iff.2 hBm).comap_le
    refine mem_lpMeas_of_stepIndicator hm (wienerIntegralLp B hB T) (fun i ↦ ?_) f
    rw [wienerIntegralLp_stepIndicator]
    exact wienerIncrementLp_mem_lpMeas hB i
      (stronglyMeasurable_b_processSigma B hBm i.1.1)
      (stronglyMeasurable_b_processSigma B hBm i.1.2)
  exact mem_lpMeas_iff_aestronglyMeasurable.1 hΦ

/-- **Wiener integrals against independent motions are independent.** For pre-Brownian
motions `B₁`, `B₂` whose path maps are independent, and deterministic kernels `f`, `g` over
`(0, T]`, the Wiener integrals `∫₀ᵀ f dB¹` and `∫₀ᵀ g dB²` are independent. -/
private theorem indepFun_wienerIntegral_of_indepFun (hB₁ : IsPreBrownianReal B₁ μ)
    (hB₂ : IsPreBrownianReal B₂ μ) (h₁m : ∀ s, Measurable (B₁ s)) (h₂m : ∀ s, Measurable (B₂ s))
    (hind : IndepFun (fun ω s ↦ B₁ s ω) (fun ω s ↦ B₂ s ω) μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
    (g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    IndepFun (fun ω ↦ (wienerIntegralLp B₁ hB₁ T f) ω)
      (fun ω ↦ (wienerIntegralLp B₂ hB₂ T g) ω) μ := by
  obtain ⟨p₁, hp₁m, hp₁e⟩ :=
    aestronglyMeasurable_wienerIntegral_processSigma hB₁ h₁m T f
  obtain ⟨p₂, hp₂m, hp₂e⟩ :=
    aestronglyMeasurable_wienerIntegral_processSigma hB₂ h₂m T g
  obtain ⟨q₁, hq₁m, hq₁c⟩ := hp₁m.exists_eq_measurable_comp
  obtain ⟨q₂, hq₂m, hq₂c⟩ := hp₂m.exists_eq_measurable_comp
  have hind' := hind.comp hq₁m.measurable hq₂m.measurable
  refine hind'.congr ?_ ?_
  · rw [← hq₁c]
    exact hp₁e.symm
  · rw [← hq₂c]
    exact hp₂e.symm

end MathFin
